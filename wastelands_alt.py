"""One foreground Roblox client. All game input is serialized in this worker."""
import re
import time

import numpy as np
from PIL import Image, ImageDraw, ImageGrab, ImageOps
from pynput import mouse

import twd_bot as farm
from wastelands_team import ABILITIES, EARLY, PLACEMENT_ORDER, bank_slot, placement_attempts, Wait, placement_label, position, private_server_links
from wastelands_view import OCR, color_boxes, invite_buttons, label, read_invite, map_point, preview, perimeter_point, rank_titan_sites, placement_pose, mission_button, ready_button, wastelands_slots, scene, screen_point, tracked_pose


class Game(farm.Bot):
    def __init__(self, guard):
        super().__init__(use_speed=False,hotkeys=False)
        self.guard = guard

    def rect(self):
        hwnd = farm.foreground_window()
        if not hwnd or not farm.is_game_window(hwnd):
            raise Wait("Жду активное окно Roblox")
        rect = farm.window_rect(hwnd)
        if not rect:
            raise Wait("Окно Roblox недоступно")
        return rect

    def grab(self, box=(0,0,1,1)):
        rect = self.rect()
        l,t,r,b = rect
        corners = [round(v*s)+p for v,s,p in zip(box,(r-l,b-t)*2,(l,t)*2)]
        img = ImageGrab.grab(bbox=tuple(corners),all_screens=True)
        if self.rect() != rect:
            raise Wait("Окно переместилось")
        return img

    @staticmethod
    def vote_button(img, mode):
        if mode=="ready":
            return ready_button(img)
        return mission_button(img,mode) or farm.Bot.vote_button(img,mode)

    def check(self):
        self.guard()
        self.rect()

    def click(self, pt, **kwargs):
        self.check()
        rect = self.rect()
        if not all(0<x<1 for x in pt):
            raise Wait("Точка вне окна")
        self.m.position = self.to_screen(pt)
        time.sleep(.12)
        if self.rect() != rect:
            raise Wait("Окно переместилось")
        self.m.press(mouse.Button.left)
        try:
            time.sleep(.085)
        finally:
            self.m.release(mouse.Button.left)

    def accept_invite(self, point):
        def current(frame):
            buttons = invite_buttons(frame)
            return buttons[1] if buttons else None
        self.click_live(point, current, "Принять")

    def click_live(self, point, locate, title):
        rect = self.rect()
        target = self.to_screen(point)
        # Roblox updates its hover target on a movement event in some RDP sessions.
        self.hover(point)
        self.sleep(.20)
        frame = self.grab()
        live = locate(frame)
        if not live or any(abs(a-b)*size > 3 for a,b,size in zip(point,live,frame.size)):
            raise Wait(f"Кнопка «{title}» изменилась · проверяю снова")
        self.check()
        if self.rect() != rect:
            raise Wait("Окно Roblox переместилось · проверяю кнопку снова")
        if any(abs(a-b)>3 for a,b in zip(self.m.position,target)):
            raise Wait(f"Курсор не попал на «{title}» · повторяю наведение")
        self.m.press(mouse.Button.left)
        try:
            self.sleep(.15)
        finally:
            self.m.release(mouse.Button.left)


def manager_card(img, words, unit):
    name = {"amplifier":"Titan Amplifierman","screen":"Titan Screen Man"}[unit]
    title = label(words,name)
    if not title:
        return None
    rgb = np.asarray(img.convert("RGB")).astype(np.int16)
    r,g,b = rgb.transpose(2,0,1)
    mask = ((r>140)&(r-g>85)&(r-b>75)).astype(np.uint8)
    w,h = img.size
    choices = []
    for x,y,cw,ch in color_boxes(mask):
        if not (.09*w<cw<.49*w and .09*h<ch<.8*h):
            continue
        if x<title[0]*w<x+cw and y<title[1]*h<y+.27*ch:
            bounds = (x/w,y/h,(x+cw)/w,(y+ch)/h)
            row = [v for v in words if bounds[0]<v[1]+v[3]/2<bounds[2] and
                   bounds[1]<v[2]+v[4]/2<bounds[3]]
            if label(row,"Upgrade") or label(row,"Max Level"):
                choices.append((cw*ch,row))
    return min(choices,key=lambda item:item[0])[1] if choices else None


def level(row):
    for _,x,y,w,h in row:
        line = sorted((v for v in row if abs(v[2]+v[4]/2-y-h/2)<h*.6),key=lambda v:v[1])
        text = " ".join(v[0] for v in line)
        hit = re.search(r'level\s*[:.]?\s*([0-8])\s*/\s*8\b',text,re.I)
        if hit:
            return int(hit[1])
    return None


def manager_bounds(img):
    rgb=np.asarray(img.convert("RGB")).astype(np.int16)
    r,g,b=rgb.transpose(2,0,1)
    cyan=((g>130)&(b>140)&(g-r>65)&(b-r>65)).astype(np.uint8)
    boxes = color_boxes(cyan)
    return max((p for p in boxes if .20*img.width<p[2]<.82*img.width and p[3]>.45*img.height),
               key=lambda p:p[2]*p[3],default=None)


def countdown(row,action,button):
    # The printed "45s cooldown" describes the skill even when it is ready.
    # Only a separate countdown without the caption is evidence of an active timer.
    for word,x,y,w,h in row:
        m=re.fullmatch(r"(\d{1,2})(?:\.\d+)?s",word,re.I)
        if not m or not 0<int(m[1])<=60 or abs(y+h/2-button[1])>.085:
            continue
        if abs(x+w/2-button[0])>(.12 if action=="Aerial Attack" else .062):
            continue
        if any("cooldown" in v[0].lower() and abs(v[2]-y)<.036 and abs(v[1]-x)<.075 for v in row):
            continue
        return int(m[1])
    return None


class Alt:
    def __init__(self, connection, slots, stop, notify):
        self.connection = connection
        self.player, self.configured_slots = connection.player, dict(slots)
        self.stop,self.notify = stop,notify
        self.run = ""
        self.status = "Подключение"
        self.last_summon = None
        self.ocr = OCR()
        self.game = Game(self.guard)
        self.last_checked = 0
        self.deadline = None

    def exchange(self, op="poll", **fields):
        return self.connection.exchange(op, run=self.run, status=self.status, **fields)

    def guard(self):
        if self.stop.is_set() or not self.run:
            raise Wait("Остановлено")
        if self.deadline is not None and time.monotonic()>=self.deadline:
            raise Wait("Время команды истекло")
        if time.monotonic()-self.last_checked>.45:
            state = self.exchange()
            if state.get("summon") or state["run"] != self.run:
                raise Wait("Матч остановлен")
            self.last_checked = time.monotonic()

    def reset(self, state):
        self.run = state["run"]
        self.phase = "lobby"
        self.slots = dict(getattr(self,"configured_slots",{}))
        self.next_slot_check = 0
        self.full_early = set()
        self.afk_signature = None
        self.afk_clicks = 0
        self.afk_retry_at = 0
        self.voted = state["progress"].get("voted",False)
        self.vote_retry = 0
        self.uncertain_votes = set()
        self.ready = state["progress"].get("ready",False)
        self.invited = state["progress"].get("invited",False)
        self.last_invite = None
        self.invite_attempts = 0
        self.placed = set()
        self.attempt = dict.fromkeys(PLACEMENT_ORDER, 0)
        self.sites = {}
        self.rescan_at = {}
        self.host_sites = state.get("placement_sites",False)
        self.pending_places = set()
        self.count_retry_at = {}
        self.slot_wait_until = {}
        self.retry = state["progress"].get("retry",0)
        self.levels = {"amplifier":0,"screen":0}
        self.wait_cash = 0
        self.next_upgrade = 0
        self.game.holding = None
        self.pose = self.shot = None
        self.reference = None
        self.confirm = None
        self.needs_close = False

    def text(self, img, box=(0,0,1,1)):
        return self.ocr.read(img,box)

    def confirm_group(self):
        if not self.invited:
            self.exchange("invited")
            self.invited = True
        self.last_invite = None
        self.invite_attempts = 0

    def vote_reading(self, img, button, mode=None):
        x,y,w,h = (button[k] for k in ("cx","cy","w","h"))
        box = ((x-.26*w,y+.52*h,x+.26*w,y+1.14*h) if mode=="ready"
               else (x+.09*w,y-.48*h,x+.49*w,y+.48*h))
        area = farm.crop_frac(img,box).convert("L")
        ink = area.point(lambda v: 255 if v>180 else 0)
        bounds = ink.getbbox()
        if not bounds or bounds[2]-bounds[0]<.30*area.width or bounds[3]-bounds[1]<.30*area.height:
            return None, None
        glyphs = ink.crop(bounds).resize((80,36),Image.Resampling.BILINEAR)
        clean = ImageOps.expand(ImageOps.invert(ink),border=8,fill=255)
        words = self.ocr.read(clean,zoom=3)
        count = re.fullmatch(r"([0-4])/([1-4])", "".join(word[0] for word in words).replace(" ",""))
        value = (int(count[1]),int(count[2])) if count and count[1]<=count[2] else None
        return value, np.asarray(glyphs)>127

    def vote(self, mode):
        title = mode.upper()
        is_ready = mode=="ready"
        if not is_ready and self.voted:
            return f"Голосование за {title} продолжается"
        if mode in self.uncertain_votes:
            return f"Проверь голос за {title} · не прочитан счётчик после попытки"
        now = time.monotonic()
        if now < self.vote_retry:
            return f"Проверяю голосование за {title}"
        turn = self.exchange("vote_turn")
        if turn.get("vote_seconds",0) < 4:
            self.vote_retry = now+.8
            return f"Жду очереди голосовать за {title}"
        until = now + turn["vote_seconds"]
        def target(button):
            if button:
                return (button["cx"] if is_ready else button["cx"]-.20*button["w"],button["cy"])
        try:
            frame = self.game.grab()
            button = self.game.vote_button(frame,mode)
            if not button:
                return "Экран голосования закрылся"
            before, original = self.vote_reading(frame,button,mode)
            if not (before and before[0]==before[1]):
                if time.monotonic()+3 > until:
                    return "Обновляю кадр голосования"
                self.game.click_live(target(button), lambda img: target(self.game.vote_button(img,mode)), "READY" if is_ready else "VOTE")
                # A second click can remove a vote. Only retry on a readable,
                # unchanged counter while this alt still holds the voting turn.
                self.uncertain_votes.add(mode)
                after = None
                changed_frames = 0
                unchanged_frames = 0
                for _ in range(3):
                    self.game.sleep(.35)
                    frame = self.game.grab()
                    button = self.game.vote_button(frame,mode)
                    if not button:
                        return "Голосование закрылось · проверяю экран матча"
                    after, current = self.vote_reading(frame,button,mode)
                    if time.monotonic()>=until:
                        return f"Проверь голос за {title} · время проверки истекло"
                    if after and (after[0]==after[1] or
                                  before and before[1]==after[1] and after[0]>before[0]):
                        break
                    # In a small RDP window OCR can merge "1/" into one glyph.
                    # Compare only the white counter lettering, away from the cursor.
                    if original is not None and current is not None:
                        diff = np.count_nonzero(current ^ original) / max(1,np.count_nonzero(current | original))
                        changed_frames = changed_frames+1 if diff>.18 and (not before or not after) else 0
                        unchanged_frames = unchanged_frames+1 if diff<.04 else 0
                        if changed_frames>=2:
                            break
                    else:
                        changed_frames = unchanged_frames = 0
                else:
                    if before and before==after or unchanged_frames>=2:
                        self.uncertain_votes.discard(mode)
                        return f"{title} · счётчик не изменился, повторю"
                    return f"Проверь голос за {title} · нет подтверждения"
            self.uncertain_votes.discard(mode)
            if is_ready:
                self.exchange("ready")
                self.ready = True
            else:
                self.exchange("voted")
                self.voted = True
            return f"Голосование за {title} · счётчик подтверждён"
        finally:
            self.vote_retry = time.monotonic()+1.2
            self.exchange("vote_end")

    def lobby(self, state, img):
        now = time.monotonic()
        if self.last_invite is not None and now-self.last_invite > 45:
            self.last_invite = None
            self.invite_attempts = 0
        if ((self.invited or self.voted) and (img is not None and ready_button(img) or self.game.ready_visible())
                or self.placed and self.game.money() is not None):
            self.phase = "battle"
            self.game.camera_top_down()
            return "Подготовка расстановки"
        vote = self.game.vote_button(img,state["mode"])
        if vote and not self.invited:
            if self.last_invite is None and not mission_button(img,state["mode"]):
                return "Ожидаю группу Wastelands от основы"
            self.confirm_group()
        if vote:
            return self.vote(state["mode"])
        accept, reason = read_invite(img,state["host"],self.ocr.read)
        if accept:
            if self.last_invite is None or now-self.last_invite >= 2:
                self.game.accept_invite(accept)
                self.last_invite = time.monotonic()
                self.invite_attempts += 1
            return f"Приглашение на экране · попытка {self.invite_attempts}, проверяю вход"
        if reason:
            return reason
        group = self.text(img,(0,.26,.19,.74))
        group_map = label(group,"Wasteland") or label(group,"Wastelands")
        controls = self.text(img,(.35,.74,.65,.98)) if group_map else []
        if label(controls,"Cancel") or label(controls,"Отмена"):
            self.confirm_group()
            return "В группе · жду запуска основой"
        if self.last_invite is not None:
            return "Приглашение исчезло · жду подтверждения входа"
        if self.voted or state["mode"] in self.uncertain_votes:
            return "Голосование закрылось · проверяю появление READY"
        return "Жду приглашение или голосование"

    def update_places(self,state):
        own = {p["unit"]:p for p in state["places"] if p["player"]==self.player}
        if not all(unit in own for unit in PLACEMENT_ORDER):
            raise Wait("Основа не передала десять мест. Обнови основу до 6.0.4.")
        self.placed = {u for u,p in own.items() if p["state"]=="placed"}
        self.points = {u:p["point"] for u,p in own.items() if u in self.placed}
        if self.confirm:
            op,unit,point = self.confirm
            if own[unit].get("target")==point:
                self.exchange(op,unit=unit,point=point)
            self.confirm = None
            return True
        pending = {unit for unit,row in own.items() if row.get("target")}
        for unit in self.pending_places-pending-self.placed:
            self.attempt[unit] += 1
        self.pending_places = pending
        return False

    def placement_sites(self,unit):
        if unit not in self.sites:
            if self.host_sites:
                self.sites[unit] = self.exchange("placement_sites",unit=unit)["sites"]
            else:
                locate = bank_slot if unit.partition("_")[0] in EARLY else position
                # Older coordinators only know the original five titan candidates.
                count = placement_attempts(unit) if unit.partition("_")[0] in EARLY else 5
                self.sites[unit] = [locate(self.player,unit,i) for i in range(count)]
        return self.sites[unit]

    @staticmethod
    def slot_center(frame,slot):
        return .5 + (slot-3.5)*.13*frame.height/frame.width

    def slot_count(self,frame,slot,limit):
        x = self.slot_center(frame,slot)*frame.width
        h = frame.height
        icon = frame.crop((round(x-.046*h),round(.854*h),round(x+.046*h),round(.897*h)))
        # White glyphs have a dark outline, even on the white TV portrait.
        # Remove bright background regions touching the edges before OCR.
        gray = icon.convert("L")
        for threshold in (155,120,None):
            if threshold is None:
                sample = icon
            else:
                mask = ImageOps.expand(gray.point(lambda v: 255 if v>=threshold else 0),1,fill=255)
                ImageDraw.floodfill(mask,(0,0),0)
                bounds = mask.getbbox()
                if not bounds:
                    continue
                sample = ImageOps.expand(ImageOps.invert(mask.crop(bounds)),4,fill=255)
            words = self.ocr.read(sample,zoom=5)
            text = "".join(word[0] for word in words).replace(" ","")
            text = text.translate(str.maketrans({"O":"0", "o":"0", "I":"1", "l":"1"}))
            found = re.fullmatch(r"([0-4])/"+str(limit),text)
            if found and int(found[1])<=limit:
                return int(found[1])
        return None

    def hover_count(self,slot,limit):
        rect = self.game.rect()
        frame = self.game.grab()
        if farm.afk_panel(frame):
            return None
        self.game.hover((self.slot_center(frame,slot),.875))
        self.game.sleep(.25)
        reads = []
        for _ in range(2):
            frame = self.game.grab()
            if self.game.rect()!=rect or farm.afk_panel(frame):
                return None
            reads.append(self.slot_count(frame,slot,limit))
            if len(reads)==1:
                self.game.sleep(.19)
        return reads[0] if reads[0]==reads[1] else None

    def placement_outcome(self,slot,limit,before_count):
        # Income, slot price and a disappearing preview cannot prove ownership.
        # Give the server time to publish the new count before a rejected retry.
        self.game.sleep(.60)
        count = self.hover_count(slot,limit)
        if count==before_count+1:
            return "commit"
        if count==before_count:
            self.game.sleep(.65)
            count = self.hover_count(slot,limit)
            if count==before_count+1:
                return "commit"
            if count==before_count:
                return "release"
        return None

    def recheck_pending(self,state):
        now = time.monotonic()
        for row in state["places"]:
            unit, point = row["unit"],row.get("target")
            before = row.get("count_before")
            if (row["player"]!=self.player or row["state"]=="placed" or not point
                    or before is None or now<self.count_retry_at.get(unit,0)):
                continue
            kind = unit.partition("_")[0]
            outcome = self.placement_outcome(self.slots[kind],4 if kind in EARLY else 1,before)
            self.count_retry_at[unit] = time.monotonic()+5
            if outcome:
                self.confirm = (outcome,unit,point)
                self.exchange(outcome,unit=unit,point=point)
                self.confirm = None
                return (f"Поставил {placement_label(unit)} · проверено по слоту" if outcome=="commit"
                        else f"{placement_label(unit)} · счётчик прежний, ищу другое место")
            break
        return None

    def place(self, unit, img):
        prices = farm.read_hotbar(img)
        slot = self.slots[unit.partition("_")[0]]
        name = placement_label(unit)
        # Associate the physical card with its slot even when another price is unreadable.
        center = self.slot_center(img,slot)
        price = next((v for x,v in prices if abs(x-center)<.032 and v),None)
        cash = self.game.money()
        # A selected early unit can cover its own price at RDP scale.
        kind = unit.partition("_")[0]
        if kind in EARLY and any(other!=kind and price==farm.UNITS[other]["price"] for other in EARLY):
            return f"{name} · в слоте {slot} видна цена другого юнита, проверь номера слотов"
        if price is None and kind in ("plunger","tv"):
            price = farm.UNITS[kind]["price"]
        if price is None and kind in ("amplifier","screen"):
            price = {"amplifier":7000,"screen":7750}[kind]
        if price is None or cash is None or cash < price:
            return f"Жду {name} · баланс {cash}, цена слота {slot}: {price}"
        sites = self.placement_sites(unit)
        if self.attempt[unit]>=len(sites):
            return f"{name} · свободное место не найдено, проверь разметку"
        limit = 4 if kind in EARLY else 1
        before_count = self.hover_count(slot,limit)
        if before_count is None or before_count==limit:
            self.slot_wait_until[kind] = time.monotonic()+4
        if before_count is None:
            return f"Не прочитал счётчик {name} в слоте {slot} · повторяю наведение"
        if before_count==limit:
            if kind in EARLY:
                self.full_early.add(kind)
            return f"{name} · в игре уже {limit}/{limit}, проверь места юнитов"
        if not self.game.take(slot):
            return "Не появилась подсветка дороги"
        try:
            self.game.hover(farm.IDLE_POINT)
            snap = self.game.grab()
            pose = placement_pose(snap)
            if pose is None and self.reference is not None:
                pose = tracked_pose(self.reference,self.pose,snap) if self.game.rect()==self.reference_rect else None
            if pose is None:
                return "Проверяю направление Wastelands по дороге и обломкам"
            titan = kind not in EARLY
            start = self.attempt[unit]
            if titan:
                sites[start:] = rank_titan_sites(snap,pose,sites[start:],sites[:start])
            clicks = 0
            for attempt in range(start,len(sites)):
                self.attempt[unit] = attempt
                if titan:
                    point = sites[attempt]
                else:
                    point = perimeter_point(snap,pose,*sites[attempt])
                    if point is None:
                        continue
                pt = screen_point(pose,point)
                if not (.015<pt[0]<.985 and .10<pt[1]<.92) or (.27<pt[0]<.74 and pt[1]>.81):
                    continue
                try:
                    self.exchange("reserve",unit=unit,point=point,count_before=before_count)
                except Wait as exc:
                    if any(reason in str(exc) for reason in
                           ("Рядом занят участок","Зона ранней защиты основы","Зона титанов основы")):
                        continue
                    if "За пределами назначенной зоны" in str(exc):
                        if not self.host_sites:
                            raise Wait("Разметка основы и твинка различается · обнови и перезапусти оба приложения") from exc
                        continue
                    raise
                outcome = self.try_place(point,pt,snap,unit,slot,limit,before_count)
                if titan:
                    farm.log(f"Wastelands · твинк {self.player} · {name} · место {attempt+1}/{len(sites)} "
                             f"({point[0]:.0f}, {point[1]:.0f}) · {outcome or 'требует проверки'}")
                if outcome=="commit":
                    self.placed.add(unit)
                    self.game.drop()
                    self.pose,self.reference = pose,self.game.grab()
                    self.reference_rect = self.game.rect()
                    return f"Поставил {name}"
                if outcome is None:
                    return f"{name} · результат не подтверждён, перепроверю счётчик"
                self.attempt[unit] = attempt+1
                clicks += 1
                if not titan or clicks>=3 or not self.game.path_visible():
                    return "Точка занята · пробую рядом"
                # The preview stayed open. Keep its pose and slot, and try a
                # different footprint after verifying the scene at click time.
                cash = self.game.money()
                if cash is None or cash<price:
                    return f"Перепроверяю баланс для {name}"
                sites[attempt+1:] = rank_titan_sites(snap,pose,sites[attempt+1:],sites[:attempt+1])
            self.attempt[unit] = len(sites)
            return f"{name} · места заняты или кромка не видна, проверь расстановку"
        finally:
            self.game.drop()

    def try_place(self,point,pt,snap,unit,slot,limit,before_count):
        reference_scene = scene(snap)
        def live_point(frame):
            if frame.size==snap.size and np.median(abs(scene(frame)-reference_scene))<4:
                return pt
            return None
        try:
            self.game.click_live(pt,live_point,placement_label(unit))
        except Wait:
            self.confirm = ("release",unit,point)
            raise
        outcome = self.placement_outcome(slot,limit,before_count)
        if outcome is None:
            self.count_retry_at[unit] = time.monotonic()+3
        if outcome:
            self.confirm = (outcome,unit,point)
            self.exchange(outcome,unit=unit,point=point)
            self.confirm = None
        return outcome

    def header(self, img):
        return label(self.text(img,(0,0,1,.32)),"UNIT MANAGER")

    def close_manager(self):
        img=self.game.grab()
        if manager_bounds(img) or self.header(img):
            # Closing our own verified menu also works after Stop or a lost lease.
            self.game.rect()
            k = self.game._vk("v")
            self.game.k.press(k)
            try:
                time.sleep(.06)
            finally:
                self.game.k.release(k)
            time.sleep(.22)
            img=self.game.grab()
            if manager_bounds(img) or self.header(img):
                raise Wait("Не удалось закрыть Unit Manager")
        self.needs_close = False

    def manager(self, unit, action, target=None):
        self.needs_close = True
        try:
            if not self.header(self.game.grab()):
                self.game.key("v")
                self.game.sleep(.28)
            img = self.game.grab()
            words = self.text(img)
            if not label(words,"UNIT MANAGER",(0,0,1,.32)):
                return "Unit Manager не распознан"
            row = manager_card(img,words,unit)
            if not row and label(words,"Rarity"):
                self.game.click(label(words,"Rarity"))
                self.game.sleep(.20)
                img = self.game.grab()
                row = manager_card(img,self.text(img),unit)
            if not row:
                return "Карточка титана не видна целиком"
            lvl = level(row)
            if lvl is not None:
                self.levels[unit]=lvl
            button = label(row,action)
            if action == "Upgrade":
                if lvl is None or lvl>=8 or unit!=min(self.levels,key=self.levels.get):
                    return "Уровни сверены"
                if not button:
                    return "Улучшение недоступно"
                prices = [v[0] for v in row if v[1]>button[0] and abs(v[2]+v[4]/2-button[1])<v[4]*.75]
                cost = re.search(r'\$\s*([\d,]+)'," ".join(prices))
                if not cost:
                    return "Не прочитал цену улучшения"
                self.wait_cash = int(cost[1].replace(",",""))
                cash = self.game.money()
                if cash is None or cash<self.wait_cash:
                    return f"Коплю {self.wait_cash} на {unit}"
            if not button:
                return "Способность закрыта или не распознана"
            if action in ABILITIES:
                remaining=countdown(row,action,button)
                if remaining:
                    return f"Перезарядка · {remaining} с"
            self.game.click(button)
            self.game.sleep(.22)
            if action=="Teleport":
                # If the destination is covered by the open panel, a click there
                # could activate a different command.
                panel_img = self.game.grab()
                panel = manager_bounds(panel_img)
                if not panel:
                    return "Границы Unit Manager не видны"
                x,y,w,h=panel
                px,py=target[0]*panel_img.width,target[1]*panel_img.height
                if x<=px<x+w and y<=py<y+h:
                    return "Точка закрыта меню"
                self.game.click(target)
                self.game.sleep(.4)
                after=self.game.grab()
                return "Перенос подтверждён" if not manager_bounds(after) and not self.header(after) else "Перенос не подтверждён"
            if action=="Upgrade":
                frame = self.game.grab()
                updated = manager_card(frame,self.text(frame),unit)
                actual = level(updated or [])
                if actual is not None and actual>lvl:
                    self.levels[unit] = actual
                    self.wait_cash = 0
                    return f"{unit} · уровень {actual}/8"
                return f"{unit}: уровень не изменился или не прочитан"
            frame=self.game.grab()
            after=manager_card(frame,self.text(frame),unit)
            if after and countdown(after,action,button):
                return f"{action}: сработало · началась перезарядка"
            return f"{action}: нажато, срабатывание не подтверждено"
        finally:
            self.deadline = None
            self.close_manager()

    def command(self, cmd):
        name = cmd["name"]
        unit = "amplifier" if name=="Aerial Attack" else "screen"
        if unit in self.pending_places:
            return {"result":"Место титана ещё не подтверждено"}
        if self.phase!="battle" or unit not in self.placed:
            return {"result":"Титан ещё не поставлен"}
        live=self.game.grab()
        current=tracked_pose(self.reference,self.pose,live) if self.reference is not None else None
        if current is not None and name!="snapshot":
            location=screen_point(current,self.points[unit])
            if all(.02<x<.98 for x in location) and farm.stun_fraction(live,location)>.25:
                return {"result":"Титан оглушён"}
        if name=="snapshot":
            if current is None:
                if not self.game.take(self.slots["screen"]):
                    return {"result":"Не удалось сверить положение камеры"}
                try:
                    self.game.hover(farm.IDLE_POINT)
                    current = placement_pose(self.game.grab())
                finally:
                    self.game.drop()
                if current is None:
                    return {"result":"Не узнал карту"}
                live=self.game.grab()
            self.shot = (cmd["id"],time.monotonic(),scene(live),current,live.size)
            return {"result":"Выбери место на кадре","frame":preview(live)}
        if name=="Teleport":
            if not self.shot or self.shot[0]!=cmd["frame_id"] or time.monotonic()-self.shot[1]>45:
                return {"result":"Кадр устарел"}
            img = self.game.grab()
            if img.size!=self.shot[4] or np.median(abs(scene(img)-self.shot[2]))>9:
                return {"result":"Камера сменилась · нужен новый кадр"}
            pt = cmd["point"]
            point = map_point(self.shot[3],pt)
            if current is not None and np.linalg.norm((np.array(screen_point(current,point))-pt)*img.size)>9:
                return {"result":"Камера сменилась · нужен новый кадр"}
            self.exchange("reserve",unit=unit,point=point)
            self.shot = None
            result = self.manager(unit,name,pt)
            op = "commit" if result=="Перенос подтверждён" else "release"
            self.confirm = (op,unit,point)
            self.exchange(op,unit=unit,point=point)
            self.confirm = None
            return {"result":result}
        return {"result":self.manager(unit,name)}

    def answer_afk(self,panel,automatic):
        _, points, signature, choice = panel
        if not farm.same_afk_signature(self.afk_signature,signature):
            self.afk_signature = signature
            self.afk_clicks = 0
            self.afk_retry_at = 0
        if not automatic or choice is None:
            return "AFK CHECK · жду ручного ответа"
        if time.monotonic()<self.afk_retry_at:
            return "AFK CHECK · жду закрытия панели"
        if self.afk_clicks>=2:
            return "AFK CHECK · панель осталась, нужен ручной ответ"

        def current(frame):
            live = farm.afk_panel(frame)
            if live and live[3]==choice and farm.same_afk_signature(signature,live[2]):
                return live[1][choice]
            return None

        self.game.click_live(points[choice],current,"AFK CHECK")
        self.afk_clicks += 1
        self.afk_retry_at = time.monotonic()+2
        return "AFK CHECK · ответ отправлен, проверяю закрытие"

    def tick(self,state):
        self.guard()
        if self.needs_close:
            self.close_manager()
        img = self.game.grab()
        panel = farm.afk_panel(img)
        if panel:
            return self.answer_afk(panel,state.get("afk_auto",False))
        self.afk_signature = None
        if farm.is_end_image(farm.crop_frac(img,farm.END_BOX)):
            self.phase = "end"
        if self.phase=="end":
            return "Матч завершён · жду следующий матч"
        if self.update_places(state):
            return "Состояние постановки синхронизировано"
        if state["progress"]["retry"]!=self.retry:
            self.attempt = dict.fromkeys(PLACEMENT_ORDER, 0)
            self.full_early.clear()
            self.slot_wait_until.clear()
            self.sites.clear()
            self.rescan_at.clear()
            self.retry = state["progress"]["retry"]
        if self.phase=="lobby":
            return self.lobby(state,img)
        if (not self.ready and "ready" not in self.uncertain_votes
                and time.monotonic()>=self.vote_retry and ready_button(img)):
            return self.vote("ready")
        if time.monotonic()>=self.next_slot_check and not self.placed and not self.pending_places:
            detected = wastelands_slots(img)
            if detected and detected!=self.slots:
                farm.log(f"Wastelands · твинк {self.player} · слоты по карточкам: {detected}")
                self.slots = detected
            self.next_slot_check = float("inf") if detected else time.monotonic()+2
        cmd = state["command"]
        if cmd:
            cmd = self.exchange("claim",id=cmd["id"])["claimed"]
            if not cmd:
                return "Команда уже принята или устарела"
            self.deadline = time.monotonic()+cmd["remaining"]
            try:
                response = self.command(cmd)
            except Wait as exc:
                response = {"result":str(exc)}
            finally:
                self.deadline = None
            self.exchange("result",id=cmd["id"],**response)
            return response["result"]
        if self.pending_places:
            checked = self.recheck_pending(state)
            if checked:
                return checked
        outstanding = [u for u in PLACEMENT_ORDER if u not in self.placed
                       and u.partition("_")[0] not in self.full_early]
        pending_kinds = {u.partition("_")[0] for u in self.pending_places}
        # Finish one early unit type before moving on to the next stage.
        stage = outstanding
        for kind in EARLY:
            copies = [u for u in outstanding if u.partition("_")[0]==kind]
            if copies:
                stage = copies
                break
        now = time.monotonic()
        for unit in stage:
            kind = unit.partition("_")[0]
            if kind in pending_kinds or now<self.slot_wait_until.get(kind,0):
                continue
            if unit in self.sites and self.attempt[unit]>=len(self.sites[unit]):
                due = self.rescan_at.setdefault(unit,now+4)
                if now<due:
                    continue
                del self.rescan_at[unit]
                self.attempt[unit] = 0
            return self.place(unit,img)
        if stage:
            kind = stage[0].partition("_")[0]
            if kind in pending_kinds:
                return f"{placement_label(stage[0])} · жду подтверждения постановки"
            if now<self.slot_wait_until.get(kind,0):
                return f"{placement_label(stage[0])} · перепроверяю счётчик слота {self.slots[kind]}"
            return f"{placement_label(stage[0])} · повторю поиск свободного места"
        if min(self.levels.values())<8 and time.monotonic()>self.next_upgrade:
            self.next_upgrade = time.monotonic()+4
            cash = self.game.money()
            if cash is not None and cash>=self.wait_cash:
                unit = min(self.levels,key=self.levels.get)
                return self.manager(unit,"Upgrade")
        return f"Amplifier {self.levels['amplifier']}/8 · Screen {self.levels['screen']}/8"

    def join_private(self, request):
        # An ACK can be lost after Windows has already opened the link.
        if self.last_summon is None or self.last_summon[0] != request["id"]:
            try:
                targets = private_server_links(request.get("link"))
                opened = farm.open_private_link(targets)
            except ValueError:
                opened = False
            self.last_summon = (request["id"], opened)
        request_id, opened = self.last_summon
        self.exchange("summon_result", id=request_id, opened=opened)
        return "Ссылка на приватку открыта" if opened else "Не удалось открыть ссылку на приватку"

    def loop(self):
        last_notice = None
        try:
            while not self.stop.is_set():
                try:
                    state = self.exchange()
                    if state["run"]!=self.run:
                        self.reset(state)
                    if state.get("summon"):
                        self.status = self.join_private(state["summon"])
                    elif self.run:
                        self.status = self.tick(state)
                    else:
                        self.status = "На связи · жду матч"
                except (Wait,OSError,ValueError,RuntimeError) as exc:
                    self.status = str(exc)
                if self.status != last_notice:
                    self.notify(self.status)
                    last_notice = self.status
                self.stop.wait(.38)
        finally:
            self.ocr.close()
