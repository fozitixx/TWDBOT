"""One foreground Roblox client. All game input is serialized in this worker."""
import math
import re
import time
from dataclasses import dataclass

import numpy as np
from PIL import Image, ImageDraw, ImageGrab, ImageOps
from pynput import mouse

import twd_bot as farm
from wastelands_manager import manager_bounds, titan_cards, upgrade_price
from wastelands_team import (ABILITIES, BANK_OFFSET, EARLY, EARLY_CLEARANCE, TITAN_CLEARANCE, REJECTION_SECONDS,
                            PLACEMENT_ORDER, SPARE_BANKS, Wait, bank_slot, footprint_class, near_rejection, placement_conflict,
                            on_third_titan_bank, placement_label, position, private_server_links, recent_sites)
from wastelands_view import (OCR, color_boxes, framing_turn, invite_buttons, label, read_invite, map_point, preview,
                            perimeter_points, rank_build_sites, placement_in_view, placement_pose, mission_button, ready_button,
                            recover_third_bank_pose, visual_slot_count, wastelands_slots, scene, screen_point, tracked_pose)


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
            # After mouse-down a network interruption cannot mean "never clicked".
            time.sleep(.15)
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


MANAGER_TITLES = {
    "scientistscreenman":"tv", "scientisttvman":"tv",
    "herocamcorderman20":"plunger", "plungercameraman20":"plunger",
    "titanamplifierman":"amplifier", "titanscreenman":"screen",
    "scientistcamcorderman":"farm", "scientistcameraman":"farm",
    "titancamcorderman":"tcam",
}

@dataclass(frozen=True)
class UnitCounts:
    """Two independent counters for one player's serialized placement."""
    slot: int | None = None
    total: int | None = None

    def delta(self, after):
        changes = {new-old for old,new in ((self.slot,after.slot),(self.total,after.total))
                   if old is not None and new is not None}
        return changes.pop() if len(changes)==1 else None

    def known(self):
        return self.slot is not None or self.total is not None

    def __str__(self):
        return ", ".join(f"{name} {value}" for name,value in (("слот",self.slot),("UNITS",self.total))
                         if value is not None) or "не прочитано"


def manager_total(words):
    """Read UNITS N as one label, even if OCR splits its words."""
    for text,x,y,w,h in words:
        token = text.casefold().strip()
        labels = ("units","юниты","юнитов","единицы")
        if not token.startswith(labels):
            continue
        if token.rstrip(":") in labels:
            following = sorted((v for v in words if x+w-.003<=v[1]<x+w+max(.025,h)
                                and abs(v[2]+v[4]/2-y-h/2)<h*.55),key=lambda v:v[1])
            if following:
                token += following[0][0]
        hit = re.fullmatch(r"(?:units|юниты|юнитов|единицы)\s*:?\s*(\d{1,2})",token)
        if hit:
            return int(hit[1])
    return None


def visual_manager_total(panel):
    """Read the numeric suffix of UNITS, anchored by the two footer buttons."""
    footer = farm.crop_frac(panel,(.035,.91,.965,.992))
    r,g,b = np.asarray(footer.convert("RGB"),dtype=np.int16).transpose(2,0,1)
    mid = footer.width//2
    green = (g>60)&(g-r>25)&(g-b>18)
    red = (r>60)&(r-g>28)&(r-b>22)
    if green[:,:mid].any(axis=0).mean()<.58 or red[:,mid:].any(axis=0).mean()<.58:
        return None
    header = farm.crop_frac(panel,(.014,.044,.28,.091)).convert("RGB")
    white = np.asarray(header).min(axis=2)
    readings = []
    for threshold in (110,123,150,172,200):
        mask = white>threshold
        ys = np.flatnonzero(mask.any(axis=1))
        if not len(ys):
            continue
        height = ys[-1]-ys[0]+1
        runs = farm._runs(mask.any(axis=0))
        # The title is several letters wide. Space before the number is
        # wider than letter spacing; the suffix occupies one or two digits.
        gaps = [(left-runs[i-1][1],left) for i,(left,_) in enumerate(runs) if i>=5
                and 2*height<runs[i-1][1]-runs[0][0]<7*height
                and runs[-1][1]-left<=2.1*height]
        if not gaps:
            continue
        gap,left = max(gaps)
        if not .16*height<=gap<=1.3*height or height<6:
            continue
        total = farm._read_green_number(mask[:,left:],tol=.16 if threshold<130 else .13,dollar=False)
        if total is None or total>99:
            continue
        readings.append(total)
    return readings[0] if len(readings)>=2 and len(set(readings))==1 else None


def manager_unit_count(words, kind, limit, total=None):
    """Words use panel-local coordinates. An incomplete list cannot prove zero."""
    if total is None:
        if not label(words,"UNIT MANAGER",(0,0,1,.10)):
            return None
        total = manager_total([v for v in words if v[1]<.28 and v[2]<.12])
    if total is None:
        return None
    def lines(left,top,right,bottom):
        inside = sorted((v for v in words if left<=v[1]+v[3]/2<right
                         and top<=v[2]+v[4]/2<bottom),key=lambda v:v[2]+v[4]/2)
        while inside:
            first = inside[0]
            mid = first[2]+first[4]/2
            row = [v for v in inside if abs(v[2]+v[4]/2-mid)<max(first[4],v[4])*.55]
            inside = [v for v in inside if v not in row]
            yield re.sub(r"[^a-z0-9]","","".join(v[0].lower() for v in sorted(row,key=lambda v:v[1])))
    cards = [MANAGER_TITLES[line] for left in (0,.5)
             for line in lines(left,.116,left+.5,.92) if line in MANAGER_TITLES]
    count = cards.count(kind)
    if count<=limit and len(cards)<=total and (len(cards)==total or count==limit):
        return count
    return None


def placement_cash(frame, read):
    region = farm.crop_frac(frame,farm.MONEY_REGION)
    cash = farm.read_money_image(region)
    if cash is not None:
        return cash
    # Isolate the amount next to the banknote. Glowing green road arrows on
    # Wastelands otherwise join the digits, particularly on compressed RDP frames.
    r,g,b = np.asarray(region.convert("RGB"),dtype=np.int16).transpose(2,0,1)
    green = (g>110)&(g-r>30)&(g-b>30)
    icon = farm._find_icon(green[:,:region.width//2])
    if icon is None:
        return None
    top,bottom,right = icon
    height = bottom-top+1
    ink = (g>116)&(g-r>19)&(g-b>18)&(r>52)&(b>51)&(np.abs(r-b)<28)&(g-r<108)
    band = ink[max(0,top-height//4):bottom+height//3+1, right+1:right+9*height]
    if not band.any():
        return None
    cash = farm._read_green_number(band,tol=farm.MONEY_TOL)
    if cash is not None:
        return cash
    digits = ImageOps.expand(Image.fromarray(np.where(band,0,255).astype(np.uint8)),4,fill=255)
    words = read(digits,zoom=5)
    value = "".join(v[0] for v in words).replace(" ","")
    if re.fullmatch(r"\$(?:\d{1,3}(?:,\d{3})+|\d{1,7})",value):
        return int(value[1:].replace(",",""))
    return None


def preserve_bank_capacity(ranked,needed,clearance=EARLY_CLEARANCE):
    """Prefer a base that leaves space for the other helpers' remaining towers."""
    if needed<=1:
        return ranked
    coords = np.asarray(ranked)
    nearby = ((coords[:,None]-coords)**2).sum(axis=2)<clearance**2
    free = np.ones(len(coords),dtype=bool)
    degree = nearby.sum(axis=1)
    packing = []
    while free.any():
        # Claim an endpoint before a midpoint that would consume two bases.
        index = np.argmin(np.where(free,degree,len(coords)+1))
        packing.append(index)
        removed = free & nearby[index]
        degree -= nearby[:,removed].sum(axis=1)
        free[removed] = False
    lost = nearby[:,packing].sum(axis=1)
    budget = max(1,len(packing)-needed+1)
    return [ranked[i] for i in np.argsort(lost>budget,kind="stable")]


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
        self.at_limit = set()
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
        self.points = {}
        self.team_places = state.get("places",[])
        self.sites = {}
        self.preferred_titans = {}
        self.failed_titan_sites = {}
        self.rescan_at = {}
        self.local_rejections = {}
        self.team_rejections = state.get("rejected_sites",())
        self.search_log_at = {}
        self.next_status_log = 0
        self.host_sites = state.get("placement_sites",False)
        self.host_totals = state.get("placement_totals",False)
        self.pending_places = set()
        self.last_inventory = None
        self.manager_until = {}
        self.unchanged = None
        self.next_check = 0
        self.read_delay = 0
        self.wait_status = ""
        self.ocr_retry = 0
        self.funded_lease = None
        self.retry = state["progress"].get("retry",0)
        self.levels = {"amplifier":None,"screen":None}
        self.upgrade_note = ""
        self.upgrade_cost = None
        self.check_price_at = 0
        self.next_upgrade = 0
        self.game.holding = None
        self.pose = self.shot = None
        self.reference = None
        self.next_pose_fit = 0
        self.turn_scale = None
        self.last_turn = None
        self.next_turn_at = 0
        self.max_turn = 90
        self.failed_heading = None
        self.confirm = None
        self.needs_close = False

    def text(self, img, box=(0,0,1,1)):
        return self.ocr.read(img,box)

    def placement_text(self,img,box=(0,0,1,1),*,zoom=2):
        if time.monotonic()<self.ocr_retry:
            return []
        try:
            return self.ocr.read(img,box,zoom=zoom)
        except (OSError,RuntimeError) as exc:
            self.ocr_retry = time.monotonic()+8
            farm.log(f"Wastelands · твинк {self.player} · OCR: {exc}")
            return []

    def wait_for_check(self,message,delay=None):
        if delay is None:
            self.read_delay = min(8,max(1,2*self.read_delay))
            delay = self.read_delay
            message += f" · повтор через {delay} с"
        self.next_check = time.monotonic()+delay
        self.wait_status = message
        return message

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
        at_ready = (self.invited or self.voted) and (img is not None and ready_button(img) or self.game.ready_visible())
        in_battle = False
        if not at_ready and img is not None and (self.ready or self.voted or self.placed or self.pending_places):
            words = self.placement_text(img,(.23,.043,.51,.16),zoom=3)
            in_battle = bool(re.search(r"(?:wave|волна)\d{1,2}/(?:25|30)\b",
                                       "".join(v[0] for v in words).replace(" ",""),re.I))
            if not in_battle and (self.placed or self.pending_places):
                in_battle = self.game.money() is not None
        if at_ready or in_battle:
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
        previous = self.team_places
        self.team_places = state["places"]
        self.team_rejections = state.get("rejected_sites",())
        own = {p["unit"]:p for p in self.team_places if p["player"]==self.player}
        if not all(unit in own for unit in PLACEMENT_ORDER):
            raise Wait("Основа не передала десять мест. Обнови основу до 6.0.4.")
        placed = {u for u,p in own.items() if p["state"]=="placed"}
        pending = {u for u,p in own.items() if p.get("target")}
        if placed!=self.placed or self.pending_places-pending:
            # A manual decision on the host invalidates our previous observation.
            self.last_inventory = self.unchanged = None
            self.next_check = self.read_delay = 0
            self.manager_until.clear()
        self.placed = placed
        self.points = {u:p["point"] for u,p in own.items() if u in self.placed}
        if self.confirm:
            op,unit,point,since,site_failed = self.confirm
            if own[unit].get("target")==point and (since is None or own[unit].get("target_since")==since):
                self.exchange(op,unit=unit,point=point,target_since=since,site_failed=site_failed)
            self.confirm = None
            return True
        cleared = self.pending_places-pending-self.placed
        for row in previous:
            if row["player"]==self.player and row["unit"] in cleared and row.get("target"):
                self.local_rejections.setdefault((footprint_class(row["unit"]),tuple(row["target"])),
                                                 time.monotonic()+8)
        self.pending_places = pending
        return False

    def placement_sites(self,unit):
        if unit not in self.sites:
            if self.host_sites:
                plan = self.exchange("placement_sites",unit=unit)
                sites = plan["sites"]
                if self.player==3 and unit in ("amplifier","screen"):
                    sites = [p for p in sites if on_third_titan_bank(p)]
                    if not sites:
                        raise Wait("Основа передала старую зону титанов твинка 3. Обнови основу до 6.0.23 или новее.")
                self.sites[unit] = sites
                if unit in ("amplifier","screen") and plan.get("preferred_site"):
                    self.preferred_titans[unit] = plan["preferred_site"]
            else:
                locate = bank_slot if unit.partition("_")[0] in EARLY else position
                # Older coordinators only know the original five titan candidates.
                count = 5+len(SPARE_BANKS) if unit.partition("_")[0] in EARLY else 5
                self.sites[unit] = [locate(self.player,unit,i) for i in range(count)]
        return self.sites[unit]

    @staticmethod
    def slot_center(frame,slot):
        return .5 + (slot-3.5)*.13*frame.height/frame.width

    def slot_icon(self,frame,slot):
        h = frame.height
        x = self.slot_center(frame,slot)*frame.width
        return frame.crop((round(x-.046*h),round(.854*h),round(x+.046*h),round(.897*h)))

    def slot_count(self,frame,slot,limit):
        gray = self.slot_icon(frame,slot).convert("L")
        for threshold in (155,135,120):
            mask = ImageOps.expand(gray.point(lambda v: 255 if v>=threshold else 0),1,fill=255)
            ImageDraw.floodfill(mask,(0,0),0)
            count = visual_slot_count(mask,limit)
            if count is not None:
                return count
        return None

    def hover_count(self,slot,limit):
        rect = self.game.rect()
        frame = self.game.grab()
        if farm.afk_panel(frame):
            raise Wait("Проверка AFK на экране")
        self.game.hover((self.slot_center(frame,slot),.875))
        self.game.sleep(.16)
        previous = None
        frames = []
        for attempt in range(4):
            if attempt:
                self.game.sleep(.12)
            frame = self.game.grab()
            if self.game.rect()!=rect or farm.afk_panel(frame):
                raise Wait("Игровое окно изменилось во время проверки слота")
            count = self.slot_count(frame,slot,limit)
            if count is not None and count==previous:
                return count
            previous = count
            frames.append(frame)
        # Do the inexpensive visual pass before calling Windows OCR. Only two
        # recent, independently captured fractions with the right limit can agree.
        observed = []
        for frame in frames[-2:]:
            icon = self.slot_icon(frame,slot)
            words = self.placement_text(icon,zoom=5)
            digits = "".join(v[0] for v in words).replace(" ","")
            digits = digits.translate(str.maketrans({"O":"0","o":"0","I":"1","l":"1"}))
            hit = re.fullmatch(r"([0-4])/"+str(limit),digits)
            if not hit or int(hit[1])>limit:
                return None
            observed.append(int(hit[1]))
        return observed[0] if observed[0]==observed[1] else None

    def manager_counts(self,kind,limit,*,cards):
        frame = self.game.grab()
        if farm.afk_panel(frame):
            raise Wait("Проверка AFK на экране")
        self.game.drop()
        self.needs_close = True
        try:
            if not manager_bounds(frame) and not self.header(frame):
                self.game.key("v")
                self.game.sleep(.22)
            previous = UnitCounts()
            for attempt in range(3):
                if attempt:
                    self.game.sleep(.13)
                frame = self.game.grab()
                if farm.afk_panel(frame):
                    raise Wait("Проверка AFK на экране")
                bounds = manager_bounds(frame)
                panel = None
                total = count = None
                if bounds:
                    x,y,w,h = bounds
                    panel = frame.crop((x,y,x+w,y+h))
                    total = visual_manager_total(panel)
                    if total is None:
                        total = manager_total(self.placement_text(panel,(0,.035,.29,.115),zoom=4))
                    if limit==1 and kind in titan_cards(frame,self.placement_text,bounds):
                        count = 1
                if total is None and count is None:
                    words = self.placement_text(frame,(0,0,1,.32))
                    if label(words,"UNIT MANAGER"):
                        total = manager_total(words)
                if total==0 and count is None:
                    count = 0
                elif cards and count is None and total and panel is not None:
                    count = manager_unit_count(self.placement_text(panel),kind,limit,total)
                current = UnitCounts(count,total)
                if total is not None and count is not None and total<count:
                    current = UnitCounts()
                if current.known() and current==previous:
                    return current
                if total is not None and previous.total==total and current.total==total:
                    return UnitCounts(None,total)
                previous = current
            return UnitCounts()
        finally:
            self.close_manager()

    def placement_baseline(self,kind,slot,limit):
        # An observed result is the next baseline while this worker has kept
        # exclusive control. Reacquire on a stage change, manual edit or idle gap.
        recent_total = None
        if self.last_inventory:
            last_kind,expires,reading = self.last_inventory
            if time.monotonic()<expires:
                if last_kind==kind:
                    return reading
                recent_total = reading.total
        count = self.hover_count(slot,limit)
        confirmed = sum(u.partition("_")[0]==kind for u in self.placed)
        if count is not None and count<confirmed:
            count = None
        if count==limit or (count is not None and not self.host_totals):
            return UnitCounts(count)
        # A stale zero can persist over the icon after a titan was placed.
        # After a rejected titan click, consult the actual roster before another.
        verify_titan = limit==1 and bool(self.failed_titan_sites)
        if recent_total is not None and not verify_titan:
            if count is not None and recent_total>=count:
                return UnitCounts(count,recent_total)
            if count is None and recent_total==len(self.placed):
                # Every unit in the calibrated roster belongs to a confirmed row.
                return UnitCounts(confirmed,recent_total)
        manager = self.manager_counts(kind,limit,cards=count is None)
        if limit==1 and manager.slot==1:
            return UnitCounts(1,manager.total if self.host_totals else None)
        if manager.slot is not None and manager.slot<confirmed:
            return UnitCounts()
        if count is None:
            if manager.total is not None:
                self.manager_until[kind] = time.monotonic()+12
            count = manager.slot
        if manager.total is not None and manager.total<max(len(self.placed),count or 0):
            return UnitCounts()
        reading = UnitCounts(count,manager.total if self.host_totals else None)
        if reading.known():
            self.last_inventory = (kind,time.monotonic()+8,reading)
        return reading

    def placement_readback(self,kind,slot,before,double_check):
        limit = 4 if kind in EARLY else 1
        manager = None
        if before.total is not None and (before.slot is None or time.monotonic()<self.manager_until.get(kind,0)):
            manager = self.manager_counts(kind,limit,cards=False)
            if before.delta(manager) in (0,1) or before.slot is None:
                return manager
        count = self.hover_count(slot,limit)
        if manager is None:
            if count is not None and (count==before.slot+1 or count==before.slot and not double_check):
                return UnitCounts(count)
            manager = self.manager_counts(kind,limit,cards=before.total is None)
        if count is None and manager.total is not None:
            self.manager_until[kind] = time.monotonic()+12
        elif count is not None:
            self.manager_until.pop(kind,None)
        if count is not None and manager.slot is not None and count!=manager.slot:
            if (limit==1 and manager.slot==1 and before.slot==0 and before.total is not None
                    and manager.total==before.total+1):
                return manager
            return UnitCounts()
        return UnitCounts(count if count is not None else manager.slot,manager.total)

    def recheck_pending(self,state):
        row = next((p for p in state["places"] if p["player"]==self.player
                    and p.get("target") and p["state"]!="placed"),None)
        if row is None:
            return None
        unit,point = row["unit"],row["target"]
        kind = unit.partition("_")[0]
        name = placement_label(unit)
        before = UnitCounts(row.get("count_before"),row.get("total_before"))
        if not before.known():
            return f"{name} · нет исходного счётчика. Проверь точку в «Места юнитов»"
        key = (unit,tuple(point),row.get("target_since"))
        second = self.unchanged==key
        after = self.placement_readback(kind,row.get("slot") or self.slots[kind],before,second)
        delta = before.delta(after)
        if delta not in (0,1):
            self.unchanged = None
            if not self.read_delay:
                farm.log(f"Wastelands · твинк {self.player} · {name} · ожидание: {before} → {after}")
            return self.wait_for_check(f"{name} · сверяю постановку по слоту и UNITS")
        if delta==0 and not second:
            self.unchanged = key
            return self.wait_for_check(f"{name} · счётчик прежний, жду обновления игры",1.1)

        op = "commit" if delta else "release"
        since = row.get("target_since")
        funded = self.funded_lease==key
        if not delta:
            cooldown = REJECTION_SECONDS if funded else 18
            self.local_rejections[footprint_class(unit),tuple(point)] = time.monotonic()+cooldown
            if kind not in EARLY and funded:
                site = tuple(point)
                self.failed_titan_sites[site] = self.failed_titan_sites.get(site,0)+1
        self.confirm = (op,unit,point,since,not delta and funded)
        self.exchange(op,unit=unit,point=point,target_since=since,site_failed=not delta and funded)
        self.confirm = None
        self.funded_lease = None
        self.unchanged = None
        self.pending_places.discard(unit)
        self.next_check = self.read_delay = 0
        if delta:
            self.placed.add(unit)
            self.points[unit] = point
        # Carry a calibrated total across consecutive confirmed changes only.
        # Never derive it from reserved places, a balance change, or a click.
        count = after.slot if after.slot is not None else (before.slot+delta if before.slot is not None else None)
        total = after.total if after.total is not None else (before.total+delta if before.total is not None else None)
        self.last_inventory = (kind,time.monotonic()+8,UnitCounts(count,total if self.host_totals else None))

        evidence = f"слот {after.slot}" if before.slot is not None and after.slot is not None else f"UNITS {before.total} → {after.total}"
        farm.log(f"Wastelands · твинк {self.player} · {name} · {op} · {evidence}")
        if delta:
            return f"Поставил {name} · {evidence}"
        if not funded:
            return self.wait_for_check(f"{name} · число прежнее, перепроверю средства и место",1)
        return f"{name} · число прежнее, пробую другую точку"

    def map_pose(self,snap):
        rect = self.game.rect()
        can_track = self.reference is not None and self.reference_rect==rect and self.reference.size==snap.size
        now = time.monotonic()
        if can_track and now<self.next_pose_fit:
            current = tracked_pose(self.reference,self.pose,snap)
            if current is not None:
                return current
        current = placement_pose(snap)
        if current is None and self.player==3:
            current = recover_third_bank_pose(snap)
        if current is not None:
            # Only a fresh landmark fit becomes the reference. Tracking always
            # starts at that frame, so motion between attempts cannot accumulate.
            self.reference,self.pose,self.reference_rect = snap,current,rect
            self.next_pose_fit = now+12
        elif can_track:
            current = tracked_pose(self.reference,self.pose,snap)
        if current is not None and self.last_turn:
            old_heading,pixels,angle = self.last_turn
            change = (self.camera_heading(current,snap.size)-old_heading+180)%360-180
            if abs(change)>3 and .3<abs(pixels/change)<90:
                self.turn_scale = pixels/change
                self.max_turn = min(90,max(20,2*abs(angle)))
            self.last_turn = None
        return current

    @staticmethod
    def camera_heading(pose,size):
        x,y = pose[1][:,0]*size
        return math.degrees(math.atan2(y,x))

    def reframe_sites(self,unit,frame,pose,sites):
        now = time.monotonic()
        if now<self.next_turn_at:
            return False
        if unit.partition("_")[0] in EARLY:
            sites = [[v+BANK_OFFSET*n for v,n in zip(center,normal)] for center,_,normal in sites]
        recent = recent_sites(self.local_rejections,now) + list(self.team_rejections)
        free = [point for point in sites if not placement_conflict(self.player,unit,point,self.team_places)
                and not near_rejection(unit,point,recent)]
        heading = self.camera_heading(pose,frame.size)
        avoid_sign = 0
        if self.failed_heading:
            failed,sign,until = self.failed_heading
            if now<until and abs((heading-failed+180)%360-180)<12:
                avoid_sign = sign
        radius = TITAN_CLEARANCE//2 if self.player==3 and unit in ("amplifier","screen") else 0
        angle = framing_turn(pose,free,frame.size,avoid_sign,radius=radius)
        angle = max(-self.max_turn,min(self.max_turn,angle))
        if not angle or farm.afk_panel(self.game.grab()):
            return False
        scale = self.turn_scale if self.turn_scale is not None else self.game.px_per_deg
        pixels = round(angle*scale)
        self.game.drop()
        self.game.turn_camera(pixels)
        self.last_turn = heading,pixels,angle
        self.next_turn_at = now+6
        self.next_pose_fit = 0
        self.rescan_at.clear()
        return True

    def candidate_sites(self,unit,frame,pose,sites):
        early = unit.partition("_")[0] in EARLY
        if early:
            measured = perimeter_points(frame,pose,sites)
            center,_,normal = sites[0]
            home = [v+BANK_OFFSET*n for v,n in zip(center,normal)]
        else:
            measured = sites
            home = sites[0]
        recent = recent_sites(self.local_rejections,time.monotonic()) + list(self.team_rejections)
        other_plans = [p["point"] for p in self.team_places if early and p["state"]!="placed"
                       and not p.get("target") and p["unit"].partition("_")[0] in EARLY
                       and (p["player"],p["unit"])!=(self.player,unit)]
        visible = busy = rejected = 0
        available,preference = [],[]
        unique = dict.fromkeys(tuple(p) for p in measured if p is not None)
        for point in unique:
            x,y = screen_point(pose,point)
            if not placement_in_view(x,y):
                continue
            visible += 1
            if placement_conflict(self.player,unit,point,self.team_places):
                busy += 1
                continue
            if near_rejection(unit,point,recent):
                rejected += 1
                continue
            available.append(list(point))
            # Prefer the unit's assigned part of the bank and leave open planned
            # sites to their owners when equally clear ground is available.
            cost = min(math.dist(point,home)/250,1)*(.50 if early else .20)
            if not early:
                learned = self.preferred_titans.get(unit)
                if learned and math.dist(point,learned)<1:
                    cost -= .42
            if any(math.dist(point,p)<EARLY_CLEARANCE for p in other_plans):
                cost += .24
            preference.append(cost)
        check_ground = self.player==3 and not early
        radius = TITAN_CLEARANCE//2 if check_ground else (12 if early else 24)
        ranked = rank_build_sites(frame,pose,available,radius,preference,clear_titan_base=check_ground)
        obstructed = len(available)-len(ranked)
        if not early and self.failed_titan_sites:
            # The team cooldown expires, but this helper still explores unused
            # ground before retrying the exact same wreck later in this match.
            ranked.sort(key=self.titan_misses)
        if early and len(ranked)>1:
            needed = sum(p["unit"].partition("_")[0] in EARLY and p["state"]!="placed" and not p.get("target")
                         for p in self.team_places)
            ranked = preserve_bank_capacity(ranked,needed)
        elif check_ground and len(ranked)>1:
            other = "screen" if unit=="amplifier" else "amplifier"
            if any(p["player"]==self.player and p["unit"]==other and p["state"]!="placed"
                   and not p.get("target") for p in self.team_places):
                ranked = preserve_bank_capacity(ranked,2,TITAN_CLEARANCE)
        return ranked,visible,busy,rejected,obstructed

    def titan_misses(self,point):
        return sum(count for site,count in self.failed_titan_sites.items() if math.dist(point,site)<25)

    def place(self,unit,img):
        kind = unit.partition("_")[0]
        slot = self.slots[kind]
        name = placement_label(unit)
        center = self.slot_center(img,slot)
        price = next((v for x,v in farm.read_hotbar(img) if abs(x-center)<.032 and v),None)
        if kind in EARLY and any(other!=kind and price==farm.UNITS[other]["price"] for other in EARLY):
            return self.wait_for_check(f"{name} · в слоте {slot} видна цена другого юнита",2)
        if price is None:
            price = farm.UNITS[kind]["price"] if kind in EARLY else {"amplifier":7000,"screen":7750}[kind]
        cash = placement_cash(img,self.placement_text)
        if cash is not None and cash<price:
            return self.wait_for_check(f"Жду {name} · есть ${cash:,}, нужно ${price:,}",.8)

        limit = 4 if kind in EARLY else 1
        before = self.placement_baseline(kind,slot,limit)
        if before.slot==limit:
            self.at_limit.add(kind)
            return f"{name} · в игре уже {limit}/{limit}"
        if not before.known():
            return self.wait_for_check(f"{name} · жду счётчик слота {slot} или UNITS")
        self.read_delay = 0
        sites = self.placement_sites(unit)
        if not self.game.take(slot):
            return self.wait_for_check(f"{name} · жду подсветку дороги",1)
        try:
            self.game.hover(farm.IDLE_POINT)
            snap = self.game.grab()
            pose = self.map_pose(snap)
            if pose is None:
                if self.last_turn and not farm.afk_panel(snap):
                    heading,pixels,angle = self.last_turn
                    self.game.drop()
                    self.game.turn_camera(-pixels)
                    self.last_turn = None
                    self.max_turn = max(10,abs(angle)//2)
                    if abs(angle)<=20:
                        self.failed_heading = heading,(1 if angle>0 else -1),time.monotonic()+30
                    self.next_pose_fit = 0
                    return self.wait_for_check(f"{name} · вернул камеру, повторно сверяю дорогу",.8)
                return self.wait_for_check(f"{name} · сверяю положение камеры по дороге и обломкам",1)
            candidates,visible,busy,rejected,obstructed = self.candidate_sites(unit,snap,pose,sites)
            if kind not in EARLY and self.failed_titan_sites and (not candidates or self.titan_misses(candidates[0])):
                unexplored = [point for point in sites if not self.titan_misses(point)]
                if unexplored and self.reframe_sites(unit,snap,pose,unexplored):
                    return self.wait_for_check(f"{name} · повернул камеру к новому участку, сверяю карту",.5)
            for point in candidates:
                pt = screen_point(pose,point)
                try:
                    reserved = self.exchange("reserve",unit=unit,point=point,slot=slot,
                                             count_before=before.slot,total_before=before.total)
                except Wait as exc:
                    if any(reason in str(exc) for reason in
                           ("Рядом занят участок","Зона ранней защиты основы","Зона титанов основы")):
                        busy += 1
                        continue
                    if "недавно отклонила" in str(exc):
                        rejected += 1
                        continue
                    if "За пределами назначенной зоны" in str(exc):
                        if not self.host_sites:
                            raise Wait("Разметка основы и твинка различается · обнови и перезапусти оба приложения") from exc
                        continue
                    raise
                self.pending_places.add(unit)
                self.last_inventory = None
                since = next(p.get("target_since") for p in reserved["places"]
                             if p["player"]==self.player and p["unit"]==unit)
                self.funded_lease = (unit,tuple(point),since) if cash is not None and since is not None else None
                reference_scene = scene(snap)
                def live_point(frame):
                    if frame.size!=snap.size or farm.afk_panel(frame):
                        return None
                    if np.median(abs(scene(frame)-reference_scene))<4:
                        return pt
                    current = tracked_pose(snap,pose,frame)
                    return screen_point(current,point) if current is not None else None
                try:
                    self.game.click_live(pt,live_point,name)
                except Wait:
                    # Game.click_live checks its guard before sending mouse-down.
                    self.confirm = ("release",unit,point,since,False)
                    raise
                farm.log(f"Wastelands · твинк {self.player} · {name} · клик, слот {slot}, "
                         f"точка ({point[0]:.0f}, {point[1]:.0f}), {before}")
                return self.wait_for_check(f"{name} · проверяю результат клика",.60)
            now = time.monotonic()
            self.rescan_at[unit] = now+4
            message = f"{name} · участков в кадре {visible}, занято {busy}, недавних отказов {rejected}"
            if obstructed:
                message = f"{name} · ищу свободный песок в своей зоне · занято {busy}, помехи в {obstructed} точках"
            if now>=self.search_log_at.get(kind,0):
                farm.log(f"Wastelands · твинк {self.player} · {message}")
                self.search_log_at[kind] = now+12
            if self.reframe_sites(unit,snap,pose,sites):
                return self.wait_for_check(f"{name} · повернул камеру к свободному участку, сверяю карту",.5)
            return message
        finally:
            self.game.drop()

    def header(self, img):
        return label(self.placement_text(img,(0,0,1,.32)),"UNIT MANAGER")

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

    def read_titan_list(self,frame,required,upgrading):
        bounds = manager_bounds(frame)
        cards = titan_cards(frame,self.placement_text,bounds) if bounds else {}
        incomplete = upgrading and any(c.level is None or (c.level<8 and not c.button) for c in cards.values())
        if bounds and (not required.issubset(cards) or incomplete):
            # Rarity puts the titans first; an already selected sort may still
            # have a scroll offset from a previous manual visit.
            x,y,w,h = bounds
            fw,fh = frame.size
            header = (x/fw,y/fh,(x+w)/fw,(y+.105*h)/fh)
            words = self.placement_text(frame,header,zoom=4)
            sort = label(words,"Rarity") or label(words,"Редкость")
            if sort:
                self.game.click(sort)
            self.game.hover(((x+.5*w)/fw,(y+.40*h)/fh))
            self.game.m.scroll(0,12)
            self.game.sleep(.22)
            frame = self.game.grab()
            if farm.afk_panel(frame):
                raise Wait("Проверка AFK на экране")
            cards = titan_cards(frame,self.placement_text)
        return frame,cards

    def improve_titans(self,frame,cards,cash):
        for kind,card in cards.items():
            if card.level is not None:
                self.levels[kind] = card.level
        for kind in self.levels:
            if kind not in cards or cards[kind].level is None:
                return f"Сверяю карточку и уровень {kind.title()}"
        unit = min(self.levels,key=self.levels.get)
        card = cards[unit]
        old = card.level
        if old==8:
            return "Улучшения завершены"
        if not card.button:
            return f"Жду кнопку Upgrade у {unit.title()}"
        cost = upgrade_price(frame,card,self.placement_text)
        same_price = self.upgrade_cost==(unit,old,cost)
        if cost is not None and cash is not None and cash<cost and not (same_price and time.monotonic()>=self.check_price_at):
            self.upgrade_cost = (unit,old,cost)
            self.check_price_at = time.monotonic()+8
            return f"Коплю на {unit.title()} · нужно ${cost:,}"
        self.upgrade_cost = None
        def current(image):
            if farm.afk_panel(image) or image.size!=frame.size:
                return None
            live = titan_cards(image,self.placement_text).get(unit)
            if live and live.level==old and live.upgrade_contains(image,card.button):
                return card.button
            return None
        self.game.click_live(card.button,current,f"Upgrade {unit.title()}")
        for delay in (.20,.22,.30):
            self.game.sleep(delay)
            after = self.game.grab()
            if farm.afk_panel(after):
                break
            updated = titan_cards(after,self.placement_text).get(unit)
            if updated and updated.level is not None and updated.level!=old:
                self.levels[unit] = updated.level
                self.next_upgrade = time.monotonic()+.65
                message = (f"{unit.title()} · уровень {old} → {updated.level}" if updated.level==old+1
                           else f"Сверил {unit.title()} · в игре уровень {updated.level}")
                farm.log(f"Wastelands · твинк {self.player} · {message}")
                return message
        self.next_upgrade = time.monotonic()+2
        return f"Проверю результат Upgrade у {unit.title()}"

    def upgrade_tick(self,img):
        now = time.monotonic()
        if all(value==8 for value in self.levels.values()):
            self.upgrade_note = "Улучшения завершены"
        elif now>=self.next_upgrade:
            cash = placement_cash(img,self.placement_text)
            waiting = self.upgrade_cost
            self.next_upgrade = now+1.5
            if (waiting and self.levels[waiting[0]]==waiting[1] and cash is not None
                    and cash<waiting[2] and now<self.check_price_at):
                self.upgrade_note = f"Коплю на {waiting[0].title()} · ${cash:,} из ${waiting[2]:,}"
            else:
                self.upgrade_note = self.manager(None,"Upgrade",cash=cash)
        known = [f"{name.title()} ур. {value}/8" for name,value in self.levels.items() if value is not None]
        return " · ".join(["Титаны 2/2",*known,self.upgrade_note or "Сверяю уровни"])

    def manager(self, unit, action, target=None, *, cash=None):
        self.needs_close = True
        try:
            img = self.game.grab()
            if farm.afk_panel(img):
                raise Wait("Проверка AFK на экране")
            if not manager_bounds(img) and not self.header(img):
                self.game.key("v")
                self.game.sleep(.24)
                img = self.game.grab()
            if farm.afk_panel(img):
                raise Wait("Проверка AFK на экране")
            required = set(self.levels) if action=="Upgrade" else {unit}
            if not manager_bounds(img) and not self.header(img):
                return "Жду открытия Unit Manager"
            img,cards = self.read_titan_list(img,required,action=="Upgrade")
            if action=="Upgrade":
                return self.improve_titans(img,cards,cash)
            def ability_row(frame,card):
                if card:
                    box = tuple(v/s for v,s in zip(card.box,frame.size*2))
                    return self.placement_text(frame,box,zoom=4)
                # Older panels may be identified by their text and red outline.
                return manager_card(frame,self.placement_text(frame),unit) or []
            row = ability_row(img,cards.get(unit))
            button = label(row,action)
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
            frame=self.game.grab()
            after=ability_row(frame,titan_cards(frame,self.placement_text).get(unit))
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
        if self.phase!="battle" or (unit not in self.placed and unit not in self.at_limit):
            return {"result":"Титан ещё не поставлен"}
        live=self.game.grab()
        current=tracked_pose(self.reference,self.pose,live) if self.reference is not None else None
        if name in ("snapshot","Teleport") and unit not in self.points:
            return {"result":"Для переноса нужна подтверждённая точка Screen"}
        if current is not None and unit in self.points and name!="snapshot":
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
            self.confirm = (op,unit,point,None,False)
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
            self.at_limit.clear()
            self.manager_until.clear()
            self.next_check = self.read_delay = 0
            self.last_inventory = self.unchanged = None
            self.sites.clear()
            self.rescan_at.clear()
            self.local_rejections.clear()
            self.failed_titan_sites.clear()
            self.retry = state["progress"]["retry"]
        if self.phase=="lobby":
            return self.lobby(state,img)
        if (not self.ready and "ready" not in self.uncertain_votes
                and time.monotonic()>=self.vote_retry and ready_button(img)):
            return self.vote("ready")
        if time.monotonic()>=self.next_slot_check:
            detected = wastelands_slots(img)
            if detected and detected!=self.slots:
                farm.log(f"Wastelands · твинк {self.player} · слоты по карточкам: {detected}")
                self.slots = detected
                self.last_inventory = None
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
        now = time.monotonic()
        if now<self.next_check:
            return self.wait_status
        if self.pending_places:
            status = self.recheck_pending(state)
            if status:
                return status

        outstanding = [u for u in PLACEMENT_ORDER if u not in self.placed
                       and u.partition("_")[0] not in self.at_limit]
        # A different copy can use another bank, but TV must wait for all
        # Plungers, and both titans must wait for all TVs.
        if outstanding:
            first = outstanding[0].partition("_")[0]
            for unit in outstanding:
                if first in EARLY and unit.partition("_")[0]!=first:
                    break
                if unit in self.pending_places:
                    continue
                if now<self.rescan_at.get(unit,0):
                    continue
                return self.place(unit,img)
            area = "по периметру дороги" if first in EARLY else "в зоне титанов"
            return f"{placement_label(outstanding[0])} · повторю поиск {area}"
        return self.upgrade_tick(img)

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
                if self.run and self.phase=="battle" and time.monotonic()>=self.next_status_log:
                    farm.log(f"Wastelands · твинк {self.player} · {self.status}")
                    self.next_status_log = time.monotonic()+15
                if self.status != last_notice:
                    self.notify(self.status)
                    last_notice = self.status
                self.stop.wait(.38)
        finally:
            self.ocr.close()
