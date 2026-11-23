"""One foreground Roblox client. All game input is serialized in this worker."""
import re
import time

import numpy as np
from PIL import ImageGrab
from pynput import mouse

import twd_bot as farm
from wastelands_team import ABILITIES, PLACEMENT_ORDER, Wait, placement_label, position, private_server_links
from wastelands_view import OCR, color_boxes, invite_buttons, label, read_invite, map_point, preview, road_pose, scene, screen_point, tracked_pose


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
        rect = self.rect()
        target = self.to_screen(point)
        # Roblox updates its hover target on a movement event in some RDP sessions.
        self.hover(point)
        self.sleep(.20)
        frame = self.grab()
        live = invite_buttons(frame)
        if not live or any(abs(a-b)*size > 3 for a,b,size in zip(point,live[1],frame.size)):
            raise Wait("Приглашение изменилось · проверяю снова")
        self.check()
        if self.rect() != rect:
            raise Wait("Окно Roblox переместилось · проверяю приглашение снова")
        if any(abs(a-b)>3 for a,b in zip(self.m.position,target)):
            raise Wait("Курсор не попал на «Принять» · повторяю наведение")
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
        self.player, self.slots = connection.player, slots
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
        self.voted = state["progress"].get("voted",False)
        self.ready = state["progress"].get("ready",False)
        self.invited = state["progress"].get("invited",False)
        self.last_invite = None
        self.invite_attempts = 0
        self.placed = set()
        self.attempt = dict.fromkeys(PLACEMENT_ORDER, 0)
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

    def lobby(self, state, img):
        now = time.monotonic()
        if self.last_invite is not None and now-self.last_invite > 45:
            self.last_invite = None
            self.invite_attempts = 0
        if (self.invited and self.game.ready_visible()) or (self.placed and self.game.money() is not None):
            self.phase = "battle"
            self.game.camera_top_down()
            return "Подготовка расстановки"
        vote = self.game.vote_point(state["mode"])
        if vote and not self.invited:
            if self.last_invite is None:
                return "Ожидаю группу Wastelands от основы"
            self.confirm_group()
        if vote and not self.voted:
            self.game.click(vote)
            self.voted = True
            self.exchange("voted")
            return "Нажат VOTE · "+state["mode"].upper()
        if vote or self.voted:
            return "Жду READY"
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
        return "Жду приглашение или голосование"

    def update_places(self,state):
        own = {p["unit"]:p for p in state["places"] if p["player"]==self.player}
        if not all(unit in own for unit in PLACEMENT_ORDER):
            raise Wait("Основа не передала десять мест. Обнови основу до 6.0.4.")
        self.placed = {u for u,p in own.items() if p["state"]=="placed"}
        self.points = {u:p["point"] for u,p in own.items() if u in self.placed}
        if self.confirm:
            op,unit,point = self.confirm
            self.exchange(op,unit=unit,point=point)
            self.confirm = None
            return True
        if any(p.get("target") for p in own.values()):
            raise Wait("Проверь постановку в игре и открой «Резервы» на основе")
        return False

    def place(self, unit, img):
        prices = farm.read_hotbar(img)
        slot = self.slots[unit.partition("_")[0]]
        name = placement_label(unit)
        # Associate the physical card with its slot even when another price is unreadable.
        center = (.313 + (slot-1)*.072)
        price = next((v for x,v in prices if abs(x-center)<.032 and v),None)
        cash = self.game.money()
        if price is None or cash is None or cash < price:
            return f"Жду {name} · баланс {cash}, цена слота {slot}: {price}"
        if self.attempt[unit]>=5:
            return f"{name}: пять точек заняты; проверь разметку"
        if not self.game.take(slot):
            return "Не появилась подсветка дороги"
        try:
            self.game.hover(farm.IDLE_POINT)
            snap = self.game.grab()
            pose = road_pose(snap)
            if pose is None:
                return "Не узнал поворот Wastelands"
            point = position(self.player,unit,self.attempt[unit])
            pt = screen_point(pose,point)
            if not (.015<pt[0]<.985 and .10<pt[1]<.92) or (.27<pt[0]<.74 and pt[1]>.81):
                return "Место закрыто интерфейсом или вне кадра"
            try:
                self.exchange("reserve",unit=unit,point=point)
            except Wait as e:
                if "занят" in str(e) or "Зона ранней защиты основы" in str(e):
                    self.attempt[unit]+=1
                raise
            self.game.click(pt)
            self.game.sleep(.40)
            after = self.game.money()
            gone = not self.game.path_visible()
            self.game.sleep(.12)
            gone = gone and not self.game.path_visible()
            spent = after is not None and cash-after >= .8*price
            if gone and spent:
                self.game.holding = None
                self.confirm = ("commit",unit,point)
                self.exchange("commit",unit=unit,point=point)
                self.confirm = None
                self.placed.add(unit)
                self.pose,self.reference = pose,self.game.grab()
                return f"Поставил {name}"
            if not gone and after is not None and after>=cash:
                self.confirm = ("release",unit,point)
                self.exchange("release",unit=unit,point=point)
                self.confirm = None
                self.attempt[unit]+=1
                return "Точка занята · пробую рядом"
            return f"Проверь {name}: результат клика не подтверждён"
        finally:
            self.game.drop()

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
                    current = road_pose(self.game.grab())
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

    def tick(self,state):
        self.guard()
        img = self.game.grab()
        if self.needs_close:
            self.close_manager()
        if farm.afk_panel(img):
            return "Проверка в игре · жду ручного ответа"
        if farm.is_end_image(farm.crop_frac(img,farm.END_BOX)):
            self.phase = "end"
        if self.phase=="end":
            return "Матч завершён · жду следующий матч"
        if self.update_places(state):
            return "Состояние постановки синхронизировано"
        if state["progress"]["retry"]!=self.retry:
            self.attempt = dict.fromkeys(PLACEMENT_ORDER, 0)
            self.retry = state["progress"]["retry"]
        if self.phase=="lobby":
            return self.lobby(state,img)
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
        if "plunger" in self.placed and not self.ready:
            if self.game.ready_visible():
                self.game.click(farm.READY_POINT)
            self.ready = True
            self.exchange("ready")
            return "Plunger поставлен · READY"
        for unit in PLACEMENT_ORDER:
            if unit not in self.placed:
                return self.place(unit,img)
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
                self.notify(self.status)
                self.stop.wait(.38)
        finally:
            self.ocr.close()
