"""One foreground Roblox client. All game input is serialized in this worker."""
import json
import re
import secrets
import time
from urllib.error import HTTPError
from urllib.request import ProxyHandler, Request, build_opener

import cv2
import numpy as np
from PIL import ImageGrab
from pynput import mouse

import twd_bot as farm
from wastelands_team import ABILITIES, PORT, UNITS, position
from wastelands_view import OCR, label, map_point, preview, road_pose, scene, screen_point, tracked_pose


class Wait(Exception):
    pass


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


def manager_card(img, words, unit):
    name = {"amplifier":"Titan Amplifierman","screen":"Titan Screen Man"}[unit]
    title = label(words,name)
    if not title:
        return None
    rgb = np.asarray(img.convert("RGB")).astype(np.int16)
    r,g,b = rgb.transpose(2,0,1)
    mask = ((r>140)&(r-g>85)&(r-b>75)).astype(np.uint8)
    contours,_ = cv2.findContours(mask,cv2.RETR_LIST,cv2.CHAIN_APPROX_SIMPLE)
    w,h = img.size
    choices = []
    for c in contours:
        x,y,cw,ch = cv2.boundingRect(c)
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
    contours,_=cv2.findContours(cyan,cv2.RETR_LIST,cv2.CHAIN_APPROX_SIMPLE)
    boxes=[cv2.boundingRect(c) for c in contours]
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
    def __init__(self, addr, player, key, slots, stop, notify):
        self.url = f"http://{addr}:{PORT}/alt/{player}"
        self.http = build_opener(ProxyHandler({}))
        self.player,self.key,self.slots = player,key,slots
        self.stop,self.notify = stop,notify
        self.instance = secrets.token_hex(12)
        self.run = ""
        self.status = "Подключение"
        self.ocr = OCR()
        self.game = Game(self.guard)
        self.last_checked = 0
        self.deadline = None

    def exchange(self, op="poll", **fields):
        data = dict(instance=self.instance,run=self.run,status=self.status,op=op,**fields)
        req = Request(self.url,data=json.dumps(data).encode(),headers={"Authorization":"Bearer "+self.key,
                      "Content-Type":"application/json"})
        try:
            with self.http.open(req,timeout=3) as res:
                return json.load(res)
        except HTTPError as exc:
            with exc:
                if exc.code == 409:
                    raise Wait(json.load(exc)["error"]) from exc
                raise Wait(f"Ошибка сети {exc.code}; проверь номер и ключ") from exc

    def guard(self):
        if self.stop.is_set() or not self.run:
            raise Wait("Остановлено")
        if self.deadline is not None and time.monotonic()>=self.deadline:
            raise Wait("Время команды истекло")
        if time.monotonic()-self.last_checked>.45:
            if self.exchange()["run"] != self.run:
                raise Wait("Матч остановлен")
            self.last_checked = time.monotonic()

    def reset(self, state):
        self.run = state["run"]
        self.phase = "lobby"
        self.voted = state["progress"].get("voted",False)
        self.ready = state["progress"].get("ready",False)
        self.invited = state["progress"].get("invited",False)
        self.last_invite = 0
        self.placed = set()
        self.attempt = {u:0 for u in UNITS}
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

    def lobby(self, state, img):
        if (self.invited and self.game.ready_visible()) or (self.placed and self.game.money() is not None):
            self.phase = "battle"
            self.game.camera_top_down()
            return "Подготовка расстановки"
        vote = self.game.vote_point(state["mode"])
        if vote and not self.invited:
            return "Ожидаю группу Wastelands от основы"
        if vote and not self.voted:
            self.game.click(vote)
            self.voted = True
            self.exchange("voted")
            return "Нажат VOTE · "+state["mode"].upper()
        if vote or self.voted:
            return "Жду READY"
        card = self.text(img,(.69,.09,1,.40))
        header = label(card,"PARTY INVITE")
        host_box = (.69,header[1]+.007,1,header[1]+.039) if header else (0,0,0,0)
        if (header and label(card,state["host"],host_box) and
                label(card,"Wastelands") and label(card,"ACCEPT")):
            if time.monotonic()-self.last_invite>3:
                self.game.click(label(card,"ACCEPT"))
                self.last_invite = time.monotonic()
                self.exchange("invited")
                self.invited = True
            return "Принято приглашение на Wastelands"
        if label(self.text(img,(0,.26,.19,.74)),"Wastelands") and label(self.text(img,(.35,.74,.65,.98)),"Cancel"):
            if not self.invited:
                self.exchange("invited")
                self.invited = True
            return "В группе · жду запуска основой"
        return "Жду приглашение или голосование"

    def update_places(self,state):
        own = {p["unit"]:p for p in state["places"] if p["player"]==self.player}
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
        slot = self.slots[unit]
        # Associate the physical card with its slot even when another price is unreadable.
        center = (.313 + (slot-1)*.072)
        price = next((v for x,v in prices if abs(x-center)<.032 and v),None)
        cash = self.game.money()
        if price is None or cash is None or cash < price:
            return f"Жду {unit} · баланс {cash}, цена слота {slot}: {price}"
        if self.attempt[unit]>=5:
            return f"{unit}: пять точек заняты; проверь разметку"
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
                if "занят" in str(e):
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
                return f"Поставил {unit}"
            if not gone and after is not None and after>=cash:
                self.confirm = ("release",unit,point)
                self.exchange("release",unit=unit,point=point)
                self.confirm = None
                self.attempt[unit]+=1
                return "Точка занята · пробую рядом"
            return f"Проверь {unit}: результат клика не подтверждён"
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
            self.attempt = {u:0 for u in UNITS}
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
        for unit in UNITS:
            if unit not in self.placed:
                return self.place(unit,img)
        if min(self.levels.values())<8 and time.monotonic()>self.next_upgrade:
            self.next_upgrade = time.monotonic()+4
            cash = self.game.money()
            if cash is not None and cash>=self.wait_cash:
                unit = min(self.levels,key=self.levels.get)
                return self.manager(unit,"Upgrade")
        return f"Amplifier {self.levels['amplifier']}/8 · Screen {self.levels['screen']}/8"

    def loop(self):
        try:
            while not self.stop.is_set():
                try:
                    state = self.exchange()
                    if state["run"]!=self.run:
                        self.reset(state)
                    if self.run:
                        self.status = self.tick(state)
                    else:
                        self.status = "На связи · жду матч"
                except (Wait,OSError,ValueError,RuntimeError) as exc:
                    self.status = str(exc)
                self.notify(self.status)
                self.stop.wait(.38)
        finally:
            self.ocr.close()
