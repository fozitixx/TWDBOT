"""Shared Wastelands match state. Map coordinates use the annotated 2048×1152 view."""
import hmac
import json
import math
import secrets
import threading
import time
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.error import HTTPError, URLError
from urllib.request import ProxyHandler, Request, build_opener


PORT = 47631
PAIR_LIFETIME = 300
PLAYERS = (1, 2, 3)
UNITS = ("plunger", "tv", "amplifier", "screen")
ABILITIES = ("Aerial Attack", "Hook and Punch", "Teleport")
# The main player's pair occupies index zero in the yellow bend.
EARLY = {
    "plunger": [(930, 452), (951, 424), (972, 396), (993, 368)],
    "tv": [(950, 482), (977, 501), (1004, 520), (1031, 539)],
}
LANES = [((1159, 631), (1336, 751)), ((1022, 690), (1285, 868)),
         ((1539, 871), (1770, 1029))]


def mix(a, b, fraction):
    return [x + (y - x) * fraction for x, y in zip(a, b)]


def position(player, unit, attempt=0):
    if unit in EARLY:
        x, y = EARLY[unit][player]
        dx, dy = [(0, 0), (8, 5), (-7, -5), (6, -8), (-5, 8)][attempt % 5]
        return [x + dx, y + dy]
    a, b = LANES[player - 1]
    progress = .22 if unit == "amplifier" else .76
    return mix(a, b, progress + (0, .09, -.09, .16, -.16)[attempt % 5])


def segment_distance(p, a, b):
    dx, dy = b[0] - a[0], b[1] - a[1]
    t = ((p[0] - a[0])*dx + (p[1] - a[1])*dy) / (dx*dx + dy*dy)
    return math.dist(p, mix(a, b, min(1, max(0, t))))


class Wait(Exception):
    pass


class AltConnection:
    def __init__(self, host, player, key, port=PORT):
        self.url = f"http://{host}:{port}/alt/{player}"
        self.player = player
        self.key = key
        self.instance = secrets.token_hex(12)
        self.http = build_opener(ProxyHandler({}))

    def exchange(self, op="poll", *, run="", status="Подключение", **fields):
        payload = dict(instance=self.instance, run=run, status=status, op=op, **fields)
        request = Request(self.url, data=json.dumps(payload).encode(), headers={
            "Authorization": "Bearer " + self.key, "Content-Type": "application/json"})
        try:
            with self.http.open(request, timeout=3) as response:
                return json.load(response)
        except HTTPError as exc:
            with exc:
                if exc.code == 409:
                    raise Wait(json.load(exc)["error"]) from exc
                raise Wait(f"Основа ответила HTTP {exc.code}. Проверь номер и код подключения.") from exc
        except (URLError, OSError) as exc:
            raise Wait("Нет связи с основой. Проверь IP и кнопку «Включить связь».") from exc


class Match:
    def __init__(self):
        self.lock = threading.RLock()
        self.keys = {i: secrets.token_urlsafe(18) for i in PLAYERS}
        self.pins = {}
        self.pair_failures = deque(maxlen=12)
        self.clients = {}
        self.run = ""
        self.mode = "nightmare"
        self.host = ""
        self.places = {}
        self.pending = {}
        self.frames = {}
        self.results = {}
        self.progress = {}

    def issue_pin(self, player):
        with self.lock:
            if player not in PLAYERS:
                raise ValueError("Неизвестный номер твинка")
            now = time.monotonic()
            existing = self.pins.get(player)
            if existing and existing[1] > now:
                return existing[0]
            occupied = {pin for pin, until in self.pins.values() if until > now}
            while True:
                pin = f"{secrets.randbelow(100_000_000):08d}"
                if pin not in occupied:
                    self.pins[player] = (pin, now + PAIR_LIFETIME)
                    return pin

    def redeem_pin(self, code):
        with self.lock:
            now = time.monotonic()
            while self.pair_failures and now - self.pair_failures[0] >= 60:
                self.pair_failures.popleft()
            if len(self.pair_failures) == self.pair_failures.maxlen:
                raise ValueError("Слишком много неверных PIN. Повтори через минуту.")
            if isinstance(code,str) and len(code)==8 and code.isascii() and code.isdigit():
                for player, (pin, until) in self.pins.items():
                    if until > now and hmac.compare_digest(pin, code):
                        del self.pins[player]
                        return {"player":player, "key":self.keys[player]}
            self.pair_failures.append(now)
            raise ValueError("PIN неверен, уже использован или истёк. Проверь PIN на основе.")

    def start(self, mode, host):
        if mode not in ("hard", "nightmare") or not host.strip():
            raise ValueError("Укажи сложность и имя основы из PARTY INVITE")
        with self.lock:
            self.run = secrets.token_hex(8)
            self.mode, self.host = mode, host.strip()
            self.places = {(i, u): {"unit": u, "player": i, "point": position(i, u),
                                    "state": "reserved"} for i in PLAYERS for u in UNITS}
            self.pending.clear()
            self.frames.clear()
            self.results.clear()
            self.progress = {i:{"invited":False,"voted":False,"ready":False,"retry":0} for i in PLAYERS}

    def stop(self):
        with self.lock:
            self.run = ""
            self.pending.clear()
            self.frames.clear()

    def command(self, player, name, **details):
        if name not in (*ABILITIES, "snapshot"):
            raise ValueError("Неизвестная команда")
        with self.lock:
            client = self.clients.get(player, {})
            if not self.run or time.monotonic() - client.get("seen", -1e9) > 8:
                raise ValueError("Твинк вне связи или матч не начат")
            prior = self.pending.get(player)
            if prior and time.monotonic() < prior["until"]:
                raise ValueError("Предыдущая команда ещё выполняется")
            self.pending[player] = dict(details, id=secrets.token_hex(8), name=name,
                                        until=time.monotonic()+8)
            self.results[player] = "Команда отправлена"
            if name == "snapshot":
                self.frames.pop(player, None)

    def reserve(self, player, unit, point):
        if not isinstance(point, list) or len(point) != 2 or not all(
                type(x) in (int,float) and math.isfinite(x) for x in point):
            raise ValueError("Некорректная точка")
        x,y = point
        if not (0 < x < 2048 and 0 < y < 1152):
            raise ValueError("Точка вне карты")
        place = self.places[player, unit]
        if place.get("target"):
            if place["target"]==point:
                return
            raise ValueError("Предыдущий резерв ещё не подтверждён")
        if place["state"] != "placed":
            if not any(math.dist(point, position(player,unit,j)) < 1 for j in range(5)):
                raise ValueError("За пределами назначенной зоны")
        elif unit != "screen":
            raise ValueError("Перенос доступен только для Screen")
        if segment_distance(point, (638,438),(886,604)) < 58:
            raise ValueError("Зона титанов основы")
        if any(math.dist(point, row[0]) < 30 for row in EARLY.values()):
            raise ValueError("Зона ранней защиты основы")
        for key, other in self.places.items():
            if key == (player,unit):
                continue
            clearance = 26 if unit in EARLY and other["unit"] in EARLY else 54
            for occupied in (other["point"], other.get("target")):
                if occupied and math.dist(point, occupied) < clearance:
                    raise ValueError("Рядом занят участок")
        place["target"] = point
        place["target_since"] = time.monotonic()

    def exchange(self, player, req):
        with self.lock:
            now = time.monotonic()
            client = self.clients.get(player, {})
            owner = req["instance"]
            if client and client["instance"] != owner and now-client["seen"] < 10:
                raise ValueError("Этот номер твинка уже подключён")
            self.clients[player] = dict(instance=owner, seen=now, status=str(req.get("status",""))[:180])
            op = req.get("op","poll")
            claimed = None
            if op != "poll":
                if not self.run or self.run != req.get("run"):
                    raise ValueError("Матч сменился")
                if op in ("reserve","release","commit"):
                    unit = req["unit"]
                    place = self.places[player,unit]
                    if op == "reserve":
                        self.reserve(player,unit,req["point"])
                    elif op == "release":
                        if place.get("target") and place["target"]!=req.get("point"):
                            raise ValueError("Резерв изменился")
                        place.pop("target",None)
                    elif place.get("target") == req["point"]:
                        place.update(point=place.pop("target"),state="placed")
                    elif place["state"] != "placed" or place["point"] != req["point"]:
                        raise ValueError("Резерв не подтверждён")
                elif op in ("invited","voted","ready"):
                    self.progress[player][op] = True
                elif op == "claim":
                    cmd = self.pending.get(player)
                    if cmd and cmd["id"]==req["id"] and not cmd.get("claimed") and now<cmd["until"]:
                        cmd["claimed"] = True
                        claimed = dict(cmd,remaining=cmd["until"]-now)
                        self.results[player] = "Твинк выполняет команду"
                elif op == "result":
                    cmd = self.pending.get(player)
                    if cmd and cmd["id"] == req["id"]:
                        if cmd["name"] == "snapshot" and req.get("frame"):
                            self.frames[player] = (cmd["id"],req["frame"])
                        self.results[player] = str(req["result"])[:160]
                        del self.pending[player]
                else:
                    raise ValueError("Неизвестная операция")
            cmd = self.pending.get(player)
            if cmd and now > cmd["until"]:
                del self.pending[player]
                self.results[player] = "Время истекло; результат не подтверждён"
                cmd = None
            return dict(run=self.run,mode=self.mode,host=self.host,places=list(self.places.values()),claimed=claimed,
                        progress=self.progress.get(player,{}),
                        command=dict(cmd,remaining=cmd["until"]-now) if cmd and not cmd.get("claimed")
                        and req.get("run")==self.run else None)


def serve(match, address):
    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_POST(self):
            try:
                pairing = self.path == "/pair"
                if not pairing:
                    if self.path not in ("/alt/1", "/alt/2", "/alt/3"):
                        self.send_error(404)
                        return
                    player = int(self.path[-1])
                    secret = self.headers.get("Authorization","")
                    if not hmac.compare_digest(secret, "Bearer " + match.keys[player]):
                        self.send_error(403)
                        return
                length = int(self.headers.get("Content-Length","0"))
                if not 0 < length <= (128 if pairing else 800_000):
                    self.send_error(413)
                    return
                self.connection.settimeout(4)
                req = json.loads(self.rfile.read(length))
                body = match.redeem_pin(req["pin"]) if pairing else match.exchange(player, req)
                code = 200
            except (ValueError, KeyError, TypeError) as exc:
                body, code = {"error":str(exc)}, 409
            data = json.dumps(body,ensure_ascii=False).encode()
            self.send_response(code)
            self.send_header("Content-Type","application/json")
            self.send_header("Content-Length",str(len(data)))
            self.end_headers()
            self.wfile.write(data)

    server = ThreadingHTTPServer(address, Handler)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    return server


def connect_by_pin(host, pin, port=PORT):
    req = Request(f"http://{host}:{port}/pair", data=json.dumps({"pin":pin}).encode(),
                  headers={"Content-Type":"application/json"})
    try:
        with build_opener(ProxyHandler({})).open(req,timeout=4) as res:
            data = json.load(res)
    except HTTPError as exc:
        with exc:
            if exc.code == 409:
                try:
                    reason = json.load(exc).get("error","")
                except ValueError:
                    reason = ""
                if "PIN" in reason:
                    raise ValueError(reason) from exc
            raise ValueError("Проверь, что на основе запущена версия 6.0.2 или новее.") from exc
    except (URLError, OSError) as exc:
        raise ValueError(f"Основа {host} недоступна. Проверь IP и кнопку «Включить связь».") from exc
    if not isinstance(data,dict) or data.get("player") not in PLAYERS or not data.get("key"):
        raise ValueError("Неверный ответ от основы. Проверь адрес и версию приложения.")
    return data["player"], data["key"]
