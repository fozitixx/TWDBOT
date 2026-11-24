"""Shared Wastelands match state. Map coordinates use the annotated 2048×1152 view."""
import hmac
import json
import math
import re
import secrets
import threading
import time
from collections import deque
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, urlsplit
from urllib.request import ProxyHandler, Request, build_opener


PORT = 47631
PAIR_LIFETIME = 300
PLAYERS = (1, 2, 3)
UNITS = ("plunger", "tv", "amplifier", "screen")
ABILITIES = ("Aerial Attack", "Hook and Punch", "Teleport")
# First copy keeps its original ID for existing commands and READY.
MAIN_EARLY = ((930, 452), (950, 482))
EARLY = ("plunger", "tv")
# Map-space axes along the main road and its branch, from their junction.
JUNCTION = (835.,475.)
_road_length = math.hypot(715,490)
TRUNK = (715/_road_length,490/_road_length)
BRANCH = (TRUNK[1],-TRUNK[0])
# Each run follows one bank. The gap in the first run leaves room for the main pair.
PERIMETER = (
    (TRUNK, BRANCH, (48,146,185,224,263,302)),
    (BRANCH, TRUNK, (112,145,178,211,244,273)),
    (BRANCH, (-TRUNK[0],-TRUNK[1]), (68,101,134,167,200,233)),
    (TRUNK, BRANCH, (-72,-110,-148,-186,-224,-262)),
)
# Extra sites continue along the trunk and around the next corner of the branch.
SPARE_BANKS = (
    *((0,s,1) for s in (-300,-340,-380,-420,340)),
    *((0,s,-1) for s in (164,202,240,278,-260,-298,-336,-374,-412)),
    *((276,s,side) for s in (-82,-122,-162,-202) for side in (-1,1)),
    *((276,s,side) for s in (-242,-282,-322) for side in (-1,1)),
    *((0,s,side) for s in (-458,-496,-534) for side in (-1,1)),
)
EDGE_GAP = 14
BANK_OFFSET = 24 + EDGE_GAP  # nominal half road width plus clearance for the base
EDGE_ADJUST = 21  # maximum correction from the nominal boundary, in map pixels
EARLY_CLEARANCE = 26
REJECTION_SECONDS = 35
PLACEMENT_ORDER = ("plunger", "plunger_2", "plunger_3", "plunger_4",
                   "tv", "tv_2", "tv_3", "tv_4", "amplifier", "screen")
LANES = [((1159, 631), (1336, 751)), ((1022, 690), (1285, 868)),
         ((1539, 871), (1770, 1029))]

# (distance along the lane, extra distance away from the road in map pixels).
TITAN_OFFSETS = ((0,0),(.09,0),(-.09,0),(.16,0),(-.16,0),
                 (0,24),(.16,24),(-.16,24),(0,45),(.20,45),(-.20,45),
                 (.32,20),(-.32,20),(.40,40),(-.40,40))


# Both titans can use the whole assigned strip if their preferred end is blocked.
TITAN_SPARES = tuple((progress, outward) for outward in (0, 28, 54)
                     for progress in (0, .25, .5, .75, 1))


def mix(a, b, fraction):
    return [x + (y - x) * fraction for x, y in zip(a, b)]


def placement_label(unit):
    kind, _, number = unit.partition("_")
    if kind in EARLY:
        name = "TV" if kind == "tv" else "Plunger"
        return f"{name} {number or '1'}/4"
    return unit.title()


def shared_bank_sections():
    # Sample along the calibrated banks, including between the original slots.
    # A long gap separates distinct strips (for example the main player's pair).
    strips = {(JUNCTION,tangent,normal):set(stops) for tangent,normal,stops in PERIMETER}
    for leg,distance,side in SPARE_BANKS:
        origin = tuple(v+leg*n for v,n in zip(JUNCTION,BRANCH))
        normal = tuple(side*n for n in BRANCH)
        strips.setdefault((origin,TRUNK,normal),set()).add(distance)
    sections = []
    for (origin,tangent,normal),stops in strips.items():
        distances = sorted(stops)
        for left,right in zip(distances,distances[1:]):
            if right-left<=48:
                steps = math.ceil((right-left)/8)
                stops.update(left+i*(right-left)/steps for i in range(1,steps))
        for distance in sorted(stops):
            center = tuple(v+distance*t for v,t in zip(origin,tangent))
            sections.append((center,tangent,normal))
    return tuple(sections)


SHARED_BANKS = shared_bank_sections()


def bank_slot(player, unit, attempt=0):
    kind, _, number = unit.partition("_")
    copy = int(number or 1)-1 + (4 if kind=="tv" else 0)
    rank, bank = divmod(copy*len(PLAYERS)+player-1, len(PERIMETER))
    tangent, normal, along = PERIMETER[bank]
    start = JUNCTION
    if attempt<5:
        distance = along[rank] + (0, 7, -7, 14, -14)[attempt]
    elif attempt < 5+len(SPARE_BANKS):
        branch_distance,distance,side = SPARE_BANKS[(attempt-5+rank+bank)%len(SPARE_BANKS)]
        start = [v+branch_distance*n for v,n in zip(JUNCTION,BRANCH)]
        tangent, normal = TRUNK, tuple(side*n for n in BRANCH)
    else:
        return SHARED_BANKS[attempt-5-len(SPARE_BANKS)]
    center = [v+distance*t for v,t in zip(start,tangent)]
    return center, tangent, normal


def placement_attempts(unit):
    if unit.partition("_")[0] in EARLY:
        return 5+len(SPARE_BANKS)+len(SHARED_BANKS)
    return len(TITAN_OFFSETS)+len(TITAN_SPARES)


def position(player, unit, attempt=0):
    if unit.partition("_")[0] in EARLY:
        center, _, normal = bank_slot(player,unit,attempt)
        return [v+BANK_OFFSET*n for v,n in zip(center,normal)]
    a, b = LANES[player - 1]
    progress = .22 if unit == "amplifier" else .76
    if attempt < len(TITAN_OFFSETS):
        along, outward = TITAN_OFFSETS[attempt]
        progress = max(0, min(1, progress + along))
    else:
        progress, outward = TITAN_SPARES[attempt - len(TITAN_OFFSETS)]
    base = mix(a,b,progress)
    side = -1 if player==2 else 1
    return [v+side*outward*n for v,n in zip(base,BRANCH)]


def segment_distance(p, a, b):
    dx, dy = b[0] - a[0], b[1] - a[1]
    t = ((p[0] - a[0])*dx + (p[1] - a[1])*dy) / (dx*dx + dy*dy)
    return math.dist(p, mix(a, b, min(1, max(0, t))))


def placement_conflict(player,unit,point,places):
    if segment_distance(point, (638,438),(886,604)) < 58:
        return "Зона титанов основы"
    if any(math.dist(point, reserved) < 30 for reserved in MAIN_EARLY):
        return "Зона ранней защиты основы"
    for other in places:
        if other["player"]==player and other["unit"]==unit:
            continue
        both_early = unit.partition("_")[0] in EARLY and other["unit"].partition("_")[0] in EARLY
        clearance = EARLY_CLEARANCE if both_early else 54
        target = other.get("target")
        # Early copies can share fallback candidates until someone claims one.
        protect_plan = other["state"]=="placed" or (not both_early and not target)
        for occupied in (other["point"] if protect_plan else None, target):
            if occupied and math.dist(point, occupied) < clearance:
                return "Рядом занят участок"
    return None


def footprint_class(unit):
    return "early" if unit.partition("_")[0] in EARLY else "titan"


def recent_sites(history, now):
    for key, until in list(history.items()):
        if until<=now:
            del history[key]
    return list(history)


def near_rejection(unit, point, sites):
    group = footprint_class(unit)
    clearance = EARLY_CLEARANCE if group=="early" else 50
    return any(group==other and math.dist(point,center)<clearance for other,center in sites)


class Wait(Exception):
    pass


def private_server_links(value):
    """Build launch targets from the server setting, including older game links."""
    invalid = "В настройках основы сохрани ссылку на приватный сервер Roblox."
    try:
        url = urlsplit(str(value or "").strip())
        query = parse_qs(url.query, max_num_fields=24)
    except ValueError:
        raise ValueError(invalid) from None
    web = url.scheme in ("https", "http") and url.netloc.lower() in ("www.roblox.com", "roblox.com")
    shared = (web and url.path.rstrip("/") == "/share") or (
        url.scheme == "roblox" and url.netloc == "navigation" and url.path == "/share_links")
    if shared and [s.lower() for s in query.get("type", [])] == ["server"]:
        codes = query.get("code", [])
        if len(codes) == 1 and re.fullmatch(r"[A-Za-z0-9_-]{1,128}", codes[0]):
            args = f"code={codes[0]}&type=Server"
            return (f"roblox://navigation/share_links?{args}", f"https://www.roblox.com/share?{args}")
    game = re.fullmatch(r"/games/([0-9]+)(?:/[^/]*)?/?", url.path) if web else None
    codes = query.get("privateServerLinkCode", [])
    if game and len(codes) == 1 and re.fullmatch(r"[A-Za-z0-9_-]{1,128}", codes[0]):
        return (f"https://www.roblox.com/games/{game[1]}?privateServerLinkCode={codes[0]}",)
    raise ValueError(invalid)


class AltConnection:
    def __init__(self, host, player, key, port=PORT):
        self.url = f"http://{host}:{port}/alt/{player}"
        self.player = player
        self.key = key
        self.instance = secrets.token_hex(12)
        self.http = build_opener(ProxyHandler({}))

    def exchange(self, op="poll", *, run="", status="Подключение", **fields):
        payload = dict(instance=self.instance, run=run, status=status, op=op, can_summon=True, uses_host_sites=True, **fields)
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
        self.summons = {}
        self.recalled = set()
        self.run = ""
        self.afk_auto = True
        self.mode = "nightmare"
        self.host = ""
        self.places = {}
        self.rejections = {}
        self.pending = {}
        self.frames = {}
        self.results = {}
        self.progress = {}
        self.vote_owner = None
        self.vote_until = 0

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

    def start(self, mode, host, *, afk_auto=True):
        if mode not in ("hard", "nightmare") or not host.strip():
            raise ValueError("Укажи сложность и имя основы из PARTY INVITE")
        with self.lock:
            self.run = secrets.token_hex(8)
            self.recalled.clear()
            self.rejections.clear()
            self.mode, self.host = mode, host.strip()
            self.afk_auto = afk_auto
            self.vote_owner = None
            self.places = {(i, u): {"unit": u, "player": i, "point": position(i, u),
                                    "state": "reserved"} for i in PLAYERS for u in PLACEMENT_ORDER}
            self.pending.clear()
            self.frames.clear()
            self.results.clear()
            self.progress = {i:{"invited":False,"voted":False,"ready":False,"retry":0} for i in PLAYERS}

    def stop(self):
        with self.lock:
            self.run = ""
            self.recalled.clear()
            self.pending.clear()
            self.frames.clear()
            self.results.clear()

    def expire_summon(self, player, now):
        request = self.summons.get(player)
        if request and now >= request["until"]:
            del self.summons[player]
            self.results[player] = "Вызов истёк. Ответ от твинка не получен."

    def summon(self, player, link):
        link = private_server_links(link)[-1]
        with self.lock:
            now = time.monotonic()
            client = self.clients.get(player, {})
            if now - client.get("seen", -1e9) > 8:
                raise ValueError("Твинк вне связи")
            if not client.get("can_summon"):
                raise ValueError("Обнови приложение твинка до 6.0.5")
            self.expire_summon(player, now)
            if player in self.summons:
                raise ValueError("Вызов уже отправлен")
            self.summons[player] = dict(id=secrets.token_hex(8), link=link, until=now+30,
                                        instance=client["instance"], run=self.run)
            self.results[player] = "Отправлен вызов в приватку"

    def command(self, player, name, **details):
        if name not in (*ABILITIES, "snapshot"):
            raise ValueError("Неизвестная команда")
        with self.lock:
            client = self.clients.get(player, {})
            if not self.run or time.monotonic() - client.get("seen", -1e9) > 8:
                raise ValueError("Твинк вне связи или матч не начат")
            if player in self.recalled or player in self.summons:
                raise ValueError("Твинк вызван в приватку")
            prior = self.pending.get(player)
            if prior and time.monotonic() < prior["until"]:
                raise ValueError("Предыдущая команда ещё выполняется")
            self.pending[player] = dict(details, id=secrets.token_hex(8), name=name,
                                        until=time.monotonic()+8)
            self.results[player] = "Команда отправлена"
            if name == "snapshot":
                self.frames.pop(player, None)

    def reserve(self, player, unit, point, count_before=None, total_before=None, slot=None):
        if not isinstance(point, list) or len(point) != 2 or not all(
                type(x) in (int,float) and math.isfinite(x) for x in point):
            raise ValueError("Некорректная точка")
        if count_before is not None:
            limit = 4 if unit.partition("_")[0] in EARLY else 1
            if type(count_before) is not int or not 0<=count_before<limit:
                raise ValueError("Некорректный счётчик перед постановкой")
        if total_before is not None and (type(total_before) is not int or not 0<=total_before<=99
                                          or count_before is not None and total_before<count_before):
            raise ValueError("Некорректное число UNITS перед постановкой")
        if slot is not None and (type(slot) is not int or not 1<=slot<=6):
            raise ValueError("Некорректный слот юнита")
        x,y = point
        if not (0 < x < 2048 and 0 < y < 1152):
            raise ValueError("Точка вне карты")
        place = self.places[player, unit]
        if place["state"]=="placed" and (slot is not None or count_before is not None or total_before is not None):
            raise ValueError("Постановка уже подтверждена")
        if place.get("target"):
            if place["target"]==point:
                return
            raise ValueError("Предыдущий резерв ещё не подтверждён")
        if place["state"] != "placed":
            # A counter-aware placement needs exclusive use of this player's
            # total. Legacy geometry-only reservations remain independent.
            if any(p.get("target") and p["state"]!="placed" and
                   (slot is not None or total_before is not None or
                    p.get("slot") is not None or p.get("total_before") is not None)
                   for (owner,_),p in self.places.items() if owner==player):
                raise ValueError("Жду результат предыдущей постановки этого твинка")
            def allowed(attempt):
                planned = position(player,unit,attempt)
                if unit.partition("_")[0] not in EARLY:
                    return math.dist(point,planned)<1
                _, tangent, normal = bank_slot(player,unit,attempt)
                dx,dy = x-planned[0],y-planned[1]
                return (abs(dx*tangent[0]+dy*tangent[1])<1 and
                        abs(dx*normal[0]+dy*normal[1])<=EDGE_ADJUST+.01)
            if not any(allowed(j) for j in range(placement_attempts(unit))):
                raise ValueError("За пределами назначенной зоны")
        elif unit != "screen":
            raise ValueError("Перенос доступен только для Screen")
        if place["state"]!="placed" and near_rejection(unit,point,recent_sites(self.rejections,time.monotonic())):
            raise ValueError("Игра недавно отклонила этот участок")
        conflict = placement_conflict(player,unit,point,self.places.values())
        if conflict:
            raise ValueError(conflict)
        place["count_before"] = count_before
        place["total_before"] = total_before
        place["slot"] = slot
        place["target"] = point
        place["target_since"] = time.monotonic()

    def exchange(self, player, req):
        with self.lock:
            now = time.monotonic()
            client = self.clients.get(player, {})
            owner = req["instance"]
            if client and client["instance"] != owner and now-client["seen"] < 10:
                raise ValueError("Этот номер твинка уже подключён")
            self.clients[player] = dict(instance=owner, seen=now, status=str(req.get("status",""))[:180],
                                        can_summon=req.get("can_summon") is True)
            self.expire_summon(player, now)
            summon = self.summons.get(player)
            op = req.get("op","poll")
            sites = None
            claimed = None
            if op == "summon_result":
                if summon and summon["id"] == req.get("id") and summon["instance"] == owner:
                    opened = req.get("opened") is True
                    self.results[player] = "Ссылка на приватку открыта" if opened else "Не удалось открыть ссылку на приватку"
                    if opened and self.run and summon["run"] == self.run:
                        self.recalled.add(player)
                        self.pending.pop(player, None)
                        self.frames.pop(player, None)
                    del self.summons[player]
                    summon = None
            elif op != "poll":
                if not self.run or self.run != req.get("run") or player in self.recalled:
                    raise ValueError("Матч сменился")
                if op=="placement_sites":
                    unit = req["unit"]
                    if unit not in PLACEMENT_ORDER:
                        raise ValueError("Неизвестный юнит")
                    locate = bank_slot if unit.partition("_")[0] in EARLY else position
                    sites = [locate(player,unit,i) for i in range(placement_attempts(unit))]
                elif op in ("reserve","release","commit"):
                    unit = req["unit"]
                    place = self.places[player,unit]
                    if (op!="reserve" and place.get("target") and req.get("target_since") is not None
                            and req["target_since"]!=place.get("target_since")):
                        raise ValueError("Резерв изменился")
                    if op == "reserve":
                        try:
                            self.reserve(player,unit,req["point"],req.get("count_before"),
                                         req.get("total_before"),req.get("slot"))
                        except ValueError as exc:
                            if str(exc)=="За пределами назначенной зоны" and not req.get("uses_host_sites"):
                                raise ValueError("Разметка твинка устарела · обнови и перезапусти твинк") from exc
                            raise
                    elif op == "release":
                        if place.get("target") and place["target"]!=req.get("point"):
                            raise ValueError("Резерв изменился")
                        # Share a funded, counted failure only for the exact active
                        # lease. A cancelled click, teleport or replay is not evidence.
                        if (req.get("site_failed") is True and place.get("target")
                                and place["state"]!="placed" and place.get("slot") is not None
                                and req.get("target_since")==place["target_since"]
                                and (place.get("count_before") is not None or place.get("total_before") is not None)):
                            self.rejections[footprint_class(unit),tuple(place["target"])] = now+REJECTION_SECONDS
                        place.pop("target",None)
                    elif place.get("target") == req["point"]:
                        place.update(point=place.pop("target"),state="placed")
                    elif place["state"] != "placed" or place["point"] != req["point"]:
                        raise ValueError("Резерв не подтверждён")
                elif op == "vote_turn":
                    if self.vote_owner is None or now >= self.vote_until:
                        self.vote_owner = player
                        self.vote_until = now+6
                elif op == "vote_end":
                    if self.vote_owner == player:
                        self.vote_owner = None
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
            return dict(run="" if player in self.recalled else self.run,
                        rejected_sites=recent_sites(self.rejections,now),
                        summon={"id":summon["id"],"link":summon["link"]} if summon and summon["instance"]==owner else None,
                        afk_auto=self.afk_auto, placement_sites=True, placement_totals=True, sites=sites, mode=self.mode,host=self.host,places=list(self.places.values()),claimed=claimed,
                        vote_seconds=max(0,self.vote_until-now) if self.vote_owner==player else 0,
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
