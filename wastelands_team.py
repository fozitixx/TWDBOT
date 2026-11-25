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
TITANS = ("amplifier", "screen")
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
TITAN_CLEARANCE = 54
REJECTION_SECONDS = 35
PLACEMENT_ORDER = ("plunger", "plunger_2", "plunger_3", "plunger_4",
                   "tv", "tv_2", "tv_3", "tv_4", "amplifier", "screen")


def trunk_point(along, across):
    return tuple(j+along*t+across*n for j,t,n in zip(JUNCTION,TRUNK,BRANCH))


# The open sand marked for helper 3 is on the negative side of the trunk,
# between the early junction and the next bend. All distances are map pixels.
THIRD_BANK_RUN = (548,664)
THIRD_BANK_EDGE = -64
LANES = (((1159,631),(1336,751)), ((1022,690),(1285,868)),
         tuple(trunk_point(along,THIRD_BANK_EDGE) for along in THIRD_BANK_RUN))
# Signed depth from the lane and clearance past either end of its centerline.
TITAN_DEPTH = (80, -80, -36)
TITAN_EXTENSION = (80, 80, 12)

# (distance along the lane, extra distance away from the road in map pixels).
TITAN_OFFSETS = ((0,0),(.09,0),(-.09,0),(.16,0),(-.16,0),
                 (0,24),(.16,24),(-.16,24),(0,45),(.20,45),(-.20,45),
                 (.32,20),(-.32,20),(.40,40),(-.40,40))


# Both titans can use the whole assigned strip if their preferred end is blocked.
TITAN_SPARES = tuple((progress, outward) for outward in (0, 28, 54)
                     for progress in (0, .25, .5, .75, 1))

# Distances on a full-size strip, scaled to each helper's depth and extension.
TITAN_BANK_GRID = tuple((along,outward) for along in range(-80,81,20)
                        for outward in (0,20,40,60,80))
TITAN_LANE_GRID = tuple((fraction,outward) for fraction in (.10,.22,.34,.46,.58,.70,.82,.94)
                        for outward in (10,35,65,80))

# Rounded canonical positions confirmed by personal counters in played matches.
CONFIRMED_TITAN_SITES = {
    1: {"amplifier":(1278,646)},
    2: {"amplifier":(1024,720),"screen":(1180,797)},
    3: {},
}


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
PRIMARY_BANK_COUNT = 5 + len(SPARE_BANKS) + len(SHARED_BANKS)
# Use the opposite edge of the main road when the usual perimeter is full.
# The worker still measures the actual visible edge before reserving a point.
OVERFLOW_BANKS = tuple((trunk_point(distance, 0), TRUNK, tuple(-v for v in BRANCH))
                       for distance in (*range(-246, 165, 12), *range(294, 529, 12)))


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
    elif attempt < PRIMARY_BANK_COUNT:
        return SHARED_BANKS[attempt-5-len(SPARE_BANKS)]
    else:
        return OVERFLOW_BANKS[attempt-PRIMARY_BANK_COUNT]
    center = [v+distance*t for v,t in zip(start,tangent)]
    return center, tangent, normal


def placement_attempts(unit):
    if unit.partition("_")[0] in EARLY:
        return PRIMARY_BANK_COUNT + len(OVERFLOW_BANKS)
    return len(TITAN_OFFSETS)+len(TITAN_SPARES)+len(TITAN_LANE_GRID)+len(TITAN_BANK_GRID)


def on_third_titan_bank(point):
    dx,dy = point[0]-JUNCTION[0],point[1]-JUNCTION[1]
    along = dx*TRUNK[0]+dy*TRUNK[1]
    across = dx*BRANCH[0]+dy*BRANCH[1]
    margin = TITAN_EXTENSION[2]
    return (THIRD_BANK_RUN[0]-margin-1 <= along <= THIRD_BANK_RUN[1]+margin+1
            and THIRD_BANK_EDGE+TITAN_DEPTH[2]-1 <= across <= THIRD_BANK_EDGE+1)


def position(player, unit, attempt=0):
    if unit.partition("_")[0] in EARLY:
        center, _, normal = bank_slot(player,unit,attempt)
        return [v+BANK_OFFSET*n for v,n in zip(center,normal)]
    a, b = LANES[player - 1]
    progress = .22 if unit == "amplifier" else .76
    if attempt < len(TITAN_OFFSETS):
        along, outward = TITAN_OFFSETS[attempt]
        progress = max(0, min(1, progress + along))
    elif attempt<len(TITAN_OFFSETS)+len(TITAN_SPARES):
        progress, outward = TITAN_SPARES[attempt - len(TITAN_OFFSETS)]
    else:
        index = attempt-len(TITAN_OFFSETS)-len(TITAN_SPARES)
        if index<len(TITAN_LANE_GRID):
            progress,outward = TITAN_LANE_GRID[index]
        else:
            extension,outward = TITAN_BANK_GRID[index-len(TITAN_LANE_GRID)]
            extension *= TITAN_EXTENSION[player-1]/80
            progress = (0 if extension<0 else 1)+extension/math.dist(a,b)
    base = mix(a,b,progress)
    depth = outward*TITAN_DEPTH[player-1]/80
    return [v+depth*n for v,n in zip(base,BRANCH)]


def segment_distance(p, a, b):
    dx, dy = b[0] - a[0], b[1] - a[1]
    t = ((p[0] - a[0])*dx + (p[1] - a[1])*dy) / (dx*dx + dy*dy)
    return math.dist(p, mix(a, b, min(1, max(0, t))))


def placement_conflict(player,unit,point,places,*,manual=False):
    if not manual and segment_distance(point, (638,438),(886,604)) < 58:
        return "Зона титанов основы"
    if not manual and any(math.dist(point, reserved) < 30 for reserved in MAIN_EARLY):
        return "Зона ранней защиты основы"
    for other in places:
        if other["player"]==player and other["unit"]==unit:
            continue
        if other["state"]=="sold":
            continue
        other_early = other["unit"].partition("_")[0] in EARLY
        both_early = unit.partition("_")[0] in EARLY and other_early
        clearance = EARLY_CLEARANCE if both_early else TITAN_CLEARANCE
        target = other.get("target")
        # The third helper's two titans can exchange unclaimed positions on
        # their small patch. Every pending or built base still owns its radius.
        same_titan_bank = (player==other["player"]==3 and unit in ("amplifier","screen")
                           and other["unit"] in ("amplifier","screen"))
        protect_plan = (other["state"]=="placed" or other.get("manual_site") or
                        (not manual and not (other_early or same_titan_bank) and not target))
        for occupied in (other["point"] if protect_plan else None, target, other.get("clear_site")):
            if occupied and math.dist(point, occupied) < clearance:
                return "Рядом занят участок"
    return None


def single_blocker(player, titan, point, places, *, manual=False):
    """Return the confirmed small tower whose removal alone frees this site."""
    blocked = [p for p in places if p["unit"].partition("_")[0] in EARLY and p["state"]=="placed"
               and math.dist(point,p["point"])<TITAN_CLEARANCE]
    if len(blocked)!=1:
        return None
    tower = blocked[0]
    if (tower.get("slot") is None or tower.get("target") or
            (tower.get("count_before") is None and tower.get("total_before") is None)):
        return None
    if placement_conflict(player,titan,point,(p for p in places if p is not tower),manual=manual):
        return None
    return tower


def footprint_class(unit):
    return "early" if unit.partition("_")[0] in EARLY else "titan"


def recent_sites(history, now):
    for key, until in list(history.items()):
        if until<=now:
            del history[key]
    return list(history)


def near_rejection(unit, point, sites):
    group = footprint_class(unit)
    # An unsuccessful click proves only that spot. A real tower still owns 54.
    clearance = EARLY_CLEARANCE if group=="early" else 18
    return any(group==other and math.dist(point,center)<clearance for other,center in sites)


def titan_layout(points):
    """Validate the six optional positions in the common road coordinate system."""
    slots = {f"{player}/{unit}" for player in PLAYERS for unit in TITANS}
    if not isinstance(points, dict) or not points.keys() <= slots:
        raise ValueError("Некорректная разметка титанов")
    layout = {}
    for key, point in points.items():
        if (not isinstance(point, (list, tuple)) or len(point) != 2 or
                not all(type(v) in (int, float) and math.isfinite(v) for v in point) or
                not (0 < point[0] < 2048 and 0 < point[1] < 1152)):
            raise ValueError("Точка за пределами карты Wastelands")
        for other, center in layout.items():
            if math.dist(center, point) < TITAN_CLEARANCE:
                raise ValueError(f"Точки {other} и {key} слишком близко для двух титанов")
        layout[key] = list(point)
    return layout


class Wait(Exception):
    pass


class PairingExpired(Wait):
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
        payload = dict(instance=self.instance, run=run, status=status, op=op, can_summon=True,
                       uses_host_sites=True, can_clear_space=True, can_map=True, **fields)
        request = Request(self.url, data=json.dumps(payload).encode(), headers={
            "Authorization": "Bearer " + self.key, "Content-Type": "application/json"})
        try:
            with self.http.open(request, timeout=3) as response:
                return json.load(response)
        except HTTPError as exc:
            with exc:
                if exc.code == 403:
                    raise PairingExpired("Основа отклонила сохранённую привязку. Введи новый PIN.") from exc
                if exc.code == 409:
                    raise Wait(json.load(exc)["error"]) from exc
                raise Wait(f"Основа ответила HTTP {exc.code}. Проверь номер и код подключения.") from exc
        except (URLError, OSError) as exc:
            raise Wait("Нет связи с основой. Проверь IP и кнопку «Включить связь».") from exc


class Match:
    def __init__(self, titan_sites=None, manual_titans=None):
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
        self.titan_sites = {}
        self.manual_titans = titan_layout({} if manual_titans is None else manual_titans)
        self.map_frame = None
        if isinstance(titan_sites,dict):
            for player in PLAYERS:
                for unit in ("amplifier","screen"):
                    key = f"{player}/{unit}"
                    point = titan_sites.get(key)
                    if (isinstance(point,(tuple,list)) and len(point)==2
                            and all(type(v) in (int,float) and math.isfinite(v) for v in point)
                            and any(math.dist(point,position(player,unit,i))<1 for i in range(placement_attempts(unit)))):
                        self.titan_sites[key] = list(point)
        self.pending = {}
        self.frames = {}
        self.results = {}
        self.progress = {}
        self.sales = {}
        self.sale_retry = {}
        self.allow_sales = False
        self.vote_owner = None
        self.vote_until = 0

    def apply_titan_point(self, row):
        if row["unit"] not in TITANS or row["state"] != "reserved" or row.get("target") or row.get("clear_site"):
            return
        player, unit = row["player"], row["unit"]
        row["manual_site"] = self.manual_titans.get(f"{player}/{unit}")
        row["point"] = row["manual_site"] or position(player, unit)

    def set_titan_layout(self, points):
        with self.lock:
            layout = titan_layout(points)
            changed = {key for key in self.manual_titans.keys() | layout.keys()
                       if self.manual_titans.get(key) != layout.get(key)}
            self.manual_titans = layout
            for sale in list(self.sales.values()):
                key = f"{sale['requester']}/{sale['titan']}"
                if key in changed and "before" not in sale:
                    self.finish_sale(sale, False, time.monotonic())
            for row in self.places.values():
                if f"{row['player']}/{row['unit']}" in changed and "clear_until" in row:
                    row.pop("clear_until")
                    row.pop("clear_site", None)
                self.apply_titan_point(row)

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

    def start(self, mode, host, *, afk_auto=True, allow_sales=False):
        if mode not in ("hard", "nightmare") or not host.strip():
            raise ValueError("Укажи сложность и имя основы из PARTY INVITE")
        with self.lock:
            self.run = secrets.token_hex(8)
            self.recalled.clear()
            self.rejections.clear()
            self.mode, self.host = mode, host.strip()
            self.afk_auto = afk_auto
            self.allow_sales = allow_sales
            self.sales.clear()
            self.sale_retry.clear()
            self.vote_owner = None
            self.places = {(i, u): {"unit": u, "player": i, "point": position(i, u),
                                    "state": "reserved"} for i in PLAYERS for u in PLACEMENT_ORDER}
            for row in self.places.values():
                self.apply_titan_point(row)
            self.map_frame = None
            self.pending.clear()
            self.frames.clear()
            self.results.clear()
            self.progress = {i:{"invited":False,"voted":False,"ready":False,"retry":0} for i in PLAYERS}

    def stop(self):
        with self.lock:
            self.run = ""
            self.map_frame = None
            self.sales.clear()
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
        if name not in (*ABILITIES, "snapshot", "map_snapshot"):
            raise ValueError("Неизвестная команда")
        with self.lock:
            client = self.clients.get(player, {})
            if not self.run or time.monotonic() - client.get("seen", -1e9) > 8:
                raise ValueError("Твинк вне связи или матч не начат")
            if name == "map_snapshot" and not client.get("can_map"):
                raise ValueError("Для кадра карты обнови твинк до 6.0.25")
            if player in self.recalled or player in self.summons:
                raise ValueError("Твинк вызван в приватку")
            prior = self.pending.get(player)
            if prior and time.monotonic() < prior["until"]:
                raise ValueError("Предыдущая команда ещё выполняется")
            self.pending[player] = dict(details, id=secrets.token_hex(8), name=name,
                                        until=time.monotonic()+(18 if name=="map_snapshot" else 8))
            self.results[player] = "Команда отправлена"
            if name == "snapshot":
                self.frames.pop(player, None)
            return self.pending[player]["id"]

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
        if place["state"]=="sold":
            raise ValueError("Это место освобождено под титана")
        if player in self.sales or any(s["requester"]==player and s["titan"]==unit for s in self.sales.values()):
            raise ValueError("Идёт освобождение места под титана")
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
            manual = place.get("manual_site")
            if manual and point != manual:
                raise ValueError("Точка титана изменилась на основе")
            if not manual and not any(allowed(j) for j in range(placement_attempts(unit))):
                raise ValueError("За пределами назначенной зоны")
        elif unit != "screen":
            raise ValueError("Перенос доступен только для Screen")
        if place["state"]!="placed" and near_rejection(unit,point,recent_sites(self.rejections,time.monotonic())):
            raise ValueError("Игра недавно отклонила этот участок")
        conflict = placement_conflict(player,unit,point,self.places.values(),
                                      manual=bool(place.get("manual_site")) and place["state"] != "placed")
        if conflict:
            raise ValueError(conflict)
        place["count_before"] = count_before
        place["total_before"] = total_before
        place["slot"] = slot
        place["target"] = point
        place["target_since"] = time.monotonic()

    def request_space(self, player, titan, point, now):
        if not self.allow_sales or titan not in ("amplifier","screen"):
            return
        row = self.places[player,titan]
        if (row["state"]=="placed" or row.get("target") or row.get("clear_site") or row.get("sale_issued")
                or any(s["requester"]==player for s in self.sales.values())):
            return
        if not isinstance(point,list) or len(point)!=2 or not all(type(v) in (float,int) and math.isfinite(v) for v in point):
            return
        manual = row.get("manual_site")
        if manual and point != manual:
            return
        if not manual and not any(math.dist(point,position(player,titan,i))<1 for i in range(placement_attempts(titan))):
            return
        tower = single_blocker(player,titan,point,self.places.values(),manual=bool(manual))
        if tower is None:
            return
        owner,unit = tower["player"],tower["unit"]
        client = self.clients.get(owner,{})
        if (owner in self.sales or owner in self.recalled or owner in self.summons or not client.get("can_clear_space")
                or now-client["seen"]>8 or any(p.get("target") for (i,_),p in self.places.items() if i==owner)
                or now<self.sale_retry.get((player,titan,owner,unit),0)):
            return
        row["clear_site"] = list(point)
        self.sales[owner] = dict(id=secrets.token_hex(12),requester=player,titan=titan,owner=owner,
                                 unit=unit,point=list(tower["point"]),slot=tower["slot"],until=now+40)

    def finish_sale(self, sale, sold, now):
        owner,unit = sale["owner"],sale["unit"]
        row = self.places[sale["requester"],sale["titan"]]
        if sold:
            self.places[owner,unit]["state"] = "sold"
            row.update(sale_used=True,clear_until=now+20)
            if row.get("manual_site") != self.manual_titans.get(f"{sale['requester']}/{sale['titan']}"):
                row.pop("clear_site", None)
                row.pop("clear_until")
                self.apply_titan_point(row)
        else:
            row.pop("clear_site",None)
            self.apply_titan_point(row)
            # After issuing a sale, never send another click for the same tower
            # and request within this match, even if the response was lost.
            self.sale_retry[sale["requester"],sale["titan"],owner,unit] = (
                float("inf") if "before" in sale else now+35)
        del self.sales[owner]

    def sale_action(self, player, op, req, now):
        sale = self.sales.get(player)
        if not sale or req.get("id")!=sale["id"]:
            return False
        count = req.get("count")
        if op=="arm_sale":
            requester = self.clients.get(sale["requester"],{})
            if ("before" not in sale and now-requester.get("seen",-1e9)<10
                    and type(count) is int and 1<=count<=4
                    and not any(p.get("target") for (i,_),p in self.places.items() if i==player)):
                sale.update(before=count,armed=now)
                self.places[sale["requester"],sale["titan"]]["sale_issued"] = True
                return True
        elif "before" not in sale:
            if op=="cancel_sale":
                self.finish_sale(sale,False,now)
        elif op=="sale_count" and type(count) is int:
            if count==sale["before"]-1:
                self.finish_sale(sale,True,now)
            elif count==sale["before"] and now-sale["armed"]>=8:
                self.finish_sale(sale,False,now)
        return False

    def exchange(self, player, req):
        with self.lock:
            now = time.monotonic()
            client = self.clients.get(player, {})
            owner = req["instance"]
            if client and client["instance"] != owner and now-client["seen"] < 10:
                raise ValueError("Этот номер твинка уже подключён")
            self.clients[player] = dict(instance=owner, seen=now, status=str(req.get("status",""))[:180],
                                        can_summon=req.get("can_summon") is True,
                                        can_map=req.get("can_map") is True,
                                        can_clear_space=req.get("can_clear_space") is True)
            for sale in list(self.sales.values()):
                if "before" not in sale and (sale["until"]<now or sale["requester"] in self.recalled
                        or sale["owner"] in self.summons or sale["requester"] in self.summons):
                    self.finish_sale(sale,False,now)
            for row in self.places.values():
                if "clear_until" in row and row["clear_until"]<=now:
                    row.pop("clear_until")
                    row.pop("clear_site",None)
                    self.apply_titan_point(row)
            self.expire_summon(player, now)
            summon = self.summons.get(player)
            op = req.get("op","poll")
            sites = None
            preferred_site = None
            manual_site = None
            claimed = None
            send_sale = False
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
                if op=="need_space":
                    self.request_space(player,req.get("unit"),req.get("point"),now)
                elif op in ("arm_sale","cancel_sale","sale_count"):
                    send_sale = self.sale_action(player,op,req,now)
                elif op=="placement_sites":
                    unit = req["unit"]
                    if unit not in PLACEMENT_ORDER:
                        raise ValueError("Неизвестный юнит")
                    locate = bank_slot if unit.partition("_")[0] in EARLY else position
                    manual_site = self.places[player,unit].get("manual_site")
                    sites = [manual_site] if manual_site else [locate(player,unit,i) for i in range(placement_attempts(unit))]
                    preferred_site = manual_site or self.titan_sites.get(f"{player}/{unit}",CONFIRMED_TITAN_SITES[player].get(unit))
                elif op in ("reserve","release","commit"):
                    unit = req["unit"]
                    place = self.places[player,unit]
                    if (op!="reserve" and place.get("target") and req.get("target_since") is not None
                            and req["target_since"]!=place.get("target_since")):
                        raise ValueError("Резерв изменился")
                    if op == "reserve":
                        if "plan_point" in req and req["plan_point"] != place.get("manual_site") and place["state"] != "placed":
                            raise ValueError("Точка титана изменилась на основе")
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
                        self.apply_titan_point(place)
                    elif place.get("target") == req["point"]:
                        if (unit in TITANS and not place.get("manual_site") and place["state"]!="placed" and place.get("slot")
                                and (place.get("count_before") is not None or place.get("total_before") is not None)):
                            self.titan_sites[f"{player}/{unit}"] = list(place["target"])
                        place.update(point=place.pop("target"),state="placed")
                        place.pop("clear_site",None)
                        place.pop("clear_until",None)
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
                        if cmd["name"] == "map_snapshot" and cmd.get("claimed") and now <= cmd["until"] and req.get("frame"):
                            self.map_frame = (cmd["id"], dict(player=player, image=req["frame"], pose=req.get("pose")))
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
                        allow_sales=self.allow_sales, sale=dict(self.sales[player]) if player in self.sales else None,
                        send_sale=send_sale,
                        rejected_sites=recent_sites(self.rejections,now),preferred_site=preferred_site,manual_site=manual_site,
                        summon={"id":summon["id"],"link":summon["link"]} if summon and summon["instance"]==owner else None,
                        afk_auto=self.afk_auto, placement_sites=True, placement_totals=True, sites=sites, mode=self.mode,host=self.host,places=[dict(p) for p in self.places.values()],claimed=claimed,
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
