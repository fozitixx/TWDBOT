"""
Бот для Toilet Warfare Defense: режим HARD, карта Invaded City.
Играет не по записи, а по плану: каждый шаг (поставить, прокачать, продать)
выполняется, как только на него хватает денег.

Установка (один раз):
    pip install pynput numpy pillow

Запуск:
    python twd_bot.py                бесконечно, матч за матчем
    python twd_bot.py --loops 3      3 матча
    python twd_bot.py diag           проверка: что бот видит на экране прямо сейчас

После запуска переключись в Roblox и нажми F8. F6 - остановить.
Начинать можно где угодно: в лобби, в зоне вертолётов, на экране выбора
сложности, перед READY или на финальном экране. Из лобби бот сам идёт:
TELEPORT -> Deployment Zone -> Teleport -> синий круг -> Invaded City ->
Select -> Start. Если Roblox закрылся, бот открывает ссылку на приватный
сервер (ссылка задаётся в настройках приложения, поле «Ссылка приватного сервера»).

Обновления: при запуске и между матчами бот сверяет свою версию с version.json в репозитории
github.com/fozitixx/TWDBOT и, если там новее, скачивает twd_bot.py, проверяет его и перезапускается.

Как бот ставит юнитов в одни и те же места:
  1. До READY ставит камеру строго сверху и отдаляет до упора.
  2. Берёт юнита в руку - игра подсвечивает дорожку красным.
  3. Сравнивает форму дорожки с эталоном, понимает, на сколько повёрнута
     камера, и доворачивает её. Поэтому угол камеры при спавне не важен.
  4. Ставит первого юнита в заранее посчитанную точку у угла дорожки и
     только потом жмёт READY. Если точка занята, пробует соседние.

План можно поменять: положи рядом файл plan.json (формат - как в build_plan ниже).
Журнал пишется в twd_log.txt рядом со скриптом.
"""

import argparse
import base64
import json
import math
import os
import sys
import threading
import subprocess
import time
import zlib

import numpy as np
from PIL import Image, ImageGrab
from pynput import keyboard, mouse

# рядом с .exe (если бот собран в exe) или рядом с .py
HERE = os.path.dirname(os.path.abspath(sys.executable if getattr(sys, "frozen", False) else __file__))
VERSION = "6.0.10 (Wasteland: голосование и расстановка)"
START_KEY = keyboard.Key.f8
ABORT_KEY = keyboard.Key.f6

# ---------- места на экране (доли окна игры: x, y) ----------

MONEY_REGION = (0.359, 0.730, 0.641, 0.792)
END_BOX = (0.36, 0.72, 0.645, 0.755)          # кнопки Rejoin / Back to Lobby
END_GREEN_X = (0.0, 0.49)
END_RED_X = (0.615, 1.0)
REJOIN_POINT = (0.43, 0.737)
IDLE_POINT = (0.6, 0.07)          # пустое место сверху: закрыть награду / снять выделение (не над чатом Roblox)
VOTE_BOX = (0.15, 0.15, 0.85, 0.78)           # по этой части узнаётся экран выбора сложности
VOTE_MAX_DIFF = 26.0
VOTE_HARD_POINT = (0.5577, 0.7241)            # кнопка VOTE под HARD
READY_BOX = (0.46, 0.17, 0.54, 0.21)
READY_POINT = (0.4986, 0.1905)
# Кнопки скорости справа сверху: 1x (обычная), 1.5x (GROUP - нужна группа игры), 2x (PASS - нужен геймпасс).
SPEED_POINTS = {"1": (0.8360, 0.1392), "1.5": (0.8984, 0.1392), "2": (0.9602, 0.1392)}
SPEED_TITLES = {"1": "1x", "1.5": "1.5x", "2": "2x"}


def speed_key():
    k = str(SETTINGS.get("speed", "2"))
    return k if k in SPEED_POINTS else "2"


def speed_factor():
    """Во сколько раз игра идёт быстрее, чем на 1.5x: времена боя с боссом записаны для 1.5x."""
    if not SETTINGS.get("use_speed", True):
        return 1.0 / 1.5
    return float(speed_key()) / 1.5

# Лобби
# Ссылка приватного сервера берётся из настроек (settings.json, поле server_link) - в коде её нет,
# потому что файл бота лежит в открытом репозитории.
SERVER_LINK = ""
SERVER_DEEPLINK = ""      # та же приватка, но открывается сразу в клиенте Roblox, без браузера
FOCUS_AFTER = 3           # через сколько секунд без фокуса самому активировать окно Roblox
MOVE_TO_PRIMARY = True    # окно Roblox на другом мониторе -> перенести на основной
PRIVATE_ONLY = True       # оказался в лобби не через ссылку -> перезайти на приватку
MAP_CARD_OFFSET = (0.065, -0.517)   # карточка Invaded City относительно кнопки Select
CHAR_POINT = (0.5, 0.56)            # где на экране персонаж (для ходьбы к синему кругу)
LOBBY_W = 320                       # ширина уменьшенного кадра для поиска кнопок

# Области интерфейса, которые не считаются при поиске дорожки
HUD_BOXES = [
    (0.00, 0.00, 0.09, 0.07),    # меню Roblox
    (0.32, 0.00, 0.66, 0.30),    # здоровье, волна, надписи посередине сверху
    (0.80, 0.07, 1.00, 0.20),    # скорость игры
    (0.27, 0.80, 0.72, 1.00),    # карточки юнитов
    (0.94, 0.90, 1.00, 1.00),    # настройки
    (0.00, 0.20, 0.25, 0.80),    # панель выбранного юнита
]

# ---------- камера ----------

ALIGN_DRAG_PX = 3000      # тянуть ПКМ вниз до упора: вид сверху
ALIGN_SCROLL_STEPS = 40   # колесо на отдаление до упора
TURN_PX_PER_DEG = 12.5    # примерно, уточняется на ходу (полный оборот ~4500px)
YAW_TOLERANCE = 1.0       # градусов: точнее камеру не доворачиваем, остаток учитываем расчётом

# ---------- дорожка ----------

PATH_W, PATH_H = 364, 205         # размер маски дорожки
PATH_CENTER = (0.5, 0.488)        # вокруг этой точки поворачивается картинка (персонаж)
REF_MASK_B64 = "eNrtmEGO5CAMRSvKSCw5AjcZjsb0zapvkl1va5lFVB6SooiB/MgeTaSWGm9arTjG72NTOLdbt27dunXr1u1fzNFD4U10lzsbel6YyB9NIosqkel7JOKvS8TSLHceVKFV+ziqSiRoqu9CRK9B1HUBXYl4Ve1diOg0iKMKMejOsuV/9OJw1zTMb03DmIcG8SBBCxHdomiY8aBycMMEUuziUb0HVKjjQZ1hxNDqihEttTwQMYZp4uCG8dSmCBvGxNCTuGGiM4kRXXSepYhrHnWOGJHoq3kGER0tzbIQMW75R02EqynQo6mHgBBtTLkuNYsQo6z3et0BIq58NRJE3GStQmHE1bHeCNgw25q+XBg2zLZmxYQRtzUruTxCfK1Z7oRBiK8KHstdh4ivUnIFFERMwhUtBhsmsZd5woZJ7IUEEDE9KNUlhJgeFGI7hPh+wMUeEeL7QeEAEd8h+drwTMjZciyEmIXgikHErDETGyLmiFxseCbkBJnY8EzYO5rFQw2zdzRLFZ4Ju1C7ChCRCbW/hxBZlF1siMiiZLHhmcCi7D7oTOBR8ouwYXiUnBOqJh4l40JEHsUlJ4hY1OT7yoAQiw0z6R+IWGyYT+sgxIJmSF6wYYo7o30lcHImzMWrM/tzJEh7PzP4x2sqXn2eHntmaeWBiDffKj/iCXBqNxWeCbdfbb1Y4Vhi0m/qJJzQ5n3rBcPf/QzxoGCCdMhdHa10AlxzGMQT4Cq2F09eUTkjnuNXsUk8x0exnXjIjXyf8iE3SuflQ244uMWfiS1H3K78T8WIq5jjzcE0cSa2Yo4fiBSfKixp5vig+VQxahBXsa/77DqrPvQoPnx169atW7duP9D+AoLGWdw="

# Точки постановки в эталонном виде (доли окна)
POINTS = {
    "s1": (0.4485, 0.4542),
    "s2": (0.4341, 0.4786),
    "s3": (0.4196, 0.5031),
    "s4": (0.4052, 0.5275),
    "s5": (0.4657, 0.4799),
    "s6": (0.4794, 0.5043),
    "s7": (0.4938, 0.5299),
    "s8": (0.5082, 0.5556),
    "t1": (0.6806, 0.6593),
    "t2": (0.7246, 0.5739),
    "c1": (0.4505, 0.5226),
    "f1": (0.572, 0.7096),
    "f2": (0.5839, 0.7298),
    "f3": (0.5606, 0.7308),
    "f4": (0.5725, 0.751),
    "p9": (0.6389, 0.6389),
    "c3": (0.8812, 0.254),
    "s9": (0.5284, 0.5916),
    "s10": (0.5485, 0.6276),
    "t1n": (0.6806, 0.6288),
    "c3b": (0.7562, 0.2955),
}

# Пробные сдвиги, если точка оказалась занята (в пикселях окна 1456x819)
# расстояние точек эталона до края дороги (доля ширины кадра) - для "прилипания" к дороге
POINT_CLEARANCE = {"s1": 0.0102, "s2": 0.0102, "s3": 0.0102, "s4": 0.0102, "s5": 0.0103, "s6": 0.0107,
                   "s7": 0.0107, "s8": 0.0117, "t1": 0.0311, "t2": 0.0298,
                   "c3": 0.0288, "c3b": 0.0288, "p9": 0.0102, "s9": 0.0107, "s10": 0.0107,
                   "t1n": 0.0426}     # Nightmare: титан во 2-м углу дальше от дороги - круг дальности как раз до внешнего угла
# c1 (титан в первом углу) к дороге не прижимается: у титана большой радиус, важнее не задеть соседей
BIG_POINTS = {"t1", "t1n", "t2", "c1", "c3", "c3b"}

# --- плотная кучка в первом углу (Nightmare), как в видео ---
# Координаты юнита: (расстояние от края 2-го отрезка, расстояние от края 1-го отрезка) в ширинах дороги.
# Отсчёт от внутренней вершины угла, которую бот находит сам по красной подсветке.
CORNER_REF = (655 / 1456.0, 349 / 819.0)     # вершина первого угла на эталоне
ROAD_W_REF = 50.5                            # ширина дороги на эталоне, px кадра 1456
_C, _D = 0.18, 0.32                          # отступ первого ряда от дороги и шаг между юнитами (вплотную)
# место в кучке: (номер вдоль дороги, по которой враги приходят; номер ряда от этой дороги)
CLUSTER = {
    "n1": (0, 0), "n2": (1, 0), "n3": (2, 0),        # ряд вдоль дороги, по которой идут враги
    "n4": (0, 1), "n5": (1, 1), "n6": (2, 1),
    "n7": (0, 2), "n8": (1, 2),
}
CLUSTER_ABS = {"c1": (1.30, 1.60),           # титан: за кучкой, как на скриншоте (в ширинах дороги)
               "m1": (2.12, 2.10), "m2": (1.79, 2.43)}   # запасные места плунжеров: ниже титана, их видно
# Сторожа (четыре TV) во внутренней вершине 3-го поворота - ловят тех, кто прошёл титана:
# (расстояние вдоль края дороги, по которой враги подходят; расстояние от этого края)
CORNER3_REF = (1346 / 1456.0, 204 / 819.0)
CLUSTER3 = {"g1": (0, 0), "g2": (1, 0), "g3": (0, 1), "g4": (1, 1)}
CLUSTER3_ABS = {"c3": (1.35, 1.00),          # титан у 3-го поворота: рядом со сторожами, но не в них
                "c3b": (3.40, 3.00)}          # второй титан: на открытой траве в глубине угла. Прежняя точка
                                              # (3.0, 0.75) попадала в поваленное дерево у дороги
# Если юнит не встал: отдельно подбираю отступ от дороги (по первому юниту в вершине)
# и шаг между юнитами (по остальным), маленькими шагами - чтобы кучка осталась как можно плотнее.
GROW_EDGE = (1.0, 1.2, 1.4, 1.65, 1.9)
GROW_STEP = (1.0, 1.06, 1.12, 1.19, 1.27, 1.36)
CLUSTER_GROW = (1.0, 1.07, 1.15, 1.24, 1.34, 1.45)   # для титана: дальше от угла

TRY_OFFSETS = [(0, 0), (0, 9), (9, 0), (-9, 0), (0, -9), (9, 9), (-9, 9), (0, 18), (18, 0), (-18, 0),
               (9, -9), (-9, -9), (18, 18), (-18, 18), (0, 27)]
TRY_OFFSETS_BIG = TRY_OFFSETS + [(27, 0), (-27, 0), (0, -27), (27, 27), (-27, 27), (36, 0), (-36, 0), (0, 36),
                                 (0, -36), (36, 36), (-36, 36), (36, -36), (-36, -36), (54, 0), (-54, 0), (0, 54)]

# ---------- план ----------
# place:   поставить юнита из слота slot в точку at, назвать его unit
#          sell_first: сначала продать этих юнитов (их ожидаемая выручка sell_value
#          учитывается, чтобы купить как можно раньше)
# upgrade: прокачать юнита unit (клик по нему и клавиша E)
# sell:    продать юнита unit (клик по нему и клавиша X)
# порядок приоритетов по клавише R (из видео): First -> Last -> Strongest -> Weakest -> Flying
PRIORITIES = ["First", "Last", "Strongest", "Weakest", "Flying", "Boss"]   # R листает по кругу

ABILITY_POINT = (0.280, 0.368)       # кнопка способности справа от панели выбранного юнита
BOSS_BAR_BOX = (0.356, 0.150, 0.644, 0.178)   # полоса здоровья босса (30-я волна Nightmare)
VOTE_FALLBACK = {"hard": (0.5577, 0.7241), "nightmare": (0.7555, 0.7241)}


def _p(unit, utype, at, **kw):
    return dict({"do": "place", "unit": unit, "type": utype, "at": at}, **kw)


def _u(*units):
    return [{"do": "upgrade", "unit": u} for u in units]


def titan_roles(slots):
    """Кто из титанов что делает: (главный, второй).
    Второй (имя юнита tspk, стоит у 2-го поворота) - всегда Titan Amplifierman: без него босса не пройти.
    Главный (имя юнита tcam: крюк или щит, переезд к 3-му повороту) - Titan Screen Man, а если его нет -
    Titan Camcorderman."""
    return ("ttv" if "ttv" in slots else "tcam"), "tspk"


def titan_groups(slots):
    """Группы «нужен один из» для двух титанов - для проверки слотов и для окна."""
    return [["tspk"], ["ttv", "tcam"]]


def build_plan(mode, slots):
    """План матча. Имена юнитов в плане постоянные (tcam - главный титан, tspk - второй),
    а какой титан стоит под каждым именем, решает titan_roles."""
    global MAIN_TITAN, SECOND_TITAN
    MAIN_TITAN, SECOND_TITAN = titan_roles(slots)
    plan = _build_plan(mode, slots)
    for st in plan:
        if st.get("type") == "tcam":
            st["type"] = MAIN_TITAN
        elif st.get("type") == "tspk":
            st["type"] = SECOND_TITAN
    return plan


def _build_plan(mode, slots):
    """План матча под выбранный режим и найденные юниты."""
    if mode == "nightmare":
        farms = ["farm1", "farm2", "farm3", "farm4"]
        # Плотная кучка во внутреннем углу, как в видео: каждый юнит достаёт до обоих отрезков дороги.
        # Плунжеры - ряд вдоль дороги, по которой враги приходят (n1-n3) и n4; TV - за ними (n5-n8).
        plan = [
            _p("pl1", "plunger", "n1"),                       # до READY - в самой вершине угла
            _p("pl2", "plunger", "n2"),
            _p("pl3", "plunger", "n3"),
            _p("tv1", "tv", "n5", priority="Flying"),
            _p("pl4", "plunger", "n4"),
            _p("tv2", "tv", "n6", priority="Flying"),
            _p("tv3", "tv", "n7", priority="Flying"),
            _p("tv4", "tv", "n8", priority="Flying"),
            # сначала на поле все восемь, и только потом прокачка: плунжеры, затем TV
            *_u("pl1", "pl2", "pl3", "pl4"),
            *_u("tv1", "tv2", "tv3", "tv4"),
            # --- дальше порядок из видео после патча (босс 100 000 HP) ---
            # фермы сразу после кучки (к концу 9-й волны стоят все четыре) и до 3 ур. - раньше титана:
            # на их доход ставятся оба титана и копится запас к боссу
            *[_p(f, "farm", "f" + f[-1]) for f in farms],
            *_u(*farms), *_u(*farms), *_u(*farms),
            # 12-я волна: Titan Amplifierman внутри 2-го поворота, ради него продаются только два TV
            _p("tspk", "tspk", "t1n", sell_first=["tv3", "tv4"], margin=30),
            *_u("tspk", "tspk"),
            # 13-я волна: два TV у 3-го поворота (лимит TV - 4), без прокачки. g1 и g3 не заслоняют друг друга
            _p("gtv1", "tv", "g1", quick=15),
            _p("gtv2", "tv", "g3", quick=15),
            *_u(*farms),                                      # фермы -> 4 (максимум) к концу 14-й
            _p("tcam", "tcam", "c1"),                         # 15-я волна, без продаж
            *_u("tcam", "tcam"),
            *_u("tcam", "tspk"),                              # 17-я: оба до 3 ур.
            *_u(*["tcam"] * 5),                               # Cameraman до 8 ур. (к 23-й волне)
            # Speakerman до 7 ур. Восьмой уровень берётся уже в бою с боссом, одним выделением вместе с
            # Aerial Attack: титана 8 ур. заново выделить кликом не получалось ни в одном матче.
            *_u(*["tspk"] * 4),
            # плунжеры не качаются и больше ничего не покупается: деньги копятся к переезду титана на боссе
        ]
        return plan
    sup = "plunger" if "plunger" in slots else "speaker"
    s_ = ["sup1", "sup2", "sup3", "sup4"]
    return [
        *[_p(f"sup{i}", sup, f"s{i}") for i in range(1, 5)],                        # первыми по ходу врагов
        *[_p(f"tv{i}", "tv", f"s{i + 4}", priority="Flying") for i in range(1, 5)],   # после угла, добивать
        *_u(*s_), *_u(*s_),
        _p("tcam", "tcam", "t1", sell_first=["tv1", "tv2", "tv3", "tv4"] + s_),
        _p("tspk", "tspk", "t2"),
        *_u("tcam", "tspk", "tcam", "tcam", "tspk", "tspk", "tcam", "tcam", "tcam"),
    ]


# Бой с боссом 30-й волны (времена - секунды после появления полосы босса, из видео):
#   +3    Shield Mode у Titan Camcorderman - сразу, как с него спадёт стартовое оглушение
#   +5    Motivation первого плунжера, +15 - второго
#   +25   новый плунжер у 2-го поворота, качается до максимума, +34 - его Motivation
#   +37   Aerial Attack у Titan Amplifierman
#   ~+51  босс дошёл до 2-го поворота (оглушил Titan Amplifierman): Titan Camcorderman продаётся
#         и ставится дальше по пути, у 3-го поворота
#   +76   плунжеры продаются - деньги в нового титана
# Каждое нажатие способности проверяется по кнопке (появился отсчёт - сработало) и повторяется.
# Перестановка Titan Camcorderman в бою с боссом: когда босс дошёл до 2-го поворота (там он оглушает
# Titan Amplifierman), титан у первого угла уже не нужен - он продаётся и ставится впереди по пути
# босса, у 3-го поворота. Заодно продаются фермы и два плунжера из первого угла - деньги в нового титана.
NIGHTMARE_START_CASH = 800                   # с этой суммой начинается матч на NIGHTMARE (на EASY - $650)
# Бой с боссом после патча (100 000 HP), времена - секунды после появления полосы босса, из видео:
BOSS_SHIELD_AT = 16.0          # Shield Mode у Titan Camcorderman
BOSS_AERIAL_AT = 40.0          # 8-й уровень и Aerial Attack у Titan Amplifierman (в видео Aerial на +54)
BOSS_MOVE_TCAM = True
BOSS_TCAM_MOVE_MIN = 52.0      # раньше этого Cameraman не переставлять (в видео +61)
BOSS_TCAM_MOVE_MAX = 56.0      # с этого момента переезд начинается в любом случае
BOSS_TSPK_MOVE_AT = 86.0       # Speakerman переезжает следом (в видео +89)
ABILITY_BOX = (0.252, 0.345, 0.305, 0.418)       # картинка на кнопке способности


def ability_state(img):
    """Состояние кнопки способности выбранного юнита: "ready" - готова (цветная, с рисунком),
    "active" - действует (бирюзовая с отсчётом), "cooldown" - перезарядка (тёмная с отсчётом)."""
    w, h = img.size
    box = ABILITY_BOX
    a = np.asarray(img.crop((int(box[0] * w), int(box[1] * h), int(box[2] * w), int(box[3] * h)))
                   .convert("RGB")).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    white = float((a.min(axis=2) > 200).mean())
    dark = float((a.max(axis=2) < 70).mean())
    cyan = float(((g > 140) & (b > 140) & (r < 110)).mean())
    if cyan > 0.4:
        return "active"
    if white > 0.09:
        return "cooldown"
    return "ready"


def stun_fraction(img, pt, k=1.0, big=True):
    """Доля "оглушённо-синих" пикселей на юните (оглушённый юнит целиком тёмно-синий, над ним отсчёт).
    big - титан (крупная фигура), иначе обычный юнит."""
    w, h = img.size
    f = w / 1456.0
    R = (45 if big else 14) * k * f
    cx, cy = pt[0] * w, pt[1] * h - (0 if big else 4 * k * f)
    box = (int(max(0, cx - R)), int(max(0, cy - R)), int(min(w, cx + R)), int(min(h, cy + R)))
    if box[2] - box[0] < 6 or box[3] - box[1] < 6:
        return 0.0
    a = np.asarray(img.crop(box).convert("RGB")).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    return float(((b > 100) & (b - r > 50) & (b - g > 35)).mean())


def boss_hp_fraction(img):
    """Сколько здоровья осталось у босса (0..1): где кончается заполненная часть полосы.
    Полоса красная, а при попаданиях розовеет - учитываются оба цвета."""
    w, h = img.size
    box = BOSS_BAR_BOX
    a = np.asarray(img.crop((int(box[0] * w), int(box[1] * h), int(box[2] * w), int(box[3] * h)))
                   .convert("RGB")).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    fill = (r > 170) & (r - g > 45) & (r - b > 30)
    cols = fill.mean(axis=0) > 0.4
    n = len(cols)
    run = cols[:-2] & cols[1:-1] & cols[2:]           # три заполненных столбца подряд
    idx = np.nonzero(run)[0]
    if len(idx) == 0:
        return 0.0
    return min(1.0, float(idx[-1] + 3) / n)


BASE_BAR_BOX = (0.366, 0.036, 0.643, 0.070)   # зелёная полоса здоровья базы вверху экрана


def base_hp_fraction(img):
    """Сколько здоровья осталось у базы (0..1) по заполненной части верхней полосы; None - полосы нет."""
    w, h = img.size
    box = BASE_BAR_BOX
    a = np.asarray(img.crop((int(box[0] * w), int(box[1] * h), int(box[2] * w), int(box[3] * h)))
                   .convert("RGB")).astype(np.int16)
    mx, mn = a.max(axis=2), a.min(axis=2)
    cols = ((mx > 120) & (mx - mn > 60)).mean(axis=0) > 0.4
    n = len(cols)
    if n < 20 or not cols[:max(3, n // 40)].any():
        return None                                   # левый край полосы не цветной - полосы на экране нет
    run = cols[:-2] & cols[1:-1] & cols[2:]
    idx = np.nonzero(run)[0]
    if len(idx) == 0:
        return None
    return min(1.0, float(idx[-1] + 3) / n)


ABILITY_LEVEL = {"tcam": 8, "ttv": 7, "tspk": 7, "plunger": 7}   # у Titan Amplifierman кнопка способности есть уже на 7 ур.

VOTE_SIG = [183,164,159,159,158,157,156,167,174,155,152,153,152,117,62,114,153,135,135,144,141,131,117,99,145,146,146,148,149,151,140,130,170,73,52,52,47,52,51,110,152,61,67,80,88,68,47,71,68,34,41,53,45,36,35,124,92,34,45,70,57,34,49,148,171,53,29,28,26,30,28,98,149,43,82,86,88,90,42,114,88,15,35,41,36,25,22,122,74,14,34,88,60,15,36,147,176,50,25,34,35,30,23,98,151,41,79,86,85,89,42,117,109,19,33,42,42,30,23,104,65,12,38,87,64,14,32,138,180,47,24,42,35,28,19,87,131,47,77,80,84,82,51,106,103,31,46,51,46,39,48,118,69,9,26,70,47,10,19,59,180,54,37,48,49,46,32,99,121,42,59,63,61,61,44,105,94,24,35,43,46,33,32,129,77,24,30,47,35,25,26,37,184,68,77,109,114,101,57,109,109,79,112,115,113,109,91,91,77,41,92,107,110,85,39,78,58,84,89,93,92,89,70,83,187,56,42,60,87,44,37,104,126,40,47,79,90,48,39,70,67,24,37,88,79,33,22,37,31,28,49,95,72,31,43,157,184,60,78,83,146,76,67,107,165,52,81,124,144,92,55,75,77,43,69,129,126,73,34,52,40,55,76,145,118,71,47,170,186,54,35,75,110,57,31,105,161,39,41,99,107,49,32,69,68,18,38,102,93,29,21,75,53,18,50,104,79,23,41,174,193,84,70,83,87,78,59,112,133,71,70,87,82,69,46,78,77,61,65,85,69,48,28,72,60,62,68,85,74,60,56,179,194,128,121,61,66,71,75,120,107,128,98,66,55,38,41,62,66,138,79,69,41,30,25,55,76,141,66,69,54,67,58,177,192,108,101,63,67,70,71,104,97,101,87,68,61,51,48,50,48,102,71,68,44,39,35,58,67,105,63,67,55,60,63,184,188,76,79,79,75,71,70,111,121,45,62,65,70,75,41,44,33,27,37,42,63,55,25,55,41,33,42,44,57,61,47,176,185,77,93,97,96,98,86,118,149,61,87,89,92,97,66,44,32,44,73,74,83,84,46,56,36,58,78,77,85,86,59,174,186,106,100,102,90,91,100,136,174,90,77,74,61,67,71,51,38,45,54,50,41,53,58,56,40,65,82,74,66,78,85,173,177,83,112,110,54,65,104,114,161,81,110,102,41,78,91,46,33,72,100,88,29,82,70,58,56,88,104,70,30,95,75,162,188,155,151,151,148,148,151,168,186,146,76,48,43,43,43,50,46,36,42,40,42,49,46,134,152,134,134,132,128,133,138,175]


class Aborted(Exception):
    pass


class MatchEnded(Exception):
    pass


# ---------- журнал ----------

_log_file = None
import collections
_log_tail = collections.deque(maxlen=200)     # последние строки лога (для /log)
_gui_queue = collections.deque(maxlen=2000)   # новые строки для окна приложения


def log(text):
    global _log_file
    line = time.strftime("%H:%M:%S ") + text
    if sys.stdout is not None:             # в exe без консоли stdout нет
        try:
            print(line, flush=True)
        except Exception:
            pass
    _log_tail.append(line)
    _gui_queue.append(line)
    try:
        if _log_file is None:
            _log_file = open(os.path.join(HERE, "twd_log.txt"), "a", encoding="utf-8")
        _log_file.write(line + "\n")
        _log_file.flush()
    except OSError:
        pass


# ---------- окно ----------

def enable_dpi_awareness():
    if sys.platform != "win32":
        return
    import ctypes
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass


def foreground_window():
    if sys.platform != "win32":
        return None
    import ctypes
    return ctypes.windll.user32.GetForegroundWindow()


def window_title(hwnd):
    if sys.platform != "win32" or not hwnd:
        return ""
    import ctypes
    buf = ctypes.create_unicode_buffer(256)
    ctypes.windll.user32.GetWindowTextW(hwnd, buf, 256)
    return buf.value


def is_game_window(hwnd):
    return sys.platform != "win32" or window_title(hwnd) == "Roblox"


def find_game_window():
    if sys.platform != "win32":
        return None
    import ctypes
    return ctypes.windll.user32.FindWindowW(None, "Roblox") or None


def bring_to_front(hwnd, click_point=None):
    """Сделать окно активным. Windows часто не даёт это сделать программно,
    поэтому: Alt-трюк, SetForegroundWindow, а если не вышло - клик по окну."""
    if sys.platform != "win32" or not hwnd:
        return
    import ctypes
    from ctypes import wintypes
    u = ctypes.windll.user32
    try:
        if u.IsIconic(hwnd):
            u.ShowWindow(hwnd, 9)                       # SW_RESTORE
        u.keybd_event(0x12, 0, 0, 0)                    # Alt вниз/вверх снимает запрет на смену фокуса
        u.keybd_event(0x12, 0, 2, 0)
        u.SetForegroundWindow(hwnd)
        u.BringWindowToTop(hwnd)
        time.sleep(0.3)
        if u.GetForegroundWindow() == hwnd:
            return
        r = wintypes.RECT()
        u.GetWindowRect(wintypes.HWND(hwnd), ctypes.byref(r))
        fx, fy = click_point or (0.5, 0.08)
        x = int(r.left + (r.right - r.left) * fx)
        y = int(r.top + (r.bottom - r.top) * fy)
        u.SetCursorPos(x, y)
        time.sleep(0.1)
        u.mouse_event(0x0002, 0, 0, 0, 0)               # левая кнопка вниз
        time.sleep(0.08)
        u.mouse_event(0x0004, 0, 0, 0, 0)               # и вверх
        time.sleep(0.3)
    except Exception:
        pass


def window_monitor(hwnd):
    """(монитор основной?, (l, t, r, b) монитора, (l, t, r, b) окна) или None."""
    if sys.platform != "win32" or not hwnd:
        return None
    import ctypes
    from ctypes import wintypes

    class MONITORINFO(ctypes.Structure):
        _fields_ = [("cbSize", wintypes.DWORD), ("rcMonitor", wintypes.RECT),
                    ("rcWork", wintypes.RECT), ("dwFlags", wintypes.DWORD)]
    try:
        u = ctypes.windll.user32
        u.MonitorFromWindow.restype = wintypes.HANDLE
        mon = u.MonitorFromWindow(wintypes.HWND(hwnd), 2)
        mi = MONITORINFO()
        mi.cbSize = ctypes.sizeof(MONITORINFO)
        if not u.GetMonitorInfoW(wintypes.HANDLE(mon), ctypes.byref(mi)):
            return None
        wr = wintypes.RECT()
        u.GetWindowRect(wintypes.HWND(hwnd), ctypes.byref(wr))
        m = mi.rcMonitor
        return bool(mi.dwFlags & 1), (m.left, m.top, m.right, m.bottom), (wr.left, wr.top, wr.right, wr.bottom)
    except Exception:
        return None


def screen_size():
    if sys.platform != "win32":
        return None
    import ctypes
    u = ctypes.windll.user32
    return u.GetSystemMetrics(0), u.GetSystemMetrics(1)


def set_resolution(w, h):
    """Выставить разрешение основного монитора (нужно, например, на ПК без монитора после tscon)."""
    if sys.platform != "win32":
        return False
    import ctypes
    from ctypes import wintypes

    class DEVMODE(ctypes.Structure):
        _fields_ = [("dmDeviceName", ctypes.c_wchar * 32), ("dmSpecVersion", wintypes.WORD),
                    ("dmDriverVersion", wintypes.WORD), ("dmSize", wintypes.WORD),
                    ("dmDriverExtra", wintypes.WORD), ("dmFields", wintypes.DWORD),
                    ("dmPositionX", ctypes.c_long), ("dmPositionY", ctypes.c_long),
                    ("dmDisplayOrientation", wintypes.DWORD), ("dmDisplayFixedOutput", wintypes.DWORD),
                    ("dmColor", ctypes.c_short), ("dmDuplex", ctypes.c_short), ("dmYResolution", ctypes.c_short),
                    ("dmTTOption", ctypes.c_short), ("dmCollate", ctypes.c_short),
                    ("dmFormName", ctypes.c_wchar * 32), ("dmLogPixels", wintypes.WORD),
                    ("dmBitsPerPel", wintypes.DWORD), ("dmPelsWidth", wintypes.DWORD),
                    ("dmPelsHeight", wintypes.DWORD), ("dmDisplayFlags", wintypes.DWORD),
                    ("dmDisplayFrequency", wintypes.DWORD), ("dmICMMethod", wintypes.DWORD),
                    ("dmICMIntent", wintypes.DWORD), ("dmMediaType", wintypes.DWORD),
                    ("dmDitherType", wintypes.DWORD), ("dmReserved1", wintypes.DWORD),
                    ("dmReserved2", wintypes.DWORD), ("dmPanningWidth", wintypes.DWORD),
                    ("dmPanningHeight", wintypes.DWORD)]
    dm = DEVMODE()
    dm.dmSize = ctypes.sizeof(DEVMODE)
    u = ctypes.windll.user32
    if not u.EnumDisplaySettingsW(None, -1, ctypes.byref(dm)):      # ENUM_CURRENT_SETTINGS
        return False
    dm.dmPelsWidth, dm.dmPelsHeight = w, h
    dm.dmFields = 0x00080000 | 0x00100000                            # DM_PELSWIDTH | DM_PELSHEIGHT
    res = u.ChangeDisplaySettingsW(ctypes.byref(dm), 0)
    return res == 0                                                   # DISP_CHANGE_SUCCESSFUL


_res_failed = None


def apply_resolution():
    want = str(SETTINGS.get("force_resolution", "")).lower().replace(" ", "").replace("×", "x").replace("х", "x")
    if want == "1366":
        want = "1366x768"
    if "x" not in want:
        return
    try:
        w, h = (int(v) for v in want.split("x", 1))
    except ValueError:
        return
    cur = screen_size()
    if cur is None or cur == (w, h):
        return
    try:
        import ctypes
        if ctypes.windll.user32.GetSystemMetrics(0x1000):      # SM_REMOTESESSION: сейчас мы в RDP - не трогаем
            return
    except Exception:
        pass
    global _res_failed
    if _res_failed == (w, h, cur):
        return
    if set_resolution(w, h):
        log(f"разрешение экрана: {cur[0]}x{cur[1]} -> {w}x{h}")
        time.sleep(2)
    else:
        _res_failed = (w, h, cur)
        log(f"не удалось выставить разрешение {w}x{h} (видеодрайвер не даёт такой режим) - "
            f"остаётся {cur[0]}x{cur[1]}")


_fs_presses = 0


def is_fullscreen(hwnd):
    """Окно без рамки/заголовка и на весь монитор (допуск пара пикселей)."""
    import ctypes
    u = ctypes.windll.user32
    style = u.GetWindowLongW(hwnd, -16)                 # GWL_STYLE
    info = window_monitor(hwnd)
    rect = window_rect(hwnd)
    if not info or not rect:
        return None
    mon = info[1]
    covers = (rect[2] - rect[0] >= mon[2] - mon[0] - 2) and (rect[3] - rect[1] >= mon[3] - mon[1] - 2)
    return covers and not (style & 0x00C00000)           # WS_CAPTION


def press_f11(kb=None):
    """F11 через pynput (SendInput со скан-кодом): Roblox не видит keybd_event без скан-кода."""
    kb = kb or keyboard.Controller()
    kb.press(keyboard.Key.f11)
    time.sleep(0.08)
    kb.release(keyboard.Key.f11)


def ensure_fullscreen(hwnd, kb=None):
    """Roblox на весь экран: если окно с рамкой - жмём F11 (не больше 3 раз за запуск,
    чтобы при ошибке распознавания не переключать туда-сюда)."""
    global _fs_presses
    if sys.platform != "win32" or not hwnd:
        return False
    st = is_fullscreen(hwnd)
    if st is None or st or _fs_presses >= 3:
        return False
    import ctypes
    u = ctypes.windll.user32
    _fs_presses += 1
    press_f11(kb)
    time.sleep(2.0)
    rect = window_rect(hwnd)
    log(f"Roblox был в окне - нажал F11; теперь окно {rect[2] - rect[0]}x{rect[3] - rect[1]}" if rect else
        "Roblox был в окне - нажал F11")
    if is_fullscreen(hwnd):
        _fs_presses = 0
    return True


def move_to_primary(hwnd):
    """Перенести окно на основной монитор и развернуть. -> True, если двигали."""
    info = window_monitor(hwnd)
    if not info or info[0]:
        return False
    import ctypes
    u = ctypes.windll.user32
    _, mon, win = info
    fullscreen = win[0] <= mon[0] and win[1] <= mon[1] and win[2] >= mon[2] and win[3] >= mon[3]
    vk_f11 = 0x7A
    if fullscreen:                       # из полноэкранного режима Roblox окно не сдвинуть
        press_f11()
        time.sleep(1.5)
    u.ShowWindow(hwnd, 9)                # SW_RESTORE
    time.sleep(0.3)
    u.SetWindowPos(hwnd, 0, 100, 100, 1280, 720, 0x0004 | 0x0010)   # NOZORDER | NOACTIVATE
    time.sleep(0.5)
    u.ShowWindow(hwnd, 3)                # SW_MAXIMIZE
    time.sleep(0.8)
    if fullscreen:
        u.SetForegroundWindow(hwnd)
        press_f11()
        time.sleep(1.5)
    return True


def window_rect(hwnd):
    if sys.platform != "win32" or not hwnd:
        return None
    import ctypes
    from ctypes import wintypes
    user32 = ctypes.windll.user32
    rect = wintypes.RECT()
    pt = wintypes.POINT(0, 0)
    if not user32.GetClientRect(hwnd, ctypes.byref(rect)) or not user32.ClientToScreen(hwnd, ctypes.byref(pt)):
        return None
    if rect.right < 200 or rect.bottom < 200:
        return None
    return pt.x, pt.y, pt.x + rect.right, pt.y + rect.bottom


def relative_move(m, dx, dy):
    """Относительное движение мыши: только его Roblox видит при зажатой ПКМ."""
    if sys.platform == "win32":
        import ctypes
        ctypes.windll.user32.mouse_event(0x0001, int(dx), int(dy), 0, 0)
    else:
        m.move(dx, dy)


# ---------- деньги ----------

_NW, _NH = 12, 16
_TEMPLATES_RAW = {
    "$": (0.630, "0000000097e3df3403000000001b2a2dbde8f0c8472a2a00248cd1d3eaf8fffbe7d1cd0ba9ccfffce9fffdb1bcc0aa10dafdff9faffce72521372a01f1ffff6498f3e51c00010100ccf7ffd1e3fce52a0f01000090b7fffffffff9d9c83109000b7ebfbfdcf6fffffeef77230002040470def4dbfffffd9b0000000024d2e56ebdfffff81213131334d6e72d9fffffe19dc2c2c2c5fbfdc5f2ffed58a2bfe4f1ffffffffe3c368031c1e8697bdeeebb84521050000000f1135cda21a02000000"),
    "0": (0.832, "000589d0d0e1ffe8d0870700001eddffffffffffffea360350a7fdffbb615887f7ffce0e92d8ffe24c0f0240ecffff66bce9fd9112000015abf1ffced5fffd67000000003ce1ffffebffec480000000027e2fffff7ffdb260000000029e3ffffefffdb260000000026e1ffffdbffe2390000000023e0ffffb8fcf664000000004fe7ffe2a4f7ff890800000abdf8ff825cd9fde6502e2e54d7f8ec2e0b3ff5fffffffffffffd8705001ac4eefbfefffceedf18000000001bc2ebffdd21000000"),
    "1": (0.435, "f4fafffffffffffffffffaf4f4fafffffffffffffffffaf428292a4076c3f0fefffffefd000000082582dcfeffffffff000000030e4eaff4ffffffff000000030c41a0f0ffffffff000000030c41a0f0ffffffff000000030c41a0f0ffffffff000000030c41a0f0ffffffff000000030c41a0f0ffffffff000000030c41a0f0ffffffff000000030c41a0f0ffffffff020100030c41a0f0fffffefd0b0500030c41a0f0fffef6f10a0500020b3c96e7fbfce3d200000000000d3d91d8ed9055"),
    "2": (0.758, "74b7ffffffffffffffec2600f2f8fffffffffffffffdcb2a9dc4c1a32f284cb3fffff0691f3974200200125ffffff37400061c000000032eecfff374000000000000155aebfff37400000000000026bbf8ffe43d00000000000768f2fff57a0b000000001e7accfce78c14000000000b76f9fff18413000000001e67d9ffe59211000000000b7afafff08404000000001950deffffd643383838362978e5fffffffffffffffff8c187dafaf8f9fbfcfdfcf8f5db5d74ccb9c2d1dbe8e1b99a5d"),
    "3": (0.753, "99fcfffffffffffffffff58099fcfffffffffffffffff56818272828282883ffffffc01000000000000b9efffff36d00000000002287e8ffea6f19000000000044c6ffec7d1500000000000b95ebfff3b581000000000012c5ffffffffed620e0000000a6887a3ccffffda860000000000002263e1ffffff000000000000001387f8ffff000000000000000042ebffff273838383838383896effdddbefffffffffffffffffff356e7e7f3f9fefffffff3e7d300000084bdf5ffffff7f000000"),
    "4": (0.900, "0000000000a4fff2760b0000000000002ac0ffda3001000000000017a7f6f27a1200000000000041d2ffc72403000000000040ccf4eb560500000000000a82ffff8a1000000000000340d5ffe2330e7a976d0e000b84fff0830a16cdffb817006fceffbc230016cdffb81700d9ffffbc686875e2ffd4764ae6ffffffffffffffffffffcfffffffffffffffffffffffffc7c7c7c7c7c7ccf4fff0ccc700000000000016cdffb8170000000000000016c8faae16000000000000000f96cc520800"),
    "5": (0.752, "23a6fffffffffffffffff67223a6fffffffffffffffff46223a6ffff9e2828282828260f23a6ffff850000000000000023b3ffed4d0000000000000023b7fff69a2b00000000000023b7ffffebb297979781000023b7ffffffffffffffed5f0013618787878790b5ffffd5630000000000000c3fd4fffce5000000000000000a8effffff00000000000000129effffff3838383838383864ecfffce6fffffffffffffffffffedf77e7e7f0f9fffffffceee0760000005dbbfcfffbdc4b000000"),
    "6": (0.815, "000039d9ffffffffffffe3220005b9eaffffffffffffe30918b1f6fce7422828282824018bd1ffff6307000000000000c3f2ff781200000000000000ccffff430000000000000000daffffb29797979797971700e3ffffffffffffffffff7b03e3ffffffa5878787d7f8e16eceffffb225000000aaf1ffe3aff7ff430000000079f1ffe3ade8ff6b0000000044f1ffe38dd6ffdb32070633bdf4ffb81885f8ffe74240ecffffdd21001ac1e9fcffffffefe8231a00000012e3ffffff550e0000"),
    "7": (0.797, "ffffffffffffffffffffffffffffffffffffffffffffffffffffff7b333333a3ffffffebffffd4190000008effffffaac3c35300000017c8ffffc32e4848030000004de8ffff8a00000000000000aaf6fff73f00000000000000d9ffffc90000000000000032ebfff550000000000000129effffce040000000000003bc9fff6650000000000000081f5ffde0a00000000000010cbfff8ba0000000000000049ffffdf5e000000000000024afdfdd4130000000000001246eee86b0000000000"),
    "8": (0.806, "000faaaaffffffffaaaa0f000064ffffffffffffffff4e08a4e7ffff9b70709bfffff209b3ffffa70b00000beaffff4badcdff7700000000e4ffff76aab9fff62200005af6ffff0978b9ffff7a65659cffffa30400b9ffffffffffffffff61052cdafff2afafafc7ffffff31d2ffffc10000001ff4ffffd2ffffff3a00000000b3f8ffffffffff3a0000000018eaffffecf0ff520b00001ebdeeffdc9db9ffff461b1be3fffff20900b0eff2fffffffff7f1a2080000001bffffffff55150000"),
    "9": (0.790, "003a8080d8d883aa801500002664dadaffffffffdad00e065d9fffe8949494bfffffa12acfdfffc22020202beaffff5fffffff8f00000000e4ffffeacdffff5500000000e4ffffffaed6ff9f4c4c4c4cf4ffffff94b9ffffe8e8e8e8ffffffff149ed7e4ffffebd3f2ffffff00125566cbcb873ea0ffffff000000000f0f0f0f8fffffd6000000000000000fdeffff5e000d1c1c131c1c44ffffe6120064f7f7d3f7f7f7ffee15000060fffffffffbf6f3680000000fffffffffd47604040000"),
}
_templates = None


def _get_templates():
    global _templates
    if _templates is None:
        _templates = {
            ch: (np.frombuffer(bytes.fromhex(hx), dtype=np.uint8).reshape(_NH, _NW).astype(np.float32) / 255.0, asp)
            for ch, (asp, hx) in _TEMPLATES_RAW.items()
        }
    return _templates


def _runs(v):
    out, start = [], None
    for i, x in enumerate(v):
        if x and start is None:
            start = i
        elif not x and start is not None:
            out.append((start, i))
            start = None
    if start is not None:
        out.append((start, len(v)))
    return out


def _find_icon(m):
    lines = [(y, a, c - a) for y, row in enumerate(m) for a, c in _runs(row) if c - a >= 10]
    best = None
    for y, x, length in lines:
        for y2, x2, length2 in lines:
            h = y2 - y + 1
            if h < 8 or abs(x2 - x) > max(2, 0.06 * length) or abs(length2 - length) > max(3, 0.1 * length):
                continue
            if not (1.2 * h < length < 2.3 * h):
                continue
            if m[y:y2 + 1, x:x + 2].any(axis=1).mean() < 0.9:
                continue
            if best is None or h > best[1] - best[0] + 1:
                best = (y, y2, x + length)
    return best


def _segment(rgb):
    r = rgb[..., 0].astype(np.int16)
    g = rgb[..., 1].astype(np.int16)
    b = rgb[..., 2].astype(np.int16)
    m = (g > 110) & (g - r > 30) & (g - b > 30)
    icon = _find_icon(m)
    if icon is None:
        return None
    yt, yb, icon_end = icon
    h = yb - yt + 1
    y0 = max(0, yt - max(1, h // 8))
    y1 = min(m.shape[0], yb + 1 + max(2, h // 6))
    band = m[y0:y1, icon_end:]
    colsum = band.sum(0)
    spans, prev_end = [], 0
    for a, c in _runs(colsum > 0):
        # между значком и суммой зазор бывает больше, чем между цифрами: узкая сумма ($11,110)
        # стоит правее. Раньше из-за этого такая сумма не читалась совсем.
        if a - prev_end > (2.2 if not spans else 1.0) * h:
            break
        prev_end = c
        w = c - a
        n = int(round(w / (0.62 * h))) if w > 0.9 * h else 1
        if n <= 1:
            spans.append((a, c))
            continue
        cuts = [a]
        for k in range(1, n):
            mid = a + w * k / n
            lo, hi = int(mid - 0.15 * h), int(mid + 0.15 * h) + 1
            cuts.append(lo + int(np.argmin(colsum[lo:hi])))
        cuts.append(c)
        spans += [(cuts[i], cuts[i + 1]) for i in range(n)]
    glyphs = []
    for a, c in spans:
        gl = band[:, a:c]
        ys = np.where(gl.sum(1) > 0)[0]
        if len(ys) == 0 or ys[-1] + 1 - ys[0] < 0.6 * h:
            continue
        gl = gl[ys[0]:ys[-1] + 1]
        xs = np.where(gl.sum(0) > 0)[0]
        gl = gl[:, xs[0]:xs[-1] + 1]
        glyphs.append((gl, gl.shape[1] / gl.shape[0]))
    return glyphs


MONEY_TOL = 0.18     # насколько цифра суммы может отличаться от образца (было 0.12: на части компьютеров
                     # суммы с семёркой и крупные суммы не читались, и бот ждал денег, которые уже есть)


def _cut_comma(gl, asp, base_h):
    """Запятая после семёрки ($7,260) на части экранов прилипает к её ножке, и «7,» читается как один
    непонятный знак - сумма с 7 тысячами не читалась вовсе. Такой знак выдаёт себя тем, что он выше
    остальных цифр: запятая свисает ниже строки. Срезается всё ниже строки и правые столбцы,
    где после этого точки остались только в самом низу. base_h - обычная высота цифры в этой сумме."""
    g = np.asarray(gl).astype(bool)
    h, w = g.shape
    if not base_h or h < 1.12 * base_h or w < 8:
        return gl, asp
    g = g[:int(round(base_h))]                      # всё, что ниже строки, - хвост запятой
    hh = g.shape[0]
    cut = w
    while cut > 0:
        r = np.nonzero(g[:, cut - 1])[0]
        if len(r) and r[0] < 0.7 * hh:
            break
        cut -= 1
    if cut < 0.45 * w:
        return gl, asp
    left = g[:, :cut]
    rows = np.nonzero(left.any(axis=1))[0]
    cols = np.nonzero(left.any(axis=0))[0]
    if len(rows) < 6 or len(cols) < 4:
        return gl, asp
    left = left[rows[0]:rows[-1] + 1, cols[0]:cols[-1] + 1]
    return left.astype(np.asarray(gl).dtype), left.shape[1] / left.shape[0]


def _money_from_glyphs(glyphs, cut):
    templates = _get_templates()
    chars = []
    base_h = float(np.median([np.asarray(g).shape[0] for g, _a in glyphs[1:]])) if len(glyphs) > 2 else 0
    for i, (gl, asp) in enumerate(glyphs):
        if cut and i:
            gl, asp = _cut_comma(gl, asp, base_h)
        small = Image.fromarray((gl * 255).astype(np.uint8)).resize((_NW, _NH), Image.BILINEAR)
        v = np.asarray(small, dtype=np.float32) / 255.0
        best, score = None, 1e9
        for ch, (tv, ta) in templates.items():
            s = float(((v - tv) ** 2).mean()) + 0.6 * (asp - ta) ** 2
            if s < score:
                best, score = ch, s
        if score > MONEY_TOL:
            return None
        chars.append(best)
    if chars[0] != "$" or "$" in chars[1:]:
        return None
    return int("".join(chars[1:]))


def read_money_image(img):
    glyphs = _segment(np.asarray(img.convert("RGB")))
    if not glyphs or not (2 <= len(glyphs) <= 8):
        return None
    v = _money_from_glyphs(glyphs, cut=False)
    if v is None:                       # не прочиталось - возможно, к цифре прилипла запятая ($7,260)
        v = _money_from_glyphs(glyphs, cut=True)
    return v


# ---------- юниты, слоты, режимы ----------

# цена постановки, цены прокачек (ур.0->1, 1->2, ...) и выручка от продажи по уровням
UNITS = {
    "tcam":    {"title": "Titan Camcorderman", "short": "Titan Camcorder",      "icon": "🎥", "price": 7650,
                "up": [3325, 5100, 13925, 13875, 21425, 21375, 25475, 17850],
                "sell": [3825, 5490, 8040, 15000, 21940, 32650, 43340, 56075, 65000]},
    # Titan Screen Man - замена Titan Camcorderman: Teleport с 4 ур., Hook and Punch с 7 ур.
    # цены трёх титанов - после ребаланса 17.11.2026 (видео меню юнитов); продажа = половина вложенного
    "ttv":     {"title": "Titan Screen Man", "short": "Titan Screen",      "icon": "📺", "price": 8600,
                "up": [3500, 5650, 15475, 15425, 23925, 23875, 28400, 20150],
                "sell": [4300, 6050, 8875, 16615, 24325, 36290, 48225, 62425, 72500]},
    "tspk":    {"title": "Titan Amplifierman", "short": "Titan Amplifier",     "icon": "📢", "price": 6975,
                "up": [2875, 4575, 12850, 12800, 19825, 19775, 23525, 16800],
                "sell": [3490, 4925, 7215, 13640, 20040, 29950, 39840, 51600, 60000]},
    "tv":      {"title": "Scientist TV Man", "short": "TV Man",      "icon": "📺", "price": 750,
                "up": [450, 800], "sell": [375, 600, 1000]},
    "plunger": {"title": "Plunger Cameraman 2.0", "short": "Plunger", "icon": "🪠", "price": 700,
                "up": [450, 800, 2300, 2250, 3000, 2050, 4500],
                "sell": [350, 575, 975, 2125, 3250, 4750, 5775, 8025]},
    "speaker": {"title": "Dark Speakerman", "short": "Speakerman",       "icon": "🔊", "price": 675,
                "up": [415, 740], "sell": [340, 525, 895]},
    "farm":    {"title": "Scientist Cameraman", "short": "Ферма",   "icon": "💰", "price": 250,
                "up": [375, 625, 1000, 2000], "sell": [125, 315, 625, 1125, 2125]},
}
PRICE_TO_TYPE = {u["price"]: t for t, u in UNITS.items()}
# цены из таблицы (без скидок). У юнита с трейтом Shiny цена ниже на 5% (ферма $238 вместо $250):
# тогда цена постановки берётся со слота, а выручка от продажи пересчитывается в той же пропорции
UNIT_BASE = {t: {"price": u["price"], "sell": list(u["sell"])} for t, u in UNITS.items()}
PRICE_SLACK = 0.06           # насколько цена на карточке может отличаться от табличной
SHINY_DISCOUNT = 0.05
# цена шайни-юнита -> тип (округление в игре вверх: 237.5 -> 238; на всякий случай беру и вниз)
def _shiny_prices():
    out = {}
    for t, u in UNITS.items():
        v = u["price"] * (1 - SHINY_DISCOUNT)
        for p in (int(v + 0.5), int(v), int(v) + (1 if v != int(v) else 0)):
            if p not in PRICE_TO_TYPE:
                out.setdefault(p, t)
    return out


SHINY_TO_TYPE = _shiny_prices()


def fuzzy_type(price, taken=()):
    """Тип юнита по цене, близкой к табличной (в пределах PRICE_SLACK), если такой тип один."""
    near = sorted((abs(price - b["price"]) / b["price"], t) for t, b in UNIT_BASE.items() if t not in taken)
    near = [t for d, t in near if d <= PRICE_SLACK]
    return near[0] if len(near) == 1 else None


def apply_slot_prices(slots, prices):
    """Подстроить цены юнитов под то, что написано на карточках в этом матче. Возвращает список отличий."""
    notes = []
    for t, base in UNIT_BASE.items():
        actual = base["price"]
        if t in slots and 0 < slots[t] <= len(prices) and prices[slots[t] - 1]:
            actual = prices[slots[t] - 1]
        k = actual / base["price"]
        UNITS[t]["price"] = actual
        UNITS[t]["sell"] = [int(round(v * k)) for v in base["sell"]]
        if actual != base["price"]:
            shiny = SHINY_TO_TYPE.get(actual) == t
            notes.append(f"{UNITS[t]['title']} ${actual} вместо ${base['price']}" + (" (шайни)" if shiny else ""))
    return notes


def _nearest(values, x, slack=PRICE_SLACK, floor=4):
    """Индекс единственного значения списка, близкого к x; None, если такого нет или их несколько."""
    near = [i for i, v in enumerate(values) if abs(v - x) <= max(floor, slack * v)]
    return near[0] if len(near) == 1 else None

MODES = {
    "hard":      {"title": "HARD",      "waves": 25, "need": ["tv"], "need_any": [["plunger", "speaker"]]},
    "nightmare": {"title": "NIGHTMARE", "waves": 30, "need": ["tv", "plunger", "farm"], "need_any": []},
}


def mode_key():
    m = str(SETTINGS.get("mode", "hard")).lower()
    return m if m in MODES else "hard"


def sell_value(utype, level):
    s = UNITS[utype]["sell"]
    return s[min(level, len(s) - 1)]


def _components(m):
    """Связные области булевой маски (8-связность): список (x0, y0, x1, y1), x1/y1 не включая."""
    H, W = m.shape
    seen = np.zeros_like(m, dtype=bool)
    out = []
    for y, x in zip(*np.nonzero(m)):
        if seen[y, x]:
            continue
        stack = [(y, x)]
        seen[y, x] = True
        x0 = x1 = x
        y0 = y1 = y
        while stack:
            cy, cx = stack.pop()
            x0, x1, y0, y1 = min(x0, cx), max(x1, cx), min(y0, cy), max(y1, cy)
            for ny in (cy - 1, cy, cy + 1):
                for nx in (cx - 1, cx, cx + 1):
                    if 0 <= ny < H and 0 <= nx < W and m[ny, nx] and not seen[ny, nx]:
                        seen[ny, nx] = True
                        stack.append((ny, nx))
        out.append((int(x0), int(y0), int(x1) + 1, int(y1) + 1))
    return out


def _read_green_number(m, tol=0.16, dollar=True):
    """Число из маски зелёного текста одной надписи ($7,500 -> 7500). Запятая отбрасывается.
    dollar=False - число без знака доллара (цены и жетоны в Research Shop)."""
    comps = _components(m)
    if not comps:
        return None
    h = max(c[3] - c[1] for c in comps)
    if h < 6:
        return None
    comps = sorted((c for c in comps if c[3] - c[1] >= 0.6 * h), key=lambda c: c[0])
    if not dollar and comps:
        top = sorted(c[1] for c in comps)[len(comps) // 2]
        comps = [c for c in comps if c[1] <= top + 0.3 * h]      # запятая начинается с середины строки
    templates = _get_templates()
    glyphs = []
    for x0, y0, x1, y1 in comps:
        w = x1 - x0
        n = int(round(w / (0.62 * h))) if w > 1.0 * h else 1
        if n <= 1:
            glyphs.append(m[y0:y1, x0:x1])
            continue
        colsum = m[y0:y1, x0:x1].sum(0)
        cuts = [0]
        for k in range(1, n):
            mid = w * k / n
            lo, hi = max(0, int(mid - 0.15 * h)), min(w, int(mid + 0.15 * h) + 1)
            cuts.append(lo + int(np.argmin(colsum[lo:hi])))
        cuts.append(w)
        for i in range(n):
            gl = m[y0:y1, x0 + cuts[i]:x0 + cuts[i + 1]]
            gy = np.where(gl.sum(1) > 0)[0]
            gx = np.where(gl.sum(0) > 0)[0]
            if len(gy) and len(gx):
                glyphs.append(gl[gy[0]:gy[-1] + 1, gx[0]:gx[-1] + 1])
    chars = []
    for gl in glyphs:
        asp = gl.shape[1] / gl.shape[0]
        small = Image.fromarray((gl * 255).astype(np.uint8)).resize((_NW, _NH), Image.BILINEAR)
        v = np.asarray(small, dtype=np.float32) / 255.0
        best, score = None, 1e9
        for ch, (tv, ta) in templates.items():
            if ch == "$" and not dollar:
                continue
            sc = float(((v - tv) ** 2).mean()) + 0.6 * (asp - ta) ** 2
            if sc < score:
                best, score = ch, sc
        if score > tol:
            return None
        chars.append(best)
    if not dollar:
        if not chars or "$" in chars:
            return None
        chars = ["$"] + chars
    if len(chars) < 2 or chars[0] != "$" or "$" in chars[1:]:
        return None
    try:
        return int("".join(chars[1:]))
    except ValueError:
        return None


PANEL_SELL_BOX = (0.1445, 0.708, 0.196, 0.752)    # цена на кнопке Sell [X] в панели выбранного юнита


def _price_fix(v):
    """Все цены в игре кратны 5. Крупная пятёрка в трёхзначной цене ($625 у фермы 1 ур.) иногда
    распознаётся как тройка - тогда панель «не читалась» и бот без конца выделял и отпускал ферму."""
    if v is not None and v % 5 == 3:
        return v + 2
    return v


def read_panel_sell(img):
    """Цена продажи из панели выбранного юнита (белые цифры на красной кнопке) или None.
    По ней однозначно узнаётся настоящий уровень юнита."""
    w, h = img.size
    box = PANEL_SELL_BOX
    a = np.asarray(img.crop((int(box[0] * w), int(box[1] * h), int(box[2] * w), int(box[3] * h)))
                   .convert("RGB")).astype(np.int16)
    m = a.min(axis=2) > 185
    if m.mean() > 0.5 or m.sum() < 12:
        return None
    return _price_fix(_read_green_number(m, tol=0.20))   # мягче к форме цифр: число всё равно сверяется с таблицей цен


PANEL_UP_BOX = (0.1515, 0.563, 0.228, 0.608)       # цена на кнопке Upgrade [E]


def read_panel_upgrade(img):
    """Цена следующей прокачки из панели выбранного юнита или None (на максимуме там прочерк)."""
    w, h = img.size
    box = PANEL_UP_BOX
    a = np.asarray(img.crop((int(box[0] * w), int(box[1] * h), int(box[2] * w), int(box[3] * h)))
                   .convert("RGB")).astype(np.int16)
    m = a.min(axis=2) > 185
    if m.mean() > 0.5 or m.sum() < 12:
        return None
    return _price_fix(_read_green_number(m, tol=0.20))   # мягче к форме цифр: число всё равно сверяется с таблицей цен


PANEL_SELL_LABEL_BOX = (0.085, 0.712, 0.135, 0.748)   # надпись "Sell [X]" в панели юнита


def panel_open(img):
    """Открыта ли панель выбранного юнита (видна белая надпись Sell [X] на тёмной кнопке)."""
    w, h = img.size
    box = PANEL_SELL_LABEL_BOX
    a = np.asarray(img.crop((int(box[0] * w), int(box[1] * h), int(box[2] * w), int(box[3] * h)))
                   .convert("RGB")).astype(np.int16)
    white = float((a.min(axis=2) > 185).mean())
    dark = float((a.max(axis=2) < 60).mean())
    return 0.08 < white < 0.3 and dark > 0.5


def _dense_span(mask, fill=0.7):
    """Границы участка, где mask почти сплошная: от первого до последнего True, если между ними
    True не меньше доли fill (строки с текстом и линиями внутри окна не должны рвать участок)."""
    idx = np.nonzero(mask)[0]
    if len(idx) == 0:
        return 0, 0
    a, b = int(idx[0]), int(idx[-1]) + 1
    while b - a > 4 and len(idx) / (b - a) < fill:      # срезаю редкие выбросы по краям
        gaps = np.diff(idx)
        k = int(np.argmax(gaps))
        idx = idx[:k + 1] if k + 1 >= len(idx) - (k + 1) else idx[k + 1:]
        a, b = int(idx[0]), int(idx[-1]) + 1
    return a, b


def disconnect_dialog(img):
    """Окно ошибки Roblox (Disconnected, Connection Failed, кик): серый прямоугольник по центру экрана
    с белой кнопкой справа внизу. Фон под ним размыт и тоже бывает сероватым, поэтому окно ищется
    как сплошной блок точного серого цвета. -> точка белой кнопки в долях кадра или None."""
    w, h = img.size
    x0, y0, x1, y1 = int(0.25 * w), int(0.20 * h), int(0.75 * w), int(0.80 * h)
    a = np.asarray(img.crop((x0, y0, x1, y1)).convert("RGB")).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    grey = (abs(r - 57) < 6) & (abs(g - 59) < 6) & (abs(b - 61) < 6)
    cx0, cx1 = _dense_span(grey.mean(axis=0) > 0.20)           # столбцы, где серого много
    if cx1 - cx0 < 0.12 * w:
        return None
    ry0, ry1 = _dense_span(grey[:, cx0:cx1].mean(axis=1) > 0.45)
    bw, bh = cx1 - cx0, ry1 - ry0
    if bh < 0.10 * h or not (1.1 < bw / max(1, bh) < 2.6):
        return None
    box = grey[ry0:ry1, cx0:cx1]
    if box.mean() < 0.55:                                      # внутри рамки должно быть в основном серое
        return None
    low = a[ry0 + int(0.62 * bh):ry1, cx0:cx1]                 # нижняя часть окна: две кнопки
    white = low.min(axis=2) > 235
    if white.mean() < 0.10:
        return None
    wy, wx = np.nonzero(white)
    if float(np.median(wx)) < 0.5 * bw:                        # белая кнопка - правая
        return None
    cx = x0 + cx0 + float(np.median(wx))
    cy = y0 + ry0 + int(0.62 * bh) + float(np.median(wy))
    return cx / w, cy / h


def level_by_sell(utype, price):
    """Уровень юнита по цене продажи; None - цена не из таблицы этого юнита."""
    sells = UNITS.get(utype, {}).get("sell", [])
    if price in sells:
        return sells.index(price)
    if any(price in u["sell"] for t, u in UNITS.items() if t != utype):
        return None                                  # это точная цена другого юнита
    return _nearest(sells, price)                    # со скидкой цены продажи чуть отличаются от таблицы


HOTBAR_BOX = (0.25, 0.885, 0.75, 0.965)


def read_hotbar(img):
    """Цены под карточками юнитов слева направо: [(x_центр в долях кадра, цена или None), ...]."""
    w, h = img.size
    x0, y0 = int(HOTBAR_BOX[0] * w), int(HOTBAR_BOX[1] * h)
    a = np.asarray(img.crop((x0, y0, int(HOTBAR_BOX[2] * w), int(HOTBAR_BOX[3] * h))).convert("RGB")).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    m = (g > 105) & (g - r > 28) & (g - b > 22)
    H, W = m.shape
    colsum = m.sum(0)
    runs = _runs(colsum > 0)
    if not runs:
        return []
    # высота текста: типичная высота зелёных столбцов
    heights = []
    for a_, c_ in runs:
        ys = np.where(m[:, a_:c_].sum(1) > 0)[0]
        heights.append(ys[-1] + 1 - ys[0])
    th = float(np.median([x for x in heights if x >= 5] or [8]))
    words, cur = [], [runs[0]]
    for rn in runs[1:]:
        if rn[0] - cur[-1][1] > 0.9 * th:
            words.append(cur)
            cur = [rn]
        else:
            cur.append(rn)
    words.append(cur)
    out = []
    for wd in words:
        xa, xb = wd[0][0], wd[-1][1]
        if xb - xa < 1.5 * th:
            continue
        val = _read_green_number(m[:, xa:xb])
        out.append(((x0 + (xa + xb) / 2) / w, val))
    return out


def detect_slots(img):
    """-> ({тип: номер слота}, [цены по слотам]) по ценам на карточках."""
    prices = [p for _, p in read_hotbar(img)]
    slots = {}
    for i, p in enumerate(prices, 1):
        t = PRICE_TO_TYPE.get(p)
        if t and t not in slots:
            slots[t] = i
    for i, p in enumerate(prices, 1):                # шайни-юнит: цена ровно на 5% ниже табличной
        t = SHINY_TO_TYPE.get(p)
        if t and t not in slots:
            slots[t] = i
    for i, p in enumerate(prices, 1):                # другая небольшая скидка - ближайший свободный тип
        if p and p not in PRICE_TO_TYPE and i not in slots.values():
            t = fuzzy_type(p, taken=slots)
            if t:
                slots[t] = i
    return slots, prices


def missing_units(slots, mode):
    md = MODES[mode]
    miss = [UNITS[t]["title"] for t in md["need"] if t not in slots]
    for group in titan_groups(slots):                # Amplifierman обязателен, плюс Screen Man или Camcorderman
        if not any(t in slots for t in group):
            miss.append(" или ".join(UNITS[t]["title"] for t in group))
    for group in md["need_any"]:
        if not any(t in slots for t in group):
            miss.append(" или ".join(UNITS[t]["title"] for t in group))
    return miss


# ---------- экраны ----------

def is_end_image(img):
    a = np.asarray(img.convert("RGB")).astype(np.int16)
    w = a.shape[1]

    def median(x_frac):
        part = a[:, int(x_frac[0] * w):int(x_frac[1] * w)].reshape(-1, 3)
        return np.median(part, axis=0)

    r, g, b = median(END_GREEN_X)
    r2, g2, b2 = median(END_RED_X)
    return bool(g > 120 and g - r > 80 and g - b > 80 and 35 <= r2 <= 110 and g2 < 25 and b2 < 35)


def is_ready_image(img):
    r, g, b = np.median(np.asarray(img.convert("RGB")).reshape(-1, 3), axis=0)
    return bool(g > 70 and g - r > 50 and g - b > 50)


def vote_diff(img):
    small = np.asarray(img.convert("L").resize((32, 18), Image.BILINEAR)).astype(np.int16).reshape(-1)
    return float(np.abs(small - np.asarray(VOTE_SIG, dtype=np.int16)).mean())


def crop_frac(img, box):
    w, h = img.size
    return img.crop((int(box[0] * w), int(box[1] * h), int(box[2] * w), int(box[3] * h)))


# ---------- лобби: поиск кнопок по цвету ----------

def _blobs(mask):
    """Связные области маски: список словарей (area, cx, cy, w, h) в долях кадра."""
    H, W = mask.shape
    seen = np.zeros_like(mask, dtype=bool)
    out = []
    ys, xs = np.nonzero(mask)
    for y0, x0 in zip(ys.tolist(), xs.tolist()):
        if seen[y0, x0]:
            continue
        stack = [(y0, x0)]
        seen[y0, x0] = True
        n, x_lo, x_hi, y_lo, y_hi = 0, x0, x0, y0, y0
        while stack:
            y, x = stack.pop()
            n += 1
            x_lo, x_hi, y_lo, y_hi = min(x_lo, x), max(x_hi, x), min(y_lo, y), max(y_hi, y)
            for yy, xx in ((y + 1, x), (y - 1, x), (y, x + 1), (y, x - 1)):
                if 0 <= yy < H and 0 <= xx < W and mask[yy, xx] and not seen[yy, xx]:
                    seen[yy, xx] = True
                    stack.append((yy, xx))
        out.append({"area": n / (W * H), "cx": (x_lo + x_hi + 1) / 2 / W, "cy": (y_lo + y_hi + 1) / 2 / H,
                    "w": (x_hi - x_lo + 1) / W, "h": (y_hi - y_lo + 1) / H})
    out.sort(key=lambda b: -b["area"])
    return out


def _blobs_green_buttons(img):
    """Зелёные кнопки (Teleport в меню телепорта) в нижней половине экрана."""
    w, h = img.size
    a = np.asarray(img.convert("RGB").resize((640, max(1, round(640 * h / w))), Image.BOX)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    return [x for x in _blobs((g > 100) & (g - r > 55) & (g - b > 55))
            if 0.07 <= x["w"] <= 0.30 and 0.035 <= x["h"] <= 0.14 and x["cy"] > 0.5]


# ---------- Research Shop (сток в хабе) ----------

STOCK_FRAME_W = 0.6422       # ширина фиолетовой рамки окна Sample Exchange / Research Shop в долях экрана (16:9)
STOCK_TAB = (0.1157, 0.0893)         # кнопка RESEARCH SHOP / SAMPLE EXCHANGE - в долях рамки
STOCK_ALL = (0.579, 0.867)           # кнопка ALL на вкладке Sample Exchange
STOCK_EXCHANGE = (0.8025, 0.867)     # кнопка EXCHANGE
STOCK_TOKENS_BOX = (0.045, 0.195, 0.215, 0.255)   # число YOUR TOKENS
STOCK_SIG = (96, 10)                 # размер отпечатка названия предмета
# известные предметы: ключ -> (название, количество, отпечатки названия). Отпечатки сняты со скриншотов
# магазина (2557x1437, 2560x1440, 1920x1080); Plunger нарисован тем же шрифтом (Montserrat Black)
STOCK_KNOWN = {
    "sound_enhancer": ("Sound Enhancer", 1, [
        "14.455:677e938c6e63636b85927c676381957462658e8a799677636286936b7e9798978f7065626262628a989898988781946f62658e8a6786926e626a93856262637e977a62626b928864627496776263687d93876c6c94989898987a8c9898957d668a9796978a677091979697896b81957462658e8a7996906b6286936b7e97979597977a646262628a989694948481978a65658e8a6786926e626a93856262668a988864626b92977462749677626b8b97969792769498959494798c9896969786958e80847966869586828b967d81957462658e8a799697816486936b7e97897d8491906f6262628a96837a7a7381979675668e8a6786926e626a938562626d9397916c626b92988b68749677627e968b8185877394927d7a7a708c948280909496866e63626c8f8965626c928884957462658e8a799698917087936b7e967562627a967d6262628a957c777565819798896d8f8a6786947e777b948562627994879177636b929896797796776689916c6263676b948f777771688c8f686280978b978b7d7278957d63626789918b957462658e8a799698978890936b7e967562626e967f6262628a989898946b8197989586948a6786989898989885626486886b8c84666b9298988e8996776d9288666262626b949898988a688c9378768b95707c8c978e83957d63626789918a957562658e8a79968c8c9798936b7e967562626e967f6262628a98928d8a698196899097988a678698938e919785626b9088748e8e6d6b929289959896776d9288666262626b94978f8d82688c979393978b62636e829585918965626c92887c947e62688f8878967e709098936b7e967562627a967d6262628a95786f6e648195777795988a6786947a6f769485637495948f9694786b928c6f879896776689916c6263676b948e706f6c688c98989893758285808b9579879586828b967d6d91918387958278967c647c98936b7e97897d8391906e6262628a96837a7a738195746686988a6786926e626a938566829898989897826c928b6671939677627e968b8185877394927d7a7a708c9276819472969796978a677091979697896b647e979797927076967c636a8f936b7e97979597967a646262628a98969494848195746372938a6786926e626a9385688c8d6d6d6f8a9072928b6666839677626b8b97969792759498959494798c8f686d9186708a94826962636b85927c676362667892896c6375967c63637f916b7e9798978f6f65626262628a98989898878195746265868a6786926e626a938579947c626262839576928b66627092776263687d93866c6c94989898987a8c8f68638795",
        "13.889:62728f907562626273908d6f626d9789676d8d92667d967a62638f8e6f8c9797957e626262626269959797979776908d6d62749783739786666283947662647997736362628f8d6e6272978566626383948166739797979796739797978d70626f9296968b6d658092969691746e9789676d8d92667d978d6d638f8e6f8c97979793876c6262626995979797977690968166749783739786666283947662678f978d6762628f968267729785666e889497948a7597979797967397979796916f8a9279706e6669928a7377908d729789676d8d92667d979681678f8e6f8c937c718295736262626995907670706890979373759783739786666283947662689397946962628f9793747397856677957e70817474978b72706f6e9790757c968491957a6462627b967d646682957a9789676d8d92667d97979276908e6f8c91726372958666626269958e6c626264909797887a978373978b6762839476627a8f86927762628f9797897997856b88956e626a657397886662626c978b696f91927f978d81796889927462627c96839789676d8d92667d9797978b948e6f8c9071626b8f9269626269959384807264909797958b9783739793827484947662878a6e8b8662628f9797958b978570948e6862626273979081806d6c978b697092906a7f8392917189927462627c9682968c686f8f90667d97909197978e6f8c9071626b8f9269626269959797977f6490948e959797837397979783849476688d8f7a8e8d66628f948e9597978570948e686262627397979797756c97927e8397806464688197787b957d64668295778f926a729388657d96838195978e6f8c91726372958666626269959488857564908f7b8c979783739791867884947675939797979272628f907b8b9797856b88956e626a6573979286856e6c97979797906d6f747077977769928a7377908d6b8297767e9779647d967c6d8a978e6f8c937c7181957362626269959076707068908e6e7a949783739786666283947680968b8a8b9680628f8e6f789397856677957e70807474978b72706f6e97948d948668859497958e72657f92969691736375919695906d627d967c6276938e6f8c97979793886d62626269959797979776908e6e67879683739786666283947984916662659183658f8e6f66869685666e889497948a7597979797967397896c8796746882938a6a62626273908d6f62626271908b6d62627d967c6263868e6f8c9797957f626262626269959797979776908e6e62709183739786666283948895896562658f93738f8e6f626e91856662638394816673979797979673978968739686",
    ]),
    "detachable_knife": ("Detachable Knife", 1, [
        "15.273:989897886d646d95989898917a9598989898856475957d64636366758e8c6e698b8d676379956f63636f948265636a909898947e677298796363638298989898826363688b8d66647c93759084646382926b89916b8d989898987c95989898989896959794726d959794948e78919597979482668198896663647f96969693768b8d676379956f63637a988d6a636a90979596967e73987963636382989694947f6363688b8d666e907f6a9095716382926b89916b8d979594947b959794949497887d86938971958f7c7a776c788193907d716a8b97926e636c928f838388738b8d676379956f636687979474636a90917f83948a7698796363638297847a7a706363688b8d6d858c696a9098886582926b89916b8d947f7a7a74958f7c7a7a96746365839478958a77776b6363688d856463729188907864759477636367688b91797784956f636c90898f7f646a908d787a908475987963636382967d7774656363688b92889176636a9098947384926b89916b8d91736f6c6d958a77776c9674636379957995989898796363688d8564637d8d6e8a846783926e636363678b98989898956f63769070838b686a9098989895777298796363638298989891696363688b9898916c636a9098988a8f926b89916b8d97908d816d959898987c9674636379957995968f8d746363688d856467898d758c8e6e82926e636363678b97918e93956f658291768792706a9096909094807598796363638298938d88686363688b98989579636a90908a9698926b89916b8d989898896d95968f8d77967463658394789589706f686363688d85646c91968f959476759477636367688b91746f81956f698b979094967c6a908d7371898f79987963636382967a6f6e646363688b978a928b686a90886f8d98926b89916b8d917877716d9589706f6897887d86938970958f7c7a776663688d8564799698989897806d928f838388738b8d676379956f749398989897866c90917f7e90917a988d85846c8297847a7a706363688b906f8094796a9087667996926b89916b8d8d6563636d958f7c7a7a9896949793716d959794948e6963688d85648391726e6f898d6b7e96969693768b8d676379956f7c94766e6f83917390979595978d78989797977182989694947f6363688b8d676c908e71908766698c926b89916b8d8d6563636d9597949494989897886c646d95989898916963688d856c918466636382936c66758f8c6e698b8d67637995758c8a67636379967790989897866b7298989898728298989898826363688b8d66637b9683928766637b906b89916b8d8d6563636d9598989898",
        "15.364:919799937867628497999897808798989898916c688c906a6262636c87917b667f9473626b917f6262678b90696264869999988a6b6a91886262627599989798896262648a916a627592788e8a64627c956c85946c8c989794977d95989898989199959697896581969592947d8694979896916d7093947062626f9196969482809371626b948262626f92977262648797959598876d928762626274959694948862626384916a688d87698d9875627b936c84946c8b979593937b9495959495949481828a95758597847c7b71717c8c958278677b95967f636483958682897c7c9474626c937f62637995967f6464869583828f917392876262627398887a7c7562626485906f7d916c678a978c677b936c86936b8a95827a777494917c787b8e8d666270918385957c76736462627c926d6266878f8b8968698e89656263637f9580767c947e626686908a8b686488947c778a8c6e9288626262749782767667626263859487907b62678b9995777e966e86936b8a91746f6c6c958b76766c948c6662668e8586999897906762627c926d626c8e7a76936e72937f636262627f979896979781626d8d7c759270648898989898816b928762626275969897986e626264879898957062688c99978c8e956d86946c8c97908e836c959898977c928d6762668e858398928d876662627c936e6278937f7c957872927d636262627f96968f9296816276937e7d9679658798929097867093876262627597958d8e6b626264889898967c63678a93899798956d86946c8c989897896c9596908d78908d66626e92868396786f6d63626279916f628296939196866c8c87646264647e9580717894806483969190988668879378717f9479928762626274987e6f6f6562626386988e8d8e6a678a8c6f8997956d85946b8b927976706c9489716f69909382828c9676859583787c6e62627d916f698f989897978d6e85938785877b7e9373626b9282678e97989798906e8494837d89957a90938882727498867c7d7562626486917278957e698e8b667494966d85946c8c8f6662626c938e7c7b7a9198959596886585989693947b62627a90706d947f6d6d7a93786f9398969782809473626b93806c937e6d6d7a917985979695979277929798977d73989793938662626385916b678c90728a8c666788956c85936c8b8f6662626c9597929492919697957d686283979798977b62627a906c80906f62626e957f636b88917a667e9573626b917e80937062626c927f8597979791706c929798977e74979698998b62626487906962759886908b656374926d85946c8b8c6662626c9297989795",
        "13.556:98989892776566919898988c658398989898906578948d65656565657e937d656792856765759878657191966b65658b989897876665879068656570989898987f65656580956d657f94787c987165678a8d79987472989898987e889898989898989897937b66919898988c65839898989890657f978d6565656d89949793826b92856765759878657597966b65658b989898958365879068656570989898987f65656580956d718e8b697c988b65678a8d79987472989898987e8898989898988c76748c9172918e77716e656c7384987e6f6884989376656572967f717b7b6892856765759878667b98977f65658b917871918966879068656570988774716b6565658095707e9475657c98967e678a8d79987472988773716b8892787171988568667b9876918a6b6565656566799876657290839380656783917265696b67928b6c667b9878698c888e8b65658b8f6d658e88658790686565709882686565656565809788908368657c9898907c8e8d79987472987d66656588916e656598836665749878919284817a656565779876657797768c86686991886b65656567929386808798786b967e828f6a658b948581938665879068656570988e828173656565809896987a65657c98989790948d79987472988b818172889585818198836665749878919898988c656565779876678097848e8f716991886b65656567929898968d9878769789899377658b989898978a6a879068656570989898987f656565809898988569657c988f9698988d79987472989898987e8898989898988568667c9876919388867e6565657798766b9098989897796783917265696b6792918685859878869798989784658b9589868f927587906b656570989087867665656580978f8d9572657c987e8a98988d7998747298908786758895898686988c76748d9172918e77716e6565657798766d97908b8d957f6772957f717b7b68928567657598788f938b8b9387698b91787185947a87937a717171988774716b65656580967a779580667c98707291988d79987472987f676565889278717198989897937b66919898988c656565779876759579656a8a906d6d89949793826b9285676575987f908265658192758b989898968a6e879898989475989898987f65656580956d6c89936c7c9870657c968d79987472987b656565889898989898989892776566919898988c6565657798768d8b6b65657a986f65657e937d656792856765759895926f65656e987b8b9898988c6c65879898989475989898987f65656580956d657f96857c987065688a8d79987472987b6565658898989898",
    ]),
    "amplifier_knives": ("Amplifier Knives", 1, [
        "14.273:63637c967d6463698d8e686363647b967a86989896836b6e96876363636a938c699198989898818e90688c9898989888819798968a6d646363636e948565647a9476898f68636b93856a928d7894886563637c9492989898988e66667b918e7363668898896763698d97786363698f967a86989695978f7596876363636a938c6991979594947f8e90688c98959494858197969597906c6363636e9485656e91816789977f646b93856a928d678a8f686368898d8b989694948b688297969693636d9197927063698d988767637694967a8696867f8d958097876363636a938c6991947f7a7a718e90688c95837a7a738196897f8995796463636e94876d878e6a67899892706b93856a928d66819474636d93818598867b7a766e8f9082838063789487917c64698d989370658598967a8693706378948c97876363636a938c699191726f6d668e90688c947b777566819575636f93846663636e948f8892776367899897847094856a928d6474957f6479937685987e7777686f918972656365848a6c8a8968698d989784759298967a86957e7585958497876363636a938c699197908d86688e90688c989898946c8196827580947d6563636e949898906b6367899898938696856a928d636b908a6a868f6a8598989898716784978f7e776c8f8a748c9170698d9693938e9390967a8697949297907796876363636a938c69919898988f688e90688c97928d8a6a8197959196926f6363636e94989895796367899488929798856a928d63658594839084658598938d8d6e636d7c8896947595958f95967c698d907b8f957e80967a8698989689747096876363636a938c699191787773668e90688c94776f6e65819798989883666363636e949689938d69678991717c9798856a928d63637a969794786385987b6f6f666363646c7d98869798989897866b8d8e6a7e8f6a7a967a86947c716b646d969385847b6a938c69918d646363658e90688c95837a7a7381967f789382636363636e948b6e82957c6789916c698e98856a928d63636e9198916e638598867b7a76657c85808898918e6e6e6f8691738d8e686f7a657a967a8693706363636d96989797896a938c69918d646363658e90688c98959494858195756684906c6363636e9486656d908f7189916c637b95856a928d636367889887666385989694948b719097959793977d6363637e96788d8e676465647a967a8693706363636d969898988a6a938c69918d646363658e90688c98989898888195756374947e6563636e948565647a97848d916c636a8c856a928d6363637d977b646385989898988e676d8794866b",
        "13.667:636383906763636e9586676363759483638d9898987a63638691726363637f927a7b999995989072958b709796979899798e989895746363636363819275637897818492776366938d6d8f908e968b63636995848b979897968a63638197866a637793957c63636f96946c6363859783638e989697947f638c91716363637f957b7b97979897947497886f9798999895798d989898927c6363636382937566898d6885968a6c66948e6e8c91778a8d636369957e87989798988a63819598947f637a97968463636f97977e6470909783638d957e71918d6e8d90736363637e96807b958971707071998a70989178706f698e937f72908b6d6363638493737a9171638599957e6a928d6d8e91718893736380947887967f70706d74938870706b6985878c8b6c636f98988c647a969883638d9273648994768d93756363637f957a7b96816363636f99896f978f6e6363638e9374648792746363638596898f8666638398969176948f6f8e937480917f638c8d6a87957a63636377958d6c63636f927a789477636f9999937a87989982638d9272648b94768c92746363638096797a978b807f6b6f98886f9695868075638e9274648b9374636363859795977b6463849897988b978e6f8e92737090856b90896387978c7f7d656b8a968780747b97857f997f656f999592918f919881638d95837c938b6c8b907163636380967d7a95969797716f97896f9698989883638d94847c928b6b6363638597969783656385968e9298988d6d8f907065908e83917e6387989897936663748089968b8c989896988a6a6f988d839889829682638d9896978d76638c917163636380957c79959084866c6f9689709793898678638e999797927b636363638697908d9372638592808296988d6e8e8f6f65839798916c6387968d8582656364636f8d9696928b888f98716e958a6f947b789583638d968c897463638c958070706b8196777a97836363636e95896f968f777170688e968d90906f6363636386957d7691896885917a6d8c988d6e8d9071636f99988f656387957f70706d6870706f8592987e63637597757095896d84747a9283638b8e72636363638c979896968380967a79977d6363636f98886f9799999998788e8f727a94806563636384937263839378859575637d958e6e8f9272636d9595806463879898989889738d969490879376636374958d739888686363779582638d8d6f636363638997979793807d94797b98816363636f95866f9697959795768c9172648e8e716363638591776375947e83937663668a8a6f8d8f72636783976d6363879397949589636e8c947964",
        "13.778:63636b91846363637d967b6363668698726f9898978d706370988867636368948c6e91989898987d88927383989898988a7b989896886963636363789881646e8f8c7a987e63638a91728594889691666365918888989898988c636381958a6b63638096937563637d978b6363699398726f98989896916e70988867636368948c6e91989898987d88927383989898988a7b989897958c66636363789881667e936e7a98906f638a91728594798692666365918383989898988c637f9497958463638598977963637d989272637a9698726f988f747d978272988867636368948c6e91927a70706988927383958170706d7b97887086947763636378988171927b647a989684688a9172859475819578637a937b82968270706d72918a70706c636f8e86908668637d98967e63889798726f988a6870918f74988867636368948c6e918f6f63636388927383957a6363637b97806379948463636378988d8b8c6c637a989893798c917285947579948463858f6b82957b63636376948e6c63636379957380936d637d98988b76919898726f988b6872938c74988867636368948c6e91938580776388927383968a807d657b9781637b9482636363789896988668637a9898988d9391728594756b8f8a6b8b8d6382968b807e666b8a958680746681977f869872637d9791918e8f9198726f98917e84977d72988867636368948c6e9198989887638892738398989893677b978c7a8a9473636363789898988e6c637a98919098989172859475638a90829180638298989894686374808a968c6c8d9898989881647d97858898818898726f989897948a6c70988967636368948c6e91958a857a6388927383968d8582667b9898989888656363637898938b977d657a98857f94989172859475637e9697966f6382978d858367636564728d9872988f8a8a9291667d977d7793708698726f98948b826d6370988f7470706b948c6e91907163636388927383958170706d7b98918e967c646363637898897090946e7a98806c88969172859475636a949893696382968270706d677371708596789775636380926a7d977d70826c8698726f98896863636370989898989874948c6e918e6f63636388927383989898988a7b977e6e8d9069636363789881647b95817a988063749191728594756368929887676382989898988c708c9697948c94917163637f96827d977d6363678698726f98896863636370989898989874948c6e918e6f63636388927383989898988a7b977e637f9479636363789881646d8e8c7b988063638290728594756366839874636382989898988c63708c947f67",
    ]),
    "rocket_launcher": ("Rocket Launcher", 1, [
        "15.000:999997876c6564656e8b9179676464687a928c6e6c8e8d68657b95799599999998799499999999916c6480997064646464647396816664839472646d948384936e646d94826464697d93866d6e9487676481956e879999999985869999967f69999896988e6a6574939897988266688498979894768e8d686e91816d95999595947790969899968d6b64809970646464646680998c6a64839472646d9483849886666d9482646b8998979892759487676481956e879997959583869997969888998a808c9673698a9586848f947074958e848589738e8e6e868f6b6d95927e7c7b6d7980909580776764809970646464646a8b98947364839472646d9483849995726d9482647c968d838787739487676481956e8798857c7c7386968681919598776476957e709187656474967c7f95736464696a8e93899379646d958f787870646466848f686464648099706464646472928a917e65839472646d9483849999867295826686936f6465686d948e7a788a956e87977e78766786936f6480989884768496787c957b64646c928c8e916b6464646a8e9999926e646d9599999984646466848f68646464809970646464657d9070888a69839472646d9483849999948896826b918c696464646d9499999999956e87999999936c86957e778b9699969397916c7b957b64646c928c8e916b6464646a8e9999967b646d9598908e7d646466848f68646464809970646464688991768b9271829474646d948384968a939998826b908c696464646d9498918f96956e8799948e896a86999594988c999999978066709187656474967c7f95736464696a8e988c938e6a6d958e72706b646466848f686464648099706464646d91979196977c7b957c647094828494767c9998826686936f6465686d948d747188956e87977a706f6686999999957898817a957f64698a9586848f947074958e848589738e917081967c6d95927e7c7b696466848f6864646480998c85846a7a979999999886719391848b967c8494726a8f9882647b968c838787739487676481956e8798857c7c7386957b7f95759877688a8e6a6574939897988266688498979894758e8d686d90907595999595946e6466848f6864646480999998956e8493756f7086926e829897988d6d849472647c9682646b8898979891759487676481956e87999795958386936f6c91889877647c957964656e8b9179676464677a928b6e6c8e8d68657b988796999999986f6466848f6864646480999999967792866864647d9770687c94856b65849472646c8e826464697d94856d6e9487676481956e87999999998586936f658695",
        "13.667:9999999172676767677e9581676767676787947a6770997f68739788729999999983679199999999846767779979676767677192986d67678e8d696772997d8d8e6a6771997e676778948968678a90696770978189999999946a7e999998856b999999989278676c889599968a6f67738c9799957f72997f6a8794776f9999999983679199999999846767779979676767677598986d67678e8d696772997d8d987f6771997e6985949997896e8a90696770978189999999946a7e999999968e998d7779997e6771978374809774677a987b7382777099807493846a6f998b76736e6771778d97776e6767779979676767687b99998267678e8d696772997d8d99947471997e6a9289737784698a90696770978189947a7372677e998173889899866a6e998069839375677292866e8a916e676d6b70998e8d8f6f676f99866a676767676985966c6767677799796767676b8d8a8f8d67678e8d696772997d8d99998c80997e7a947b67686f678a9371677698818993706767677e997467839999876a6e997f6a908b6d676c89937596856a676767709998998c67676f999184837667676884966c6767677799796767676c968184916c678e8d696772997d8d99999891997e889170676767678a9789838598818997878380687e997567839999918182987d69908b6d676c89937596856a676767709999999171676f999999998367676884966c67676777997967676776988b8a9579678c8e6c6775987c8d97929999997e889170676767678a9999998f998189999999946a7e99877d8d9899999999927468829375677292866e8a916e676d6b7099958c9781686f999389887967676884966c67676777997c68676787999999998567849275678294778d917e9299997e7a937b67686f678a96898884988189978b8884697e999999998a99948d968a6a6771978273809774677a987b73827770998970918d6f6f998b76736e67676884966c67676777998875737091958d8d95896a76978774938c6d8d8e697e97997e6a9289737784698a90696770978189947a7372677e998f91997a998568899375676c88959996896f67738c9799957f72997f6980997c70999999998367676884966c67676777999999998e958567678394776b8f97999581678d8e69678c997e6884949997896e8a90696770978189999999946a7e997175948b9985686e997e6767677e9581676767676787947a6770997f6873979575999999998367676884966c6767677799999999989572676770997c676d89967d67678d8e696772997e676778948968678a90696770978189999999946a7e9971678399",
    ]),
    "toilet_rolls": ("Toilet Rolls x1,000", 1000, [
        "10.688:96969696969696967a666c7c8c948b7b6b666a8e968d697a969678666666668296969696969689709496969696969696736666678b969696958b7a6b666666697785938f7f72666682969672666666668996926f6666666666717f8f948b7c7096969696969696967a6e899596969695886d6a8e968d697a969678666666668296969696969689709496969696969696736666678b969696969695856a666981949696969690756682969672666666668996926f66666666719096969696957b7e7e8395968d7e7e73859594847e859495836c8e968d697a96967866666666829696847e7e7e786b7d7e869696897e7e6d6666678b9693817e8b969375667b94958b7e8191968f6d82969672666666668996926f66666668819692817e7f866d66667195968466667191968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b96906d6674959582698a968e7066687b93967883969672666666668996926f66666668879691766e676b677b697195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b9691726c7d95947d709496826666666b8e968884969672666666668996926f66666667769296958f867c6a866b7195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b969591909396906f709496826666666b8e968884969672666666668996926f666666666878858d95969483866b7195968466667091968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b9696969696927868698a968e7066687b93967883969672666666668996926f66666666696d686c738e9695866b7195968466666a859594847e859495836c8e968d697a9696877e7e7e6e829696847e7e7e786666667596967d6666666666678b9693828a96927466667b94958b7e8191968f6d829696847e7e7d6b899694827e7e7c6a738d807e7f919693866b719596846666666e899596969695886c6a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d729296866966698194969696969075668296969696969470899696969696906e7f9696969696937c866b71959684666666666c7b8c948b7b6b666a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d667c9594796666697784938f7f7266668296969696969470899696969696906d707b889392847568",
        "11.273:959897989898989880686c768c968c776c686785988c706b9298886b67676774979898989797846784979897989695988c676767779598989893816b6867676a6e8194907f6d6a677295987c676767677b95916f67676767686c7a91968a746993929598989693947f6e8d95959696968f716781978e716b9397836a6767677597959692949486678893939698979494886767677a9695969594968971676a809498969698947e6a7497967e676767677f979275676767676d8f9695969896747c7e899697897e7d738396938a81889297886885988d706b9398856a6767677598978b7d7e7b7767787e8393988e7d7d766767677a9897887d8796977d687595968c83838b9794737498977d676767677f969273676767677d9495868288826e67677594987d67676e8d95846a67698196907185978e706b9398856a676767759797857a7977686767676f8c98876767676767677a97957867699298846c8098936f67676f96977d7597987c676767677f979173676767678596927d6f67676767677494987d67677c9694796767677992957e84988e706b9398846a6767677598989798969169676767708c98866767676767677a979583767c93967f6e92978b6b67676c8d968f7797987c676767677f9891746767676775909793887d7a6c67677494987d67677d94957b6767677692977f83988d706b9397836a676767749696958e8f8969676767708c98866767676767677a97969590959790766d9498896a67676c8b978e7798987b676767677e9792736767676768777d859398947b67677594987c67676e8c97836967697f96916f84988d706b9497876b6767677597968573747168676767708c988767676767676779969896969796826b6a8197927167677292987c74979779676767677e979273676767676767676c788c979067677594987d6767678597928984869296896785958e706b949891888589827697978b7e7e7f78676767718d98866767676767677997957d7f90968267677594968b83868b9793727498978e8686887e7e97978c868487756a8689837f92988b67677594987d6767676f8b989795979590716786978d706b949897979697917898989694949485676767708d97876767676767677a9594796a8a979477676a7e9498969697927c6973969798959796887f9797969696977e819696959497947767677493987d676767686b7689958c766c686786988d6f6b949798989796927897989898979789676767708d97876767676767677a989577676d92977f69676a6e819492816d696773979698989898887e9798989898967f6b728996937f6d69",
    ]),
    "toilet_rolls_500": ("Toilet Rolls x500", 500, [
        "10.688:96969696969696967a666c7c8c948b7b6b666a8e968d697a969678666666668296969696969689709496969696969696736666678b969696958b7a6b666666697785938f7f72666682969672666666668996926f6666666666717f8f948b7c7096969696969696967a6e899596969695886d6a8e968d697a969678666666668296969696969689709496969696969696736666678b969696969695856a666981949696969690756682969672666666668996926f66666666719096969696957b7e7e8395968d7e7e73859594847e859495836c8e968d697a96967866666666829696847e7e7e786b7d7e869696897e7e6d6666678b9693817e8b969375667b94958b7e8191968f6d82969672666666668996926f66666668819692817e7f866d66667195968466667191968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b96906d6674959582698a968e7066687b93967883969672666666668996926f66666668879691766e676b677b697195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b9691726c7d95947d709496826666666b8e968884969672666666668996926f66666667769296958f867c6a866b7195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b969591909396906f709496826666666b8e968884969672666666668996926f666666666878858d95969483866b7195968466667091968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b9696969696927868698a968e7066687b93967883969672666666668996926f66666666696d686c738e9695866b7195968466666a859594847e859495836c8e968d697a9696877e7e7e6e829696847e7e7e786666667596967d6666666666678b9693828a96927466667b94958b7e8191968f6d829696847e7e7d6b899694827e7e7c6a738d807e7f919693866b719596846666666e899596969695886c6a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d729296866966698194969696969075668296969696969470899696969696906e7f9696969696937c866b71959684666666666c7b8c948b7b6b666a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d667c9594796666697784938f7f7266668296969696969470899696969696906d707b889392847568",
        "11.273:959897989898989880686c768c968c776c686785988c706b9298886b67676774979898989797846784979897989695988c676767779598989893816b6867676a6e8194907f6d6a677295987c676767677b95916f67676767686c7a91968a746993929598989693947f6e8d95959696968f716781978e716b9397836a6767677597959692949486678893939698979494886767677a9695969594968971676a809498969698947e6a7497967e676767677f979275676767676d8f9695969896747c7e899697897e7d738396938a81889297886885988d706b9398856a6767677598978b7d7e7b7767787e8393988e7d7d766767677a9897887d8796977d687595968c83838b9794737498977d676767677f969273676767677d9495868288826e67677594987d67676e8d95846a67698196907185978e706b9398856a676767759797857a7977686767676f8c98876767676767677a97957867699298846c8098936f67676f96977d7597987c676767677f979173676767678596927d6f67676767677494987d67677c9694796767677992957e84988e706b9398846a6767677598989798969169676767708c98866767676767677a979583767c93967f6e92978b6b67676c8d968f7797987c676767677f9891746767676775909793887d7a6c67677494987d67677d94957b6767677692977f83988d706b9397836a676767749696958e8f8969676767708c98866767676767677a97969590959790766d9498896a67676c8b978e7798987b676767677e9792736767676768777d859398947b67677594987c67676e8c97836967697f96916f84988d706b9497876b6767677597968573747168676767708c988767676767676779969896969796826b6a8197927167677292987c74979779676767677e979273676767676767676c788c979067677594987d6767678597928984869296896785958e706b949891888589827697978b7e7e7f78676767718d98866767676767677997957d7f90968267677594968b83868b9793727498978e8686887e7e97978c868487756a8689837f92988b67677594987d6767676f8b989795979590716786978d706b949897979697917898989694949485676767708d97876767676767677a9594796a8a979477676a7e9498969697927c6973969798959796887f9797969696977e819696959497947767677493987d676767686b7689958c766c686786988d6f6b949798989796927897989898979789676767708d97876767676767677a989577676d92977f69676a6e819492816d696773979698989898887e9798989898967f6b728996937f6d69",
    ]),
    "toilet_rolls_200": ("Toilet Rolls x200", 200, [
        "10.688:96969696969696967a666c7c8c948b7b6b666a8e968d697a969678666666668296969696969689709496969696969696736666678b969696958b7a6b666666697785938f7f72666682969672666666668996926f6666666666717f8f948b7c7096969696969696967a6e899596969695886d6a8e968d697a969678666666668296969696969689709496969696969696736666678b969696969695856a666981949696969690756682969672666666668996926f66666666719096969696957b7e7e8395968d7e7e73859594847e859495836c8e968d697a96967866666666829696847e7e7e786b7d7e869696897e7e6d6666678b9693817e8b969375667b94958b7e8191968f6d82969672666666668996926f66666668819692817e7f866d66667195968466667191968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b96906d6674959582698a968e7066687b93967883969672666666668996926f66666668879691766e676b677b697195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b9691726c7d95947d709496826666666b8e968884969672666666668996926f66666667769296958f867c6a866b7195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b969591909396906f709496826666666b8e968884969672666666668996926f666666666878858d95969483866b7195968466667091968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b9696969696927868698a968e7066687b93967883969672666666668996926f66666666696d686c738e9695866b7195968466666a859594847e859495836c8e968d697a9696877e7e7e6e829696847e7e7e786666667596967d6666666666678b9693828a96927466667b94958b7e8191968f6d829696847e7e7d6b899694827e7e7c6a738d807e7f919693866b719596846666666e899596969695886c6a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d729296866966698194969696969075668296969696969470899696969696906e7f9696969696937c866b71959684666666666c7b8c948b7b6b666a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d667c9594796666697784938f7f7266668296969696969470899696969696906d707b889392847568",
        "11.273:959897989898989880686c768c968c776c686785988c706b9298886b67676774979898989797846784979897989695988c676767779598989893816b6867676a6e8194907f6d6a677295987c676767677b95916f67676767686c7a91968a746993929598989693947f6e8d95959696968f716781978e716b9397836a6767677597959692949486678893939698979494886767677a9695969594968971676a809498969698947e6a7497967e676767677f979275676767676d8f9695969896747c7e899697897e7d738396938a81889297886885988d706b9398856a6767677598978b7d7e7b7767787e8393988e7d7d766767677a9897887d8796977d687595968c83838b9794737498977d676767677f969273676767677d9495868288826e67677594987d67676e8d95846a67698196907185978e706b9398856a676767759797857a7977686767676f8c98876767676767677a97957867699298846c8098936f67676f96977d7597987c676767677f979173676767678596927d6f67676767677494987d67677c9694796767677992957e84988e706b9398846a6767677598989798969169676767708c98866767676767677a979583767c93967f6e92978b6b67676c8d968f7797987c676767677f9891746767676775909793887d7a6c67677494987d67677d94957b6767677692977f83988d706b9397836a676767749696958e8f8969676767708c98866767676767677a97969590959790766d9498896a67676c8b978e7798987b676767677e9792736767676768777d859398947b67677594987c67676e8c97836967697f96916f84988d706b9497876b6767677597968573747168676767708c988767676767676779969896969796826b6a8197927167677292987c74979779676767677e979273676767676767676c788c979067677594987d6767678597928984869296896785958e706b949891888589827697978b7e7e7f78676767718d98866767676767677997957d7f90968267677594968b83868b9793727498978e8686887e7e97978c868487756a8689837f92988b67677594987d6767676f8b989795979590716786978d706b949897979697917898989694949485676767708d97876767676767677a9594796a8a979477676a7e9498969697927c6973969798959796887f9797969696977e819696959497947767677493987d676767686b7689958c766c686786988d6f6b949798989796927897989898979789676767708d97876767676767677a989577676d92977f69676a6e819492816d696773979698989898887e9798989898967f6b728996937f6d69",
    ]),
    "toilet_rolls_100": ("Toilet Rolls x100", 100, [
        "10.688:96969696969696967a666c7c8c948b7b6b666a8e968d697a969678666666668296969696969689709496969696969696736666678b969696958b7a6b666666697785938f7f72666682969672666666668996926f6666666666717f8f948b7c7096969696969696967a6e899596969695886d6a8e968d697a969678666666668296969696969689709496969696969696736666678b969696969695856a666981949696969690756682969672666666668996926f66666666719096969696957b7e7e8395968d7e7e73859594847e859495836c8e968d697a96967866666666829696847e7e7e786b7d7e869696897e7e6d6666678b9693817e8b969375667b94958b7e8191968f6d82969672666666668996926f66666668819692817e7f866d66667195968466667191968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b96906d6674959582698a968e7066687b93967883969672666666668996926f66666668879691766e676b677b697195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b9691726c7d95947d709496826666666b8e968884969672666666668996926f66666667769296958f867c6a866b7195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b969591909396906f709496826666666b8e968884969672666666668996926f666666666878858d95969483866b7195968466667091968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b9696969696927868698a968e7066687b93967883969672666666668996926f66666666696d686c738e9695866b7195968466666a859594847e859495836c8e968d697a9696877e7e7e6e829696847e7e7e786666667596967d6666666666678b9693828a96927466667b94958b7e8191968f6d829696847e7e7d6b899694827e7e7c6a738d807e7f919693866b719596846666666e899596969695886c6a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d729296866966698194969696969075668296969696969470899696969696906e7f9696969696937c866b71959684666666666c7b8c948b7b6b666a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d667c9594796666697784938f7f7266668296969696969470899696969696906d707b889392847568",
        "11.273:959897989898989880686c768c968c776c686785988c706b9298886b67676774979898989797846784979897989695988c676767779598989893816b6867676a6e8194907f6d6a677295987c676767677b95916f67676767686c7a91968a746993929598989693947f6e8d95959696968f716781978e716b9397836a6767677597959692949486678893939698979494886767677a9695969594968971676a809498969698947e6a7497967e676767677f979275676767676d8f9695969896747c7e899697897e7d738396938a81889297886885988d706b9398856a6767677598978b7d7e7b7767787e8393988e7d7d766767677a9897887d8796977d687595968c83838b9794737498977d676767677f969273676767677d9495868288826e67677594987d67676e8d95846a67698196907185978e706b9398856a676767759797857a7977686767676f8c98876767676767677a97957867699298846c8098936f67676f96977d7597987c676767677f979173676767678596927d6f67676767677494987d67677c9694796767677992957e84988e706b9398846a6767677598989798969169676767708c98866767676767677a979583767c93967f6e92978b6b67676c8d968f7797987c676767677f9891746767676775909793887d7a6c67677494987d67677d94957b6767677692977f83988d706b9397836a676767749696958e8f8969676767708c98866767676767677a97969590959790766d9498896a67676c8b978e7798987b676767677e9792736767676768777d859398947b67677594987c67676e8c97836967697f96916f84988d706b9497876b6767677597968573747168676767708c988767676767676779969896969796826b6a8197927167677292987c74979779676767677e979273676767676767676c788c979067677594987d6767678597928984869296896785958e706b949891888589827697978b7e7e7f78676767718d98866767676767677997957d7f90968267677594968b83868b9793727498978e8686887e7e97978c868487756a8689837f92988b67677594987d6767676f8b989795979590716786978d706b949897979697917898989694949485676767708d97876767676767677a9594796a8a979477676a7e9498969697927c6973969798959796887f9797969696977e819696959497947767677493987d676767686b7689958c766c686786988d6f6b949798989796927897989898979789676767708d97876767676767677a989577676d92977f69676a6e819492816d696773979698989898887e9798989898967f6b728996937f6d69",
    ]),
    "toilet_rolls_50": ("Toilet Rolls x50", 50, [
        "10.688:96969696969696967a666c7c8c948b7b6b666a8e968d697a969678666666668296969696969689709496969696969696736666678b969696958b7a6b666666697785938f7f72666682969672666666668996926f6666666666717f8f948b7c7096969696969696967a6e899596969695886d6a8e968d697a969678666666668296969696969689709496969696969696736666678b969696969695856a666981949696969690756682969672666666668996926f66666666719096969696957b7e7e8395968d7e7e73859594847e859495836c8e968d697a96967866666666829696847e7e7e786b7d7e869696897e7e6d6666678b9693817e8b969375667b94958b7e8191968f6d82969672666666668996926f66666668819692817e7f866d66667195968466667191968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b96906d6674959582698a968e7066687b93967883969672666666668996926f66666668879691766e676b677b697195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b9691726c7d95947d709496826666666b8e968884969672666666668996926f66666667769296958f867c6a866b7195968466667f959672666666739695808e968d697a9696786666666682969696969695716666667596967d6666666666678b969591909396906f709496826666666b8e968884969672666666668996926f666666666878858d95969483866b7195968466667091968469666a859690728e968d697a969678666666668296967c737372696666667596967d6666666666678b9696969696927868698a968e7066687b93967883969672666666668996926f66666666696d686c738e9695866b7195968466666a859594847e859495836c8e968d697a9696877e7e7e6e829696847e7e7e786666667596967d6666666666678b9693828a96927466667b94958b7e8191968f6d829696847e7e7d6b899694827e7e7c6a738d807e7f919693866b719596846666666e899596969695886c6a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d729296866966698194969696969075668296969696969470899696969696906e7f9696969696937c866b71959684666666666c7b8c948b7b6b666a8e968d697a9696969696967582969696969696896666667596967d6666666666678b96906d667c9594796666697784938f7f7266668296969696969470899696969696906d707b889392847568",
        "11.273:959897989898989880686c768c968c776c686785988c706b9298886b67676774979898989797846784979897989695988c676767779598989893816b6867676a6e8194907f6d6a677295987c676767677b95916f67676767686c7a91968a746993929598989693947f6e8d95959696968f716781978e716b9397836a6767677597959692949486678893939698979494886767677a9695969594968971676a809498969698947e6a7497967e676767677f979275676767676d8f9695969896747c7e899697897e7d738396938a81889297886885988d706b9398856a6767677598978b7d7e7b7767787e8393988e7d7d766767677a9897887d8796977d687595968c83838b9794737498977d676767677f969273676767677d9495868288826e67677594987d67676e8d95846a67698196907185978e706b9398856a676767759797857a7977686767676f8c98876767676767677a97957867699298846c8098936f67676f96977d7597987c676767677f979173676767678596927d6f67676767677494987d67677c9694796767677992957e84988e706b9398846a6767677598989798969169676767708c98866767676767677a979583767c93967f6e92978b6b67676c8d968f7797987c676767677f9891746767676775909793887d7a6c67677494987d67677d94957b6767677692977f83988d706b9397836a676767749696958e8f8969676767708c98866767676767677a97969590959790766d9498896a67676c8b978e7798987b676767677e9792736767676768777d859398947b67677594987c67676e8c97836967697f96916f84988d706b9497876b6767677597968573747168676767708c988767676767676779969896969796826b6a8197927167677292987c74979779676767677e979273676767676767676c788c979067677594987d6767678597928984869296896785958e706b949891888589827697978b7e7e7f78676767718d98866767676767677997957d7f90968267677594968b83868b9793727498978e8686887e7e97978c868487756a8689837f92988b67677594987d6767676f8b989795979590716786978d706b949897979697917898989694949485676767708d97876767676767677a9594796a8a979477676a7e9498969697927c6973969798959796887f9797969696977e819696959497947767677493987d676767686b7689958c766c686786988d6f6b949798989796927897989898979789676767708d97876767676767677a989577676d92977f69676a6e819492816d696773979698989898887e9798989898967f6b728996937f6d69",
    ]),
    "stun_gun": ("Stun Gun", 1, [
        "8.062:676c78828e9392887c73678c96969295959595959695959596916c6767677e95959372677a93949179676767678094948c6c676767676767676768727a848f928e847b73678994948f69676767829496936e677f94959074676767678495948f70899393949695949582678c95949594959495959594959596926c6767677b94959573677b91949590786967678294948f6d676767676767676d839094959494949595907c8c94948f69676767819595966e677f9495938d756867678795948f84949390817d7d7e897167797e7e829495968a7d7e7d8b9496926c6767677d95959472677c94939594907868678195948f6d6767676767676f87909391847e7e7d879087728994958f69676767819594956e6780949494958f7567678794948f8f95948e79706a676c67676767676e95959481676767859596936c6767677d95959372677b9495969595917a678095958f6d6767676767687d92929078696767676a6f6a678b95948f696767677f9495956e677e94949596958f74678794948f78909494949189847d6c676767676e96959682676767859595936d6767677d95969673677c94969694959592828d95948f6d67676767676d8c9393836a676767676a6c6c6c8a95958f69676767819593956e678193959595959590838e959590687080858d93959694896f6767676e96969682676767859696926c6767677d94959372677b93969487869295949594958f6d67676767676e8d9392836a676767697f9090899094968c69676767829395936e677e949594868893949594949590696e6a686d727e9595957b6767676e95959682676767789394937b67676c8796948a6d677c949595746a7a91949595948f6d6767676767687e949491786a6767698396958f859295907467676d889593886b6780949494706a809293949494907490857e7d7e85949694796767676e95959682676767698b95948f7c7d849395947c67677b9395967367677a919495948f6d6767676767676f87939591837d7e808e95968d749195958d7e7e879693937967677f9496927067697d9295949490849494939595959693806a6767676e9696968267676767728e95959495959493816a67677a93969573676768799094958f6d676767676767676c83909594949595959592856d768e959596959596917e6a67677f949593706767697a91949490707a7e8c93948d807767676767676e9594958167676767676e798491938e7e77686767677b9394957567676768768f958f6d676767676767676768737a858f938e817a756a6767707a8893948b7e76676767677e94959270676767687a919490",
        "7.538:676d74808f9391887a7167729494949494949494949494949494947a6767678494949473678a94948a6d67676791949493676767676767676767676a73798992928b7e746e677c9494947b6767678494949474678994948a6e676767909494946887949494949494938567729494949494949494949494949494947a6767678494949473678a949494836a6767919494936767676767676767676c829494949494949494866f7c9494947b67676784949494746789949494836b6767909494948094949276767678806f676b7676768094949488767676859494947a6767678494949473678a94949494866b679194949367676767676767676e8994948d7c76767c8b8b796d7c9494947b6767678494949474678994949494866b67909494948e949491706f6f6b6a67676767676776949494826767677d9494947a6767678494949473678a9494949494866c91949493676767676767676a7c94948c72686767686b6b68677c9494947b676767849494947467899494949494876c9094949475929494949492857972676767676776949494826767677d9494947a6767678494949473678a9494949494948393949493676767676767676f90949488676767676b7373736e7c9494947b67676784949494746789949494949494839394949467777b8b94949494938a706767676776949494826767677d9494947a6767678494949473678a9494948592949494949493676767676767676f9094948867676767758e8e8e7d7c9494947b676767849494947467899494948592949494949494676d696d70707994949384676767677694949482676767758c94947d6967698594949172678a949494707c919494949493676767676767676a7c94948c736867677894949480758c94947e69676985949491736789949494717b9094949494946b917e7676767b9494907a676767677694949482676767687e94948e7e767e8e94947d6a678a9494946e687d929494949367676767676767676e8994948d7c76768194949480687d94948e7e767e8e94947d6a67899494946f687d92949494948194949494949494927f6767676767769494948267676767718793949494949494846d67678a9494946e67677a929494936767676767676767676c8294949494949494948f7967718793949494949494846e6767899494946f67677a9294949473747e8c92938c7d726b6767676767769494948267676767676d73808f938e7e756b6767678a9494946e6767677d939493676767676767676767676a74798992928b7d74716b67676d737f8e938e7e756b676767899494946f6767677d939494",
    ]),
    "spikes": ("Spikes", 1, [
        "5.562:63636a747a838c90918d877e7675646363839192919292919293918b80787167636363748f9291928c6463637d8e9392907f6663636363677a8c90908f816d74909091919191929292929292918163636363636d757a828a90908b8278757463658089909291929392919292928d6563638693939392919293939392939390887466637793929193916463638190939292826663636674879193908977676374929193929293939293939392918263636368828d9192919192919090929189637c8f919291897f7b7b7a797e8a6f64636386939393938a7b7a7b7b7f919391908d756377949494949264636382909393938267656d809292928c7c6b6463637593939493927d7b7b7b7b7b7b7b736363667e8f909292887e7a7a7a7a7f866e63879293939285766e6a656364696363636386949493938263636363659092929293786377939294929264636382919494948a7c818d939290826e6563636363759292949394726f6f6f6f6f6f6a63636368899393939380726d696563656863636a858e92939192928b8382807769636363869393939384686868696e909290919077637794939493926463638191939393939293949294896a636363636363759394949393949494939393937e636363646c8c8f92919192908a8481807767636367737e7f838a9093929293918e7565638694939392908d8c8d8d8b9091918f836e63779494939492646363819193939393939293949490826e6563636363759493939393939393949393937f636363636368707f81868c9092929191908874636a6a666365696d6f7a93939391926963869393939392939393918f8c8a81736763637793939294906463638191949494928c878890939293897868636363749293929493726f6f6f6f6f6f6a63636363636a6b6563666a6d6f7d9191919191648a8d827c7b7a7a7b839393919090696386939393928a7b7b7b7a776b66646363636377939292938d6463638191949393887065677490919392907f6c64637593939293937c7b7b7b7b7b7b7b7b756363668a8f817c7b7b7a7a839192928f8f79909292939393939393929091866d6463859191929282636363636363636363636363779392929390646363849294939382646363646c849290929289776775939393949393949391919293939386636679939392929393939292929390846b6874777b848c9192918b7e7773636363638191929192826363636363636363636363637591939392916463638091949492806763636363657a909393928f7f7c94939094939293939292939392938663646b77777d878c9091918a7d77736363",
        "5.231:63666b7079838d91928f897e767066636c8e9393939393939392908a7d756f6663636382939393938a6863729393939393786363636771899193938a7963637a939393939393939393939393938063636364686e757d898f92918c8479736b6363768893939393939393939390896c636c8e939393939393939393939393907e6e636382939393938a68637293939393937863636c7b8d92938f826e6363637a93939393939393939393939393806363636b828e9393939393939393938d7a637d8a9393938673737373737d7b6d66636c8e9393939385737373767f8d939393826f6482939393938a686372939393939378666e838f9392887968646363637a93939393927c737373737373736d63637182929393917a7373737378817369638c90939393846c6c6c6b6867656363636c8e939393937e63636364668593939390836682939393938a6863729393939393837d8e92939081716563636363637a9393939392776c6c6c6c6c6c66636363788e93939390756c6c6c6a676664636371829193939393939390877c757167636c8e939393937e636363656b869393938d7f6582939393938a686372939393939393939393928d6c636363636363637a939393939393939393939393726363636a788e929393939393938b8176746c63636c7476838c939393939393918d76696c8e939393938a80808082878f9393937f6a6482939393938a686372939393939393939393939182706363636363637a93939393939393939393939372636363636772757d899093939393939390816f63676865686a6c6c6f79919393928d786c8e939393939393939392918f8d897267636382939393938a68637293939393938d898990939393887865636363637a9393939392776c6c6c6c6c6c666363636365696766696b6c6d7185939393908b667e8b7d76737373737b9193939282716c8e939393938c838382807b6f68646363636382939393938a686372939393939379646479899393938c776a6363637a93939393927c737373737373736d636364708e8479737373737386939393897d7e8a939393939393939393938d826a636c8e939393937e63636363636363636363636382939393938a686372939393939378636363728991939393827163637a93939393939393939393939393806363718392939393939393939393938875636f70737b858c91928f897d756e6864636c8e939393937e63636363636363636363636382939393938a686372939393939378636363666f89919393928773677a939393939393939393939393938063636a707177808a8f92918d8379706b6663",
    ]),
    "plunger": ("Plunger", 1, [
        "7.600:9393939392929292938c776564648392929078646464646464668c9292886d6464647a929292826464859293907c676464718e92928c64646464758a9392929292929384736669819292939292929292928264648792939392929292938e7c68939293938f8d8d909292917b64648391928f76646464646464648c9192866c6464647a929292806464859193928f796664708c92928c6464667c909392918e8d8e9192918467687f9292928f8d8d8d8d8d7f646487929393908d8d90929292869393939374696c7d9093928968648392928f77646464646464648c9292876c6464647b9292928064648592939393907865708d93928c6464788f92938d7d6e696c7c857b6a65687f929290716969696969686464889393937c696a788e939292939393937064646b8692928c71648392928f77646464646464648c9292876c6464647b929292806464859293939392927e728c93928c6468829292907b646464646466666464687f9292917c747474747164646488939393796464688092929393939393796f717e8f93928969648392928f77646464646464648c9292876c6464647b92929280646485929393939393918b9093928c646e8992928a6a646464646a74747366687f929393919090909087646464889393937e6c6d798d93929393939393908e909393928e7964648392928f77646464646464648c9292896d6464647b9292927f64648592938d7f8a9293939393928c646c8792928c6f646464657792928f6968809293938f8d8d8d8d8564646488939393908b8d929393918693939393939292928e86766664648392928f77646464646464648c92939073646469819292907564648592928a6f738c92939393928c646580929392846a6464657792928f69688092928f6e696969696964646488939393939292939391806b939393937c7474736e666464646483929392867c7c7c7c7c6f64829292938a7f7c889293928a6764648592928a6f64718d929393928c6464708a92939289807b808b93938f6968809292917d77777777767165648893939382748a929291776593929293706464646464646464648392939392919191919178646a8792939391919393928c736464648591928a6f64656e889293928c64646574889293929191929393928a68687f9292939190909090908266648792929278646c8c92928f75939393937064646464646464646483929393939292929292786464697b8b92929293907e6f656464648592928b706464646d8893928c646464646b7a8c939292929287796d65688093939393929292929284666487939393786465759292938f",
        "7.818:93949494949494949494756866667c94948c66666666666666769494948b6c666666799494906866668594948d796766666d8a9494806666666a7f91949494949494938a6c66667f9494949494949494947c66749494949494949494948b70668d9293938f8b8b8e9393947769667c92908b6666666666666675929393866b6666667892908f666666849292938c7366666a8991928066666a8b9393938e8b8b8c8f918b7268667f9292918b8b8b8b8b8b7866728f9393938c8b8c9093938e6e8e939491796668749193939273667c93918c6666666666666675939494876b6666667993919066666685939394938f73666a89939380666978949294897266666a7884686666667f939289666666666666666672909494906f66697d919393918e9394907866666d8a94939474667c93918c6666666666666675939494876b666666799391906666668593939494939376718b939380666f9193939072666666666666666666667f93938e77777777776c6666728f94948f6e6666768d9494948e9394928173757f9193948e72667c93918c6666666666666675939494876b6666667993919066666685939394949494918b929393806670949394866e66666669727a796c67667f9493949494949494786666728f949491787075849193938d8e939494908c8e949493937a6a667c93918c66666666666666759394948a6c666666799391906666668593938b7f8c9494949493948066709493948a706666666d8293937468667f939392887f807f80706666728f9494948c898e9394938e748e939494949494948f81776966667c93918c66666666666666738e9493916d66666d8293929066666685939383687693939494939480666d89949392796966666d8494947568667f93928b6e69696869676666728f94949494949494938b74668e93949281737373716a666666667c939291807a7a7a7b776d6978949294897a7a869093938d666666859292836668749293949394806667729492938d857b77808e93937568667f93938f7c75767675766e6672909494927a7a8a93938866668d939490786666666666666666667c93929393919191918b78666f8c94949391919293948d6d666666859292836666666f8e9392938066666770919493939190919494947668667f939293918f90908f8f7a66729094948f6f687e9092908566929494937a6666666666666666667c94949494949494948f7a66676c7b929494949490816a6666666685949483666666666f8b949480666666666b81909494949493896e6866667f9494949494949494947c6674949494936f66687e94949388",
        "7.000:929292929292928d80756c6464729292928e64646464646464839292927d646464709292929065648d929289706564647a929292866464646464647071808c918f8779716c6474929292929292929292927064829292929292928f867670646492929292929292929292877164729292928e64646464646464839292927d646464709292929065648d929292846e64647a929292866464646464798f9292929292929292846d74929292929292929292927064829292929292929292928f7864929292927b74747b8a9292866e729292928e64646464646464839292927d646464709292929065648d929292928871657a929292866464646683929292807674747e8b87776b749292928f747474747474686482929292857474778492929073929292926f6464667f9292907e729292928e64646464646464839292927d646464709292929065648d929292929289747b929292866464667592929278696564646769696664749292928e6d6d6d6d6d666464829292927e646465719292928c929292926f6464698192928e7b729292928e64646464646464839292927d646464709292929065648d9292929292928888929292866464698d9292926b646464646c7171716c749292929292929292926d6464829292927e646467759292928892929292848080848e9292846a729292928e64646464646464839292927d646464709292929065648d929292868c929292929292866464698d9292926b646464647c8c8c8c7d749292929292929292926d6464829292928a8080828a9292906e92929292929292918f8d7e6a64729292928e64646464646464788c92927f676465729292928b65648d9292927575889292929292866464667592929279696564647f92929281749292928e6d6d6d6d6d666464829292929292929292928c6d64929292928783837e7268656464729292929074747474747469658192928d7f74788592928f7064648d9292927365738992929292866464646683929292817674748692929281749292928f7474747474746864829292928c8388919291856464929292926f6464646464646464729292929292929292929271647186929292929292928e786464648d9292927364647085929292866464646464799092929292929292928d7a74929292929292929292927064829292927e646b7f9292907b64929292926f646464646464646472929292929292929292927164646b717b8b918f84746f646464648d9292927364646470869292866464646464647071808c918f8679716f6974929292929292929292927064829292927e646468799292917b",
    ]),
    "yellow_energy": ("Yellow Energy (Contained)", 1, [
        "5.125:8e9b85727d988e7199a69b8f8f8d7196a1896d6d6d6d919d886d6d6d6d7d8c8f8c9183819589727285a28d767283916d6d6d6d6d7d9d9e8a8a897b7ea09e7f718da29276a3a1928c8c8375a2a2938e908b796e6d7d8d918f9171869b8d74789c6d869697938d6d6d99a69b8e8c8e7196a48b6d6d6d6d94a48d6d6d6d909f8c74707ea49f9d9c8d81a299a3878a98886d6d6d6d6d7fa2a5918c8c7e80a6a6998394a49476a4a7958e8e8575a5a5867a8da2936f8c9f8d7473837a7084979b968f6d6f8ea08f6f6d6d97a58e7272726e95a28c7171726e95a590747372869c927c7686a48e7d90a39f9872959fa2916f6d6d6d6d6d80a3a37873727080a6a3788a9ea69476a6a68474737275a6a49398a298726e819b937b7ca2a2786e8aa4986f6d6d8492856d6d6d8a94908a898a718a948f898a87718a95908a8c8c727580898c8a796f6d80928e756e7a8b94866d6d6d6d6d6d7991958d8b8b7d7b979572708694897497968f8c8c847394957a74848e756e6e75818a8a85796f6d8192876d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d707e7e726d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6f787d736d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6f7a9f7e7074808a8b8f746e6d727d8a8c877c726d7794947a7082958c708a8c9294918a896f768b91826d6d6d8d96837b9692766f86978b7497958f8c8c837395948e8c8d8778779a84716d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d7893a1748199957d7480766f7d959b80707d99937c7ca6a59a7f8da4976e727093a693717070999495977e6d6d97a58c80a6a6977e92a69676a7a69289898275a6a48070798ea18b9fa0856d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d7da0a274889e92766f75756f849c9a776f74989e867ca7a6848d9da5996d6d6d91a6926d7198a38b8fa198726e98a68c7ea2a183909fa59476a7a48578787575a6a67f6f7484a5929fa5886d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d6d7891a4746d7b8c928c8d7b716d7788918c9089786d7ba3a277758b9e966d6d6d8ea290738aa38c84848d9b927195a38b7fa4a274778f9f9176a4a5958f8e8474a1a29491928e836e9a9a806d6d6d6d6d6d6d6d6d6d",
        "5.188:8b9e86727f97896e9ca4988e8e88709fa4826e6e6e72a2a47f6e6e6e7184928f928d848aa27b707c9599816f769d806f6e6e6e6f9ea4978e8e8772a1a1887483a49d6e9da4988e8e88709fa49791928c7a6e6e7d8d92909072889d88737d988c6e86979994886e6e9ca4978d8c87709fa4826e6e6e72a2a47f6e6e7793a47e71748ca19b9d9c7f939e9d987a9a967a6e6e6e6e6f9ea4968d8c8572a1a49b898da49d6e9da4978d8c86709fa4887a8ba08f6f8a9e8b7374817a6f85969994896e6e6f92a4906f6e6e9ca489747271709fa48674737272a2a48474737889a286767a909a857ca1a09d85829f9ea3796f6e6e6e6e6f9ea48773727172a1a484859aa49d6e9da488747271709fa49495a198726e8199907a7fa19f736f8fa4926f6e6e6e8896866e6e6e9096908c8c876f9296918e8d86719496908d8d856f78888b8b82756e709296817174849590736e6e6e6e6e6f9296908c8c857194967b707f92916e9096908c8c867092967d74838f796e6e75838c8c89786f6e8696886e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e737f7d6f6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6f7b80736e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e70819c796f75848b8b85716e6e75828b8b88786f6e869489737093967c7d8c8f96968e8c7b7383958e716e6e81968d7194937e707e96916e9096908c8c86709296908c8b85787a9c83706e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e7e979b6f839b8d79767e776e8199907b7585a28c758ea4a09077a0a4816f707ea4a4787070859a8da283726e88a49872a1a49b8488a49d6e9da4958a8984709fa48372788b9f8ba09c816e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e84a29b6f8da088737276736e8a9e8c74717da496788ea4978296a3a4816e6e7ba4a4776e859d9882a0a07e7088a49872a1a48a8a9ba49d6e9da48b797876709fa4826f7383a291a1a4866e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e6e7d979b6e6e7f8f92908d766e6e7d8d92909284716e8ea492707b9ca3816e6e7ba4a4778098968484859b987d88a49872a1a4807488a09d6e9da4988e8e88709fa4968f9191826f9b9c816e6e6e6e6e6e6e6e6e6e6e",
    ]),
    "head_cannon": ("Head Cannon", 1, [
        "11.867:8d6b646f94957b67889595959494906c64646d91959272646464809595959495917866646464646465718e959595937e6764646f9395906f64646486958e6e646f929578698a958d69646b90937b64667892959595917665647b9595786467828b6b646f94947b678795948f8f8f8b6c64647893959482656464809595908f9295927865646464646b8a95949091948d6b64647b9495947d65646486949481666e9194786889959582666b8f937a64769195929092959171647b95958e6c66808c6a646f94957b6787958b6a6a6a69656466869594958c6a6464819593726a7b91958a69646464657e9494826b7188766564668a9594958869646486959591746e9295786889959592766c8f937a67899591786b7b929583667b9596958068819284818695957b6787958f7775756d64646d91917e90937264648195926e64658394906c6464646989958a696464696564646f92907e92916f6464869596958e7791957868899596958a7290937a6f93957f66646688958c687b9596959276819594949496957b678795959292927e646478948d6d88948464648195926e6464789391706464646c909583656464646464657b958a6d8c947f646486959595958f9495786889959595948e94947b719595796464647d948e6c7b95969595909095908f9196957b678795948f908f7c64658895886d7e958f6b648195926e64647b93916f6464646b8e9584656464646464678b95856c83958b696486958c8795959595786889958d89959595947a7195957a64646580958d6b7b9594839495958e706a7495957b6787958b6a6a6a67646e9295938f92959475648195926e64688895906c6464646786948f6f64656e6964729295928f9295937264869485748f95969578688995886e8f9595947a6d9095846764698c958c687b9594718595958b6b646f94957b6787959079787876687c9594908f909395866581959484808894948267646464647a93958c7f838e82697f95948f8f9094958364869486697a939595786889958864799295937a65859593857e8895947b657b95946f708f958b6b646f94947b678795959292928f6e8994876c6a6b81948e6c81959594949595896e64646464646a8794959394958a708c94856a6a6c85948d698694856867839595786889948864698794937a646e8e9594939595866a647b95946f657c938d6b647095957b67889595959595917890957765646474949574819595959593806d646464646464646b7f9395958a71759295736464647994957086958768646c909578698a958864647291947b64647087949595856a64647b95956f646783",
        "12.800:959372666889957e6b91959595959588666666759195876b66666b91959595959377666666666666666a8e959595937266666673959588666666698a957e66667e95886680949271666688957e6666708e9595958f7266667e95886666739595938d6f666687927d6a8e9395959595876666667e9392937366666a8f9395959595947c666666666666889595959595916b66688092918a6b66666687929372667d9287667b919386696687927d66708f94959595949171667d92937e66708f93958e6f666688947e6a90957e6866666666666a859495947466666b90947a67738f938d6e666666667e94947d6671917366666b919595947c6666668894958a6a7e9388667c939492766688947e677994937b667892947d687e9494957371929595927166728f947e6a90957a67666666666673949286958d6a666b909473666677929473666666667e9388666666666666666f918c89947e66666688949492767e9488667c939594886688947e6a8e95886966698694906a7e9495958c738f95959595959595957e6a9095959595916b66667395857493916b666b90947366666b9093736666666b8695866666666666666686947e6b919070666688949595908c9488667c939595958d90957e6b9094736666667394906b7e949595948b9195959595959595957e6a9095959595916b666a8c95736b86947f666b90947366666b9093736666666b8795866666666666666688937b6a90947366668893929495959488667c939393959595957e6b9094736666667394906b7e94939395959595959274687490947e6a90958168666666666b90948e8b919488666b90947366666e919473666666688093886666666666667892948d8a939584696688937a8694959488667c938870909495957e6a9095826866687f94906b7e9488738f949595958e6f666688947e6a90957767666666667e9395959595948e716b909473666688949271666666667e939278666c8370667e949595959595916b6789947d6b90949488667c938b6e749495957e688194906c666b909486697e93886685949495948e6f666687927d6a8f9494939393866688938b7a787e90937d6a8f9395959594957e66666666666d8c9495939595907087938878787f9291746688937c6673949287667b928a6d6b8793937d66739593959395949573667d9287666b909393959271666789957e6b91959595959588708e947b6666668895816c9195959595958466666666666666749295959595787495916b6666698395886688957e6669839588667f948d6e667691957e66667a93959595947b66667e95886666739595",
        "11.545:969674666687968066709696969696968366666e8b9686676666668b96969694857068666666666666666a718c94856c6866667391967d6766666c939676676689967f667296947066688f96786666666a768e927d6c67668096896966749696969674666687968066709696949292928166667896968e716666668b9695939496947d6866666666666a859595949694786666829696896b66666c9396906e6689967f667296968b6a688f967866666b8c969594969375678096957f68749696969674666687968066709696847b7b7b736669819695967c6666668b968c7e808b94907366666666677b95938580888d73666c899695967166666c939695826889967f66729696947c698f9678666781959184828d968d69809696907274969696968178788d9680667096957d78787566666d94948695866a66668b967d66666d8c967f666666666a85968566666971666678959088967c67666c939696907389967f66729696968c718f9678666d89947d66667391927280969696827696969696969696969680667096969696968e66667995867093957066668b967d66666689967f666666666f93957466666666666982967c77958e68666c93969696898f967f66729696969685929678667794906c66666a85958280969696938596969696938d8c93968066709696928c8c8666668a96837692967d67668b967d66666689967f666666666f93957466666666666d92967b7c949274666c9396858e9696967f66729695849196969678667794906c66666a85958280968e859496969696967f72718b9680667096957a717170666e9096928d94968d68668b967d66666d8c967f666666666a8596856666697166779696908e959583666c9396747a9596967f667296946f8195969678666d89947d6666739192728096876d8b969696969674666687968066709696847b7b7b737e9596969696969272668b968c7e808b94907366666666677a95938580888d73899696969696968b6d6c9396726a8596967f667296946c6c8a969678666781959184828d968d6980968766739496969696746666879680667096969492929283859585707070859583668b9695939496947d6866666666666a8595959496948190947e7070708e947a6c939672666b8c967f667296946c666e91967866666b8c9695949693756780968766677a9696969674666687968066709696969696969393906d666666819689698b96969694847068666666666666666a718c94846c8295886a6666668c967f6d93967266667c947f667296946c66678296786666666a768e927d6c676680968766666e8c96",
    ]),
    "jetpack_thruster": ("Jetpack Thruster", 1, [
        "17.000:929898906d88989898947d98989898957c939898937466666b8e956f666666749598906d6f93866875988167667095989898987c89926d6988956f8a989897816671928a666f9289667b969896798d98989898837498989898728798989782679498978f6d85969898967e98979798967c90979898926d667094958166666c90979897887191846b8c916d66667196989797987c86906c6886926e8897989898786f9187666d90866f959798987d8e989797988374969798987286979898987e66688c8f6d8594716666676a849783696d9191718c957f667796978866667f968a6c8a7d6e92817b968266666666697e968a6b6b88906c6886936e88957b7d968b729188666d918770948066766d6876958e6d6974977866666686957d7b969266668a8f6d85926e666666667e9477666d928666719484668994908f6b698795706666666e928d8e936e6666666666729384666a8a926e6a8b936e88916c678c8f729188666d9187709480666666666b908a686675967766666686926d678a9766668a8f6d859798978466667e9578666d928766779583668a847f97726c908d6b6666666e92979787666666666666739384666a8a97989898936e88916c6a8e8f729188666d9187709597937266666c908a6866759798988c6986926e698d9766668a8f6d859798988566667e9578666d92948793957b71957a7594776d918b696666666e9297968b686666666666739384666a8a97989898936e8896878a9789729188666d9186668498989877666c908a6866759798988e6a86968888978f66668a8f6d859471666666667e9578666d929898988f6c74968e8c968b6c8d926e6666666e92979897726666666666739384666a8a957f7d92936e8997989895756d908a6671928466666e8b968c696c908a686675977866666686979898957a66668a8f6d85916d666666667e9578666d92969082686784979898978c6680957666776b6e928e7e958b6666666666739384666a8a906c6886936e899793968c666a8e8b667e957c6666666b8f8e6a6c908a6866759677666666869793968d699791968f6d84969393906f667d9377666d9087666666678d927c7a8b94737c96979497856f91836c8e927166666666729183666a898f6c6885926e87906e8a91706a8e969497947070958b869587686b8f89686674959493927086916e89917498989878688798989896706681967b666e938867666671938867667598776989989897817094866976988167666666759488666b8c926d698995708a926e75987a66779898988767719698989775666d918d6866779898989872879370739881",
        "16.857:9d9d9d85729d9d9d9d8e7e9d9d9d9d9472969d9d9d9769677d99977567676e9d9d9d9d8e75947d6d8f9574676772919d9d9d9d778392716788926f879d9d9d9d776d97896c6c978667909c989c78799d9d9d9d9073929d9d9d8267949d9d9d947f869782719c8e7f7f79727f9198857b6c95937f8d977367829b9a8067678398877f867974937e7593856d67676c7a819a907f6e8391706785906d869b878494887093876a6b93866a8f917d7f6f6f7f8d9c857a72918e807f736793917f909867729180719b866f6d67676787936f6767958b677e977b6988929489676795927167706874928684937467676767676b988667678493797289906c8699746d8b97728f866a6b91856b8f8c6e686767677f9b7167739286706d6968938867859c67709080719c94847f6867678591696767968c677b957d6f8e777d8b6967958d6767676774949a9b896867676767676b99866767879b959399916d869a716986987290876a6b9286679099826c676767809c7167749494837e6f69948867859c67709080719d9a928d6c676785926a676796958791977078977475957767958d6767676774949d9d896767676767676b99866767879d9b9a9b916d879c898795896f91876a6b9286677794948c796867809c7167749499918d7669949285949c67719180719c9387846c676786926b6767969a989689697e9c82809b7f67958d6867676774949995907067676767676b9886676787998e8a94916d879c9799997b6d908a6c6b94866768838d978b6b67809c7167749391888473699498989c8e6975937e709b83696968676785916a6767959a958a6c69819c9b9b9c8267948e6d696969749391859d8368676767676b988667678692726786906d879c989b92716b8c92746d98866769686f8b9a6e67809b71677493806a69686994999b9c748a879a78709d9488857e676787926b6767968f7370687094907a7b9391717d998b838d8173938274959473676767676b998767678791706785916d879b77849975687d9a8b8a9b8667847b7892936c67809d726775949387867767938a82997d999494726f99989593886767848f6a676793896767677397836b6b8596756f8c9794947b728f7a6b85977c686767676a96856767848d6e67818d6c84966b76947f69719096989178678b8e8b93826a677e99716773919894937d679083718e8b9b9d896c6e949598978b6767808a6767678f8667676772937867677795766778999d8e69718b7767759382696767676a9182676780896c677e896a81916b708b896a687f9b9c846767879c9d907067677c937067728c9598977f678c80678297",
        "14.111:769a9a8f6a6a949a9a9a8468929a9a9a9a7c919a9a927367677393946a6767676784957a67739a7b687b977e6767709a9a9a9a9a789880686985947a9a9a98876c67809770676d9483676e91947a7c9a9a9a9a927b9a9a9a9a72779a9a98866c769a9a8f6a6a949a9a9a8468929a9a9a9a7c919a9a999278677799946a67676f8c9799957e749a7b6e8d926f6767709a9a9a9a9a789880686985947a9a9a9a978b6a809770676d9483698e98998d7c9a9a9a9a927b9a9a9a9a72779a9a9a978f6b748f8f6a6a948e78746e6772788f94746c91907979987d687d9a987d676774987e748277739a7c79967e68676769747a958b74719880686985947a9a857587946c809770676d94837e937d74766c74819a83727a9a8374746a779a8475879967678b8f6a6a948a6c676767676a8a916767918a6b6e987f6c8e8a92886769859371676e6b739a8d8f8b6d67676767676c9286676e98886b6b89947a9a796881966d809770676d948383968069696767759a7c67799a7c686767779a7968819a67678b8f6a6a949385837767676988916767918b6b6e987f6d977f888d6b6b92896c676767739a989a836767676767676a9286676e989485838f947a9a7b6881966d809770676d9483749591857d6767729a7c67799a8c83836d779a7a68819a67678b8e696a949a9a9a846767698891676791938182987c77988b8d93766b92896c676767739a9a9a8c6e67676767676a9286676e989a9a9593947a9a8b7f8c946c7e967367709482687f8693937267729a7c67799a9a9a9a72779a8a7f8c9867678b8e686a94948a887a67676988916767919a9a978a7387999a9a9a7f69859371676e6b739a948d987b68676767676a9286676e989189858e947a9a9a9a9a886a79947f677b947b67686b83968067729a7c67799a8f88886e779a9a9a9a8b73748f8d676a948e78746e6767698891676791968e866f688f958d8e96846974987e748277739a867396886a676767676a9286676e9880686985947a9a91919979686e8f90748d926f6d76747e937c67729a7c67799a8374746a779a9191997b92999888676a949a9a9a846767698891676791896967676e9085676a8893716f8b9799957e749a7b6b879873676767676a9286676e9880686985947a9a777294896a678596999789677b9499988b6767729a7c67799a9a9a9a72779a7772948c72928b6a676a949a9a9a846767698891676791896967678194736767769a74676784957a67739a7b687b988c676767676a9286676e9880686985947a9a776781966c67688197846a67687e95906d6767729a7c67799a9a9a9a72779a7767819a",
    ]),
    "dart_gun": ("Dart Gun", 1, [
        "8.400:9493949493939394927b6e6767676767677b929494937467676767678a939494939393948d7b69748f939394949494939393866a6767676767676a758d9494949393938870676f949494836767677d93949475677b9494948269676774929394939394928e8e909394938871676767676c87939493938868676767678a9394938f8e919494927a738a8e8e91949494908e8e836a6767676767697f909493918f8f9193927d676f939393816767677c93939375677b949494937e686773919293949394866c6c7288929493826a6767677693949393949074676767678a93948b6f6c789094938a686b6c6c82949494766c6c6b676767676767749193948d786c6d7989806a676f949394816767677c93949475677b9494949490786773929394949393826767676b869394937067676a8993927e82949383696767678a9394896a67698894938c6767676780949494736767676767676767678894939071676767676c6867676f949394816767677c93949475677b94949494948f777492939494939383676767677f939393716767749193906d758f9390766767678a93948b716f768f94938c6767676780949494736767676767676767678c93948e696767676e76766f676f949394816767677c93949475677b949494949494918c949394949393836767676780939494716769889394896f6e889394866b67678a9394938d8d92949491786767676780949494736767676767676767678b94948f6a6767677c949380676f949394826767677d93949475677b949492818c949494949394949393836767676e889494906f6778919494928f8e929494937367678a93949493939494907a6867676767809494947367676767676767676782949391786867677c949380676f939494866a67698294949273677b94949278718e94949493949493948d7f80848b9494917d696c879394918f8e8e8f9294948868678a93948e788393949076676767676780949494736767676767676767676f90939490857e7f8c949380676a82939491877e85909493836a677b9494937868788f94949394939394939393949393917c6967769293917b6c6c6c6c7e94939073678a9394896a6e8993938d6e67676767809394947367676767676767676767758d93949392929494927f6767728c939493929394938d7467677b9494927767687890949393949494949494948e7f7467676b899493896a676767676f92949483678a93948a6a67739094948367676767809494947367676767676767676767676f7e90949393948c796f6767677080929493949280726767677b9494937867676777929494",
        "8.800:95959595959595958d7769696969696969819595958c6969696969698495959595959595906e6969849595959595959595958d73696969696969696a8f9495959595958469696e959595766a69697d9495907c696e9095957969696976959595939293949595959494948c6969696969698093919291846969696969839292949595959495957269849595949393939595958c736969696969696e95959494959595949488696e93919372696969798e938d7569698e9193927c6969759391939593947d6d697388949393846a6969697e90949594948f69696969698494948870696e9293938c72696969799594927c6a69696969696969697295939393726969788c8469696e959395726969697990958f76696a8f9394948f7b69769493959592947669696970839493936b696969849591888794917c6a6969698493938469696a75939495766969697994938f69696969696969696969729492956e69696969696969696e959395726969697990958f76696a8f939494948873769493959592947669696969769492936b69697a8d958169769493936b6969698493938469696d8694949275696969799493906c69696969696969696e7f9594926e69696969696969696e959395726969697990958f76696a8f93949594948f899394959592947669696969769492936b69698894948169738d9493726a696984949493908f949593957e6d696969799493906c69696969696969696e809595906e6969697b8f9588696e959395726969697990958f76696a8f94929293949495949395959294766969696b799493936b69748c94938f8a8c919494916e6969849494959595959494826e69696969799493906c69696969696969696a759492956e696969798d9588696e9594957a6c69697b92948d71696a8f9590777e92949494939595939476696969799493938e6a698a949595959595959593956e696984949490898c9593956e6969696969799493906c696969696969696969729492948c7069697c909487696d8c94949074696a7e94938c69696a90949479697d9494949395939293949595959494958f6969698b9393867a797a7d8d93938c7069849292846971929293856e696969697993928e6b6969696969696969696b7a9593959592939493938869696b939294959393949494896969698e93917869697994929293959595959595959593866969698e94958571696969696e95959572698495958469696e959595756a696969799595906f696969696969696969696b7794959595959595928369696a7891959595959594876969696c9095957969696c7c959595",
        "7.692:949494949494918678716a6767676767676787939494756867676767709494949494938f82766c676787949494949494949494948a676767676767676d747e8c929187777369679194948e6767677494949480677e94948c736867678c9494949494949494949494948e7e6d6767676767728c94949491696767676770949494949494949494866f6787949494949494949494948a6767676767677188949494949494949379689194948e6767677494949480677e949494866e67678c9494949494948f7676767f9394917c68676767678493949494947b67676767709494948976767c8b9494816c7276767690949492767676736767676767748c94938679767682908273689194948e6767677494949480677e94949494886f678c9494949494948c676767697b94948d75676767748d9491849194916a67676770949494846767688094949074676767678e94949167676767676767676d839494836e6867676a6d6a67679194948e6767677494949480677e9494949494886f8c9494949494948c67676767779494947d6767678594947c6a8b94947f676767709494948467676b8294948d72676767678e9494916767676767676767779194947b6767676770737373689194948e6767677494949480677e94949494949485919494949494948c67676767779494947d6767768d9494706779929491676767709494948d8282858f94947d6a676767678e9494916767676767676767779194947b67676767848e8e8e6b9094948e6767677494949480677e949494888f9494949494949494948c676767697b94948c756769849494948d8b8d939493846767709494949494949494937d6a67676767678e94949167676767676767676d839494846e686767899494946b8294948e6a6768769494927d677e94949477788e94949494949494948f7676767f9394917c67677b90949494949494949494906f67709494948e858b93948f766767676767678e949491676767676767676767748c9493877976768c9494946b69929492867679889494876e677e94949476687a90949494949494949494949494948e7e6d676b849494837c7c7c7c7c92949386677094949484676f869494877067676767678e94949167676767676767676767718894949494949494948a6a677c929494949494948b7467677e9494947667677790949494949494949494918678716a67677b9094947467676767677c94948f6d709494948467676d849494856e676767678e94949167676767676767676767676d747e8d93908677746e68676873778a929185766f6767677e949494766767677b919494",
    ]),
}


def _purple_mask(a):
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    return (b > 140) & (r > 80) & (b - g > 70) & (r - g > 30)


def stock_frame(img):
    """Фиолетовая рамка окна Sample Exchange / Research Shop: (x0, y0, x1, y1) в долях экрана или None.
    Рамка - тонкие линии, поэтому ищу её по строкам и столбцам, где фиолетового больше 45% длины:
    самые крайние такие строки - верх и низ рамки, столбцы между ними - её бока."""
    w, h = img.size
    sw = min(w, 1280)
    a = np.asarray(img.convert("RGB").resize((sw, max(1, round(sw * h / w))), Image.BILINEAR)).astype(np.int16)
    m = _purple_mask(a)
    H, W = m.shape
    rows = np.nonzero(m.mean(axis=1) > 0.45)[0]
    if len(rows) < 2 or rows[-1] - rows[0] < 0.4 * H:
        return None
    y0, y1 = int(rows[0]), int(rows[-1])
    cols = np.nonzero(m[y0:y1 + 1].mean(axis=0) > 0.45)[0]
    if len(cols) < 2:
        return None
    x0, x1 = int(cols[0]), int(cols[-1])
    if not (0.45 * W < x1 - x0 < 0.85 * W):
        return None
    return (x0 / W, y0 / H, (x1 + 1) / W, (y1 + 1) / H)


def daily_frame(img):
    """Золотая рамка окна DAILY REWARDS: (x0, y0, x1, y1) в долях экрана или None."""
    w, h = img.size
    sw = min(w, 1280)
    a = np.asarray(img.convert("RGB").resize((sw, max(1, round(sw * h / w))), Image.BILINEAR)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    m = (r > 185) & (g > 140) & (b < 140) & (r - b > 70)
    H, W = m.shape
    rows = np.nonzero(m.mean(axis=1) > 0.38)[0]
    if len(rows) < 2 or rows[-1] - rows[0] < 0.3 * H:
        return None
    y0, y1 = int(rows[0]), int(rows[-1])
    cols = np.nonzero(m[y0:y1 + 1].mean(axis=0) > 0.38)[0]
    if len(cols) < 2:
        return None
    x0, x1 = int(cols[0]), int(cols[-1])
    if not (0.35 * W < x1 - x0 < 0.75 * W):
        return None
    return (x0 / W, y0 / H, (x1 + 1) / W, (y1 + 1) / H)


def stock_point(frame, rel):
    return (frame[0] + rel[0] * (frame[2] - frame[0]), frame[1] + rel[1] * (frame[3] - frame[1]))


def _white_number(a, thr=215):
    """Число белыми цифрами на тёмном фоне (без знака доллара); полоски рамок по краям отбрасываются."""
    m = a.min(axis=2) > thr
    H = m.shape[0]
    for x0, y0, x1, y1 in _components(m):
        if y1 - y0 > 0.85 * H or y1 - y0 < 0.25 * H and (x1 - x0) > 3 * (y1 - y0):
            m[y0:y1, x0:x1] = False
    if m.sum() < 12 or m.mean() > 0.5:
        return None
    return _read_green_number(m, tol=0.22, dollar=False)


def stock_tokens(img, frame):
    """Сколько жетонов (YOUR TOKENS) или None."""
    w, h = img.size
    p0, p1 = stock_point(frame, STOCK_TOKENS_BOX[:2]), stock_point(frame, STOCK_TOKENS_BOX[2:])
    a = np.asarray(img.crop((int(p0[0] * w), int(p0[1] * h), int(p1[0] * w), int(p1[1] * h))).convert("RGB")).astype(np.int16)
    return _white_number(a)


def _text_comps(gray, thr=232):
    """Маска белого текста без линий рамки и мелких точек; вторым значением - компоненты (x0, y0, x1, y1)."""
    m = gray > thr
    H, W = m.shape
    keep = []
    for x0, y0, x1, y1 in _components(m):
        if x1 - x0 > 0.5 * W or y1 - y0 > 0.75 * H:      # линия рамки картинки
            _erase_comp(m, x0, y0, x1)
        elif (x1 - x0) * (y1 - y0) < 4:
            m[y0:y1, x0:x1] = False
        else:
            keep.append((x0, y0, x1, y1))
    return m, keep


def _erase_comp(m, x0, y0, x1):
    """Стереть из маски связную область, верхняя строка которой лежит в [x0, x1) строки y0."""
    xs = np.nonzero(m[y0, x0:x1])[0]
    if len(xs) == 0:
        return
    H, W = m.shape
    stack = [(y0, x0 + int(xs[0]))]
    m[stack[0]] = False
    while stack:
        cy, cx = stack.pop()
        for ny in (cy - 1, cy, cy + 1):
            for nx in (cx - 1, cx, cx + 1):
                if 0 <= ny < H and 0 <= nx < W and m[ny, nx]:
                    m[ny, nx] = False
                    stack.append((ny, nx))


def _name_sig(gray):
    """Отпечаток названия предмета: (отношение ширины надписи к высоте, вектор 96x10).
    Надпись вырезается точно по тексту и приводится к одному размеру - на разных разрешениях игра рисует
    её разным кеглем, а так отпечаток от размера не зависит."""
    m, comps = _text_comps(gray)
    if not comps:
        return None
    rows = m.sum(axis=1)
    good = np.nonzero(rows >= max(2, 0.2 * rows.max()))[0]
    if len(good) == 0:
        return None
    y0, y1 = int(good[0]), int(good[-1]) + 1
    cols = np.nonzero(m[y0:y1].sum(axis=0) >= 1)[0]
    if len(cols) < 8 or y1 - y0 < 4:
        return None
    x0, x1 = int(cols[0]), int(cols[-1]) + 1
    piece = np.clip(gray[y0:y1, x0:x1].astype(np.float32) - 150, 0, 105) * 2.4
    small = Image.fromarray(piece.astype(np.uint8)).resize(STOCK_SIG, Image.BILINEAR)
    v = np.asarray(small, dtype=np.float32).ravel()
    v -= v.mean()
    n = float(np.linalg.norm(v))
    if n < 1e-3:
        return None
    return (x1 - x0) / (y1 - y0), v / n


def _qty_number(gray):
    """Количество под названием (x1, x50, x1,000) -> число или None."""
    m, comps = _text_comps(gray, thr=225)
    # буквы и цифры плотные и не слишком вытянутые; уголки и линии рамки - тонкие
    comps = [c for c in comps if 0.25 <= (c[2] - c[0]) / (c[3] - c[1]) <= 1.2
             and m[c[1]:c[3], c[0]:c[2]].mean() >= 0.3]
    if len(comps) < 2:
        return None
    h = max(c[3] - c[1] for c in comps)
    comps = sorted((c for c in comps if c[3] - c[1] >= 0.45 * h), key=lambda c: c[0])
    # надпись стоит по центру одной группой; обрывки рамки по краям отделены от неё большим промежутком
    groups = [[comps[0]]] if comps else []
    for c in comps[1:]:
        if c[0] - groups[-1][-1][2] > 1.2 * h:
            groups.append([])
        groups[-1].append(c)
    mid = m.shape[1] / 2
    comps = min(groups, key=lambda g: abs((g[0][0] + g[-1][2]) / 2 - mid)) if groups else []
    if len(comps) < 2:
        return None
    clean = np.zeros_like(m)
    for x0, y0, x1, y1 in comps[1:]:                 # первая буква - «x»
        clean[y0:y1, x0:x1] = m[y0:y1, x0:x1]
    return _read_green_number(clean, tol=0.3, dollar=False)


def sig_to_hex(sig):
    asp, v = sig
    q = np.clip(np.round(v * 600 + 128), 0, 255).astype(np.uint8)
    return f"{asp:.3f}:" + q.tobytes().hex()


def sig_from_hex(text):
    try:
        asp, hx = text.split(":")
        v = np.frombuffer(bytes.fromhex(hx), dtype=np.uint8).astype(np.float32) - 128
        if len(v) != STOCK_SIG[0] * STOCK_SIG[1]:
            return None                              # отпечаток от старой версии
        return float(asp), v / max(1e-3, float(np.linalg.norm(v)))
    except Exception:
        return None


def sig_match(a, b):
    """Похожесть двух отпечатков названий (1 - одинаковые); 0, если пропорции надписей заметно разные."""
    if a is None or b is None:
        return 0.0
    if abs(a[0] - b[0]) > 0.3 * max(a[0], b[0]):
        return 0.0
    # надпись может быть вырезана на пиксель шире или уже - пробую небольшие сдвиги по горизонтали
    A = a[1].reshape(STOCK_SIG[1], STOCK_SIG[0])
    return max(float((np.roll(A, dx, axis=1).ravel() * b[1]).sum()) for dx in (-2, -1, 0, 1, 2))


def stock_cards(img, frame):
    """Карточки Research Shop: список словарей по одной на товар.
    state: buy (зелёная BUY) / sold (красная SOLD OUT); pt - центр кнопки; price; sig; box - картинка товара (пиксели)."""
    w, h = img.size
    sw = 960
    a = np.asarray(img.convert("RGB").resize((sw, max(1, round(sw * h / w))), Image.BILINEAR)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    fw = frame[2] - frame[0]
    bw = 0.0889 * fw                               # ширина кнопки BUY в долях экрана
    found = []
    for state, mask in (("buy", (g > 100) & (g - r > 55) & (g - b > 55)),
                        ("sold", (r > 150) & (r - g > 80) & (r - b > 60))):
        for x in _blobs(mask):
            if (0.6 * bw <= x["w"] <= 1.35 * bw and 0.25 * x["w"] <= x["h"] * h / w <= 0.65 * x["w"]
                    and frame[0] + 0.3 * fw < x["cx"] < frame[2] and frame[1] < x["cy"] < frame[3]):
                found.append((state, x))
    full = np.asarray(img.convert("RGB")).astype(np.int16)
    u = fw * w / 1642.0                            # масштаб окна относительно снимка 2557x1437
    cards = []
    for state, x in found:
        bx, by = x["cx"] * w, x["cy"] * h
        card = {"state": state, "pt": (x["cx"], x["cy"]), "price": None, "sig": None}
        # цена: белые цифры справа от значка жетона, над кнопкой
        px0, px1, py0, py1 = int(bx - 76 * u), int(bx + 85 * u), int(by - 128 * u), int(by - 84 * u)
        if py0 >= 0 and px0 >= 0:
            card["price"] = _white_number(full[py0:py1, px0:px1])
        # картинка товара слева от кнопки; название - белый текст внизу картинки
        cx0, cx1, cy0, cy1 = int(bx - 278 * u), int(bx - 82 * u), int(by - 225 * u), int(by + 31 * u)
        card["box"] = (max(0, cx0), max(0, cy0), cx1, cy1)
        nx0, nx1, ny0, ny1 = int(bx - 268 * u), int(bx - 90 * u), int(by - 75 * u), int(by - 10 * u)
        card["qty"] = None
        if ny0 >= 0 and nx0 >= 0:
            card["sig"] = _name_sig(full[ny0:ny1, nx0:nx1].min(axis=2))
            card["qty"] = _qty_number(full[int(by - 10 * u):int(by + 25 * u), nx0:nx1].min(axis=2))
        cards.append(card)
    cards.sort(key=lambda c: (round(c["pt"][1] * 8), c["pt"][0]))
    return cards


def open_private_link(links=None):
    """Открыть приватный сервер прямо в клиенте Roblox (deeplink), при ошибке - через браузер."""
    if links is None:
        links = (SERVER_DEEPLINK, SERVER_LINK)
    for link in links:
        if not link:
            continue
        try:
            os.startfile(link)
            return True
        except Exception as e:
            log(f"  не получилось открыть {link.split(':')[0]}-ссылку: {type(e).__name__}")
    return False


def close_roblox():
    if sys.platform == "win32":
        subprocess.run(["taskkill", "/IM", "RobloxPlayerBeta.exe", "/F"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def _menu_frame(img):
    """Большая зелёная рамка меню телепорта (ищем на кадре 640 px, чтобы тонкая линия не терялась)."""
    w, h = img.size
    a = np.asarray(img.convert("RGB").resize((640, max(1, round(640 * h / w))), Image.BILINEAR)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    frames = [x for x in _blobs((g > 100) & (g - r > 55) & (g - b > 55)) if x["w"] > 0.4 and x["h"] > 0.3]
    return max(frames, key=lambda x: x["w"]) if frames else None


def analyze_screen(img):
    """Что из элементов лобби видно на кадре окна."""
    w, h = img.size
    a = np.asarray(img.convert("RGB").resize((LOBBY_W, max(1, round(LOBBY_W * h / w))), Image.BOX)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    res = {}
    greens = _blobs((g > 100) & (g - r > 55) & (g - b > 55))
    # большая зелёная кнопка внизу: Select / Start / TELEPORT в меню телепорта
    res["button"] = next((x for x in greens if 0.10 <= x["w"] <= 0.30 and 0.045 <= x["h"] <= 0.14
                          and x["cy"] > 0.6), None)
    # зелёная иконка TELEPORT в меню слева
    res["tp_icon"] = next((x for x in greens if x["cx"] < 0.1 and 0.03 <= x["w"] <= 0.09
                           and 0.04 <= x["h"] <= 0.11), None)
    reds = _blobs((r > 170) & (r - g > 90) & (r - b > 60))
    # красная карточка Deployment Zone (у полноэкранного меню её правая часть темнеет,
    # поэтому ширина красного пятна может быть всего ~0.1 экрана)
    res["deploy_card"] = next((x for x in sorted(reds, key=lambda x: -x["area"])
                               if 0.12 < x["cx"] < 0.5 and 0.06 <= x["w"] <= 0.35
                               and 0.04 <= x["h"] <= 0.2), None)
    # карточка считается, только если вокруг есть большая зелёная рамка меню
    # (на экране загрузки Roblox бывает красный арт, похожий на карточку)
    if res["deploy_card"] is not None and not _menu_frame(img):
        res["deploy_card"] = None
    blues = _blobs((b > 190) & (b - r > 110) & (g > 90))
    # синие круги; издалека они маленькие. Слева - синие иконки меню (UNITS, CODES), их пропускаем
    res["pads"] = [x for x in blues if x["area"] > 0.001 and x["cy"] > 0.15
                   and not (x["cx"] < 0.17 and x["cy"] < 0.8)]
    H = a.shape[0]
    patch = a[int(0.50 * H):int(0.62 * H), int(0.58 * LOBBY_W):int(0.66 * LOBBY_W)]
    res["dialog"] = bool(patch.mean() < 45)        # тёмное окно Matchmaking
    return res


# ---------- дорожка и поворот ----------

def _hud_mask():
    m = np.zeros((PATH_H, PATH_W), dtype=bool)
    for x0, y0, x1, y1 in HUD_BOXES:
        m[int(y0 * PATH_H):int(math.ceil(y1 * PATH_H)), int(x0 * PATH_W):int(math.ceil(x1 * PATH_W))] = True
    return m


HUD = _hud_mask()
_ref_mask = None


def ref_mask():
    global _ref_mask
    if _ref_mask is None:
        bits = np.frombuffer(zlib.decompress(base64.b64decode(REF_MASK_B64)), dtype=np.uint8)
        _ref_mask = np.unpackbits(bits)[:PATH_W * PATH_H].reshape(PATH_H, PATH_W).astype(bool)
    return _ref_mask


def path_mask(img):
    """Красная подсветка дорожки на кадре окна -> маска PATH_W x PATH_H."""
    a = np.asarray(img.convert("RGB").resize((PATH_W * 2, PATH_H * 2), Image.BILINEAR)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    m = (r > 110) & (r - g > 60) & (r - b > 55)
    m = m.reshape(PATH_H, 2, PATH_W, 2).mean(axis=(1, 3)) > 0.5
    return m & ~HUD


def _rotate_mask(mask, angle, shift=(0, 0), scale=1.0):
    """Эталонная маска -> как она выглядит при повороте камеры на angle, сдвиге и масштабе
    (то же преобразование, что transform_point)."""
    im = Image.fromarray((mask * 255).astype(np.uint8))
    cx, cy = PATH_CENTER[0] * PATH_W, PATH_CENTER[1] * PATH_H
    t = math.radians(angle)
    c, sn = math.cos(t), math.sin(t)
    dx, dy = shift
    a_, b_ = c / scale, -sn / scale
    d_, e_ = sn / scale, c / scale
    c_ = cx - (c * (cx + dx) - sn * (cy + dy)) / scale
    f_ = cy - (sn * (cx + dx) + c * (cy + dy)) / scale
    out = im.transform(im.size, Image.AFFINE, (a_, b_, c_, d_, e_, f_), resample=Image.NEAREST)
    return np.asarray(out) > 127


def _score(ref, cur):
    inter = (ref & cur).sum()
    union = (ref | cur).sum()
    return inter / union if union else 0.0


def estimate_rotation(cur):
    """На какой угол (градусы, против часовой), сдвиг и масштаб текущая дорожка отличается
    от эталона. Масштаб нужен, если камера отдалена не так, как на эталоне.
    -> (угол, сдвиг (dx, dy) в клетках маски, оценка 0..1, масштаб)."""
    ref = ref_mask() & ~HUD
    cur = cur & ~HUD

    def sc(ang, scale, sh=(0, 0)):
        return _score(_rotate_mask(ref, ang, sh, scale) & ~HUD, cur)

    best = (0.0, 1.0, -1.0)
    for scale in (0.55, 0.65, 0.75, 0.85, 1.0, 1.15, 1.3, 1.45):
        for ang in range(-180, 180, 6):
            v = sc(ang, scale)
            if v > best[2]:
                best = (float(ang), scale, v)
    ang, scale, score = best
    shift = (0, 0)
    for rnd in range(2):          # угол+масштаб, потом сдвиг; и ещё раз с найденным сдвигом
        for d_ang, d_sc in ((3, 0.05), (1.5, 0.025), (0.75, 0.0125), (0.25, 0.006)):
            improved = True
            while improved:
                improved = False
                for a2 in (ang - d_ang, ang, ang + d_ang):
                    for s2 in (scale - d_sc, scale, scale + d_sc):
                        v = sc(a2, s2, shift)
                        if v > score + 1e-9:
                            ang, scale, score, improved = a2, s2, v, True
        sx, sy = shift
        for dx in range(sx - 4, sx + 5):
            for dy in range(sy - 4, sy + 5):
                v = sc(ang, scale, (dx, dy))
                if v > score:
                    shift, score = (dx, dy), v
    ang = (ang + 180) % 360 - 180
    return ang, shift, score, scale


def transform_point(pt, angle, shift, scale=1.0):
    """Точка эталона (доли окна) -> точка текущего вида (доли окна)."""
    # считаем в пикселях маски: квадратные пиксели, поворот как у Image.rotate
    cx, cy = PATH_CENTER[0] * PATH_W, PATH_CENTER[1] * PATH_H
    x, y = pt[0] * PATH_W - cx, pt[1] * PATH_H - cy
    t = math.radians(angle)
    xr = (x * math.cos(t) + y * math.sin(t)) * scale
    yr = (-x * math.sin(t) + y * math.cos(t)) * scale
    return ((xr + cx + shift[0]) / PATH_W, (yr + cy + shift[1]) / PATH_H)


def _red_mask_1456(img):
    w, h = img.size
    W = 1456
    H = max(1, round(W * h / w))
    a = np.asarray(img.convert("RGB").resize((W, H), Image.BILINEAR)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    return (r > 110) & (r - g > 60) & (r - b > 55), a


def _fit_line(ys, xs):
    """x = p*y + q с отбрасыванием выбросов."""
    ys, xs = np.asarray(ys, float), np.asarray(xs, float)
    keep = np.ones(len(ys), bool)
    p = q = 0.0
    for _ in range(3):
        if keep.sum() < 6:
            return None
        p, q = np.polyfit(ys[keep], xs[keep], 1)
        res = np.abs(xs - (p * ys + q))
        new = res < max(1.5, 2.5 * float(np.median(res[keep])))
        if (new == keep).all():
            break
        keep = new
    return float(p), float(q), int(keep.sum())


def find_corner(img, guess, scale=1.0, flipped=False):
    """Внутренняя вершина первого угла дорожки по красной подсветке (юнит в руке).
    guess - где она ожидается (доли окна). Возвращает словарь в пикселях кадра шириной 1456:
    v - вершина, a1 - единичное направление вдоль края первого отрезка (к туннелю),
    a2 - вдоль края второго отрезка, w - ширина дороги, h - высота кадра. Либо None."""
    m, _ = _red_mask_1456(img)
    H, W = m.shape
    if not flipped:
        return _corner_in_mask(m, guess[0] * W, guess[1] * H, scale)
    # камера развёрнута на 180 градусов: клин открыт вверх - ищу в перевёрнутой маске
    r = _corner_in_mask(m[::-1, ::-1], W - 1 - guess[0] * W, H - 1 - guess[1] * H, scale)
    if r is None:
        return None
    return {"v": (W - 1 - r["v"][0], H - 1 - r["v"][1]), "a1": (-r["a1"][0], -r["a1"][1]),
            "a2": (-r["a2"][0], -r["a2"][1]), "w": r["w"], "h": H, "found": True}


def find_corner3(img, guess, scale=1.0):
    """То же для 3-го поворота (клин между дорогами открыт влево): a1 - вдоль края дороги,
    по которой враги подходят (вниз-влево), a2 - вдоль края дороги, по которой уходят (вверх-влево)."""
    m, _ = _red_mask_1456(img)
    H, W = m.shape
    r = _corner_in_mask(np.rot90(m), guess[1] * H, W - 1 - guess[0] * W, scale, depth=40, width_from=1)
    if r is None:
        return None

    def back(d):
        return (-d[1], d[0])
    vx, vy = r["v"]
    return {"v": (W - 1 - vy, vx), "a1": back(r["a2"]), "a2": back(r["a1"]), "w": r["w"], "h": H, "found": True}


def _corner_in_mask(m, gx, gy, scale=1.0, depth=46, width_from=None):
    """Вершина клина (не-дороги), открытого вниз, в маске дороги m. width_from - по какому из двух
    отрезков мерить ширину дороги (None - по обоим)."""
    H, W = m.shape
    s = max(0.5, min(1.6, scale))
    xc = gx
    fit = None
    for _pass in range(2):
        rows = []
        xi = int(round(xc))
        if not (60 <= xi < W - 60):
            return None
        for y in range(int(gy - 30 * s), int(gy + depth * s)):
            if not (0 <= y < H) or m[y, xi]:
                continue
            left = m[y, xi::-1]
            pl = left[:-1] & left[1:]
            right = m[y, xi:]
            pr = right[:-1] & right[1:]
            if not pl.any() or not pr.any():
                continue
            xl = xi - int(np.argmax(pl)) + 0.5
            xr = xi + int(np.argmax(pr)) - 0.5
            if 12 * s <= xr - xl <= 100 * s:
                rows.append((y, xl, xr))
        # враги на дороге дают в маске "дырки" - беру только самый длинный сплошной кусок строк (сам клин)
        groups, cur = [], []
        for t in rows:
            if cur and t[0] != cur[-1][0] + 1:
                groups.append(cur)
                cur = []
            cur.append(t)
        if cur:
            groups.append(cur)
        rows = max(groups, key=len) if groups else []
        if len(rows) < 10:
            return None
        ys = [t[0] for t in rows]
        f1 = _fit_line(ys, [t[1] for t in rows])
        f2 = _fit_line(ys, [t[2] for t in rows])
        if not f1 or not f2:
            return None
        p1, q1, _n1 = f1
        p2, q2, _n2 = f2
        if not (-1.7 < p1 < -0.55 and 0.55 < p2 < 1.7):
            return None
        vy = (q2 - q1) / (p1 - p2)
        vx = p1 * vy + q1
        fit = (vx, vy, p1, p2)
        if abs(vx - xc) < 2:
            break
        xc = vx
    vx, vy, p1, p2 = fit
    if math.hypot(vx - gx, vy - gy) > 45 * s:
        return None
    n1, n2 = math.hypot(p1, 1), math.hypot(p2, 1)
    a1, a2 = (p1 / n1, 1 / n1), (p2 / n2, 1 / n2)
    if abs(a1[0] * a2[0] + a1[1] * a2[1]) > 0.3:
        return None

    def width(along, across):
        out = []
        need_gap = max(4, int(round(7 * s)))      # узкие разрывы (разметка по центру дороги) - не край
        for t in (14, 19, 24, 29, 34, 39):
            px, py = vx + along[0] * t * s, vy + along[1] * t * s
            seen, gap = False, 0
            for k in range(2, int(90 * s)):
                x, y = int(round(px - across[0] * k)), int(round(py - across[1] * k))
                if not (0 <= x < W and 0 <= y < H):
                    break
                if m[y, x]:
                    seen, gap = True, 0
                elif seen:
                    gap += 1
                    if gap >= need_gap:
                        out.append(k - need_gap)
                        break
        return float(max(out)) if len(out) >= 3 else None      # враги на дороге только укорачивают замер

    both = (width(a1, a2), width(a2, a1))
    ws = [w_ for w_ in (both if width_from is None else (both[width_from],)) if w_]
    w_road = sum(ws) / len(ws) if ws else ROAD_W_REF * s
    # ширина дороги известна по масштабу; замер нужен только для уточнения. Если он далеко от
    # ожидаемого (что-то закрыло дорогу) - не верю ему: от ширины зависит вся расстановка кучки.
    if not (0.85 * ROAD_W_REF * s <= w_road <= 1.2 * ROAD_W_REF * s):
        w_road = ROAD_W_REF * s
    return {"v": (vx, vy), "a1": a1, "a2": a2, "w": w_road, "h": H, "found": True}


def corner_point(c, uv, k=1.0):
    """Точка кучки (в ширинах дороги от вершины угла) -> доли окна."""
    u, v = uv[0] * c["w"] * k, uv[1] * c["w"] * k
    x = c["v"][0] + c["a1"][0] * u + c["a2"][0] * v
    y = c["v"][1] + c["a1"][1] * u + c["a2"][1] * v
    return (x / 1456.0, y / c["h"])


def find_range_circle(img, near, rmin, rmax, color="yellow"):
    """Центр круга дальности выделенного юнита (цвет круга зависит от редкости: у плунжеров и TV
    жёлтый, у ферм фиолетовый). near - где он ожидается, rmin/rmax - радиус, всё в пикселях кадра
    шириной 1456. -> (x, y, r) или None."""
    w, h = img.size
    W = 1456
    H = max(1, round(W * h / w))
    a = np.asarray(img.convert("RGB").resize((W, H), Image.BILINEAR)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    if color == "purple":
        m = (b > 105) & (b - g > 55) & (b - r > 30) & (g < 90)
        need = 25
    else:
        # линия круга тонкая и при уменьшении кадра тускнеет - пороги мягкие, лишнее отсеет подгонка
        m = (r > 150) & (g > 130) & (b < 110) & (r - b > 70) & (np.abs(r - g) < 60)
        need = 40
    for x0, y0, x1, y1 in HUD_BOXES:
        m[int(y0 * H):int(math.ceil(y1 * H)), int(x0 * W):int(math.ceil(x1 * W))] = False
    ys, xs = np.nonzero(m)
    if len(xs) < need:
        return None
    d = np.hypot(xs - near[0], ys - near[1])
    sel = (d > rmin * 0.8) & (d < rmax * 1.2)
    xs, ys = xs[sel].astype(float), ys[sel].astype(float)
    best = None
    for _ in range(6):
        if len(xs) < need:
            return None
        A = np.c_[2 * xs, 2 * ys, np.ones(len(xs))]
        sol = np.linalg.lstsq(A, xs ** 2 + ys ** 2, rcond=None)[0]
        cx, cy = float(sol[0]), float(sol[1])
        rad = math.sqrt(max(0.0, float(sol[2]) + cx * cx + cy * cy))
        res = np.abs(np.hypot(xs - cx, ys - cy) - rad)
        best = (cx, cy, rad, float(np.median(res)), len(xs))
        keep = res < max(2.5, 2.0 * float(np.median(res)))
        if keep.all():
            break
        xs, ys = xs[keep], ys[keep]
    cx, cy, rad, med, n = best
    if med > 2.5 or not (rmin <= rad <= rmax):
        return None
    return cx, cy, rad


def inverse_point(pt, angle, shift, scale=1.0):
    """Обратное к transform_point: точка текущего вида (доли окна) -> точка эталона."""
    cx, cy = PATH_CENTER[0] * PATH_W, PATH_CENTER[1] * PATH_H
    X = (pt[0] * PATH_W - cx - shift[0]) / scale
    Y = (pt[1] * PATH_H - cy - shift[1]) / scale
    t = math.radians(angle)
    x = X * math.cos(t) - Y * math.sin(t)
    y = X * math.sin(t) + Y * math.cos(t)
    return ((x + cx) / PATH_W, (y + cy) / PATH_H)


# ---------- бот ----------

# ---------- статистика сессии (её читают окно приложения и Discord) ----------

class Stats:
    def __init__(self):
        self.state = "idle"          # idle / waiting / running / stopping
        self.started_at = None       # когда нажали Старт
        self.matches = 0             # матчей за сессию
        self.match_started = None
        self.last_match_min = None
        self.step = 0
        self.step_total = 0
        self.step_text = ""
        self.money = None
        self.total_matches = 0       # за всё время (хранится в settings.json)
        self.slots = {}              # найденные юниты: тип -> номер слота
        self.prices = []             # цены на карточках слева направо
        self.mode = ""               # режим текущего матча


STATS = Stats()


# ---------- настройки (settings.json рядом с приложением) ----------

DEFAULT_SETTINGS = {
    "loops": 0,                  # 0 - бесконечно
    "use_speed": True,
    "speed": "2",                # скорость игры: "1", "1.5" или "2"
    "focus_after": 3,
    "move_to_primary": True,
    "private_only": True,
    "server_link": "",           # ссылка приватного сервера (roblox.com/share?code=...&type=Server)
    "auto_update": True,         # обновляться с GitHub при запуске и между матчами
    "mode": "hard",              # hard / nightmare
    "force_resolution": "",      # например "1920x1080": выставить разрешение экрана при старте
    "roblox_fullscreen": True,   # держать Roblox на весь экран (F11): ровно 16:9, как в эталоне
    "discord_enabled": False,
    "afk_auto": False,
    "discord_token": "",
    "discord_channel": "",
    "discord_allowed": "",       # ID через запятую; пусто - все в канале
    "discord_ping": "",
    "notify_match": True,
    "notify_screens": True,
    "notify_actions": True,      # постановки, прокачки, голосование, Rejoin
    "total_matches": 0,
    "stock_enabled": False,      # раз в полчаса между матчами заходить в Research Shop и скупать сток
    "stock_sell_trash": True,    # сдавать все образцы (ALL -> EXCHANGE) перед покупкой
    "stock_buy_new": False,      # покупать предметы, которых бот раньше не видел
    "stock_min_tokens": 0,       # сколько жетонов всегда оставлять
    "stock_last": "",            # отрезок последней проверки стока ("2026-11-15 14:30")
    "stock_items": {},           # предметы: ключ -> {name, buy, sigs, price}
}
SETTINGS = dict(DEFAULT_SETTINGS)


def stock_period():
    """Текущий получасовой отрезок: сток обновляется в XX:00 и XX:30."""
    t = time.localtime()
    return time.strftime("%Y-%m-%d %H:", t) + ("00" if t.tm_min < 30 else "30")


def stock_items():
    """Список предметов стока из настроек; дополняется известными предметами."""
    items = SETTINGS.get("stock_items")
    if not isinstance(items, dict) or items is DEFAULT_SETTINGS["stock_items"]:
        items = {}                   # не трогаю словарь из DEFAULT_SETTINGS
    fresh = not items                # новые известные предметы в уже настроенном списке не включаю сам
    size = STOCK_SIG[0] * STOCK_SIG[1] * 2
    for key, (name, qty, sigs) in STOCK_KNOWN.items():
        it = items.setdefault(key, {"name": name, "buy": fresh, "sigs": [], "price": None})
        it["qty"] = qty
        have = it.setdefault("sigs", [])
        for sig in reversed(sigs):
            if sig not in have:
                have.insert(0, sig)
    for it in items.values():                        # отпечатки старых форматов больше не годятся
        it["sigs"] = [h for h in it.get("sigs", []) if len(h.split(":")[-1]) == size]
        it.setdefault("qty", None)
    SETTINGS["stock_items"] = items
    global _STOCK_CLEANED
    if not _STOCK_CLEANED:
        _STOCK_CLEANED = True
        try:
            stock_cleanup(items)
        except Exception as e:
            log(f"сток: не получилось разобрать старые «новые предметы» ({e!r})")
    return items


_STOCK_CLEANED = False


def sig_from_picture(path):
    """Отпечаток названия и количество по сохранённой картинке товара (stock\\<ключ>.png)."""
    a = np.asarray(Image.open(path).convert("RGB")).astype(np.int16).min(axis=2)
    u = a.shape[1] / 196.0
    x0, x1 = int(10 * u), int(188 * u)
    return _name_sig(a[int(150 * u):int(215 * u), x0:x1]), _qty_number(a[int(215 * u):int(250 * u), x0:x1])


def stock_cleanup(items):
    """Разобрать записи «Новый предмет N», оставшиеся от прежних версий: по сохранённой картинке заново узнаю
    предмет; если он уже есть в списке - сливаю запись с ним, иначе обновляю её отпечаток."""
    changed = []
    for key in [k for k in items if k.startswith("item")]:
        it = items[key]
        path = os.path.join(HERE, "stock", key + ".png")
        sig, qty = None, it.get("qty")
        if os.path.exists(path):
            try:
                sig, qty = sig_from_picture(path)
            except Exception:
                sig = None
        if sig is None:
            if not it.get("sigs"):
                del items[key]                      # ни отпечатка, ни картинки - узнать его уже нельзя
                changed.append(f"{it.get('name', key)} - удалён (нет картинки)")
            continue
        # с кем совпадает: все остальные записи, кроме самой этой
        best, best_key = 0.0, None
        for other, o in items.items():
            if other == key or o.get("qty") != qty:
                continue
            sc = max((sig_match(sig_from_hex(h), sig) for h in o.get("sigs", [])), default=0.0)
            if sc > best:
                best, best_key = sc, other
        if best_key and best >= 0.6:
            o = items[best_key]
            o["buy"] = bool(o.get("buy")) or bool(it.get("buy"))
            if not o.get("price"):
                o["price"] = it.get("price")
            new_path = os.path.join(HERE, "stock", best_key + ".png")
            try:
                if os.path.exists(new_path):
                    os.remove(path)
                else:
                    os.replace(path, new_path)
            except Exception:
                pass
            del items[key]
            changed.append(f"{it.get('name', key)} = {o.get('name', best_key)}")
        else:
            it["sigs"] = [sig_to_hex(sig)]
            it["qty"] = qty
    if changed:
        log("сток: разобрал старые записи: " + "; ".join(changed))
        save_settings()


def stock_base_name(name):
    """'Toilet Rolls x1,000' -> 'Toilet Rolls'"""
    import re as _re
    return _re.sub(r"\s+[xх×]\s*[\d,. ]+$", "", str(name)).strip()


def stock_identify(sig, qty):
    """Какой это предмет: (ключ, похожесть названия, название семейства).
    Название сверяется по отпечатку, количество (x1, x50, x1,000) - по числу. Ключ None - такого предмета
    в списке нет; если при этом название знакомо (другое количество), третьим значением идёт его имя."""
    scores = []
    for key, it in list(stock_items().items()):
        best = max((sig_match(sig_from_hex(h), sig) for h in it.get("sigs", [])), default=0.0)
        scores.append((best, key))
    scores.sort(reverse=True)
    if not scores or scores[0][0] < 0.6:
        return None, scores[0][0] if scores else 0.0, None
    top = scores[0][0]
    items = stock_items()
    family = [k for sc, k in scores if sc >= top - 0.08]
    same = [k for k in family if items[k].get("qty") == qty and qty is not None]
    if same:
        return same[0], top, None
    if len(family) == 1 and (qty is None or items[family[0]].get("qty") is None):
        return family[0], top, None                  # количество не прочиталось, а предмет с таким именем один
    return None, top, stock_base_name(items[family[0]].get("name", ""))


def stock_summary():
    """Текст о настройках стока для Discord: переключатели и пронумерованный список предметов."""
    lines = [("✅" if SETTINGS.get("stock_enabled") else "⛔") + " проверять сток",
             ("✅" if SETTINGS.get("stock_sell_trash") else "⛔") + " сдавать образцы",
             ("✅" if SETTINGS.get("stock_buy_new") else "⛔") + " покупать новые предметы",
             f"оставлять жетонов: {int(SETTINGS.get('stock_min_tokens') or 0)}", ""]
    for n, (key, it) in enumerate(stock_items().items(), 1):
        price = f" — {it['price']}" if it.get("price") else ""
        lines.append(f"`{n:>2}` {'✅' if it.get('buy') else '▫️'} {it.get('name', key)}{price}")
    return "\n".join(lines)


def stock_find(text):
    """Предметы по номеру из списка, по части названия или все (all / все): список ключей."""
    items = stock_items()
    keys = list(items)
    out = []
    for part in str(text).replace(";", ",").split(","):
        part = part.strip().lower()
        if not part:
            continue
        if part in ("all", "все", "всё", "*"):
            return keys
        if part.isdigit() and 1 <= int(part) <= len(keys):
            hit = [keys[int(part) - 1]]
        else:
            exact = [k for k in keys if str(items[k].get("name", "")).lower() == part]
            hit = exact or [k for k in keys if part in str(items[k].get("name", "")).lower()]
        out += [k for k in hit if k not in out]
    return out


def stock_circle(img):
    """Фиолетовый круг под NPC (SAMPLES) в Research Sector: самое большое фиолетовое пятно вне меню и панели."""
    w, h = img.size
    a = np.asarray(img.convert("RGB").resize((LOBBY_W, max(1, round(LOBBY_W * h / w))), Image.BOX)).astype(np.int16)
    r, g, b = a[..., 0], a[..., 1], a[..., 2]
    blobs = [x for x in _blobs((b > 150) & (r > 90) & (b - g > 80) & (r - g > 40))
             if x["area"] > 0.0005 and x["cy"] < 0.78 and x["cy"] > 0.08 and not (x["cx"] < 0.18 and x["cy"] > 0.2)]
    if not blobs:
        return None
    big = blobs[0]
    # вблизи кольцо распадается на дуги (его перекрывает персонаж) - объединяю куски рядом с самым большим
    near = [x for x in blobs if abs(x["cx"] - big["cx"]) < 0.16 and abs(x["cy"] - big["cy"]) < 0.14
            and x["area"] > 0.15 * big["area"]]
    x0 = min(x["cx"] - x["w"] / 2 for x in near)
    x1 = max(x["cx"] + x["w"] / 2 for x in near)
    y0 = min(x["cy"] - x["h"] / 2 for x in near)
    y1 = max(x["cy"] + x["h"] / 2 for x in near)
    return {"cx": (x0 + x1) / 2, "cy": (y0 + y1) / 2, "w": x1 - x0, "h": y1 - y0, "area": sum(x["area"] for x in near)}


# ---------- автообновление с GitHub ----------
UPDATE_REPO = "fozitixx/TWDBOT"
UPDATE_BASE = f"https://raw.githubusercontent.com/{UPDATE_REPO}/main/"
UPDATE_EVERY = 20 * 60          # между матчами проверять не чаще, чем раз в 20 минут
_update_checked = 0.0

# 5.x updates only the entry script. These Git blob IDs identify the exact
# companion files for this version, even after the release branch moves on.
TEAM_FILES = {
    "wastelands.py": "9cad2e8755b2126fa8c750e3392eef164682a03e",
    "wastelands_alt.py": "11c539432b8c3f8221890a86bca6f31ee86ab88b",
    "wastelands_team.py": "d2626bd2cd32a489479804af05177968c84f3c95",
    "wastelands_view.py": "2e778d21677a17d0fc5e74672baa5e3b62c412e6",
    "wastelands_ocr.ps1": "496e34e723f8a27cd6993fc72f826f398459b5b9",
}


def team_directory(download=False):
    import hashlib
    import tempfile
    from pathlib import Path

    def matches(data, blob):
        return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest() == blob

    local = Path(HERE)
    cache = local / ".twd-wastelands" / VERSION.split()[0]
    for directory in (local, cache):
        if all((directory / name).is_file() and matches((directory / name).read_bytes(), blob)
               for name, blob in TEAM_FILES.items()):
            return str(directory)
    if not download:
        return None
    cache.mkdir(parents=True, exist_ok=True)
    for name, blob in TEAM_FILES.items():
        dest = cache / name
        src = local / name
        if dest.is_file() and matches(dest.read_bytes(), blob):
            continue
        data = src.read_bytes() if src.is_file() else b""
        if not matches(data, blob):
            response = _http_get(f"https://api.github.com/repos/{UPDATE_REPO}/git/blobs/{blob}", timeout=15)
            data = base64.b64decode(json.loads(response)["content"])
            if not matches(data, blob):
                raise ValueError(f"Не совпала контрольная сумма {name}")
        with tempfile.NamedTemporaryFile(dir=cache, delete=False) as tmp:
            tmp.write(data)
        try:
            os.replace(tmp.name, dest)
        finally:
            Path(tmp.name).unlink(missing_ok=True)
    return str(cache)


def version_tuple(text):
    """'5.6.0 (описание)' -> (5, 6, 0)"""
    import re as _re
    m = _re.match(r"\s*(\d+(?:\.\d+)*)", str(text))
    return tuple(int(x) for x in m.group(1).split(".")) if m else (0,)


def _http_get(url, timeout=8, accept=None):
    import urllib.request
    headers = {"User-Agent": "TWD-Farm-updater", "Cache-Control": "no-cache"}
    if accept:
        headers["Accept"] = accept
    req = urllib.request.Request(url + f"?t={int(time.time())}", headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def update_base(branch="main"):
    """Адрес файлов последнего коммита ветки. По имени ветки GitHub отдаёт файлы из кэша ещё минут пять после
    выкладки, поэтому сначала узнаю номер последнего коммита и беру файлы именно из него."""
    try:
        sha = _http_get(f"https://api.github.com/repos/{UPDATE_REPO}/commits/{branch}", timeout=6,
                        accept="application/vnd.github.sha").decode("ascii").strip()
        if len(sha) == 40 and all(c in "0123456789abcdef" for c in sha):
            return f"https://raw.githubusercontent.com/{UPDATE_REPO}/{sha}/"
    except Exception:
        pass
    return f"https://raw.githubusercontent.com/{UPDATE_REPO}/{branch}/"


def self_update(quiet=False):
    """Сверить версию с репозиторием и, если там новее, заменить свой файл.
    -> номер новой версии (нужен перезапуск) или None. Любая ошибка - просто работаем дальше на старой."""
    global _update_checked
    _update_checked = time.time()
    if not SETTINGS.get("auto_update", True):
        return None
    try:
        base = update_base()
        info = json.loads(_http_get(base + "version.json").decode("utf-8-sig"))
        new = str(info.get("version", ""))
        if version_tuple(new) <= version_tuple(VERSION):
            if not quiet:
                log(f"обновлений нет (версия {VERSION.split()[0]} - последняя)")
            return None
        log(f"на GitHub есть версия {new} (сейчас {VERSION.split()[0]}) - скачиваю"
            + (f": {info.get('notes')}" if info.get("notes") else ""))
        data = _http_get(base + str(info.get("file", "twd_bot.py")), timeout=30)
        import hashlib
        digest = hashlib.sha256(data).hexdigest()
        if info.get("sha256") and digest != str(info["sha256"]).lower():
            log("  обновление не установлено: файл скачался не полностью (не сошлась контрольная сумма)")
            return None
        text = data.decode("utf-8")
        compile(text, "twd_bot.py", "exec")                     # битый файл не ставим
        if version_tuple(text.split('VERSION = "', 1)[1].split('"', 1)[0]) <= version_tuple(VERSION):
            log("  обновление не установлено: в скачанном файле версия не новее текущей")
            return None
        me = os.path.abspath(__file__)
        try:                                                      # прошлая версия остаётся рядом - на случай отката
            with open(me, "rb") as f:
                old = f.read()
            with open(os.path.join(HERE, "twd_bot_prev.py"), "wb") as f:
                f.write(old)
        except OSError:
            pass
        tmp = me + ".new"
        with open(tmp, "wb") as f:
            f.write(data)
        os.replace(tmp, me)
        log(f"  установлена версия {new}; прошлая сохранена как twd_bot_prev.py")
        return new
    except Exception as e:
        if not quiet:
            log(f"проверить обновление не получилось ({type(e).__name__}: {e}) - работаю на текущей версии")
        return None


def restart_app(resume=False):
    """Перезапустить приложение (после обновления). resume - сразу продолжить фарм."""
    args = [a for a in sys.argv[1:] if a != "--resume"] + (["--resume"] if resume else [])
    try:
        save_settings()
    except Exception:
        pass
    try:
        subprocess.Popen([sys.executable, os.path.abspath(__file__)] + args, cwd=HERE)
    except Exception as e:
        log(f"не получилось перезапуститься после обновления: {e}. Закрой и открой приложение вручную.")
        return
    os._exit(0)


def settings_path():
    return os.path.join(HERE, "settings.json")


def load_settings():
    SETTINGS.update(DEFAULT_SETTINGS)
    try:
        with open(settings_path(), encoding="utf-8-sig") as f:
            SETTINGS.update(json.load(f))
    except Exception:
        # перенос из старого discord.json
        try:
            with open(os.path.join(HERE, "discord.json"), encoding="utf-8-sig") as f:
                old = json.load(f)
            tok = str(old.get("token", ""))
            if tok and "ТОКЕН" not in tok:
                SETTINGS.update(discord_enabled=True, discord_token=tok,
                                discord_channel=str(old.get("channel_id", "")),
                                discord_allowed=",".join(str(x) for x in old.get("allowed_user_ids", [])),
                                discord_ping=str(old.get("ping_user_id", "")))
        except Exception:
            pass
    STATS.total_matches = int(SETTINGS.get("total_matches", 0) or 0)
    apply_settings()


def save_settings():
    SETTINGS["total_matches"] = STATS.total_matches
    try:
        with open(settings_path(), "w", encoding="utf-8") as f:
            json.dump(SETTINGS, f, ensure_ascii=False, indent=2)
    except OSError as e:
        log(f"не удалось сохранить настройки: {e}")


def apply_settings():
    global FOCUS_AFTER, MOVE_TO_PRIMARY, PRIVATE_ONLY, SERVER_LINK, SERVER_DEEPLINK
    link = str(SETTINGS.get("server_link", "") or "").strip()
    SERVER_LINK, SERVER_DEEPLINK = "", ""
    if link:
        import re as _re
        m = _re.search(r"code=([0-9A-Za-z]+)", link)
        if m:
            SERVER_LINK = f"https://www.roblox.com/share?code={m.group(1)}&type=Server"
            SERVER_DEEPLINK = f"roblox://navigation/share_links?code={m.group(1)}&type=Server"
        elif link.startswith(("http://", "https://", "roblox://")):
            SERVER_LINK = SERVER_DEEPLINK = link
    try:
        FOCUS_AFTER = max(1, int(SETTINGS.get("focus_after", 3)))
    except (TypeError, ValueError):
        FOCUS_AFTER = 3
    MOVE_TO_PRIMARY = bool(SETTINGS.get("move_to_primary", True))
    PRIVATE_ONLY = bool(SETTINGS.get("private_only", True))


UNIT_TITLES = {"gtv": "📺 ТВ-сторож", "tv": "📺 ТВ", "sp": "🔊 Спикер", "sup": "🪠 Поддержка", "pl": "🪠 Плунжер", "farm": "💰 Ферма",
               "tcam": "🎥 Титан-Камкордер", "tspk": "📢 Титан-Амплифаер"}


MAIN_TITAN = "tcam"          # главный титан этого матча (имя юнита tcam): "tcam" или "ttv"
SECOND_TITAN = "tspk"        # второй титан (имя юнита tspk): "tspk" или "tcam"


def unit_title(name):
    if name.startswith("tcam") and MAIN_TITAN == "ttv":
        return "📺 Титан-Скрин" + name[4:]
    if name.startswith("tspk") and SECOND_TITAN == "tcam":
        return "🎥 Титан-Камкордер" + name[4:]
    for pre in sorted(UNIT_TITLES, key=len, reverse=True):
        if name.startswith(pre):
            num = name[len(pre):]
            return UNIT_TITLES[pre] + (f" {num}" if num else "")
    return name


def report(title, desc="", color=None, image=None):
    """Подробный отчёт в Discord (если включён)."""
    if SETTINGS.get("notify_actions", True):
        LINK.send(title, desc, COLOR_INFO if color is None else color, image)


def grab_game_window():
    """Скриншот окна Roblox (или всего экрана, если окна нет)."""
    try:
        rect = window_rect(find_game_window())
        if rect:
            try:
                return ImageGrab.grab(bbox=rect, all_screens=True)
            except TypeError:
                return ImageGrab.grab(bbox=rect)
        return ImageGrab.grab(all_screens=True)
    except Exception:
        return None


# ---------- Discord: уведомления + слэш-команды ----------
# Слэш-команды приходят через Gateway (веб-сокет), поэтому нужен пакет websocket-client.
# Особые права (intents) не нужны. Бота приглашают со scope "bot" + "applications.commands".

DISCORD_API = "https://discord.com/api/v10"
DISCORD_GATEWAY = "wss://gateway.discord.gg/?v=10&encoding=json"
COLOR_OK, COLOR_INFO, COLOR_WARN, COLOR_BAD = 0x3DDC84, 0x5865F2, 0xF5B942, 0xED4245

SLASH_COMMANDS = [
    {"name": "status", "description": "Состояние фарма: матчи, время, деньги, текущий шаг"},
    {"name": "screen", "description": "Скриншот окна Roblox"},
    {"name": "log", "description": "Последние строки лога",
     "options": [{"type": 4, "name": "lines", "description": "Сколько строк (1-40)",
                  "required": False, "min_value": 1, "max_value": 40}]},
    {"name": "mode", "description": "Выбрать режим фарма (со следующего матча)",
     "options": [{"type": 3, "name": "mode", "description": "Режим", "required": True,
                  "choices": [{"name": "HARD", "value": "hard"}, {"name": "NIGHTMARE", "value": "nightmare"}]}]},
    {"name": "stock", "description": "Сток Research Shop: показать и изменить настройки автоскупа",
     "options": [
         {"type": 3, "name": "check", "description": "Проверять сток", "required": False,
          "choices": [{"name": "включить", "value": "on"}, {"name": "выключить", "value": "off"},
                      {"name": "проверить при первой возможности", "value": "now"}]},
         {"type": 3, "name": "buy", "description": "Покупать: номера или названия через запятую, либо all",
          "required": False},
         {"type": 3, "name": "skip", "description": "Не покупать: номера или названия через запятую, либо all",
          "required": False},
         {"type": 4, "name": "min_tokens", "description": "Сколько жетонов оставлять", "required": False,
          "min_value": 0},
         {"type": 5, "name": "sell_trash", "description": "Сдавать образцы перед покупкой", "required": False},
         {"type": 5, "name": "buy_new", "description": "Покупать новые (незнакомые) предметы", "required": False},
     ]},
    {"name": "start", "description": "Запустить фарм"},
    {"name": "stop", "description": "Остановить фарм"},
]


def _fmt_dur(sec):
    sec = int(sec or 0)
    h, m = sec // 3600, sec % 3600 // 60
    return f"{h} ч {m} мин" if h else f"{m} мин"


class NullLink:
    ok = False

    def send(self, *a, **k):
        pass

    def stop(self):
        pass


class DiscordLink:
    def __init__(self, app):
        self.app = app                       # контроллер приложения (start/stop фарма)
        self.token = str(SETTINGS.get("discord_token", "")).strip()
        self.channel = str(SETTINGS.get("discord_channel", "")).strip()
        self.allowed = {x.strip() for x in str(SETTINGS.get("discord_allowed", "")).replace(";", ",").split(",")
                        if x.strip()}
        self.ping = str(SETTINGS.get("discord_ping", "")).strip()
        self.app_id = None
        self.queue = collections.deque()
        self.wake = threading.Event()
        self.alive = True
        self.ok = False
        self.status = "не подключён"
        self.ws = None

    # --- HTTP ---
    def _request(self, method, path, body=None, ctype="application/json", auth=True):
        import urllib.request
        import urllib.error
        for _ in range(4):
            headers = {"User-Agent": "DiscordBot (https://roblox.com, 1.0) TWDFarm", "Content-Type": ctype}
            if auth:
                headers["Authorization"] = "Bot " + self.token
            req = urllib.request.Request(DISCORD_API + path, data=body, method=method, headers=headers)
            try:
                with urllib.request.urlopen(req, timeout=20) as r:
                    data = r.read()
                    return json.loads(data) if data else None
            except urllib.error.HTTPError as e:
                if e.code == 429:
                    try:
                        wait = float(json.loads(e.read()).get("retry_after", 2))
                    except Exception:
                        wait = 2
                    time.sleep(min(wait, 30) + 0.2)
                    continue
                txt = e.read()[:300].decode("utf-8", "replace")
                raise RuntimeError(f"HTTP {e.code}: {txt}")
        raise RuntimeError("слишком много запросов")

    @staticmethod
    def _multipart(payload, image):
        import io
        buf = io.BytesIO()
        img = image.convert("RGB")
        if img.width > 1920:
            img = img.resize((1920, round(img.height * 1920 / img.width)))
        img.save(buf, "JPEG", quality=82)
        boundary = "----twdfarm" + str(int(time.time() * 1000))
        body = b"".join([
            f"--{boundary}\r\nContent-Disposition: form-data; name=\"payload_json\"\r\n"
            f"Content-Type: application/json\r\n\r\n{json.dumps(payload)}\r\n".encode(),
            f"--{boundary}\r\nContent-Disposition: form-data; name=\"files[0]\"; filename=\"screen.jpg\"\r\n"
            f"Content-Type: image/jpeg\r\n\r\n".encode() + buf.getvalue() + b"\r\n",
            f"--{boundary}--\r\n".encode(),
        ])
        return body, "multipart/form-data; boundary=" + boundary

    @staticmethod
    def embed(title, desc="", color=COLOR_INFO, fields=None, image=False):
        e = {"title": title, "description": desc, "color": color,
             "footer": {"text": f"TWD Farm {VERSION.split()[0]}"},
             "timestamp": time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime()) + "Z"}
        if fields:
            e["fields"] = [{"name": n, "value": v, "inline": True} for n, v in fields]
        if image:
            e["image"] = {"url": "attachment://screen.jpg"}
        return e

    def _post(self, path, payload, image=None, auth=True):
        if image is None:
            return self._request("POST", path, json.dumps(payload).encode(), auth=auth)
        if payload.get("embeds"):
            payload["embeds"][0]["image"] = {"url": "attachment://screen.jpg"}
        body, ctype = self._multipart(payload, image)
        return self._request("POST", path, body, ctype, auth=auth)

    # --- уведомления ---
    def send(self, title, desc="", color=COLOR_INFO, image=None, ping=False, fields=None):
        if not self.ok:
            return
        content = f"<@{self.ping}>" if ping and self.ping else ""
        self.queue.append(({"content": content, "embeds": [self.embed(title, desc, color, fields)]}, image))
        self.wake.set()

    def afk_prompt(self, key, panel):
        if self.ok:
            buttons = [{"type": 2, "style": 1, "label": str(i+1), "custom_id": f"afk:{key}:{i}"} for i in range(4)]
            mention = f"<@{self.ping}> " if self.ping else ""
            self.queue.append(({"content": mention + "AFK CHECK — выбери позицию слева направо",
                                "components": [{"type": 1, "components": buttons}]}, panel))
            self.wake.set()

    def stats_fields(self):
        up = time.time() - STATS.started_at if STATS.started_at else 0
        f = [("Состояние", {"idle": "⏸ остановлен", "waiting": "⏳ лобби / загрузка", "running": "▶ фармит",
                             "stock": "🛒 проверяет сток",
                             "stopping": "⏹ останавливается"}.get(STATS.state, STATS.state)),
             ("Режим", MODES[mode_key()]["title"]),
             ("Матчей", f"{STATS.matches} (всего {STATS.total_matches})"),
             ("Работает", _fmt_dur(up) if STATS.started_at else "—")]
        if STATS.match_started:
            f.append(("Текущий матч", _fmt_dur(time.time() - STATS.match_started)))
        if STATS.step_total:
            f.append(("Шаг плана", f"{STATS.step}/{STATS.step_total} · {STATS.step_text}"))
        if STATS.money is not None:
            f.append(("Деньги", f"${STATS.money:,}"))
        return f

    # --- запуск ---
    def start(self):
        threading.Thread(target=self._run, daemon=True).start()

    def stop(self):
        self.alive = False
        self.wake.set()
        try:
            if self.ws:
                self.ws.close()
        except Exception:
            pass

    def _run(self):
        try:
            me = self._request("GET", "/oauth2/applications/@me")
            self.app_id = me["id"]
            ch = self._request("GET", f"/channels/{self.channel}")
            guild = ch.get("guild_id")
            if guild:      # команды сервера появляются сразу (глобальные - до часа)
                self._request("PUT", f"/applications/{self.app_id}/guilds/{guild}/commands",
                              json.dumps(SLASH_COMMANDS).encode())
            else:
                self._request("PUT", f"/applications/{self.app_id}/commands", json.dumps(SLASH_COMMANDS).encode())
            self.ok = True
            self.status = f"подключён: {me.get('name', '?')}"
            log(f"Discord: {self.status}, канал #{ch.get('name', self.channel)}")
        except Exception as e:
            self.status = f"ошибка: {e}"
            log(f"Discord: не удалось подключиться ({e})")
            return
        threading.Thread(target=self._sender, daemon=True).start()
        self._gateway_loop()

    def _sender(self):
        while self.alive:
            self.wake.wait(timeout=1.0)
            self.wake.clear()
            while self.queue:
                payload, image = self.queue.popleft()
                try:
                    self._post(f"/channels/{self.channel}/messages", payload, image)
                except Exception as e:
                    log(f"Discord: сообщение не отправилось ({e})")

    # --- Gateway: только чтобы получать слэш-команды ---
    def _gateway_loop(self):
        try:
            import websocket          # пакет websocket-client
        except ImportError:
            self.status += " (без слэш-команд: нет websocket-client)"
            log("Discord: пакет websocket-client не установлен - работают только уведомления")
            return
        while self.alive:
            try:
                self._gateway_session(websocket)
            except Exception as e:
                if self.alive:
                    log(f"Discord: соединение прервалось ({e}), переподключаюсь")
            if self.alive:
                time.sleep(5)

    def _gateway_session(self, websocket):
        ws = websocket.create_connection(DISCORD_GATEWAY, timeout=30)
        self.ws = ws
        hello = json.loads(ws.recv())
        interval = hello["d"]["heartbeat_interval"] / 1000.0
        seq = None
        ws.send(json.dumps({"op": 2, "d": {"token": self.token, "intents": 0,
                                           "properties": {"os": "windows", "browser": "twdfarm",
                                                          "device": "twdfarm"}}}))
        next_beat = time.time() + interval * 0.9
        ws.settimeout(1.0)
        while self.alive:
            if time.time() >= next_beat:
                ws.send(json.dumps({"op": 1, "d": seq}))
                next_beat = time.time() + interval
            try:
                raw = ws.recv()
            except websocket.WebSocketTimeoutException:
                continue
            if not raw:
                raise RuntimeError("сервер закрыл соединение")
            msg = json.loads(raw)
            if msg.get("s") is not None:
                seq = msg["s"]
            op = msg.get("op")
            if op == 1:
                ws.send(json.dumps({"op": 1, "d": seq}))
            elif op in (7, 9):
                raise RuntimeError("Discord попросил переподключиться")
            elif op == 0 and msg.get("t") == "INTERACTION_CREATE":
                threading.Thread(target=self._interaction, args=(msg["d"],), daemon=True).start()
        ws.close()

    def _reply(self, it, payload, image=None, deferred=False):
        if deferred:
            self._post(f"/webhooks/{self.app_id}/{it['token']}", payload, image, auth=False)
        elif image is None:
            self._post(f"/interactions/{it['id']}/{it['token']}/callback", {"type": 4, "data": payload}, auth=False)
        else:
            self._request("POST", f"/interactions/{it['id']}/{it['token']}/callback",
                          json.dumps({"type": 5}).encode(), auth=False)
            self._post(f"/webhooks/{self.app_id}/{it['token']}", payload, image, auth=False)

    def _interaction(self, it):
        try:
            data = it.get("data", {})
            name = data.get("name")
            user = (it.get("member") or {}).get("user") or it.get("user") or {}
            if self.allowed and str(user.get("id")) not in self.allowed:
                self._reply(it, {"content": "Нет доступа к этому боту.", "flags": 64})
                return
            if it.get("type") == 3 and data.get("custom_id", "").startswith("afk:"):
                _, key, index = data["custom_id"].split(":")
                bot = self.app.bot
                valid = (str(it.get("channel_id")) == str(self.channel) and bot
                         and key == getattr(bot, "afk_id", None) and index in ("0","1","2","3"))
                if valid:
                    bot.afk_answer = (key, int(index))
                self._reply(it, {"content": f"Выбрана кнопка {int(index)+1}. Ответ передан макросу." if valid else "Проверка завершена", "flags": 64})
                return
            if name == "status":
                self._reply(it, {"embeds": [self.embed("Состояние фарма", "", COLOR_INFO, self.stats_fields())]})
            elif name == "screen":
                img = grab_game_window()
                if img is None:
                    self._reply(it, {"content": "Не получилось снять экран."})
                else:
                    self._reply(it, {"embeds": [self.embed("Скриншот Roblox", "", COLOR_INFO)]}, img)
            elif name == "log":
                n = 15
                for o in data.get("options", []) or []:
                    if o.get("name") == "lines":
                        n = int(o.get("value", 15))
                body = "\n".join(list(_log_tail)[-n:]) or "(пусто)"
                self._reply(it, {"content": "```\n" + body[-1900:] + "\n```"})
            elif name == "mode":
                val = next((o.get("value") for o in data.get("options", []) or [] if o.get("name") == "mode"), "")
                if val in MODES:
                    SETTINGS["mode"] = val
                    save_settings()
                    self._reply(it, {"embeds": [self.embed(f"Режим: {MODES[val]['title']}",
                                                           "Применится со следующего матча.", COLOR_OK)]})
                else:
                    self._reply(it, {"content": "Неизвестный режим."})
            elif name == "stock":
                opts = {o.get("name"): o.get("value") for o in data.get("options", []) or []}
                notes = []
                if opts.get("check") in ("on", "off"):
                    SETTINGS["stock_enabled"] = opts["check"] == "on"
                elif opts.get("check") == "now":
                    SETTINGS["stock_last"] = ""
                    notes.append("Сток проверю перед следующим матчем" if SETTINGS.get("stock_enabled")
                                 else "Проверка стока выключена - включи её: /stock check:включить")
                if "min_tokens" in opts:
                    SETTINGS["stock_min_tokens"] = max(0, int(opts["min_tokens"]))
                for opt, key in (("sell_trash", "stock_sell_trash"), ("buy_new", "stock_buy_new")):
                    if opt in opts:
                        SETTINGS[key] = bool(opts[opt])
                items = stock_items()
                for opt, flag in (("skip", False), ("buy", True)):
                    if opts.get(opt):
                        keys = stock_find(opts[opt])
                        for k in keys:
                            items[k]["buy"] = flag
                        if not keys:
                            notes.append(f"Не нашёл предмет «{opts[opt]}» - укажи номер из списка или часть названия")
                if opts:
                    save_settings()
                    try:
                        self.app.root.after(0, self.app.sync_stock_vars)
                    except Exception:
                        pass
                if SETTINGS.get("stock_enabled") and not SERVER_LINK:
                    notes.append("Не задана ссылка приватного сервера - без неё бот в хаб не зайдёт")
                desc = stock_summary() + ("\n\n" + "\n".join(notes) if notes else "")
                self._reply(it, {"embeds": [self.embed("🛒 Сток: настройки" + (" изменены" if opts else ""),
                                                       desc[:3900], COLOR_OK if opts else COLOR_INFO)]})
            elif name == "start":
                ok = self.app.start_farm()
                self._reply(it, {"embeds": [self.embed("▶ Фарм запущен" if ok else "Фарм уже идёт", "",
                                                       COLOR_OK if ok else COLOR_WARN)]})
            elif name == "stop":
                ok = self.app.stop_farm()
                self._reply(it, {"embeds": [self.embed("⏹ Останавливаю фарм" if ok else "Фарм и так остановлен",
                                                       "", COLOR_WARN)]})
        except Exception as e:
            log(f"Discord: ошибка команды ({e})")


LINK = NullLink()



AFK_HEADER = np.frombuffer(bytes.fromhex("2c2b1b1b25171d1d1d1b21281e1c1a2020211b1c231c1b1c211e252d291c6a6e239e987b65832f19789d7c505f4e9897378a917858801f292624ccca38de7287fb8c0f4dbb3691cac973dc8f86a436adf4621f2b1c62dedc85d56d82d9b4253ec174a5aeb574e09c74b270b6d29d1d2a1a493c3b594f0d3f3a5731164b7052384037696e255a66522f642022201617181414201715151a2018121518181a13121e1614161a142024"), dtype=np.uint8)

def afk_panel(img):
    gray = img.convert("L")
    edges = np.diff(np.asarray(gray) > 150, axis=1, prepend=False, append=False)
    ys, xs = np.nonzero(edges)
    widths = xs[1::2] - xs[::2]
    for i in np.flatnonzero((widths >= 115) & (widths <= 900)):
        x, y = int(xs[2*i]), int(ys[2*i])
        scale = widths[i] / 239
        def crop(a,b,c,d):
            return gray.crop((x+round(a*scale), y+round(b*scale),
                              x+round(c*scale), y+round(d*scale)))
        title = np.asarray(crop(8,9,64,20).resize((28,6))).ravel()
        if title.std() < 18 or np.corrcoef(title, AFK_HEADER)[0,1] < .75:
            continue
        def digits(box):
            mask = crop(*box).point(lambda v: 255 if v > 160 else 0)
            return np.asarray(mask.crop(mask.getbbox()).resize((32,20))) > 127
        target = digits((22,49,65,70))
        centers = (98,132,166,200)
        options = [digits((c-12,55,c+12,70)) for c in centers]
        scores = [np.count_nonzero(target & o)/max(1,np.count_nonzero(target | o)) for o in options]
        second, best = np.argsort(scores)[-2:]
        choice = best if scores[best] > .68 and scores[best]-scores[second] > .10 else None
        points = [((x+c*scale)/img.width,(y+62*scale)/img.height) for c in centers]
        signature = tuple(np.packbits(o).tobytes() for o in [target]+options)
        return crop(0,0,242,112), points, signature, choice

class Bot:
    def __init__(self, use_speed=True, hotkeys=True):
        self.m = mouse.Controller()
        self.k = keyboard.Controller()
        self.abort = threading.Event()
        self.start = threading.Event()
        self.hwnd = None
        self.use_speed = use_speed
        self.units = {}            # имя -> точка (доли окна)
        self.levels = {}           # имя -> уровень
        self.types = {}            # имя -> тип юнита (ключ UNITS)
        self.slots = {}            # тип -> номер слота
        self.boss_t0, self.boss_done, self.boss_hits, self.boss_upgrade, self.in_boss = None, set(), 0, None, False
        self.angle, self.shift = 0.0, (0, 0)
        self.scale = 1.0
        self.px_per_deg = TURN_PX_PER_DEG
        self.turn_known = False
        try:
            saved = float(SETTINGS.get("turn_px_per_deg") or 0)
            if 0.3 < abs(saved) < 90:
                self.px_per_deg, self.turn_known = saved, True
        except (TypeError, ValueError):
            pass
        self.lag = 0.2                 # как быстро игра отвечает на клик (уточняется на ходу)
        self.holding = None        # какой слот сейчас "в руке" (подсвечена дорожка)
        self.ready_pending = False # READY ещё не нажат
        self.away_since = None
        self.link_opened = 0.0
        self.moved_at = -1e9
        self.in_private = False   # True - сейчас в лобби, куда зашли по ссылке приватки
        self.listener = None
        if hotkeys:
            self.listener = keyboard.Listener(on_press=self._on_key)
            self.listener.start()

    def _on_key(self, key):
        if key == ABORT_KEY:
            self.abort.set()
        elif key == START_KEY:
            self.start.set()

    # --- базовые действия ---

    def check(self):
        if self.abort.is_set():
            raise Aborted
        told = False
        since = time.perf_counter()
        while not is_game_window(foreground_window()):
            if self.abort.is_set():
                raise Aborted
            if not told:
                log("окно Roblox не активно - жду")
                told = True
            game = find_game_window()
            waited = time.perf_counter() - since
            if game and waited > FOCUS_AFTER:
                log("окно Roblox есть, но не активно - кликаю по нему")
                bring_to_front(game, IDLE_POINT)
                since = time.perf_counter()
            elif not game and waited > 5 and SERVER_LINK and time.perf_counter() - self.link_opened > 120:
                log("Roblox не запущен (вылетел или закрыт) - захожу на приватный сервер")
                self.crashed = True
                open_private_link()
                self.in_private = True
                self.link_opened = time.perf_counter()
            time.sleep(0.3)
        if sys.platform == "win32":
            self.hwnd = foreground_window()
            if MOVE_TO_PRIMARY and time.perf_counter() - self.moved_at > 60:
                self.moved_at = time.perf_counter()
                if move_to_primary(self.hwnd):
                    log("окно Roblox было на втором мониторе - перенёс на основной")
            if time.perf_counter() - getattr(self, "res_at", -1e9) > 20:
                # после tscon (отключения RDP) Windows сбрасывает разрешение - возвращаем нужное
                self.res_at = time.perf_counter()
                apply_resolution()
            if SETTINGS.get("roblox_fullscreen", True) and time.perf_counter() - getattr(self, "fs_at", -1e9) > 60:
                self.fs_at = time.perf_counter()
                ensure_fullscreen(self.hwnd, self.k)
        if getattr(self, "crashed", False):
            self.crashed = False
            if STATS.match_started:               # игра вылетела посреди матча - этот матч уже не продолжить
                log("Roblox был перезапущен посреди матча - начинаю заново")
                self.bar_missing = 0
                raise MatchEnded
        if time.monotonic() >= getattr(self, "afk_next", 0):
            self.afk_next = time.monotonic() + 3
            self.handle_afk()
        self.timelapse()
        self.check_disconnect()
        if getattr(self, "bar_missing", 0) >= 3 and STATS.match_started:
            # 45 с на экране нет полосы здоровья базы: матч кончился, а итоговый экран не узнан
            # (его закрыло окно награды или игра уже вернула в лобби). Без этого бот ждал бы денег вечно.
            self.bar_missing = 0
            log("полосы здоровья базы нет уже 45 с - матч закончился (окно награды или лобби)")
            raise MatchEnded

    def handle_afk(self):
        stamp, bounds, cached = getattr(self, "afk_capture", (0, None, None))
        fresh = time.monotonic() - stamp < .2 and bounds == self.rect()
        frame = afk_panel(cached if fresh else self.grab())
        previous = None
        misses = 0
        focus_retry = 0
        try:
            while frame or (previous is not None and misses < 4):
                if not is_game_window(foreground_window()):
                    if getattr(self, "afk_answer", None) and time.monotonic() >= focus_retry:
                        focus_retry = time.monotonic() + 3
                        bring_to_front(self.hwnd, IDLE_POINT)
                    self.sleep(.25)
                    frame = None
                    continue
                if frame is None:
                    self.sleep(.25)
                    frame = afk_panel(self.grab())
                    misses = 0 if frame else misses + 1
                    continue
                misses = 0
                panel, points, signature, automatic = frame
                # Small changes in antialiasing should not invalidate Discord buttons.
                if previous is None or any(
                    sum(bin(a ^ b).count("1") for a, b in zip(old, new)) > 64
                    for old, new in zip(previous, signature)
                ):
                    previous = signature
                    clicked = False
                    handled_answer = None
                    self.afk_answer = None
                    self.afk_id = str(time.monotonic_ns())
                    if isinstance(LINK, DiscordLink):
                        LINK.afk_prompt(self.afk_id, panel)
                answer = self.afk_answer
                choice = automatic if SETTINGS.get("afk_auto") else None
                if answer and answer[0] == self.afk_id:
                    choice = answer[1]
                if choice is not None and (not clicked or answer is not handled_answer):
                    self.m.position = self.to_screen(points[choice])
                    self.sleep(.03)
                    relative_move(self.m, 1, 0)
                    relative_move(self.m, -1, 0)
                    self.sleep(.15)
                    if is_game_window(foreground_window()):
                        self.m.press(mouse.Button.left)
                        try:
                            time.sleep(.12)
                        finally:
                            self.m.release(mouse.Button.left)
                        log(f'AFK CHECK: нажата кнопка {choice + 1}')
                        clicked = True
                        handled_answer = answer
                self.sleep(.5)
                frame = afk_panel(self.grab())
        finally:
            self.afk_id = None

    def relaunch_private(self):
        """Закрыть Roblox и зайти заново по ссылке приватного сервера. Ждёт ~25 с, пока клиент запустится."""
        close_roblox()
        for wait, act in ((6, open_private_link), (25, None)):
            t_end = time.perf_counter() + wait
            while time.perf_counter() < t_end:
                if self.abort.is_set():
                    raise Aborted
                time.sleep(0.2)
            if act:
                act()
                self.in_private = True
                self.link_opened = time.perf_counter()
        self.holding = None
        self.selected = None

    def check_disconnect(self):
        """Раз в 3 с: не выкинуло ли из игры - серое окно Roblox с ошибкой (Disconnected, Connection Failed,
        кик). Если задан приватный сервер - сразу закрываю Roblox и захожу на него заново; иначе жму
        белую кнопку окна (Reconnect / Retry). Текущий матч считается законченным."""
        now = time.perf_counter()
        if getattr(self, "in_dc", False) or now - getattr(self, "dc_at", 0.0) < 3:
            return
        self.dc_at = now
        try:
            shot = self.grab()
            pt = disconnect_dialog(shot)
        except Exception:
            return
        if not pt:
            return
        self.in_dc = True
        try:
            self.holding = None
            if SERVER_LINK:
                log("Roblox выкинул из игры (окно с ошибкой) - перезапускаю его на приватном сервере")
                try:
                    LINK.send("Вылет из игры", "Roblox показал окно с ошибкой - закрываю его и захожу на "
                              "приватный сервер заново.", COLOR_WARN, grab_game_window())
                except Exception:
                    pass
                self.relaunch_private()
            else:
                log("Roblox выкинул из игры (окно с ошибкой) - нажимаю кнопку переподключения")
                x, y = self.to_screen(pt)
                self.m.position = (x, y)
                time.sleep(0.15)
                self.m.press(mouse.Button.left)
                time.sleep(0.12)
                self.m.release(mouse.Button.left)
                time.sleep(8)
                self.in_private = False
            self.dc_at = time.perf_counter() + 7       # следующая проверка - через 10 с
        finally:
            self.in_dc = False
        if STATS.match_started:
            self.bar_missing = 0
            raise MatchEnded

    def sleep(self, seconds):
        end = time.perf_counter() + seconds
        while time.perf_counter() < end:
            if self.abort.is_set():
                raise Aborted
            time.sleep(min(0.05, max(0.0, end - time.perf_counter())))

    def rect(self):
        rect = window_rect(self.hwnd)
        if rect is None:
            w, h = ImageGrab.grab().size
            rect = (0, 0, w, h)
        return rect

    def grab(self, box=(0, 0, 1, 1)):
        l, t, r, b = self.rect()
        w, h = r - l, b - t
        bbox = (int(l + box[0] * w), int(t + box[1] * h), int(l + box[2] * w), int(t + box[3] * h))
        try:
            img = ImageGrab.grab(bbox=bbox, all_screens=True)
        except TypeError:
            img = ImageGrab.grab(bbox=bbox)

        if box == (0, 0, 1, 1):
            self.afk_capture = (time.monotonic(), bbox, img)
        return img

    def to_screen(self, pt):
        l, t, r, b = self.rect()
        return int(l + pt[0] * (r - l)), int(t + pt[1] * (b - t))

    def click(self, pt, dwell=0.15, button=mouse.Button.left):
        self.check()
        self.selected = None          # любой клик может снять выделение
        self.m.position = self.to_screen(pt)
        time.sleep(0.03)
        relative_move(self.m, 1, 0)
        relative_move(self.m, -1, 0)
        self.sleep(dwell)             # игре нужно время заметить курсор
        self.m.press(button)
        time.sleep(0.12)              # слишком короткое нажатие игра пропускает
        self.m.release(button)

    def hover(self, pt):
        self.check()
        self.m.position = self.to_screen(pt)
        time.sleep(0.03)
        relative_move(self.m, 1, 0)
        relative_move(self.m, -1, 0)

    @staticmethod
    def _vk(ch):
        """Клавиша по коду, а не по букве: так работает и на русской раскладке."""
        if isinstance(ch, str) and len(ch) == 1 and ch.isalnum():
            return keyboard.KeyCode.from_vk(ord(ch.upper()))
        return ch

    def key(self, ch):
        self.check()
        k = self._vk(ch)
        self.k.press(k)
        time.sleep(0.06)
        self.k.release(k)

    def hold_keys(self, chars, seconds):
        self.check()
        keys = [self._vk(c) for c in chars]
        for k in keys:
            self.k.press(k)
        try:
            self.sleep(seconds)
        finally:
            for k in keys:
                self.k.release(k)

    # --- что на экране ---

    def money(self):
        try:
            v = read_money_image(self.grab(MONEY_REGION))
            if v is not None:
                STATS.money = v
            return v
        except Exception:
            return None

    def end_screen(self):
        try:
            return is_end_image(self.grab(END_BOX))
        except Exception:
            return False

    def vote_point(self, mode=None):
        """Кнопка VOTE под карточкой нужной сложности: тёмная цветная карточка и такая же кнопка под ней
        (HARD - красная, NIGHTMARE - фиолетовая). Работает при любом размере окна. -> (x, y) или None."""
        mode = mode or mode_key()
        try:
            img = self.grab()
        except Exception:
            return None
        button = self.vote_button(img, mode)
        return (button["cx"], button["cy"]) if button else None

    @staticmethod
    def vote_button(img, mode):
        w, h = img.size
        a = np.asarray(img.convert("RGB").resize((LOBBY_W, max(1, round(LOBBY_W * h / w))), Image.BOX)).astype(np.int16)
        r, g, b = a[..., 0], a[..., 1], a[..., 2]
        if mode == "nightmare":
            # Wastelands: центр правой из двух карточек находится на 58.6% ширины окна.
            mask, lo, hi = (b > 30) & (b > 2 * g + 8) & (b > 1.25 * r + 4) & (r > g), 0.52, 0.95
        else:
            mask, lo, hi = (r > 35) & (r > 3 * g + 5) & (r > 3 * b + 5), 0.4, 0.75
        blobs = _blobs(mask)
        cards = [x for x in blobs if 0.08 <= x["w"] <= 0.2 and 0.35 <= x["h"] <= 0.7 and lo < x["cx"] < hi]
        for c in cards:
            for v in blobs:
                if (abs(v["cx"] - c["cx"]) < 0.02 and 0.03 <= v["h"] <= 0.1 and abs(v["w"] - c["w"]) < 0.04
                        and v["cy"] > c["cy"] + c["h"] / 2):
                    return v
        return None

    def vote_screen(self):
        try:
            if vote_diff(self.grab(VOTE_BOX)) < VOTE_MAX_DIFF:
                return True
        except Exception:
            pass
        return self.vote_point("hard") is not None or self.vote_point("nightmare") is not None

    def ready_visible(self):
        try:
            return is_ready_image(self.grab(READY_BOX))
        except Exception:
            return False

    def money_stable(self, tries=6):
        """Сумма, прочитанная два раза подряд одинаково (защита от ошибки чтения)."""
        prev = None
        for _ in range(tries):
            v = self.money()
            if v is not None and v == prev:
                return v
            prev = v
            self.sleep(0.08)
        return prev

    # --- деньги ---

    def wait_money(self, need, what):
        told = False
        last_seen = time.perf_counter()
        last_log = time.perf_counter()
        while True:
            self.check()
            self.boss_tick()
            v = self.money()
            if self.ready_pending and (v is None or v < need):
                self.press_ready()          # дальше денег без начала волн не будет
                continue
            if v is not None:
                last_seen = time.perf_counter()
                if v >= need:
                    v2 = self.money()
                    if v2 is not None and v2 >= need:
                        return v2
            if self.end_screen():
                raise MatchEnded
            if v is None and time.perf_counter() - last_seen > 2.5 and getattr(self, "nomoney_snaps", 0) < 4 \
                    and time.perf_counter() - getattr(self, "nomoney_at", 0) > 5:
                # сумма не читается уже 2.5 с - сохраняю область с деньгами без сжатия: по ней видно,
                # как цифры выглядят на этом компьютере и что мешает их прочитать
                self.nomoney_at = time.perf_counter()
                self.nomoney_snaps = getattr(self, "nomoney_snaps", 0) + 1
                try:
                    d = os.path.join(HERE, "debug")
                    os.makedirs(d, exist_ok=True)
                    self.grab(MONEY_REGION).convert("RGB").save(
                        os.path.join(d, f"nomoney_{self.nomoney_snaps}.png"))
                    log(f"  сумму денег не удаётся прочитать - снимок сохранён в debug\\nomoney_{self.nomoney_snaps}.png")
                except Exception:
                    pass
            if time.perf_counter() - last_seen > 6:
                # сумму не видно: награда "click anywhere" или конец матча
                if self.end_screen():
                    raise MatchEnded
                self.click(IDLE_POINT, dwell=0.1)
                last_seen = time.perf_counter()
            if not told:
                log(f"  жду ${need} на {what} (сейчас ${v})")
                told = True
            elif time.perf_counter() - last_log > 20:
                log(f"  ...всё ещё жду ${need} на {what}, сейчас " + (f"${v}" if v is not None else "сумму не видно"))
                last_log = time.perf_counter()
            self.sleep(0.25)

    def wait_change(self, before, sign, amount, timeout=1.6):
        """Ждать, пока деньги изменятся: sign=-1 уменьшатся на amount, +1 вырастут на amount."""
        end = time.perf_counter() + timeout
        while time.perf_counter() < end:
            v = self.money()
            if v is not None and before is not None:
                if sign < 0 and before - v >= amount:
                    return v
                if sign > 0 and v - before >= amount:
                    return v
            self.sleep(0.1)
        return None

    # --- камера ---

    def camera_top_down(self):
        self.check()
        self.hover((0.5, 0.45))
        self.m.press(mouse.Button.right)
        time.sleep(0.1)
        for _ in range(ALIGN_DRAG_PX // 50):
            relative_move(self.m, 0, 50)
            time.sleep(0.01)
        time.sleep(0.1)
        self.m.release(mouse.Button.right)
        time.sleep(0.1)
        for _ in range(ALIGN_SCROLL_STEPS):
            self.m.scroll(0, -1)
            time.sleep(0.02)
        self.sleep(0.8)

    def turn_camera(self, px):
        self.check()
        self.hover((0.5, 0.45))
        self.m.press(mouse.Button.right)
        time.sleep(0.1)
        left = abs(int(px))
        sign = 1 if px > 0 else -1
        while left > 0:
            part = min(4, left)
            relative_move(self.m, sign * part, 0)
            left -= part
            time.sleep(0.003)
        time.sleep(0.08)
        self.m.release(mouse.Button.right)
        self.sleep(0.5)

    def path_visible(self):
        return path_mask(self.grab()).mean() > 0.01

    def take(self, slot):
        """Взять юнита из слота в руку (клавиша слота работает как переключатель)."""
        if self.holding == slot and self.path_visible():
            return True
        for attempt in range(3):
            self.key(str(slot))
            self.sleep(0.45)
            if self.path_visible():
                self.holding = slot
                return True
        self.holding = None
        return False

    def drop(self):
        """Убрать юнита из руки, если он там."""
        if self.holding is not None and self.path_visible():
            self.key(str(self.holding))
            self.sleep(0.3)
        self.holding = None

    def see_path(self, slot):
        """Взять юнита в руку и вернуть (угол, сдвиг, оценка) дорожки."""
        if not self.take(slot):
            return None
        return estimate_rotation(path_mask(self.grab()))

    def align_to_path(self, slot):
        """Довернуть камеру так, чтобы дорожка совпала с эталоном. Сколько пикселей мыши приходится
        на градус, на разных компьютерах разное (и может отличаться в разы), поэтому сначала делается
        маленький пробный поворот, а большие повороты ограничены, чтобы не проскочить пол-оборота."""
        res = self.see_path(slot)
        if res is None:
            log("  дорожку не видно - ставлю в эталонные точки без поворота")
            self.angle, self.shift, self.scale = 0.0, (0, 0), 1.0
            return False
        ang, shift, score, scale = res
        log(f"  дорожка: поворот {ang:+.1f} град, масштаб {scale:.2f}, совпадение {score:.2f}")
        k = self.px_per_deg                     # модель: после поворота на px угол становится ang + px / k
        known = bool(getattr(self, "turn_known", False))
        bad = 0
        for _ in range(10):
            if abs(ang) <= YAW_TOLERANCE:
                break
            if not known:
                px = 40.0 if (-ang * k) > 0 else -40.0       # пробный поворот в нужную сторону
            else:
                px = max(-110.0, min(110.0, -ang)) * k        # не больше 110 градусов за раз
            self.turn_camera(px)
            res = self.see_path(slot)
            if res is None:
                break
            new_ang, shift, score, scale = res
            change = (new_ang - ang + 180) % 360 - 180
            if known:                           # из трёх вариантов (с оборотом туда-сюда) - ближайший к расчёту
                pred = px / k
                change = min((change - 360, change, change + 360), key=lambda c: abs(c - pred))
            if abs(change) > 1.2:
                k_new = px / change
                if 0.3 < abs(k_new) < 90:
                    k = k_new
                    known = True
            log(f"  повернул камеру на {px:.0f}px: теперь {new_ang:+.1f} град, совпадение {score:.2f}"
                f" ({abs(k):.1f} px на градус)")
            if known and abs(new_ang) > 0.6 * abs(ang) and abs(new_ang) > 8:
                bad += 1                        # поворот не приблизил к цели - чувствительность не та
                if bad >= 2:
                    known, bad = False, 0       # начинаю заново с пробного поворота
            ang = new_ang
        self.px_per_deg = k
        if known and not getattr(self, "turn_known", False):
            self.turn_known = True
            SETTINGS["turn_px_per_deg"] = round(k, 3)   # запоминаю для этого компьютера
            try:
                save_settings()
            except Exception:
                pass
        self.angle, self.shift, self.scale = ang, shift, scale
        if abs(ang) > 3:
            log(f"  ВНИМАНИЕ: камеру выровнять не удалось (осталось {ang:+.0f} град) - ставлю с поправкой на поворот")
        if score < 0.35:
            log("  ВНИМАНИЕ: дорожка похожа на эталон плохо, клики могут промахнуться")
        return True

    def point(self, name):
        return transform_point(POINTS[name], self.angle, self.shift, getattr(self, "scale", 1.0))

    # --- шаги плана ---

    def snap_to_road(self, pt, clear):
        """Подвинуть точку так, чтобы до края красной дорожки было ровно столько, сколько на эталоне
        (с учётом масштаба камеры). Юнит должен быть в руке - тогда дорожка подсвечена."""
        if not clear:
            return pt
        try:
            self.hover(IDLE_POINT)           # призрак юнита - наверх, в зону интерфейса
            self.sleep(0.25)
            img = self.grab()
        except Exception:
            return pt
        w, h = img.size
        W = 640
        H = max(1, round(W * h / w))
        a = np.asarray(img.convert("RGB").resize((W, H), Image.BILINEAR)).astype(np.int16)
        r, g, b = a[..., 0], a[..., 1], a[..., 2]
        m = (r > 110) & (r - g > 60) & (r - b > 55)
        for x0, y0, x1, y1 in HUD_BOXES:
            m[int(y0 * H):int(math.ceil(y1 * H)), int(x0 * W):int(math.ceil(x1 * W))] = False
        ys, xs = np.nonzero(m)
        if len(xs) < 200:
            return pt
        px, py = pt[0] * W, pt[1] * H
        d2 = (xs - px) ** 2 + (ys - py) ** 2
        i = int(np.argmin(d2))
        d = math.sqrt(float(d2[i]))
        want = clear * W * getattr(self, "scale", 1.0)
        if d < 0.5:                          # точка прямо на дороге - направление не понять
            return pt
        qx, qy = float(xs[i]), float(ys[i])
        nx, ny = qx + (px - qx) / d * want, qy + (py - qy) / d * want
        move = math.hypot(nx - px, ny - py)
        if move > 0.08 * W:                  # слишком далеко - скорее всего, ближайшая дорога не та
            log(f"  до дороги {d:.0f}px (нужно {want:.0f}) - слишком далеко, точку не двигаю")
            return pt
        if move > 1:
            log(f"  прижимаю к дороге: было {d:.0f}px до края, стало {want:.0f}px")
        return (nx / W, ny / H)

    def get_corner(self, key="c1"):
        """Вершина угла дорожки на экране (ищется один раз за матч, пока юнит в руке).
        key: "c1" - первый угол (кучка), "c3" - третий поворот (сторожа)."""
        corners = self.__dict__.setdefault("corners", {})
        tries = self.__dict__.get("corner_tries")
        if not isinstance(tries, dict):
            tries = self.corner_tries = {}
        c = corners.get(key)
        if c is not None and c.get("found"):
            return c
        ref, finder, n1, n2, title = {
            "c1": (CORNER_REF, find_corner, (-0.7268, 0.6869), (0.7174, 0.6966), "первый угол"),
            "c3": (CORNER3_REF, find_corner3, (-0.68, 0.73), (-0.78, -0.62), "третий поворот"),
        }[key]
        scale = getattr(self, "scale", 1.0)
        guess = transform_point(ref, self.angle, self.shift, scale)
        found = None
        if tries.get(key, 0) < 3 and abs(self.angle) <= 3:     # искатель рассчитан на эталонный поворот
            tries[key] = tries.get(key, 0) + 1
            try:
                self.hover(IDLE_POINT)           # призрак юнита - наверх, чтобы не закрывал угол
                self.sleep(0.25)
                found = finder(self.grab(), guess, scale)
            except Exception as e:
                log(f"  поиск угла дорожки: ошибка {e}")
        if found:
            log(f"  {title} дорожки найден: ширина дороги {found['w']:.0f}px, "
                f"поправка {found['v'][0] - guess[0] * 1456:+.0f},{found['v'][1] - guess[1] * found['h']:+.0f}px")
            c = found
        elif c is None:
            log(f"  {title} дорожки по подсветке не нашёл - считаю по эталону")
            t = math.radians(self.angle)

            def rot(x, y):
                return (x * math.cos(t) + y * math.sin(t), -x * math.sin(t) + y * math.cos(t))
            c = {"v": (guess[0] * 1456, guess[1] * 819), "a1": rot(*n1), "a2": rot(*n2),
                 "w": ROAD_W_REF * scale, "h": 819, "found": False}
        corners[key] = c
        if key == "c1":
            self.corner = c
        return c

    def candidates(self, at):
        """Куда пробовать ставить юнита: [(точка, пометка для журнала, что запомнить при успехе)]."""
        k = getattr(self, "scale", 1.0)
        offsets = TRY_OFFSETS_BIG if at in BIG_POINTS else TRY_OFFSETS
        out = []
        self._cand_uv = {}
        if at in CLUSTER or at in CLUSTER3 or at in CLUSTER_ABS or at in CLUSTER3_ABS:
            key = "c3" if (at in CLUSTER3 or at in CLUSTER3_ABS) else "c1"
            c = self.get_corner(key)
            target = None
            if at in CLUSTER_ABS or at in CLUSTER3_ABS:
                uv0 = CLUSTER_ABS[at] if at in CLUSTER_ABS else CLUSTER3_ABS[at]
                for g in CLUSTER_GROW:
                    target = corner_point(c, uv0, g)
                    out.append((target, f"дальше от угла x{g:.2f}" if g > 1 else "", None))
                    self._cand_uv[target] = (key, (uv0[0] * g, uv0[1] * g))
            else:
                i, j = CLUSTER[at] if at in CLUSTER else CLUSTER3[at]
                ke, ks = getattr(self, "cluster_edge", 1.0), getattr(self, "cluster_step", 1.0)
                if (i, j) == (0, 0):
                    variants = [(ke * g, ks, g) for g in GROW_EDGE]
                else:
                    variants = [(ke, ks * g, g) for g in GROW_STEP]
                for e, st, g in variants:
                    uv = (_C * e + i * _D * st, _C * e + j * _D * st)
                    target = corner_point(c, uv)
                    out.append((target, f"шаг кучки x{st:.2f}, отступ x{e:.2f}" if g > 1 else "", (e, st)))
                    self._cand_uv[target] = ("c3" if at in CLUSTER3 else "c1", uv)
            for dx, dy in offsets[1:]:
                out.append(((target[0] + dx * k / 1456.0, target[1] + dy * k / 819.0), f"сдвиг {dx},{dy}", None))
            return out
        target = self.snap_to_road(self.point(at), POINT_CLEARANCE.get(at))
        for n, (dx, dy) in enumerate(offsets):
            out.append(((target[0] + dx * k / 1456.0, target[1] + dy * k / 819.0),
                        f"сдвиг {dx},{dy}" if n else "", None))
        return out

    def step_slot(self, step):
        utype = step.get("type")
        if step.get("slot"):
            return step["slot"]
        return self.slots.get(utype)

    def place(self, step):
        name, utype = step["unit"], step.get("type")
        slot = self.step_slot(step)
        if not slot:
            log(f"  пропускаю {name}: юнит «{UNITS.get(utype, {}).get('title', utype)}» не найден на панели")
            return False
        cost = step.get("cost") or UNITS[utype]["price"]
        sell = step.get("sell_first") or []
        sell = [u for u in sell if u in self.units]
        if sell:
            value = step.get("sell_value")
            if value is None:
                value = sum(sell_value(self.types[u], self.levels.get(u, 0)) for u in sell if u in self.types)
            self.wait_money(max(0, cost - value) + step.get("margin", 150), f"{name} (после продажи {len(sell)} юнитов)")
            log(f"  продаю {', '.join(sell)} ради {name}")
            sold_all = True
            for u in sell:
                if not self.sell_unit(u):
                    sold_all = False
            if sold_all:
                # Денег теперь точно хватает: перед продажей было проверено, что с выручкой их достаточно.
                # Ставлю сразу, не дожидаясь, пока сумма на экране прочитается (на части компьютеров
                # она читается с задержкой, и титан вставал на 10 секунд позже, чем мог).
                step = dict(step, nowait=True)
        if not step.get("nowait"):               # nowait: деньги точно есть (только что продан титан),
            self.wait_money(cost, name)          # а сумму на экране в бою с боссом бывает не прочитать
        at = step["at"]
        cands = None
        i = 0
        quick_end = time.perf_counter() + step["quick"] if step.get("quick") else None
        while True:
            if quick_end and time.perf_counter() > quick_end:
                log(f"  {name} не встаёт уже {step['quick']} с - не трачу на него время")
                break
            if not self.take(slot):
                log(f"  не получается взять юнита из слота {slot}")
                break
            if cands is None:
                cands = self.candidates(at)          # юнит в руке - дорожка подсвечена
            if i >= len(cands):
                break
            pt, note, grow = cands[i]
            i += 1
            before = self.money_stable()
            self.click(pt)
            if self.placed_check(before, cost, timeout=1.1 if grow else 1.6):
                self.holding = None
                self.units[name] = pt
                uv = getattr(self, "_cand_uv", {}).get(pt)
                cl = self.__dict__.setdefault("cluster_uv", {})
                if uv:
                    cl[name] = uv                # место юнита относительно угла дорожки
                else:
                    cl.pop(name, None)
                if grow:
                    e, st = grow
                    if e > self.cluster_edge + 1e-6 or st > self.cluster_step + 1e-6:
                        log(f"  вплотную не встал: отступ от дороги x{e:.2f}, шаг между юнитами x{st:.2f} "
                            f"- дальше ставлю так же")
                    self.cluster_edge, self.cluster_step = max(self.cluster_edge, e), max(self.cluster_step, st)
                    self.tight.add(name)
                if utype == "farm":
                    self.tight.add(name)         # фермы стоят рядом - тоже сверяю выделение по кругу
                log(f"  поставил {name} (слот {slot}) за ${cost}" + (f", {note}" if note else ""))
                self.sleep(0.3)
                self.levels[name] = 0
                self.types[name] = utype
                self.__dict__.setdefault("want", {})[name] = 0
                if SETTINGS.get("notify_actions", True):
                    report(f"Поставил {unit_title(name)}", f"${cost:,} · шаг {STATS.step}/{STATS.step_total}",
                           COLOR_OK, self.grab())
                if step.get("priority"):
                    self.set_priority(name, step["priority"])
                return True
            if self.end_screen():
                raise MatchEnded
        self.snap(f"noplace_{name}")
        self.__dict__.setdefault("failed_place", {}).setdefault(name, dict(step))
        log(f"  НЕ удалось поставить {name}: все точки рядом заняты")
        if SETTINGS.get("notify_actions", True):
            report(f"Не получилось поставить {unit_title(name)}", "Все точки рядом заняты или вне зоны",
                   COLOR_WARN, self.grab())
        self.drop()
        return False

    def placed_check(self, before, cost, timeout=1.6):
        """Юнит поставлен, если он ушёл из руки (красная дорожка пропала)
        или деньги упали. Нечитаемые деньги не считаются провалом."""
        end = time.perf_counter() + timeout
        gone = 0
        while time.perf_counter() < end:
            self.check()
            if not self.path_visible():
                gone += 1
                if gone >= 2:          # два кадра подряд - не случайная вспышка
                    return True
            else:
                gone = 0
            if before is not None:
                v = self.money()
                if v is not None and before - v >= cost * 0.6:
                    return True
            self.sleep(0.1)
        return False

    def select(self, name, off=(0, 0)):
        """Клик по юниту (off - сдвиг клика в px эталона). Для юнитов, стоящих вплотную, по кругу
        дальности проверяется, кто именно выделился; если сосед - клик повторяется в сторону от соседа."""
        self.drop()
        k = getattr(self, "scale", 1.0)
        base = self.units[name]
        pt = (base[0] + off[0] * k / 1456.0, base[1] + off[1] * k / 819.0)
        self.click_unit(pt)
        if name not in getattr(self, "tight", ()):
            return
        if getattr(self, "cluster_uv", {}).get(name, ("",))[0] == "c3":
            return        # круг там наполовину закрыт панелью скорости - центр по нему не определить
        for attempt in range(3):
            other = self.selected_other(name)
            if not other:
                return
            ox, oy = self.units[other]
            dx, dy = (base[0] - ox) * 1456, (base[1] - oy) * 819
            d = math.hypot(dx, dy) or 1.0
            step_px = 5 * (attempt + 1) * k
            pt2 = (base[0] + dx / d * step_px / 1456.0, base[1] + dy / d * step_px / 819.0)
            log(f"  выделился {other} вместо {name} - кликаю на {step_px:.0f}px в сторону от него")
            self.click_unit(pt2)

    def click_unit(self, pt):
        """Клик по юниту и ожидание, пока игра покажет его панель. На медленном компьютере игра
        отвечает с задержкой: если панели до клика не было, время её появления замеряется и дальше
        все ожидания растягиваются под эту задержку."""
        lag = getattr(self, "lag", 0.2)
        try:
            was_open = panel_open(self.grab())
        except Exception:
            was_open = True
        if was_open and time.perf_counter() - getattr(self, "lag_at", 0.0) > 45:
            # давно не замерял отклик игры: закрываю панель и смотрю, за сколько она исчезнет
            self.click(IDLE_POINT, dwell=0.1)
            t0 = time.perf_counter()
            while time.perf_counter() - t0 < max(1.5, 4 * lag):
                self.sleep(0.1)
                try:
                    if not panel_open(self.grab()):
                        lag = self.lag = min(2.0, 0.5 * lag + 0.5 * (time.perf_counter() - t0))
                        self.lag_at = time.perf_counter()
                        was_open = False
                        break
                except Exception:
                    break
        self.click(pt)
        t0 = time.perf_counter()
        if was_open:
            self.sleep(max(0.35, 1.5 * lag))      # панель уже была - жду, пока сменится её содержимое
            return
        limit = max(1.2, 4 * lag)
        while time.perf_counter() - t0 < limit:
            self.sleep(0.1)
            try:
                if panel_open(self.grab()):
                    dt = time.perf_counter() - t0
                    self.lag = min(2.0, 0.6 * lag + 0.4 * dt)
                    self.lag_at = time.perf_counter()
                    self.lag_samples = getattr(self, "lag_samples", 0) + 1
                    if self.lag > 0.6 and not getattr(self, "lag_told", False):
                        self.lag_told = True
                        log(f"  игра отвечает медленно (~{self.lag:.1f} с на клик) - увеличиваю ожидания")
                    self.sleep(0.1)
                    return
            except Exception:
                break
        # панель так и не появилась: клик мимо, либо игра отвечает ещё медленнее, чем я жду.
        # Пока ни одного замера отклика нет - считаю, что дело в медленной игре, и жду дольше.
        if getattr(self, "lag_samples", 0) == 0 and getattr(self, "panel_reads", 0) == 0:
            self.lag = min(2.0, lag * 1.6 + 0.2)

    def selected_other(self, name):
        """Если круг дальности на экране принадлежит не name, а соседу - вернуть имя соседа."""
        c = getattr(self, "corner", None) or next(iter(getattr(self, "corners", {}).values()), None)
        if not c or name not in self.units:
            return None
        try:
            img = self.grab()
        except Exception:
            return None
        H = c["h"]
        own = (self.units[name][0] * 1456, self.units[name][1] * H)
        if self.types.get(name) == "farm":
            res = find_range_circle(img, own, 0.5 * c["w"], 1.05 * c["w"], "purple")
        else:
            res = find_range_circle(img, own, 1.0 * c["w"], 3.2 * c["w"])
        if res is None:
            return None
        cx, cy = res[0], res[1]
        best, best_d = None, None
        for u, p in self.units.items():
            d = math.hypot(p[0] * 1456 - cx, p[1] * H - cy)
            if best_d is None or d < best_d:
                best, best_d = u, d
        own_d = math.hypot(own[0] - cx, own[1] - cy)
        if best == name or own_d < 0.16 * c["w"] or best_d > 0.3 * c["w"]:
            return None
        if (self.types.get(best) == "farm") != (self.types.get(name) == "farm"):
            return None                          # у ферм круг другого цвета - с остальными не сравниваю
        return best

    def upgrade_cost(self, name):
        ups = UNITS.get(self.types.get(name), {}).get("up", [])
        lvl = self.levels.get(name, 0)
        return ups[lvl] if lvl < len(ups) else None

    def panel_level(self, name):
        """Настоящий уровень выделенного юнита по панели: по цене продажи и по цене прокачки.
        Чужим юнит считается, только если обе цены не подходят этому типу, а цена продажи есть
        в таблице другого типа (одна неточная цифра в таблице не должна сбивать с толку).
        -> (уровень или None, цена продажи или None, чужой ли это юнит)."""
        try:
            img = self.grab()
            price = read_panel_sell(img)
            up = read_panel_upgrade(img)
        except Exception:
            return None, None, False
        utype = self.types.get(name)
        ups = UNITS.get(utype, {}).get("up", [])
        lvl_s = level_by_sell(utype, price) if price is not None else None
        lvl_u = ups.index(up) if up is not None and up in ups else None
        if lvl_u is None and up is not None:
            lvl_u = _nearest(ups, up)                # одна неточная цифра или скидка на прокачку
        if lvl_s is not None:
            return lvl_s, price, False
        if lvl_u is not None:
            return lvl_u, price, False
        if price is not None and any(price in u["sell"] for t, u in UNITS.items() if t != utype):
            return None, price, True
        return None, price, False

    def select_checked(self, name, tries=8):
        """Выделить юнита и по панели убедиться, что выделен он, а не чужой (сосед или титан, который
        заслонил его сверху) и что панель вообще открылась. Камера не трогается: несколько попыток
        с небольшим сдвигом клика и паузой (титан двигается и на мгновение открывает юнита).
        -> (получилось ли, уровень или None, цена продажи или None)."""
        if getattr(self, "selected", None) == name:
            lvl, price, foreign = self.panel_level(name)
            if not foreign and lvl is not None:
                return True, lvl, price           # панель этого юнита всё ещё открыта - не кликаю заново
        offs = [(0, 0), (0, 6), (0, -6), (6, 0), (-6, 0), (0, 0), (0, 10), (0, -10)]
        if self.types.get(name) in ("tcam", "ttv", "tspk"):
            # титан большой и поворачивается за врагом: клик в одну и ту же точку может попасть
            # между частями модели. Пробую разные места вокруг его круга-основания.
            offs = [(0, 0), (-16, 0), (0, -14), (12, 10), (-12, 12), (16, -12), (-26, -6), (0, 22)]
            tries = max(tries, 5)
        seen = None
        reads = getattr(self, "panel_reads", 0)   # читалась ли панель в этом матче вообще
        for off in offs[:max(1, tries)]:
            self.select(name, off)
            lvl, price, foreign = self.panel_level(name)
            if lvl is not None:
                self.panel_reads = reads + 1
                self.selected = name
                return True, lvl, price
            if not foreign and reads == 0:
                self.selected = name              # панель не читается совсем (мелкое окно) - верю клику
                return True, lvl, price
            what = f"другой юнит (продажа ${price})" if foreign else "никто (панель не открылась)"
            if what != seen:
                log(f"  вместо {name} выделился {what} - пробую ещё")
                seen = what
            fails = self.__dict__.setdefault("nosel", {})
            if fails.get(name, 0) < 3:            # снимок: что было на экране, когда юнит не выделился
                fails[name] = fails.get(name, 0) + 1
                self.snap(f"nosel_{name}")
            self.click(IDLE_POINT, dwell=0.1)
            self.sleep(max(0.5, 2 * getattr(self, "lag", 0.2)))
        return False, None, None

    def replace_hidden(self, name):
        """Плунжера в углу заслонил титан и выделить его не выходит - ставлю вместо него нового
        на видном месте ниже титана (там он достаёт титана своей способностью)."""
        alias = self.__dict__.setdefault("alias", {})
        if name in alias or self.types.get(name) != "plunger" or "plunger" not in self.slots:
            return None
        spot = "m1" if "m1" not in self.__dict__.setdefault("spots_used", set()) else "m2"
        if spot in self.spots_used:
            return None
        self.spots_used.add(spot)
        new = name + "b"
        log(f"  {name} закрыт титаном - ставлю вместо него нового плунжера на видном месте")
        if not self.place({"unit": new, "type": "plunger", "at": spot}):
            return None
        alias[name] = new
        return new

    def upgrade(self, step, wait=True):
        """Одна прокачка (по плану - до следующего уровня). Уровень сверяется по панели юнита до и
        после нажатия E, поэтому бот не жмёт E вслепую повторно и не качает то, что уже прокачано."""
        name0 = step["unit"]
        name = getattr(self, "alias", {}).get(name0, name0)
        if name not in self.units:
            st = getattr(self, "failed_place", {}).get(name)
            if st and st["type"] in ("tcam", "ttv", "tspk") and st.get("retries", 0) < 4:
                st["retries"] = st.get("retries", 0) + 1
                log(f"  {name} так и не стоит на поле - пробую поставить ещё раз ({st['retries']}/4)")
                again = {k: v for k, v in st.items() if k not in ("retries", "sell_first", "margin")}
                self.place(again)
            if name not in self.units:
                log(f"  пропускаю прокачку {name}: его нет на поле")
                return False
        utype = self.types.get(name)
        ups = UNITS.get(utype, {}).get("up", [])
        want_map = self.__dict__.setdefault("want", {})
        if step.get("now"):                       # качать от того уровня, что есть (бой с боссом)
            want = None
        else:
            want = max(want_map.get(name0, 0), 0) + 1
            want_map[name0] = want
            if want > len(ups):
                log(f"  пропускаю прокачку {name}: уже максимальный уровень")
                return False
            if self.levels.get(name, 0) >= want:
                log(f"  {name} уже {self.levels[name]} ур. - прокачка не нужна")
                return True
        cost = step.get("cost") or self.upgrade_cost(name)
        if not cost:
            log(f"  пропускаю прокачку {name}: уже максимальный уровень")
            return False
        if wait:
            self.wait_money(cost, f"прокачку {name}")
        fails = blind = stun_waits = 0
        while fails < 4:
            if self.end_screen():
                raise MatchEnded
            ok_sel, lvl, price = self.select_checked(name)
            if name.startswith("gtv"):
                self.snap(f"sel_{name}")
            if not ok_sel:
                new = self.replace_hidden(name) if (name == name0 and want is not None) else None
                if new:
                    name = new                    # дальше качаю замену до нужного уровня
                    continue
                log(f"  не получается выделить {name} - пропускаю прокачку")
                return False
            if lvl is None:
                # панель не читается (мелкое окно) - старый способ: по падению денег, E один раз за попытку
                blind += 1
                if blind > 2:
                    break
                before = self.money_stable()
                self.key("e")
                if self.wait_change(before, -1, cost * 0.5) is not None:
                    log(f"  прокачал {name} за ${cost} (панель не прочиталась)")
                    self.levels[name] = self.levels.get(name, 0) + 1
                    report(f"Прокачал {unit_title(name)} → ур. {self.levels[name]}", f"${cost:,}", COLOR_INFO)
                    return True
                continue
            if lvl != self.levels.get(name, 0):
                log(f"  {name}: на самом деле {lvl} ур. (считал {self.levels.get(name, 0)}) - поправил")
                self.levels[name] = lvl
            if lvl >= len(ups):
                log(f"  {name} уже на максимуме ({lvl} ур.)")
                return False
            if want is not None and lvl >= want:
                log(f"  {name} уже {lvl} ур. - прокачка не нужна")
                return True
            cost = ups[lvl]
            have = self.money_stable()
            for _ in range(6):                    # сумма не прочиталась - не жму E вслепую, перечитываю
                if have is not None:
                    break
                self.sleep(0.3)
                have = self.money_stable()
            if have is not None and have < cost:
                if not wait:
                    return False
                self.wait_money(cost, f"прокачку {name}")
                continue                          # после ожидания выделяю и сверяю заново
            self.key("e")
            ok, after = False, lvl
            for _ in range(max(6, int(4 * (1.0 + 3 * getattr(self, "lag", 0.2))))):   # ждём новый уровень в панели
                self.sleep(0.25)
                after, _p, _f = self.panel_level(name)
                if after is not None and after > lvl:
                    ok = True
                    self.levels[name] = after
                    break
            if not ok and after is None:
                # панель перестала читаться (новая цена не распозналась) - решаю по деньгам
                now = self.money_stable()
                if have is None or now is None or have - now >= cost * 0.5:
                    ok = True
                    self.levels[name] = lvl + 1
            if not ok:
                if self.unit_stunned(name):
                    stun_waits += 1
                    if stun_waits == 1:
                        log(f"  {name} оглушён - его нельзя качать, жду")
                    if stun_waits > 10 or not wait:
                        return False
                    self.sleep(1.5)
                    continue
                log(f"  {name}: уровень не изменился ({lvl}) - повторяю")
                if fails == 0:
                    self.snap(f"noup_{name}")
                fails += 1
                continue
            log(f"  прокачал {name} за ${cost} -> {self.levels[name]} ур.")
            report(f"Прокачал {unit_title(name)} → ур. {self.levels[name]}", f"${cost:,}", COLOR_INFO)
            if want is None or self.levels[name] >= want:
                return True
        log(f"  НЕ удалось прокачать {name}")
        return False

    def sell_unit(self, name):
        """Продажа на клиенте мгновенная: выделить и X, ничего не ждём."""
        if name not in self.units:
            return False
        ok_sel, _lvl, _price = self.select_checked(name)   # по панели: выделен именно он, а не сосед/титан
        if not ok_sel:
            log(f"  не получается выделить {name} - не продаю (иначе продам чужого)")
            return False
        try:
            was_open = panel_open(self.grab())
        except Exception:
            was_open = False
        self.key("x")
        if was_open:
            # проданный юнит исчезает вместе с панелью; если панель осталась - продажа не прошла
            # (оглушённого юнита игра продать не даёт)
            sold = False
            t0 = time.perf_counter()
            limit = max(1.2, 4 * getattr(self, "lag", 0.2))
            while time.perf_counter() - t0 < limit:
                self.sleep(0.08)
                try:
                    if not panel_open(self.grab()):
                        sold = True
                        break
                except Exception:
                    sold = True
                    break
            if not sold:
                why = " - он оглушён, игра не даёт его продать" if self.unit_stunned(name) else ""
                log(f"  {name} не продался{why}")
                return False
        else:
            self.sleep(0.15)
        del self.units[name]
        self.levels.pop(name, None)
        self.selected = None
        return True

    def set_priority(self, name, target):
        """Новый юнит стоит на First; R листает приоритеты по кругу."""
        presses = PRIORITIES.index(target) - PRIORITIES.index("First")
        if presses <= 0:
            return
        ok_sel, _lvl, _price = self.select_checked(name)
        if not ok_sel:
            log(f"  не получается выделить {name} - приоритет не меняю (иначе поменяю соседу)")
            return
        for _ in range(presses):
            self.key("r")
            self.sleep(0.25)
        log(f"  {name}: приоритет {target}")
        self.click(IDLE_POINT, dwell=0.1)      # снять выделение
        self.sleep(0.2)

    def close_player_list(self):
        """Список игроков (Tab) справа сверху закрывает кнопки скорости. Tab его переключает:
        жмём Tab и смотрим, посветлел ли угол (список закрылся) или потемнел (открылся - жмём ещё раз)."""
        box = (0.80, 0.10, 0.98, 0.20)

        def shade():
            try:
                return float(np.asarray(self.grab(box).convert("L")).mean())
            except Exception:
                return None
        before = shade()
        self.check()
        self.k.press(keyboard.Key.tab)
        time.sleep(0.06)
        self.k.release(keyboard.Key.tab)
        self.sleep(0.5)
        after = shade()
        if before is None or after is None:
            return
        if after < before - 3:
            self.k.press(keyboard.Key.tab)
            time.sleep(0.06)
            self.k.release(keyboard.Key.tab)
            self.sleep(0.4)
        else:
            log("закрыл список игроков (Tab), чтобы не мешал кнопке скорости")

    def press_ready(self):
        """Включить 1.5x и нажать READY (один раз за матч)."""
        if not self.ready_pending:
            return
        self.ready_pending = False
        self.drop()
        if not self.ready_visible():
            return
        if self.use_speed and SETTINGS.get("use_speed", True):
            self.close_player_list()
            log(f"включаю скорость {SPEED_TITLES[speed_key()]}")
            self.click(SPEED_POINTS[speed_key()], dwell=0.35)
            self.sleep(0.5)
        for _ in range(5):
            log("нажимаю READY")
            self.click(READY_POINT, dwell=0.35)
            self.sleep(1.0)
            if not self.ready_visible():
                break

    def read_slots(self):
        """Какой юнит в каком слоте - по ценам на карточках. Два одинаковых чтения подряд."""
        prev = None
        best = ({}, [])
        for _ in range(8):
            try:
                slots, prices = detect_slots(self.grab())
            except Exception:
                slots, prices = {}, []
            known = [PRICE_TO_TYPE.get(p) or SHINY_TO_TYPE.get(p) for p in prices
                     if p in PRICE_TO_TYPE or p in SHINY_TO_TYPE]
            clean = len(known) == len(set(known))          # один юнит не может быть в двух слотах
            if clean and len(slots) >= len(best[0]):
                best = (slots, prices)
            if clean and slots and (slots, prices) == prev:
                return slots, prices
            prev = (slots, prices)
            self.sleep(0.25)
        return best

    def run_plan(self, plan, ready_pending=True):
        self.units = {}
        self.levels = {}
        self.types = {}
        self.holding = None
        self.ready_pending = ready_pending
        self.boss_t0 = None
        self.boss_done = set()
        self.boss_hits = 0
        self.boss_upgrade = None
        self.in_boss = False
        self.corner = None           # найденный 1-й угол дорожки (для плотной кучки)
        self.corners = {}            # все найденные углы: "c1", "c3"
        self.corner_tries = {}
        self.cluster_edge = 1.0      # во сколько раз пришлось увеличить отступ кучки от дороги
        self.cluster_step = 1.0      # ...и шаг между юнитами
        self.tight = set()           # юниты, стоящие в кучке вплотную
        self.want = {}               # до какого уровня план уже просил довести юнита
        self.nosel = {}
        self.snaps = 0               # отладочные снимки в папке debug (перезаписываются каждый матч)
        self.base_hp_last = 1.0
        self.base_hp_ref = None
        self.bar_missing = 0
        self.failed_place = {}
        self.nomoney_snaps = 0
        self.boss_stun_spam = {}
        self.boss_upgrade2 = None
        self.lapse_at = 0.0
        try:                             # снимки двух прошлых матчей хранятся в debug_prev и debug_prev2
            dbg, prev, prev2 = (os.path.join(HERE, x) for x in ("debug", "debug_prev", "debug_prev2"))
            if os.path.isdir(dbg) and any(fn.endswith(".jpg") for fn in os.listdir(dbg)):
                for src, dst in ((prev, prev2), (dbg, prev)):
                    if not os.path.isdir(src):
                        continue
                    os.makedirs(dst, exist_ok=True)
                    for fn in os.listdir(dst):
                        if fn.endswith((".jpg", ".png")):
                            os.remove(os.path.join(dst, fn))
                    for fn in os.listdir(src):
                        if fn.endswith((".jpg", ".png")):
                            os.replace(os.path.join(src, fn), os.path.join(dst, fn))
        except Exception:
            pass
        self.panel_reads = 0
        self.alias = {}              # плунжер, закрытый титаном -> его замена на видном месте
        self.spots_used = set()
        self.selected = None         # чья панель сейчас открыта (чтобы не кликать по юниту повторно)
        self.boss_try = {}
        self.boss_stun_hits = 0
        self.boss_saw_stun = False
        self.boss_at_turn = False
        self.boss_to_sell = []
        self.boss_waiting = set()
        self.boss_hp_logged = -99
        self.boss_moved_at = 0
        self.cluster_uv = {}         # юнит -> (угол, место относительно угла в ширинах дороги)
        first = next((s for s in plan if s["do"] == "place"), None)
        first_slot = (self.step_slot(first) if first else None) or 1
        self.camera_top_down()
        self.align_to_path(first_slot)
        for i, step in enumerate(plan, 1):
            log(f"шаг {i}/{len(plan)}: {step['do']} {step.get('unit', '')}")
            STATS.step, STATS.step_total = i, len(plan)
            STATS.step_text = {"place": "ставлю", "upgrade": "качаю", "sell": "продаю"}.get(
                step["do"], step["do"]) + " " + step.get("unit", "")
            if step["do"] == "place":
                self.place(step)
            elif step["do"] == "upgrade":
                self.upgrade(step)
            elif step["do"] == "sell":
                self.sell_unit(step["unit"])
            self.boss_tick()
        self.press_ready()
        log("план выполнен, жду конца матча")

    # --- способности и босс 30-й волны (Nightmare) ---

    def use_ability(self, name, tries=None, sel_tries=3, spam=10.0):
        """Нажать способность юнита клавишей T (первая способность на панели) и убедиться по кнопке,
        что она сработала (на кнопке появился отсчёт). Если не сработала - юнит оглушён, игра не
        приняла нажатие - T нажимается снова и снова до spam секунд, пока не сработает.
        -> True (сработала / уже действует), False (не получилось), "cooldown" (на перезарядке),
        "stunned" (за всё время так и не сработала, юнит оглушён)."""
        name = getattr(self, "alias", {}).get(name, name)
        if name not in self.units:
            return False
        utype = self.types.get(name)
        need = ABILITY_LEVEL.get(utype)
        if need and self.levels.get(name, 0) < need:
            log(f"  способность {name} ещё не открыта (ур. {self.levels.get(name, 0)} из {need})")
            return False
        ok_sel, lvl, _price = self.select_checked(name, tries=sel_tries)
        if not ok_sel:
            log(f"  не получается выделить {name} - способность не нажимаю")
            return False
        if need and lvl is not None and lvl < need:
            self.levels[name] = lvl
            log(f"  способность {name} ещё не открыта (на самом деле {lvl} ур. из {need})")
            return False
        state = ability_state(self.grab())
        if state == "active":
            log(f"  способность {name} уже действует")
            return True
        if state == "cooldown":
            log(f"  способность {name} на перезарядке")
            return "cooldown"
        hook = utype == "ttv"
        if hook:
            # Hook and Punch бьёт по цели титана: на время удара приоритет Boss, чтобы крюк точно ушёл в босса
            for _ in range(PRIORITIES.index("Boss")):
                self.key("r")
                self.sleep(0.12)
            self.sleep(0.35)
        t_end = time.perf_counter() + spam
        ok, presses = False, 0
        while True:
            self.key("t")
            presses += 1
            self.selected = name
            for _ in range(3):                    # ~0.6 с ждём отсчёт на кнопке
                self.sleep(0.2)
                if ability_state(self.grab()) != "ready":
                    ok = True
                    break
            if ok or time.perf_counter() > t_end:
                break
            if presses == 1:
                self.snap(f"abil_{name}_fail")
                log(f"  способность {name} не сработала с первого нажатия"
                    + (" (юнит оглушён)" if self.unit_stunned(name) else "")
                    + f" - жму T ещё до {spam:.0f} с")
            try:
                opened = panel_open(self.grab())
            except Exception:
                opened = True
            if not opened:                        # выделение слетело - выделяю заново
                self.selected = None
                if not self.select_checked(name, tries=2)[0]:
                    break
        if hook:
            self.sleep(0.4 if ok else 0.1)
            for _ in range(len(PRIORITIES) - PRIORITIES.index("Boss")):
                self.key("r")                     # Boss -> First
                self.sleep(0.12)
        if ok:
            log(f"  способность сработала: {name}" + (f" (с {presses}-го нажатия)" if presses > 1 else ""))
            report(f"✨ Способность: {unit_title(name)}", "", COLOR_INFO)
            return True
        log(f"  способность {name} так и не сработала за {spam:.0f} с ({presses} нажатий)")
        return "stunned" if self.unit_stunned(name) else False

    def teleport(self, name, at):
        """Teleport у Titan Screen Man: способность работает как постановка - навести и кликнуть, Q - отмена.
        Стоит половину цены продажи; титан переезжает со всеми уровнями. -> получилось ли."""
        if name not in self.units or self.types.get(name) != "ttv":
            return False
        lvl = self.levels.get(name, 0)
        if lvl < 4:
            return False
        cost = sell_value("ttv", lvl) // 2
        ok_sel, lvl2, price = self.select_checked(name, tries=4)
        if not ok_sel:
            log(f"  не получается выделить {name} - телепорт не нажимаю")
            return False
        if price:
            cost = price // 2
        v = self.money()
        if v is not None and v < cost:
            log(f"  на телепорт нужно ${cost}, а есть ${v}")
            return False
        self.key("y" if (lvl2 if lvl2 is not None else lvl) >= 7 else "t")   # с 7 ур. T - это Hook, телепорт - Y
        self.holding = None
        self.sleep(0.5)
        cands = self.candidates(at)
        t_end = time.perf_counter() + 14
        for pt, note, grow in cands:
            if time.perf_counter() > t_end:
                break
            before = self.money_stable()
            self.click(pt)
            moved = False
            for _ in range(12):
                self.sleep(0.12)
                v = self.money()
                if before is not None and v is not None and before - v >= cost * 0.6:
                    moved = True
                    break
            if moved:
                self.units[name] = pt
                self.selected = None
                self.__dict__.setdefault("cluster_uv", {}).pop(name, None)
                log(f"  телепортировал {name} за ${cost}" + (f", {note}" if note else ""))
                report(f"Телепорт: {unit_title(name)}", f"${cost:,}", COLOR_OK, self.grab())
                self.click(IDLE_POINT, dwell=0.1)
                return True
        self.key("q")                              # отмена телепорта
        self.sleep(0.2)
        self.click(IDLE_POINT, dwell=0.1)
        self.snap(f"notp_{name}")
        log(f"  телепорт {name} не удался: ни одна точка не подошла")
        return False

    def boss_visible(self):
        try:
            a = np.asarray(self.grab(BOSS_BAR_BOX).convert("RGB")).astype(np.int16)
        except Exception:
            return False
        r, g, b = a[..., 0], a[..., 1], a[..., 2]
        return float(((r > 170) & (g < 120) & (b < 150) & (r - g > 80)).mean()) > 0.45

    def upgrade_now(self, name):
        """Быстро качать юнита, пока хватает денег: одно выделение и E подряд, уровень сверяется
        по панели после каждого нажатия. -> сколько уровней прибавилось."""
        name = getattr(self, "alias", {}).get(name, name)
        if name not in self.units:
            return 0
        ups = UNITS.get(self.types.get(name), {}).get("up", [])
        ok_sel, lvl, _price = self.select_checked(name, tries=3)
        if not ok_sel or lvl is None:
            return 0
        self.levels[name] = lvl
        n = 0
        while lvl < len(ups):
            v = self.money()
            if v is None:
                v = self.money_stable()
            if v is None or v < ups[lvl]:
                break
            self.key("e")
            new = lvl
            for _ in range(max(6, int(8 * (0.6 + 3 * getattr(self, "lag", 0.2))))):
                self.sleep(0.12)
                a, _p, _f = self.panel_level(name)
                if a is not None and a > lvl:
                    new = a
                    break
            if new == lvl:
                if self.unit_stunned(name):
                    log(f"  {name} оглушён - докачаю, когда очнётся")
                break
            log(f"  прокачал {name} за ${ups[lvl]} -> {new} ур.")
            lvl = new
            self.levels[name] = lvl
            n += 1
        if n:
            report(f"Прокачал {unit_title(name)} → ур. {lvl}", "", COLOR_INFO)
        return n

    def timelapse(self):
        """Хроника матча: раз в 15 с уменьшенный снимок поля в папку debug (tММСС.jpg) и запись в журнал,
        когда у базы убыло здоровье. По этим снимкам видно, где и когда прорвались враги."""
        if not STATS.match_started or getattr(self, "in_lapse", False):
            return
        now = time.perf_counter()
        if now - getattr(self, "lapse_at", 0.0) < 15:
            return
        self.lapse_at = now
        self.in_lapse = True
        try:
            img = self.grab().convert("RGB")
            t = int(time.time() - STATS.match_started)
            hp = base_hp_fraction(img)
            if hp is None and base_hp_fraction(self.grab().convert("RGB")) is None:
                self.bar_missing = getattr(self, "bar_missing", 0) + 1
            else:
                self.bar_missing = 0
            if hp is not None and hp > 0.5 and getattr(self, "base_hp_ref", None) is None:
                self.base_hp_ref = hp             # первое чтение в матче - это полная полоса
            ref = getattr(self, "base_hp_ref", None)
            last = getattr(self, "base_hp_last", 1.0)
            if hp is not None and ref and hp / ref <= last - 0.04:
                self.base_hp_last = hp / ref
                log(f"  ! здоровье базы {self.base_hp_last:.0%} (на {t // 60}:{t % 60:02d} матча)")
            d = os.path.join(HERE, "debug")
            os.makedirs(d, exist_ok=True)
            w, h = img.size
            if w > 1280:
                img = img.resize((1280, round(h * 1280 / w)), Image.BILINEAR)
            img.save(os.path.join(d, f"t{t // 60:02d}{t % 60:02d}.jpg"), quality=60)
        except Exception:
            pass
        finally:
            self.in_lapse = False

    def snap(self, tag):
        """Снимок экрана в папку debug рядом с ботом - чтобы потом разобраться, что было на экране."""
        n = getattr(self, "snaps", 0)
        if n >= 90:
            return
        try:
            d = os.path.join(HERE, "debug")
            os.makedirs(d, exist_ok=True)
            self.grab().convert("RGB").save(os.path.join(d, f"{n:02d}_{tag}.jpg"), quality=82)
            self.snaps = n + 1
        except Exception:
            pass

    def unit_stunned(self, name):
        """Оглушён ли юнит (босс оглушает всех вокруг: юнит становится синим, над ним отсчёт)."""
        if name not in self.units:
            return False
        big = self.types.get(name) in ("tcam", "ttv", "tspk")
        try:
            v = stun_fraction(self.grab(), self.units[name], getattr(self, "scale", 1.0), big)
        except Exception:
            return False
        return v > (0.25 if big else 0.15)

    def boss_hp(self):
        """Здоровье босса 0..1 (медиана трёх замеров: полоса мигает при попаданиях)."""
        vals = []
        for _ in range(3):
            try:
                vals.append(boss_hp_fraction(self.grab()))
            except Exception:
                pass
            self.sleep(0.1)
        return sorted(vals)[len(vals) // 2] if vals else None

    def boss_tick(self):
        """Вызывается постоянно во время матча: следит за боссом и ведёт бой по шагам.
        Времена - секунды после появления полосы босса (из видео), но каждое действие ещё и
        привязано к событию: щит - когда титан не оглушён, перестановка титана - когда босс
        надолго оглушил его, и т.д."""
        if STATS.mode != "nightmare" or self.in_boss or not STATS.match_started:
            return
        now = time.perf_counter()
        if self.boss_t0 is None:
            if self.holding is not None or time.time() - STATS.match_started < 600 / max(0.6, speed_factor()):
                return
            self.boss_hits = self.boss_hits + 1 if self.boss_visible() else 0
            if self.boss_hits < 2:
                return
            self.boss_t0 = now
            self.boss_try = {}
            self.snap("boss_start")
            log("БОСС: появилась полоса здоровья - начинаю бой")
            report("👹 Босс 30-й волны", "Щит титана, Aerial Attack, затем переезд обоих титанов к 3-му повороту",
                   0x9B59B6, self.grab())
        self.in_boss = True
        try:
            t0 = self.boss_t0
            done, tries = self.boss_done, self.boss_try

            def el():
                # секунды боя в пересчёте на скорость 1.5x: все времена BOSS_* записаны для неё,
                # на 2x босс проходит тот же путь быстрее, на 1x - медленнее
                return (time.perf_counter() - t0) * speed_factor()

            def attempt(key, limit):
                if key in done:
                    return False
                tries[key] = tries.get(key, 0) + 1
                if tries[key] > limit:
                    done.add(key)
                    log(f"БОСС: шаг «{key}» так и не получился - иду дальше")
                    return False
                return True

            def ability(key, unit, limit):
                if key in done:
                    return
                real = getattr(self, "alias", {}).get(unit, unit)
                if real not in self.units:
                    done.add(key)
                    return
                if key.startswith("hook") and time.perf_counter() < getattr(self, "boss_hook_wait", 0):
                    return
                if not attempt(key, limit):
                    return
                self.drop()
                log(f"БОСС +{el():.0f}с: способность {unit}")
                res = self.use_ability(unit)
                if res == "cooldown" and key.startswith("hook"):
                    tries[key] -= 1               # крюк ещё перезаряжается - попытку не трачу, нажму позже
                    self.boss_hook_wait = time.perf_counter() + 4
                elif res == "stunned":
                    # 10 секунд жал - юнит всё это время был оглушён. Не больше двух таких заходов на шаг.
                    spams = self.__dict__.setdefault("boss_stun_spam", {})
                    spams[key] = spams.get(key, 0) + 1
                    if spams[key] < 2:
                        tries[key] -= 1
                elif res:
                    done.add(key)

            # здоровье босса в журнал раз в ~10 с - чтобы потом было видно, как шёл бой
            if el() - getattr(self, "boss_hp_logged", -99) >= 10:
                self.boss_hp_logged = el()
                hp_now = self.boss_hp()
                if hp_now is not None:
                    log(f"БОСС +{el():.0f}с: здоровье босса {hp_now:.0%}")

            # 1. Shield Mode у Titan Camcorderman (в видео после патча - на +17 с, когда босс уже под огнём)
            ttv = self.types.get("tcam") == "ttv"
            mt = "ttv" if ttv else "tcam"
            if ttv:
                # Titan Screen Man: Hook and Punch (14 320 урона, перезарядка 35 с) - пока босс в его радиусе
                if "move" not in done:
                    if el() >= BOSS_SHIELD_AT:
                        ability("hook1", "tcam", 3)
                    if el() >= BOSS_SHIELD_AT + 26 and el() < BOSS_TCAM_MOVE_MIN - 4:
                        ability("hook2", "tcam", 2)
                elif getattr(self, "boss_moved_at", None):
                    since = (time.perf_counter() - self.boss_moved_at) * speed_factor()
                    if since >= 6:
                        ability("hook3", "tcam", 3)
                    if since >= 34:
                        ability("hook4", "tcam", 3)
            elif el() >= BOSS_SHIELD_AT:
                ability("shield1", "tcam", 3)
            # 2. Aerial Attack у Titan Amplifierman (удар по области ~10 000) - когда босс у 2-го поворота
            #    Переезд Cameraman важнее: пока он не сделан, на Aerial не больше двух попыток.
            if (el() >= BOSS_AERIAL_AT and el() < 84.0 and "move2" not in done and "aerial" not in done
                    and "tspk" in self.units
                    and ("move" in done or el() < BOSS_TCAM_MOVE_MIN or tries.get("aerial", 0) < 2)):
                if self.levels.get("tspk", 0) < 8 and not self.unit_stunned("tspk"):
                    self.drop()
                    log(f"БОСС +{el():.0f}с: {UNITS[SECOND_TITAN]['title']} -> 8 ур. и сразу "
                        + ("Shield Mode" if SECOND_TITAN == "tcam" else "Aerial Attack"))
                    self.upgrade_now("tspk")          # выделение остаётся на нём - способность жмётся без нового клика
                ability("aerial", "tspk", 4)
            # 6. босс дошёл до 2-го поворота - Titan Camcorderman переезжает вперёд, к 3-му повороту.
            #    Признак: босс оглушил Titan Amplifierman, стоящего у 2-го поворота. Оглушённого юнита
            #    игра продать не даёт, поэтому если сам Cameraman ещё оглушён - жду, пока очнётся.
            if BOSS_MOVE_TCAM and "move" not in done and el() >= BOSS_TCAM_MOVE_MIN and "tcam" in self.units:
                if not getattr(self, "boss_at_turn", False) and self.unit_stunned("tspk"):
                    self.boss_at_turn = True
                    log(f"БОСС +{el():.0f}с: босс у 2-го поворота (оглушил {UNITS[SECOND_TITAN]['title']})")
                ready = getattr(self, "boss_at_turn", False) or el() >= BOSS_TCAM_MOVE_MAX
                if ready and self.unit_stunned("tcam"):
                    if "tcam_wait" not in self.boss_waiting:
                        self.boss_waiting.add("tcam_wait")
                        log(f"БОСС +{el():.0f}с: {UNITS[mt]['title']} оглушён - перееду, как только очнётся")
                elif ready:
                    hp = self.boss_hp()
                    if hp is not None and hp < 0.10:
                        done.add("move")
                        log(f"БОСС +{el():.0f}с: у босса осталось {hp:.0%} - титана не переставляю")
                    elif self.levels.get("tcam", 0) < 6:
                        done.add("move")
                        log("БОСС: титан-камера ниже 6 ур. - не переставляю (не хватит денег вернуть уровень)")
                    elif ttv and attempt("tp_try", 2) and self.teleport("tcam", "c3"):
                        # Titan Screen Man переезжает телепортом: без продажи, со всеми уровнями
                        done.add("move")
                        self.boss_upgrade = "tcam"
                        self.boss_moved_at = time.perf_counter()
                        self.boss_to_sell = [u for u in ("farm1", "farm2", "farm3", "farm4") if u in self.units]
                    elif ttv and "tp_try" not in done:
                        pass                      # вторая попытка телепорта - на следующем шаге
                    elif mt not in self.slots:
                        done.add("move")
                    elif attempt("move_try", 6):
                        log(f"БОСС +{el():.0f}с: переставляю {UNITS[mt]['title']} к 3-му повороту"
                            + (f" (у босса {hp:.0%})" if hp is not None else ""))
                        self.snap("move_tcam")
                        self.drop()
                        if self.sell_unit("tcam"):
                            done.add("move")
                            self.sleep(0.3)
                            if not self.place({"unit": "tcam", "type": mt, "at": "c3", "nowait": True}):
                                log("  у третьего поворота не встал - возвращаю титана в первый угол")
                                self.place({"unit": "tcam", "type": mt, "at": "c1", "nowait": True})
                            self.boss_upgrade = "tcam"
                            self.boss_moved_at = time.perf_counter()
                            self.upgrade_now("tcam")
                            # что ещё продать ради титана: фермы (волна последняя, дохода больше не будет)
                            self.boss_to_sell = [u for u in ("farm1", "farm2", "farm3", "farm4")
                                                 if u in self.units]
                    else:
                        done.add("move")
            # 7. после переезда: продаю фермы (оглушённые - когда очнутся), всё в титана
            if self.boss_upgrade:
                left = []
                for u in getattr(self, "boss_to_sell", []):
                    if u not in self.units:
                        continue
                    if self.unit_stunned(u) or not self.sell_unit(u):
                        left.append(u)
                if getattr(self, "boss_to_sell", []) and not left:
                    log(f"БОСС +{el():.0f}с: фермы проданы - деньги в титана")
                self.boss_to_sell = left
                cost = self.upgrade_cost(self.boss_upgrade)
                v = self.money()
                if cost and v is not None and v >= cost:
                    self.upgrade_now(self.boss_upgrade)
                u2 = getattr(self, "boss_upgrade2", None)
                if u2 and u2 in self.units:
                    cost2 = self.upgrade_cost(u2)
                    v = self.money()
                    if cost2 and v is not None and v >= cost2:
                        self.upgrade_now(u2)
            # 8. у нового Cameraman способность свежая - второй щит, как только он докачан
            if ("move" in done and not ttv and "tcam" in self.units and getattr(self, "boss_moved_at", None)
                    and (self.levels.get("tcam", 0) >= ABILITY_LEVEL["tcam"])):
                ability("shield3", "tcam", 2)
            # 9. босс прошёл 3-й поворот - Speakerman у 2-го поворота до него уже не достаёт:
            #    продаю и ставлю рядом с новым Cameraman, на все деньги
            #    Титан, который не достаёт до босса, бесполезен, поэтому переезд не откладывается ни из-за
            #    непроданных ферм, ни из-за недокачанного Cameraman: у Speakerman свои деньги от продажи.
            if ("move" in done and "move2" not in done and el() >= BOSS_TSPK_MOVE_AT and "tspk" in self.units
                    and SECOND_TITAN in self.slots):
                hp = self.boss_hp()
                if hp is not None and hp < 0.08:
                    done.add("move2")
                    log(f"БОСС +{el():.0f}с: у босса осталось {hp:.0%} - {UNITS[SECOND_TITAN]['title']} не переставляю")
                elif self.unit_stunned("tspk"):
                    pass
                elif attempt("move2_try", 2):
                    log(f"БОСС +{el():.0f}с: переставляю {UNITS[SECOND_TITAN]['title']} к 3-му повороту"
                        + (f" (у босса {hp:.0%})" if hp is not None else ""))
                    self.drop()
                    if self.sell_unit("tspk"):
                        done.add("move2")
                        self.sleep(0.3)
                        if not self.place({"unit": "tspk", "type": SECOND_TITAN, "at": "c3b", "quick": 12, "nowait": True}):
                            log("  у третьего поворота не встал - возвращаю второго титана на прежнее место")
                            self.place({"unit": "tspk", "type": SECOND_TITAN, "at": "t1n", "nowait": True})
                        self.upgrade_now("tspk")
                        self.boss_upgrade2 = "tspk"
        finally:
            self.in_boss = False

    # --- экраны между матчами ---

    def wait_end(self, timeout=1800, ready_breaks=False):
        end = time.perf_counter() + timeout
        last_click = 0
        while time.perf_counter() < end:
            self.check()
            if self.end_screen():
                return True
            if ready_breaks and self.ready_visible():
                return "ready"
            if not ready_breaks and getattr(self, "units", None) is not None:
                self.boss_tick()
            if self.money() is None and time.perf_counter() - last_click > 3:
                self.click(IDLE_POINT, dwell=0.1)    # закрыть окно с наградой
                last_click = time.perf_counter()
            self.sleep(0.5)
        return False

    # --- сток в хабе (Research Shop) ---

    def stock_due(self):
        """Пора ли проверить сток: он обновляется каждые полчаса (XX:00 и XX:30), проверяю между матчами."""
        if not SETTINGS.get("stock_enabled"):
            return False
        if not SERVER_LINK:
            if not getattr(self, "stock_nolink", False):
                self.stock_nolink = True
                log("сток: не задана ссылка приватного сервера - в хаб зайти не смогу, проверку пропускаю")
            return False
        return stock_period() != SETTINGS.get("stock_last")

    def stock_snap(self, tag):
        try:
            d = os.path.join(HERE, "stock_debug")
            os.makedirs(d, exist_ok=True)
            self.grab().convert("RGB").save(os.path.join(d, tag + ".jpg"), quality=80)
        except Exception:
            pass

    def stock_trip(self):
        """Между матчами: перезайти на приватку, дойти до NPC с образцами, сдать мусор, скупить сток."""
        SETTINGS["stock_last"] = stock_period()                  # сразу: при неудаче не повторять каждый матч
        save_settings()
        STATS.state = "stock"
        log("=== сток: перезахожу на приватный сервер и иду в Research Shop ===")
        t0 = time.perf_counter()
        try:
            self.relaunch_private()
            result = self.stock_run()
        except Aborted:
            raise
        except MatchEnded:
            result = "игра перезапустилась по дороге"
        except Exception as e:
            result = f"ошибка: {e!r}"
        if result is not True:
            log(f"сток: не получилось ({result}) - продолжаю фарм, следующая попытка после следующего обновления стока")
            self.stock_snap("fail")
            LINK.send("🛒 Сток: не получилось", f"{result}. Продолжаю фарм, попробую после следующего обновления стока.",
                      COLOR_WARN, grab_game_window())
        log(f"сток: заняло {_fmt_dur(time.perf_counter() - t0)}")

    def claim_daily(self):
        """Окно DAILY REWARDS в лобби: забрать награду (зелёная CLAIM) и закрыть окно крестиком.
        True - окно было."""
        if getattr(self, "daily_fail", 0) >= 3 and time.perf_counter() - getattr(self, "daily_fail_at", 0) < 600:
            return False                             # не закрывается - не зацикливаюсь, иду дальше как есть
        img = self.grab()
        frame = daily_frame(img)
        if not frame:
            return False
        btn = next((x for x in _blobs_green_buttons(img)
                    if frame[0] < x["cx"] < frame[2] and frame[1] < x["cy"] < frame[3] and x["w"] > 0.1), None)
        if btn:
            log("лобби: окно DAILY REWARDS - забираю ежедневную награду")
            self.click((btn["cx"], btn["cy"]), dwell=0.3)
            self.sleep(2.0)
        else:
            log("лобби: окно DAILY REWARDS - закрываю")
        # крестик - ромб на правом верхнем углу рамки; пробую его центр и точки чуть в стороны
        for dx, dy in ((-0.001, 0.003), (-0.004, 0.008), (0.003, -0.003), (-0.001, 0.003), (-0.006, 0.003)):
            frame = daily_frame(self.grab())
            if not frame:
                log("лобби: окно DAILY REWARDS закрыто")
                self.daily_fail = 0
                break
            pt = (frame[2] + dx, frame[1] + dy)
            self.hover(pt)
            self.sleep(0.25)
            self.click(pt, dwell=0.3)
            self.hover(IDLE_POINT)
            self.sleep(1.5)
        else:
            if daily_frame(self.grab()):
                self.daily_fail = getattr(self, "daily_fail", 0) + 1
                self.daily_fail_at = time.perf_counter()
                log(f"лобби: окно DAILY REWARDS не закрылось крестиком (попытка {self.daily_fail} из 3)")
                self.stock_snap("daily_not_closed")
            else:
                self.daily_fail = 0
        return True

    def stock_wait_lobby(self, timeout=200):
        """Дождаться лобби после перезахода (слева видна иконка TELEPORT)."""
        end = time.perf_counter() + timeout
        hits, idle = 0, time.perf_counter()
        while time.perf_counter() < end:
            self.check()
            if self.end_screen() or self.money() is not None or self.vote_screen():
                return None
            view = analyze_screen(self.grab())
            if view["tp_icon"] and not view["button"]:
                hits += 1
                if hits >= 3:
                    return view["tp_icon"]
            elif self.claim_daily():                 # окно ежедневной награды (и уже забранной тоже)
                hits = 0
                idle = time.perf_counter()
            else:
                hits = 0
                if time.perf_counter() - idle > 4:
                    self.click(IDLE_POINT, dwell=0.1)        # окно с наградой / загрузка
                    idle = time.perf_counter()
            self.sleep(0.6)
        return None

    def stock_teleport(self, icon):
        """Меню TELEPORT -> Research Sector -> Teleport."""
        self.tp_icon_pt = (icon["cx"], icon["cy"])
        frame = None
        for attempt in range(5):
            frame = _menu_frame(self.grab())
            if frame:
                break
            if attempt == 2 and self.toggle_chat():
                log("сток: меню телепорта не открывается - закрываю чат Roblox")
                self.sleep(1.0)
            self.click(self.tp_icon_pt, dwell=0.35)
            self.sleep(1.5)
        if not frame:
            return False
        x0, y0 = frame["cx"] - frame["w"] / 2, frame["cy"] - frame["h"] / 2
        card = (x0 + 0.25 * frame["w"], y0 + 0.297 * frame["h"])      # вторая строка списка: RESEARCH SECTOR
        log(f"сток: меню телепорта -> Research Sector ({card[0]:.3f}, {card[1]:.3f}) -> Teleport")
        btn = None
        for attempt in range(6):
            if attempt in (0, 3):
                self.click(card, dwell=0.35)
                self.sleep(1.0)
            btn = next((x for x in _blobs_green_buttons(self.grab()) if x["cx"] > 0.5), None)
            if btn:
                break
            self.sleep(0.4)
        self.stock_snap("1_menu")
        if btn:
            self.click((btn["cx"], btn["cy"]), dwell=0.35)
        else:
            # зелёной кнопки нет: либо уже стоим в Research Sector, либо её не видно - жму в её место
            log("сток: зелёной кнопки Teleport не вижу - жму в её место")
            self.click(self.tp_button_estimate(), dwell=0.35)
        self.sleep(5.0)
        if _menu_frame(self.grab()):
            self.close_tp_menu()
        return True

    def stock_walk_to_npc(self):
        """После телепорта: повернуть камеру налево на 90 градусов, найти фиолетовый круг (SAMPLES) и дойти до него.
        Возвращает рамку открывшегося окна или None."""
        quarter = abs(self.px_per_deg) * 90
        self.turn_camera(-quarter)
        self.stock_snap("2_turned")
        circle = None
        for turn in range(4):
            circle = stock_circle(self.grab())
            if circle:
                break
            log("сток: фиолетового круга не видно - поворачиваю камеру ещё на 90 градусов")
            self.turn_camera(-quarter)
        if not circle:
            return None
        log(f"сток: вижу круг NPC ({circle['cx']:.2f}, {circle['cy']:.2f}) - иду к нему")
        lost, prev, talks = 0, None, 0
        for step in range(45):
            circle = stock_circle(self.grab())
            if not circle:
                lost += 1
                if lost >= 4:
                    break
                self.walk_forward(0.25, jump=True)
                continue
            lost = 0
            dx = circle["cx"] - 0.5
            close = circle["cy"] > 0.40 or circle["w"] > 0.115
            if abs(dx) > (0.07 if close else 0.04):
                self.turn_camera(dx * 100 * abs(self.px_per_deg) * 0.8)
                if step < 6 and abs(dx) > 0.15:
                    continue
            if close:
                frame = self.stock_talk()
                if frame:
                    return frame
                talks += 1
                if talks >= 6:
                    break
                self.walk_forward(0.25, jump=talks % 2 == 0)
                continue
            stuck = prev is not None and abs(circle["cy"] - prev[0]) < 0.004 and abs(circle["w"] - prev[1]) < 0.006
            prev = (circle["cy"], circle["w"])
            self.walk_forward(0.4 if circle["cy"] < 0.3 else 0.22, jump=stuck)
        # круг потерян (стоим прямо на нём или NPC его закрыл) - пробую поговорить там, где стою
        for _ in range(2):
            frame = self.stock_talk()
            if frame:
                return frame
            self.walk_forward(0.3)
        return None

    def stock_talk(self):
        """Зажать E у NPC, два клика пропустить диалог; вернуть рамку окна Sample Exchange или None."""
        self.hold_keys("e", 1.6)
        self.sleep(0.5)
        for _ in range(2):
            frame = stock_frame(self.grab())
            if frame:
                return frame
            self.click((0.548, 0.66), dwell=0.12)            # окно диалога «Click to skip»
            self.sleep(0.6)
        end = time.perf_counter() + 2.5
        while time.perf_counter() < end:
            frame = stock_frame(self.grab())
            if frame:
                return frame
            self.sleep(0.3)
        return None

    def stock_run(self):
        """Вся прогулка за стоком. True - дошли до магазина; иначе строка с причиной."""
        icon = self.stock_wait_lobby()
        if not icon:
            return "не дождался лобби после перезахода"
        self.sleep(2.0)
        if not self.stock_teleport(icon):
            return "не открылось меню телепорта"
        frame = self.stock_walk_to_npc()
        if not frame:
            return "не дошёл до NPC с образцами (окно обмена не открылось)"
        self.sleep(0.8)
        self.stock_snap("3_exchange")
        self.hover(IDLE_POINT)
        self.sleep(0.2)
        img = self.grab()
        frame = stock_frame(img) or frame
        tokens = stock_tokens(img, frame)
        lines = []
        in_shop = bool(stock_cards(img, frame))
        if SETTINGS.get("stock_sell_trash", True) and not in_shop:
            log("сток: сдаю образцы (ALL -> EXCHANGE)")
            self.click(stock_point(frame, STOCK_ALL), dwell=0.2)
            self.sleep(0.7)
            self.click(stock_point(frame, STOCK_EXCHANGE), dwell=0.2)
            self.sleep(1.5)
            self.hover(IDLE_POINT)
            self.sleep(0.3)
            after = stock_tokens(self.grab(), frame)
            if tokens is not None and after is not None and after != tokens:
                log(f"сток: образцы сданы, жетонов {tokens} -> {after}")
                lines.append(f"Сдал образцы: +{after - tokens} жетонов")
            else:
                log(f"сток: сдавать нечего (жетонов {after if after is not None else '?'})")
            if after is not None:
                tokens = after
        # вкладка Research Shop (та же кнопка в магазине возвращает обратно - жму, только пока карточек нет)
        cards = []
        for attempt in range(4):
            img = self.grab()
            frame = stock_frame(img) or frame
            cards = stock_cards(img, frame)
            if cards:
                break
            if attempt in (0, 2):
                self.click(stock_point(frame, STOCK_TAB), dwell=0.2)
                self.hover(IDLE_POINT)
            self.sleep(1.2)
        if not cards:
            self.stock_close(frame)
            return "не открылась вкладка Research Shop"
        self.sleep(0.5)
        img = self.grab()
        cards = stock_cards(img, frame)
        tokens = stock_tokens(img, frame) or tokens
        self.stock_snap("4_shop")
        keep = int(SETTINGS.get("stock_min_tokens") or 0)
        log(f"сток: магазин открыт, жетонов {tokens if tokens is not None else '?'}, товаров {len(cards)}, "
            f"оставлять не меньше {keep}")
        items = stock_items()
        bought = []
        for n, card in enumerate(cards, 1):
            key = None
            if card["sig"] is not None:
                key, score, base = stock_identify(card["sig"], card.get("qty"))
                if key is None:
                    num = 1 + sum(1 for k in items if k.startswith("item"))
                    key = f"item{num}"
                    while key in items:
                        num += 1
                        key = f"item{num}"
                    qty = card.get("qty")
                    if base and qty:
                        title = f"{base} x{qty:,}"           # знакомое название, новое количество
                    elif base:
                        title = f"{base} (количество не прочиталось)"
                    else:
                        title = f"Новый предмет {num}"
                    items[key] = {"name": title, "buy": bool(SETTINGS.get("stock_buy_new")), "qty": qty,
                                  "sigs": [sig_to_hex(card["sig"])], "price": card["price"]}
                    log(f"сток: товар {n} - новый предмет (похожесть названия на известные {score:.2f}), записал как "
                        f"«{title}»; картинка: stock\\{key}.png")
                elif score < 0.9 and len(items[key]["sigs"]) < 5:
                    items[key]["sigs"].append(sig_to_hex(card["sig"]))   # так название выглядит на этом экране
                try:
                    d = os.path.join(HERE, "stock")
                    os.makedirs(d, exist_ok=True)
                    path = os.path.join(d, key + ".png")
                    if not os.path.exists(path):
                        img.crop(card["box"]).convert("RGB").save(path)
                except Exception:
                    pass
            it = items.get(key) if key else None
            name = it["name"] if it else f"товар {n} (название не прочиталось)"
            price = card["price"]
            if it is not None and price is not None:
                it["price"] = price
            ptxt = f"{price}" if price is not None else "?"
            if card["state"] != "buy":
                log(f"сток: {name} - уже куплен (SOLD OUT)")
                continue
            want = bool(it["buy"]) if it else bool(SETTINGS.get("stock_buy_new"))
            if not want:
                log(f"сток: {name} за {ptxt} - пропускаю (выключен в настройках)")
                continue
            if keep > 0 and (tokens is None or price is None):
                log(f"сток: {name} за {ptxt} - не покупаю: не прочитал жетоны или цену, а задан минимальный запас")
                lines.append(f"✖ {name}: не прочитал цену/жетоны")
                continue
            if tokens is not None and price is not None and tokens - price < keep:
                log(f"сток: {name} за {price} - не покупаю: останется {tokens - price}, а нужно не меньше {keep}")
                lines.append(f"✖ {name} ({price}): не хватает жетонов сверх запаса")
                continue
            # товара может быть несколько штук («2 LEFT»): жму BUY, пока кнопка не станет SOLD OUT
            count, fails = 0, 0
            while count < 12 and fails < 2:
                if count and tokens is not None and price is not None and tokens - price < keep:
                    log(f"сток: {name} - ещё есть, но на следующую штуку жетонов сверх запаса не хватает")
                    break
                if count and keep > 0 and (tokens is None or price is None):
                    break
                self.click(card["pt"], dwell=0.2)
                self.hover(IDLE_POINT)
                self.sleep(1.2)
                shot = self.grab()
                now = stock_cards(shot, frame)
                same = [c for c in now if abs(c["pt"][0] - card["pt"][0]) < 0.03 and abs(c["pt"][1] - card["pt"][1]) < 0.04]
                sold = bool(same) and same[0]["state"] == "sold"
                left = stock_tokens(shot, frame)
                paid = left is not None and tokens is not None and left < tokens
                if sold or paid:
                    count += 1
                    fails = 0
                    if left is not None:
                        tokens = left
                    elif tokens is not None and price is not None:
                        tokens -= price
                    if sold:
                        break
                    if left is None:
                        break                                    # жетоны не читаются - не жму вслепую дальше
                else:
                    fails += 1
            if count:
                log(f"сток: КУПИЛ {name}" + (f" x{count}" if count > 1 else "") + f" по {ptxt}"
                    + (f", жетонов осталось {tokens}" if tokens is not None else ""))
                bought.append(name)
                lines.append(f"✔ {name}" + (f" ×{count}" if count > 1 else "") + f" ({ptxt})")
            else:
                log(f"сток: {name} за {ptxt} - нажал BUY, но ничего не изменилось (не хватило жетонов?)")
                lines.append(f"✖ {name} ({ptxt}): покупка не прошла")
        SETTINGS["stock_items"] = items
        save_settings()
        self.stock_snap("5_done")
        shot = grab_game_window()
        self.stock_close(frame)
        title = f"🛒 Сток: куплено {len(bought)}" if bought else "🛒 Сток: ничего не купил"
        if tokens is not None:
            lines.append(f"Жетонов: {tokens}")
        LINK.send(title, "\n".join(lines), COLOR_OK if bought else COLOR_INFO, shot)
        return True

    def stock_close(self, frame):
        """Закрыть окно магазина крестиком в правом верхнем углу рамки."""
        for _ in range(3):
            self.click((frame[2] - 0.002, frame[1] + 0.005), dwell=0.25)
            self.hover(IDLE_POINT)
            self.sleep(1.0)
            now = stock_frame(self.grab())
            if not now:
                return True
            frame = now
        return False

    def press_rejoin(self):
        self.rejoined_at = time.perf_counter()
        report("🔁 Rejoin", "Перезапускаю матч", COLOR_INFO)
        for _ in range(6):
            log("финальный экран: нажимаю Rejoin")
            self.click(REJOIN_POINT, dwell=0.35)
            end = time.perf_counter() + 4
            while time.perf_counter() < end:
                if not self.end_screen():
                    return True
                self.sleep(0.2)
        return False

    def zoom_out(self, notches=12):
        """Отдалить камеру колёсиком, чтобы видеть больше кругов."""
        self.check()
        self.hover((0.5, 0.45))
        for _ in range(notches):
            self.m.scroll(0, -1)
            time.sleep(0.03)
        self.sleep(0.4)

    def walk_forward(self, seconds, jump=False):
        """Идти вперёд (W); с jump=True ещё и прыгнуть в начале шага."""
        self.check()
        w = self._vk("w")
        self.k.press(w)
        try:
            if jump:
                self.sleep(0.08)
                self.k.press(keyboard.Key.space)
                self.sleep(0.12)
                self.k.release(keyboard.Key.space)
            self.sleep(seconds)
        finally:
            self.k.release(w)

    def walk_to_pad(self, max_steps=40):
        """Повернуть камеру так, чтобы синий круг был по центру экрана, и идти вперёд (W).
        Круги стоят полукругом вокруг точки появления, так что путь прямо к кругу свободен."""
        log("иду к синему кругу")
        self.zoom_out(6)          # издалека кругов видно больше, и они не теряются при повороте
        lost = 0
        target_x = None
        prev = None               # (cy, area) круга на прошлом шаге - чтобы понять, что застряли
        for step in range(max_steps):
            view = analyze_screen(self.grab())
            if view["button"] or self.vote_screen():
                return True
            pads = view["pads"]
            if not pads:
                lost += 1
                if lost >= 3:
                    return False
                self.walk_forward(0.3, jump=True)
                continue
            lost = 0
            # круг ближе всего к центру по горизонтали (тот, что прямо по курсу)
            ref_x = 0.5 if target_x is None else target_x
            pad = min(pads, key=lambda p: abs(p["cx"] - ref_x) - p["area"] * 2)
            dx = pad["cx"] - 0.5
            if abs(dx) > 0.04:
                # ~100 градусов на ширину экрана; поворачиваем чуть меньше, чтобы не перелететь
                self.turn_camera(dx * 100 * abs(self.px_per_deg) * 0.8)
                target_x = 0.5
                if step < 6 and abs(dx) > 0.15:
                    continue
            # прыгаем каждый 3-й шаг и всегда, если круг не приблизился (упёрлись в забор)
            stuck = prev is not None and abs(pad["cy"] - prev[0]) < 0.004 and abs(pad["area"] - prev[1]) < prev[1] * 0.04
            prev = (pad["cy"], pad["area"])
            self.walk_forward(0.45 if abs(dx) < 0.1 else 0.25, jump=stuck or step % 3 == 2)
        return False

    def toggle_chat(self):
        """Клик по иконке чата - самой правой иконке в верхней панели Roblox (логотип, меню, чат)."""
        img = self.grab((0, 0, 0.25, 0.1))
        a = np.asarray(img.convert("RGB")).astype(np.int16)
        h, w = a.shape[:2]
        blobs = [x for x in _blobs(a.min(axis=2) > 200) if x["area"] > 0.0002]
        big = [x for x in blobs if x["area"] > 0.003]
        if not big:
            return False
        row = min(x["cy"] for x in big)                 # иконки панели - самый верхний ряд
        icons = [x for x in blobs if abs(x["cy"] - row) * h < max(6, h * 0.08) and x["cx"] * w > 3]
        if len(icons) < 2:
            return False
        chat = max(icons, key=lambda x: x["cx"])
        if chat["cx"] * 0.25 > 0.2:                      # не дальше 20% ширины экрана
            return False
        self.click((chat["cx"] * 0.25, chat["cy"] * 0.1), dwell=0.3)
        return True

    def tp_button_estimate(self):
        """Где в меню телепорта кнопка Teleport (по зелёной рамке меню)."""
        img = self.grab()
        w, h = img.size
        a = np.asarray(img.convert("RGB").resize((640, max(1, round(640 * h / w))), Image.BILINEAR)).astype(np.int16)
        r, g, b = a[..., 0], a[..., 1], a[..., 2]
        frames = [x for x in _blobs((g > 100) & (g - r > 55) & (g - b > 55)) if x["w"] > 0.4 and x["h"] > 0.3]
        if not frames:
            return (0.734, 0.689)
        fr = max(frames, key=lambda x: x["w"])
        x0, y0 = fr["cx"] - fr["w"] / 2, fr["cy"] - fr["h"] / 2
        return (x0 + 0.862 * fr["w"], y0 + 0.89 * fr["h"])

    def close_tp_menu(self):
        """Закрыть меню телепорта: повторный клик по иконке TELEPORT, а если не вышло - крестик."""
        icon = getattr(self, "tp_icon_pt", None) or (0.047, 0.41)
        self.click(icon, dwell=0.35)
        self.sleep(0.8)
        if not analyze_screen(self.grab())["deploy_card"]:
            return
        img = self.grab()
        w, h = img.size
        a = np.asarray(img.convert("RGB").resize((LOBBY_W, max(1, round(LOBBY_W * h / w))), Image.BOX)).astype(np.int16)
        r, g, b = a[..., 0], a[..., 1], a[..., 2]
        frames = [x for x in _blobs((g > 100) & (g - r > 55) & (g - b > 55)) if x["w"] > 0.4 and x["h"] > 0.3]
        if frames:
            fr = max(frames, key=lambda x: x["w"])
            pt = (fr["cx"] + fr["w"] / 2 - 0.003, fr["cy"] - fr["h"] / 2 + 0.008)
        else:
            pt = (0.819, 0.175)
        self.click(pt, dwell=0.35)
        self.sleep(0.8)

    def to_match_start(self, timeout=300):
        """Дойти до начала матча (экран с READY). Из лобби, зоны вертолётов,
        выбора карты, выбора сложности или финального экрана."""
        end = time.perf_counter() + timeout
        voted = idle = deployed = here = lobby_hits = tp_fail = vote_tries = 0
        vote_done = False
        turns = 0
        unknown_logged = 0
        while time.perf_counter() < end:
            self.check()
            if self.end_screen():
                self.press_rejoin()
                continue
            if self.money() is not None:
                if self.ready_visible():
                    self.in_private = False   # из матча через Back to Lobby попадём в обычное лобби
                    return True
                # READY появляется не сразу после загрузки - подождём его, прежде чем решать,
                # что матч уже идёт без нас
                seen_ready = False
                for _ in range(40):
                    self.sleep(0.5)
                    if self.ready_visible():
                        seen_ready = True
                        break
                    if self.end_screen() or self.vote_screen():
                        break
                if seen_ready:
                    self.in_private = False
                    return True
                if self.money() is None:
                    continue
                log("матч уже идёт - жду его конца (или появления READY)")
                if self.wait_end(ready_breaks=True) == "ready":
                    log("появилась кнопка READY - начинаю матч")
                    self.in_private = False
                    return True
                continue
            if self.vote_screen():
                # повторный клик по VOTE снимает голос, поэтому жмём, только пока голос не засчитан
                if not vote_done and vote_tries < 4 and time.perf_counter() - voted > 1.5:
                    vmode = mode_key()
                    vtitle = MODES[vmode]["title"]
                    pt = self.vote_point(vmode) or VOTE_FALLBACK[vmode]
                    box = (pt[0] - 0.07, pt[1] - 0.035, pt[0] + 0.07, pt[1] + 0.035)
                    before = np.asarray(self.grab(box).convert("L")).astype(np.int16)
                    log(f"экран выбора сложности: голосую за {vtitle} ({pt[0]:.3f}, {pt[1]:.3f})")
                    self.click(pt, dwell=0.35)
                    vote_tries += 1
                    voted = time.perf_counter()
                    self.sleep(0.8)
                    after = np.asarray(self.grab(box).convert("L")).astype(np.int16)
                    diff = float(np.abs(after - before).mean()) if after.shape == before.shape else 99.0
                    if diff > 1.2:                  # счётчик 0/1 -> 1/1 и подсветка кнопки
                        vote_done = True
                        log(f"  голос засчитан (изменение кнопки {diff:.1f})")
                        report(f"🗳 Голосую за {vtitle}", "", 0xED4245 if vmode == "hard" else 0x9B59B6)
                    else:
                        log(f"  кнопка не изменилась ({diff:.1f}) - клик не прошёл, повторю")
                self.sleep(0.5)
                continue
            vote_done, vote_tries = False, 0
            view = analyze_screen(self.grab())
            btn = view["button"]
            if (btn or view["dialog"] or not view["tp_icon"]) and self.claim_daily():
                continue
            # лобби узнаём только по меню слева (иконка TELEPORT) и только если видим его
            # несколько раз подряд; сразу после Rejoin загрузочные экраны не считаем лобби
            in_lobby = bool(view["tp_icon"] or view["deploy_card"]) and not view["button"]
            lobby_hits = lobby_hits + 1 if in_lobby else 0
            after_rejoin = time.perf_counter() - getattr(self, "rejoined_at", -1e9) < 120
            if PRIVATE_ONLY and SERVER_LINK and lobby_hits >= 3 and not self.in_private and not after_rejoin:
                log("лобби не приватное (или неизвестно какое) - перезахожу на приватный сервер по ссылке")
                LINK.send("Перезахожу на приватный сервер", "", COLOR_WARN)
                close_roblox()
                self.sleep(3)
                open_private_link()
                self.in_private = True
                self.link_opened = time.perf_counter()
                self.sleep(25)
                continue
            if btn and not view["deploy_card"]:
                # Экран выбора сложности выезжает с анимацией: в первые мгновения он ещё не узнаётся,
                # а зелёная кнопка VOTE под карточкой EASY уже видна и похожа на Start. В одиночку
                # один такой клик сразу запускает матч на EASY. Поэтому зелёную кнопку жму, только если
                # она простояла на месте, а экран за это время не оказался выбором сложности.
                self.sleep(2.5 if time.perf_counter() - getattr(self, "rejoined_at", -1e9) < 45 else 1.2)
                if self.vote_screen() or self.end_screen() or self.money() is not None:
                    continue
                view2 = analyze_screen(self.grab())
                b2 = view2["button"]
                if (not b2 or abs(b2["cx"] - btn["cx"]) > 0.03 or abs(b2["cy"] - btn["cy"]) > 0.03
                        or self.vote_screen()):
                    continue
                view, btn = view2, b2
            if view["deploy_card"]:
                tp_fail = 0
                log("меню телепорта: Deployment Zone -> Teleport")
                card = view["deploy_card"]
                self.click((card["cx"], card["cy"]), dwell=0.35)
                self.sleep(1.0)
                # после выбора карточки кнопка справа внизу становится зелёной
                btn2 = None
                for attempt in range(6):
                    btn2 = next((x for x in _blobs_green_buttons(self.grab()) if x["cx"] > 0.5), None)
                    if btn2:
                        break
                    if attempt == 2:           # первый клик Roblox иногда пропускает
                        self.click((card["cx"], card["cy"]), dwell=0.35)
                    self.sleep(0.4)
                if btn2:
                    self.click((btn2["cx"], btn2["cy"]), dwell=0.35)
                    deployed = time.perf_counter()
                    turns = 0
                    here = 0
                    self.sleep(5.0)
                else:
                    # зелёную кнопку не видно: жмём туда, где она должна быть (правый низ рамки меню).
                    # Если мы уже в Deployment Zone, кнопка серая и клик ничего не сделает.
                    pt = self.tp_button_estimate()
                    log("  зелёную кнопку не вижу - жму в место кнопки Teleport "
                        f"({pt[0]:.3f}, {pt[1]:.3f}); снимок меню: tp_menu_debug.png")
                    try:
                        shot = self.grab()
                        shot.save(os.path.join(HERE, "tp_menu_debug.png"))
                        if not getattr(self, "tp_debug_sent", False):
                            self.tp_debug_sent = True
                            LINK.send("Отладка: меню телепорта", f"Кнопку Teleport не нашёл, жму в "
                                      f"({pt[0]:.3f}, {pt[1]:.3f}). Перешли этот снимок Claude.",
                                      COLOR_WARN, shot)
                    except Exception:
                        pass
                    self.click(pt, dwell=0.35)
                    self.sleep(4.0)
                    deployed = time.perf_counter()
                    turns = 0
                    if not analyze_screen(self.grab())["deploy_card"]:
                        here = 0
                        self.sleep(1.0)
                        continue
                    here += 1
                    log("  меню не закрылось - значит, мы уже в Deployment Zone; ищу синие круги")
                    self.close_tp_menu()
                    if here >= 3:
                        log("  круги так и не нашлись - перезахожу на приватный сервер")
                        close_roblox()
                        self.sleep(3)
                        open_private_link()
                        self.in_private = True
                        self.link_opened = time.perf_counter()
                        here = 0
                        self.sleep(25)
            elif btn and (btn["cx"] < 0.36 or btn["cy"] < 0.76):
                # Start у вертолёта и Select в выборе карты - по центру внизу.
                # Зелёная кнопка левее или выше - это не они
                # (например, VOTE под EASY на экране выбора сложности) - не трогаю.
                if time.perf_counter() - unknown_logged > 15:
                    log(f"зелёная кнопка не на месте Start ({btn['cx']:.2f}, {btn['cy']:.2f}) - не нажимаю")
                    unknown_logged = time.perf_counter()
            elif btn and view["dialog"]:
                log("выбор карты: Invaded City -> Select")
                self.click((btn["cx"] + MAP_CARD_OFFSET[0], btn["cy"] + MAP_CARD_OFFSET[1]), dwell=0.35)
                self.sleep(0.8)
                self.click((btn["cx"], btn["cy"]), dwell=0.35)
                self.sleep(2.0)
            elif btn:
                log("вертолёт: Start")
                self.click((btn["cx"], btn["cy"]), dwell=0.35)
                self.sleep(3.0)
            elif view["pads"] and time.perf_counter() - deployed < 120:
                # круги ищем только после телепорта: в Command Hall полно синих ламп
                self.walk_to_pad()
            elif view["tp_icon"]:
                if time.perf_counter() - deployed < 30 and turns < 5:
                    if turns == 0:
                        log("синих кругов не видно - отдаляю камеру")
                        self.zoom_out()
                    else:
                        log("синих кругов не видно - поворачиваю камеру")
                        self.turn_camera(abs(self.px_per_deg) * 90)
                    turns += 1
                else:
                    tp_fail += 1
                    if tp_fail in (3, 6):
                        # меню не открывается - скорее всего иконку закрыло окно чата Roblox
                        if self.toggle_chat():
                            log("лобби: TELEPORT не открывается - закрываю чат Roblox")
                            self.sleep(1.0)
                            continue
                    log("лобби: открываю TELEPORT")
                    icon = view["tp_icon"]
                    self.tp_icon_pt = (icon["cx"], icon["cy"])
                    self.click((icon["cx"], icon["cy"]), dwell=0.35)
                    self.sleep(1.5)
            elif time.perf_counter() - idle > 4:
                if time.perf_counter() - unknown_logged > 15:
                    log("не узнаю экран (загрузка или окно с наградой?) - кликаю в угол; "
                        "снимок сохранён в unknown_screen.png")
                    try:
                        self.grab().save(os.path.join(HERE, "unknown_screen.png"))
                    except Exception:
                        pass
                    unknown_logged = time.perf_counter()
                self.click(IDLE_POINT, dwell=0.1)   # окно с наградой "click anywhere" / загрузка
                idle = time.perf_counter()
            self.sleep(0.5)
        return False

    def run(self, loops):
        if not self.start.is_set():
            log(f"бот версии {VERSION}. Переключись в Roblox и нажми F8. F6 - остановить.")
        while not self.start.wait(0.1):
            if self.abort.is_set():
                raise Aborted
        log("старт")
        if not SERVER_LINK:
            log("ссылка приватного сервера не задана (Настройки -> «Ссылка приватного сервера») - "
                "после вылета бот не сможет сам зайти в игру")
        apply_resolution()
        LINK.send("▶ Фарм запущен", f"Invaded City · {MODES[mode_key()]['title']}", COLOR_OK)
        custom = os.path.join(HERE, "plan.json")
        done = 0
        while loops == 0 or done < loops:
            STATS.state = "waiting"
            if done and time.time() - _update_checked > UPDATE_EVERY:
                new = self_update(quiet=True)            # между матчами: обновиться и продолжить фарм
                if new:
                    LINK.send("Обновление", f"Установлена версия {new}, перезапускаюсь и продолжаю фарм.", COLOR_OK)
                    time.sleep(1.5)
                    restart_app(resume=True)
            if self.stock_due():                     # сток - первым делом: и при старте фарма, и между матчами
                self.stock_trip()
                STATS.state = "waiting"
            self.check()
            if not self.to_match_start():
                stuck = getattr(self, "stuck", 0) + 1
                self.stuck = stuck
                if not SERVER_LINK or stuck > 3:
                    log("не дошёл до начала матча за 5 минут" + (" три раза подряд даже после перезапуска Roblox"
                                                                 if stuck > 3 else "") + " - останавливаюсь")
                    LINK.send("Застрял", "Не дошёл до начала матча, фарм остановлен.",
                              COLOR_BAD, grab_game_window(), ping=True)
                    return
                # застрял (зависший экран, окно ошибки, не тот сервер): закрываю Roblox и захожу заново
                # по ссылке приватного сервера - дальше бот идёт в матч как после обычного запуска
                log(f"не дошёл до начала матча за 5 минут - перезапускаю Roblox на приватном сервере ({stuck}/3)")
                LINK.send("Застрял - перезапускаю Roblox", f"Не дошёл до начала матча за 5 минут. "
                          f"Закрываю игру и захожу на приватный сервер (попытка {stuck} из 3).",
                          COLOR_WARN, grab_game_window(), ping=(stuck == 3))
                self.relaunch_private()
                continue
            self.stuck = 0
            mode = mode_key()
            STATS.mode = mode
            self.slots, prices = self.read_slots()
            STATS.slots, STATS.prices = dict(self.slots), list(prices)
            for note in apply_slot_prices(self.slots, prices):
                log(f"цена не как в таблице: {note} - считаю по цене с карточки")
            found = ", ".join(f"{n}: {UNITS[t]['title']}" for t, n in sorted(self.slots.items(), key=lambda x: x[1]))
            log(f"режим {MODES[mode]['title']}; слоты: {found or 'ничего не распознал'} (цены: {prices})")
            cash0 = self.money_stable()
            if mode == "nightmare" and cash0 is not None and cash0 != NIGHTMARE_START_CASH:
                log(f"ВНИМАНИЕ: в начале матча ${cash0}, а на NIGHTMARE должно быть ${NIGHTMARE_START_CASH} - "
                    f"похоже, запустилась другая сложность (голос ушёл не туда)")
                LINK.send("Похоже, запустилась не NIGHTMARE", f"Стартовые деньги ${cash0} вместо "
                          f"${NIGHTMARE_START_CASH}.", COLOR_WARN, grab_game_window())
            miss = missing_units(self.slots, mode)
            if miss:
                log("НЕТ НУЖНЫХ ЮНИТОВ на панели: " + "; ".join(miss) + " - останавливаюсь")
                LINK.send("Нет нужных юнитов", f"Для {MODES[mode]['title']} на панели не хватает: "
                          + "; ".join(miss), COLOR_BAD, grab_game_window(), ping=True)
                return
            if os.path.exists(custom):
                with open(custom, encoding="utf-8") as f:
                    plan = json.load(f)
                log(f"план из plan.json: {len(plan)} шагов")
            else:
                plan = build_plan(mode, self.slots)
            done += 1
            log(f"=== матч {done}" + (f" из {loops}" if loops else "") + f" · {MODES[mode]['title']} ===")
            STATS.state = "running"
            STATS.match_started = time.time()
            STATS.step, STATS.step_total = 0, len(plan)
            try:
                self.run_plan(plan, ready_pending=True)
                self.wait_end()
            except MatchEnded:
                log("матч закончился")
            try:                                     # итоговый экран (победа/поражение, волна) - в debug
                self.grab().convert("RGB").save(os.path.join(HERE, "debug", "zz_end.jpg"), quality=75)
            except Exception:
                pass
            dur = time.time() - STATS.match_started
            STATS.matches = done
            STATS.total_matches += 1
            STATS.match_started = None
            STATS.step_total = 0
            if SETTINGS.get("notify_match", True):
                img = grab_game_window() if SETTINGS.get("notify_screens", True) else None
                LINK.send(f"Матч {done} завершён", "", COLOR_OK, img,
                          fields=[("Длительность", _fmt_dur(dur)),
                                  ("За сессию", str(done)), ("Всего", str(STATS.total_matches))])
            save_settings()
            if loops and done >= loops:
                log("готово")
                return



# ---------- приложение (окно) ----------

APP_NAME = "TWD Farm"
C = {
    "bg": "#0f1115", "side": "#14171d", "card": "#1a1e26", "card2": "#212631", "line": "#2a3040",
    "text": "#e8ecf3", "muted": "#8a93a6", "dim": "#5d6578",
    "accent": "#3ddc84", "accent_d": "#2bb36a", "red": "#ef5350", "red_d": "#c94341",
    "yellow": "#f5b942", "blue": "#5b8cff", "entry": "#11141a",
}
FONT = "Segoe UI"


def _rounded(cv, x1, y1, x2, y2, r, **kw):
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
           x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return cv.create_polygon(pts, smooth=True, **kw)


class FarmApp:
    def __init__(self):
        import tkinter as tk
        self.tk = tk
        if sys.platform == "win32":            # своя иконка на панели задач, даже при запуске через pythonw
            try:
                import ctypes
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("TWDFarm.App")
            except Exception:
                pass
        self.bot = None
        self.thread = None
        self.link = None
        self.team = None
        self.team_install = None
        self.mode_lock = threading.RLock()
        self.root = tk.Tk()
        self.root.title(APP_NAME)
        self.root.configure(bg=C["bg"])
        self.root.geometry("980x640")
        self.root.minsize(860, 560)
        self._set_icon()
        self.pages = {}
        self.nav = {}
        try:
            from tkinter import ttk
            st = ttk.Style(self.root)
            st.theme_use("clam")
            st.configure("Dark.Vertical.TScrollbar", background=C["line"], troughcolor=C["bg"],
                         bordercolor=C["bg"], arrowcolor=C["muted"], lightcolor=C["line"], darkcolor=C["line"],
                         gripcount=0, arrowsize=12)
            st.map("Dark.Vertical.TScrollbar", background=[("active", C["dim"])])
            self.ttk = ttk
        except Exception:
            self.ttk = None
        self.vars = {}
        self._build()
        self.show("home")
        self.hotkeys = keyboard.Listener(on_press=self._on_hotkey)
        self.hotkeys.start()
        self.restart_discord()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.root.after(200, self.tick)
        log(f"{APP_NAME} {VERSION.split()[0]} готов. Старт - кнопкой или F8, стоп - F6.")

    # --- оформление ---
    def _set_icon(self):
        try:
            from PIL import ImageTk, ImageDraw
            ico = Image.new("RGBA", (64, 64), (0, 0, 0, 0))
            d = ImageDraw.Draw(ico)
            d.rounded_rectangle([2, 2, 62, 62], 14, fill=(26, 30, 38))
            d.polygon([(24, 18), (24, 46), (47, 32)], fill=(61, 220, 132))
            self._icon = ImageTk.PhotoImage(ico)
            self.root.iconphoto(True, self._icon)
        except Exception:
            pass

    def label(self, parent, text="", size=10, color="text", weight="normal", bg="card", **kw):
        return self.tk.Label(parent, text=text, font=(FONT, size, weight), fg=C[color], bg=C[bg], **kw)

    def card(self, parent, **kw):
        return self.tk.Frame(parent, bg=C["card"], highlightthickness=1, highlightbackground=C["line"], **kw)

    def _build(self):
        tk = self.tk
        side = tk.Frame(self.root, bg=C["side"], width=230)
        side.pack(side="left", fill="y")
        side.pack_propagate(False)
        logo = tk.Frame(side, bg=C["side"])
        logo.pack(fill="x", padx=18, pady=(22, 26))
        cv = tk.Canvas(logo, width=34, height=34, bg=C["side"], highlightthickness=0)
        cv.pack(side="left")
        _rounded(cv, 1, 1, 33, 33, 9, fill=C["card2"])
        cv.create_polygon(13, 9, 13, 25, 26, 17, fill=C["accent"])
        t = tk.Frame(logo, bg=C["side"])
        t.pack(side="left", padx=10)
        self.label(t, "TWD Farm", 13, "text", "bold", bg="side").pack(anchor="w")
        self.mode_sub = self.label(t, "Invaded City", 8, "muted", bg="side")
        self.mode_sub.pack(anchor="w")
        for key, icon, name in [("home", "⌂", "Главная"), ("wastelands", "◈", "Wastelands"), ("settings", "⚙", "Настройки"),
                                ("stock", "🛒", "Сток"), ("discord", "✉", "Discord"), ("log", "≡", "Журнал")]:
            b = tk.Label(side, text=f"  {icon}   {name}", anchor="w", font=(FONT, 11), fg=C["muted"],
                         bg=C["side"], padx=14, pady=10, cursor="hand2")
            b.pack(fill="x", padx=10, pady=2)
            b.bind("<Button-1>", lambda e, k=key: self.show(k))
            b.bind("<Enter>", lambda e, w=b, k=key: w.configure(bg=C["card"]) if self.current != k else None)
            b.bind("<Leave>", lambda e, w=b, k=key: w.configure(bg=C["side"]) if self.current != k else None)
            self.nav[key] = b
        self.label(side, f"версия {VERSION.split()[0]}", 8, "dim", bg="side").pack(side="bottom", pady=14)
        self.hk = self.label(side, "F8 — старт   F6 — стоп", 8, "dim", bg="side")
        self.hk.pack(side="bottom")
        self.main = tk.Frame(self.root, bg=C["bg"])
        self.main.pack(side="left", fill="both", expand=True)
        self.current = None
        self._page_home()
        self.pages["wastelands"] = tk.Frame(self.main, bg=C["bg"])
        self._page_settings()
        self._page_stock()
        self._page_discord()
        self._page_log()

    def show(self, key):
        for k, p in self.pages.items():
            p.pack_forget()
        padding = 6 if key=="wastelands" else 26
        self.pages[key].pack(fill="both", expand=True, padx=padding, pady=12 if key=="wastelands" else 22)
        for k, b in self.nav.items():
            b.configure(bg=C["card"] if k == key else C["side"], fg=C["text"] if k == key else C["muted"])
        self.current = key
        if key == "wastelands":
            self.mode_sub.configure(text="Wastelands", fg=C["accent"])
            self.hk.configure(text="F6 — остановить помощника")
            if self.team is None and self.team_install is None:
                self.open_team()
        else:
            self._units_sig = None
            self._draw_units()
            self.hk.configure(text="F8 — старт   F6 — стоп")

    def open_team(self):
        page = self.pages["wastelands"]
        for widget in page.winfo_children():
            widget.destroy()
        try:
            directory = team_directory()
            if directory:
                self.mount_team(directory)
                return
        except (OSError, ImportError) as exc:
            self.team_error(exc)
            return
        import queue
        result = queue.SimpleQueue()
        self.team_install = result
        self.label(page, "Загружаю компоненты Wastelands…", bg="bg").pack(anchor="w", padx=10)

        def fetch():
            try:
                result.put(team_directory(download=True))
            except Exception as exc:
                result.put(exc)
        threading.Thread(target=fetch, daemon=True).start()

    def mount_team(self, directory):
        if directory not in sys.path[:1]:
            sys.path.insert(0, directory)
        from wastelands import App
        page = self.pages["wastelands"]
        for widget in page.winfo_children():
            widget.destroy()
        self.team = App(page, prefs=SETTINGS.get("wastelands"), save_prefs=self.save_team,
                        farm_busy=lambda: self.thread is not None and self.thread.is_alive(),
                        mode_lock=self.mode_lock)

    def save_team(self, prefs):
        if SETTINGS.get("wastelands") != prefs:
            SETTINGS["wastelands"] = prefs
            save_settings()

    def team_error(self, error):
        page = self.pages["wastelands"]
        for widget in page.winfo_children():
            widget.destroy()
        self.label(page, f"Не удалось открыть Wastelands: {error}", bg="bg", wraplength=480).pack(anchor="w")
        self.flat_button(page, "Повторить", self.open_team).pack(anchor="w", pady=10)

    def header(self, page, title, sub):
        h = self.tk.Frame(page, bg=C["bg"])
        h.pack(fill="x", pady=(0, 16))
        self.label(h, title, 18, "text", "bold", bg="bg").pack(anchor="w")
        self.label(h, sub, 10, "muted", bg="bg").pack(anchor="w")
        return h

    # --- Главная ---
    def _page_home(self):
        tk = self.tk
        p = tk.Frame(self.main, bg=C["bg"])
        self.pages["home"] = p
        top = tk.Frame(p, bg=C["bg"])
        top.pack(fill="x", pady=(0, 18))
        left = tk.Frame(top, bg=C["bg"])
        left.pack(side="left", fill="x", expand=True)
        self.label(left, "Главная", 18, "text", "bold", bg="bg").pack(anchor="w")
        st = tk.Frame(left, bg=C["bg"])
        st.pack(anchor="w", pady=(4, 0))
        self.dot = tk.Canvas(st, width=12, height=12, bg=C["bg"], highlightthickness=0)
        self.dot.pack(side="left")
        self.dot_id = self.dot.create_oval(2, 2, 11, 11, fill=C["dim"], outline="")
        self.state_lbl = self.label(st, "остановлен", 10, "muted", bg="bg")
        self.state_lbl.pack(side="left", padx=6)
        self.btn = tk.Canvas(top, width=190, height=52, bg=C["bg"], highlightthickness=0, cursor="hand2")
        self.btn.pack(side="right")
        self.btn.bind("<Button-1>", lambda e: self.toggle())
        self.btn.bind("<Enter>", lambda e: self._draw_btn(hover=True))
        self.btn.bind("<Leave>", lambda e: self._draw_btn())
        self._draw_btn()

        grid = tk.Frame(p, bg=C["bg"])
        grid.pack(fill="x")
        self.stat = {}
        for i, (key, title) in enumerate([("matches", "Матчей за сессию"), ("total", "Всего матчей"),
                                          ("uptime", "Время работы"), ("money", "Деньги")]):
            c = self.card(grid)
            c.grid(row=0, column=i, sticky="nsew", padx=(0 if i == 0 else 10, 0))
            grid.columnconfigure(i, weight=1)
            self.label(c, title, 9, "muted").pack(anchor="w", padx=16, pady=(14, 0))
            v = self.label(c, "—", 20, "text", "bold")
            v.pack(anchor="w", padx=16, pady=(2, 14))
            self.stat[key] = v

        uc = self.card(p)
        uc.pack(fill="x", pady=(14, 0))
        head = tk.Frame(uc, bg=C["card"])
        head.pack(fill="x", padx=16, pady=(12, 4))
        self.label(head, "Режим", 11, "text", "bold").pack(side="left")
        self.mode_btn = {}
        seg = tk.Frame(head, bg=C["entry"], highlightthickness=1, highlightbackground=C["line"])
        seg.pack(side="left", padx=14)
        for key in ("hard", "nightmare"):
            b = tk.Label(seg, text=MODES[key]["title"], font=(FONT, 9, "bold"), padx=14, pady=5, cursor="hand2",
                         bg=C["entry"], fg=C["muted"])
            b.pack(side="left")
            b.bind("<Button-1>", lambda e, k=key: self.set_mode(k))
            self.mode_btn[key] = b
        self.mode_note = self.label(head, "", 9, "muted")
        self.mode_note.pack(side="left")
        self.speed_btn = {}
        seg2 = tk.Frame(head, bg=C["entry"], highlightthickness=1, highlightbackground=C["line"])
        seg2.pack(side="right")
        for key in ("1", "1.5", "2"):
            b = tk.Label(seg2, text=SPEED_TITLES[key], font=(FONT, 9, "bold"), padx=12, pady=5, cursor="hand2",
                         bg=C["entry"], fg=C["muted"])
            b.pack(side="left")
            b.bind("<Button-1>", lambda e, k=key: self.set_speed(k))
            self.speed_btn[key] = b
        self.label(head, "Скорость", 11, "text", "bold").pack(side="right", padx=(0, 10))
        self._paint_speed()
        self.units_row = tk.Frame(uc, bg=C["card"])
        self.units_row.pack(fill="x", padx=16, pady=(4, 12))
        self._units_sig = None

        mc = self.card(p)
        mc.pack(fill="x", pady=(14, 0))
        row = tk.Frame(mc, bg=C["card"])
        row.pack(fill="x", padx=16, pady=(14, 6))
        self.label(row, "Текущий матч", 11, "text", "bold").pack(side="left")
        self.match_time = self.label(row, "", 10, "muted")
        self.match_time.pack(side="right")
        self.step_lbl = self.label(mc, "ожидание старта", 10, "muted")
        self.step_lbl.pack(anchor="w", padx=16)
        self.bar = tk.Canvas(mc, height=10, bg=C["card"], highlightthickness=0)
        self.bar.pack(fill="x", padx=16, pady=(10, 16))

        lc = self.card(p)
        lc.pack(fill="both", expand=True, pady=(14, 0))
        self.label(lc, "Последние события", 11, "text", "bold").pack(anchor="w", padx=16, pady=(14, 6))
        self.mini_log = tk.Text(lc, height=8, bg=C["card"], fg=C["muted"], font=("Consolas", 9), bd=0,
                                highlightthickness=0, wrap="none", state="disabled")
        self.mini_log.pack(fill="both", expand=True, padx=16, pady=(0, 14))
        self._tags(self.mini_log)

    def _paint_speed(self):
        cur = speed_key()
        for k, b in self.speed_btn.items():
            b.configure(bg=C["accent"] if k == cur else C["entry"], fg="#0f1115" if k == cur else C["muted"])

    def set_speed(self, key):
        SETTINGS["speed"] = key
        save_settings()
        self._paint_speed()
        log(f"скорость игры: {SPEED_TITLES[key]}" + (" (применится со следующего матча)"
                                                    if self.thread is not None and self.thread.is_alive() else ""))

    def set_mode(self, key):
        SETTINGS["mode"] = key
        save_settings()
        log(f"режим: {MODES[key]['title']}" + (" (применится со следующего матча)"
                                               if self.thread is not None and self.thread.is_alive() else ""))

    def _draw_units(self):
        """Плашки нужных юнитов: зелёная - найден (с номером слота), красная - не найден, серая - ещё не проверял."""
        mode = mode_key()
        slots = dict(STATS.slots)
        sig = (mode, tuple(sorted(slots.items())), bool(STATS.prices))
        if sig == self._units_sig:
            return
        self._units_sig = sig
        for k, b in self.mode_btn.items():
            b.configure(bg=C["accent"] if k == mode else C["entry"], fg="#0f1115" if k == mode else C["muted"])
        col = C["red"] if mode == "hard" else "#b07cff"
        if self.current != "wastelands":
            self.mode_sub.configure(text=f"Invaded City · {MODES[mode]['title']}", fg=col)
        self.mode_note.configure(text=f"{MODES[mode]['waves']} волн")
        for w in self.units_row.winfo_children():
            w.destroy()
        checked = bool(STATS.prices)
        groups = titan_groups(slots) + [[t] for t in MODES[mode]["need"]] + MODES[mode]["need_any"]
        self.label(self.units_row, "Юниты [слот]:" if checked else "Нужны:", 9, "muted").pack(side="left", padx=(0, 8))
        for group in groups:
            have = [t for t in group if t in slots]
            title = " / ".join(UNITS[t]["short"] for t in (have[:1] or group))
            if have:
                txt, fg, bg = f"✓ {title} [{slots[have[0]]}]", C["accent"], "#12281c"
            elif checked:
                txt, fg, bg = f"✗ {title}", C["red"], "#2a1516"
            else:
                txt, fg, bg = title, C["muted"], C["card2"]
            self.tk.Label(self.units_row, text=txt, font=(FONT, 9), fg=fg, bg=bg, padx=7, pady=4).pack(
                side="left", padx=(0, 5))

    def _draw_btn(self, hover=False):
        cv = self.btn
        cv.delete("all")
        running = self.thread is not None and self.thread.is_alive()
        col = (C["red_d"] if hover else C["red"]) if running else (C["accent_d"] if hover else C["accent"])
        _rounded(cv, 2, 2, 188, 50, 14, fill=col)
        if running:
            cv.create_rectangle(56, 19, 70, 33, fill="#ffffff", outline="")
            cv.create_text(118, 26, text="Стоп", font=(FONT, 13, "bold"), fill="#ffffff")
        else:
            cv.create_polygon(55, 17, 55, 35, 71, 26, fill="#0f1115")
            cv.create_text(118, 26, text="Старт", font=(FONT, 13, "bold"), fill="#0f1115")

    def _tags(self, txt):
        txt.tag_configure("time", foreground=C["dim"])
        txt.tag_configure("ok", foreground=C["accent"])
        txt.tag_configure("warn", foreground=C["yellow"])
        txt.tag_configure("bad", foreground=C["red"])
        txt.tag_configure("head", foreground=C["blue"])
        txt.tag_configure("norm", foreground=C["text"])

    @staticmethod
    def _tag_for(line):
        low = line.lower()
        if "ошибк" in low or "не удалось" in low or "застрял" in low or "упал" in low:
            return "bad"
        if "===" in line or "старт" in low:
            return "head"
        if "поставил" in low or "прокачал" in low or "готов" in low or "подключён" in low:
            return "ok"
        if "не узнаю" in low or "не найд" in low or "не нашёл" in low or "жду" in low or "останов" in low:
            return "warn"
        return "norm"

    def _append(self, txt, line, limit):
        txt.configure(state="normal")
        txt.insert("end", line[:9], "time")
        txt.insert("end", line[9:] + "\n", self._tag_for(line))
        n = int(txt.index("end-1c").split(".")[0])
        if n > limit:
            txt.delete("1.0", f"{n - limit}.0")
        txt.configure(state="disabled")
        txt.see("end")

    # --- элементы настроек ---
    def switch(self, parent, key, title, sub=""):
        tk = self.tk
        row = tk.Frame(parent, bg=C["card"])
        row.pack(fill="x", padx=18, pady=8)
        t = tk.Frame(row, bg=C["card"])
        t.pack(side="left", fill="x", expand=True)
        self.label(t, title, 10, "text").pack(anchor="w")
        if sub:
            self.label(t, sub, 8, "muted", wraplength=480, justify="left").pack(anchor="w")
        var = tk.BooleanVar(value=bool(SETTINGS.get(key)))
        self.vars[key] = var
        cv = tk.Canvas(row, width=46, height=24, bg=C["card"], highlightthickness=0, cursor="hand2")
        cv.pack(side="right")

        def draw(*_):
            cv.delete("all")
            on = var.get()
            _rounded(cv, 1, 1, 45, 23, 11, fill=C["accent"] if on else C["line"])
            x = 33 if on else 13
            cv.create_oval(x - 8, 4, x + 8, 20, fill="#ffffff", outline="")
        cv.bind("<Button-1>", lambda e: var.set(not var.get()))
        var.trace_add("write", draw)
        draw()
        return var

    def entry(self, parent, key, title, sub="", width=40, secret=False, numeric=False):
        tk = self.tk
        row = tk.Frame(parent, bg=C["card"])
        row.pack(fill="x", padx=18, pady=8)
        self.label(row, title, 10, "text").pack(anchor="w")
        if sub:
            self.label(row, sub, 8, "muted", wraplength=560, justify="left").pack(anchor="w")
        var = tk.StringVar(value=str(SETTINGS.get(key, "")))
        self.vars[key] = var
        box = tk.Frame(row, bg=C["entry"], highlightthickness=1, highlightbackground=C["line"],
                       highlightcolor=C["accent"])
        box.pack(anchor="w", pady=(6, 0), fill="x" if width > 30 else None)
        e = tk.Entry(box, textvariable=var, width=width, font=(FONT, 10), bg=C["entry"], fg=C["text"],
                     insertbackground=C["text"], bd=0, relief="flat", highlightthickness=0,
                     show="•" if secret else "")
        e.pack(padx=10, pady=7, fill="x")
        if secret:
            def toggle_show(e_=e):
                e_.configure(show="" if e_.cget("show") else "•")
            eye = self.tk.Label(box, text="👁", bg=C["entry"], fg=C["muted"], cursor="hand2")
            eye.place(relx=1.0, x=-24, rely=0.5, anchor="w")
            eye.bind("<Button-1>", lambda ev: toggle_show())
        return var

    def flat_button(self, parent, text, cmd, color="accent", fg="#0f1115"):
        b = self.tk.Label(parent, text=text, font=(FONT, 10, "bold"), bg=C[color], fg=fg, padx=18, pady=8,
                          cursor="hand2")
        b.bind("<Button-1>", lambda e: cmd())
        return b

    def section(self, page, title):
        c = self.card(page)
        c.pack(fill="x", pady=(0, 14))
        self.label(c, title, 11, "text", "bold").pack(anchor="w", padx=18, pady=(14, 2))
        return c

    def scrollbar(self, parent, command):
        if self.ttk:
            return self.ttk.Scrollbar(parent, orient="vertical", command=command, style="Dark.Vertical.TScrollbar")
        return self.tk.Scrollbar(parent, orient="vertical", command=command)

    def scroll_page(self, key):
        tk = self.tk
        outer = tk.Frame(self.main, bg=C["bg"])
        self.pages[key] = outer
        cv = tk.Canvas(outer, bg=C["bg"], highlightthickness=0)
        sb = self.scrollbar(outer, cv.yview)
        inner = tk.Frame(cv, bg=C["bg"])
        inner.bind("<Configure>", lambda e: cv.configure(scrollregion=cv.bbox("all")))
        win = cv.create_window((0, 0), window=inner, anchor="nw")
        cv.bind("<Configure>", lambda e: cv.itemconfigure(win, width=e.width))
        cv.configure(yscrollcommand=sb.set)
        cv.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        outer.bind_all("<MouseWheel>", lambda e: cv.yview_scroll(int(-e.delta / 120), "units")
                       if self.current == key else None, add="+")
        return inner

    # --- Настройки ---
    def _page_settings(self):
        p = self.scroll_page("settings")
        self.header(p, "Настройки", "Сохраняются в settings.json рядом с приложением")
        self.flat_button(p, "Wastelands · основа и твинки", lambda: self.show("wastelands")).pack(anchor="w", pady=(0, 10))
        s = self.section(p, "Матчи")
        self.entry(s, "loops", "Сколько матчей сыграть", "0 — без ограничений", width=8)
        self.switch(s, "use_speed", "Включать скорость игры", "Какую именно - выбирается на главной странице (1x / 1.5x / 2x)")
        self.switch(s, "auto_update", "Обновляться автоматически",
                    "При запуске и между матчами бот скачивает новую версию с GitHub и перезапускается")
        s = self.section(p, "Окно Roblox")
        self.entry(s, "focus_after", "Через сколько секунд кликать в Roblox, если окно не активно",
                   "Если переключишься в другое окно, фарм сам вернётся в игру", width=8)
        self.switch(s, "move_to_primary", "Переносить Roblox на основной монитор")
        self.switch(s, "private_only", "Играть только на приватном сервере",
                    "Если окажешься в чужом лобби — перезайти по ссылке приватки")
        self.entry(s, "server_link", "Ссылка приватного сервера",
                   "roblox.com/share?code=…&type=Server. Нужна, чтобы бот сам перезаходил после вылета", width=52)
        self.switch(s, "roblox_fullscreen", "Держать Roblox на весь экран (F11)",
                    "Бот рассчитан на картинку 16:9 — в окне с панелью задач клики смещаются")
        self.entry(s, "force_resolution", "Разрешение экрана при старте фарма",
                   "1366 = 1366×768. Можно указать другой размер, например 1920x1080. "
                   "Для активного RDP размер задаётся при подключении. Пусто — оставить текущий.", width=14)
        bar = self.tk.Frame(p, bg=C["bg"])
        bar.pack(fill="x", pady=(4, 20))
        self.flat_button(bar, "Сохранить", self.save).pack(side="left")
        self.saved_lbl = self.label(bar, "", 9, "accent", bg="bg")
        self.saved_lbl.pack(side="left", padx=12)

    # --- Сток ---
    def _page_stock(self):
        p = self.scroll_page("stock")
        self.header(p, "Сток", "Research Shop в хабе: сток обновляется каждые полчаса (в XX:00 и XX:30)")
        s = self.section(p, "Автоскуп")
        self.switch(s, "stock_enabled", "Проверять сток",
                    "Сразу при старте фарма и после каждого обновления стока (между матчами) бот перезаходит на приватный сервер, идёт в Research Sector "
                    "к NPC с образцами и покупает отмеченные ниже предметы. Нужна ссылка приватного сервера.")
        self.switch(s, "stock_sell_trash", "Сдавать образцы перед покупкой",
                    "На вкладке Sample Exchange нажимает ALL и EXCHANGE - все образцы меняются на жетоны")
        self.switch(s, "stock_buy_new", "Покупать новые предметы",
                    "Предметы, которых бот ещё не видел. Выключено - он только добавит их в список ниже")
        self.entry(s, "stock_min_tokens", "Сколько жетонов оставлять",
                   "Бот не купит предмет, если после покупки останется меньше. 0 — тратить всё", width=10)
        bar = self.tk.Frame(s, bg=C["card"])
        bar.pack(fill="x", padx=18, pady=(4, 16))
        self.flat_button(bar, "Сохранить", self.save).pack(side="left")
        self.flat_button(bar, "Проверить при первой возможности", self.stock_now, color="card2", fg=C["text"]).pack(
            side="left", padx=10)
        self.stock_lbl = self.label(bar, "", 9, "muted")
        self.stock_lbl.pack(side="left", padx=4)
        s = self.section(p, "Предметы")
        self.label(s, "Галочка — покупать. Новые предметы появляются здесь после того, как бот увидит их в магазине; "
                   "название можно исправить (Enter — сохранить).", 8, "muted", wraplength=600,
                   justify="left").pack(anchor="w", padx=18, pady=(0, 8))
        self.stock_box = self.tk.Frame(s, bg=C["card"])
        self.stock_box.pack(fill="x", padx=18, pady=(0, 14))
        self.stock_imgs = {}
        self.stock_shown = None
        self._stock_rows()

    def stock_now(self):
        SETTINGS["stock_last"] = ""
        save_settings()
        self.stock_lbl.configure(text="проверю сток перед следующим матчем" if SETTINGS.get("stock_enabled")
                                 else "сначала включи «Проверять сток» и сохрани")

    def _stock_state(self):
        return tuple((k, v.get("price"), bool(v.get("buy")), v.get("name")) for k, v in stock_items().items())

    def sync_stock_vars(self):
        """Настройки стока поменяли из Discord - показать это в окне."""
        for k in ("stock_enabled", "stock_sell_trash", "stock_buy_new", "stock_min_tokens"):
            if k in self.vars:
                val = SETTINGS.get(k)
                self.vars[k].set(str(val) if k == "stock_min_tokens" else bool(val))

    def _stock_rows(self):
        """Перерисовать список предметов стока (галочка «покупать», картинка, название, цена)."""
        tk = self.tk
        items = stock_items()
        self.stock_shown = self._stock_state()
        for w in self.stock_box.winfo_children():
            w.destroy()
        for key, it in list(items.items()):
            row = tk.Frame(self.stock_box, bg=C["card2"])
            row.pack(fill="x", pady=3)
            var = tk.BooleanVar(value=bool(it.get("buy")))

            def flip(*_, k=key, v=var):
                cur = stock_items()
                if k in cur:
                    cur[k]["buy"] = bool(v.get())
                    save_settings()
                    self.stock_shown = self._stock_state()
            cb = tk.Checkbutton(row, variable=var, command=flip, bg=C["card2"], activebackground=C["card2"],
                                selectcolor=C["entry"], fg=C["accent"], activeforeground=C["accent"],
                                bd=0, highlightthickness=0, cursor="hand2")
            cb.pack(side="left", padx=(10, 6), pady=6)
            pic = self.stock_imgs.get(key)
            if pic is None:
                try:
                    from PIL import ImageTk
                    im = Image.open(os.path.join(HERE, "stock", key + ".png")).convert("RGB")
                    im.thumbnail((58, 76))
                    pic = self.stock_imgs[key] = ImageTk.PhotoImage(im)
                except Exception:
                    pic = None
            if pic is not None:
                tk.Label(row, image=pic, bg=C["card2"]).pack(side="left", padx=(0, 10), pady=4)
            name = tk.StringVar(value=str(it.get("name", key)))

            def rename(*_, k=key, v=name):
                cur = stock_items()
                text = v.get().strip()
                if k in cur and text and text != cur[k].get("name"):
                    cur[k]["name"] = text
                    save_settings()
                    self.stock_shown = self._stock_state()
            e = tk.Entry(row, textvariable=name, width=30, font=(FONT, 10), bg=C["card2"], fg=C["text"],
                         insertbackground=C["text"], bd=0, relief="flat", highlightthickness=0)
            e.pack(side="left", pady=6)
            e.bind("<Return>", rename)
            e.bind("<FocusOut>", rename)
            price = it.get("price")
            self.label(row, f"{price} жетонов" if price else "цена ещё неизвестна", 9, "muted", bg="card2").pack(
                side="right", padx=12)

            def remove(k=key):
                cur = stock_items()
                if k in cur and k not in STOCK_KNOWN:
                    del cur[k]
                    save_settings()
                    self._stock_rows()
            if key not in STOCK_KNOWN:
                x = tk.Label(row, text="✕", bg=C["card2"], fg=C["dim"], cursor="hand2", font=(FONT, 10))
                x.pack(side="right")
                x.bind("<Button-1>", lambda ev, f=remove: f())

    # --- Discord ---
    def _page_discord(self):
        p = self.scroll_page("discord")
        self.header(p, "Discord", "Уведомления о матчах и управление слэш-командами")
        s = self.section(p, "Подключение")
        self.switch(s, "afk_auto", "Автоматически отвечать на AFK CHECK")
        self.switch(s, "discord_enabled", "Включить Discord-бота")
        self.entry(s, "discord_token", "Токен бота", "Developer Portal → твоё приложение → Bot → Reset Token. "
                   "Никому не показывай.", secret=True)
        self.entry(s, "discord_channel", "ID канала", "ПКМ по каналу → «Копировать ID канала» "
                   "(нужен режим разработчика в настройках Discord)")
        st = self.tk.Frame(s, bg=C["card"])
        st.pack(fill="x", padx=18, pady=(4, 16))
        self.flat_button(st, "Сохранить и подключить", self.save).pack(side="left")
        self.dc_status = self.label(st, "", 9, "muted")
        self.dc_status.pack(side="left", padx=12)
        s = self.section(p, "Доступ и уведомления")
        self.entry(s, "discord_allowed", "Кто может управлять (ID пользователей через запятую)",
                   "Пусто — любой, кто видит канал")
        self.entry(s, "discord_ping", "Упоминать, если что-то сломалось (твой ID)", width=30)
        self.switch(s, "notify_match", "Сообщать о каждом матче")
        self.switch(s, "notify_screens", "Прикладывать скриншот к сообщению о матче")
        self.switch(s, "notify_actions", "Подробные отчёты",
                    "Каждая постановка (со скриншотом), прокачка, голосование и Rejoin")
        s = self.section(p, "Команды")
        for cmd, desc in [("/status", "состояние, матчи, деньги, шаг плана"), ("/screen", "скриншот Roblox"),
                          ("/log", "последние строки журнала"),
                          ("/stock", "сток: настройки, какие предметы покупать"), ("/start", "запустить фарм"),
                          ("/stop", "остановить фарм")]:
            r = self.tk.Frame(s, bg=C["card"])
            r.pack(fill="x", padx=18, pady=3)
            self.label(r, cmd, 10, "accent", "bold", width=8, anchor="w").pack(side="left")
            self.label(r, desc, 10, "muted").pack(side="left")
        self.label(s, "Бота приглашай со scope «bot» и «applications.commands».", 8, "dim").pack(
            anchor="w", padx=18, pady=(8, 16))

    # --- Журнал ---
    def _page_log(self):
        tk = self.tk
        p = tk.Frame(self.main, bg=C["bg"])
        self.pages["log"] = p
        h = self.header(p, "Журнал", "Всё, что делает бот. Полная версия — twd_log.txt")
        self.flat_button(h, "Открыть папку", self.open_folder, "card2", C["text"]).place(relx=1.0, y=4, anchor="ne")
        c = self.card(p)
        c.pack(fill="both", expand=True)
        self.log_txt = tk.Text(c, bg=C["card"], fg=C["text"], font=("Consolas", 9), bd=0, highlightthickness=0,
                               wrap="word", state="disabled")
        sb = self.scrollbar(c, self.log_txt.yview)
        self.log_txt.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.log_txt.pack(fill="both", expand=True, padx=14, pady=12)
        self._tags(self.log_txt)

    def open_folder(self):
        try:
            os.startfile(HERE)
        except Exception:
            pass

    # --- логика ---
    def save(self):
        for k, v in self.vars.items():
            val = v.get()
            if isinstance(DEFAULT_SETTINGS.get(k), bool):
                SETTINGS[k] = bool(val)
            elif isinstance(DEFAULT_SETTINGS.get(k), int):
                try:
                    SETTINGS[k] = max(0, int(str(val).strip() or 0))
                except ValueError:
                    v.set(str(SETTINGS.get(k)))
            else:
                SETTINGS[k] = str(val).strip()
        save_settings()
        apply_settings()
        self.saved_lbl.configure(text="✓ сохранено")
        self.root.after(2500, lambda: self.saved_lbl.configure(text=""))
        self.stock_lbl.configure(text="✓ сохранено")
        self.root.after(2500, lambda: self.stock_lbl.configure(text=""))
        self.restart_discord()

    def restart_discord(self):
        global LINK
        if self.link:
            self.link.stop()
        self.link = None
        LINK = NullLink()
        if SETTINGS.get("discord_enabled") and SETTINGS.get("discord_token") and SETTINGS.get("discord_channel"):
            self.link = DiscordLink(self)
            self.link.status = "подключаюсь…"
            LINK = self.link
            self.link.start()

    def start_farm(self):
        """Можно вызывать из любого потока (кнопка, F8, /start)."""
        with self.mode_lock:
            if self.team and self.team.active():
                log("Сначала останови помощника Wastelands")
                return False
            return self._start_farm()

    def _start_farm(self):
        if self.thread is not None and self.thread.is_alive():
            return False
        self.bot = Bot(use_speed=bool(SETTINGS.get("use_speed", True)), hotkeys=False)
        self.bot.start.set()
        STATS.started_at = time.time()
        STATS.matches = 0
        STATS.state = "waiting"
        self.thread = threading.Thread(target=self._worker, args=(self.bot,), daemon=True)
        self.thread.start()
        return True

    def stop_farm(self):
        if self.thread is None or not self.thread.is_alive():
            return False
        STATS.state = "stopping"
        self.bot.abort.set()
        return True

    def toggle(self):
        if not self.stop_farm():
            self.start_farm()
        self._draw_btn()

    def _worker(self, bot):
        try:
            bot.run(int(SETTINGS.get("loops", 0) or 0))
            LINK.send("Фарм завершён", f"Сыграно матчей: {STATS.matches}", COLOR_INFO)
        except Aborted:
            log("остановлено")
            LINK.send("⏹ Фарм остановлен", f"Сыграно матчей: {STATS.matches}", COLOR_WARN)
        except Exception as e:
            import traceback
            log("ОШИБКА: " + "".join(traceback.format_exception_only(type(e), e)).strip())
            try:
                with open(os.path.join(HERE, "twd_log.txt"), "a", encoding="utf-8") as f:
                    f.write(traceback.format_exc() + "\n")
            except OSError:
                pass
            LINK.send("Бот упал с ошибкой", f"`{e}`", COLOR_BAD, grab_game_window(), ping=True)
        finally:
            bot.release_all_inputs() if hasattr(bot, "release_all_inputs") else None
            STATS.state = "idle"
            STATS.match_started = None
            STATS.step_total = 0
            save_settings()

    def _on_hotkey(self, key):
        if key == START_KEY and self.current != "wastelands":
            self.start_farm()
        elif key == ABORT_KEY:
            self.stop_farm()
            if self.team and self.team.active():
                self.team.stop.set()
                if self.team.match.run:
                    self.root.after(0, self.team.stop_match)

    def tick(self):
        if self.team_install is not None and not self.team_install.empty():
            result = self.team_install.get()
            self.team_install = None
            if isinstance(result, Exception):
                self.team_error(result)
            else:
                try:
                    self.mount_team(result)
                except (OSError, ImportError) as exc:
                    self.team_error(exc)
        while _gui_queue:
            line = _gui_queue.popleft()
            self._append(self.log_txt, line, 3000)
            self._append(self.mini_log, line, 200)
        try:
            if self.stock_shown != self._stock_state():
                self._stock_rows()                      # бот увидел в магазине новый предмет или цену
            last = SETTINGS.get("stock_last")
            if last and self.stock_lbl.cget("text") in ("", getattr(self, "_stock_last_txt", "")):
                self._stock_last_txt = f"последняя проверка: сток {last[-5:]}"
                self.stock_lbl.configure(text=self._stock_last_txt)
        except Exception:
            pass
        running = self.thread is not None and self.thread.is_alive()
        if not running and STATS.state != "idle":
            STATS.state = "idle"
        state = STATS.state if running else "idle"
        col, txt = {"idle": (C["dim"], "остановлен"), "waiting": (C["yellow"], "в лобби, иду в матч"),
                    "stock": (C["blue"], "проверяю сток в хабе"),
                    "running": (C["accent"], "фармит"), "stopping": (C["red"], "останавливается…")}.get(
            state, (C["dim"], state))
        self.dot.itemconfigure(self.dot_id, fill=col)
        self.state_lbl.configure(text=txt, fg=col if state != "idle" else C["muted"])
        if getattr(self, "_was_running", None) != running:
            self._was_running = running
            self._draw_btn()
        self.stat["matches"].configure(text=str(STATS.matches))
        self.stat["total"].configure(text=str(STATS.total_matches))
        self.stat["uptime"].configure(text=_fmt_dur(time.time() - STATS.started_at)
                                      if running and STATS.started_at else "—")
        self.stat["money"].configure(text=f"${STATS.money:,}" if running and STATS.money is not None else "—")
        if running and STATS.match_started:
            self.match_time.configure(text=_fmt_dur(time.time() - STATS.match_started))
            self.step_lbl.configure(text=f"Шаг {STATS.step}/{STATS.step_total}: {STATS.step_text}"
                                    if STATS.step_total else "идёт матч")
            frac = STATS.step / STATS.step_total if STATS.step_total else 0
        else:
            self.match_time.configure(text="")
            self.step_lbl.configure(text="в лобби / загрузка" if running else "ожидание старта")
            frac = 0
        w = max(10, self.bar.winfo_width())
        self.bar.delete("all")
        _rounded(self.bar, 0, 0, w, 10, 5, fill=C["line"])
        if frac > 0:
            _rounded(self.bar, 0, 0, max(10, int(w * frac)), 10, 5, fill=C["accent"])
        self._draw_units()
        if self.link:
            ok = self.link.ok
            self.dc_status.configure(text=("● " if ok else "○ ") + self.link.status,
                                     fg=C["accent"] if ok else C["muted"])
        else:
            self.dc_status.configure(text="○ выключен", fg=C["muted"])
        self.root.after(250, self.tick)

    def on_close(self):
        self.stop_farm()
        self.hotkeys.stop()
        if self.team:
            self.team.close()
        try:
            self.save_quiet()
        finally:
            if self.link:
                self.link.stop()
            self.root.after(300, self.root.destroy)

    def save_quiet(self):
        save_settings()

    def run(self):
        self.root.mainloop()


def diag():
    """Что бот видит на экране прямо сейчас (запускать, когда Roblox открыт)."""
    bot = Bot()
    log("Переключись в Roblox и нажми F8 - сниму экран и проверю.")
    while not bot.start.wait(0.1):
        pass
    bot.check()
    img = bot.grab()
    img.save(os.path.join(HERE, "diag_screen.png"))
    log(f"игровая область: {img.width}×{img.height} пикселей; границы окна: {bot.rect()}")
    log(f"деньги: {bot.money()}")
    log(f"финальный экран: {bot.end_screen()}; выбор сложности: {bot.vote_screen()} "
        f"(отличие {vote_diff(bot.grab(VOTE_BOX)):.1f}); READY: {bot.ready_visible()}")
    view = analyze_screen(img)
    log(f"лобби: кнопка {view['button']}, иконка TELEPORT {view['tp_icon']}, карточка Deployment "
        f"{view['deploy_card']}, синих кругов {len(view['pads'])}, окно Matchmaking {view['dialog']}")
    mask = path_mask(img)
    Image.fromarray((mask * 255).astype(np.uint8)).save(os.path.join(HERE, "diag_path.png"))
    if mask.mean() > 0.01:
        ang, shift, score, scale = estimate_rotation(mask)
        log(f"дорожка видна: поворот {ang:+.1f} град, масштаб {scale:.2f}, сдвиг {shift}, совпадение {score:.2f}")
    else:
        log("дорожку не видно (возьми юнита в руку, чтобы она подсветилась)")


def main():
    parser = argparse.ArgumentParser(description="TWD Farm - бот для Toilet Warfare Defense (HARD)")
    parser.add_argument("cmd", nargs="?", default="app", choices=["app", "wastelands", "run", "diag"],
                        help="app - окно приложения (по умолчанию), run - консольный режим, diag - диагностика")
    parser.add_argument("--loops", type=int, default=None, help="сколько матчей сыграть (0 - бесконечно)")
    parser.add_argument("--no-speed", action="store_true", help="не нажимать 1.5x")
    parser.add_argument("--resume", action="store_true", help="сразу начать фарм (после автообновления)")
    args = parser.parse_args()
    enable_dpi_awareness()
    load_settings()
    if args.cmd in ("app", "wastelands", "run") and self_update():
        restart_app(resume=args.resume)
    if args.cmd in ("app", "wastelands"):
        app = FarmApp()
        if args.cmd == "wastelands":
            app.show("wastelands")
        if args.resume:
            app.root.after(2500, app.start_farm)
        app.run()
        return
    try:
        if args.cmd == "diag":
            diag()
        else:
            loops = args.loops if args.loops is not None else int(SETTINGS.get("loops", 0) or 0)
            Bot(use_speed=not args.no_speed and SETTINGS.get("use_speed", True)).run(loops)
    except Aborted:
        log("остановлено (F6)")
    finally:
        save_settings()


if __name__ == "__main__":
    sys.modules.setdefault("twd_bot", sys.modules[__name__])
    main()
