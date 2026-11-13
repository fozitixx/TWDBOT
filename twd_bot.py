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
VERSION = "5.6.3 (после продажи юнитов титан ставится сразу, без ожидания суммы на экране)"
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
SPEED_POINT = (0.9602, 0.1392)                # кнопка 1.5x

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
    "c3b": (0.831, 0.3651),
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
                "c3b": (3.00, 0.75)}          # второй титан там же: дальше вдоль дороги, по которой идёт босс
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


def build_plan(mode, slots):
    """План матча. Если в слотах Titan TV Man, а Titan Cameraman нет - он встаёт на его место
    (имя юнита в плане остаётся tcam, меняется только тип)."""
    global MAIN_TITAN
    MAIN_TITAN = "ttv" if ("ttv" in slots and "tcam" not in slots) else "tcam"
    plan = _build_plan(mode, slots)
    if MAIN_TITAN == "ttv":
        for st in plan:
            if st.get("type") == "tcam":
                st["type"] = "ttv"
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
            *_u("pl1", "pl2", "pl3", "pl4"),
            _p("tv2", "tv", "n6", priority="Flying"),
            _p("tv3", "tv", "n7", priority="Flying"),
            _p("tv4", "tv", "n8", priority="Flying"),
            *_u("tv1", "tv2", "tv3", "tv4"),
            # --- дальше порядок из видео после патча (босс 100 000 HP) ---
            # фермы сразу после кучки (к концу 9-й волны стоят все четыре) и до 3 ур. - раньше титана:
            # на их доход ставятся оба титана и копится запас к боссу
            *[_p(f, "farm", "f" + f[-1]) for f in farms],
            *_u(*farms), *_u(*farms), *_u(*farms),
            # 12-я волна: Titan Speakerman внутри 2-го поворота, ради него продаются только два TV
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
#   +3    Shield Mode у Titan Cameraman - сразу, как с него спадёт стартовое оглушение
#   +5    Motivation первого плунжера, +15 - второго
#   +25   новый плунжер у 2-го поворота, качается до максимума, +34 - его Motivation
#   +37   Aerial Attack у Titan Speakerman
#   ~+51  босс дошёл до 2-го поворота (оглушил Titan Speakerman): Titan Cameraman продаётся
#         и ставится дальше по пути, у 3-го поворота
#   +76   плунжеры продаются - деньги в нового титана
# Каждое нажатие способности проверяется по кнопке (появился отсчёт - сработало) и повторяется.
# Перестановка Titan Cameraman в бою с боссом: когда босс дошёл до 2-го поворота (там он оглушает
# Titan Speakerman), титан у первого угла уже не нужен - он продаётся и ставится впереди по пути
# босса, у 3-го поворота. Заодно продаются фермы и два плунжера из первого угла - деньги в нового титана.
NIGHTMARE_START_CASH = 800                   # с этой суммой начинается матч на NIGHTMARE (на EASY - $650)
# Бой с боссом после патча (100 000 HP), времена - секунды после появления полосы босса, из видео:
BOSS_SHIELD_AT = 16.0          # Shield Mode у Titan Cameraman
BOSS_AERIAL_AT = 40.0          # 8-й уровень и Aerial Attack у Titan Speakerman (в видео Aerial на +54)
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


ABILITY_LEVEL = {"tcam": 8, "ttv": 7, "tspk": 7, "plunger": 7}   # у Titan Speakerman кнопка способности есть уже на 7 ур.

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
    want = str(SETTINGS.get("force_resolution", "")).lower().replace(" ", "").replace("×", "x")
    if "x" not in want:
        return
    try:
        w, h = (int(v) for v in want.split("x", 1))
    except ValueError:
        return
    cur = screen_size()
    if cur == (w, h):
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
        if a - prev_end > 1.0 * h:
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


def read_money_image(img):
    glyphs = _segment(np.asarray(img.convert("RGB")))
    if not glyphs or not (2 <= len(glyphs) <= 8):
        return None
    templates = _get_templates()
    chars = []
    for gl, asp in glyphs:
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


# ---------- юниты, слоты, режимы ----------

# цена постановки, цены прокачек (ур.0->1, 1->2, ...) и выручка от продажи по уровням
UNITS = {
    "tcam":    {"title": "Titan Cameraman", "short": "Titan Cam",       "icon": "🎥", "price": 7500,
                "up": [3250, 5000, 13650, 13600, 21025, 20975, 25000, 17500],
                "sell": [3750, 5375, 7875, 14700, 21500, 32015, 42500, 55000, 63750]},
    # Titan TV Man - замена Titan Cameraman (цены из видео): Teleport с 4 ур., Hook and Punch с 7 ур.
    "ttv":     {"title": "Titan TV Man", "short": "Titan TV",        "icon": "📺", "price": 8000,
                "up": [3250, 5250, 14400, 14350, 22275, 22225, 26500, 18750],
                "sell": [4000, 5625, 8250, 15450, 22625, 33765, 44875, 58125, 67500]},
    "tspk":    {"title": "Titan Speakerman", "short": "Titan Speaker",      "icon": "📢", "price": 7250,
                "up": [3000, 4750, 13400, 13350, 20650, 20600, 24500, 17500],
                "sell": [3625, 5125, 7500, 14200, 20875, 31200, 41500, 53750, 62500]},
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

MODES = {
    "hard":      {"title": "HARD",      "waves": 25, "need": ["tspk", "tv"], "need_any": [["tcam", "ttv"], ["plunger", "speaker"]]},
    "nightmare": {"title": "NIGHTMARE", "waves": 30, "need": ["tspk", "tv", "plunger", "farm"], "need_any": [["tcam", "ttv"]]},
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


def _read_green_number(m, tol=0.16):
    """Число из маски зелёного текста одной надписи ($7,500 -> 7500). Запятая отбрасывается."""
    comps = _components(m)
    if not comps:
        return None
    h = max(c[3] - c[1] for c in comps)
    if h < 6:
        return None
    comps = sorted((c for c in comps if c[3] - c[1] >= 0.6 * h), key=lambda c: c[0])
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
            sc = float(((v - tv) ** 2).mean()) + 0.6 * (asp - ta) ** 2
            if sc < score:
                best, score = ch, sc
        if score > tol:
            return None
        chars.append(best)
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
    return sells.index(price) if price in sells else None


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
    return slots, prices


def missing_units(slots, mode):
    md = MODES[mode]
    miss = [UNITS[t]["title"] for t in md["need"] if t not in slots]
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


def open_private_link():
    """Открыть приватный сервер прямо в клиенте Roblox (deeplink), при ошибке - через браузер."""
    for link in (SERVER_DEEPLINK, SERVER_LINK):
        if not link:
            continue
        try:
            os.startfile(link)
            return True
        except Exception as e:
            log(f"  не получилось открыть {link.split(':')[0]}-ссылку: {e}")
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
    "focus_after": 3,
    "move_to_primary": True,
    "private_only": True,
    "server_link": "",           # ссылка приватного сервера (roblox.com/share?code=...&type=Server)
    "auto_update": True,         # обновляться с GitHub при запуске и между матчами
    "mode": "hard",              # hard / nightmare
    "force_resolution": "",      # например "1920x1080": выставить разрешение экрана при старте
    "roblox_fullscreen": True,   # держать Roblox на весь экран (F11): ровно 16:9, как в эталоне
    "discord_enabled": False,
    "discord_token": "",
    "discord_channel": "",
    "discord_allowed": "",       # ID через запятую; пусто - все в канале
    "discord_ping": "",
    "notify_match": True,
    "notify_screens": True,
    "notify_actions": True,      # постановки, прокачки, голосование, Rejoin
    "total_matches": 0,
}
SETTINGS = dict(DEFAULT_SETTINGS)


# ---------- автообновление с GitHub ----------
UPDATE_REPO = "fozitixx/TWDBOT"
UPDATE_BASE = f"https://raw.githubusercontent.com/{UPDATE_REPO}/main/"
UPDATE_EVERY = 20 * 60          # между матчами проверять не чаще, чем раз в 20 минут
_update_checked = 0.0


def version_tuple(text):
    """'5.6.0 (описание)' -> (5, 6, 0)"""
    import re as _re
    m = _re.match(r"\s*(\d+(?:\.\d+)*)", str(text))
    return tuple(int(x) for x in m.group(1).split(".")) if m else (0,)


def _http_get(url, timeout=8):
    import urllib.request
    req = urllib.request.Request(url + f"?t={int(time.time())}", headers={"User-Agent": "TWD-Farm-updater",
                                                                           "Cache-Control": "no-cache"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


def self_update(quiet=False):
    """Сверить версию с репозиторием и, если там новее, заменить свой файл.
    -> номер новой версии (нужен перезапуск) или None. Любая ошибка - просто работаем дальше на старой."""
    global _update_checked
    _update_checked = time.time()
    if not SETTINGS.get("auto_update", True):
        return None
    try:
        info = json.loads(_http_get(UPDATE_BASE + "version.json").decode("utf-8-sig"))
        new = str(info.get("version", ""))
        if version_tuple(new) <= version_tuple(VERSION):
            if not quiet:
                log(f"обновлений нет (версия {VERSION.split()[0]} - последняя)")
            return None
        log(f"на GitHub есть версия {new} (сейчас {VERSION.split()[0]}) - скачиваю"
            + (f": {info.get('notes')}" if info.get("notes") else ""))
        data = _http_get(UPDATE_BASE + str(info.get("file", "twd_bot.py")), timeout=30)
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
               "tcam": "🎥 Титан-Камера", "tspk": "📢 Титан-Спикер"}


MAIN_TITAN = "tcam"          # какой титан стоит на месте Titan Cameraman в этом матче: "tcam" или "ttv"


def unit_title(name):
    if name.startswith("tcam") and MAIN_TITAN == "ttv":
        return "📺 Титан-ТВ" + name[4:]
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

    def stats_fields(self):
        up = time.time() - STATS.started_at if STATS.started_at else 0
        f = [("Состояние", {"idle": "⏸ остановлен", "waiting": "⏳ лобби / загрузка", "running": "▶ фармит",
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
        self.timelapse()
        self.check_disconnect()
        if getattr(self, "bar_missing", 0) >= 3 and STATS.match_started:
            # 45 с на экране нет полосы здоровья базы: матч кончился, а итоговый экран не узнан
            # (его закрыло окно награды или игра уже вернула в лобби). Без этого бот ждал бы денег вечно.
            self.bar_missing = 0
            log("полосы здоровья базы нет уже 45 с - матч закончился (окно награды или лобби)")
            raise MatchEnded

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
            return ImageGrab.grab(bbox=bbox, all_screens=True)
        except TypeError:
            return ImageGrab.grab(bbox=bbox)

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
        w, h = img.size
        a = np.asarray(img.convert("RGB").resize((LOBBY_W, max(1, round(LOBBY_W * h / w))), Image.BOX)).astype(np.int16)
        r, g, b = a[..., 0], a[..., 1], a[..., 2]
        if mode == "nightmare":
            mask, lo, hi = (b > 30) & (b > 2 * g + 8) & (b > 1.25 * r + 4) & (r > g), 0.6, 0.95
        else:
            mask, lo, hi = (r > 35) & (r > 3 * g + 5) & (r > 3 * b + 5), 0.4, 0.75
        blobs = _blobs(mask)
        cards = [x for x in blobs if 0.08 <= x["w"] <= 0.2 and 0.35 <= x["h"] <= 0.7 and lo < x["cx"] < hi]
        for c in cards:
            for v in blobs:
                if (abs(v["cx"] - c["cx"]) < 0.02 and 0.03 <= v["h"] <= 0.1 and abs(v["w"] - c["w"]) < 0.04
                        and v["cy"] > c["cy"] + c["h"] / 2):
                    return (v["cx"], v["cy"])
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
        if lvl_u is None and up is not None and price is None:
            near = [i for i, u in enumerate(ups) if abs(u - up) <= 4]
            if len(near) == 1:
                lvl_u = near[0]
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
        if self.use_speed:
            self.close_player_list()
            log("включаю скорость 1.5x")
            self.click(SPEED_POINT, dwell=0.35)
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
            known = [PRICE_TO_TYPE.get(p) for p in prices if p in PRICE_TO_TYPE]
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

    def use_ability(self, name, tries=None, sel_tries=3):
        """Нажать способность юнита. У плунжера проверяется, что на кнопке появился отсчёт (сработала);
        у титанов кнопка после нажатия не меняется, поэтому нажимается один раз без ожидания.
        -> True (нажата/сработала/уже действует), False (не получилось), "cooldown" (на перезарядке),
        "stunned" (юнит оглушён - способность сейчас не нажать)."""
        name = getattr(self, "alias", {}).get(name, name)
        if name not in self.units:
            return False
        utype = self.types.get(name)
        titan = utype in ("tcam", "ttv", "tspk")
        need = ABILITY_LEVEL.get(utype)
        if need and self.levels.get(name, 0) < need:
            log(f"  способность {name} ещё не открыта (ур. {self.levels.get(name, 0)} из {need})")
            return False
        if self.unit_stunned(name):
            return "stunned"
        if tries is None:
            tries = 1 if titan else 3
        ok_sel, lvl, _price = self.select_checked(name, tries=sel_tries)
        if not ok_sel:
            log(f"  не получается выделить {name} - способность не нажимаю")
            return False
        if need and lvl is not None and lvl < need:
            self.levels[name] = lvl
            log(f"  способность {name} ещё не открыта (на самом деле {lvl} ур. из {need})")
            return False
        self.hover(ABILITY_POINT)
        self.sleep(0.25)
        state = ability_state(self.grab())
        if state == "active":
            log(f"  способность {name} уже действует")
            self.hover(IDLE_POINT)
            return True
        if state == "cooldown":
            log(f"  способность {name} на перезарядке")
            self.hover(IDLE_POINT)
            return "cooldown"
        hook = utype == "ttv"
        if hook:
            # Hook and Punch бьёт по цели титана: на время удара приоритет Boss, чтобы крюк точно ушёл в босса
            for _ in range(PRIORITIES.index("Boss")):
                self.key("r")
                self.sleep(0.12)
            self.sleep(0.35)
        for attempt in range(tries):
            self.click(ABILITY_POINT, dwell=0.2)
            self.selected = name                  # клик по кнопке панели выделения не снимает
            if hook:
                self.sleep(0.6)
                for _ in range(len(PRIORITIES) - PRIORITIES.index("Boss")):
                    self.key("r")                 # Boss -> First
                    self.sleep(0.12)
            if titan:
                self.sleep(0.3)
                self.snap(f"abil_{name}")
                log(f"  способность нажата: {name}")
                report(f"✨ Способность: {unit_title(name)}", "", COLOR_INFO)
                self.hover(IDLE_POINT)
                return True
            for _ in range(5):                    # до ~1.2 с ждём отсчёт на кнопке
                self.sleep(0.25)
                if ability_state(self.grab()) != "ready":
                    log(f"  способность сработала: {name}")
                    report(f"✨ Способность: {unit_title(name)}", "", COLOR_INFO)
                    self.hover(IDLE_POINT)
                    return True
            if attempt == 0:
                self.snap(f"abil_{name}_fail")
            log(f"  способность {name}: отсчёт на кнопке не появился - нажимаю ещё раз")
        self.hover(IDLE_POINT)
        log(f"  способность {name} НЕ подтвердилась")
        return False

    def teleport(self, name, at):
        """Teleport у Titan TV Man: способность работает как постановка - навести и кликнуть, Q - отмена.
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
            if self.holding is not None or time.time() - STATS.match_started < 600:
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
                return time.perf_counter() - t0

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
                if self.unit_stunned(real):
                    if key not in self.boss_waiting:
                        self.boss_waiting.add(key)
                        log(f"БОСС +{el():.0f}с: {unit} оглушён - способность нажму, когда очнётся")
                    return                        # оглушение - не неудача, попытку не трачу
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
                elif res and res != "stunned":
                    done.add(key)

            # здоровье босса в журнал раз в ~10 с - чтобы потом было видно, как шёл бой
            if el() - getattr(self, "boss_hp_logged", -99) >= 10:
                self.boss_hp_logged = el()
                hp_now = self.boss_hp()
                if hp_now is not None:
                    log(f"БОСС +{el():.0f}с: здоровье босса {hp_now:.0%}")

            # 1. Shield Mode у Titan Cameraman (в видео после патча - на +17 с, когда босс уже под огнём)
            ttv = self.types.get("tcam") == "ttv"
            mt = "ttv" if ttv else "tcam"
            if ttv:
                # Titan TV Man: Hook and Punch (14 320 урона, перезарядка 35 с) - пока босс в его радиусе
                if "move" not in done:
                    if el() >= BOSS_SHIELD_AT:
                        ability("hook1", "tcam", 3)
                    if el() >= BOSS_SHIELD_AT + 26 and el() < BOSS_TCAM_MOVE_MIN - 4:
                        ability("hook2", "tcam", 2)
                elif getattr(self, "boss_moved_at", None):
                    since = time.perf_counter() - self.boss_moved_at
                    if since >= 6:
                        ability("hook3", "tcam", 3)
                    if since >= 34:
                        ability("hook4", "tcam", 3)
            elif el() >= BOSS_SHIELD_AT:
                ability("shield1", "tcam", 3)
            # 2. Aerial Attack у Titan Speakerman (удар по области ~10 000) - когда босс у 2-го поворота
            #    Переезд Cameraman важнее: пока он не сделан, на Aerial не больше двух попыток.
            if (el() >= BOSS_AERIAL_AT and el() < 84.0 and "move2" not in done and "aerial" not in done
                    and "tspk" in self.units
                    and ("move" in done or el() < BOSS_TCAM_MOVE_MIN or tries.get("aerial", 0) < 2)):
                if self.levels.get("tspk", 0) < 8 and not self.unit_stunned("tspk"):
                    self.drop()
                    log(f"БОСС +{el():.0f}с: Speakerman -> 8 ур. и сразу Aerial Attack")
                    self.upgrade_now("tspk")          # выделение остаётся на нём - способность жмётся без нового клика
                ability("aerial", "tspk", 4)
            # 6. босс дошёл до 2-го поворота - Titan Cameraman переезжает вперёд, к 3-му повороту.
            #    Признак: босс оглушил Titan Speakerman, стоящего у 2-го поворота. Оглушённого юнита
            #    игра продать не даёт, поэтому если сам Cameraman ещё оглушён - жду, пока очнётся.
            if BOSS_MOVE_TCAM and "move" not in done and el() >= BOSS_TCAM_MOVE_MIN and "tcam" in self.units:
                if not getattr(self, "boss_at_turn", False) and self.unit_stunned("tspk"):
                    self.boss_at_turn = True
                    log(f"БОСС +{el():.0f}с: босс у 2-го поворота (оглушил Titan Speakerman)")
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
                        # Titan TV Man переезжает телепортом: без продажи, со всеми уровнями
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
                    and "tspk" in self.slots):
                hp = self.boss_hp()
                if hp is not None and hp < 0.08:
                    done.add("move2")
                    log(f"БОСС +{el():.0f}с: у босса осталось {hp:.0%} - Speakerman не переставляю")
                elif self.unit_stunned("tspk"):
                    pass
                elif attempt("move2_try", 2):
                    log(f"БОСС +{el():.0f}с: переставляю Titan Speakerman к 3-му повороту"
                        + (f" (у босса {hp:.0%})" if hp is not None else ""))
                    self.drop()
                    if self.sell_unit("tspk"):
                        done.add("move2")
                        self.sleep(0.3)
                        if not self.place({"unit": "tspk", "type": "tspk", "at": "c3b", "quick": 12, "nowait": True}):
                            log("  у третьего поворота не встал - возвращаю Speakerman на прежнее место")
                            self.place({"unit": "tspk", "type": "tspk", "at": "t1n", "nowait": True})
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
        for key, icon, name in [("home", "⌂", "Главная"), ("settings", "⚙", "Настройки"),
                                ("discord", "✉", "Discord"), ("log", "≡", "Журнал")]:
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
        self._page_settings()
        self._page_discord()
        self._page_log()

    def show(self, key):
        for k, p in self.pages.items():
            p.pack_forget()
        self.pages[key].pack(fill="both", expand=True, padx=26, pady=22)
        for k, b in self.nav.items():
            b.configure(bg=C["card"] if k == key else C["side"], fg=C["text"] if k == key else C["muted"])
        self.current = key

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
        self.mode_sub.configure(text=f"Invaded City · {MODES[mode]['title']}", fg=col)
        self.mode_note.configure(text=f"{MODES[mode]['waves']} волн")
        for w in self.units_row.winfo_children():
            w.destroy()
        checked = bool(STATS.prices)
        groups = [[t] for t in MODES[mode]["need"]] + MODES[mode]["need_any"]
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
        s = self.section(p, "Матчи")
        self.entry(s, "loops", "Сколько матчей сыграть", "0 — без ограничений", width=8)
        self.switch(s, "use_speed", "Включать скорость 1.5x", "Кнопка справа сверху в начале матча")
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
                   "Например 1920x1080. Пусто — не трогать. Полезно на ПК без монитора (RDP/tscon)", width=14)
        bar = self.tk.Frame(p, bg=C["bg"])
        bar.pack(fill="x", pady=(4, 20))
        self.flat_button(bar, "Сохранить", self.save).pack(side="left")
        self.saved_lbl = self.label(bar, "", 9, "accent", bg="bg")
        self.saved_lbl.pack(side="left", padx=12)

    # --- Discord ---
    def _page_discord(self):
        p = self.scroll_page("discord")
        self.header(p, "Discord", "Уведомления о матчах и управление слэш-командами")
        s = self.section(p, "Подключение")
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
                          ("/log", "последние строки журнала"), ("/start", "запустить фарм"),
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
        if key == START_KEY:
            self.start_farm()
        elif key == ABORT_KEY:
            self.stop_farm()

    def tick(self):
        while _gui_queue:
            line = _gui_queue.popleft()
            self._append(self.log_txt, line, 3000)
            self._append(self.mini_log, line, 200)
        running = self.thread is not None and self.thread.is_alive()
        if not running and STATS.state != "idle":
            STATS.state = "idle"
        state = STATS.state if running else "idle"
        col, txt = {"idle": (C["dim"], "остановлен"), "waiting": (C["yellow"], "в лобби, иду в матч"),
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
    log(f"окно: {bot.rect()}")
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
    parser.add_argument("cmd", nargs="?", default="app", choices=["app", "run", "diag"],
                        help="app - окно приложения (по умолчанию), run - консольный режим, diag - диагностика")
    parser.add_argument("--loops", type=int, default=None, help="сколько матчей сыграть (0 - бесконечно)")
    parser.add_argument("--no-speed", action="store_true", help="не нажимать 1.5x")
    parser.add_argument("--resume", action="store_true", help="сразу начать фарм (после автообновления)")
    args = parser.parse_args()
    enable_dpi_awareness()
    load_settings()
    if args.cmd in ("app", "run") and self_update():
        restart_app(resume=args.resume)
    if args.cmd == "app":
        app = FarmApp()
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
    main()
