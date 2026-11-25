"""Host editor for the six titan positions on a calibrated game frame."""
import base64
import io
import time
import tkinter as tk
from tkinter import ttk

import numpy as np
from PIL import Image, ImageTk

from twd_bot import C, FONT
from wastelands import button, text
from wastelands_team import PLAYERS, TITANS, titan_layout
from wastelands_view import map_point, placement_in_view, screen_point


def decode_map_frame(packet):
    if not isinstance(packet, dict) or packet.get("player") not in PLAYERS:
        raise ValueError("Некорректный кадр карты")
    try:
        origin, axes = (np.asarray(part, dtype=float) for part in packet["pose"])
        if (origin.shape != (2,) or axes.shape != (2, 2) or not np.isfinite(origin).all()
                or not np.isfinite(axes).all() or abs(np.linalg.det(axes)) < 1e-12
                or np.linalg.cond(axes) > 30):
            raise ValueError
        data = packet["image"]
        if not isinstance(data, str) or len(data) > 790000:
            raise ValueError
        with Image.open(io.BytesIO(base64.b64decode(data, validate=True))) as thumb:
            if thumb.format != "JPEG" or not (0 < thumb.width <= 960 and 0 < thumb.height <= 540):
                raise ValueError
            return thumb.convert("RGB"), (origin, axes)
    except (KeyError, TypeError, ValueError, OSError, OverflowError) as exc:
        raise ValueError("Не удалось прочитать кадр и привязку дороги") from exc


class TitanMapEditor:
    def __init__(self, app):
        self.app = app
        self.win = win = tk.Toplevel(app.root)
        win.title("Wastelands · Карта титанов")
        win.configure(bg=C["bg"], padx=10, pady=8)
        win.geometry(f"{min(1020, win.winfo_screenwidth()-40)}x{min(760, win.winfo_screenheight()-88)}")
        self.packet = self.image = self.pose = self.photo = self.request = None
        self.bounds = (0, 0, 0, 0)
        self.draft = dict(app.match.manual_titans)
        self.baseline = dict(self.draft)
        self.selected = tk.StringVar(win, "1/amplifier")
        online = [p for p, c in app.match.clients.copy().items() if time.monotonic()-c["seen"] < 8]
        self.source = tk.IntVar(win, min(online, default=1))

        top = tk.Frame(win, bg=C["bg"])
        top.pack(fill="x")
        text(top, "Экран твинка").pack(side="left")
        ttk.Combobox(top, textvariable=self.source, values=PLAYERS, width=3, state="readonly").pack(side="left", padx=6)
        self.capture = button(top, "Получить кадр", self.get_frame)
        self.capture.pack(side="left")
        self.caption = text(top, "", size=9, color="muted")
        self.caption.pack(side="left", padx=8)

        controls = tk.Frame(win, bg=C["bg"])
        controls.pack(fill="x", pady=(6, 3))
        self.choices = {}
        for column, player in enumerate(PLAYERS):
            group = tk.Frame(controls, bg=C["card"], padx=4, pady=3)
            group.grid(row=0, column=column, sticky="ew", padx=(0, 4))
            controls.columnconfigure(column, weight=1)
            text(group, f"Твинк {player}", bold=True).pack()
            for unit in TITANS:
                key = f"{player}/{unit}"
                choice = tk.Radiobutton(group, value=key, variable=self.selected, indicatoron=False,
                                        bg=C["card2"], fg=C["text"], selectcolor=C["line"],
                                        activebackground=C["line"], activeforeground=C["text"],
                                        font=(FONT, 9), relief="flat", bd=0, command=self.draw)
                choice.pack(side="left", expand=True, fill="x", padx=1)
                self.choices[key] = choice

        bottom = tk.Frame(win, bg=C["bg"])
        bottom.pack(side="bottom", fill="x", pady=(5, 0))
        button(bottom, "Сохранить точки", self.save, primary=True).pack(side="right")
        button(bottom, "Снять метку", self.clear).pack(side="right", padx=5)
        self.note = text(bottom, "Выбери титана и нажми по земле на карте.", size=9, wraplength=410)
        self.note.pack(side="left", fill="x", expand=True)
        self.canvas = tk.Canvas(win, bg=C["entry"], highlightthickness=0, cursor="crosshair")
        self.canvas.pack(fill="both", expand=True)
        self.canvas.bind("<Configure>", lambda _: self.draw())
        self.canvas.bind("<Button-1>", self.pick)
        if app.titan_frame:
            try:
                self.show_frame(app.titan_frame)
            except ValueError as exc:
                self.note.configure(text=str(exc))
        if self.image is None and online and app.match.run:
            self.get_frame()
        self.draw()

    def get_frame(self):
        player = self.source.get()
        try:
            request = self.app.match.command(player, "map_snapshot")
        except ValueError as exc:
            self.note.configure(text=str(exc))
            return
        self.request = player, request, self.app.match.run, time.monotonic()+19
        self.capture.configure(state="disabled")
        self.note.configure(text=f"Твинк {player} сверяет положение дороги…")

    def poll(self):
        with self.app.match.lock:
            if self.baseline != self.app.match.manual_titans:
                self.merge_learned_points()
                self.draw()
        if self.request is None:
            return
        player, request, run, deadline = self.request
        match = self.app.match
        with match.lock:
            frame = match.map_frame
            current_run = match.run
            pending = match.pending.get(player, {}).get("id")
            message = match.results.get(player) or "Запроси кадр снова."
        if current_run != run:
            message = "Матч сменился. Можно запросить новый кадр."
        elif frame and frame[0] == request:
            try:
                self.show_frame(frame[1])
                message = "Выбери титана и нажми по земле на карте."
            except ValueError as exc:
                message = str(exc)
        elif time.monotonic() >= deadline:
            message = "Твинк не прислал кадр. Запроси его снова."
        elif pending == request:
            return
        self.request = None
        self.capture.configure(state="normal")
        self.note.configure(text=message)

    def show_frame(self, packet):
        self.image, self.pose = decode_map_frame(packet)
        self.packet = packet
        self.photo = None
        self.caption.configure(text=f"На карте экран твинка {packet['player']}")
        self.draw()

    def draw(self):
        canvas = self.canvas
        canvas.delete("all")
        for key, choice in self.choices.items():
            unit = key.split("/")[1].title()
            choice.configure(text=unit if key in self.draft else f"{unit} · авто")
        width, height = canvas.winfo_width(), canvas.winfo_height()
        if self.image is None or min(width, height) <= 1:
            canvas.create_text(width/2, height/2, width=max(240, width-40), fill=C["muted"],
                               text="Во время матча выбери твинка и нажми «Получить кадр».")
            return
        scale = min(width/self.image.width, height/self.image.height)
        w, h = max(1, round(self.image.width*scale)), max(1, round(self.image.height*scale))
        left, top = (width-w)//2, (height-h)//2
        self.bounds = left, top, w, h
        if self.photo is None or (w, h) != (self.photo.width(), self.photo.height()):
            self.photo = ImageTk.PhotoImage(self.image.resize((w, h), Image.Resampling.BILINEAR), master=self.win)
        canvas.create_image(left, top, anchor="nw", image=self.photo)
        for key, point in self.draft.items():
            x, y = screen_point(self.pose, point)
            if not (0 <= x <= 1 and 0 <= y <= 1):
                continue
            x, y = left + x*w, top + y*h
            player, unit = key.split("/")
            color = (C["accent"], C["blue"], C["yellow"])[int(player)-1]
            canvas.create_oval(x-5, y-5, x+5, y+5, fill=color, outline="white",
                               width=3 if key == self.selected.get() else 1)
            tag = f"{player} · {unit.title()}"
            canvas.create_text(x+9, y+1, text=tag, anchor="w", fill="black", font=(FONT, 10, "bold"))
            canvas.create_text(x+8, y, text=tag, anchor="w", fill="white", font=(FONT, 10, "bold"))

    def pick(self, event):
        left, top, w, h = self.bounds
        if self.pose is None or min(w, h) < 1:
            return
        screen = ((event.x-left)/w, (event.y-top)/h)
        if not placement_in_view(*screen):
            self.note.configure(text="Выбери землю внутри кадра, в стороне от игрового интерфейса.")
            return
        key = self.selected.get()
        point = [round(v, 2) for v in map_point(self.pose, screen)]
        try:
            self.draft = titan_layout(self.draft | {key:point})
        except ValueError as exc:
            self.note.configure(text=str(exc))
            return
        self.note.configure(text="Метка выставлена. Нажми «Сохранить точки».")
        self.draw()

    def clear(self):
        self.draft.pop(self.selected.get(), None)
        self.note.configure(text="Для выбранного титана включится автопоиск после сохранения.")
        self.draw()

    def merge_learned_points(self):
        latest = dict(self.app.match.manual_titans)
        for key in self.baseline.keys() | latest.keys():
            if self.draft.get(key) == self.baseline.get(key):
                if key in latest:
                    self.draft[key] = latest[key]
                else:
                    self.draft.pop(key, None)
        self.baseline = latest

    def save(self):
        try:
            with self.app.match.lock:
                self.merge_learned_points()
                plan = titan_layout(self.draft)
                self.app.profile.write("titan-map.json", dict(points=plan, frame=self.packet))
                self.app.match.set_titan_layout(plan)
                self.app.saved_layout = dict(plan)
                self.baseline = dict(plan)
                self.app.titan_frame = self.packet
        except (ValueError, OSError) as exc:
            self.note.configure(text=f"Не удалось сохранить точки. {exc}")
            return
        self.draw()
        self.note.configure(text="Сохранено. Метки применяются при следующей постановке каждого титана.")
