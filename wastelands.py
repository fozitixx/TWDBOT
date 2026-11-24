"""Desktop entry point for the main account and three RDP workers."""
import base64
import io
import ipaddress
import queue
import re
import socket
import threading
import time
import tkinter as tk
from tkinter import messagebox, ttk

from PIL import Image, ImageTk

from twd_bot import C, FONT, SETTINGS
from wastelands_team import ABILITIES, AltConnection, Match, PLAYERS, PORT, UNITS, Wait, connect_by_pin, placement_label, serve


def peer_host(value):
    value = value.strip().rstrip(".")
    try:
        return str(ipaddress.IPv4Address(value))
    except ValueError:
        try:
            value = value.encode("idna").decode("ascii")
        except UnicodeError:
            raise ValueError("Проверь сетевое имя компьютера основы.") from None
        labels = value.split(".")
        if (len(value) <= 253 and not all(part.isdigit() for part in labels)
                and all(re.fullmatch(r"[A-Za-z0-9](?:[A-Za-z0-9-]{0,61}[A-Za-z0-9])?", part)
                        for part in labels)):
            return value
        raise ValueError("Введи IP или сетевое имя компьютера основы.") from None


def text(parent, value, *, size=10, color="text", bold=False, **options):
    return tk.Label(parent, text=value, font=(FONT, size, "bold" if bold else "normal"),
                    bg=parent.cget("background"), fg=C[color], anchor="w", justify="left", **options)


def button(parent, title, command, *, primary=False):
    return tk.Button(parent, text=title, command=command, font=(FONT, 9, "bold"),
                     bg=C["accent" if primary else "card2"], fg=C["bg" if primary else "text"],
                     activebackground=C["accent_d" if primary else "line"], activeforeground=C["bg" if primary else "text"],
                     disabledforeground=C["dim"], relief="flat", bd=0, padx=10, pady=4,
                     highlightthickness=1, highlightbackground=C["line"], highlightcolor=C["accent"], cursor="hand2")


def card(parent):
    return tk.Frame(parent, bg=C["card"], padx=12, pady=9, highlightthickness=1, highlightbackground=C["line"])


def field(parent, **options):
    return tk.Entry(parent, font=(FONT, 10), bg=C["entry"], fg=C["text"], insertbackground=C["text"],
                    readonlybackground=C["entry"], relief="flat", highlightthickness=1,
                    highlightbackground=C["line"], highlightcolor=C["accent"], **options)


class App:
    def __init__(self,root,*,prefs=None,save_prefs=None,farm_busy=None,mode_lock=None):
        self.root = root
        self.standalone = isinstance(root,tk.Tk)
        self.farm_busy = farm_busy or (lambda: False)
        self.mode_lock = mode_lock or threading.RLock()
        self.save_prefs = save_prefs
        prefs = prefs if isinstance(prefs,dict) else {}
        if self.standalone:
            root.title("TWD · Wastelands")
            root.minsize(760,420)
        self.match = Match()
        self.server = self.worker = self.listener = None
        self.stop = threading.Event()
        self.messages = queue.SimpleQueue()
        self.shown = {}
        self.rows = {}
        self.slot_vars = {}
        root.configure(bg=C["bg"])
        heading = tk.Frame(root, bg=C["bg"])
        heading.pack(fill="x", padx=14, pady=(4, 6))
        text(heading, "Wastelands", size=18, bold=True).pack(side="left")
        self.connection_count = text(heading, "", color="muted")
        self.connection_count.pack(side="right")
        style = ttk.Style(root)
        if self.standalone:
            style.theme_use("clam")
        style.configure("Wastelands.TNotebook", background=C["bg"], borderwidth=0, tabmargins=0,
                        bordercolor=C["bg"], lightcolor=C["bg"], darkcolor=C["bg"])
        style.configure("Wastelands.TNotebook.Tab", background=C["card"], foreground=C["muted"],
                        padding=(16, 5), font=(FONT, 10, "bold"), borderwidth=0, focuscolor=C["line"],
                        bordercolor=C["line"], lightcolor=C["line"], darkcolor=C["line"])
        style.map("Wastelands.TNotebook.Tab", background=[("selected", C["card2"]), ("active", C["line"])],
                  foreground=[("disabled", C["dim"]), ("selected", C["accent"])])
        style.configure("Wastelands.Vertical.TScrollbar", background=C["line"], troughcolor=C["bg"],
                        bordercolor=C["bg"], arrowcolor=C["muted"], lightcolor=C["line"], darkcolor=C["line"], arrowsize=10)
        tabs = ttk.Notebook(root, style="Wastelands.TNotebook")
        tabs.pack(fill="both", expand=True, padx=14, pady=(0, 6))
        self.tabs = tabs
        self.main = tk.Frame(tabs, bg=C["bg"])
        self.client = tk.Frame(tabs, bg=C["bg"])
        tabs.add(self.main,text="Основа")
        tabs.add(self.client,text="Твинк")
        tabs.bind("<<NotebookTabChanged>>",lambda _:self.refresh_tabs())
        try:
            addr = socket.gethostbyname(socket.gethostname())
        except OSError:
            addr = "127.0.0.1"
        self.addr = tk.StringVar(value=prefs.get("address") or addr)
        self.peer_addr = tk.StringVar(value=prefs.get("peer_address",""))
        self.host = tk.StringVar(value=prefs.get("host",""))
        self.mode = tk.StringVar(value="hard" if prefs.get("mode")=="hard" else "nightmare")
        self.afk_auto = tk.BooleanVar(value=prefs.get("afk_auto",True))
        self._build_main()
        self._build_client(prefs)
        self._run_view = False
        if prefs.get("role")=="alt":
            tabs.select(self.client)
        if self.standalone:
            root.protocol("WM_DELETE_WINDOW",self.close)
        self.timer = root.after(200,self.tick)

    def _build_main(self):
        # Keep connection feedback in view while scrolling the three players on short RDP desktops.
        self.note = text(self.main, "Нажми «Показать PIN» у нужного твинка и введи IP и PIN в его RDP-сеансе.",
                         size=9, color="muted", wraplength=530)
        self.note.pack(fill="x", pady=(7, 5))
        canvas = tk.Canvas(self.main, bg=C["bg"], highlightthickness=0, width=1, height=1)
        scroll = ttk.Scrollbar(self.main, orient="vertical", command=canvas.yview, style="Wastelands.Vertical.TScrollbar")
        scroll.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        canvas.configure(yscrollcommand=scroll.set)
        body = tk.Frame(canvas, bg=C["bg"])
        item = canvas.create_window(0, 0, anchor="nw", window=body)
        canvas.bind("<Configure>", lambda e: canvas.itemconfigure(item, width=e.width))
        body.bind("<Configure>", lambda _: canvas.configure(scrollregion=canvas.bbox("all")))
        def wheel(event):
            if canvas.winfo_ismapped() and str(event.widget).startswith(str(canvas)) and canvas.yview() != (0., 1.):
                canvas.yview_scroll(-int(event.delta / 120), "units")
        self.wheel_binding = self.root.winfo_toplevel().bind("<MouseWheel>", wheel, add="+")

        settings = card(body)
        settings.pack(fill="x", pady=(0, 6))
        net = tk.Frame(settings, bg=C["card"])
        net.pack(fill="x")
        text(net, "Подключение", size=11, bold=True).pack(side="left")
        self.network_state = text(net, "Выключено", size=9, color="muted")
        self.network_state.pack(side="left", padx=10)
        self.listen = button(net, "Включить связь", self.start_server)
        self.listen.pack(side="right")
        line = tk.Frame(settings, bg=C["card"])
        line.pack(fill="x", pady=(6, 0))
        text(line, "IP основы", size=9, color="muted").pack(side="left")
        self.ip_entry = field(line, textvariable=self.addr, width=16)
        self.ip_entry.pack(side="left", padx=8, ipady=3)
        text(line, "Имя ПК: " + socket.gethostname(), size=9, color="muted").pack(side="left")

        match = card(body)
        match.pack(fill="x", pady=(0, 6))
        top = tk.Frame(match, bg=C["card"])
        top.pack(fill="x")
        self.match_title = text(top, "Настройки матча", size=11, bold=True)
        self.match_title.pack(side="left")
        self.run_button = button(top, "Запустить помощника", self.start_match, primary=True)
        self.run_button.pack(side="right")
        self.match_fields = tk.Frame(match, bg=C["card"])
        self.match_fields.pack(fill="x", pady=(4, 0))
        text(self.match_fields, "Имя в приглашении", size=9, color="muted").grid(row=0,column=0,sticky="w",padx=(0,16))
        field(self.match_fields, textvariable=self.host, width=19).grid(row=1,column=0,sticky="ew",ipady=3,padx=(0,16))
        text(self.match_fields, "Сложность", size=9, color="muted").grid(row=0,column=1,sticky="w")
        modes = tk.Frame(self.match_fields, bg=C["entry"])
        modes.grid(row=1,column=1,sticky="w")
        for name in ("hard","nightmare"):
            tk.Radiobutton(modes, text=name.upper(), value=name, variable=self.mode, indicatoron=False,
                           font=(FONT,9,"bold"), bg=C["entry"], fg=C["text"],
                           selectcolor="#81323b" if name=="hard" else "#614285",
                           activebackground=C["card2"], activeforeground=C["accent"], relief="flat",
                           offrelief="flat", bd=0, highlightthickness=0, padx=9, pady=4).pack(side="left")

        tk.Checkbutton(self.match_fields, text="Автоответ твинков на AFK CHECK",
                       variable=self.afk_auto, bg=C["card"], fg=C["text"], selectcolor=C["entry"],
                       activebackground=C["card"], activeforeground=C["accent"], font=(FONT,9),
                       highlightthickness=0).grid(row=2,column=0,columnspan=2,sticky="w",pady=(4,0))

        top = tk.Frame(body, bg=C["bg"])
        top.pack(fill="x", pady=(2, 4))
        text(top, "Твинки", size=12, bold=True).pack(side="left")
        self.group_attack = button(top,"Aerial Attack — всем",self.send_all)
        self.summon_all = button(top, "Всех в приватку", lambda: self.summon(PLAYERS))
        self.summon_all.pack(side="right", padx=4)
        self.summon_buttons = {}
        self.place_buttons = {}
        self.player_status, self.player_actions, self.command_buttons, self.player_results = {}, {}, {}, {}
        self.pin_labels = {}
        for player in PLAYERS:
            row = card(body)
            row.pack(fill="x", pady=(0, 5))
            head = tk.Frame(row, bg=C["card"])
            head.pack(fill="x")
            text(head, f"Твинк {player}", size=10, bold=True).pack(side="left")
            self.player_status[player] = text(head, "●  Вне связи", size=9, color="muted")
            self.player_status[player].pack(side="left", padx=9)
            button(head,"Скопировать код",lambda i=player:self.pair(i)).pack(side="right")
            button(head,"Показать PIN",lambda i=player:self.show_pin(i)).pack(side="right",padx=5)
            self.summon_buttons[player] = button(head, "В приватку", lambda i=player: self.summon((i,)))
            self.summon_buttons[player].pack(side="right")
            self.pin_labels[player] = text(row,"",bold=True,color="accent")
            self.rows[player] = text(row,"",size=9,color="muted",wraplength=470)
            self.player_results[player] = text(row,"",size=9,color="blue",wraplength=470)
            actions = tk.Frame(row, bg=C["card"])
            self.player_actions[player] = actions
            self.command_buttons[player] = []
            for name in ABILITIES:
                b = button(actions,name,lambda i=player,n=name:self.send(i,n))
                b.pack(side="left",padx=(0,4))
                self.command_buttons[player].append(b)
            self.place_buttons[player] = button(actions,"Места юнитов",lambda i=player:self.reservations(i))
            self.place_buttons[player].pack(side="right")

    def _build_client(self, prefs):
        conn = card(self.client)
        conn.pack(fill="x",pady=(10,8))
        text(conn,"Подключение к основе",size=12,bold=True).pack(anchor="w")
        text(conn,"На основе нажми «Показать PIN» в строке этого твинка.",size=9,color="muted").pack(anchor="w",pady=(3,5))
        fields = tk.Frame(conn,bg=C["card"])
        fields.pack(fill="x")
        text(fields,"IP или имя ПК основы",size=9,color="muted").grid(row=0,column=0,sticky="w")
        text(fields,"PIN из 8 цифр или скопированный код",size=9,color="muted").grid(row=0,column=1,sticky="w")
        field(fields,textvariable=self.peer_addr,width=17).grid(row=1,column=0,sticky="ew",ipady=4,padx=(0,12))
        self.connection_code = tk.StringVar()
        self.token = field(fields,textvariable=self.connection_code)
        self.token.grid(row=1,column=1,sticky="ew",ipady=4)
        fields.columnconfigure(1,weight=1)
        self.connection_code.trace_add("write",lambda *_:self.token.configure(
            show="•" if "|" in self.connection_code.get() else ""))
        group = card(self.client)
        group.pack(fill="x",pady=(0,8))
        text(group,"Слоты юнитов",size=12,bold=True).pack(anchor="w")
        text(group,"Выбери номер каждой карточки на нижней панели Roblox.",size=9,color="muted").pack(anchor="w",pady=(3,6))
        slots = tk.Frame(group,bg=C["card"])
        slots.pack(fill="x")
        saved = prefs.get("slots",{})
        for col,(unit,default) in enumerate(zip(UNITS,(3,4,1,2))):
            slots.columnconfigure(col,weight=1,uniform="slot")
            text(slots,"TV" if unit=="tv" else unit.title(),size=9,color="muted").grid(row=0,column=col,sticky="w")
            value = str(saved.get(unit,default)) if isinstance(saved,dict) else str(default)
            var = tk.StringVar(value=value if value in ("1","2","3","4","5","6") else str(default))
            self.slot_vars[unit] = var
            tk.Spinbox(slots, from_=1,to=6,textvariable=var,width=4,state="readonly",wrap=True,
                       font=(FONT,11,"bold"), readonlybackground=C["entry"], fg=C["text"],buttonbackground=C["card2"],
                       highlightbackground=C["line"],highlightcolor=C["accent"],highlightthickness=1,bd=0
                       ).grid(row=1,column=col,sticky="ew",padx=(0,8),ipady=4)
        actions = tk.Frame(self.client,bg=C["bg"])
        actions.pack(fill="x")
        self.join_button = button(actions,"Подключиться",self.join,primary=True)
        self.join_button.pack(side="left")
        self.stop_client = button(actions,"Остановить · F6",self.stop.set)
        self.stop_client.pack(side="left",padx=6)
        self.stop_client.configure(state="disabled")
        self.status = text(self.client,"Твинк отключён",color="muted",wraplength=475)
        self.status.pack(anchor="w",pady=10)

    def remember(self):
        if self.save_prefs:
            self.save_prefs(dict(address=self.addr.get().strip(),peer_address=self.peer_addr.get().strip(),host=self.host.get().strip(),
                                 mode=self.mode.get(),afk_auto=self.afk_auto.get(),slots={u:v.get() for u,v in self.slot_vars.items()},
                                 role="alt" if self.tabs.select()==str(self.client) else "main"))

    def active(self):
        return bool(self.match.run or (self.worker and self.worker.is_alive()))

    def refresh_tabs(self):
        self.tabs.tab(self.client,state="disabled" if self.server else "normal")
        working = bool(self.worker and self.worker.is_alive())
        self.tabs.tab(self.main,state="disabled" if working else "normal")
        self.join_button.configure(state="disabled" if working else "normal")
        self.stop_client.configure(state="normal" if working else "disabled")

    def start_server(self):
        if self.server:
            return
        try:
            self.server = serve(self.match,(self.addr.get().strip(),PORT))
        except OSError as exc:
            messagebox.showerror("Подключение",str(exc))
            return
        self.listen.configure(text="Выключить связь",command=self.disconnect_server)
        self.ip_entry.configure(state="readonly")
        self.network_state.configure(text="●  Включено",fg=C["accent"])
        self.refresh_tabs()
        self.note.configure(text="Связь включена. Покажи PIN нужного твинка и введи его вместе с IP в RDP.")

    def disconnect_server(self):
        self.match.stop()
        self.server.shutdown()
        self.server.server_close()
        self.server = None
        with self.match.lock:
            self.match.pins.clear()
            self.match.summons.clear()
            self.match.clients.clear()
        self.render_players()
        self.listen.configure(text="Включить связь",command=self.start_server)
        self.ip_entry.configure(state="normal")
        self.network_state.configure(text="Выключено",fg=C["muted"])
        self.refresh_tabs()
        self.note.configure(text="Подключение закрыто")

    def start_match(self):
        with self.mode_lock:
            if self.farm_busy():
                self.note.configure(text="Сначала останови фарм Invaded City на главной странице.")
                return
            self._start_match()

    def _start_match(self):
        if not self.host.get().strip():
            self.note.configure(text="Введи имя основы так, как оно указано в игровом приглашении.")
            return
        if not self.server:
            self.start_server()
        if not self.server:
            return
        if self.match.run:
            messagebox.showinfo("Матч","Сначала останови текущий матч помощника.")
            return
        try:
            self.match.start(self.mode.get(),self.host.get(),afk_auto=self.afk_auto.get())
            self.remember()
            self.note.configure(text="Пригласи твинков на Wastelands и запусти матч в Roblox с основы.")
            self.render_players()
        except ValueError as exc:
            messagebox.showerror("Матч",str(exc))

    def stop_match(self):
        self.match.stop()
        self.note.configure(text="Матч помощника остановлен")
        self.render_players()

    def pair(self,player):
        if not self.server:
            self.start_server()
        if self.server:
            self.root.clipboard_clear()
            self.root.clipboard_append(f"{self.server.server_address[0]}|{player}|{self.match.keys[player]}")
            self.note.configure(text=f"Код скопирован. В RDP-сеансе твинка {player} открой «Твинк» и вставь код.")

    def show_pin(self,player):
        if not self.server:
            self.start_server()
        if self.server:
            self.match.issue_pin(player)
            self.note.configure(text=f"Твинк {player}: введи IP и PIN вручную. Новый PIN можно получить после входа или истечения таймера.")
            self.render_players()

    def join(self):
        with self.mode_lock:
            if self.farm_busy():
                self.status.configure(text="Сначала останови фарм Invaded City на главной странице.")
                return
            self._join()

    def _join(self):
        if self.worker and self.worker.is_alive():
            return
        try:
            from pynput import keyboard
            raw = self.token.get().strip()
            pin = None
            if "|" in raw:
                parts = raw.split("|")
                if len(parts)!=3 or parts[1] not in ("1","2","3") or not parts[0] or not parts[2]:
                    self.status.configure(text="Скопируй полный код на основе или введи IP и PIN вручную.")
                    return
                host,num,key = parts
                number = int(num)
            else:
                try:
                    host = peer_host(self.peer_addr.get())
                except ValueError as exc:
                    self.status.configure(text=str(exc))
                    return
                pin = raw.replace(" ","")
                if len(pin)!=8 or not pin.isascii() or not pin.isdigit():
                    self.status.configure(text="Введи все 8 цифр PIN, включая начальные нули.")
                    return
                number = key = None
            slots = {u:int(v.get()) for u,v in self.slot_vars.items()}
            if len(set(slots.values()))!=4:
                self.status.configure(text="У двух юнитов выбран один слот. Укажи четыре разных номера.")
                return
            self.stop.clear()
            if self.standalone:
                self.listener = keyboard.Listener(on_press=lambda k:self.stop.set() if k==keyboard.Key.f6 else None)
                self.listener.start()
            self.worker = threading.Thread(target=self.worker_loop,args=(host,number,key,pin,slots),daemon=True)
            self.worker.start()
            self.refresh_tabs()
            self.status.configure(text=f"Подключаюсь к {host}…")
            self.remember()
        except (ValueError,ImportError,OSError) as exc:
            messagebox.showerror("Твинк",str(exc))

    def worker_loop(self,host,number,key,pin,slots):
        try:
            if pin is not None:
                try:
                    host = socket.gethostbyname(host)
                except OSError as exc:
                    raise ValueError("Не удалось найти основу по имени. Введи IP из её окна.") from exc
                number,key = connect_by_pin(host,pin)
            connection = AltConnection(host, number, key)
            while not self.stop.is_set():
                try:
                    connection.exchange(status="Загружаю распознавание")
                except Wait as exc:
                    self.messages.put(str(exc))
                    self.stop.wait(1)
                    continue
                self.messages.put(f"Твинк {number} на связи. Загружаю распознавание…")
                from wastelands_alt import Alt
                Alt(connection,slots,self.stop,self.messages.put).loop()
                break
            self.messages.put("Твинк остановлен")
        except Exception as exc:
            self.messages.put(f"Твинк остановлен: {exc}")

    def summon(self, players):
        link = SETTINGS.get("server_link")
        if not link:
            self.note.configure(text="В настройках основы заполни «Ссылка приватного сервера» и сохрани настройки.")
            return
        sent, skipped = [], []
        for i in players:
            try:
                self.match.summon(i, link)
                sent.append(str(i))
            except ValueError as exc:
                skipped.append(f"Твинк {i} · {exc}")
        messages = ["Вызов в приватку отправлен: " + ", ".join(sent)] if sent else []
        self.note.configure(text=". ".join(messages + skipped))
        self.render_players()

    def send(self,player,name):
        try:
            self.match.command(player,"snapshot" if name=="Teleport" else name)
        except ValueError as exc:
            self.note.configure(text=f"Твинк {player} · {exc}")

    def send_all(self):
        sent = []
        skipped = []
        for i in PLAYERS:
            try:
                self.match.command(i,"Aerial Attack")
                sent.append(str(i))
            except ValueError as exc:
                skipped.append(f"Твинк {i} · {exc}")
        message = ["Aerial Attack отправлен: " + ", ".join(sent)] if sent else []
        self.note.configure(text=". ".join(message + skipped))

    def reservations(self,player):
        with self.match.lock:
            rows = [dict(v) for (i,_),v in self.match.places.items() if i==player]
            run = self.match.run
        win = tk.Toplevel(self.root)
        win.title(f"Твинк {player} · места")
        win.configure(bg=C["bg"],padx=14,pady=12)
        text(win,f"Места юнитов · твинк {player}",size=14,bold=True).pack(anchor="w",pady=(0,8))
        body = tk.Frame(win, bg=C["bg"])
        body.pack(fill="both", expand=True)
        canvas = tk.Canvas(body, bg=C["bg"], highlightthickness=0,
                           width=420, height=min(480, win.winfo_screenheight()//2))
        scroll = ttk.Scrollbar(body, orient="vertical", command=canvas.yview)
        scroll.pack(side="right", fill="y")
        canvas.pack(side="left", fill="both", expand=True)
        canvas.configure(yscrollcommand=scroll.set)
        listing = tk.Frame(canvas, bg=C["bg"])
        content = canvas.create_window(0, 0, window=listing, anchor="nw")
        listing.bind("<Configure>", lambda _: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda ev: canvas.itemconfigure(content, width=ev.width))
        win.bind("<MouseWheel>", lambda ev: canvas.yview_scroll(-int(ev.delta/120), "units"))
        for row in rows:
            unit = row["unit"]
            placed = row["state"]=="placed"
            area = card(listing)
            area.pack(fill="x",pady=(0,4))
            line = tk.Frame(area,bg=C["card"])
            line.pack(fill="x")
            text(line,placement_label(unit),bold=True).pack(side="left")
            status = "Поставлен" if placed else "Место в плане"
            if not placed and row.get("target"):
                status = "Проверка постановки"
            text(line,status,size=9,
                 color="accent" if placed else "muted").pack(side="left",padx=9)
            x,y = row["point"]
            text(line,f"{x:.0f}, {y:.0f}",size=9,color="muted").pack(side="right")
            if row.get("target") and time.monotonic()-row.get("target_since",0)>12:
                target = row["target"]
                def resolve(ok,u=unit,p=target,since=row.get("target_since")):
                    with self.match.lock:
                        current=self.match.places.get((player,u),{})
                        if self.match.run!=run or current.get("target")!=p or current.get("target_since")!=since:
                            win.destroy()
                            return
                        if ok:
                            current.update(point=p,state="placed")
                        current.pop("target",None)
                    win.destroy()
                text(area,f"Ручная сверка точки {target[0]:.0f}, {target[1]:.0f}. Юнит встал?",color="yellow").pack(anchor="w")
                button(area,"Да, стоит",lambda f=resolve:f(True)).pack(side="left")
                button(area,"Нет, место свободно",lambda f=resolve:f(False)).pack(side="left",padx=4)
        def retry():
            with self.match.lock:
                if run and run==self.match.run:
                    self.match.progress[player]["retry"]+=1
            win.destroy()
        if run:
            button(win,"Повторить поиск места",retry).pack(anchor="w",pady=6)

    def destination(self,player,frame_id,encoded):
        image = Image.open(io.BytesIO(base64.b64decode(encoded)))
        win = tk.Toplevel(self.root)
        win.title(f"Твинк {player} · выбери место телепортации")
        win.configure(bg=C["bg"])
        text(win,f"Teleport · твинк {player}     Нажми по земле, чтобы перенести Screen.",bold=True).pack(anchor="w",padx=10,pady=7)
        photo = ImageTk.PhotoImage(image)
        canvas = tk.Canvas(win,width=image.width,height=image.height,highlightthickness=0,cursor="crosshair")
        canvas.pack()
        canvas.create_image(0,0,image=photo,anchor="nw")
        canvas.photo = photo
        run = self.match.run
        def choose(event):
            if run==self.match.run and run:
                try:
                    self.match.command(player,"Teleport",frame_id=frame_id,
                                       point=[event.x/image.width,event.y/image.height])
                except ValueError as exc:
                    self.note.configure(text=str(exc))
            win.destroy()
        canvas.bind("<Button-1>",choose)

    def render_players(self):
        now = time.monotonic()
        with self.match.lock:
            running = bool(self.match.run)
            if running != self._run_view:
                self._run_view = running
                if running:
                    self.match_fields.pack_forget()
                    self.match_title.configure(text=f"{self.match.mode.upper()}  ·  {self.match.host}")
                    self.run_button.configure(text="Остановить помощника",command=self.stop_match,
                                              bg=C["card2"],fg=C["text"],activebackground=C["line"])
                    self.group_attack.pack(side="right")
                else:
                    self.match_fields.pack(fill="x",pady=(4,0))
                    self.match_title.configure(text="Настройки матча")
                    self.run_button.configure(text="Запустить помощника",command=self.start_match,
                                              bg=C["accent"],fg=C["bg"],activebackground=C["accent_d"])
                    self.group_attack.pack_forget()
                self.listen.configure(state="disabled" if running else "normal")
            connected = 0
            for i in PLAYERS:
                self.match.expire_summon(i, now)
                c = self.match.clients.get(i,{})
                pin = self.match.pins.get(i)
                if self.server and pin and now < pin[1]:
                    digits, deadline = pin
                    ip = self.server.server_address[0]
                    if ip == "0.0.0.0":
                        ip = "локальный адрес ПК"
                    seconds = int(deadline - now)
                    self.pin_labels[i].configure(text=f"IP  {ip}      PIN  {digits[:4]} {digits[4:]}      {seconds//60}:{seconds%60:02}")
                    self.pin_labels[i].pack(fill="x",pady=(4,0))
                else:
                    self.pin_labels[i].pack_forget()
                online = bool(self.server and now-c.get("seen",-1e8)<8)
                connected += int(online)
                self.summon_buttons[i].configure(state="normal" if online and i not in self.match.summons else "disabled")
                self.player_status[i].configure(text="●  На связи" if online else "●  Вне связи",
                                                fg=C["accent" if online else "muted"])
                if running:
                    pending = sum(1 for (owner,_),place in self.match.places.items() if owner==i and
                                  place.get("target") and not place.get("slot") and now-place.get("target_since",now)>12)
                    caption = f"Проверить места ({pending})" if pending else "Места юнитов"
                    if self.place_buttons[i].cget("text")!=caption:
                        self.place_buttons[i].configure(text=caption)
                    self.player_actions[i].pack(fill="x",pady=(5,0))
                    for b in self.command_buttons[i]:
                        b.configure(state="normal" if online and i not in self.match.recalled and i not in self.match.summons else "disabled")
                else:
                    self.player_actions[i].pack_forget()
                activity = c.get("status","") if online else ""
                result = self.match.results.get(i,"")
                for widget,value in ((self.rows[i],activity),(self.player_results[i],f"Команда · {result}" if result else "")):
                    if value:
                        widget.configure(text=value)
                        widget.pack(fill="x",pady=(2,0))
                    else:
                        widget.pack_forget()
                frame = self.match.frames.get(i)
                if frame and frame[0]!=self.shown.get(i):
                    self.shown[i]=frame[0]
                    try:
                        self.destination(i,*frame)
                    except (ValueError,OSError):
                        self.note.configure(text="Не удалось открыть кадр")
            self.connection_count.configure(text=f"На связи   {connected} / {len(PLAYERS)}"
                                            if self.tabs.select()==str(self.main) else "")
            self.group_attack.configure(state="normal" if connected else "disabled")
            self.summon_all.configure(state="normal" if connected else "disabled")

    def tick(self):
        while not self.messages.empty():
            self.status.configure(text=self.messages.get())
        if self.worker and not self.worker.is_alive():
            self.worker = None
            if self.listener:
                self.listener.stop()
                self.listener=None
            self.refresh_tabs()
        self.render_players()
        self.timer = self.root.after(400,self.tick)

    def close(self):
        self.root.after_cancel(self.timer)
        self.root.winfo_toplevel().unbind("<MouseWheel>", self.wheel_binding)
        self.stop.set()
        self.match.stop()
        if self.listener:
            self.listener.stop()
        if self.server:
            self.server.shutdown()
            self.server.server_close()
        self.remember()
        if self.standalone:
            self.root.destroy()


if __name__=="__main__":
    import twd_bot
    twd_bot.enable_dpi_awareness()
    twd_bot.load_settings()
    window=tk.Tk()
    App(window)
    window.mainloop()
