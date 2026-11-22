"""Desktop entry point for the main account and three RDP workers."""
import base64
import io
import queue
import socket
import threading
import time
import tkinter as tk
from tkinter import messagebox, ttk

from PIL import Image, ImageTk

from twd_bot import C, FONT
from wastelands_team import ABILITIES, Match, PLAYERS, PORT, UNITS, serve


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
        self.host = tk.StringVar(value=prefs.get("host",""))
        self.mode = tk.StringVar(value="hard" if prefs.get("mode")=="hard" else "nightmare")
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
        self.note = text(self.main, "Передай каждому твинку его код подключения из списка ниже.",
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

        top = tk.Frame(body, bg=C["bg"])
        top.pack(fill="x", pady=(2, 4))
        text(top, "Твинки", size=12, bold=True).pack(side="left")
        self.group_attack = button(top,"Aerial Attack — всем",self.send_all)
        self.player_status, self.player_actions, self.command_buttons, self.player_results = {}, {}, {}, {}
        for player in PLAYERS:
            row = card(body)
            row.pack(fill="x", pady=(0, 5))
            head = tk.Frame(row, bg=C["card"])
            head.pack(fill="x")
            text(head, f"Твинк {player}", size=10, bold=True).pack(side="left")
            self.player_status[player] = text(head, "●  Вне связи", size=9, color="muted")
            self.player_status[player].pack(side="left", padx=9)
            button(head,"Скопировать код",lambda i=player:self.pair(i)).pack(side="right")
            self.rows[player] = text(row,"",size=9,color="muted",wraplength=470)
            self.player_results[player] = text(row,"",size=9,color="blue",wraplength=470)
            actions = tk.Frame(row, bg=C["card"])
            self.player_actions[player] = actions
            self.command_buttons[player] = []
            for name in ABILITIES:
                b = button(actions,name,lambda i=player,n=name:self.send(i,n))
                b.pack(side="left",padx=(0,4))
                self.command_buttons[player].append(b)
            button(actions,"Места юнитов",lambda i=player:self.reservations(i)).pack(side="right")

    def _build_client(self, prefs):
        conn = card(self.client)
        conn.pack(fill="x",pady=(10,8))
        text(conn,"Подключение к основе",size=12,bold=True).pack(anchor="w")
        text(conn,"Вставь код, скопированный на основе для этого твинка.",size=9,color="muted").pack(anchor="w",pady=(3,5))
        self.token = field(conn,show="•")
        self.token.pack(fill="x",ipady=5)
        group = card(self.client)
        group.pack(fill="x",pady=(0,8))
        text(group,"Слоты юнитов",size=12,bold=True).pack(anchor="w")
        text(group,"Выбери номер каждой карточки на нижней панели Roblox.",size=9,color="muted").pack(anchor="w",pady=(3,6))
        slots = tk.Frame(group,bg=C["card"])
        slots.pack(fill="x")
        saved = prefs.get("slots",{})
        for col,(unit,default) in enumerate(zip(UNITS,(4,5,1,3))):
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
            self.save_prefs(dict(address=self.addr.get().strip(),host=self.host.get().strip(),
                                 mode=self.mode.get(),slots={u:v.get() for u,v in self.slot_vars.items()},
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
        self.note.configure(text="Связь включена. Скопируй код для каждого твинка и передай его в нужный RDP-сеанс.")

    def disconnect_server(self):
        self.match.stop()
        self.server.shutdown()
        self.server.server_close()
        self.server = None
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
            self.match.start(self.mode.get(),self.host.get())
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
            from wastelands_alt import Alt
            from pynput import keyboard
            parts = self.token.get().strip().split("|")
            if len(parts)!=3 or parts[1] not in ("1","2","3") or not parts[0] or not parts[2]:
                self.status.configure(text="Скопируй код на основе и вставь его целиком.")
                return
            host,num,key = parts
            number=int(num)
            slots = {u:int(v.get()) for u,v in self.slot_vars.items()}
            if len(set(slots.values()))!=4:
                self.status.configure(text="У двух юнитов выбран один слот. Укажи четыре разных номера.")
                return
            self.stop.clear()
            alt = Alt(host,number,key,slots,self.stop,self.messages.put)
            if self.standalone:
                self.listener = keyboard.Listener(on_press=lambda k:self.stop.set() if k==keyboard.Key.f6 else None)
                self.listener.start()
            self.worker = threading.Thread(target=self.worker_loop,args=(alt,),daemon=True)
            self.worker.start()
            self.refresh_tabs()
            self.status.configure(text=f"Подключаюсь к {host} как твинк {number}…")
            self.remember()
        except ModuleNotFoundError as exc:
            if exc.name=="cv2":
                messagebox.showerror("Твинк","Для твинка нужен OpenCV. Установи opencv-python-headless "
                                     "в тот же Python, которым запускается TWD Farm.")
            else:
                messagebox.showerror("Твинк",str(exc))
        except (ValueError,ImportError,OSError) as exc:
            messagebox.showerror("Твинк",str(exc))

    def worker_loop(self,alt):
        try:
            alt.loop()
            self.messages.put("Твинк остановлен")
        except Exception as exc:
            self.messages.put(f"Твинк остановлен: {exc}")

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
        for row in rows:
            unit = row["unit"]
            placed = row["state"]=="placed"
            area = card(win)
            area.pack(fill="x",pady=(0,4))
            line = tk.Frame(area,bg=C["card"])
            line.pack(fill="x")
            text(line,"TV" if unit=="tv" else unit.title(),bold=True).pack(side="left")
            text(line,"Поставлен" if placed else "Место занято под юнита",size=9,
                 color="accent" if placed else "muted").pack(side="left",padx=9)
            x,y = row["point"]
            text(line,f"{x:.0f}, {y:.0f}",size=9,color="muted").pack(side="right")
            if row.get("target") and time.monotonic()-row.get("target_since",0)>12:
                target = row["target"]
                def resolve(ok,u=unit,p=target):
                    with self.match.lock:
                        current=self.match.places.get((player,u),{})
                        if self.match.run!=run or current.get("target")!=p:
                            win.destroy()
                            return
                        if ok:
                            current.update(point=p,state="placed")
                        current.pop("target",None)
                    win.destroy()
                text(area,f"Проверь в игре точку {target[0]:.0f}, {target[1]:.0f}. Юнит встал?",color="yellow").pack(anchor="w")
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
                c = self.match.clients.get(i,{})
                online = bool(self.server and now-c.get("seen",-1e8)<8)
                connected += int(online)
                self.player_status[i].configure(text="●  На связи" if online else "●  Вне связи",
                                                fg=C["accent" if online else "muted"])
                if running:
                    self.player_actions[i].pack(fill="x",pady=(5,0))
                    for b in self.command_buttons[i]:
                        b.configure(state="normal" if online else "disabled")
                else:
                    self.player_actions[i].pack_forget()
                activity = c.get("status","") if online else ""
                result = self.match.results.get(i,"") if running else ""
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
    window=tk.Tk()
    App(window)
    window.mainloop()
