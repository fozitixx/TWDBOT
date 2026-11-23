import math
import sys
import threading
import time
import unittest
import base64
import json
import tempfile
import queue
from functools import partial
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import Mock, patch

import numpy as np
from PIL import Image, ImageDraw, ImageFont

from wastelands_alt import Alt, Game, Wait, level, manager_card, countdown
from wastelands_team import AltConnection, Match, PAIR_LIFETIME, PLACEMENT_ORDER, PLAYERS, UNITS, connect_by_pin, position, serve
from wastelands_view import OCR, label, road_pose, screen_point

PRIVATE_LINK = "https://www.roblox.com/share?code=Test123&type=Server"

class IntegrationTest(unittest.TestCase):
    def test_peer_address(self):
        from wastelands import peer_host
        self.assertEqual(peer_host(" main-pc.lan "), "main-pc.lan")
        self.assertEqual(peer_host("127.0.0.1"), "127.0.0.1")
        self.assertEqual(peer_host("основа"), "основа".encode("idna").decode("ascii"))
        for value in ("", "192.168.0.999", "http://main", "main:47631", "main/path"):
            with self.assertRaises(ValueError):
                peer_host(value)

    def test_three_workers_pair_and_wait_for_match(self):
        from wastelands import App
        match = Match()
        server = serve(match,("127.0.0.1",0))
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        workers = []
        slots = dict(zip(UNITS,(4,5,1,3)))
        with patch("wastelands.connect_by_pin", partial(connect_by_pin, port=server.server_port)), \
             patch("wastelands.AltConnection", partial(AltConnection, port=server.server_port)), \
             patch("twd_bot.os.startfile",create=True) as launch:
            try:
                for player in PLAYERS:
                    panel = App.__new__(App)
                    panel.stop = threading.Event()
                    panel.messages = queue.SimpleQueue()
                    worker = threading.Thread(target=panel.worker_loop,
                        args=("localhost",None,None,match.issue_pin(player),slots))
                    workers.append((panel,worker))
                    worker.start()
                for panel,_ in workers:
                    self.assertIn("на связи", panel.messages.get(timeout=5))
                    self.assertEqual(panel.messages.get(timeout=5), "На связи · жду матч")
                with match.lock:
                    self.assertEqual(set(match.clients), set(PLAYERS))
                for player in PLAYERS:
                    match.summon(player,PRIVATE_LINK)
                for panel,_ in workers:
                    deadline = time.monotonic()+5
                    while panel.messages.get(timeout=max(.01,deadline-time.monotonic())) != "Ссылка на приватку открыта":
                        self.assertLess(time.monotonic(), deadline)
                self.assertEqual([c.args for c in launch.call_args_list],
                                 [("roblox://navigation/share_links?code=Test123&type=Server",)]*3)
            finally:
                for panel,worker in workers:
                    panel.stop.set()
                    worker.join(5)
                    self.assertFalse(worker.is_alive())

    def test_page_in_regular_farm_window(self):
        import twd_bot as farm
        with patch.object(farm,"log"), patch.object(farm.keyboard,"Listener"), \
             patch.object(farm.FarmApp,"restart_discord"), patch.object(farm,"save_settings"), \
             patch.dict(farm.SETTINGS, farm.DEFAULT_SETTINGS, clear=True):
            app = farm.FarmApp()
            try:
                app.root.withdraw()
                self.assertIn("wastelands",app.nav)
                self.assertTrue(farm.team_directory())
                app.show("wastelands")
                panel = app.team
                self.assertEqual([panel.tabs.tab(p,"text") for p in panel.tabs.tabs()],["Основа","Твинк"])
                panel.host.set("S4R")
                panel.tabs.select(panel.client)
                panel.remember()
                self.assertEqual(farm.SETTINGS["wastelands"]["host"],"S4R")
                self.assertEqual(farm.SETTINGS["wastelands"]["role"],"alt")
                app.show("settings")
                app.show("wastelands")
                self.assertIs(app.team,panel)
                with patch.object(app,"_start_farm") as start:
                    app._on_hotkey(farm.START_KEY)
                    start.assert_not_called()
                panel.server = Mock()
                panel.match.start("nightmare","S4R")
                panel.match.clients[1] = {"seen":time.monotonic(),"status":"Жду READY"}
                panel.render_players()
                self.assertEqual(panel.match_fields.winfo_manager(),"")
                self.assertEqual(panel.command_buttons[1][0].cget("state"),"normal")
                self.assertEqual(panel.command_buttons[2][0].cget("state"),"disabled")
                panel.reservations(1)
                popup = next(w for w in panel.root.winfo_children() if w.winfo_class()=="Toplevel")
                widgets = [popup]
                labels = []
                while widgets:
                    widget = widgets.pop()
                    widgets.extend(widget.winfo_children())
                    if widget.winfo_class()=="Label":
                        labels.append(widget.cget("text"))
                for kind in ("Plunger","TV"):
                    self.assertTrue(all(f"{kind} {n}/4" in labels for n in range(1,5)))
                self.assertIn("Amplifier",labels)
                self.assertIn("Screen",labels)
                popup.destroy()
                panel.group_attack.invoke()
                panel.render_players()
                self.assertEqual(set(panel.match.pending),{1})
                self.assertIn("Команда отправлена",panel.player_results[1].cget("text"))
                panel.run_button.invoke()
                self.assertEqual(panel.match_fields.winfo_manager(),"pack")
                self.assertEqual(panel.player_actions[1].winfo_manager(),"")
                panel.summon_buttons[1].invoke()
                self.assertIn("Ссылка приватного сервера",panel.note.cget("text"))
                farm.SETTINGS["server_link"] = PRIVATE_LINK
                panel.match.clients[1].update(can_summon=True, instance="test")
                panel.summon_all.invoke()
                self.assertEqual(set(panel.match.summons), {1})
                self.assertIn("вызов в приватку", panel.player_results[1].cget("text"))
            finally:
                app.on_close()
                app.root.mainloop()

    def test_upgrade_from_single_file(self):
        import twd_bot as farm
        src = Path(farm.HERE)
        files = {blob:(src/name).read_bytes() for name,blob in farm.TEAM_FILES.items()}
        def fetch(url,timeout):
            data = files[url.rsplit("/",1)[1]]
            return json.dumps({"content":base64.b64encode(data).decode()}).encode()
        with tempfile.TemporaryDirectory() as tmp, patch.object(farm,"HERE",tmp), \
             patch.object(farm,"_http_get",side_effect=fetch) as http:
            self.assertIsNone(farm.team_directory())
            cached = farm.team_directory(download=True)
            self.assertEqual(http.call_count,len(files))
            self.assertEqual(farm.team_directory(),cached)
            for name in farm.TEAM_FILES:
                self.assertEqual((Path(cached)/name).read_bytes(),(src/name).read_bytes())


class InviteInputTest(unittest.TestCase):
    def test_button_and_cursor_must_still_match(self):
        frame = Image.new("RGB", (1366, 768))
        with Image.open(Path(__file__).parent / "tests/fixtures/wasteland_invite_buttons.png") as card:
            frame.paste(card, (1163, 229))
        game = Mock(spec=Game)
        game.rect.return_value = (100, 50, 1466, 818)
        game.to_screen.side_effect = lambda pt: Game.to_screen(game, pt)
        game.grab.return_value = frame
        point = (1288/1366, 261/768)
        game.m = Mock()
        game.m.position = (500, 500)
        with self.assertRaisesRegex(Wait, "Курсор"):
            Game.accept_invite(game, point)
        game.m.press.assert_not_called()
        game.m.position = (1388, 311)
        Game.accept_invite(game, point)
        game.m.press.assert_called_once()
        game.m.release.assert_called_once()
        game.grab.return_value = Image.new("RGB", frame.size)
        with self.assertRaisesRegex(Wait, "Приглашение"):
            Game.accept_invite(game, point)
        game.m.press.assert_called_once()

    def test_click_retries_until_confirmed(self):
        alt = Alt.__new__(Alt)
        alt.game, alt.ocr, alt.exchange = Mock(), Mock(), Mock()
        alt.reset({"run":"match", "progress":{}})
        alt.game.vote_point.return_value = None
        state = {"mode":"nightmare", "host":"Host"}
        point = (.95, .33)
        with patch("wastelands_alt.read_invite", return_value=(point, "")) as invite, \
             patch("wastelands_alt.time.monotonic", return_value=100) as clock:
            for t in (100, 101, 103):
                clock.return_value = t
                alt.lobby(state, None)
            self.assertEqual(alt.game.accept_invite.call_count, 2)
            self.assertFalse(alt.invited)
            alt.exchange.assert_not_called()
            invite.return_value = None, ""
            alt.ocr.read.return_value = []
            self.assertIn("жду подтверждения", alt.lobby(state, None))
            alt.exchange.assert_not_called()
            alt.ocr.read.side_effect = [[("Wasteland", .1, .4, .05, .02)],
                                        [("Cancel", .5, .9, .05, .02)]]
            self.assertIn("В группе", alt.lobby(state, None))
            alt.exchange.assert_called_once_with("invited")
            self.assertTrue(alt.invited)


class NetworkTest(unittest.TestCase):
    def setUp(self):
        self.match = Match()
        self.server = serve(self.match,("127.0.0.1",0))
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)
        self.alts = []
        for i in PLAYERS:
            connection = AltConnection("127.0.0.1", i, self.match.keys[i], self.server.server_port)
            a = Alt(connection,dict(zip(UNITS,(4,5,1,3))),
                    threading.Event(),lambda status:None)
            self.alts.append(a)
        self.match.start("nightmare","S4R")
        for a in self.alts:
            a.reset(a.exchange())

    def test_manual_pairing_for_all_three_players(self):
        codes = [self.match.issue_pin(i) for i in PLAYERS]
        self.assertEqual(len(set(codes)),3)
        for alt,code in zip(self.alts,codes):
            self.assertEqual(self.match.issue_pin(alt.player),code)
            number,key = connect_by_pin("127.0.0.1",code,self.server.server_port)
            self.assertEqual(number,alt.player)
            alt.connection.key = key
            self.assertEqual(alt.exchange()["run"],self.match.run)
            with self.assertRaisesRegex(ValueError,"PIN"):
                connect_by_pin("127.0.0.1",code,self.server.server_port)

    def test_duplicate_pin_requests_and_expiry(self):
        with patch("wastelands_team.secrets.randbelow",return_value=54321):
            code = self.match.issue_pin(1)
        self.assertEqual(code,"00054321")
        def redeem():
            try:
                return connect_by_pin("127.0.0.1",code,self.server.server_port)[0]
            except ValueError:
                return None
        with ThreadPoolExecutor(2) as pool:
            futures = [pool.submit(redeem) for _ in range(2)]
            self.assertCountEqual([f.result() for f in futures],[1,None])
        with patch("wastelands_team.time.monotonic",return_value=10):
            old = self.match.issue_pin(2)
        with patch("wastelands_team.time.monotonic",return_value=10+PAIR_LIFETIME):
            with self.assertRaisesRegex(ValueError,"PIN"):
                self.match.redeem_pin(old)

    def test_wrong_pin_is_throttled(self):
        code=self.match.issue_pin(3)
        for _ in range(12):
            with self.assertRaisesRegex(ValueError,"PIN неверен"):
                self.match.redeem_pin("invalid")
        with self.assertRaisesRegex(ValueError,"через минуту"):
            self.match.redeem_pin(code)
        later=time.monotonic()+61
        with patch("wastelands_team.time.monotonic",return_value=later):
            self.assertEqual(self.match.redeem_pin(code)["player"],3)

    def test_three_clients_and_contested_teleport(self):
        for unit in PLACEMENT_ORDER:
            for a in self.alts:
                p = position(a.player,unit)
                a.exchange("reserve",unit=unit,point=p)
                a.exchange("commit",unit=unit,point=p)
                a.exchange("commit",unit=unit,point=p)
        places = self.alts[2].exchange()["places"]
        self.assertEqual(len({tuple(row["point"]) for row in places}),30)
        for player in PLAYERS:
            own = [r for r in places if r["player"] == player and r["state"] == "placed"]
            kinds = [r["unit"].partition("_")[0] for r in own]
            self.assertCountEqual(kinds, ["plunger"]*4 + ["tv"]*4 + ["amplifier", "screen"])
        def compete(a):
            try:
                a.exchange("reserve",unit="screen",point=[1200,540])
                return True
            except Wait:
                return False
        with ThreadPoolExecutor(3) as pool:
            self.assertEqual(sum(pool.map(compete,self.alts)),1)
        for a in self.alts:
            with self.assertRaises(Wait):
                a.exchange("reserve",unit="screen",point=position(3,"tv_3"))
            with self.assertRaises(Wait):
                a.exchange("reserve",unit="screen",point=[765,528])
        self.match.command(2,"Aerial Attack")
        self.assertIsNone(self.alts[0].exchange()["command"])
        cmd=self.alts[1].exchange()["command"]
        self.assertEqual(self.alts[1].exchange("claim",id=cmd["id"])["claimed"]["name"],"Aerial Attack")
        self.assertIsNone(self.alts[1].exchange()["command"])
        self.assertIsNone(self.alts[1].exchange("claim",id=cmd["id"])["claimed"])
        self.alts[1].exchange("result",id=cmd["id"],result="OK")
        self.assertIsNone(self.alts[1].exchange()["command"])
        self.match.stop()
        self.match.start("hard","S4R")
        with self.assertRaises(Wait):
            self.alts[0].exchange("commit",unit="screen",point=[1150,540])

    def test_identity_and_lease(self):
        a=self.alts[0]
        with patch.object(a.connection,"key",self.alts[1].connection.key),self.assertRaises(Wait):
            a.exchange()
        with patch.object(a.connection,"instance","another"),self.assertRaises(Wait):
            a.exchange()
        self.match.command(1,"Hook and Punch")
        self.match.pending[1]["until"] = time.monotonic()-1
        self.assertIsNone(a.exchange()["command"])
        self.match.stop()
        with self.assertRaises(Wait):
            a.guard()

    def test_individual_summon_and_ack_retry_during_match(self):
        a, other, _ = self.alts
        self.match.summon(1,PRIVATE_LINK)
        with self.assertRaisesRegex(ValueError,"уже отправлен"):
            self.match.summon(1,PRIVATE_LINK)
        request = a.exchange()["summon"]
        self.assertIsNone(other.exchange()["summon"])
        with patch("twd_bot.os.startfile",create=True) as launch:
            with patch.object(a,"exchange",side_effect=Wait("временный обрыв")), self.assertRaises(Wait):
                a.join_private(request)
            a.join_private(a.exchange()["summon"])
            launch.assert_called_once()
        self.assertIsNone(a.exchange()["summon"])
        self.assertEqual(a.exchange()["run"],"")
        self.assertTrue(other.exchange()["run"])
        self.match.start("nightmare","S4R")
        self.assertEqual(a.exchange()["run"], self.match.run)

    def test_private_link_validation_and_failure(self):
        a = self.alts[0]
        for invalid in ("", "file:///test.exe", PRIVATE_LINK.replace(".com/",".com.example/"),
                        PRIVATE_LINK.replace("Server","ExperienceDetails"), "roblox://other"):
            with self.assertRaises(ValueError):
                self.match.summon(1,invalid)
        legacy = "https://www.roblox.com/games/123/TWD?privateServerLinkCode=Test123"
        self.match.summon(1,legacy)
        with patch("twd_bot.os.startfile",side_effect=OSError,create=True) as launch, patch("twd_bot.log"):
            a.join_private(a.exchange()["summon"])
            launch.assert_called_once_with(legacy.replace("/TWD",""))
        self.assertEqual(a.exchange()["run"],self.match.run)
        self.assertIn("Не удалось",self.match.results[1])

    def test_battle_order(self):
        a=self.alts[0]
        a.phase="battle"
        frame=Image.new("RGB",(1366,768))
        calls=[]
        def place(unit,img):
            pt=position(1,unit)
            a.exchange("reserve",unit=unit,point=pt)
            a.exchange("commit",unit=unit,point=pt)
            calls.append(unit)
        def improve(unit,action):
            self.assertEqual(action,"Upgrade")
            a.levels[unit]+=1
            calls.append(unit)
        with patch.object(a,"place",side_effect=place),patch.object(a,"manager",side_effect=improve), \
             patch.object(a.game,"grab",return_value=frame),patch.object(a.game,"ready_visible",return_value=True), \
             patch.object(a.game,"click",side_effect=lambda _:calls.append("ready")),patch.object(a.game,"money",return_value=100000):
            for _ in range(27):
                a.next_upgrade=0
                a.tick(a.exchange())
        self.assertEqual(calls,["plunger","ready","plunger_2","plunger_3","plunger_4",
                                "tv","tv_2","tv_3","tv_4","amplifier","screen"]+["amplifier","screen"]*8)

    def test_blocked_then_paid_placement(self):
        alt=self.alts[0]
        game=Mock()
        frame=Image.new("RGB",(1366,768))
        game.grab.return_value=frame
        game.take.return_value=True
        game.money.side_effect=[900,900,900,200]
        game.path_visible.side_effect=[True,False,False]
        pose=(np.array([.41,.41]),np.diag([1/2048,1/1152]))
        with patch.object(alt,"game",game),patch("wastelands_alt.road_pose",return_value=pose), \
             patch("twd_bot.read_hotbar",return_value=[(.532,700)]):
            self.assertIn("занята",alt.place("plunger_2",frame))
            self.assertNotIn("target",self.match.places[1,"plunger_2"])
            self.assertIn("Поставил Plunger 2/4",alt.place("plunger_2",frame))
        self.assertEqual(self.match.places[1,"plunger_2"]["point"],position(1,"plunger_2",1))
        self.assertEqual(self.match.places[1,"plunger"]["state"],"reserved")
        self.assertEqual([call.args for call in game.take.call_args_list], [(4,), (4,)])
        self.assertEqual(game.click.call_count,2)

    def test_teleport_frame_and_ack(self):
        a=self.alts[1]
        self.match.command(2,"snapshot")
        cmd=a.exchange()["command"]
        a.exchange("result",id=cmd["id"],result="Выбери место",frame="test")
        self.assertEqual(self.match.frames[2],(cmd["id"],"test"))
        self.match.command(2,"Teleport",frame_id=cmd["id"],point=[.65,.59])
        cmd2=a.exchange()["command"]
        self.assertEqual(cmd2["frame_id"],cmd["id"])
        self.assertIsNone(self.alts[0].exchange()["command"])
        a.exchange("result",id=cmd["id"],result="stale")
        self.assertEqual(a.exchange()["command"]["id"],cmd2["id"])


class VisionTest(unittest.TestCase):
    def test_printed_cooldown_is_not_active_timer(self):
        row=[("45s",.3,.4,.03,.02),("cooldown",.34,.4,.05,.02)]
        self.assertIsNone(countdown(row,"Aerial Attack",(.36,.38)))
        self.assertEqual(countdown([("39s",.32,.39,.03,.02)],"Aerial Attack",(.35,.38)),39)
    def test_road_at_rdp_resolution(self):
        for angle,zoom in [(0,1),(18,.96),(-11,1.06)]:
            frame=Image.new("RGB",(1366,768),(118,100,80))
            draw=ImageDraw.Draw(frame)
            rad=math.radians(angle)
            mat=1366/2048*zoom*np.array([[math.cos(rad),-math.sin(rad)],[math.sin(rad),math.cos(rad)]])
            def point(p):
                return tuple((np.array(p)-[1024,576])@mat.T+[683,384])
            for a,b in [((0,-95),(2048,1305)),((835,475),(990,246)),((990,246),(730,73)),((1550,965),(1420,1160))]:
                draw.line((point(a),point(b)),fill=(218,64,47),width=round(1366/2048*zoom*48))
            pose=road_pose(frame)
            self.assertIsNotNone(pose)
            for p in ([930,452],[1336,751],[1770,1029]):
                pixel=np.array(screen_point(pose,p))*frame.size
                self.assertLess(np.linalg.norm(pixel-point(p)),19,(angle,p,pixel,point(p)))
        self.assertIsNone(road_pose(Image.new("RGB",(1366,768))))

    def test_stationary_terrain_without_opencv(self):
        from wastelands_view import tracked_pose
        terrain = np.random.default_rng(12).integers(0,256,(180,320),dtype=np.uint8)
        frame = Image.fromarray(terrain)
        pose = (np.array([.41,.41]),np.diag([1/2048,1/1152]))
        with patch("wastelands_view.cv2", None):
            self.assertIs(tracked_pose(frame,pose,frame),pose)
            self.assertIsNone(tracked_pose(frame,pose,Image.fromarray(np.roll(terrain,4,axis=1))))
            blank = Image.new("L",frame.size)
            self.assertIsNone(tracked_pose(blank,pose,blank))

    @unittest.skipUnless(sys.platform=="win32","Windows OCR")
    def test_windows_manager_ocr(self):
        im=Image.new("RGB",(1366,768),(55,55,55))
        d=ImageDraw.Draw(im)
        font=ImageFont.truetype("arialbd.ttf",20)
        d.rectangle((385,150,690,410),fill=(56,28,28),outline=(255,8,8),width=4)
        for xy,t in [((440,70),"UNIT MANAGER"),((416,162),"Titan Screen Man"),((525,205),"Level: 6 / 8"),
                     ((458,275),"Teleport"),((425,355),"Upgrade"),((565,355),"$28,575")]:
            d.text(xy,t,font=font,fill="white")
        reader=OCR()
        self.addCleanup(reader.close)
        words=reader.read(im)
        self.assertIsNotNone(label(words,"UNIT MANAGER"))
        row=manager_card(im,words,"screen")
        self.assertTrue(row,words)
        self.assertEqual(level(row),6)
        self.assertIsNotNone(label(row,"Teleport"))
        self.assertIsNone(label(row,"Hook and Punch"))


if __name__=="__main__":
    unittest.main()
