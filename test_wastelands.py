import math
import sys
import threading
import time
import unittest
import base64
import json
import tempfile
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import Mock, patch

import numpy as np
from PIL import Image, ImageDraw, ImageFont

from wastelands_alt import Alt, Wait, level, manager_card, countdown
from wastelands_team import Match, PLAYERS, UNITS, position, serve
from wastelands_view import OCR, label, road_pose, screen_point


class IntegrationTest(unittest.TestCase):
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
                panel.group_attack.invoke()
                panel.render_players()
                self.assertEqual(set(panel.match.pending),{1})
                self.assertIn("Команда отправлена",panel.player_results[1].cget("text"))
                panel.run_button.invoke()
                self.assertEqual(panel.match_fields.winfo_manager(),"pack")
                self.assertEqual(panel.player_actions[1].winfo_manager(),"")
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


class NetworkTest(unittest.TestCase):
    def setUp(self):
        self.match = Match()
        self.server = serve(self.match,("127.0.0.1",0))
        self.addCleanup(self.server.server_close)
        self.addCleanup(self.server.shutdown)
        self.alts = []
        for i in PLAYERS:
            a = Alt("127.0.0.1",i,self.match.keys[i],dict(zip(UNITS,(4,5,1,3))),
                    threading.Event(),lambda status:None)
            a.url = f"http://127.0.0.1:{self.server.server_port}/alt/{i}"
            self.alts.append(a)
        self.match.start("nightmare","S4R")
        for a in self.alts:
            a.reset(a.exchange())

    def test_three_clients_and_contested_teleport(self):
        for unit in UNITS:
            for a in self.alts:
                p = position(a.player,unit)
                a.exchange("reserve",unit=unit,point=p)
                a.exchange("commit",unit=unit,point=p)
                a.exchange("commit",unit=unit,point=p)
        self.assertEqual(len(self.alts[2].exchange()["places"]),12)
        def compete(a):
            try:
                a.exchange("reserve",unit="screen",point=[1150,540])
                return True
            except Wait:
                return False
        with ThreadPoolExecutor(3) as pool:
            self.assertEqual(sum(pool.map(compete,self.alts)),1)
        for a in self.alts:
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
        with patch.object(a,"key",self.alts[1].key),self.assertRaises(Wait):
            a.exchange()
        with patch.object(a,"instance","another"),self.assertRaises(Wait):
            a.exchange()
        self.match.command(1,"Hook and Punch")
        self.match.pending[1]["until"] = time.monotonic()-1
        self.assertIsNone(a.exchange()["command"])
        self.match.stop()
        with self.assertRaises(Wait):
            a.guard()

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
            for _ in range(21):
                a.next_upgrade=0
                a.tick(a.exchange())
        self.assertEqual(calls,["plunger","ready","tv","amplifier","screen"]+["amplifier","screen"]*8)

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
            self.assertIn("занята",alt.place("plunger",frame))
            self.assertNotIn("target",self.match.places[1,"plunger"])
            self.assertIn("Поставил",alt.place("plunger",frame))
        self.assertEqual(self.match.places[1,"plunger"]["point"],position(1,"plunger",1))
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
