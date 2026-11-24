import math
import sys
import threading
import time
import unittest
import base64
import json
import tempfile
import queue
from contextlib import ExitStack
from functools import partial
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import Mock, patch

import numpy as np
from PIL import Image, ImageDraw, ImageFont

from wastelands_alt import Alt, Game, Wait, UnitCounts, level, manager_card, manager_total, manager_unit_count, placement_cash, preserve_bank_capacity, visual_manager_total, countdown
from wastelands_team import AltConnection, BRANCH, JUNCTION, Match, PAIR_LIFETIME, PLACEMENT_ORDER, PLAYERS, TRUNK, UNITS, bank_slot, connect_by_pin, position, serve
from wastelands_view import ANCHOR, OCR, label, placement_in_view, road_pose, screen_point
from wastelands_manager import titan_cards, upgrade_price

PRIVATE_LINK = "https://www.roblox.com/share?code=Test123&type=Server"


def titan_manager_frame(levels=(0,0), *, reverse=False, left=974):
    import twd_bot as farm
    with Image.open(Path(__file__).parent/"tests/fixtures/titans_rdp.png") as fixture:
        row = fixture.convert("RGB")
    for level_value,x in zip(levels,(125,293)):
        if level_value==0:
            continue
        ImageDraw.Draw(row).rectangle((x-1,31,x+8,42),fill=(46,22,24))
        if level_value is not None:
            glyph,aspect = farm._get_templates()[str(level_value)]
            ink = Image.fromarray((glyph*255).astype(np.uint8)).resize((round(aspect*9),9),Image.Resampling.LANCZOS)
            row.paste("white",(x,32,x+ink.width,41),ink)
    if reverse:
        first,second = row.crop((0,0,167,134)),row.crop((169,0,336,134))
        row.paste(second,(0,0))
        row.paste(first,(169,0))
    frame = Image.new("RGB",(1356,698),(89,73,52))
    draw = ImageDraw.Draw(frame)
    draw.rectangle((left,44,left+369,682),fill=(21,32,36),outline=(25,209,227),width=3)
    draw.rectangle((50,400,220,434),fill=(27,141,45))  # selected unit's separate upgrade
    draw.rectangle((left+9,638,left+181,670),fill=(27,141,45))  # Upgrade All
    draw.rectangle((left+185,638,left+360,670),fill=(148,15,17))  # Sell All
    frame.paste(row,(left+15,118))
    return frame


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
        def fetch(url,timeout):
            name = url.rsplit("/",1)[1]
            self.assertIn(name,farm.TEAM_FILES)
            self.assertEqual(url,f"https://raw.githubusercontent.com/{farm.UPDATE_REPO}/{farm.TEAM_REVISION}/{name}")
            return (src/name).read_bytes()
        with tempfile.TemporaryDirectory() as tmp, patch.object(farm,"HERE",tmp), \
             patch.object(farm,"_http_get",side_effect=fetch) as http:
            self.assertIsNone(farm.team_directory())
            cached = farm.team_directory(download=True)
            self.assertEqual(http.call_count,len(farm.TEAM_FILES))
            self.assertEqual(farm.team_directory(),cached)
            for name in farm.TEAM_FILES:
                self.assertEqual((Path(cached)/name).read_bytes(),(src/name).read_bytes())

    def test_offline_open_with_bundled_or_previously_cached_components(self):
        import twd_bot as farm
        src = Path(farm.HERE)
        with tempfile.TemporaryDirectory() as tmp, patch.object(farm,"HERE",tmp), \
             patch.object(farm,"_http_get",side_effect=AssertionError("unexpected download")):
            root = Path(tmp)
            previous = root/".twd-wastelands"/"6.0.14"
            previous.mkdir(parents=True)
            for name in farm.TEAM_FILES:
                (root/name).write_bytes((src/name).read_bytes())
            self.assertEqual(farm.team_directory(),tmp)
            for name in ("wastelands.py","wastelands_alt.py"):
                (root/name).rename(previous/name)
                (root/name).write_bytes(b"outdated")
            directory = Path(farm.team_directory(download=True))
            for name in farm.TEAM_FILES:
                self.assertEqual((directory/name).read_bytes(),(src/name).read_bytes())

    def test_damaged_download_can_be_retried(self):
        import twd_bot as farm
        src = Path(farm.HERE)
        files = list(farm.TEAM_FILES)
        with tempfile.TemporaryDirectory() as tmp, patch.object(farm,"HERE",tmp):
            with patch.object(farm,"_http_get",side_effect=[(src/files[0]).read_bytes(),b"damaged"]):
                with self.assertRaisesRegex(ValueError,files[1]):
                    farm.team_directory(download=True)
            self.assertIsNone(farm.team_directory())
            with patch.object(farm,"_http_get",side_effect=lambda url,timeout:(src/url.rsplit("/",1)[1]).read_bytes()) as http:
                cache = Path(farm.team_directory(download=True))
                self.assertEqual(http.call_count,len(files)-1)
                self.assertEqual((cache/files[1]).read_bytes(),(src/files[1]).read_bytes())


class InviteInputTest(unittest.TestCase):
    def test_button_and_cursor_must_still_match(self):
        frame = Image.new("RGB", (1366, 768))
        with Image.open(Path(__file__).parent / "tests/fixtures/wasteland_invite_buttons.png") as card:
            frame.paste(card, (1163, 229))
        game = Mock(spec=Game)
        game.click_live.side_effect = partial(Game.click_live,game)
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
        with self.assertRaisesRegex(Wait, "Кнопка"):
            Game.accept_invite(game, point)
        game.m.press.assert_called_once()

    def test_click_retries_until_confirmed(self):
        alt = Alt.__new__(Alt)
        alt.game, alt.ocr, alt.exchange = Mock(), Mock(), Mock()
        alt.reset({"run":"match", "progress":{}})
        alt.game.vote_button.return_value = None
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


class VoteTest(unittest.TestCase):
    def test_missed_vote_retries_and_confirmed_vote_stays_selected(self):
        alt = Alt.__new__(Alt)
        alt.game, alt.ocr, alt.exchange = Mock(), Mock(), Mock()
        alt.exchange.return_value = {"vote_seconds":6}
        alt.reset({"run":"match", "progress":{"invited":True}})
        alt.game.ready_visible.return_value = False
        alt.game.vote_button.return_value = {"cx":.59,"cy":.72,"w":.14,"h":.06}
        alt.vote_reading = Mock(side_effect=[((n,4),None) for n in (1,1,1,1,1,2)])
        state = {"mode":"nightmare", "host":"Host"}
        with patch("wastelands_alt.time.monotonic",return_value=100) as clock:
            self.assertIn("повторю",alt.lobby(state,None))
            self.assertFalse(alt.voted)
            clock.return_value = 103
            self.assertIn("подтверждён",alt.lobby(state,None))
            self.assertTrue(alt.voted)
            self.assertNotIn("READY",alt.lobby(state,None))
        self.assertEqual(alt.game.click_live.call_count,2)
        self.assertAlmostEqual(alt.game.click_live.call_args.args[0][0],.562)

    def test_ready_after_first_plunger_requires_confirmation(self):
        alt = Alt.__new__(Alt)
        alt.game, alt.ocr, alt.exchange = Mock(), Mock(), Mock()
        alt.exchange.return_value = {"vote_seconds":6}
        alt.reset({"run":"match", "progress":{"invited":True,"voted":True}})
        alt.game.vote_button.return_value = {"cx":.5,"cy":.19,"w":.1,"h":.06}
        alt.vote_reading = Mock(side_effect=[((n,4),None) for n in (0,0,0,0,0,1)])
        with patch("wastelands_alt.time.monotonic",return_value=100) as clock:
            self.assertIn("повторю",alt.vote("ready"))
            self.assertFalse(alt.ready)
            clock.return_value=103
            self.assertIn("подтверждён",alt.vote("ready"))
            self.assertTrue(alt.ready)
        alt.exchange.assert_any_call("ready")
        self.assertEqual(alt.game.click_live.call_args.args[0],(.5,.19))

    def test_voting_turn_released_or_expires(self):
        match = Match()
        match.start("nightmare","Host")
        def turn(p,op="vote_turn"):
            return match.exchange(p,{"op":op,"instance":str(p),"run":match.run})["vote_seconds"]
        with patch("wastelands_team.time.monotonic",return_value=100) as clock:
            self.assertGreater(turn(1),0)
            self.assertEqual(turn(2),0)
            turn(1,"vote_end")
            self.assertGreater(turn(2),0)
            clock.return_value=107
            self.assertGreater(turn(3),0)
            turn(2,"vote_end")
            self.assertEqual(turn(1),0)


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

    def test_afk_answer_uses_live_panel_and_waits_for_close(self):
        import twd_bot as farm
        frame = Image.new("L",(1366,768))
        x,y = 240,90
        draw = ImageDraw.Draw(frame)
        draw.line((x,y,x+238,y),fill=255)
        title = Image.fromarray(farm.AFK_HEADER.reshape(6,28)).resize((56,11),Image.Resampling.NEAREST)
        frame.paste(title,(x+8,y+9))
        for dx in (30,164):
            draw.rectangle((x+dx,y+56,x+dx+2,y+67),fill=255)
            draw.rectangle((x+dx,y+65,x+dx+8,y+67),fill=255)
        for dx in (94,128,196):
            draw.rectangle((x+dx,y+56,x+dx+8,y+67),outline=255)
        frame=frame.convert("RGB")
        panel=farm.afk_panel(frame)
        self.assertEqual(panel[3],2)
        for a in self.alts:
            state=a.exchange()
            self.assertTrue(state["afk_auto"])
            with patch.object(a,"game") as game:
                game.grab.return_value=frame
                self.assertIn("ответ отправлен",a.tick(state))
                pt,locate,title=game.click_live.call_args.args
                self.assertEqual(locate(frame),pt)
                self.assertIsNone(locate(Image.new("RGB",frame.size)))
                changed=frame.copy()
                changed.paste(frame.crop((x+154,y+54,x+178,y+71)),(x+86,y+54))
                self.assertIsNone(locate(changed))
                self.assertIn("жду закрытия",a.tick(state))
                game.click_live.assert_called_once()
                a.afk_retry_at=0
                a.tick(state)
                a.afk_retry_at=0
                self.assertIn("ручной",a.tick(state))
                self.assertEqual(game.click_live.call_count,2)
                self.assertIn("ручного",a.tick(dict(state,afk_auto=False)))
                a.stop.set()
                with self.assertRaises(Wait):
                    a.tick(state)
                a.stop.clear()
                self.assertEqual(game.click_live.call_count,2)
        self.match.start("nightmare","S4R",afk_auto=False)
        self.assertFalse(self.alts[0].connection.exchange()["afk_auto"])

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

    def test_unconfirmed_plunger_blocks_later_stages(self):
        a=self.alts[0]
        a.phase="battle"
        for unit in PLACEMENT_ORDER:
            if unit not in ("plunger_4","amplifier","screen"):
                point=position(a.player,unit)
                a.exchange("reserve",unit=unit,point=point)
                a.exchange("commit",unit=unit,point=point)
        target=position(a.player,"plunger_4")
        a.exchange("reserve",unit="plunger_4",point=target)
        frame=Image.new("RGB",(1366,768))
        with patch.object(a.game,"grab",return_value=frame),patch.object(a,"place",return_value="placing") as place:
            self.assertIn("Plunger",a.tick(a.exchange()))
            place.assert_not_called()
        self.assertEqual(a.pending_places,{"plunger_4"})
        self.assertEqual(self.match.places[1,"plunger_4"]["target"],target)

    def test_plunger_slot_backoff_and_exhaustion_never_select_tv(self):
        a=self.alts[0]
        a.phase="battle"
        a.wait_for_check("Plunger · жду счётчик",10)
        frame=Image.new("RGB",(1366,768))
        with patch.object(a.game,"grab",return_value=frame),patch.object(a,"place") as place:
            self.assertIn("счётчик",a.tick(a.exchange()))
            place.assert_not_called()
            a.next_check=0
            for u in PLACEMENT_ORDER[:4]:
                a.rescan_at[u]=time.monotonic()+4
            self.assertIn("поиск",a.tick(a.exchange()))
            place.assert_not_called()
            a.rescan_at["plunger"]=0
            a.tick(a.exchange())
            self.assertEqual(place.call_args.args[0],"plunger")
            a.at_limit.add("plunger")
            a.tick(a.exchange())
            self.assertEqual(place.call_args.args[0],"tv")

    def test_all_three_vote_ready_while_plunger_is_unavailable(self):
        frame=Image.new("RGB",(1366,768))
        ImageDraw.Draw(frame).rectangle((611,120,755,167),fill=(0,155,0))
        for i,a in enumerate(self.alts):
            a.phase="battle"
            a.wait_for_check("Plunger · жду счётчик",10)
            with patch.object(a.game,"grab",return_value=frame),patch.object(a.game,"click_live") as click, \
                 patch.object(a,"vote_reading",side_effect=[((i,4),None),((i+1,4),None)]):
                a.tick(a.exchange())
                click.assert_called_once()
                self.assertTrue(a.exchange()["progress"]["ready"])

    def test_host_assigns_titan_alternatives_for_all_three_alts(self):
        for a in self.alts:
            for unit in ("amplifier","screen"):
                with patch("wastelands_alt.position",side_effect=AssertionError("local layout")):
                    sites=a.placement_sites(unit)
                self.assertEqual(sites[:30],[position(a.player,unit,n) for n in range(30)])
                self.assertGreater(len({tuple(site) for site in sites[30:]}),50)
                point=sites[8]
                a.exchange("reserve",unit=unit,point=point)
                a.exchange("commit",unit=unit,point=point)
                self.assertEqual(self.match.places[a.player,unit]["point"],point)

    def test_screen_skips_debris_and_tries_a_new_site_after_verified_rejection(self):
        a=self.alts[0]
        frame=Image.new("RGB",(1366,768),(112,90,53))
        pose=(np.array([.41,.41]),np.diag([1/2048,1/1152]))
        preferred=position(1,"screen")
        cx,cy=np.asarray(screen_point(pose,preferred))*frame.size
        ImageDraw.Draw(frame).rectangle((cx-22,cy-22,cx+22,cy+22),fill=(72,72,70))
        with patch.object(a,"game") as game,patch("wastelands_alt.placement_pose",return_value=pose), \
             patch.object(a,"hover_count",side_effect=[0,0,0,1]),patch.object(a,"manager_counts",return_value=UnitCounts(0,0)):
            game.grab.return_value=frame
            a.place("screen",frame)
            self.assertIn("жду обновления",a.recheck_pending(a.exchange()))
            self.assertIn("прежнее",a.recheck_pending(a.exchange()))
            a.place("screen",frame)
            self.assertIn("Поставил",a.recheck_pending(a.exchange()))
            first,second=[call.args[0] for call in game.click_live.call_args_list]
            self.assertGreater(np.linalg.norm((np.array(first)-screen_point(pose,preferred))*frame.size),22)
            self.assertGreater(np.linalg.norm((np.array(first)-second)*frame.size),26)
            np.testing.assert_allclose(screen_point(pose,self.match.places[1,"screen"]["point"]),second)

    def test_first_screen_explores_past_five_rejected_patches_and_remembers_success(self):
        a = self.alts[0]
        amp = min(a.placement_sites("amplifier"),key=lambda p:math.dist(p,(1278,646)))
        a.exchange("reserve",unit="amplifier",point=amp,slot=1,count_before=0,total_before=8)
        a.exchange("commit",unit="amplifier",point=amp)
        sites = a.placement_sites("screen")
        missed = [(1294,722),(1336,751),(1367,706),(1175,608),(1219,638)]
        for target in missed:
            point = min(sites,key=lambda p:math.dist(p,target))
            self.assertLess(math.dist(point,target),1)
            state = a.exchange("reserve",unit="screen",point=point,slot=3,count_before=0,total_before=9)
            a.update_places(state)
            a.funded_lease = ("screen",tuple(point),self.match.places[1,"screen"]["target_since"])
            with patch.object(a,"placement_readback",return_value=UnitCounts(0,9)):
                a.recheck_pending(state)
                a.recheck_pending(state)
        self.assertNotIn("1/screen",self.match.titan_sites)
        # The old 35-second shared cooldown has expired; obstacles still exist.
        self.match.rejections.clear()
        a.local_rejections.clear()
        a.update_places(a.exchange())
        frame=Image.new("RGB",(1356,698),(115,93,54))
        pose=(np.array([.40,.4]),np.diag([1/2048,1/1152]))
        with patch.object(a,"game") as game,patch.object(a,"map_pose",return_value=pose), \
             patch("wastelands_alt.placement_cash",return_value=20000), \
             patch.object(a,"placement_baseline",return_value=UnitCounts(0,9)):
            game.grab.return_value = frame
            a.place("screen",frame)
            game.click_live.assert_called_once()
            chosen = self.match.places[1,"screen"]["target"]
            self.assertTrue(all(math.dist(chosen,p)>=24 for p in missed))
            self.assertGreaterEqual(math.dist(chosen,amp),54)
            with patch.object(a,"placement_readback",return_value=UnitCounts(1,10)):
                self.assertIn("Поставил",a.recheck_pending(a.exchange()))
        saved = self.match.titan_sites
        self.assertEqual(saved,{"1/amplifier":amp,"1/screen":chosen})
        restarted = Match(dict(saved,**{"2/screen":[999,999]}))
        restarted.start("nightmare","Host")
        for u,p in (("screen",chosen),("amplifier",amp)):
            plan = restarted.exchange(1,{"instance":"test","run":restarted.run,"op":"placement_sites","unit":u})
            self.assertEqual(plan["preferred_site"],p)
        self.assertNotIn("2/screen",restarted.titan_sites)

    def test_personal_titan_card_and_total_can_resolve_a_stale_hover(self):
        a = self.alts[1]
        with patch.object(a,"hover_count",return_value=0), \
             patch.object(a,"manager_counts",return_value=UnitCounts(1,10)) as manager:
            self.assertEqual(a.placement_readback("screen",2,UnitCounts(0,9),True),UnitCounts(1,10))
            self.assertEqual(a.placement_baseline("screen",2,1).slot,1)
            manager.return_value = UnitCounts(1,9)
            self.assertEqual(a.placement_readback("screen",2,UnitCounts(0,9),True),UnitCounts())

    def test_paid_rejection_skips_the_same_patch_across_copies_and_players(self):
        a=self.alts[2]
        center,_,normal=map(np.asarray,bank_slot(3,"tv"))
        p=(center+46*normal).tolist()
        adjacent=position(3,"tv",1)
        self.assertLess(math.dist(p,adjacent),26)
        for funded in (False,True):
            with self.subTest(funded=funded):
                self.match.start("nightmare","Host")
                a.reset(a.exchange())
                state=a.exchange("reserve",unit="tv",point=p,slot=4,count_before=0,total_before=4)
                a.update_places(state)
                since=self.match.places[3,"tv"]["target_since"]
                a.funded_lease=("tv",tuple(p),since) if funded else None
                with patch.object(a,"placement_readback",return_value=UnitCounts(0,4)):
                    a.recheck_pending(state)
                    self.assertFalse(a.exchange()["rejected_sites"])
                    a.recheck_pending(state)
                self.assertIn(("early",tuple(p)),a.local_rejections)
                self.assertEqual(bool(a.exchange()["rejected_sites"]),funded)
                if funded:
                    # The other helper's shared bank includes the same center.
                    with self.assertRaisesRegex(ValueError,"недавно отклонила"):
                        self.match.reserve(1,"tv_3",position(3,"tv"))
                    with patch("wastelands_team.time.monotonic",return_value=time.monotonic()+40):
                        self.match.reserve(1,"tv_3",position(3,"tv"))
                else:
                    self.match.reserve(1,"tv_3",position(3,"tv"))

    def test_offscreen_titan_remeasures_after_turn_and_restores_an_unverified_view(self):
        a=self.alts[2]
        frame=Image.new("RGB",(1366,768),(110,88,53))
        size=np.asarray(frame.size)
        origin=np.array([.596,.670])
        mat=np.array([[-.0004268,.0002371],[-.0004639,-.0008350]])
        view=[(origin,mat)]
        def turn(px):
            angle=math.radians(px/5)
            co,si=math.cos(angle),math.sin(angle)
            rotate=np.array([[co,-si],[si,co]])
            o,m=view[0]
            view[0]=(.5+(rotate@((o-.5)*size))/size,(rotate@(m*size[:,None]))/size[:,None])
        with patch.object(a,"game") as game,patch.object(a,"hover_count",return_value=0), \
             patch.object(a,"manager_counts",return_value=UnitCounts(0,8)), \
             patch("wastelands_alt.placement_cash",return_value=10000), \
             patch("wastelands_alt.placement_pose",side_effect=lambda f:view[0]) as fit, \
             patch("wastelands_alt.tracked_pose",return_value=None):
            game.grab.return_value=frame
            game.px_per_deg=5
            game.turn_camera.side_effect=turn
            self.assertIn("повернул",a.place("amplifier",frame))
            self.assertFalse(self.match.places[3,"amplifier"].get("target"))
            first=game.turn_camera.call_args.args[0]
            fit.side_effect=lambda f:None
            self.assertIn("вернул",a.place("amplifier",frame))
            self.assertEqual(game.turn_camera.call_args.args[0],-first)
            game.click_live.assert_not_called()
            fit.side_effect=lambda f:view[0]
            for _ in range(4):
                a.next_turn_at=0
                a.place("amplifier",frame)
                if game.click_live.called:
                    break
            game.click_live.assert_called_once()
            target=self.match.places[3,"amplifier"]["target"]
            click=game.click_live.call_args.args[0]
            np.testing.assert_allclose(screen_point(view[0],target),click)
            self.assertTrue(placement_in_view(*click))
            self.assertFalse(placement_in_view(*screen_point((origin,mat),target)))
            with patch.object(a,"placement_readback",return_value=UnitCounts(1,9)):
                self.assertIn("Поставил",a.recheck_pending(a.exchange()))

    def test_ambiguous_screen_keeps_single_reservation(self):
        a=self.alts[1]
        frame=Image.new("RGB",(1366,768),(110,86,52))
        pose=(np.array([.4,.4]),np.diag([1/2048,1/1152]))
        with patch.object(a,"game") as game,patch("wastelands_alt.placement_pose",return_value=pose), \
             patch.object(a,"hover_count",side_effect=[0,None]),patch.object(a,"manager_counts",return_value=UnitCounts()):
            game.grab.return_value=frame
            a.place("screen",frame)
            self.assertIn("сверяю",a.recheck_pending(a.exchange()))
            game.click_live.assert_called_once()
            self.assertTrue(self.match.places[a.player,"screen"]["target"])

    def test_manager_proves_zero_only_with_every_card_accounted_for(self):
        def word(text,x,y):
            return (text,x,y,.12,.018)
        words=[word("UNIT MANAGER",.42,.02), word("UNITS 4",.04,.065)]
        cards=[word("Hero Camcorderman 2.0",x,y) for x in (.07,.55) for y in (.16,.48)]
        self.assertEqual(manager_unit_count(words+cards,"tv",4),0)
        self.assertIsNone(manager_unit_count(words+cards[:-1],"tv",4))
        cards[-1]=word("Scientist Screen Man",.55,.48)
        self.assertEqual(manager_unit_count(words+cards,"tv",4),1)

    def test_manager_reads_personal_total_when_list_is_clipped(self):
        a=self.alts[1]
        frame=Image.new("RGB",(1366,768))
        words=[("UNITS",.04,.065,.09,.018),("7",.137,.065,.025,.018)]
        with patch.object(a,"game") as game,patch.object(a,"header",return_value=None), \
             patch.object(a,"placement_text",return_value=words),patch.object(a,"close_manager") as close, \
             patch("wastelands_alt.manager_bounds",side_effect=[None,(300,20,620,710),(300,20,620,710)]):
            game.grab.return_value=frame
            self.assertEqual(a.manager_counts("tv",4,cards=True),UnitCounts(None,7))
            game.key.assert_called_once_with("v")
            close.assert_called_once()
        self.assertEqual(manager_total([("UNITS 0",.04,.065,.09,.018)]),0)
        self.assertIsNone(manager_total([("Upgrade",.04,.065,.09,.018),("7",.139,.065,.025,.018)]))

    def test_pending_placement_recovers_without_manual_retry_or_second_click(self):
        a=self.alts[1]
        a.phase="battle"
        a.ready=True
        p=position(a.player,"plunger")
        a.exchange("reserve",unit="plunger",point=p,count_before=0,total_before=0,slot=3)
        frame=Image.new("RGB",(1366,768))
        with patch.object(a.game,"grab",return_value=frame),patch.object(a.game,"click_live") as click, \
             patch.object(a,"hover_count",return_value=None), \
             patch.object(a,"manager_counts",side_effect=[UnitCounts()]*4+[UnitCounts(None,1)]) as manager:
            for i in range(4):
                a.next_check=0
                status=a.tick(a.exchange())
                self.assertIn("сверяю",status)
                self.assertEqual(status,a.tick(a.exchange()))
                self.assertEqual(manager.call_count,i+1)
            a.next_check=0
            self.assertIn("Поставил",a.tick(a.exchange()))
            self.assertEqual(self.match.places[2,"plunger"]["state"],"placed")
            click.assert_not_called()

    def test_unbuilt_early_plans_release_ground_but_actual_claims_block_it(self):
        a,b=self.alts[1:]
        first=position(2,"tv",3)
        adjacent=position(3,"tv_2")
        self.assertLess(math.dist(first,adjacent),26)
        a.exchange("reserve",unit="tv",point=first)
        with self.assertRaisesRegex(Wait,"Рядом занят"):
            b.exchange("reserve",unit="tv_2",point=adjacent)
        a.exchange("release",unit="tv",point=first)
        b.exchange("reserve",unit="tv_2",point=adjacent)
        b.exchange("commit",unit="tv_2",point=adjacent)
        with self.assertRaisesRegex(Wait,"Рядом занят"):
            a.exchange("reserve",unit="tv",point=first)

    def test_personal_totals_cannot_resolve_two_concurrent_clicks(self):
        a,other=self.alts[:2]
        site=position(a.player,"tv")
        a.exchange("reserve",unit="tv",point=site,total_before=4,slot=5)
        with self.assertRaisesRegex(Wait,"предыдущей постановки"):
            a.exchange("reserve",unit="amplifier",point=position(a.player,"amplifier"),total_before=4)
        other.exchange("reserve",unit="tv",point=position(other.player,"tv"),total_before=4)
        self.assertEqual(a.exchange()["places"],other.exchange()["places"])
        self.assertEqual(self.match.places[1,"tv"]["slot"],5)

    def test_counter_comparison_requires_a_common_source_and_agreement(self):
        for before,after,delta in (
            (UnitCounts(0,None),UnitCounts(None,1),None),
            (UnitCounts(2,6),UnitCounts(2,7),None),
            (UnitCounts(2,6),UnitCounts(None,7),1),
            (UnitCounts(2,6),UnitCounts(2,6),0),
            (UnitCounts(2,6),UnitCounts(3,None),1),
            (UnitCounts(2,6),UnitCounts(4,8),2),
        ):
            self.assertEqual(before.delta(after),delta)

    def test_hover_samples_only_selected_icon_without_click(self):
        a=self.alts[0]
        frame=Image.new("RGB",(1356,698))
        for reads,expected in (([2,2],2),([None,0,0],0),([0,1,0,1],None),([2,None,2,None],None)):
            with patch.object(a,"game") as game,patch.object(a,"slot_count",side_effect=reads) as count, \
                 patch.object(a,"placement_text",return_value=[]):
                game.grab.return_value=frame
                self.assertEqual(a.hover_count(4,4),expected)
                x,y=game.hover.call_args.args[0]
                self.assertTrue(688<x*frame.width<767 and 570<y*frame.height<642)
                self.assertEqual([c.args[1:] for c in count.call_args_list],[(4,4)]*len(reads))
                game.click.assert_not_called()
                game.key.assert_not_called()

    def test_lost_commit_reply_and_stale_release_preserve_the_new_reservation(self):
        a=self.alts[1]
        p=position(a.player,"tv")
        a.exchange("reserve",unit="tv",point=p,total_before=4,slot=5)
        first=self.match.places[a.player,"tv"]["target_since"]
        a.exchange("release",unit="tv",point=p,target_since=first)
        a.exchange("reserve",unit="tv",point=p,total_before=4,slot=5)
        with self.assertRaisesRegex(Wait,"Резерв изменился"):
            a.exchange("release",unit="tv",point=p,target_since=first)
        state=a.exchange()
        a.reset(state)
        a.update_places(state)
        exchange=a.exchange
        def lose_receipt(op,**fields):
            exchange(op,**fields)
            raise Wait("Соединение потеряно после подтверждения")
        with patch.object(a,"placement_readback",return_value=UnitCounts(None,5)), \
             patch.object(a,"exchange",side_effect=lose_receipt),self.assertRaises(Wait):
            a.recheck_pending(state)
        with patch.object(a.game,"click_live") as click:
            self.assertTrue(a.update_places(a.exchange()))
            a.update_places(a.exchange())
            self.assertIsNone(a.recheck_pending(a.exchange()))
            self.assertIn("tv",a.placed)
            click.assert_not_called()

    def test_pending_titan_reconciles_after_restart_without_second_click(self):
        a=self.alts[0]
        for unit,count,expected in (("screen",0,"reserved"),("amplifier",1,"placed")):
            point=position(a.player,unit)
            a.exchange("reserve",unit=unit,point=point,count_before=0)
            state=a.exchange()
            a.reset(state)
            with patch.object(a,"game") as game,patch.object(a,"hover_count",return_value=count), \
                 patch.object(a,"manager_counts",return_value=UnitCounts()):
                if count==0:
                    self.assertIn("жду обновления",a.recheck_pending(state))
                self.assertIsNotNone(a.recheck_pending(state))
                game.click_live.assert_not_called()
                game.key.assert_not_called()
            row=self.match.places[a.player,unit]
            self.assertEqual(row["state"],expected)
            self.assertNotIn("target",row)

    def test_unreadable_or_full_slot_cannot_place(self):
        a=self.alts[0]
        frame=Image.new("RGB",(1366,768))
        for count in (None,1):
            with patch.object(a,"game") as game,patch.object(a,"hover_count",return_value=count), \
                 patch.object(a,"manager_counts",return_value=UnitCounts()), patch("twd_bot.read_hotbar",return_value=[]):
                game.money.return_value=22000
                a.place("amplifier",frame)
                game.click_live.assert_not_called()
                game.take.assert_not_called()
                self.assertNotIn("target",self.match.places[a.player,"amplifier"])

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
        ImageDraw.Draw(frame).rectangle((610,119,755,167),fill=(0,155,0))
        def place(unit,img):
            pt=position(1,unit)
            a.exchange("reserve",unit=unit,point=pt)
            a.exchange("commit",unit=unit,point=pt)
            calls.append(unit)
        def improve(unit,action,*,cash):
            self.assertEqual(action,"Upgrade")
            self.assertIsNone(unit)
            unit=min(a.levels,key=lambda name:a.levels[name] or 0)
            a.levels[unit]=a.levels[unit] or 0
            a.levels[unit]+=1
            calls.append(unit)
        with patch.object(a,"place",side_effect=place),patch.object(a,"manager",side_effect=improve), \
             patch.object(a.game,"grab",return_value=frame),patch.object(a,"vote_reading",side_effect=[((0,4),None),((1,4),None)]), \
             patch.object(a.game,"click_live",side_effect=lambda *args:calls.append("ready")),patch.object(a.game,"money",return_value=100000):
            for _ in range(27):
                a.next_upgrade=0
                a.tick(a.exchange())
        self.assertEqual(calls,["ready","plunger","plunger_2","plunger_3","plunger_4",
                                "tv","tv_2","tv_3","tv_4","amplifier","screen"]+["amplifier","screen"]*8)

    def test_individual_upgrades_read_both_levels_and_verify_purchase_through_battle_tick(self):
        a = self.alts[2]
        a.phase,a.ready,a.next_slot_check = "battle",True,float("inf")
        for unit in PLACEMENT_ORDER:
            self.match.places[a.player,unit]["state"] = "placed"
        levels = [0,0]
        panel_open = False
        hidden = Image.new("RGB",(1356,698))
        clicks = []
        def frame():
            return titan_manager_frame(levels,reverse=bool(sum(levels)%2)) if panel_open else hidden
        def toggle(key):
            nonlocal panel_open
            self.assertEqual(key,"v")
            panel_open = not panel_open
        def click(point,locate,title):
            self.assertTrue(panel_open)
            self.assertEqual(point,locate(frame()))
            index = min(range(2),key=levels.__getitem__)
            name = ("Amplifier","Screen")[index]
            self.assertEqual(title,"Upgrade "+name)
            x,y = np.asarray(point)*hidden.size
            column = index ^ (sum(levels)%2)
            self.assertLess(abs(x-(1048+169*column)),3)
            self.assertLess(abs(y-228),3)
            levels[index]+=1
            clicks.append(name)
        with patch.object(a,"game") as game,patch.object(a,"placement_text",return_value=[]), \
             patch("wastelands_alt.placement_cash",return_value=100000),patch("wastelands_alt.time.sleep"), \
             patch("twd_bot.log"):
            game.grab.side_effect=frame
            game.key.side_effect=game.k.release.side_effect=toggle
            game._vk.side_effect=lambda key:key
            game.click_live.side_effect=click
            for i in range(16):
                if i==5:  # A restarted worker must use the live levels.
                    a.reset(a.exchange())
                    a.phase,a.ready,a.next_slot_check = "battle",True,float("inf")
                a.next_upgrade=0
                status=a.tick(a.exchange())
                self.assertIn("Титаны 2/2",status)
                self.assertIn(f"Amplifier ур. {levels[0]}/8",status)
                self.assertIn(f"Screen ур. {levels[1]}/8",status)
                self.assertFalse(panel_open)
            self.assertIn("завершены",a.tick(a.exchange()))
            self.assertEqual(clicks,["Amplifier","Screen"]*8)
            self.assertEqual(game.key.call_count,16)
            game.click.assert_not_called()

    def test_upgrade_waits_for_money_and_requires_an_observed_level_change(self):
        a=self.alts[0]
        frame=titan_manager_frame()
        cards=titan_cards(frame)
        with patch.object(a,"game") as game,patch.object(a,"placement_text",return_value=[]):
            game.grab.return_value=frame
            self.assertIn("2,875",a.improve_titans(frame,cards,1000))
            game.click_live.assert_not_called()
            self.assertIn("Проверю результат",a.improve_titans(frame,cards,35675))
            self.assertEqual(a.levels,{"amplifier":0,"screen":0})
            locate=game.click_live.call_args.args[1]
            self.assertIsNone(locate(titan_manager_frame((1,0))))
            self.assertIsNone(locate(Image.new("RGB",frame.size)))
            bad=titan_manager_frame((None,0))
            self.assertIn("Сверяю",a.improve_titans(bad,titan_cards(bad),35675))
            game.click_live.assert_called_once()

    def test_all_three_complete_the_build_with_partial_and_delayed_readings(self):
        # Each RDP client sees the same road from its own spawn. The two small
        # blocked patches match the repeated TV attempts in the reported match.
        size=(1366,768)
        frames,poses=[],{}
        for angle,spawn in ((2.65,(990,550)),(.86,(1040,590)),(-.62,(1030,570))):
            frame=Image.new("RGB",size,(125,101,62))
            co,si=math.cos(angle),math.sin(angle)
            mat=.58*np.array([[co,-si],[si,co]])/np.array(size)[:,None]
            pose=(np.array([.5,.5])-mat@(np.array(spawn)-ANCHOR),mat)
            trunk,branch,junction=map(np.asarray,(TRUNK,BRANCH,JUNCTION))
            for start,end,normal in ((junction-650*trunk,junction+1100*trunk,branch),
                                     (junction,junction+276*branch,trunk),
                                     (junction+276*branch,junction+276*branch-420*trunk,branch)):
                corners=[tuple(np.asarray(screen_point(pose,p))*size) for p in
                         (start-24*normal,end-24*normal,end+24*normal,start+24*normal)]
                ImageDraw.Draw(frame).polygon(corners,fill=(169,46,38))
            frames.append(frame)
            poses[id(frame)]=pose
        rosters=[[] for _ in self.alts]
        clicks=[[] for _ in self.alts]
        failures=[[],[]]
        with ExitStack() as stack:
            stack.enter_context(patch("twd_bot.log"))
            stack.enter_context(patch("wastelands_alt.placement_pose",side_effect=lambda f:poses[id(f)]))
            stack.enter_context(patch("wastelands_alt.placement_cash",return_value=30000))
            for i,a in enumerate(self.alts):
                a.phase="battle"
                a.ready=True
                a.next_slot_check=float("inf")
                def click(pt,locate,name,i=i,a=a):
                    self.assertEqual(locate(frames[i]),pt)
                    self.assertTrue(placement_in_view(*pt))
                    pending=[r for r in self.match.places.values() if r["player"]==a.player and r.get("target")]
                    self.assertEqual(len(pending),1)
                    unit=pending[0]["unit"]
                    clicks[i].append(unit)
                    for failed,center in zip(failures,((1041,571),(891,311))):
                        if math.dist(pending[0]["target"],center)<17:
                            failed.append(pending[0]["target"])
                            return
                    rosters[i].append(unit)
                def hover(slot,limit,i=i,a=a):
                    kind=next(k for k,v in a.slots.items() if v==slot)
                    if i==0 or (i==2 and len(rosters[i])%3==2):
                        return None
                    return sum(u.partition("_")[0]==kind for u in rosters[i])
                def manager(kind,limit,*,cards,i=i):
                    # After the first unit all card titles may be clipped.
                    return UnitCounts(None,len(rosters[i]))
                game=stack.enter_context(patch.object(a,"game"))
                game.grab.return_value=frames[i]
                game.click_live.side_effect=click
                stack.enter_context(patch.object(a,"hover_count",side_effect=hover))
                stack.enter_context(patch.object(a,"manager_counts",side_effect=manager))
            for _ in range(40):
                for a in self.alts:
                    if len(a.placed)<10:
                        a.next_check=0
                        a.tick(a.exchange())
                if all(len(roster)==10 and len(a.placed)==10 for a,roster in zip(self.alts,rosters)):
                    break
        self.assertEqual(rosters,[list(PLACEMENT_ORDER) for _ in PLAYERS])
        self.assertEqual([len(p) for p in failures],[1,1])
        self.assertEqual(sum(map(len,clicks)),32)
        self.assertTrue(all(r["state"]=="placed" and not r.get("target") for r in self.match.places.values()))

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
    def test_individual_titan_cards_at_rdp_sizes_and_in_swapped_columns(self):
        for scale,reverse,left in ((.9,False,974),(1,False,974),(1.2,True,530),(1.5,False,550),(1.8,True,800)):
            frame=titan_manager_frame(reverse=reverse,left=left)
            frame=frame.resize(tuple(round(v*scale) for v in frame.size),Image.Resampling.LANCZOS)
            cards=titan_cards(frame)
            self.assertEqual(set(cards),{"amplifier","screen"})
            for index,(name,price) in enumerate((("amplifier",2875),("screen",3525))):
                card=cards[name]
                self.assertEqual(card.level,0)
                x,y=np.asarray(card.button)*frame.size/scale
                self.assertLess(abs(x-(left+74+169*(index^reverse))),3)
                self.assertLess(abs(y-228),3)
                if scale==1:
                    self.assertEqual(upgrade_price(frame,card),price)

    def test_partial_card_and_unrelated_green_bar_cannot_be_upgraded(self):
        frame=titan_manager_frame()
        # Keep both green frames but remove the label from only one.
        ImageDraw.Draw(frame).rectangle((1020,213,1087,240),fill=(20,90,24))
        cards=titan_cards(frame)
        self.assertIsNone(cards["amplifier"].button)
        self.assertIsNotNone(cards["screen"].button)
        # Scroll until the visible part of Screen no longer includes its button.
        ImageDraw.Draw(frame).rectangle((1158,185,1325,256),fill=(21,32,36))
        card=titan_cards(frame).get("screen")
        self.assertTrue(card is None or card.button is None)

    def test_hotbar_portraits_find_reordered_units_and_reject_ambiguous_layout(self):
        from wastelands_view import wastelands_slots
        with Image.open(Path(__file__).with_name("wastelands_hotbar.png")) as refs:
            icons = [refs.crop((x,0,x+32,32)).resize((50,52),Image.Resampling.BILINEAR)
                     for x in range(0,128,32)]
        frame = Image.new("RGB",(1366,768),(41,37,48))
        def put(slot,icon):
            x=round(frame.width*.5+(slot-3.5)*.13*frame.height)
            frame.paste(icon,(x-25,round(frame.height*.874)-26))
        for slot,icon in zip((6,1,4,3),icons):
            put(slot,icon)
        self.assertEqual(wastelands_slots(frame),dict(amplifier=6,screen=1,plunger=4,tv=3))
        put(2,icons[3])
        self.assertIsNone(wastelands_slots(frame))

    def test_visual_hotbar_counts_from_rdp_without_ocr(self):
        a = Alt.__new__(Alt)
        a.ocr = Mock()
        a.ocr.read.return_value = []
        fixtures = Path(__file__).parent/"tests"/"fixtures"
        for name,size,slot,limit,value in (
            ("plunger_zero",(1353,697),3,4,0),
            ("plunger_small",(1092,559),3,4,0),
            ("tv_two",(1356,698),4,4,2),
            ("titan_zero",(2047,1150),2,1,0),
        ):
            with self.subTest(name=name):
                frame = Image.new("RGB",size)
                x = a.slot_center(frame,slot)*frame.width
                with Image.open(fixtures/("count_"+name+".png")) as crop:
                    frame.paste(crop,(round(x-.046*frame.height),round(.854*frame.height)))
                a.ocr.read.reset_mock()
                self.assertEqual(a.slot_count(frame,slot,limit),value)
                a.ocr.read.assert_not_called()
                self.assertIsNone(a.slot_count(frame,slot,1 if limit==4 else 4))
                self.assertIsNone(a.slot_count(frame,slot+1,limit))

    def test_balance_on_rdp_over_green_arrows_and_wave_effects(self):
        import twd_bot as farm
        for value,size in ((1140,(1353,697)),(21535,(1354,697))):
            frame=Image.new("RGB",size)
            l,t,_,_=farm.MONEY_REGION
            with Image.open(Path(__file__).parent/"tests"/"fixtures"/f"cash_rdp_{value}.png") as crop:
                # Only the two green masks from the HUD are kept in the fixture.
                self.assertIsNone(farm.read_money_image(crop))
                frame.paste(crop,(int(size[0]*l),int(size[1]*t)))
            read=Mock()
            self.assertEqual(placement_cash(frame,read),value)
            read.assert_not_called()

    def test_manager_total_from_zero_through_ten_requires_footer_and_suffix(self):
        import twd_bot as farm
        panel=Image.new("RGB",(400,700),(20,30,32))
        draw=ImageDraw.Draw(panel)
        draw.rectangle((18,651,190,682),fill=(18,99,29))
        draw.rectangle((208,651,378,682),fill=(99,20,15))
        for i in range(5):
            draw.rectangle((15+7*i,40,19+7*i,50),fill="white")
        self.assertIsNone(visual_manager_total(panel))
        for n in range(11):
            draw.rectangle((53,36,105,55),fill=(20,30,32))
            x=56
            for char in str(n):
                glyph,aspect=farm._get_templates()[char]
                ink=Image.fromarray((glyph*255).astype("uint8")).resize((round(aspect*11),11),Image.Resampling.LANCZOS)
                panel.paste("white",(x,40,x+ink.width,51),ink)
                x+=ink.width+1
            self.assertEqual(visual_manager_total(panel),n)
        draw.rectangle((0,640,399,699),fill="black")
        self.assertIsNone(visual_manager_total(panel))

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

    def test_placement_uses_wrecks_at_opposite_headings(self):
        from wastelands_view import placement_pose
        for sign in (1,-1):
            frame = Image.new("RGB",(1366,768),(117,94,62))
            def point(p):
                return tuple((np.asarray(p)-[1024,576])*sign*1366/2048+[683,384])
            draw = ImageDraw.Draw(frame)
            for a,b in [((0,-95),(2048,1305)),((835,475),(990,246)),((990,246),(730,73)),((1550,965),(1420,1160))]:
                draw.line((point(a),point(b)),fill=(218,64,47),width=32)
            self.assertIsNone(placement_pose(frame))
            for pos in ((804,700),(505,515)):
                x,y=point(pos)
                draw.rectangle((x-25,y-17,x+25,y+17),fill=(69,69,48))
            pose=placement_pose(frame)
            self.assertIsNotNone(pose)
            placed=np.asarray(screen_point(pose,(951,424)))*frame.size
            self.assertLess(np.linalg.norm(placed-point((951,424))),16)

    def test_stationary_terrain_without_opencv(self):
        from wastelands_view import tracked_pose
        terrain = np.random.default_rng(12).integers(0,256,(180,320),dtype=np.uint8)
        frame = Image.fromarray(terrain)
        pose = (np.array([.41,.41]),np.diag([1/2048,1/1152]))
        with patch("wastelands_view.cv2", None):
            self.assertIs(tracked_pose(frame,pose,frame),pose)
            crowded=frame.copy()
            draw=ImageDraw.Draw(crowded)
            draw.rectangle((100,42,220,139),fill=38)
            draw.rectangle((25,75,280,98),fill=180)
            self.assertIs(tracked_pose(frame,pose,crowded),pose)
            self.assertIsNone(tracked_pose(frame,pose,Image.fromarray(np.roll(terrain,4,axis=1))))
            blank = Image.new("L",frame.size)
            self.assertIsNone(tracked_pose(blank,pose,blank))

    def test_two_remaining_bases_do_not_lose_the_last_free_stretch(self):
        middle,left,right=[900,320],[881,320],[919,320]
        self.assertEqual(preserve_bank_capacity([middle,left,right],2),[left,right,middle])
        self.assertEqual(preserve_bank_capacity([middle,left,right],1)[0],middle)

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
