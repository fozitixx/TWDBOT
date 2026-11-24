import math
import queue
import tempfile
import threading
import unittest
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest.mock import Mock, patch

import numpy as np
from PIL import Image, ImageDraw

from wastelands import App, worker_logs
from wastelands_alt import Alt
from wastelands_pairing import PairingProfile
from wastelands_team import (AltConnection, Match, PLAYERS, PairingExpired, UNITS,
                             connect_by_pin, near_rejection, placement_attempts,
                             placement_conflict, position, serve)
from wastelands_view import ANCHOR, rank_build_sites


class PairingTest(unittest.TestCase):
    def test_two_instances_see_the_same_new_host_keys(self):
        with tempfile.TemporaryDirectory() as tmp, ThreadPoolExecutor(max_workers=4) as pool:
            keys = list(pool.map(lambda _:PairingProfile(tmp).host_keys(Match().keys),range(8)))
            self.assertTrue(all(k==keys[0] for k in keys))

    def test_log_collection_reports_missing_profiles_and_keeps_only_team_lines(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = Path(tmp)/"test"/"Desktop"/"TWDBOT-release"
            base.mkdir(parents=True)
            line = "13:00:16 Wastelands · твинк 1 · Amplifier · commit · слот 1"
            (base/"twd_log.txt").write_text("12:59:01 Discord: unrelated\n"+line+"\n",encoding="utf-8")
            self.assertEqual(worker_logs(Path(tmp)),({"test":line+"\n"},["test2","test3"]))

    def test_empty_pin_reuses_only_the_selected_host(self):
        with tempfile.TemporaryDirectory() as tmp:
            app = App.__new__(App)
            app.profile = PairingProfile(tmp)
            key = Match().keys[2]
            app.profile.write("peer.key",dict(host="host-pc",player=2,key=key))
            slots = dict(zip(UNITS,(3,4,1,2)))
            app.slot_vars = {name:Mock(get=Mock(return_value=n)) for name,n in slots.items()}
            app.peer_addr = Mock(get=Mock(return_value="another-pc"))
            app.token = Mock(get=Mock(return_value=""))
            app.worker = None
            app.standalone = False
            app.status,app.stop,app.refresh_tabs,app.remember = Mock(),Mock(),Mock(),Mock()
            with patch("wastelands.threading.Thread") as thread:
                app._join()
                thread.assert_not_called()
                app.peer_addr.get.return_value = "host-pc"
                app._join()
                self.assertEqual(thread.call_args.kwargs["args"],("host-pc",2,key,None,slots))
                thread.return_value.start.assert_called_once()

    def test_restart_host_and_three_clients_without_consuming_another_pin(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            profile = PairingProfile(root/"host")
            host = Match()
            host.keys = profile.host_keys(host.keys)
            server = serve(host,("127.0.0.1",0))
            slots = dict(zip(UNITS,(3,4,1,2)))
            def worker(i,pin=None):
                app = App.__new__(App)
                app.profile = PairingProfile(root/str(i))
                app.pair_lock = threading.Lock()
                app.messages = queue.SimpleQueue()
                app.stop = threading.Event()
                saved = app.profile.peer()
                with patch("wastelands_alt.Alt.loop"), \
                     patch("wastelands.connect_by_pin",side_effect=lambda h,p:connect_by_pin(h,p,server.server_port)) as pair, \
                     patch("wastelands.AltConnection",side_effect=lambda h,n,k:AltConnection(h,n,k,server.server_port)):
                    app.worker_loop("localhost",saved.get("player"),saved.get("key"),pin,slots)
                    self.assertEqual(pair.call_count,int(pin is not None))
                self.assertEqual(app.profile.read("resume.json"),dict(role="alt",peer_address="localhost",slots=slots))
                self.assertEqual(app.profile.peer()["player"],i)
                self.assertNotIn("key",app.profile.read("resume.json"))
            try:
                for i in PLAYERS:
                    worker(i,host.issue_pin(i))
                self.assertEqual(set(host.clients),set(PLAYERS))
            finally:
                server.shutdown()
                server.server_close()
            restarted = Match()
            restarted.keys = PairingProfile(root/"host").host_keys(restarted.keys)
            self.assertEqual(restarted.keys,host.keys)
            server = serve(restarted,("127.0.0.1",0))
            try:
                for i in PLAYERS:
                    worker(i)
                self.assertEqual(set(restarted.clients),set(PLAYERS))
                self.assertEqual(restarted.pins,{})
                with self.assertRaises(PairingExpired):
                    AltConnection("127.0.0.1",1,restarted.keys[2],server.server_port).exchange()
            finally:
                server.shutdown()
                server.server_close()


class SpaceTest(unittest.TestCase):
    def setUp(self):
        self.match = Match()
        self.match.start("nightmare","Host",allow_sales=True)
        for i in PLAYERS:
            self.exchange(i)
        # An eligible titan site with a single confirmed TV at its edge.
        self.point = position(3,"screen")
        self.tower = self.match.places[1,"tv_2"]
        self.tower.update(state="placed",point=[self.point[0]-37,self.point[1]],
                          slot=4,count_before=1,total_before=5)
        self.titan = self.match.places[3,"screen"]

    def exchange(self,player,op="poll",**args):
        return self.match.exchange(player,dict(instance=str(player),run=self.match.run,op=op,can_clear_space=True,**args))

    def request(self):
        self.exchange(3,"need_space",unit="screen",point=self.point)
        return self.exchange(1)["sale"]

    def test_owner_sells_once_and_freed_site_is_reserved_for_requester(self):
        sale = self.request()
        self.assertEqual((sale["owner"],sale["unit"],sale["requester"]),(1,"tv_2",3))
        self.assertEqual(self.titan["clear_site"],self.point)
        self.assertFalse(self.exchange(2,"arm_sale",id=sale["id"],count=2)["send_sale"])
        self.assertTrue(self.exchange(1,"arm_sale",id=sale["id"],count=2)["send_sale"])
        self.assertFalse(self.exchange(1,"arm_sale",id=sale["id"],count=2)["send_sale"])
        with self.assertRaises(ValueError):
            self.match.reserve(1,"plunger",position(1,"plunger"),0,6,3)
        self.exchange(1,"sale_count",id=sale["id"],count=None)
        self.exchange(1,"sale_count",id=sale["id"],count=2)
        self.assertEqual(self.tower["state"],"placed")
        self.exchange(1,"sale_count",id=sale["id"],count=1)
        self.exchange(1,"sale_count",id=sale["id"],count=1)
        self.assertEqual(self.tower["state"],"sold")
        self.assertTrue(self.titan["sale_used"])
        self.assertIsNotNone(placement_conflict(2,"amplifier",self.point,self.match.places.values()))
        self.exchange(3,"reserve",unit="screen",point=self.point,slot=2,count_before=0,total_before=9)
        self.exchange(3,"commit",unit="screen",point=self.point)
        self.assertEqual(self.titan["state"],"placed")
        self.assertNotIn("clear_site",self.titan)
        self.assertIsNone(self.request())

    def test_no_sale_for_disabled_policy_multiple_blockers_or_unbuilt_plan(self):
        self.match.allow_sales = False
        self.assertIsNone(self.request())
        self.match.allow_sales = True
        self.tower.update(state="reserved")
        self.assertIsNone(self.request())
        self.assertIsNone(placement_conflict(3,"screen",self.point,self.match.places.values()))
        self.tower["state"]="placed"
        self.match.places[2,"plunger"].update(state="placed",point=self.point)
        self.assertIsNone(self.request())
        self.match.places[2,"plunger"]["state"]="reserved"
        self.match.places[2,"amplifier"].update(state="placed",point=self.point)
        self.assertIsNone(self.request())

    def test_stale_request_and_expired_sale_cannot_click_again(self):
        sale = self.request()
        self.match.sales[1]["until"]=0
        self.assertFalse(self.exchange(1,"arm_sale",id=sale["id"],count=1)["send_sale"])
        self.assertNotIn("clear_site",self.titan)
        self.match.sale_retry.clear()
        sale = self.request()
        self.assertTrue(self.exchange(1,"arm_sale",id=sale["id"],count=2)["send_sale"])
        self.match.sales[1]["armed"] -= 10
        self.exchange(1,"sale_count",id=sale["id"],count=2)
        self.assertEqual(self.tower["state"],"placed")
        self.assertIsNone(self.request())

    def test_two_rejected_titan_clicks_leave_nearby_sites_on_third_bank(self):
        rejected = [("titan",(1266,861)),("titan",(1315,897))]
        for unit in ("amplifier","screen"):
            sites = {tuple(position(3,unit,i)) for i in range(placement_attempts(unit))}
            self.assertTrue(all(min(math.dist(p,q) for _,q in rejected)<50 for p in sites))
            self.assertGreaterEqual(sum(not near_rejection(unit,p,rejected) for p in sites),80)

    def test_placement_requests_only_a_verified_blocker_on_visible_sand(self):
        a = Alt.__new__(Alt)
        a.player = 3
        a.game = Mock()
        a.configured_slots = dict(zip(UNITS,(3,4,1,2)))
        a.exchange = lambda op="poll",**kw:self.exchange(3,op,**kw)
        a.reset(a.exchange())
        a.map_pose = Mock(return_value=(np.array([.30,.27]),np.diag([1/2048,1/1152])))
        a.placement_sites = Mock(return_value=[self.point])
        from wastelands_alt import UnitCounts
        a.placement_baseline = Mock(return_value=UnitCounts(0,9))
        a.reframe_sites = Mock(return_value=False)
        with patch("wastelands_alt.placement_cash",return_value=10000), patch("twd_bot.read_hotbar",return_value=[]):
            for color,requested in (((72,72,70),False),((95,77,46),True)):
                a.game.grab.return_value = Image.new("RGB",(1366,768),color)
                a.place("screen",a.game.grab())
                self.assertEqual(bool(self.exchange(1)["sale"]),requested)
                a.game.click_live.assert_not_called()

    def test_only_the_confirmed_small_base_can_cover_sand(self):
        point = ANCHOR.tolist()
        frame = Image.new("RGB",(1366,768),(95,77,46))
        pose = (np.array([.5,.5]),np.diag(1/np.array(frame.size)))
        draw = ImageDraw.Draw(frame)
        draw.ellipse((673,374,693,394),fill=(48,48,48))
        def ranked(ignore=None):
            return rank_build_sites(frame,pose,[point],27,[0],clear_titan_base=True,occupied_centers=ignore)
        self.assertEqual(ranked(),[])
        self.assertEqual(ranked([point]),[point])
        draw.rectangle((685,361,704,400),fill=(72,72,70))
        self.assertEqual(ranked([point]),[])

    def test_worker_checks_selected_small_tower_and_reads_personal_count(self):
        sale = self.request()
        a = Alt.__new__(Alt)
        a.player = 1
        a.placed = {"tv_2"}
        a.points = {"tv_2":self.tower["point"]}
        a.pending_places = set()
        a.slots = {"tv":4}
        a.sale_checks = {}
        a.game = Mock()
        frame = Image.new("RGB",(1366,768))
        a.game.grab.return_value = frame
        a.game.take.return_value = True
        a.hover_count = Mock(return_value=1)
        a.exchange = lambda op,**kw:self.exchange(1,op,**kw)
        pose = (np.array([.32,.28]),np.diag([1/2048,1/1152]))
        a.map_pose = Mock(return_value=pose)
        def word(s,x,y):
            return s,x,y,.10,.025
        invalid = [word("Owner",.02,.2),word("Titan Screen Man",.04,.3),word("Sell [X]",.05,.72)]
        valid = [word("Owner",.02,.2),word("Scientist Screen Man",.04,.3),word("Sell [X]",.05,.72)]
        with patch("wastelands_alt.tracked_pose",return_value=pose):
            a.placement_text = Mock(side_effect=[[],invalid])
            a.clear_space(sale)
            self.assertEqual(a.game.click_live.call_count,1)
            self.assertEqual(self.tower["state"],"placed")
            self.match.sale_retry.clear()
            sale = self.request()
            a.placement_text = Mock(side_effect=[[],valid,valid])
            def click(point,live,title):
                self.assertEqual(live(frame),point)
            a.game.click_live.side_effect=click
            a.clear_space(sale)
            self.assertEqual(a.game.click_live.call_args.args[2],"Продать TV 2/4")
            self.assertEqual(self.tower["state"],"placed")
            a.sale_checks.clear()
            a.hover_count.return_value=0
            a.clear_space(self.exchange(1)["sale"])
            self.assertEqual(self.tower["state"],"sold")
            self.assertEqual(a.game.click_live.call_count,3)
