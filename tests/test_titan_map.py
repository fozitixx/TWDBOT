import math
from pathlib import Path
import tempfile
import threading
import time
import tkinter as tk
import unittest
from types import SimpleNamespace
from unittest.mock import Mock, patch

import numpy as np
from PIL import Image

from wastelands import App
from wastelands_alt import Alt, UnitCounts
from wastelands_map import TitanMapEditor, decode_map_frame
from wastelands_pairing import PairingProfile
from wastelands_team import (AltConnection, Match, PLAYERS, TITANS, UNITS,
                             PLACEMENT_ORDER, PRIMARY_BANK_COUNT, on_third_titan_bank,
                             nearby_titan_sites, placement_attempts, placement_conflict, position, serve, titan_layout)
from wastelands_view import ANCHOR, invalid_placement, preview, screen_point


def camera(size, angle, focus):
    co, si = math.cos(angle), math.sin(angle)
    axes = .7*np.array([[co, -si], [si, co]])/np.array(size)[:, None]
    return np.array([.5, .46])-axes@(focus-ANCHOR), axes


def packet(frame, pose, player=1):
    return dict(image=preview(frame), pose=[p.tolist() for p in pose], player=player)


POINTS = {f"{p}/{unit}":[980+p*95, 575+i*100] for p in PLAYERS for i,unit in enumerate(TITANS)}


class TitanMapTest(unittest.TestCase):
    def test_invalid_then_nearby_confirm_and_reload(self):
        player, unit = 3, "amplifier"
        key = "3/amplifier"
        host = Match(manual_titans=POINTS)
        host.start("hard", "Host")
        anchor = POINTS[key]
        conn = Mock(player=player)
        conn.exchange.side_effect = lambda op, **data: host.exchange(player,dict(instance="three",op=op,**data))
        with patch("wastelands_alt.Game"):
            alt = Alt(conn,dict(zip(UNITS,(3,4,1,2))),threading.Event(),Mock())
        alt.reset(alt.exchange())
        alt.update_places(alt.exchange())
        frame = Image.new("RGB",(1024,576),(140,108,65))
        toast = frame.copy()
        with Image.open(Path(__file__).resolve().parents[1]/"wastelands_invalid.png") as mask:
            toast.paste((192,24,22),(416,84,416+mask.width,84+mask.height),mask)
        self.assertTrue(invalid_placement(toast))
        self.assertFalse(invalid_placement(frame))
        pose = camera(frame.size,.61,np.array(anchor))
        alt.game.grab.return_value = frame
        alt.game.click_live.side_effect = lambda point,locate,title: self.assertEqual(locate(frame),point)
        with patch.object(alt,"map_pose",return_value=pose), patch("wastelands_alt.placement_cash",return_value=None), \
             patch.object(alt,"placement_baseline",return_value=UnitCounts(0,8)):
            alt.place(unit,frame)
            row = host.places[player,unit]
            self.assertEqual(row["target"], anchor)
            with patch.object(alt,"placement_readback",side_effect=AssertionError("explicit game rejection")):
                alt.recheck_pending(alt.exchange(),toast)
            self.assertTrue(row["retry_nearby"])
            self.assertEqual(host.manual_titans,POINTS)
            alt.update_places(alt.exchange())
            gray = Image.new("RGB",frame.size,(95,96,94))
            self.assertFalse(alt.candidate_sites(unit,gray,pose,nearby_titan_sites(anchor))[0])
            # The first warning can still be visible when the next click lands.
            alt.game.click_live.side_effect = lambda point,locate,title: self.assertEqual(locate(toast),point)
            alt.place(unit,frame)
            target = list(row["target"])
            self.assertIn(target,nearby_titan_sites(anchor))
            self.assertGreater(math.dist(target,anchor),18)
            self.assertLessEqual(math.dist(target,anchor),50.01)
            self.assertEqual(host.manual_titans,POINTS)
            with patch.object(alt,"placement_readback",return_value=UnitCounts(1,9)):
                alt.recheck_pending(alt.exchange(),toast)
        expected = POINTS | {key:target}
        self.assertEqual(host.manual_titans,expected)
        with tempfile.TemporaryDirectory() as tmp:
            app = App.__new__(App)
            app.match, app.saved_layout = host, dict(POINTS)
            app.profile, app.titan_frame = PairingProfile(tmp), packet(frame,pose,player)
            app.save_learned_layout()
            saved = app.profile.read("titan-map.json")
            self.assertEqual(saved["frame"], app.titan_frame)
            restored = Match(manual_titans=saved["points"])
            restored.start("hard","Host")
            self.assertEqual(restored.places[player,unit]["point"],target)

    def test_nearby_requires_failure_and_preserves_concurrent_edit(self):
        m = Match(manual_titans=POINTS)
        m.start("hard","Host")
        key, unit = "3/screen","screen"
        anchor = POINTS[key]
        candidate = nearby_titan_sites(anchor)[0]
        with self.assertRaisesRegex(ValueError,"изменилась"):
            m.reserve(3,unit,candidate,0,8,2)
        m.reserve(3,unit,anchor,0,8,2)
        row = m.places[3,unit]
        m.exchange(3,dict(instance="three",run=m.run,op="release",unit=unit,point=anchor,
                          target_since=row["target_since"],site_failed=True))
        m.reserve(3,unit,candidate,0,8,2)
        edited = POINTS | {key:[1350,830]}
        m.set_titan_layout(edited)
        m.exchange(3,dict(instance="three",run=m.run,op="commit",unit=unit,point=candidate))
        self.assertEqual(row["point"],candidate)
        self.assertEqual(m.manual_titans,edited)

    def test_editor_keeps_unsaved_edits_and_updates_untouched_markers(self):
        m = Match(manual_titans=POINTS)
        editor = TitanMapEditor.__new__(TitanMapEditor)
        editor.app = SimpleNamespace(match=m)
        editor.baseline = dict(POINTS)
        editor.draft = dict(POINTS)
        editor.draft.pop("1/screen")
        m.set_titan_layout(POINTS | {"3/screen":[1350,830]})
        editor.merge_learned_points()
        self.assertNotIn("1/screen",editor.draft)
        self.assertEqual(editor.draft["3/screen"],[1350,830])

    def test_editor_marks_all_six_on_one_letterboxed_frame_and_reopens_offline(self):
        root = tk.Tk()
        root.withdraw()
        self.addCleanup(root.destroy)
        frame = Image.new("RGB", (1366, 768))
        pose = camera(frame.size, -.48, np.array([1100, 650]))
        with tempfile.TemporaryDirectory() as tmp:
            app = SimpleNamespace(root=root, match=Match(), profile=PairingProfile(tmp),
                                  titan_frame=packet(frame, pose, 2))
            editor = TitanMapEditor(app)
            editor.win.withdraw()
            bounds = (46, 72, 769, 432)
            for key, point in POINTS.items():
                editor.bounds = bounds
                editor.selected.set(key)
                x, y = screen_point(pose, point)
                editor.pick(SimpleNamespace(x=round(bounds[0]+x*bounds[2]), y=round(bounds[1]+y*bounds[3])))
                self.assertLess(math.dist(editor.draft[key], point), 2.2)
            self.assertEqual(app.match.manual_titans, {})
            editor.save()
            saved = app.profile.read("titan-map.json")
            self.assertEqual(app.match.manual_titans, saved["points"])
            image, restored = decode_map_frame(saved["frame"])
            self.assertEqual(image.width, 960)
            np.testing.assert_allclose(restored[1], pose[1])
            editor.win.destroy()
            with patch("wastelands.team_profile_dir", return_value=tmp):
                reopened = App(tk.Frame(root))
                try:
                    reopened.open_titan_map()
                    again = reopened.map_editor
                    again.win.withdraw()
                    self.assertEqual(again.draft, saved["points"])
                    self.assertIsNotNone(again.image)
                    again.selected.set("3/screen")
                    again.clear()
                    again.save()
                    self.assertEqual(set(reopened.match.manual_titans), set(POINTS)-{"3/screen"})
                finally:
                    reopened.close()

    def test_invalid_calibration_overlaps_and_outside_marks(self):
        frame = Image.new("RGB", (900, 300))
        with self.assertRaises(ValueError):
            decode_map_frame(packet(frame, (np.zeros(2), np.zeros((2, 2)))))
        for value in ([float("nan"), 200], [2049, 400], [1]):
            with self.assertRaises(ValueError):
                titan_layout({"1/screen":value})
        with self.assertRaisesRegex(ValueError,"слишком близко"):
            titan_layout({"1/amplifier":[1010,600], "3/screen":[1011,606]})

    def test_frame_before_first_unit_and_exact_points_across_three_camera_poses(self):
        match = Match()
        match.start("nightmare", "Host")
        server = serve(match, ("127.0.0.1", 0))
        self.addCleanup(server.server_close)
        self.addCleanup(server.shutdown)
        workers = []
        for i in PLAYERS:
            conn = AltConnection("127.0.0.1", i, match.keys[i], server.server_port)
            with patch("wastelands_alt.Game"):
                alt = Alt(conn, dict(zip(UNITS, (3,4,1,2))), threading.Event(), Mock())
            alt.reset(alt.exchange())
            alt.phase, alt.ready, alt.next_slot_check = "battle", True, float("inf")
            workers.append(alt)
        request = match.command(2, "map_snapshot")
        frame = Image.new("RGB", (1366, 768), (95,76,50))
        pose = camera(frame.size, .3, np.array([1130,630]))
        source = workers[1]
        source.game.grab.return_value = frame
        with patch.object(source, "map_pose", return_value=pose):
            self.assertIn("готов", source.tick(source.exchange()))
        self.assertEqual(match.map_frame[0],request)
        image, _ = decode_map_frame(match.map_frame[1])
        self.assertLessEqual(image.width, 960)
        self.assertFalse(match.frames)
        source.game.click_live.assert_not_called()
        match.set_titan_layout(POINTS)
        self.assertFalse(on_third_titan_bank(POINTS["3/screen"]))
        for alt, angle, size in zip(workers, (0,1.4,math.pi), ((1920,1080),(1366,768),(1280,720))):
            # Grey terrain previously rejected by the third worker's sand search.
            frame = Image.new("RGB", size, (84,79,75))
            pose = camera(size, angle, np.array([1090+alt.player*28,650]))
            alt.game.grab.return_value = frame
            for unit in TITANS:
                point = POINTS[f"{alt.player}/{unit}"]
                alt.update_places(alt.exchange())
                with patch.object(alt, "map_pose", return_value=pose), \
                     patch("wastelands_alt.placement_cash", return_value=30000), \
                     patch.object(alt, "placement_baseline", return_value=UnitCounts(0, 8)), \
                     patch.object(alt, "hover_count", return_value=1):
                    alt.place(unit,frame)
                    click, locate, _ = alt.game.click_live.call_args.args
                    np.testing.assert_allclose(click, screen_point(pose,point))
                    self.assertEqual(locate(frame),click)
                    with patch.object(alt,"map_pose",return_value=None):
                        self.assertIsNone(locate(frame))
                    self.assertIn("Поставил",alt.recheck_pending(alt.exchange()))
                self.assertEqual(match.places[alt.player,unit]["point"],point)
        self.assertEqual(match.titan_sites, {})

    def test_edits_respect_live_reservations_and_invalidate_old_plans(self):
        m = Match(manual_titans=POINTS)
        m.start("hard", "Host")
        original = POINTS["3/screen"]
        updated = dict(POINTS, **{"3/screen":[1265,795]})
        self.assertEqual(placement_conflict(1,"tv",original,m.places.values()),"Рядом занят участок")
        m.reserve(3,"screen",original,0,8,2)
        m.set_titan_layout(updated)
        row = m.places[3,"screen"]
        self.assertEqual(row["target"],original)
        m.exchange(3,dict(instance="three",run=m.run,op="release",unit="screen",point=original))
        self.assertEqual(row["point"],updated["3/screen"])
        with self.assertRaisesRegex(ValueError,"изменилась"):
            m.reserve(3,"screen",original,0,8,2)
        new = updated["3/screen"]
        m.reserve(3,"screen",new,0,8,2)
        m.exchange(3,dict(instance="three",run=m.run,op="commit",unit="screen",point=new))
        m.set_titan_layout({})
        self.assertEqual(row["point"],new)
        m.start("hard","Host")
        self.assertEqual(m.places[3,"screen"]["point"],position(3,"screen"))

    def test_moving_a_marker_cancels_an_unarmed_sale_at_the_old_location(self):
        point = position(3,"screen")
        m = Match(manual_titans={"3/screen":point})
        m.start("nightmare","Host",allow_sales=True)
        for player in PLAYERS:
            m.exchange(player,dict(instance=str(player),run=m.run,can_clear_space=True))
        tower = m.places[1,"tv_2"]
        tower.update(state="placed",point=[point[0]-37,point[1]],slot=4,count_before=1,total_before=5)
        m.request_space(3,"screen",point,time.monotonic())
        old = m.sales[1]["id"]
        m.set_titan_layout({"3/screen":[1100,800]})
        self.assertFalse(m.sale_action(1,"arm_sale",dict(id=old,count=2),time.monotonic()))
        self.assertEqual(tower["state"],"placed")
        self.assertEqual(m.places[3,"screen"]["point"],[1100,800])


class SmallPlacementTest(unittest.TestCase):
    def test_early_readbacks_use_confirmed_inventory_across_waits(self):
        a = Alt.__new__(Alt)
        a.host_totals = True
        a.placed = set(PLACEMENT_ORDER[:6])
        a.last_inventory = ("tv", time.monotonic()-30, UnitCounts(2,6))
        a.manager_until = {"tv":time.monotonic()+10}
        a.hover_count = Mock(return_value=2)
        a.manager_counts = Mock()
        before = a.placement_baseline("tv",4,4)
        self.assertEqual(before,UnitCounts(2,6))
        a.hover_count.return_value = 3
        self.assertEqual(a.placement_readback("tv",4,before,False),UnitCounts(3))
        a.manager_counts.assert_not_called()
        a.hover_count.return_value = 2
        a.manager_counts.return_value = UnitCounts(None,7)
        self.assertEqual(before.delta(a.placement_readback("tv",4,before,True)),1)
        a.manager_counts.assert_called_once()

    def test_extra_bank_checked_before_turning_and_last_tvs_yield_to_a_titan(self):
        m = Match()
        m.start("nightmare","Host")
        for unit in PLACEMENT_ORDER[:6]:
            m.places[3,unit]["state"] = "placed"
        a = Alt.__new__(Alt)
        a.player, a.game, a.guard = 3, Mock(), Mock()
        state = m.exchange(3,dict(instance="three",run=m.run))
        a.reset(state)
        a.phase, a.ready, a.next_slot_check = "battle", True, float("inf")
        frame = Image.new("RGB", (1366,768))
        a.game.grab.return_value = frame
        empty = ([],66,63,3,0)
        overflow = position(3,"tv_4",PRIMARY_BANK_COUNT)
        sites = list(range(placement_attempts("tv_4")))
        with patch.object(a,"rank_sites",side_effect=[empty,([overflow],1,0,0,0)]) as rank:
            self.assertEqual(a.candidate_sites("tv_4",frame,None,sites),([overflow],67,63,3,0))
            self.assertEqual(rank.call_args_list[1].args[-1], sites[PRIMARY_BANK_COUNT:])
        actions = []
        def place(unit, img):
            actions.append(unit)
            if unit.startswith("tv"):
                a.blocked_tv.add(unit)
                a.rescan_at[unit] = time.monotonic()-1
            return unit
        with patch.object(a,"place",side_effect=place):
            for _ in range(4):
                a.tick(state)
        self.assertEqual(actions,["tv_3","tv_4","amplifier","tv_3"])
