import math
import unittest

import numpy as np
from PIL import Image, ImageDraw

from wastelands_team import (BANK_OFFSET, EDGE_GAP, MAIN_EARLY, Match, bank_slot,
                             on_third_titan_bank, placement_attempts, position)
from wastelands_view import ANCHOR, framing_turn, perimeter_point, rank_build_sites, screen_point


class PerimeterTest(unittest.TestCase):
    def test_third_titan_bank_matches_the_marked_sand_and_discards_old_sites(self):
        old_amp,old_screen = [1590,906],[1570,826]
        match = Match({"3/amplifier":old_amp,"3/screen":old_screen,"2/screen":position(2,"screen")})
        self.assertEqual(match.titan_sites,{"2/screen":position(2,"screen")})
        match.start("nightmare","Host")
        # Landmark fit and the interior of the marked sand on the 2047x1150 report.
        pose = (np.array([.30194518,.50504288]),np.array([[.00042021,.00023935],[-.00058122,.00080800]]))
        for kind,legacy in (("amplifier",old_amp),("screen",old_screen)):
            plan = match.exchange(3,{"instance":"test","op":"placement_sites","run":match.run,"unit":kind})
            self.assertIsNone(plan["preferred_site"])
            for p in plan["sites"]:
                x,y = np.array(screen_point(pose,p))*[2047,1150]
                self.assertTrue(1125<x<1290 and 615<y<695)
                self.assertTrue(on_third_titan_bank(p))
            self.assertFalse(on_third_titan_bank(legacy))
            with self.assertRaisesRegex(ValueError,"За пределами"):
                match.reserve(3,kind,legacy)

    def test_third_titans_can_swap_planned_spots_and_respect_confirmed_bases(self):
        match = Match()
        match.start("nightmare","Host")
        alternatives = [position(3,"amplifier",n) for n in range(placement_attempts("amplifier"))]
        screen_sites = {tuple(position(3,"screen",n)) for n in range(placement_attempts("screen"))}
        shared = [p for p in alternatives if tuple(p) in screen_sites]
        # Debris covers the normal Amplifier position. Its sibling's end of
        # the strip is available until there is a real reservation there.
        right = min(shared,key=lambda p:math.dist(p,position(3,"screen")))
        left = min(shared,key=lambda p:math.dist(p,position(3,"amplifier")))
        match.reserve(3,"amplifier",right,0,8,1)
        with self.assertRaises(ValueError):
            match.reserve(3,"screen",right,0,8,2)
        match.exchange(3,{"instance":"test","run":match.run,"op":"commit","unit":"amplifier","point":right})
        with self.assertRaisesRegex(ValueError,"занят"):
            match.reserve(3,"screen",right,0,9,2)
        match.reserve(3,"screen",left,0,9,2)
        self.assertGreaterEqual(math.dist(left,right),54)

    def test_clear_center_with_rubble_on_one_side_of_the_base(self):
        frame = Image.new("RGB",(1366,768),(95,77,46))
        pose = (np.array([.5,.5]),np.diag(1/np.array(frame.size)))
        sites = [ANCHOR.tolist()]
        self.assertEqual(rank_build_sites(frame,pose,sites,27,[-.42],clear_titan_base=True),sites)
        ImageDraw.Draw(frame).rectangle((696,387,708,406),fill=(87,75,58))
        self.assertEqual(frame.getpixel((683,384)),(95,77,46))
        self.assertEqual(rank_build_sites(frame,pose,sites,27,[-.42],clear_titan_base=True),[])

    def test_reframe_when_only_part_of_the_titan_base_is_behind_the_hotbar(self):
        size = (1366,768)
        pose = (np.array([.744,.86]),np.diag(1/np.array(size)))
        sites = [ANCHOR.tolist()]
        self.assertEqual(framing_turn(pose,sites,size),0)
        self.assertNotEqual(framing_turn(pose,sites,size,radius=27),0)

    def test_snap_follows_visible_edge_for_rotated_cameras(self):
        for angle in (0, .6, math.pi):
            co, si = math.cos(angle), math.sin(angle)
            mat = np.array([[co,-si],[si,co]]) * .7
            frame = Image.new("RGB", (1366,768))
            center, tangent, normal = map(np.array, bank_slot(2,"plunger"))
            size = np.array(frame.size)
            pose = np.array([.5,.5]) - (mat@(center-ANCHOR))/size, mat/size[:,None]
            def point(t,n):
                return tuple(size/2 + mat@(t*tangent+n*normal))
            # The visible edge is 11 map pixels farther out than the nominal edge.
            ImageDraw.Draw(frame).polygon([point(t,n) for t,n in
                ((-80,-20),(80,-20),(80,35),(-80,35))], fill=(168,48,39))
            result = perimeter_point(frame,pose,center,tangent,normal)
            self.assertIsNotNone(result)
            self.assertAlmostEqual((result-center)@normal,35+EDGE_GAP,delta=3)
            self.assertAlmostEqual((result-center)@tangent,0,places=6)
            self.assertIsNone(perimeter_point(Image.new("RGB",frame.size),pose,center,tangent,normal))

    def test_reserve_measured_positions_and_protect_neighbors(self):
        match=Match()
        match.start("nightmare","Host")
        for kind in ("plunger","tv"):
            for copy in ("","_2","_3","_4"):
                for player in (1,2,3):
                    unit=kind+copy
                    center, tangent, normal=map(np.array,bank_slot(player,unit))
                    point=(center+(BANK_OFFSET+2)*normal).tolist()
                    self.assertTrue(all(math.dist(point,p)>=30 for p in MAIN_EARLY))
                    match.reserve(player,unit,point)
        wrong = np.asarray(position(1,"plunger"))-80*np.array(bank_slot(1,"plunger")[2])
        match.places[1,"plunger"].pop("target")
        with self.assertRaisesRegex(ValueError,"За пределами"):
            match.reserve(1,"plunger",wrong.tolist())
