import math
import unittest

import numpy as np
from PIL import Image, ImageDraw

from wastelands_team import BANK_OFFSET, EDGE_GAP, MAIN_EARLY, Match, bank_slot, position
from wastelands_view import ANCHOR, perimeter_point


class PerimeterTest(unittest.TestCase):
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
