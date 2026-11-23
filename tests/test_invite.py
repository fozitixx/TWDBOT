import unittest
from pathlib import Path
from unittest.mock import Mock

from PIL import Image, ImageDraw

from wastelands_view import read_invite


class InviteTest(unittest.TestCase):
    def test_compact_invite_when_map_ocr_is_empty(self):
        frame = Image.new("RGB", (1366, 768))
        with Image.open(Path(__file__).parent / "fixtures/wasteland_invite_buttons.png") as card:
            frame.paste(card, (1163, 229))
        sender = [("Host", .9, .28, .02, .02)]
        read = Mock(side_effect=[sender])
        button, _ = read_invite(frame, "Host", read)
        self.assertIsNotNone(button)
        self.assertLess(abs(button[0]*1366 - 1288), 2)
        self.assertLess(abs(button[1]*768 - 261), 2)
        read.assert_called_once()
        self.assertIsNone(read_invite(frame, "Other", Mock(return_value=sender))[0])

        draw = ImageDraw.Draw(frame)
        draw.rectangle((1223, 230, 1272, 242), fill="black")
        draw.text((1223, 230), "Other City", fill="skyblue")
        self.assertIsNone(read_invite(frame, "Host", Mock(side_effect=[sender, []]))[0])
        words = [("Wastelands", .92, .30, .05, .01)]
        self.assertEqual(read_invite(frame, "Host", Mock(side_effect=[sender, words]))[0], button)
