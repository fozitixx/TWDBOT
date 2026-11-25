import unittest
from unittest.mock import Mock, patch

import twd_bot as farm
from wastelands import App
from wastelands_team import Match


class DiscordFeedbackTest(unittest.TestCase):
    def setUp(self):
        settings = dict(discord_token="test", discord_channel="100", discord_worker_1="101",
                        discord_worker_2="102", discord_worker_3="")
        with patch.dict(farm.SETTINGS, settings):
            self.link = farm.DiscordLink(None)
        self.panel = App.__new__(App)
        self.panel.match = Match()
        self.panel.discord_state = {}
        active = patch.object(farm, "LINK", self.link)
        active.start()
        self.addCleanup(active.stop)

    def test_destinations_include_existing_farm_and_afk_messages(self):
        link = self.link
        link.ok = True
        link.send("farm")
        link.send("one", player=1)
        link.afk_prompt("test", None)
        link.send("two", player=2)
        link.send("muted", player=3)
        paths = []
        def post(path, payload, image):
            paths.append(path)
            if not link.queue:
                link.stop()
        link._post = post
        link._sender()
        self.assertEqual(paths, [f"/channels/{i}/messages" for i in (100, 101, 100, 102)])

    def test_worker_only_never_opens_gateway_or_sends_farm_actions(self):
        link = self.link
        link.channel = ""
        link._request = Mock(return_value={"id": "bot"})
        link._gateway_loop = Mock()
        link._run()
        link._gateway_loop.assert_not_called()
        link.send("farm")
        link.afk_prompt("test", None)
        link.send("two", player=2)
        self.assertEqual([channel for channel, _, _ in link.queue], ["102"])

    def test_confirmed_events_and_reconnect(self):
        panel = self.panel
        match = panel.match
        match.start("nightmare", "host")
        match.exchange(2, dict(instance="two", run=match.run))
        match.progress[2]["ready"] = True
        match.places[2, "screen"]["state"] = "placed"
        match.places[1, "amplifier"]["state"] = "placed"
        activity = "Титаны 2/2 · Screen ур. 2/8"
        panel.report_player(2, True, activity)
        panel.report_player(2, True, activity)
        panel.report_player(3, False, "")
        panel.report_player(2, False, "")
        panel.report_player(2, True, activity)
        match.stop()
        panel.report_player(2, True, "")
        descriptions = [p["embeds"][0]["description"] for _, p, _ in self.link.queue]
        self.assertEqual(len(descriptions), 4)
        self.assertIn("Поставлен Screen", descriptions[0])
        self.assertIn("READY нажат", descriptions[0])
        self.assertIn("уровень 2/8", descriptions[0])
        self.assertNotIn("Amplifier", descriptions[0])
        self.assertEqual(descriptions[1:], ["Связь потеряна", "На связи", "Помощник остановлен"])
        self.assertTrue(all(ch == "102" for ch, _, _ in self.link.queue))

    def test_placement_warning_is_sent_once_per_match(self):
        panel = self.panel
        activity = "Amplifier · игра отклонила постановку. Можно передвинуть метку."
        for _ in range(2):
            panel.match.start("hard", "host")
            panel.match.exchange(1, dict(instance="one", run=panel.match.run))
            for status in (activity, "Проверяю", activity):
                panel.report_player(1, True, status)
        messages = [p["embeds"][0]["description"] for _, p, _ in self.link.queue]
        self.assertEqual(len(messages), 2)
        self.assertTrue(all("проверь метку" in m for m in messages))
