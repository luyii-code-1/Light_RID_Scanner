import unittest

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


def notification_namespace():
    return load_namespace(
        create_runtime_context(
            chunk_files=("common_core.py", "hardware_core.py"),
            module_name="station_edition.light_rid._test_wecom_notification",
        )
    )


class WeComNotificationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ns = notification_namespace()

    def test_visual_draft_can_send_without_saving_or_master_enable(self):
        original_config = self.ns["json"].loads(self.ns["json"].dumps(self.ns["APP_CONFIG"]))
        sent = []
        self.ns["APP_CONFIG"]["notify"] = {
            "enabled": False,
            "send_timeout_sec": 5,
            "wecom_webhooks": [{"name": "saved", "enabled": True, "key": "saved-key"}],
        }
        self.ns["_wecom_send_text"] = lambda key, content, timeout_sec=8: (
            sent.append((key, content, timeout_sec)) or (True, "ok")
        )
        try:
            ok, message = self.ns["send_test_notification_from_visual_payload"]({
                "notify": {
                    "enabled": False,
                    "send_timeout_sec": 7,
                    "wecom_webhooks": [{
                        "index": 0,
                        "name": "当前草稿",
                        "enabled": True,
                        "key": "__KEEP__",
                    }],
                },
            })
            self.assertTrue(ok, message)
            self.assertEqual(1, len(sent))
            self.assertEqual("saved-key", sent[0][0])
            self.assertEqual(7, sent[0][2])
            self.assertFalse(self.ns["APP_CONFIG"]["notify"]["enabled"])
            self.assertEqual("saved", self.ns["APP_CONFIG"]["notify"]["wecom_webhooks"][0]["name"])
        finally:
            self.ns["APP_CONFIG"].clear()
            self.ns["APP_CONFIG"].update(original_config)

    def test_visual_draft_rejects_missing_channel_key(self):
        ok, message = self.ns["send_test_notification_from_visual_payload"]({
            "notify": {
                "enabled": False,
                "wecom_webhooks": [{"index": None, "name": "new", "enabled": True, "key": ""}],
            },
        })
        self.assertFalse(ok)
        self.assertIn("missing wecom webhook", message)


if __name__ == "__main__":
    unittest.main()
