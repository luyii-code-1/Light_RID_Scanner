import unittest
from pathlib import Path

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


class NativeCaptureIntegrationTests(unittest.TestCase):
    def test_home_page_does_not_hide_rid_using_stale_browser_flag(self):
        source = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")
        function = source.split("function includeDroneByFirmware(e){", 1)[1].split("}", 1)[0]

        self.assertIn("return !!e;", function)
        self.assertNotIn("newFirmwareParseEnabled", function)

    def test_exact_rid_ssid_can_create_row_before_coordinates_arrive(self):
        namespace = load_namespace(create_runtime_context())

        self.assertTrue(
            namespace["_rid_realtime_candidate_valid"](
                False,
                sn="1581FANLC258U029RTN6",
                ssid="RID-1581FANLC258U029RTN6",
            )
        )
        self.assertFalse(
            namespace["_rid_realtime_candidate_valid"](
                False,
                sn="NOT-A-REAL-RID",
                ssid="RID-NOT-A-REAL-RID",
            )
        )

    def test_native_record_reuses_python_parser_and_state_update(self):
        namespace = load_namespace(create_runtime_context())
        updates = []
        namespace["state_update"] = lambda *args, **kwargs: updates.append((args, kwargs))
        payload = (
            "fa0bbc0d24ff2048fffffe3135383146414e4c433235385530323952544e36"
            "30303030303030000101d1823b483bf2eb11ed0769833b4822f0eb1105001c"
            "00284700c2083d0902000c050478acc5529e0103"
        )
        line = f"RIDCAP1\t8\t8c:1e:d9:03:09:b2\t-42\t6\t\t{payload}"

        namespace["_parse_native_capture_line"](line)

        self.assertGreaterEqual(len(updates), 1)
        for args, kwargs in updates:
            self.assertEqual(args[0], "8c:1e:d9:03:09:b2")
            self.assertEqual(kwargs["rssi"], -42)
            self.assertEqual(kwargs["ch"], 6)
        self.assertTrue(any(kwargs["firmware_type"] == "new" for _args, kwargs in updates))


if __name__ == "__main__":
    unittest.main()
