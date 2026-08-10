import unittest
import os
import tempfile
from unittest import mock
from pathlib import Path

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


class NativeCaptureIntegrationTests(unittest.TestCase):
    def test_home_page_does_not_hide_rid_using_stale_browser_flag(self):
        source = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")
        function = source.split("function includeDroneByFirmware(e){", 1)[1].split("}", 1)[0]

        self.assertIn("return !!e;", function)
        self.assertNotIn("newFirmwareParseEnabled", function)

    def test_parsed_rid_is_not_filtered_for_missing_coordinates(self):
        source = Path("station_edition/light_rid/cli_app.py").read_text(encoding="utf-8")
        process_source = Path("station_edition/light_rid/process_core.py").read_text(encoding="utf-8")

        self.assertNotIn("not _rid_parser_has_coord(decoded)", source)
        self.assertIn("rid_verified=True", source)
        self.assertIn('if scan_type_key != "phone" and not _rid_target_sn_valid(sn):', process_source)

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

    def test_router_capture_stream_does_not_spawn_a_child(self):
        namespace = load_namespace(create_runtime_context())
        updates = []
        namespace["_parse_native_capture_line"] = updates.append
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False) as stream:
            stream.write("RIDCAP1\t8\taa:bb:cc:dd:ee:ff\t-42\t6\t\t00\n")
            stream_path = stream.name
        try:
            with mock.patch.dict(os.environ, {"LIGHT_RID_CAPTURE_STREAM": stream_path}):
                with mock.patch("subprocess.Popen") as popen:
                    with self.assertRaisesRegex(RuntimeError, "capture stream closed"):
                        namespace["_sniff_run_native"]("ridmon", 20.0)
            popen.assert_not_called()
            self.assertEqual(1, len(updates))
        finally:
            os.unlink(stream_path)

    def test_router_launcher_uses_one_persistent_capture_stream(self):
        source = Path("openwrt/light-rid-run").read_text(encoding="utf-8")

        self.assertIn('mkfifo "$CAPTURE_FIFO"', source)
        self.assertIn('--timeout-ms 0 >"$CAPTURE_FIFO"', source)
        self.assertIn('LIGHT_RID_CAPTURE_STREAM="$CAPTURE_FIFO"', source)


if __name__ == "__main__":
    unittest.main()
