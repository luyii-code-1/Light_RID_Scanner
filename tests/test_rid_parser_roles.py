import os
import struct
import tempfile
import unittest
from pathlib import Path

from station_edition.light_rid.analize_core import parse_raw_packet, parse_rid_payload, parse_rid_payloads
from station_edition.light_rid.runtime import create_runtime_context, load_namespace


LEGACY_ODID_RAW = bytes.fromhex(
    "00 00 12 00 2e 48 00 00 00 0c 85 09 c0 00 b4 01 00 00 80 00 00 00 "
    "ff ff ff ff ff ff 8c 1e d9 03 09 b2 8c 1e d9 03 09 b2 00 00 e8 0c "
    "6b 22 00 00 00 00 a0 00 21 04 00 18 52 49 44 2d 31 35 38 31 46 38 "
    "44 42 57 32 35 42 38 30 30 42 33 34 31 37 dd 53 fa 0b bc 0d 06 f1 "
    "19 03 01 12 31 35 38 31 46 38 44 42 57 32 35 42 38 30 30 42 33 34 "
    "31 37 00 00 00 11 20 ac 16 00 a3 d4 ea 11 cb fe 3c 48 e2 08 9e 08 "
    "79 08 2c 04 c6 25 0a 00 41 09 ff ee ea 11 99 b7 3d 48 01 00 00 00 "
    "00 00 00 02 00 08 d7 74 da 0d 00"
)


def parser_namespace():
    return load_namespace(
        create_runtime_context(
            chunk_files=("common_core.py", "scan_core.py"),
            module_name="station_edition.light_rid._test_parser_roles",
        )
    )


def common_namespace():
    return load_namespace(
        create_runtime_context(
            chunk_files=("common_core.py",),
            module_name="station_edition.light_rid._test_common_tracks",
        )
    )


def process_namespace():
    return load_namespace(
        create_runtime_context(
            chunk_files=("common_core.py", "scan_core.py", "process_core.py"),
            module_name="station_edition.light_rid._test_process_tracks",
        )
    )


def startup_namespace(name: str):
    return load_namespace(
        create_runtime_context(
            chunk_files=("common_core.py",),
            module_name=name,
        )
    )


def gb46750_ff2048_sample() -> bytes:
    vendor = bytearray(72)
    vendor[0:4] = bytes.fromhex("fa 0b bc 0d")
    vendor[4] = 0x29
    vendor[5:11] = bytes.fromhex("ff 20 48 ff ff fe")
    vendor[11:31] = b"1581F8DBW25B800B3417"
    vendor[31:39] = b"UASID123"
    vendor[42:46] = struct.pack("<i", int(round(121.1956939 * 1e7)))
    vendor[46:50] = struct.pack("<i", int(round(30.0602531 * 1e7)))
    vendor[52:56] = struct.pack("<i", int(round(121.2004249 * 1e7)))
    vendor[56:60] = struct.pack("<i", int(round(30.0609279 * 1e7)))
    return bytes(vendor)


GB46750_STANDARD_SAMPLE = bytes.fromhex(
    "fa0bbc0d24ff2048fffffe3135383146414e4c433235385530323952544e363030303030303030000101d1823b483bf2eb11ed0769833b4822f0eb1105001c00284700c2083d0902000c050478acc5529e0103"
)


class RidParserRoleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ns = parser_namespace()
        cls.common_ns = common_namespace()
        cls.process_ns = process_namespace()

    def test_legacy_odid_result_roles_are_message_type_based(self):
        result = self.ns["parse_rid_payload"](LEGACY_ODID_RAW, "auto")

        self.assertTrue(result["ok"])
        self.assertEqual(result["format"], "DJI_OLD_ODID")
        self.assertEqual(result["sn"], "1581F8DBW25B800B3417")

        aircraft = result["aircraft_position"]
        self.assertEqual(aircraft["role"], "aircraft")
        self.assertEqual(aircraft["source"], "ODID_LOCATION")
        self.assertAlmostEqual(aircraft["lat"], 30.0602531, places=7)
        self.assertAlmostEqual(aircraft["lon"], 121.1956939, places=7)

        operator = result["operator_positions"][0]
        self.assertEqual(operator["role"], "operator")
        self.assertEqual(operator["source"], "ODID_SYSTEM")
        self.assertAlmostEqual(operator["lat"], 30.0609279, places=7)
        self.assertAlmostEqual(operator["lon"], 121.2004249, places=7)

    def test_legacy_odid_decoded_roles_match_result_roles(self):
        result = self.ns["parse_rid_payload"](LEGACY_ODID_RAW, "dji_old_odid")
        decoded = self.ns["rid_parse_result_to_decoded"](result)

        self.assertEqual(decoded["location"]["lat"], result["aircraft_position"]["lat"])
        self.assertEqual(decoded["location"]["lon"], result["aircraft_position"]["lon"])

        operator = result["operator_positions"][0]
        self.assertEqual(decoded["system"]["pilot_lat"], operator["lat"])
        self.assertEqual(decoded["system"]["pilot_lon"], operator["lon"])
        self.assertEqual(decoded["metadata"]["aircraft_position"], result["aircraft_position"])
        self.assertEqual(decoded["metadata"]["operator_positions"], result["operator_positions"])

    def test_analize_core_exposes_the_same_role_fields(self):
        parsed = parse_raw_packet(LEGACY_ODID_RAW, "dji_old_odid")

        self.assertTrue(parsed["ok"])
        self.assertEqual(parsed["format"], "DJI_OLD_ODID")
        self.assertEqual(parsed["sn"], "1581F8DBW25B800B3417")
        self.assertAlmostEqual(parsed["aircraft_position"]["lat"], 30.0602531, places=7)
        self.assertAlmostEqual(parsed["aircraft_position"]["lon"], 121.1956939, places=7)
        self.assertAlmostEqual(parsed["operator_positions"][0]["lat"], 30.0609279, places=7)
        self.assertAlmostEqual(parsed["operator_positions"][0]["lon"], 121.2004249, places=7)

    def test_gb46750_ff2048_marker_does_not_fall_back_to_legacy_odid(self):
        result = self.ns["parse_rid_payload"](gb46750_ff2048_sample(), "auto")

        self.assertTrue(result["ok"])
        self.assertEqual(result["format"], "GB46750_2025")
        self.assertEqual(result["sub_format"], "GB46750_STANDARD_PACKET")
        self.assertAlmostEqual(result["aircraft_position"]["lat"], 30.0609279, places=7)
        self.assertAlmostEqual(result["operator_positions"][0]["lon"], 121.1956939, places=7)

    def test_frontend_map_uses_role_specific_fields(self):
        source = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")

        self.assertIn("function aircraftMapCoord(e)", source)
        self.assertIn("var airCoord = aircraftMapCoord(e);", source)
        self.assertIn("function primaryOperatorCoord(e)", source)
        self.assertIn("var op = primaryOperatorCoord(e);", source)
        self.assertNotIn("home_lat || e.lat", source)
        self.assertNotIn("aux_lat || e.lat", source)

    def test_gb46750_standard_packet_roles_and_track_samples(self):
        result = parse_rid_payload(GB46750_STANDARD_SAMPLE, "gb46750_2025")

        self.assertTrue(result["ok"])
        self.assertEqual(result["format"], "GB46750_2025")
        self.assertEqual(result["sn"], "1581FANLC258U029RTN6")
        self.assertEqual(result["uas_id"], "00000000")
        self.assertAlmostEqual(result["operator_positions"][0]["lat"], 30.0675643, places=7)
        self.assertAlmostEqual(result["operator_positions"][0]["lon"], 121.1859665, places=7)
        self.assertAlmostEqual(result["aircraft_position"]["lat"], 30.0675106, places=7)
        self.assertAlmostEqual(result["aircraft_position"]["lon"], 121.1859817, places=7)
        self.assertEqual([x["track_type"] for x in result["track_samples"]], ["aircraft", "operator"])
        self.assertEqual(result["decoded"]["location"]["lat"], result["aircraft_position"]["lat"])
        self.assertEqual(result["decoded"]["system"]["pilot_lat"], result["operator_positions"][0]["lat"])

    def test_multi_packet_parser_accumulates_all_samples(self):
        payload = LEGACY_ODID_RAW + GB46750_STANDARD_SAMPLE + GB46750_STANDARD_SAMPLE
        result = parse_rid_payloads(payload, "auto")

        self.assertTrue(result["ok"])
        self.assertGreaterEqual(result["count"], 3)
        self.assertGreaterEqual(len(result["track_samples"]), 5)
        self.assertIn("1581F8DBW25B800B3417", result["tracks"])
        self.assertIn("1581FANLC258U029RTN6", result["tracks"])
        self.assertGreaterEqual(len(result["tracks"]["1581FANLC258U029RTN6"]["aircraft"]), 2)
        self.assertGreaterEqual(len(result["tracks"]["1581FANLC258U029RTN6"]["operator"]), 2)

    def test_invalid_basic_id_serial_is_rejected(self):
        payload = bytearray(25)
        payload[0] = 0x00
        payload[1] = 0x01
        payload[2:6] = b".HP:"

        result = parse_rid_payload(bytes(payload), "dji_old_odid")

        self.assertFalse(result["ok"])
        self.assertEqual(result["format"], "UNKNOWN")

    def test_track_store_dedups_same_packet_hash(self):
        store = self.common_ns["_empty_track_store"]()
        append = self.common_ns["_track_store_append_sample"]

        first = {
            "track_type": "aircraft",
            "sn": "RID-1",
            "lat": 30.0,
            "lon": 121.0,
            "timestamp_ms": 1000,
            "receive_time_ms": 2000,
            "packet_hash": "pkt-1",
        }
        duplicate = dict(first)
        duplicate["receive_time_ms"] = 2001

        self.assertTrue(append(store, first))
        self.assertTrue(append(store, duplicate))
        self.assertEqual(len(store["aircraft"]), 1)
        self.assertEqual(store["last_aircraft"]["receive_time_ms"], 2001)

    def test_track_store_caps_points_and_keeps_latest_marker(self):
        store = self.common_ns["_empty_track_store"]()
        append = self.common_ns["_track_store_append_sample"]
        config = self.common_ns["APP_CONFIG"]
        old_basic = dict(config.get("basic") or {})
        config["basic"] = dict(old_basic)
        config["basic"]["track_points_limit"] = 10
        try:
            for idx in range(12):
                self.assertTrue(append(store, {
                    "track_type": "aircraft",
                    "sn": "RID-2",
                    "lat": 30.0 + idx * 0.001,
                    "lon": 121.0 + idx * 0.001,
                    "timestamp_ms": 1000 + idx,
                    "receive_time_ms": 2000 + idx,
                }))
            self.assertEqual(len(store["aircraft"]), 10)
            self.assertEqual(store["aircraft"][0]["timestamp_ms"], 1002)
            self.assertEqual(store["last_aircraft"]["timestamp_ms"], 1011)
        finally:
            config["basic"] = old_basic

    def test_import_payload_supports_legacy_and_dual_tracks(self):
        build_store = self.common_ns["_track_store_from_import_payload"]

        legacy_store, legacy_primary = build_store({
            "track": [
                {"lat": 30.1, "lon": 121.1, "ts": 1.0},
                {"lat": 30.2, "lon": 121.2, "ts": 2.0},
            ],
        }, sn="RID-3")
        self.assertEqual(len(legacy_store["aircraft"]), 2)
        self.assertEqual(len(legacy_store["operator"]), 0)
        self.assertEqual(len(legacy_primary), 2)

        dual_store, dual_primary = build_store({
            "aircraft": [
                {"lat": 30.3, "lon": 121.3, "timestamp_ms": 3000},
                {"lat": 30.4, "lon": 121.4, "timestamp_ms": 4000},
            ],
            "operator": [
                {"lat": 31.3, "lon": 122.3, "timestamp_ms": 3500},
                {"lat": 31.4, "lon": 122.4, "timestamp_ms": 4500},
            ],
        }, sn="RID-4")
        self.assertEqual(len(dual_store["aircraft"]), 2)
        self.assertEqual(len(dual_store["operator"]), 2)
        self.assertEqual(len(dual_primary), 2)
        self.assertEqual(dual_store["last_aircraft"]["timestamp_ms"], 4000)
        self.assertEqual(dual_store["last_operator"]["timestamp_ms"], 4500)

    def test_frontend_track_import_accepts_dual_track_payload(self):
        source = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")

        self.assertIn("var hasLegacyTrack = Array.isArray(payload.track);", source)
        self.assertIn("var hasDualTrack = Array.isArray(payload.aircraft) || Array.isArray(payload.operator);", source)
        self.assertIn("trackCache[payload.sn] = normalizeTrackCacheEntry(payload.tracks || payload);", source)

    def test_state_update_accepts_exact_rid_ssid_before_coordinates(self):
        state_table = self.process_ns["state_table"]
        history_table = self.process_ns["history_table"]
        mac_to_basic = self.process_ns["mac_to_basic"]
        mac_to_ssid_sn = self.process_ns["mac_to_ssid_sn"]
        state_update = self.process_ns["state_update"]
        self.process_ns["_fmt"] = lambda value, *args: "-" if value is None else str(value)
        self.process_ns["_notification_add"] = lambda *args, **kwargs: None
        self.process_ns["_notify_online_text"] = lambda *args, **kwargs: ""
        self.process_ns["_notify_zone_alarm_text"] = lambda *args, **kwargs: ""
        self.process_ns["queue_online_notification"] = lambda *args, **kwargs: None
        self.process_ns["queue_zone_alarm_notification"] = lambda *args, **kwargs: None

        state_table.clear()
        history_table.clear()
        mac_to_basic.clear()
        mac_to_ssid_sn.clear()

        state_update(
            "aa:bb:cc:dd:ee:ff",
            {
                "basic_id": {"uas_id": "1581F8DBW25B800B3417", "id_type": "Serial"},
                "location": None,
                "system": None,
                "metadata": {"format": "DJI_OLD_ODID", "rid_format": "DJI_OLD_ODID"},
            },
            rssi=-42,
            ch=6,
            ch_assumed=False,
            pl_sig=123,
            scan_type="rid",
            ssid="RID-1581F8DBW25B800B3417",
            capture_type="Beacon",
            raw_pkt_hex=None,
            firmware_type="old",
        )

        self.assertIn("1581F8DBW25B800B3417", state_table)
        self.assertIsNone(state_table["1581F8DBW25B800B3417"]["lat"])

        state_table.clear()
        history_table.clear()

        state_update(
            "aa:bb:cc:dd:ee:11",
            {
                "basic_id": {"uas_id": ".HP:", "id_type": "Serial"},
                "location": {"lat": 30.0, "lon": 121.0, "alt_geodetic": 20.0},
                "system": None,
                "metadata": {"format": "DJI_OLD_ODID", "rid_format": "DJI_OLD_ODID"},
            },
            rssi=-41,
            ch=6,
            ch_assumed=False,
            pl_sig=124,
            scan_type="rid",
            ssid="RID-1581F8DBW25B800B3417",
            capture_type="Beacon",
            raw_pkt_hex=None,
            firmware_type="old",
        )

        self.assertEqual({}, state_table)

        state_update(
            "aa:bb:cc:dd:ee:22",
            {
                "basic_id": {"uas_id": "1581F8DBW25B800B3417", "id_type": "Serial"},
                "location": {"lat": 30.0, "lon": 121.0, "alt_geodetic": 20.0},
                "system": None,
                "metadata": {"format": "DJI_ENTERPRISE_PRIVATE", "rid_format": "DJI_ENTERPRISE_PRIVATE"},
            },
            rssi=-40,
            ch=6,
            ch_assumed=False,
            pl_sig=125,
            scan_type="rid",
            ssid="RID-1581F8DBW25B800B3417",
            capture_type="Beacon",
            raw_pkt_hex=None,
            firmware_type="old",
        )

        self.assertIn("1581F8DBW25B800B3417", state_table)
        hist = history_table["1581F8DBW25B800B3417"]
        self.assertEqual(1, len(hist["tracks"]["aircraft"]))
        self.assertEqual(30.0, hist["tracks"]["aircraft"][0]["lat"])

    def test_track_get_route_applies_limit_to_dual_tracks_payload(self):
        source = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")

        self.assertIn('aircraft_query = dict(query)', source)
        self.assertIn('aircraft_query["track_type"] = ["aircraft"]', source)
        self.assertIn('operator_query["track_type"] = ["operator"]', source)
        self.assertIn('"aircraft": _track_for_query(tracks, aircraft_query, firmware_type=firmware_type)', source)
        self.assertIn('"operator": _track_for_query(tracks, operator_query, firmware_type=firmware_type)', source)

    def test_reidentify_history_packet_for_sn_no_longer_uses_undefined_track_points(self):
        history_table = self.process_ns["history_table"]
        state_table = self.process_ns["state_table"]
        reidentify = self.process_ns["reidentify_history_packet_for_sn"]
        self.process_ns["_resolve_model_name"] = lambda sn, scan_type=None, current_model=None: current_model or "N/A"
        target_sn = "1581F8DBW25B800B3417"
        history_table.clear()
        state_table.clear()
        try:
            history_table[target_sn] = {
                "sn": target_sn,
                "raw_packets": [{
                    "hex": LEGACY_ODID_RAW.hex(),
                    "ts": 1.0,
                }],
                "pkt_count_total": 1,
            }
            result = reidentify(target_sn, "auto")
            self.assertTrue(result["ok"])
            self.assertEqual(result["sn_now"], target_sn)
            self.assertGreaterEqual(result["track_count"], 1)
            self.assertIn("tracks", result)
        finally:
            history_table.clear()
            state_table.clear()

    def test_reidentify_preserves_longer_existing_aircraft_track_for_gb_cache(self):
        history_table = self.process_ns["history_table"]
        state_table = self.process_ns["state_table"]
        reidentify = self.process_ns["reidentify_history_packet_for_sn"]
        self.process_ns["_resolve_model_name"] = lambda sn, scan_type=None, current_model=None: current_model or "N/A"
        target_sn = "GB-PRESERVE-1"
        history_table.clear()
        state_table.clear()
        try:
            history_table[target_sn] = {
                "sn": target_sn,
                "track": [
                    {"lat": 30.0 + idx * 0.0001, "lon": 121.0 + idx * 0.0001, "ts": 1000.0 + idx}
                    for idx in range(120)
                ],
                "raw_packets": [{
                    "hex": GB46750_STANDARD_SAMPLE.hex(),
                    "ts": 2000.0,
                }],
                "pkt_count_total": 120,
            }
            result = reidentify(target_sn, "auto")
            self.assertTrue(result["ok"])
            self.assertEqual(result["before_counts"]["aircraft"], 120)
            self.assertEqual(result["rebuilt_counts"]["aircraft"], 1)
            self.assertEqual(result["rebuilt_counts"]["operator"], 1)
            self.assertEqual(result["final_counts"]["aircraft"], 120)
            self.assertEqual(result["final_counts"]["operator"], 1)
            self.assertTrue(result["preserve_existing_longer_tracks"])
            self.assertIn("aircraft", result["preserved_track_types"])
        finally:
            history_table.clear()
            state_table.clear()

    def test_reidentify_warns_when_only_one_raw_packet_exists(self):
        history_table = self.process_ns["history_table"]
        state_table = self.process_ns["state_table"]
        reidentify = self.process_ns["reidentify_history_packet_for_sn"]
        self.process_ns["_resolve_model_name"] = lambda sn, scan_type=None, current_model=None: current_model or "N/A"
        target_sn = "RAW-ONLY-1"
        history_table.clear()
        state_table.clear()
        try:
            history_table[target_sn] = {
                "sn": target_sn,
                "raw_packets": [{
                    "hex": GB46750_STANDARD_SAMPLE.hex(),
                    "ts": 3000.0,
                }],
                "pkt_count_total": 1,
            }
            result = reidentify(target_sn, "auto")
            self.assertTrue(result["ok"])
            self.assertEqual(result["before_counts"]["aircraft"], 0)
            self.assertEqual(result["rebuilt_counts"]["aircraft"], 1)
            self.assertEqual(result["rebuilt_counts"]["operator"], 1)
            self.assertEqual(result["final_counts"]["aircraft"], 1)
            self.assertEqual(result["final_counts"]["operator"], 1)
            self.assertFalse(result["preserve_existing_longer_tracks"])
            self.assertTrue(any("only has 1 raw packet" in msg for msg in result["warnings"]))
        finally:
            history_table.clear()
            state_table.clear()

    def test_realtime_append_120_packets_keeps_aircraft_and_operator_counts(self):
        store = self.common_ns["_empty_track_store"]()
        append = self.common_ns["_track_store_append_sample"]
        parsed = parse_rid_payload(GB46750_STANDARD_SAMPLE, "gb46750_2025")
        base_samples = parsed["track_samples"]
        for idx in range(120):
            for sample in base_samples:
                item = dict(sample)
                item["timestamp_ms"] = int(item.get("timestamp_ms") or 0) + idx
                item["receive_time_ms"] = 10_000 + idx
                item["packet_hash"] = f"pkt-{idx}"
                self.assertTrue(append(store, item))
        self.assertEqual(len(store["aircraft"]), 120)
        self.assertEqual(len(store["operator"]), 120)

    def test_history_touch_keeps_live_track_while_aircraft_is_online(self):
        history_table = self.process_ns["history_table"]
        touch = self.process_ns["_history_touch"]
        self.process_ns["_resolve_model_name"] = lambda sn, scan_type=None, current_model=None: current_model or "N/A"
        history_table.clear()
        try:
            live_entry = {
                "sn": "RID-LIVE-1",
                "tracks": {
                    "aircraft": [{
                        "track_type": "aircraft",
                        "sample_type": "aircraft",
                        "sn": "RID-LIVE-1",
                        "lat": 30.1,
                        "lon": 121.1,
                        "timestamp_ms": 1000,
                        "receive_time_ms": 1000,
                    }],
                    "operator": [],
                    "last_aircraft": {
                        "track_type": "aircraft",
                        "sample_type": "aircraft",
                        "sn": "RID-LIVE-1",
                        "lat": 30.1,
                        "lon": 121.1,
                        "timestamp_ms": 1000,
                        "receive_time_ms": 1000,
                    },
                    "last_operator": None,
                },
                "track_updated_wall_ts": 1.0,
                "raw_packets": [],
            }
            touch(live_entry, 1.0, 1.0)
            hist = history_table["RID-LIVE-1"]
            self.assertEqual(1, len(hist["tracks"]["aircraft"]))
            self.assertEqual(1, len(hist["track"]))
            self.assertEqual(1.0, hist["track_updated_wall_ts"])
        finally:
            history_table.clear()

    def test_history_storage_raw_packet_roundtrips_parsed_snapshot(self):
        ns = common_namespace()
        with tempfile.TemporaryDirectory(prefix="rid_raw_packet_store_") as tmpdir:
            db_path = os.path.join(tmpdir, "rid_storage.db")
            ns["HISTORY_STORE_PATH"] = db_path
            ns["_history_storage_append_raw_packet"]("RID-STORE-1", {
                "ts": "2026-01-01 00:00:00",
                "_wall_ts": 1.0,
                "capture_type": "Beacon",
                "firmware_type": "new",
                "uas_id": "RID-STORE-1",
                "hex": "fa0bbc0d",
                "parse_mode": "live",
                "parse_format": "GB46750_2025",
                "parsed": {"location": {"lat": 30.1, "lon": 121.1}},
            }, db_path)
            packets = ns["_history_storage_fetch_raw_packets"]("RID-STORE-1", path=db_path)
            self.assertEqual(1, len(packets))
            self.assertEqual("live", packets[0]["parse_mode"])
            self.assertEqual("GB46750_2025", packets[0]["parse_format"])
            self.assertEqual(30.1, packets[0]["parsed"]["location"]["lat"])
            ns["_history_db_close_locked"]()

    def test_reidentify_preserves_longer_existing_aircraft_track_for_legacy_dji(self):
        history_table = self.process_ns["history_table"]
        state_table = self.process_ns["state_table"]
        reidentify = self.process_ns["reidentify_history_packet_for_sn"]
        self.process_ns["_resolve_model_name"] = lambda sn, scan_type=None, current_model=None: current_model or "N/A"
        target_sn = "1581F8DBW25B800B3417"
        history_table.clear()
        state_table.clear()
        try:
            history_table[target_sn] = {
                "sn": target_sn,
                "track": [
                    {"lat": 30.0 + idx * 0.0001, "lon": 121.0 + idx * 0.0001, "ts": 4000.0 + idx}
                    for idx in range(120)
                ],
                "raw_packets": [{
                    "hex": LEGACY_ODID_RAW.hex(),
                    "ts": 5000.0,
                }],
                "pkt_count_total": 120,
            }
            result = reidentify(target_sn, "auto")
            self.assertTrue(result["ok"])
            self.assertEqual(result["before_counts"]["aircraft"], 120)
            self.assertEqual(result["rebuilt_counts"]["aircraft"], 1)
            self.assertEqual(result["rebuilt_counts"]["operator"], 1)
            self.assertEqual(result["final_counts"]["aircraft"], 120)
            self.assertEqual(result["final_counts"]["operator"], 1)
            self.assertTrue(result["preserve_existing_longer_tracks"])
            self.assertIn("aircraft", result["preserved_track_types"])
        finally:
            history_table.clear()
            state_table.clear()

    def test_first_startup_creates_config_and_sqlite_store_when_paths_are_missing(self):
        ns = startup_namespace("station_edition.light_rid._test_first_startup_default")
        with tempfile.TemporaryDirectory(prefix="rid_first_startup_default_") as tmpdir:
            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                config_path = os.path.join(tmpdir, "config.json")
                db_path = ns["_history_store_default_path"](config_path)
                ns["APP_CONFIG_PATH"] = config_path
                ns["APP_CONFIG_PATH_LOCKED"] = False
                ns["HISTORY_STORE_PATH"] = db_path
                ns["_history_set_legacy_source_paths"]([])

                ns["_ensure_runtime_json_files"](config_path, db_path, config_locked=False)
                cfg = ns["load_app_config"](config_path)
                ns["APP_CONFIG"] = cfg
                ns["load_history_store"](db_path)
                self.assertTrue(ns["save_history_store"](force=True))
                ns["_history_db_close_locked"]()
                ns["history_table"].clear()
                ns["load_history_store"](db_path)

                file_info = ns["_scan_data_file_info"](db_path)
                self.assertTrue(os.path.exists(config_path))
                self.assertTrue(os.path.exists(db_path))
                self.assertTrue(file_info["exists"])
                self.assertGreaterEqual(int(file_info["size"]), 1)
                self.assertEqual(cfg["basic"]["history_file"], db_path)
            finally:
                os.chdir(old_cwd)
                ns["_history_db_close_locked"]()

    def test_first_startup_with_locked_missing_config_uses_defaults_and_creates_sqlite_store(self):
        ns = startup_namespace("station_edition.light_rid._test_first_startup_locked")
        with tempfile.TemporaryDirectory(prefix="rid_first_startup_locked_") as tmpdir:
            config_path = os.path.join(tmpdir, "nested", "config.json")
            db_path = ns["_history_store_default_path"](config_path)
            ns["APP_CONFIG_PATH"] = config_path
            ns["APP_CONFIG_PATH_LOCKED"] = True
            ns["HISTORY_STORE_PATH"] = db_path
            ns["_history_set_legacy_source_paths"]([])

            ns["_ensure_runtime_json_files"](config_path, db_path, config_locked=True)
            cfg = ns["load_app_config"](config_path)
            ns["APP_CONFIG"] = cfg
            ns["load_history_store"](db_path)
            self.assertTrue(ns["save_history_store"](force=True))
            ns["_history_db_close_locked"]()
            ns["history_table"].clear()
            ns["load_history_store"](db_path)

            file_info = ns["_scan_data_file_info"](db_path)
            self.assertFalse(os.path.exists(config_path))
            self.assertTrue(os.path.exists(db_path))
            self.assertTrue(file_info["exists"])
            self.assertGreaterEqual(int(file_info["size"]), 1)
            self.assertIn("basic", cfg)
            ns["_history_db_close_locked"]()


if __name__ == "__main__":
    unittest.main()
