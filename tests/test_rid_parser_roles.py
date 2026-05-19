import struct
import unittest
from pathlib import Path

from station_edition.light_rid.analize_core import parse_raw_packet
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


class RidParserRoleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ns = parser_namespace()

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
        self.assertEqual(result["sub_format"], "FF2048_EXTENDED_COORD_PAIR")
        self.assertAlmostEqual(result["aircraft_position"]["lat"], 30.0602531, places=7)
        self.assertAlmostEqual(result["operator_positions"][0]["lon"], 121.2004249, places=7)

    def test_frontend_map_uses_role_specific_fields(self):
        source = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")

        self.assertIn("function aircraftMapCoord(e)", source)
        self.assertIn("var airCoord = aircraftMapCoord(e);", source)
        self.assertIn("function primaryOperatorCoord(e)", source)
        self.assertIn("var op = primaryOperatorCoord(e);", source)
        self.assertNotIn("home_lat || e.lat", source)
        self.assertNotIn("aux_lat || e.lat", source)


if __name__ == "__main__":
    unittest.main()
