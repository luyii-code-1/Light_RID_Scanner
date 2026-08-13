import unittest

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


def simulation_namespace():
    return load_namespace(
        create_runtime_context(
            chunk_files=(
                "common_core.py",
                "hardware_core.py",
                "scan_core.py",
                "process_core.py",
                "simulation_core.py",
            ),
            module_name="station_edition.light_rid._test_simulation",
        )
    )


class SimulationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ns = simulation_namespace()

    def tearDown(self):
        self.ns["simulation_stop"]()
        self.ns["state_table"].clear()
        self.ns["history_table"].clear()

    def _start_memory(self, body=None):
        payload = {"transport": "memory", "center_lat": 30.0, "center_lon": 121.0}
        payload.update(body or {})
        return self.ns["simulation_start"](payload)

    def test_simulated_targets_appear_in_lightweight_snapshot_only_in_memory(self):
        result = self._start_memory({
            "count": 3,
            "pattern": "circle",
            "center_lat": 30.0,
            "center_lon": 121.0,
            "radius_m": 250,
            "speed_mps": 10,
        })

        self.assertTrue(result["ok"])
        self.assertEqual(3, result["count"])
        rows = [
            row for row in self.ns["_state_snapshot"](lightweight=True)["drones"]
            if row.get("capture_type") == "simulation"
        ]
        self.assertEqual(3, len(rows))
        self.assertTrue(all(len(row["sn"]) == 20 for row in rows))
        self.assertEqual({}, self.ns["history_table"])

    def test_stop_removes_simulated_targets_without_touching_real_target(self):
        self.ns["state_table"]["REAL-TARGET"] = {"sn": "REAL-TARGET"}
        self._start_memory({"count": 2})

        result = self.ns["simulation_stop"]()

        self.assertEqual(2, result["removed"])
        self.assertIn("REAL-TARGET", self.ns["state_table"])
        self.assertFalse(any(entry.get("_simulation") for entry in self.ns["state_table"].values()))

    def test_rejects_invalid_scenario(self):
        result = self._start_memory({"count": 101})
        self.assertFalse(result["ok"])
        self.assertIn("between 1 and 100", result["error"])

    def test_defaults_to_configured_base_station_coordinates(self):
        self.ns["WEB_CFG"] = {"base_lat": 31.25, "base_lon": 121.5}
        result = self.ns["simulation_start"]({"transport": "memory", "count": 1})
        self.assertTrue(result["ok"])
        self.assertEqual(31.25, result["options"]["center_lat"])
        self.assertEqual(121.5, result["options"]["center_lon"])

    def test_missing_base_station_coordinates_has_no_hardcoded_fallback(self):
        self.ns["WEB_CFG"] = {}
        result = self.ns["simulation_start"]({"transport": "memory", "count": 1})
        self.assertFalse(result["ok"])
        self.assertIn("not configured", result["error"])

    def test_network_transport_requires_configured_scan_interface(self):
        self.ns["APP_CONFIG"] = {"basic": {}}
        result = self.ns["simulation_start"]({"center_lat": 30.0, "center_lon": 121.0})
        self.assertFalse(result["ok"])
        self.assertIn("scan interface", result["error"])

    def test_network_payload_encodes_simulated_coordinates(self):
        entry = {
            "sn": "SIM00010000000000001",
            "lat": 31.25,
            "lon": 121.5,
            "alt": 120.0,
            "speed": 12.0,
            "vspeed": 0.0,
            "pilot_lat": 31.2,
            "pilot_lon": 121.4,
        }
        messages = self.ns["_simulation_odid_messages"](entry)
        decoded_location = self.ns["decode_location"](messages[1])
        decoded_system = self.ns["decode_system"](messages[2])
        self.assertAlmostEqual(31.25, decoded_location["lat"], places=6)
        self.assertAlmostEqual(121.5, decoded_location["lon"], places=6)
        self.assertAlmostEqual(31.2, decoded_system["pilot_lat"], places=6)
        self.assertAlmostEqual(121.4, decoded_system["pilot_lon"], places=6)


if __name__ == "__main__":
    unittest.main()
