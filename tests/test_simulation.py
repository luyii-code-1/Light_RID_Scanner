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

    def test_simulated_targets_appear_in_lightweight_snapshot_only_in_memory(self):
        result = self.ns["simulation_start"]({
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
        self.ns["simulation_start"]({"count": 2})

        result = self.ns["simulation_stop"]()

        self.assertEqual(2, result["removed"])
        self.assertIn("REAL-TARGET", self.ns["state_table"])
        self.assertFalse(any(entry.get("_simulation") for entry in self.ns["state_table"].values()))

    def test_rejects_invalid_scenario(self):
        result = self.ns["simulation_start"]({"count": 101})
        self.assertFalse(result["ok"])
        self.assertIn("between 1 and 100", result["error"])


if __name__ == "__main__":
    unittest.main()
