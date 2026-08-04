from __future__ import annotations

import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


class GlAr750sPackagingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runtime = load_namespace(create_runtime_context())

    def test_settings_template_resolves_from_installed_app_root(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            app_root = Path(tmp)
            template = app_root / "station_edition/light_rid/assets/templates/router-only.html"
            template.parent.mkdir(parents=True)
            template.write_text("router settings", encoding="utf-8")
            with mock.patch.dict(os.environ, {"LIGHT_RID_APP_ROOT": str(app_root)}):
                resolved = self.runtime["_station_asset_path"](
                    "assets", "templates", "router-only.html"
                )
        self.assertEqual(resolved, template)

    def test_settings_html_is_packaged_and_renderable(self) -> None:
        rendered = self.runtime["_build_settings_html"]()
        self.assertNotIn("settings template missing", rendered)
        self.assertIn("station-settings.js", rendered)

    def test_runtime_security_does_not_probe_uid(self) -> None:
        with mock.patch.object(os, "geteuid", side_effect=AssertionError("UID probed"), create=True):
            payload = self.runtime["_runtime_security_payload"]()
        self.assertFalse(payload["running_as_root"])
        self.assertEqual(payload["risk"], "")

    def test_router_package_has_no_init_service(self) -> None:
        workflow = Path(".github/workflows/gl-ar750s.yml").read_text(encoding="utf-8")
        self.assertNotIn("install -m 0755 openwrt/light-rid.init", workflow)
        self.assertIn("openwrt/light-rid-run", workflow)
        self.assertFalse(Path("openwrt/light-rid.init").exists())


if __name__ == "__main__":
    unittest.main()
