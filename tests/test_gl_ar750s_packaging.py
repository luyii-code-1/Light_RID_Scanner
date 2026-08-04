from __future__ import annotations

import os
import json
import contextlib
import io
import sys
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
        self.assertIn("openwrt/light-rid-install", workflow)
        self.assertIn("openwrt/light-rid-upgrade", workflow)
        self.assertIn("package-manifest.sha256", workflow)
        self.assertIn("! -path './usr/share/light-rid/rid_model.json'", workflow)
        self.assertIn("test ! -e \"$root/etc/light-rid/config.json\"", workflow)
        self.assertIn('"$root/etc/light-rid/EULA.md"', workflow)
        self.assertIn('"$root/etc/light-rid/rid_build_info.json"', workflow)
        self.assertFalse(Path("openwrt/light-rid.init").exists())

    def test_router_defaults_are_bounded_and_offline(self) -> None:
        config = json.loads(Path("openwrt/config.gl-ar750s.json").read_text(encoding="utf-8"))
        self.assertEqual(config["basic"]["iface"], "ridmon")
        self.assertEqual(config["basic"]["model_map"], "/etc/light-rid/rid_model.json")
        self.assertLessEqual(config["basic"]["track_points_limit"], 5000)
        self.assertFalse(config["web"]["allow_restart"])
        self.assertFalse(config["metrics"]["enabled"])
        self.assertFalse(config["model_update"]["enabled"])
        self.assertFalse(config["app_update"]["enabled"])

    def test_router_scripts_do_not_register_autostart(self) -> None:
        scripts = "\n".join(
            Path(path).read_text(encoding="utf-8")
            for path in (
                "openwrt/light-rid-run",
                "openwrt/light-rid-install",
                "openwrt/light-rid-upgrade",
            )
        )
        self.assertNotIn("procd_set_param", scripts)
        self.assertNotIn("/etc/rc.common", scripts)
        self.assertIn("already running", scripts)
        self.assertIn("station process already exists outside this launcher", scripts)
        self.assertIn("stop_runtime", scripts)
        self.assertIn("cleanup must restore radio1", scripts)
        self.assertIn("stop it before install", scripts)
        self.assertIn("existing configuration preserved", scripts)
        self.assertIn("initial model map installed", scripts)
        self.assertIn("memory_available_kb", scripts)
        self.assertIn("hashlib.scrypt", scripts)
        self.assertIn("secrets.token_urlsafe", scripts)
        self.assertIn("only its scrypt hash was stored", scripts)
        self.assertIn("unsafe archive path detected", scripts)
        self.assertIn("archive checksum verification failed", scripts)

    def test_installer_credential_provisioner_is_valid_python(self) -> None:
        installer = Path("openwrt/light-rid-install").read_text(encoding="utf-8")
        marker = "<<'PY'\n"
        self.assertIn(marker, installer)
        provisioner = installer.split(marker, 1)[1].split("\nPY\n", 1)[0]
        compile(provisioner, "light-rid-install:provision_auth", "exec")
        with tempfile.TemporaryDirectory() as tmp:
            config_path = Path(tmp) / "config.json"
            config_path.write_text('{"auth":{"enabled":false}}\n', encoding="utf-8")
            previous_argv = sys.argv
            output = io.StringIO()
            try:
                sys.argv = ["provision_auth", str(config_path)]
                with contextlib.redirect_stdout(output):
                    exec(compile(provisioner, "provision_auth", "exec"), {})
            finally:
                sys.argv = previous_argv
            config_text = config_path.read_text(encoding="utf-8")
            config = json.loads(config_text)
        auth = config["auth"]
        self.assertTrue(auth["enabled"])
        self.assertTrue(auth["username_hash"].startswith("scrypt$16384$8$1$"))
        self.assertTrue(auth["password_hash"].startswith("scrypt$16384$8$1$"))
        self.assertNotIn("admin_password", config_text)
        self.assertIn("admin_password=", output.getvalue())
        password = output.getvalue().split("admin_password=", 1)[1].splitlines()[0]
        self.assertGreaterEqual(len(password), 16)
        self.assertNotIn(password, config_text)


if __name__ == "__main__":
    unittest.main()
