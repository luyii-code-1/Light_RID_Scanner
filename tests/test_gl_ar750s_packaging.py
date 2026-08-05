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
        self.assertIn("btn-sync-system-time", rendered)

    def test_system_time_sync_uses_browser_epoch(self) -> None:
        function = self.runtime["_sync_system_time_payload"]
        globals_map = function.__globals__
        completed = mock.Mock(returncode=0, stdout="", stderr="")
        with mock.patch.dict(globals_map["os"].environ, {}, clear=False), \
             mock.patch.object(globals_map["sys"], "platform", "linux"), \
             mock.patch.object(globals_map["shutil"], "which", side_effect=lambda name: f"/sbin/{name}"), \
             mock.patch.object(globals_map["os"].path, "exists", return_value=True), \
             mock.patch.object(globals_map["subprocess"], "run", return_value=completed) as run:
            payload = function({"epoch_ms": 1_800_000_000_250, "timezone": "Asia/Shanghai", "timezone_offset_min": -480})
        self.assertTrue(payload["ok"])
        self.assertEqual(payload["browser_timezone"], "Asia/Shanghai")
        self.assertEqual(payload["system_timezone"], "CST-8")
        self.assertEqual(run.call_count, 5)
        self.assertEqual(run.call_args_list[0].args[0], ["/sbin/date", "-s", "@1800000000"])
        self.assertEqual(run.call_args_list[1].args[0], ["/sbin/uci", "set", "system.@system[0].zonename=Asia/Shanghai"])
        self.assertEqual(run.call_args_list[2].args[0], ["/sbin/uci", "set", "system.@system[0].timezone=CST-8"])
        self.assertEqual(run.call_args_list[3].args[0], ["/sbin/uci", "commit", "system"])
        self.assertEqual(run.call_args_list[4].args[0], ["/etc/init.d/system", "reload"])

    def test_system_time_sync_rejects_invalid_epoch(self) -> None:
        payload = self.runtime["_sync_system_time_payload"]({"epoch_ms": "not-a-time"})
        self.assertFalse(payload["ok"])
        self.assertEqual(payload["error"], "invalid epoch_ms")

    def test_browser_timezone_supports_fractional_offsets(self) -> None:
        function = self.runtime["_browser_timezone_config"]
        self.assertEqual(function({"timezone": "Asia/Kolkata", "timezone_offset_min": -330}), ("Asia/Kolkata", "UTC-5:30"))
        self.assertEqual(function({"timezone": "America/New_York", "timezone_offset_min": 240}), ("America/New_York", "UTC+4"))

    def test_bootstrap_prefers_gh_proxy_with_verified_fallbacks(self) -> None:
        installer = Path("openwrt/install-gl-ar750s.sh").read_text(encoding="utf-8")
        self.assertIn("https://gh-proxy.com/https://github.com/", installer)
        self.assertLess(installer.index('download_verified_package "$GH_PROXY_DOWNLOAD_BASE"'), installer.index('download_verified_package "$MIRROR_DOWNLOAD_BASE"'))
        self.assertIn('sha256sum -c "$ASSET.sha256"', installer)

    def test_runtime_security_does_not_probe_uid(self) -> None:
        with mock.patch.object(os, "geteuid", side_effect=AssertionError("UID probed"), create=True):
            payload = self.runtime["_runtime_security_payload"]()
        self.assertFalse(payload["running_as_root"])
        self.assertEqual(payload["risk"], "")

    def test_router_package_has_procd_service(self) -> None:
        workflow = Path(".github/workflows/gl-ar750s.yml").read_text(encoding="utf-8")
        self.assertIn("openwrt/light-rid.init", workflow)
        self.assertIn("openwrt/light-rid-run", workflow)
        self.assertIn("openwrt/light-rid-install", workflow)
        self.assertIn("openwrt/light-rid-upgrade", workflow)
        self.assertIn("package-manifest.sha256", workflow)
        self.assertIn("! -path './usr/share/light-rid/rid_model.json'", workflow)
        self.assertIn("test ! -e \"$root/etc/light-rid/config.json\"", workflow)
        self.assertIn('"$root/etc/light-rid/EULA.md"', workflow)
        self.assertIn('"$root/etc/light-rid/rid_build_info.json"', workflow)
        self.assertIn("assets/templates/router.html", workflow)
        self.assertIn("assets/vue/router.js", workflow)
        self.assertIn("router_core.py", workflow)
        self.assertTrue(Path("openwrt/light-rid.init").exists())

    def test_router_defaults_are_bounded_and_offline(self) -> None:
        config = json.loads(Path("openwrt/config.gl-ar750s.json").read_text(encoding="utf-8"))
        self.assertEqual(config["basic"]["iface"], "ridmon")
        self.assertEqual(config["basic"]["model_map"], "/etc/light-rid/rid_model.json")
        self.assertLessEqual(config["basic"]["track_points_limit"], 5000)
        self.assertFalse(config["web"]["allow_restart"])
        self.assertFalse(config["metrics"]["enabled"])
        self.assertFalse(config["model_update"]["enabled"])
        self.assertFalse(config["app_update"]["enabled"])

    def test_router_scripts_register_supervised_autostart(self) -> None:
        scripts = "\n".join(
            Path(path).read_text(encoding="utf-8")
            for path in (
                "openwrt/light-rid-run",
                "openwrt/light-rid-install",
                "openwrt/light-rid-upgrade",
            )
        )
        self.assertIn("already running", scripts)
        self.assertIn("station process already exists outside this launcher", scripts)
        self.assertIn("stop_runtime", scripts)
        self.assertIn("radio1 stays reserved for RID", scripts)
        self.assertIn("stop it before install", scripts)
        self.assertIn("existing configuration preserved", scripts)
        self.assertIn("initial model map installed", scripts)
        self.assertIn("memory_available_kb", scripts)
        self.assertIn("hashlib.scrypt", scripts)
        self.assertIn("secrets.token_urlsafe", scripts)
        self.assertIn("only its scrypt hash was stored", scripts)
        self.assertIn("unsafe archive path detected", scripts)
        self.assertIn("archive checksum verification failed", scripts)
        self.assertIn("/etc/init.d/light-rid enable", scripts)
        self.assertIn("light-rid-run reserve", scripts)

        init_script = Path("openwrt/light-rid.init").read_text(encoding="utf-8")
        self.assertIn("#!/bin/sh /etc/rc.common", init_script)
        self.assertIn("USE_PROCD=1", init_script)
        self.assertIn("procd_set_param respawn", init_script)
        self.assertIn('procd_set_param command "$PROG" supervise', init_script)

    def test_one_click_deployer_is_in_ci_artifact(self) -> None:
        workflow = Path(".github/workflows/gl-ar750s.yml").read_text(encoding="utf-8")
        deployer = Path("openwrt/deploy-gl-ar750s.ps1").read_text(encoding="utf-8")
        self.assertIn("openwrt/deploy-gl-ar750s.ps1", workflow)
        self.assertIn("light-rid-upgrade", deployer)
        self.assertIn("/etc/rc.d/S96light-rid", deployer)

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
