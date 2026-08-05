from __future__ import annotations

import os
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


class RouterManagementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.runtime = load_namespace(create_runtime_context())

    def valid_payload(self) -> dict:
        return {
            "mode": "wired",
            "wan": {"protocol": "dhcp", "dns": []},
            "lan": {
                "ipaddr": "192.168.8.1",
                "netmask": "255.255.255.0",
                "dhcp_enabled": True,
                "dhcp_start": 100,
                "dhcp_limit": 150,
                "lease_time": "12h",
                "dns": [],
            },
            "ap": {
                "enabled": True,
                "ssid_mode": "normal",
                "ssid": "Light-RID",
                "password": "factory-password",
                "channel": 36,
                "htmode": "VHT80",
                "txpower": 20,
            },
            "repeater": {"ssid": "", "bssid": "", "encryption": "psk2", "password": ""},
            "port_forwards": [],
            "remote_management": {"enabled": False},
        }

    def test_router_page_is_packaged_and_renderable(self) -> None:
        rendered = self.runtime["_build_router_html"]()
        self.assertNotIn("router template missing", rendered)
        self.assertIn("/assets/vue/router.js", rendered)
        self.assertIn("IP 模式", rendered)
        self.assertIn("保存设置", rendered)
        self.assertNotIn("恢复安装前网络", rendered)
        self.assertNotIn("访客 5GHz AP", rendered)
        self.assertNotIn("IPv6 状态", rendered)
        self.assertIn("LuCI", rendered)

    def test_router_page_resolves_from_installed_app_root(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            app_root = Path(tmp)
            template = app_root / "station_edition/light_rid/assets/templates/router.html"
            template.parent.mkdir(parents=True)
            template.write_text("router", encoding="utf-8")
            with mock.patch.dict(os.environ, {"LIGHT_RID_APP_ROOT": str(app_root)}):
                resolved = self.runtime["_router_template_path"]()
        self.assertEqual(resolved, template)

    def test_valid_wired_configuration_normalizes(self) -> None:
        normalized, errors = self.runtime["_router_validate_config"](self.valid_payload())
        self.assertEqual(errors, [])
        self.assertEqual(normalized["mode"], "wired")
        self.assertEqual(normalized["wan"]["protocol"], "dhcp")

    def test_router_redirect_preserves_browser_address(self) -> None:
        source = Path("station_edition/light_rid/assets/vue/router.js").read_text(encoding="utf-8")
        self.assertIn("new URL(location.href)", source)
        self.assertIn("location.assign(url)", source)
        self.assertNotIn("data.transaction && data.transaction.new_url", source)
        self.assertIn('url.pathname = "/cgi-bin/luci"', source)
        self.assertNotIn("/api/router/confirm", source)
        self.assertNotIn("/api/router/rollback", source)

    def test_ip_ssid_mode_does_not_require_custom_ssid(self) -> None:
        payload = self.valid_payload()
        payload["ap"]["ssid_mode"] = "ip"
        payload["ap"]["ssid"] = ""
        normalized, errors = self.runtime["_router_validate_config"](payload)
        self.assertEqual(errors, [])
        self.assertEqual(normalized["ap"]["ssid_mode"], "ip")

    def test_management_ip_prefers_upstream_interface(self) -> None:
        function = self.runtime["_router_management_ipv4"]
        globals_map = function.__globals__
        original_status = globals_map["_router_interface_status"]
        try:
            globals_map["_router_interface_status"] = lambda name: {
                "up": name in {"wan", "lan"},
                "addresses": {"wan": ["192.168.1.164/24"], "lan": ["192.168.8.1/24"]}.get(name, []),
            }
            self.assertEqual(function(), "192.168.1.164")
        finally:
            globals_map["_router_interface_status"] = original_status

    def test_static_wan_and_forward_validation(self) -> None:
        payload = self.valid_payload()
        payload["wan"] = {
            "protocol": "static",
            "ipaddr": "10.10.10.2",
            "netmask": "255.255.255.0",
            "gateway": "10.10.10.1",
            "dns": ["1.1.1.1"],
        }
        payload["port_forwards"] = [{
            "name": "web",
            "protocol": "tcp",
            "external_port": 8080,
            "internal_ip": "192.168.8.10",
            "internal_port": 80,
        }]
        normalized, errors = self.runtime["_router_validate_config"](payload)
        self.assertEqual(errors, [])
        self.assertEqual(normalized["port_forwards"][0]["external_port"], 8080)

    def test_radio1_is_never_targeted_by_router_commands(self) -> None:
        source = Path("station_edition/light_rid/router_core.py").read_text(encoding="utf-8")
        command_lines = [line for line in source.splitlines() if "_router_run([" in line or "setv(" in line]
        self.assertFalse(any("radio1" in line or "phy1" in line for line in command_lines))
        self.assertIn('["wifi", "reload", "radio0"]', source)
        self.assertNotIn('["wifi", "reload"]', source)

    def test_uci_apply_targets_only_managed_router_sections(self) -> None:
        normalized, errors = self.runtime["_router_validate_config"](self.valid_payload())
        self.assertEqual(errors, [])
        commands = []
        globals_map = self.runtime["_router_apply_uci"].__globals__
        original_run = globals_map["_router_run"]
        original_show = globals_map["_router_uci_show"]
        try:
            globals_map["_router_run"] = lambda args, timeout=15, input_text=None: (commands.append(list(args)) or (True, ""))
            globals_map["_router_uci_show"] = lambda package: {
                "firewall.@zone[1].name": "wan",
                "firewall.vendor_rule": "rule",
            } if package == "firewall" else {}
            ok, message = self.runtime["_router_apply_uci"](normalized)
        finally:
            globals_map["_router_run"] = original_run
            globals_map["_router_uci_show"] = original_show
        self.assertTrue(ok, message)
        rendered = repr(commands)
        self.assertIn("wireless.radio0.channel=36", rendered)
        self.assertIn("wireless.default_radio0.light_rid_ssid_mode=normal", rendered)
        self.assertIn("network.wwan=interface", rendered)
        self.assertIn("firewall.light_rid_wan_admin=rule", rendered)
        self.assertIn("firewall.@zone[1].network=wwan", rendered)
        self.assertNotIn("radio1", rendered)
        self.assertNotIn("phy1", rendered)
        self.assertNotIn("vendor_rule", rendered)
        self.assertIn("wireless.guest5g", rendered)

    def test_status_redacts_openwrt_secrets(self) -> None:
        values = {
            "wireless.default_radio0.key": "main-secret",
            "wireless.light_rid_repeater.key": "repeater-secret",
            "network.wan.password": "pppoe-secret",
        }
        globals_map = self.runtime["_router_config_payload"].__globals__
        original_get = globals_map["_router_uci_get"]
        original_show = globals_map["_router_uci_show"]
        try:
            globals_map["_router_uci_get"] = lambda key, default="": values.get(key, default)
            globals_map["_router_uci_show"] = lambda package: {
                key: value for key, value in values.items() if key.startswith(package + ".")
            }
            payload = self.runtime["_router_config_payload"]()
        finally:
            globals_map["_router_uci_get"] = original_get
            globals_map["_router_uci_show"] = original_show
        rendered = repr(payload)
        for secret in values.values():
            self.assertNotIn(secret, rendered)
        self.assertTrue(payload["ap"]["password"]["configured"])

    def test_startup_refreshes_ip_mode_ssid(self) -> None:
        launcher = Path("openwrt/light-rid-run").read_text(encoding="utf-8")
        self.assertIn("refresh_management_ssid", launcher)
        self.assertIn('desired_ssid="RID-$management_ip"', launcher)
        self.assertIn("wireless.default_radio0.light_rid_ssid_mode", launcher)

    def test_router_routes_use_direct_save_only(self) -> None:
        server = Path("station_edition/light_rid/web_server.py").read_text(encoding="utf-8")
        self.assertIn('path == "/api/router/apply"', server)
        self.assertNotIn('path == "/api/router/confirm"', server)
        self.assertNotIn('path == "/api/router/rollback"', server)
        self.assertNotIn('path == "/api/router/reset-network"', server)

    def test_apply_payload_saves_without_transaction(self) -> None:
        function = self.runtime["_router_apply_payload"]
        globals_map = function.__globals__
        originals = {name: globals_map[name] for name in ("_router_capabilities", "_router_validate_config", "_router_uci_get", "_router_apply_uci", "Thread")}

        class DummyThread:
            def __init__(self, **kwargs):
                self.kwargs = kwargs
            def start(self):
                return None

        normalized, errors = self.runtime["_router_validate_config"](self.valid_payload())
        self.assertEqual(errors, [])
        try:
            globals_map["_router_capabilities"] = lambda: {"supported": True}
            globals_map["_router_validate_config"] = lambda payload: (normalized, [])
            globals_map["_router_uci_get"] = lambda key, default="": "configured-secret"
            globals_map["_router_apply_uci"] = lambda config: (True, "")
            globals_map["Thread"] = DummyThread
            response, code = function(self.valid_payload())
        finally:
            globals_map.update(originals)
        self.assertEqual(code, 200)
        self.assertTrue(response["saved"])
        self.assertNotIn("transaction", response)

    def test_installer_preserves_original_network_baseline(self) -> None:
        installer = Path("openwrt/light-rid-install").read_text(encoding="utf-8")
        self.assertIn("backup_original_network", installer)
        self.assertIn("openwrt-original", installer)
        self.assertIn("manifest.sha256", installer)
        self.assertIn("--factory-provision", installer)
        self.assertIn("LIGHT_RID_FACTORY_WIFI_PASSWORD", installer)
        self.assertNotIn("echo \"$wifi_password\"", installer)


if __name__ == "__main__":
    unittest.main()
