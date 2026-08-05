"""GL-AR750S router management through OpenWrt UCI/ubus.

This chunk is loaded into the shared station runtime namespace.  It deliberately
does not reuse network_binding_core: netifd remains the sole owner of router
interfaces while radio1 remains reserved for RID capture.
"""

from __future__ import annotations

ROUTER_BOARD = "glinet,gl-ar750s-nor-nand"
ROUTER_CONFIG_FILES = ("network", "wireless", "dhcp", "firewall", "uhttpd")
ROUTER_TX_ROOT = "/tmp/light-rid-router"
ROUTER_ORIGINAL_ROOT = "/etc/light-rid/openwrt-original"
ROUTER_ROLLBACK_SECONDS = 60
ROUTER_SAFE_CHANNELS = {36, 40, 44, 48, 149, 153, 157, 161, 165}
ROUTER_HTMODES = {"VHT20", "VHT40", "VHT80"}
ROUTER_UPLINK_ENCRYPTIONS = {"none", "psk2", "psk-mixed", "sae", "sae-mixed"}
router_tx_lock = Lock()
router_active_tx: dict = {}


def _router_read_text(path: str) -> str:
    try:
        return Path(path).read_text(encoding="utf-8", errors="replace").strip()
    except OSError:
        return ""


def _router_capabilities() -> dict:
    board = _router_read_text("/tmp/sysinfo/board_name")
    release = _router_read_text("/etc/openwrt_release")
    commands = {name: bool(shutil.which(name)) for name in ("uci", "ubus", "wifi", "ifup", "ifdown", "iwinfo")}
    architecture_ok = "DISTRIB_ARCH='mips_24kc'" in release
    return {
        "supported": board == ROUTER_BOARD and architecture_ok and all(commands.values()),
        "board": board or "unknown",
        "target": "GL-AR750S",
        "architecture": "mips_24kc" if architecture_ok else "unknown",
        "openwrt": "DISTRIB_ID='OpenWrt'" in release or "OpenWrt" in release,
        "commands": commands,
        "radio1_reserved": True,
        "rollback_seconds": ROUTER_ROLLBACK_SECONDS,
    }


def _router_run(args: list[str], timeout: int = 15, input_text: str | None = None) -> tuple[bool, str]:
    try:
        proc = subprocess.run(
            [str(item) for item in args],
            input=input_text,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        output = ((proc.stdout or "") + (("\n" + proc.stderr) if proc.stderr else "")).strip()
        return proc.returncode == 0, output[:12000]
    except Exception as exc:
        return False, str(exc)


def _router_uci_get(key: str, default: str = "") -> str:
    ok, output = _router_run(["uci", "-q", "get", key], timeout=5)
    return output.splitlines()[0].strip() if ok and output else default


def _router_uci_show(package: str) -> dict[str, str]:
    ok, output = _router_run(["uci", "-q", "show", package], timeout=8)
    result: dict[str, str] = {}
    if not ok:
        return result
    for line in output.splitlines():
        if "=" not in line:
            continue
        key, value = line.split("=", 1)
        value = value.strip()
        if len(value) >= 2 and value[0] == value[-1] == "'":
            value = value[1:-1].replace("'\\''", "'")
        result[key.strip()] = value
    return result


def _router_bool(value, default: bool = False) -> bool:
    if isinstance(value, bool):
        return value
    if value is None:
        return default
    return str(value).strip().lower() in {"1", "true", "yes", "on", "enabled"}


def _router_int(value, default: int, minimum: int, maximum: int) -> int:
    try:
        parsed = int(value)
    except (TypeError, ValueError):
        parsed = default
    return max(minimum, min(maximum, parsed))


def _router_secret_placeholder(value: str) -> dict:
    return {"configured": bool(value), "value": ""}


def _router_interface_status(name: str) -> dict:
    ok, output = _router_run(["ubus", "call", f"network.interface.{name}", "status"], timeout=6)
    if not ok:
        return {"up": False, "available": False}
    try:
        raw = json.loads(output)
    except Exception:
        return {"up": False, "available": True}
    addresses = []
    for item in raw.get("ipv4-address") or []:
        if isinstance(item, dict) and item.get("address"):
            addresses.append(f"{item['address']}/{item.get('mask', '')}".rstrip("/"))
    addresses6 = []
    for item in raw.get("ipv6-address") or []:
        if isinstance(item, dict) and item.get("address"):
            addresses6.append(f"{item['address']}/{item.get('mask', '')}".rstrip("/"))
    route = raw.get("route") or []
    gateways = [str(item.get("nexthop")) for item in route if isinstance(item, dict) and item.get("nexthop")]
    return {
        "up": bool(raw.get("up")),
        "available": bool(raw.get("available", True)),
        "device": str(raw.get("l3_device") or raw.get("device") or ""),
        "uptime": int(raw.get("uptime") or 0),
        "addresses": addresses,
        "addresses6": addresses6,
        "gateways": gateways,
        "dns": [str(item) for item in (raw.get("dns-server") or [])],
    }


def _router_parse_port_forwards(firewall: dict[str, str]) -> list[dict]:
    sections: dict[str, dict] = {}
    for key, value in firewall.items():
        if not key.startswith("firewall."):
            continue
        rest = key[len("firewall."):]
        section, dot, option = rest.partition(".")
        if not section.startswith("light_rid_pf_"):
            continue
        item = sections.setdefault(section, {"id": section[len("light_rid_pf_"):], "managed": True})
        if dot:
            item[option] = value
    result = []
    for section in sorted(sections):
        item = sections[section]
        result.append({
            "id": item.get("id", ""),
            "name": item.get("name", ""),
            "enabled": item.get("enabled", "1") != "0",
            "protocol": item.get("proto", "tcp"),
            "external_port": item.get("src_dport", ""),
            "internal_ip": item.get("dest_ip", ""),
            "internal_port": item.get("dest_port", ""),
            "source_ip": item.get("src_ip", ""),
        })
    return result


def _router_config_payload() -> dict:
    wireless = _router_uci_show("wireless")
    firewall = _router_uci_show("firewall")
    mode = "repeater" if _router_uci_get("wireless.light_rid_repeater.disabled", "1") != "1" else "wired"
    wan_proto = _router_uci_get("network.wan.proto", "dhcp")
    lan_ip = _router_uci_get("network.lan.ipaddr", "192.168.8.1")
    lan_mask = _router_uci_get("network.lan.netmask", "255.255.255.0")
    return {
        "mode": mode,
        "wan": {
            "protocol": wan_proto if wan_proto in {"dhcp", "static", "pppoe"} else "dhcp",
            "ipaddr": _router_uci_get("network.wan.ipaddr"),
            "netmask": _router_uci_get("network.wan.netmask", "255.255.255.0"),
            "gateway": _router_uci_get("network.wan.gateway"),
            "dns": _router_uci_get("network.wan.dns").split(),
            "username": _router_uci_get("network.wan.username"),
            "password": _router_secret_placeholder(_router_uci_get("network.wan.password")),
        },
        "lan": {
            "ipaddr": lan_ip,
            "netmask": lan_mask,
            "dhcp_enabled": _router_uci_get("dhcp.lan.ignore", "0") != "1",
            "dhcp_start": _router_int(_router_uci_get("dhcp.lan.start", "100"), 100, 1, 253),
            "dhcp_limit": _router_int(_router_uci_get("dhcp.lan.limit", "150"), 150, 1, 253),
            "lease_time": _router_uci_get("dhcp.lan.leasetime", "12h"),
            "dns": _router_uci_get("dhcp.@dnsmasq[0].server").split(),
        },
        "ap": {
            "enabled": _router_uci_get("wireless.default_radio0.disabled", "0") != "1",
            "ssid": wireless.get("wireless.default_radio0.ssid", ""),
            "password": _router_secret_placeholder(wireless.get("wireless.default_radio0.key", "")),
            "channel": _router_uci_get("wireless.radio0.channel", "36"),
            "htmode": _router_uci_get("wireless.radio0.htmode", "VHT80"),
            "txpower": _router_int(_router_uci_get("wireless.radio0.txpower", "20"), 20, 1, 20),
        },
        "repeater": {
            "ssid": wireless.get("wireless.light_rid_repeater.ssid", ""),
            "bssid": wireless.get("wireless.light_rid_repeater.bssid", ""),
            "encryption": wireless.get("wireless.light_rid_repeater.encryption", "psk2"),
            "password": _router_secret_placeholder(wireless.get("wireless.light_rid_repeater.key", "")),
        },
        "guest": {
            "enabled": _router_uci_get("wireless.guest5g.disabled", "1") != "1",
            "ssid": wireless.get("wireless.guest5g.ssid", ""),
            "password": _router_secret_placeholder(wireless.get("wireless.guest5g.key", "")),
            "ipaddr": _router_uci_get("network.guest.ipaddr", "192.168.9.1"),
            "netmask": _router_uci_get("network.guest.netmask", "255.255.255.0"),
            "dhcp_start": _router_int(_router_uci_get("dhcp.guest.start", "100"), 100, 1, 253),
            "dhcp_limit": _router_int(_router_uci_get("dhcp.guest.limit", "150"), 150, 1, 253),
            "lease_time": _router_uci_get("dhcp.guest.leasetime", "12h"),
        },
        "port_forwards": _router_parse_port_forwards(firewall),
        "remote_management": {
            "enabled": _router_uci_get("firewall.light_rid_wan_admin.enabled", "0") != "0",
            "light_rid_port": int(globals().get("HTTP_PORT", 4600) or 4600),
            "luci_port": 80,
            "encrypted": False,
        },
    }


def _router_tx_status() -> dict:
    with router_tx_lock:
        tx = dict(router_active_tx)
    if not tx:
        return {"pending": False}
    remaining = max(0, int(float(tx.get("deadline", 0)) - time.time()))
    if remaining <= 0:
        return {"pending": False}
    return {
        "pending": True,
        "id": tx.get("id"),
        "phase": tx.get("phase", "pending"),
        "deadline": tx.get("deadline"),
        "remaining_seconds": remaining,
        "new_url": tx.get("new_url", ""),
    }


def _router_status_payload() -> dict:
    capabilities = _router_capabilities()
    payload = {
        "ok": True,
        "capabilities": capabilities,
        "transaction": _router_tx_status(),
        "luci_url": "http://{}/cgi-bin/luci".format(_router_uci_get("network.lan.ipaddr", "192.168.8.1")),
    }
    if not capabilities["supported"]:
        payload["config"] = {}
        payload["runtime"] = {}
        return payload
    payload["config"] = _router_config_payload()
    payload["runtime"] = {
        "lan": _router_interface_status("lan"),
        "wan": _router_interface_status("wan"),
        "wwan": _router_interface_status("wwan"),
        "wan6": _router_interface_status("wan6"),
        "radio1": {"reserved": True, "interface": "ridmon", "channel": int(globals().get("current_channel", 0) or 0)},
    }
    return payload


def _router_valid_ipv4(value, label: str, errors: list[str], allow_empty: bool = False) -> str:
    text = str(value or "").strip()
    if not text and allow_empty:
        return ""
    try:
        return str(ipaddress.IPv4Address(text))
    except Exception:
        errors.append(f"{label} 不是有效的 IPv4 地址")
        return text


def _router_validate_config(payload: dict | None) -> tuple[dict, list[str]]:
    body = payload if isinstance(payload, dict) else {}
    errors: list[str] = []
    mode = str(body.get("mode") or "wired").strip().lower()
    if mode not in {"wired", "repeater"}:
        errors.append("上联模式必须是 wired 或 repeater")
        mode = "wired"

    wan_raw = body.get("wan") if isinstance(body.get("wan"), dict) else {}
    protocol = str(wan_raw.get("protocol") or "dhcp").lower()
    if protocol not in {"dhcp", "static", "pppoe"}:
        errors.append("WAN 协议无效")
        protocol = "dhcp"
    dns_raw = wan_raw.get("dns") if isinstance(wan_raw.get("dns"), list) else []
    wan = {
        "protocol": protocol,
        "ipaddr": str(wan_raw.get("ipaddr") or "").strip(),
        "netmask": str(wan_raw.get("netmask") or "255.255.255.0").strip(),
        "gateway": str(wan_raw.get("gateway") or "").strip(),
        "dns": [str(item).strip() for item in dns_raw if str(item).strip()][:4],
        "username": str(wan_raw.get("username") or "").strip(),
        "password": str(wan_raw.get("password") or ""),
    }
    if protocol == "static":
        wan["ipaddr"] = _router_valid_ipv4(wan["ipaddr"], "WAN 地址", errors)
        wan["gateway"] = _router_valid_ipv4(wan["gateway"], "WAN 网关", errors)
        wan["netmask"] = _router_valid_ipv4(wan["netmask"], "WAN 掩码", errors)
    if protocol == "pppoe" and not wan["username"]:
        errors.append("PPPoE 用户名不能为空")
    for value in wan["dns"]:
        _router_valid_ipv4(value, "WAN DNS", errors)

    lan_raw = body.get("lan") if isinstance(body.get("lan"), dict) else {}
    lan_dns_raw = lan_raw.get("dns") if isinstance(lan_raw.get("dns"), list) else []
    lan = {
        "ipaddr": _router_valid_ipv4(lan_raw.get("ipaddr") or "192.168.8.1", "LAN 地址", errors),
        "netmask": _router_valid_ipv4(lan_raw.get("netmask") or "255.255.255.0", "LAN 掩码", errors),
        "dhcp_enabled": _router_bool(lan_raw.get("dhcp_enabled"), True),
        "dhcp_start": _router_int(lan_raw.get("dhcp_start"), 100, 1, 253),
        "dhcp_limit": _router_int(lan_raw.get("dhcp_limit"), 150, 1, 253),
        "lease_time": str(lan_raw.get("lease_time") or "12h").strip(),
        "dns": [str(item).strip() for item in lan_dns_raw if str(item).strip()][:4],
    }
    if not re.fullmatch(r"[1-9][0-9]*[mhd]", lan["lease_time"]):
        errors.append("LAN 租期格式应类似 30m、12h 或 2d")
    for value in lan["dns"]:
        _router_valid_ipv4(value, "LAN DNS", errors)

    ap_raw = body.get("ap") if isinstance(body.get("ap"), dict) else {}
    channel = _router_int(ap_raw.get("channel"), 36, 1, 196)
    htmode = str(ap_raw.get("htmode") or "VHT80").upper()
    ap = {
        "enabled": _router_bool(ap_raw.get("enabled"), True),
        "ssid": str(ap_raw.get("ssid") or "").strip(),
        "password": str(ap_raw.get("password") or ""),
        "channel": channel,
        "htmode": htmode,
        "txpower": _router_int(ap_raw.get("txpower"), 20, 1, 20),
    }
    if ap["enabled"] and not (1 <= len(ap["ssid"].encode("utf-8")) <= 32):
        errors.append("主 AP SSID 必须为 1 到 32 字节")
    if ap["password"] and not (8 <= len(ap["password"]) <= 63):
        errors.append("主 AP 密码必须为 8 到 63 个字符")
    if channel not in ROUTER_SAFE_CHANNELS:
        errors.append("5GHz 信道不在支持的非 DFS 列表中")
    if htmode not in ROUTER_HTMODES:
        errors.append("5GHz 带宽无效")
    if channel == 165 and htmode != "VHT20":
        errors.append("信道 165 只能使用 VHT20")

    repeater_raw = body.get("repeater") if isinstance(body.get("repeater"), dict) else {}
    encryption = str(repeater_raw.get("encryption") or "psk2").lower()
    repeater = {
        "ssid": str(repeater_raw.get("ssid") or "").strip(),
        "bssid": str(repeater_raw.get("bssid") or "").strip().upper(),
        "encryption": encryption,
        "password": str(repeater_raw.get("password") or ""),
    }
    if encryption not in ROUTER_UPLINK_ENCRYPTIONS:
        errors.append("中继加密类型不受支持")
    if mode == "repeater" and not repeater["ssid"]:
        errors.append("无线中继必须选择上游 SSID")
    if repeater["password"] and not (8 <= len(repeater["password"]) <= 63):
        errors.append("中继密码必须为 8 到 63 个字符")
    if repeater["bssid"] and not re.fullmatch(r"(?:[0-9A-F]{2}:){5}[0-9A-F]{2}", repeater["bssid"]):
        errors.append("中继 BSSID 格式无效")

    guest_raw = body.get("guest") if isinstance(body.get("guest"), dict) else {}
    guest = {
        "enabled": _router_bool(guest_raw.get("enabled"), False),
        "ssid": str(guest_raw.get("ssid") or "").strip(),
        "password": str(guest_raw.get("password") or ""),
        "ipaddr": _router_valid_ipv4(guest_raw.get("ipaddr") or "192.168.9.1", "访客网地址", errors),
        "netmask": _router_valid_ipv4(guest_raw.get("netmask") or "255.255.255.0", "访客网掩码", errors),
        "dhcp_start": _router_int(guest_raw.get("dhcp_start"), 100, 1, 253),
        "dhcp_limit": _router_int(guest_raw.get("dhcp_limit"), 150, 1, 253),
        "lease_time": str(guest_raw.get("lease_time") or "12h").strip(),
    }
    if guest["enabled"] and not (1 <= len(guest["ssid"].encode("utf-8")) <= 32):
        errors.append("访客 SSID 必须为 1 到 32 字节")
    if guest["password"] and not (8 <= len(guest["password"]) <= 63):
        errors.append("访客密码必须为 8 到 63 个字符")
    if not re.fullmatch(r"[1-9][0-9]*[mhd]", guest["lease_time"]):
        errors.append("访客租期格式应类似 30m、12h 或 2d")
    try:
        lan_network = ipaddress.IPv4Network((lan["ipaddr"], lan["netmask"]), strict=False)
        guest_network = ipaddress.IPv4Network((guest["ipaddr"], guest["netmask"]), strict=False)
        if lan["dhcp_start"] + lan["dhcp_limit"] > max(1, lan_network.num_addresses - 1):
            errors.append("LAN DHCP 地址池超出当前子网")
        if guest["dhcp_start"] + guest["dhcp_limit"] > max(1, guest_network.num_addresses - 1):
            errors.append("访客 DHCP 地址池超出当前子网")
        if lan_network.overlaps(guest_network):
            errors.append("LAN 与访客网段不能重叠")
        if protocol == "static":
            wan_network = ipaddress.IPv4Network((wan["ipaddr"], wan["netmask"]), strict=False)
            if ipaddress.IPv4Address(wan["gateway"]) not in wan_network:
                errors.append("静态 WAN 网关必须位于 WAN 子网内")
            if wan_network.overlaps(lan_network) or wan_network.overlaps(guest_network):
                errors.append("静态 WAN 网段不能与 LAN 或访客网重叠")
    except Exception:
        pass

    forwards_raw = body.get("port_forwards") if isinstance(body.get("port_forwards"), list) else []
    forwards = []
    seen_ports: set[tuple[str, int]] = set()
    for index, raw in enumerate(forwards_raw[:64]):
        if not isinstance(raw, dict):
            continue
        proto = str(raw.get("protocol") or "tcp").lower()
        if proto not in {"tcp", "udp", "tcp udp"}:
            errors.append(f"端口转发 #{index + 1} 协议无效")
            proto = "tcp"
        external = _router_int(raw.get("external_port"), 0, 0, 65535)
        internal = _router_int(raw.get("internal_port"), external, 0, 65535)
        internal_ip = _router_valid_ipv4(raw.get("internal_ip"), f"端口转发 #{index + 1} 内部地址", errors)
        source_ip = str(raw.get("source_ip") or "").strip()
        if source_ip:
            try:
                source_ip = str(ipaddress.ip_network(source_ip, strict=False))
            except Exception:
                errors.append(f"端口转发 #{index + 1} 来源地址无效")
        if not external or not internal:
            errors.append(f"端口转发 #{index + 1} 端口必须为 1 到 65535")
        try:
            if ipaddress.IPv4Address(internal_ip) not in ipaddress.IPv4Network((lan["ipaddr"], lan["netmask"]), strict=False):
                errors.append(f"端口转发 #{index + 1} 内部地址必须位于 LAN 子网")
        except Exception:
            pass
        for part in proto.split():
            key = (part, external)
            if key in seen_ports:
                errors.append(f"外部 {part.upper()} 端口 {external} 重复")
            seen_ports.add(key)
        forwards.append({
            "id": re.sub(r"[^a-zA-Z0-9_]", "", str(raw.get("id") or index + 1))[:24] or str(index + 1),
            "name": str(raw.get("name") or f"转发 {index + 1}")[:48],
            "enabled": _router_bool(raw.get("enabled"), True),
            "protocol": proto,
            "external_port": external,
            "internal_ip": internal_ip,
            "internal_port": internal,
            "source_ip": source_ip,
        })

    remote_raw = body.get("remote_management") if isinstance(body.get("remote_management"), dict) else {}
    normalized = {
        "mode": mode,
        "wan": wan,
        "lan": lan,
        "ap": ap,
        "repeater": repeater,
        "guest": guest,
        "port_forwards": forwards,
        "remote_management": {"enabled": _router_bool(remote_raw.get("enabled"), False)},
    }
    return normalized, errors


def _router_uci_set(key: str, value) -> tuple[bool, str]:
    return _router_run(["uci", "set", f"{key}={value}"], timeout=6)


def _router_uci_delete(key: str) -> None:
    _router_run(["uci", "-q", "delete", key], timeout=6)


def _router_set_secret(key: str, value: str) -> tuple[bool, str]:
    if not value:
        return True, "preserved"
    return _router_uci_set(key, value)


def _router_apply_uci(config: dict) -> tuple[bool, str]:
    steps: list[tuple[str, object]] = []
    def setv(key, value):
        steps.append((key, value))

    mode = config["mode"]
    wan = config["wan"]
    lan = config["lan"]
    ap = config["ap"]
    repeater = config["repeater"]
    guest = config["guest"]

    setv("network.wan.disabled", "1" if mode == "repeater" else "0")
    setv("network.wan.proto", wan["protocol"])
    for option in ("ipaddr", "netmask", "gateway", "dns"):
        if wan["protocol"] == "static" and option in {"ipaddr", "netmask", "gateway", "dns"}:
            setv(f"network.wan.{option}", " ".join(wan[option]) if option == "dns" else wan[option])
        elif wan["protocol"] == "pppoe" and option == "username":
            setv("network.wan.username", wan["username"])
        else:
            _router_uci_delete(f"network.wan.{option}")
    if wan["protocol"] == "pppoe":
        setv("network.wan.username", wan["username"])
        ok, msg = _router_set_secret("network.wan.password", wan["password"])
        if not ok:
            return False, msg
    else:
        _router_uci_delete("network.wan.username")
        _router_uci_delete("network.wan.password")

    setv("network.lan.ipaddr", lan["ipaddr"])
    setv("network.lan.netmask", lan["netmask"])
    setv("dhcp.lan.ignore", "0" if lan["dhcp_enabled"] else "1")
    setv("dhcp.lan.start", lan["dhcp_start"])
    setv("dhcp.lan.limit", lan["dhcp_limit"])
    setv("dhcp.lan.leasetime", lan["lease_time"])
    if lan["dns"]:
        setv("dhcp.@dnsmasq[0].server", " ".join(lan["dns"]))
    else:
        _router_uci_delete("dhcp.@dnsmasq[0].server")

    setv("wireless.radio0.channel", "auto" if mode == "repeater" else ap["channel"])
    setv("wireless.radio0.htmode", ap["htmode"])
    setv("wireless.radio0.txpower", ap["txpower"])
    setv("wireless.default_radio0.device", "radio0")
    setv("wireless.default_radio0.network", "lan")
    setv("wireless.default_radio0.mode", "ap")
    setv("wireless.default_radio0.encryption", "psk2")
    setv("wireless.default_radio0.ssid", ap["ssid"])
    setv("wireless.default_radio0.disabled", "0" if ap["enabled"] else "1")
    ok, msg = _router_set_secret("wireless.default_radio0.key", ap["password"])
    if not ok:
        return False, msg

    setv("network.wwan", "interface")
    setv("network.wwan.proto", "dhcp")
    setv("network.wwan.disabled", "0" if mode == "repeater" else "1")
    setv("wireless.light_rid_repeater", "wifi-iface")
    setv("wireless.light_rid_repeater.device", "radio0")
    setv("wireless.light_rid_repeater.network", "wwan")
    setv("wireless.light_rid_repeater.mode", "sta")
    setv("wireless.light_rid_repeater.ssid", repeater["ssid"])
    setv("wireless.light_rid_repeater.encryption", repeater["encryption"])
    setv("wireless.light_rid_repeater.disabled", "0" if mode == "repeater" else "1")
    if repeater["bssid"]:
        setv("wireless.light_rid_repeater.bssid", repeater["bssid"])
    else:
        _router_uci_delete("wireless.light_rid_repeater.bssid")
    ok, msg = _router_set_secret("wireless.light_rid_repeater.key", repeater["password"])
    if not ok:
        return False, msg

    setv("network.guest", "interface")
    setv("network.guest.type", "bridge")
    setv("network.guest.proto", "static")
    setv("network.guest.ipaddr", guest["ipaddr"])
    setv("network.guest.netmask", guest["netmask"])
    setv("dhcp.guest", "dhcp")
    setv("dhcp.guest.interface", "guest")
    setv("dhcp.guest.start", guest["dhcp_start"])
    setv("dhcp.guest.limit", guest["dhcp_limit"])
    setv("dhcp.guest.leasetime", guest["lease_time"])
    setv("dhcp.guest.ignore", "0" if guest["enabled"] else "1")
    setv("wireless.guest5g.device", "radio0")
    setv("wireless.guest5g.network", "guest")
    setv("wireless.guest5g.mode", "ap")
    setv("wireless.guest5g.encryption", "psk2")
    setv("wireless.guest5g.ssid", guest["ssid"])
    setv("wireless.guest5g.disabled", "0" if guest["enabled"] else "1")
    ok, msg = _router_set_secret("wireless.guest5g.key", guest["password"])
    if not ok:
        return False, msg

    setv("firewall.guestzone", "zone")
    setv("firewall.guestzone.name", "guestzone")
    setv("firewall.guestzone.network", "guest")
    setv("firewall.guestzone.input", "REJECT")
    setv("firewall.guestzone.output", "ACCEPT")
    setv("firewall.guestzone.forward", "REJECT")
    setv("firewall.guestzone_fwd", "forwarding")
    setv("firewall.guestzone_fwd.src", "guestzone")
    setv("firewall.guestzone_fwd.dest", "wan")
    for suffix, port in (("dhcp", "67-68"), ("dns", "53")):
        section = f"firewall.guestzone_{suffix}"
        setv(section, "rule")
        setv(f"{section}.src", "guestzone")
        setv(f"{section}.proto", "udp" if suffix == "dhcp" else "tcp udp")
        setv(f"{section}.dest_port", port)
        setv(f"{section}.target", "ACCEPT")
        setv(f"{section}.enabled", "1" if guest["enabled"] else "0")

    firewall = _router_uci_show("firewall")
    for key in list(firewall):
        section = key[len("firewall."):].split(".", 1)[0] if key.startswith("firewall.") else ""
        if section.startswith("light_rid_pf_"):
            _router_uci_delete(f"firewall.{section}")
    for index, item in enumerate(config["port_forwards"], 1):
        section = f"firewall.light_rid_pf_{index}"
        setv(section, "redirect")
        setv(f"{section}.name", item["name"])
        setv(f"{section}.src", "wan")
        setv(f"{section}.dest", "lan")
        setv(f"{section}.proto", item["protocol"])
        setv(f"{section}.src_dport", item["external_port"])
        setv(f"{section}.dest_ip", item["internal_ip"])
        setv(f"{section}.dest_port", item["internal_port"])
        setv(f"{section}.target", "DNAT")
        setv(f"{section}.enabled", "1" if item["enabled"] else "0")
        if item["source_ip"]:
            setv(f"{section}.src_ip", item["source_ip"])

    remote = config["remote_management"]["enabled"]
    setv("firewall.light_rid_wan_admin", "rule")
    setv("firewall.light_rid_wan_admin.name", "Light RID WAN administration")
    setv("firewall.light_rid_wan_admin.src", "wan")
    setv("firewall.light_rid_wan_admin.proto", "tcp")
    setv("firewall.light_rid_wan_admin.dest_port", f"80 {int(globals().get('HTTP_PORT', 4600) or 4600)}")
    setv("firewall.light_rid_wan_admin.target", "ACCEPT")
    setv("firewall.light_rid_wan_admin.enabled", "1" if remote else "0")
    setv("uhttpd.main.redirect_https", "0")

    for key, value in steps:
        ok, message = _router_uci_set(key, value)
        if not ok:
            return False, f"设置 {key} 失败: {message}"
    firewall_after = _router_uci_show("firewall")
    wan_zone = ""
    for key, value in firewall_after.items():
        if key.endswith(".name") and value == "wan":
            wan_zone = key.rsplit(".", 1)[0]
            break
    if wan_zone:
        _router_run(["uci", "-q", "del_list", f"{wan_zone}.network=wwan"], timeout=6)
        ok, message = _router_run(["uci", "add_list", f"{wan_zone}.network=wwan"], timeout=6)
        if not ok:
            return False, f"无法将无线中继加入 WAN 防火墙区域: {message}"
    for package in ROUTER_CONFIG_FILES:
        ok, message = _router_run(["uci", "commit", package], timeout=10)
        if not ok:
            return False, f"提交 {package} 失败: {message}"
    return True, ""


def _router_backup_config(directory: Path) -> tuple[bool, str]:
    try:
        directory.mkdir(parents=True, exist_ok=False)
        os.chmod(directory, 0o700)
        for name in ROUTER_CONFIG_FILES:
            source = Path("/etc/config") / name
            if source.is_file():
                shutil.copy2(source, directory / name)
        return True, ""
    except Exception as exc:
        return False, str(exc)


def _router_reload_services(mode: str = "wired") -> list[dict]:
    commands = [
        ["wifi", "reload", "radio0"],
        ["ifup", "lan"],
        ["ifup", "wwan" if mode == "repeater" else "wan"],
        ["ifdown", "wan" if mode == "repeater" else "wwan"],
        ["/etc/init.d/dnsmasq", "restart"],
        ["/etc/init.d/firewall", "reload"],
        ["/etc/init.d/uhttpd", "reload"],
    ]
    results = []
    for command in commands:
        ok, output = _router_run(command, timeout=30)
        results.append({"command": " ".join(command), "ok": ok, "output": output[:600]})
    return results


def _router_write_rollback_script(tx_dir: Path, tx_id: str, mode: str) -> Path:
    script = tx_dir / "rollback.sh"
    files = " ".join(ROUTER_CONFIG_FILES)
    content = f"""#!/bin/sh
sleep {ROUTER_ROLLBACK_SECONDS}
[ -f {shlex.quote(str(tx_dir / 'confirmed'))} ] && exit 0
for name in {files}; do
    [ -f {shlex.quote(str(tx_dir))}/$name ] && cp -f {shlex.quote(str(tx_dir))}/$name /etc/config/$name
done
uci revert >/dev/null 2>&1 || true
wifi reload radio0 >/dev/null 2>&1 || true
ifup lan >/dev/null 2>&1 || true
ifup wan >/dev/null 2>&1 || true
ifdown wwan >/dev/null 2>&1 || true
/etc/init.d/dnsmasq restart >/dev/null 2>&1 || true
/etc/init.d/firewall reload >/dev/null 2>&1 || true
/etc/init.d/uhttpd reload >/dev/null 2>&1 || true
printf '%s\n' rolled-back > {shlex.quote(str(tx_dir / 'result'))}
"""
    script.write_text(content, encoding="utf-8")
    os.chmod(script, 0o700)
    return script


def _router_apply_worker(tx_id: str, normalized: dict) -> None:
    time.sleep(0.8)
    with router_tx_lock:
        if str(router_active_tx.get("id") or "") != tx_id:
            return
        tx_dir = Path(str(router_active_tx.get("dir") or ""))
    if (tx_dir / "confirmed").exists():
        return
    ok, message = _router_apply_uci(normalized)
    if not ok:
        _router_restore_transaction(tx_id)
        try:
            Path(ROUTER_TX_ROOT, tx_id, "error").write_text(message + "\n", encoding="utf-8")
        except OSError:
            pass
        return
    reload_steps = _router_reload_services(normalized["mode"])
    critical_failed = [step for step in reload_steps if not step["ok"] and not step["command"].startswith("ifdown ")]
    if critical_failed:
        _router_restore_transaction(tx_id)
        try:
            Path(ROUTER_TX_ROOT, tx_id, "error").write_text("OpenWrt service reload failed\n", encoding="utf-8")
        except OSError:
            pass
        return
    with router_tx_lock:
        if str(router_active_tx.get("id") or "") == tx_id:
            router_active_tx["phase"] = "applied"
            router_active_tx["reload"] = reload_steps


def _router_apply_payload(payload: dict | None) -> tuple[dict, int]:
    capabilities = _router_capabilities()
    if not capabilities["supported"]:
        return {"ok": False, "error": "当前设备不是受支持的 GL-AR750S OpenWrt 环境"}, 409
    normalized, errors = _router_validate_config(payload)
    if normalized["ap"]["enabled"] and not normalized["ap"]["password"] and not _router_uci_get("wireless.default_radio0.key"):
        errors.append("主 AP 尚未配置密码")
    if normalized["guest"]["enabled"] and not normalized["guest"]["password"] and not _router_uci_get("wireless.guest5g.key"):
        errors.append("访客 AP 尚未配置密码")
    if normalized["mode"] == "repeater" and normalized["repeater"]["encryption"] != "none" and not normalized["repeater"]["password"] and not _router_uci_get("wireless.light_rid_repeater.key"):
        errors.append("无线中继尚未配置密码")
    if normalized["wan"]["protocol"] == "pppoe" and not normalized["wan"]["password"] and not _router_uci_get("network.wan.password"):
        errors.append("PPPoE 尚未配置密码")
    if errors:
        return {"ok": False, "error": "配置校验失败", "errors": errors}, 400
    with router_tx_lock:
        current = dict(router_active_tx)
        if current and float(current.get("deadline", 0)) > time.time():
            remaining = max(0, int(float(current.get("deadline", 0)) - time.time()))
            transaction = {"pending": True, "id": current.get("id"), "deadline": current.get("deadline"), "remaining_seconds": remaining, "new_url": current.get("new_url", "")}
            return {"ok": False, "error": "已有等待确认的网络事务", "transaction": transaction}, 409
    tx_id = secrets.token_hex(8)
    tx_dir = Path(ROUTER_TX_ROOT) / tx_id
    ok, message = _router_backup_config(tx_dir)
    if not ok:
        return {"ok": False, "error": f"无法备份 OpenWrt 配置: {message}"}, 500
    script = _router_write_rollback_script(tx_dir, tx_id, normalized["mode"])
    deadline = time.time() + ROUTER_ROLLBACK_SECONDS
    # The backend cannot know whether the browser reached this page through a
    # WAN address, reverse proxy, or forwarded port.  The browser preserves its
    # own current page URL instead of being redirected to the LAN address.
    new_url = ""
    try:
        subprocess.Popen(
            ["/bin/sh", str(script)],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
    except Exception as exc:
        shutil.rmtree(tx_dir, ignore_errors=True)
        return {"ok": False, "error": f"无法启动回滚守护进程: {exc}"}, 500
    with router_tx_lock:
        router_active_tx.clear()
        router_active_tx.update({"id": tx_id, "dir": str(tx_dir), "deadline": deadline, "new_url": new_url, "phase": "scheduled"})
    worker = Thread(target=_router_apply_worker, args=(tx_id, normalized), daemon=True, name=f"router-apply-{tx_id}")
    worker.start()
    return {
        "ok": True,
        "transaction": _router_tx_status(),
        "scheduled": True,
        "warning": "必须在 60 秒内从当前页面确认，否则配置会自动恢复。",
    }, 202


def _router_confirm_transaction(tx_id: str) -> tuple[dict, int]:
    with router_tx_lock:
        current = dict(router_active_tx)
    if not current or str(current.get("id")) != str(tx_id or ""):
        return {"ok": False, "error": "没有匹配的待确认事务"}, 404
    if float(current.get("deadline", 0)) <= time.time():
        return {"ok": False, "error": "确认期限已过，配置正在回滚"}, 409
    if current.get("phase") != "applied":
        return {"ok": False, "error": "配置仍在应用，请稍后确认"}, 409
    try:
        Path(str(current["dir"]), "confirmed").write_text("confirmed\n", encoding="utf-8")
        Path(str(current["dir"]), "result").write_text("confirmed\n", encoding="utf-8")
    except Exception as exc:
        return {"ok": False, "error": str(exc)}, 500
    with router_tx_lock:
        router_active_tx.clear()
    return {"ok": True, "confirmed": True}, 200


def _router_restore_files(directory: Path) -> tuple[bool, str]:
    try:
        for name in ROUTER_CONFIG_FILES:
            source = directory / name
            if source.is_file():
                shutil.copy2(source, Path("/etc/config") / name)
        _router_reload_services("wired")
        return True, ""
    except Exception as exc:
        return False, str(exc)


def _router_restore_transaction(tx_id: str) -> tuple[dict, int]:
    if not re.fullmatch(r"[0-9a-f]{16}", str(tx_id or "")):
        return {"ok": False, "error": "网络事务 ID 无效"}, 400
    with router_tx_lock:
        current = dict(router_active_tx)
    directory = Path(str(current.get("dir") or (Path(ROUTER_TX_ROOT) / str(tx_id))))
    if not directory.is_dir() or (current and str(current.get("id")) != str(tx_id or "")):
        return {"ok": False, "error": "没有匹配的网络事务"}, 404
    try:
        (directory / "confirmed").write_text("manual rollback\n", encoding="utf-8")
    except OSError:
        pass
    ok, message = _router_restore_files(directory)
    if ok:
        with router_tx_lock:
            router_active_tx.clear()
        return {"ok": True, "rolled_back": True}, 200
    return {"ok": False, "error": message}, 500


def _router_reset_original() -> tuple[dict, int]:
    directory = Path(ROUTER_ORIGINAL_ROOT)
    if not directory.is_dir():
        return {"ok": False, "error": "首次安装前的原厂网络备份不存在"}, 404
    manifest = directory / "manifest.sha256"
    if not manifest.is_file():
        return {"ok": False, "error": "原厂网络备份校验清单不存在"}, 409
    try:
        expected = {}
        for line in manifest.read_text(encoding="utf-8").splitlines():
            digest, name = line.split(None, 1)
            expected[name.lstrip(" *")] = digest.lower()
        for name in ROUTER_CONFIG_FILES:
            data = (directory / name).read_bytes()
            if expected.get(name) != hashlib.sha256(data).hexdigest():
                return {"ok": False, "error": f"原厂网络备份校验失败: {name}"}, 409
    except Exception as exc:
        return {"ok": False, "error": f"无法校验原厂网络备份: {exc}"}, 409
    ok, message = _router_restore_files(directory)
    return ({"ok": True, "restored": True} if ok else {"ok": False, "error": message}, 200 if ok else 500)


def _router_wifi_scan_payload() -> tuple[dict, int]:
    capabilities = _router_capabilities()
    if not capabilities["supported"]:
        return {"ok": False, "error": "当前设备不支持 5GHz 扫描"}, 409
    ok, output = _router_run(["iwinfo", "radio0", "scan"], timeout=25)
    if not ok:
        ok, output = _router_run(["iwinfo", "wlan0", "scan"], timeout=25)
    if not ok:
        return {"ok": False, "error": output or "扫描失败"}, 500
    items = []
    current: dict | None = None
    for raw_line in output.splitlines():
        line = raw_line.strip()
        match = re.match(r"Cell \d+ - Address: ([0-9A-Fa-f:]{17})", line)
        if match:
            if current and current.get("ssid"):
                items.append(current)
            current = {"bssid": match.group(1).upper(), "ssid": "", "channel": 0, "signal": None, "encryption": "none"}
            continue
        if current is None:
            continue
        if line.startswith("ESSID:"):
            current["ssid"] = line.split(":", 1)[1].strip().strip('"')
        elif line.startswith("Channel:"):
            current["channel"] = _router_int(line.split(":", 1)[1].split()[0], 0, 0, 196)
        elif line.startswith("Signal:"):
            match = re.search(r"-?\d+", line)
            current["signal"] = int(match.group(0)) if match else None
        elif line.startswith("Encryption:"):
            label = line.split(":", 1)[1].strip().lower()
            if "sae" in label:
                current["encryption"] = "sae-mixed" if "psk" in label else "sae"
            elif "wpa" in label or "psk" in label:
                current["encryption"] = "psk2" if "wpa2" in label else "psk-mixed"
    if current and current.get("ssid"):
        items.append(current)
    items.sort(key=lambda item: item.get("signal") if item.get("signal") is not None else -999, reverse=True)
    return {"ok": True, "items": items[:80]}, 200
