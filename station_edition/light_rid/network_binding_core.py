from __future__ import annotations

# This chunk keeps NIC binding, hotspot, and lightweight DHCP support out of
# the larger web/runtime chunks while sharing their assembled namespace.

NETWORK_BINDING_ROLES = ("none", "scan", "web", "ap_web", "disabled", "idle")
NETWORK_BINDING_ROLE_LABELS = {
    "none": "None",
    "scan": "扫描",
    "web": "网页服务",
    "ap_web": "AP热点网页服务",
    "disabled": "禁用",
    "idle": "闲置",
}
AP_WEB_ADDRESS_DEFAULT = "172.16.0.1"
AP_WEB_CIDR_DEFAULT = "172.16.0.1/24"
AP_WEB_DHCP_START_DEFAULT = "172.16.0.20"
AP_WEB_DHCP_END_DEFAULT = "172.16.0.240"
AP_WEB_HTTP_PORT_DEFAULT = 80

NETWORK_BINDINGS_CFG: dict = {
    "items": [],
    "ap": {
        "ssid": "LightRID-HotSpot",
        "password": "",
        "channel": 6,
        "address": AP_WEB_ADDRESS_DEFAULT,
        "cidr": AP_WEB_CIDR_DEFAULT,
        "dhcp_start": AP_WEB_DHCP_START_DEFAULT,
        "dhcp_end": AP_WEB_DHCP_END_DEFAULT,
        "http_port": AP_WEB_HTTP_PORT_DEFAULT,
        "internet_enabled": False,
        "uplink_iface": "",
    },
}
network_binding_lock = Lock()
network_binding_runtime: dict = {
    "http_servers": {},
    "dhcp_threads": {},
    "dns_threads": {},
    "hostapd": {},
    "last_apply": {},
}


def _network_role_key(value: str | None) -> str:
    raw = str(value or "").strip().lower().replace("-", "_")
    alias = {
        "": "none",
        "null": "none",
        "none": "none",
        "scan": "scan",
        "scanner": "scan",
        "capture": "scan",
        "web": "web",
        "http": "web",
        "lan_web": "web",
        "ap": "ap_web",
        "apweb": "ap_web",
        "ap_web": "ap_web",
        "hotspot": "ap_web",
        "hotspot_web": "ap_web",
        "disabled": "disabled",
        "disable": "disabled",
        "down": "disabled",
        "idle": "idle",
        "unused": "idle",
    }
    return alias.get(raw, "none")


def _network_safe_iface_name(iface: str | None) -> str | None:
    name = str(iface or "").strip()
    if not name:
        return None
    if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,32}", name):
        return None
    return name


def _network_ap_defaults() -> dict:
    return dict(NETWORK_BINDINGS_CFG.get("ap") or {})


def _normalize_network_bindings_cfg(cfg: dict | None) -> dict:
    raw_root = cfg.get("network_bindings") if isinstance(cfg, dict) else {}
    raw_root = raw_root if isinstance(raw_root, dict) else {}
    raw_items = raw_root.get("items") if isinstance(raw_root.get("items"), list) else []
    preferred = _cfg_preferred_iface_from_cfg(cfg)
    seen: set[str] = set()
    items: list[dict] = []
    scan_seen = False
    for item in raw_items:
        if not isinstance(item, dict):
            continue
        safe_iface = _network_safe_iface_name(str(item.get("iface") or "").strip())
        if not safe_iface or safe_iface in seen:
            continue
        role = _network_role_key(item.get("role"))
        if role == "scan":
            scan_seen = True
        seen.add(safe_iface)
        items.append({"iface": safe_iface, "role": role})
    if preferred and preferred not in seen:
        items.insert(0, {"iface": preferred, "role": "scan"})
        scan_seen = True
    if preferred and not scan_seen:
        for item in items:
            if item.get("iface") == preferred:
                item["role"] = "scan"
                scan_seen = True
                break
    ap = _network_ap_defaults()
    raw_ap = raw_root.get("ap") if isinstance(raw_root.get("ap"), dict) else {}
    for k in ("ssid", "password", "address", "cidr", "dhcp_start", "dhcp_end"):
        if k in raw_ap:
            ap[k] = str(raw_ap.get(k) or "").strip()
    uplink = _network_safe_iface_name(raw_ap.get("uplink_iface")) if "uplink_iface" in raw_ap else None
    ap["uplink_iface"] = uplink or ""
    ap["internet_enabled"] = bool(raw_ap.get("internet_enabled"))
    try:
        ap["channel"] = max(1, min(196, int(raw_ap.get("channel") if "channel" in raw_ap else ap.get("channel", 6))))
    except Exception:
        ap["channel"] = 6
    try:
        ap["http_port"] = max(1, min(65535, int(raw_ap.get("http_port") if "http_port" in raw_ap else ap.get("http_port", AP_WEB_HTTP_PORT_DEFAULT))))
    except Exception:
        ap["http_port"] = AP_WEB_HTTP_PORT_DEFAULT
    if not ap.get("ssid"):
        ap["ssid"] = "LightRID-HotSpot"
    if not ap.get("address"):
        ap["address"] = AP_WEB_ADDRESS_DEFAULT
    if not ap.get("cidr"):
        ap["cidr"] = AP_WEB_CIDR_DEFAULT
    if not ap.get("dhcp_start"):
        ap["dhcp_start"] = AP_WEB_DHCP_START_DEFAULT
    if not ap.get("dhcp_end"):
        ap["dhcp_end"] = AP_WEB_DHCP_END_DEFAULT
    if not ap.get("uplink_iface"):
        ap["internet_enabled"] = False
    return {"items": items, "ap": ap}


def init_network_bindings_from_config(cfg: dict | None) -> None:
    global NETWORK_BINDINGS_CFG
    NETWORK_BINDINGS_CFG = _normalize_network_bindings_cfg(cfg)


def _network_binding_scan_iface(cfg: dict | None) -> str | None:
    norm = _normalize_network_bindings_cfg(cfg)
    for item in norm.get("items") or []:
        if item.get("role") == "scan" and item.get("iface"):
            return str(item.get("iface"))
    return _cfg_preferred_iface_from_cfg(cfg)


def _network_bindings_visual_payload(cfg: dict | None = None) -> dict:
    norm = _normalize_network_bindings_cfg(cfg if isinstance(cfg, dict) else APP_CONFIG)
    return {
        "items": list(norm.get("items") or []),
        "ap": dict(norm.get("ap") or {}),
        "roles": [
            {"key": key, "label": NETWORK_BINDING_ROLE_LABELS.get(key, key)}
            for key in NETWORK_BINDING_ROLES
        ],
        "runtime": _network_bindings_runtime_payload(),
    }


def _network_bindings_runtime_payload() -> dict:
    with network_binding_lock:
        http = {
            str(k): {"running": bool(v.get("running")), "error": str(v.get("error") or "")}
            for k, v in (network_binding_runtime.get("http_servers") or {}).items()
            if isinstance(v, dict)
        }
        dhcp = {
            str(k): {"running": bool(v.get("running")), "error": str(v.get("error") or "")}
            for k, v in (network_binding_runtime.get("dhcp_threads") or {}).items()
            if isinstance(v, dict)
        }
        dns = {
            str(k): {"running": bool(v.get("running")), "error": str(v.get("error") or "")}
            for k, v in (network_binding_runtime.get("dns_threads") or {}).items()
            if isinstance(v, dict)
        }
        hostapd = {
            str(k): {"running": bool(v.get("running")), "error": str(v.get("error") or ""), "pid": v.get("pid")}
            for k, v in (network_binding_runtime.get("hostapd") or {}).items()
            if isinstance(v, dict)
        }
        last_apply = dict(network_binding_runtime.get("last_apply") or {})
    return {"http": http, "dhcp": dhcp, "dns": dns, "hostapd": hostapd, "last_apply": last_apply}


def _network_bindings_status_payload() -> dict:
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else APP_CONFIG
    return {
        "ok": True,
        "interfaces": _iface_options_snapshot(),
        "bindings": _network_bindings_visual_payload(cfg),
        "selected_iface": _network_binding_scan_iface(cfg),
    }


def _network_bindings_apply_visual(cfg: dict, payload: dict | None) -> tuple[dict, str | None]:
    p = payload if isinstance(payload, dict) else {}
    norm = _normalize_network_bindings_cfg({"network_bindings": p, "basic": cfg.get("basic") if isinstance(cfg, dict) else {}})
    ifaces_seen: set[str] = set()
    scan_ifaces: list[str] = []
    for item in list(norm.get("items") or []):
        iface = str(item.get("iface") or "").strip()
        role = _network_role_key(item.get("role"))
        if not iface or iface in ifaces_seen:
            continue
        ifaces_seen.add(iface)
        if role == "scan":
            scan_ifaces.append(iface)
    if len(scan_ifaces) > 1:
        return cfg, "只能设置一张网卡为扫描"
    basic = cfg.setdefault("basic", {})
    if not isinstance(basic, dict):
        basic = {}
        cfg["basic"] = basic
    if scan_ifaces:
        basic["iface"] = scan_ifaces[0]
    elif basic.get("iface"):
        norm["items"].insert(0, {"iface": str(basic.get("iface")), "role": "scan"})
    cfg["network_bindings"] = norm
    return cfg, None


def _network_bindings_save_payload(body: dict | None) -> dict:
    if not APP_CONFIG_PATH:
        return {"ok": False, "error": "config path missing"}
    payload = body.get("network_bindings") if isinstance(body, dict) else None
    if not isinstance(payload, dict):
        payload = body if isinstance(body, dict) else {}
    cfg = load_app_config(APP_CONFIG_PATH)
    cfg, err = _network_bindings_apply_visual(cfg, payload)
    if err:
        return {"ok": False, "error": err}
    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="network-bindings")
    if not b_ok:
        return {"ok": False, "error": f"backup failed: {backup_path}"}
    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
    if not ok:
        return {"ok": False, "error": f"save failed: {msg}"}
    cfg_loaded = load_app_config(APP_CONFIG_PATH)
    r_ok, r_msg = reload_runtime_config(cfg_loaded)
    if not r_ok:
        return {"ok": False, "error": f"reload failed: {r_msg}", "backup_path": backup_path}
    return {"ok": True, "backup_path": backup_path, "reload_msg": r_msg, "bindings": _network_bindings_visual_payload(cfg_loaded)}


def _dhcp_ip_to_int(ip: str) -> int:
    return int(ipaddress.ip_address(str(ip)))


def _dhcp_int_to_ip(value: int) -> str:
    return str(ipaddress.ip_address(int(value)))


def _dhcp_option(code: int, data: bytes) -> bytes:
    raw = bytes(data or b"")
    return bytes([int(code) & 0xFF, len(raw) & 0xFF]) + raw


def _dhcp_parse_options(buf: bytes) -> dict:
    opts: dict[int, bytes] = {}
    i = 240
    data = bytes(buf or b"")
    while i < len(data):
        code = data[i]
        i += 1
        if code == 255:
            break
        if code == 0:
            continue
        if i >= len(data):
            break
        ln = data[i]
        i += 1
        opts[int(code)] = data[i:i + ln]
        i += ln
    return opts


def _dhcp_build_reply(req: bytes, msg_type: int, yiaddr: str, server_ip: str, lease_sec: int = 3600) -> bytes:
    xid = req[4:8]
    flags = req[10:12]
    chaddr = req[28:44]
    siaddr = socket.inet_aton(server_ip)
    pkt = bytearray(240)
    pkt[0] = 2
    pkt[1] = req[1] if len(req) > 1 else 1
    pkt[2] = req[2] if len(req) > 2 else 6
    pkt[3] = 0
    pkt[4:8] = xid
    pkt[10:12] = flags
    pkt[16:20] = socket.inet_aton(yiaddr)
    pkt[20:24] = siaddr
    pkt[28:44] = chaddr
    pkt[236:240] = b"\x63\x82\x53\x63"
    options = b"".join([
        _dhcp_option(53, bytes([msg_type])),
        _dhcp_option(54, siaddr),
        _dhcp_option(1, socket.inet_aton("255.255.255.0")),
        _dhcp_option(3, siaddr),
        _dhcp_option(6, siaddr),
        _dhcp_option(51, int(lease_sec).to_bytes(4, "big")),
        _dhcp_option(58, int(max(60, lease_sec // 2)).to_bytes(4, "big")),
        _dhcp_option(59, int(max(120, lease_sec * 7 // 8)).to_bytes(4, "big")),
        _dhcp_option(114, f"http://{server_ip}/".encode("ascii")),
        b"\xff",
    ])
    return bytes(pkt) + options


def _dhcp_mac_from_request(req: bytes) -> str:
    try:
        hlen = int(req[2])
        raw = bytes(req[28:28 + min(hlen, 6)])
        return ":".join(f"{b:02x}" for b in raw)
    except Exception:
        return ""


def _dhcp_requested_ip(opts: dict, req: bytes) -> str:
    raw = opts.get(50)
    if raw and len(raw) == 4:
        return socket.inet_ntoa(raw)
    if len(req) >= 16 and req[12:16] != b"\x00\x00\x00\x00":
        return socket.inet_ntoa(req[12:16])
    return ""


def _dhcp_server_loop(iface: str, ap: dict, state: dict) -> None:
    leases: dict[str, str] = {}
    start_i = _dhcp_ip_to_int(ap.get("dhcp_start") or AP_WEB_DHCP_START_DEFAULT)
    end_i = _dhcp_ip_to_int(ap.get("dhcp_end") or AP_WEB_DHCP_END_DEFAULT)
    server_ip = str(ap.get("address") or AP_WEB_ADDRESS_DEFAULT)
    sock = None
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        try:
            sock.setsockopt(socket.SOL_SOCKET, 25, str(iface).encode() + b"\x00")
        except Exception:
            pass
        sock.bind(("", 67))
        state["running"] = True
        state["error"] = ""
        next_i = start_i
        while True:
            req, _addr = sock.recvfrom(2048)
            if len(req) < 240 or req[236:240] != b"\x63\x82\x53\x63":
                continue
            opts = _dhcp_parse_options(req)
            msg = int(opts.get(53, b"\x00")[0])
            if msg not in (1, 3):
                continue
            mac = _dhcp_mac_from_request(req)
            if not mac:
                continue
            requested = _dhcp_requested_ip(opts, req)
            yiaddr = leases.get(mac) or ""
            if requested:
                try:
                    req_i = _dhcp_ip_to_int(requested)
                    if start_i <= req_i <= end_i:
                        yiaddr = requested
                except Exception:
                    pass
            if not yiaddr:
                for _ in range(max(1, end_i - start_i + 1)):
                    candidate = _dhcp_int_to_ip(next_i)
                    next_i = start_i if next_i >= end_i else next_i + 1
                    if candidate not in leases.values():
                        yiaddr = candidate
                        break
            if not yiaddr:
                continue
            leases[mac] = yiaddr
            reply_type = 2 if msg == 1 else 5
            reply = _dhcp_build_reply(req, reply_type, yiaddr, server_ip)
            sock.sendto(reply, ("255.255.255.255", 68))
    except Exception as e:
        state["running"] = False
        state["error"] = str(e)
        _log(f"[WARN] DHCP server failed on {iface}: {e}")
    finally:
        try:
            if sock:
                sock.close()
        except Exception:
            pass


def _start_dhcp_server(iface: str, ap: dict) -> None:
    with network_binding_lock:
        current = (network_binding_runtime.get("dhcp_threads") or {}).get(iface)
        if isinstance(current, dict) and current.get("running"):
            return
        state = {"running": False, "error": "", "thread": None}
        network_binding_runtime.setdefault("dhcp_threads", {})[iface] = state
    th = Thread(target=_dhcp_server_loop, args=(iface, dict(ap), state), daemon=True)
    state["thread"] = th
    th.start()


def _dns_question_end(data: bytes, offset: int = 12) -> int | None:
    i = int(offset)
    jumps = 0
    while i < len(data):
        ln = data[i]
        if ln & 0xC0 == 0xC0:
            if i + 1 >= len(data):
                return None
            i += 2
            break
        i += 1
        if ln == 0:
            break
        if i + ln > len(data):
            return None
        i += ln
        jumps += 1
        if jumps > 64:
            return None
    if i + 4 > len(data):
        return None
    return i + 4


def _dns_build_portal_reply(query: bytes, server_ip: str) -> bytes | None:
    data = bytes(query or b"")
    if len(data) < 12:
        return None
    qdcount = int.from_bytes(data[4:6], "big")
    if qdcount < 1:
        return None
    q_end = _dns_question_end(data, 12)
    if not q_end:
        return None
    qtype = int.from_bytes(data[q_end - 4:q_end - 2], "big")
    question = data[12:q_end]
    answer = b""
    ancount = 0
    if qtype in (1, 255):
        answer = (
            b"\xc0\x0c"
            + (1).to_bytes(2, "big")
            + (1).to_bytes(2, "big")
            + (30).to_bytes(4, "big")
            + (4).to_bytes(2, "big")
            + socket.inet_aton(server_ip)
        )
        ancount = 1
    header = (
        data[0:2]
        + (0x8180).to_bytes(2, "big")
        + (1).to_bytes(2, "big")
        + int(ancount).to_bytes(2, "big")
        + b"\x00\x00"
        + b"\x00\x00"
    )
    return header + question + answer


def _dns_server_loop(iface: str, ap: dict, state: dict) -> None:
    server_ip = str(ap.get("address") or AP_WEB_ADDRESS_DEFAULT)
    sock = None
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            sock.setsockopt(socket.SOL_SOCKET, 25, str(iface).encode() + b"\x00")
        except Exception:
            pass
        sock.bind((server_ip, 53))
        state["running"] = True
        state["error"] = ""
        _log(f"[INFO] AP DNS captive portal service started: {iface} -> {server_ip}:53")
        while True:
            req, addr = sock.recvfrom(2048)
            reply = _dns_build_portal_reply(req, server_ip)
            if reply:
                sock.sendto(reply, addr)
    except Exception as e:
        state["running"] = False
        state["error"] = str(e)
        _log(f"[WARN] AP DNS captive portal service failed on {iface}: {e}")
    finally:
        try:
            if sock:
                sock.close()
        except Exception:
            pass


def _start_dns_server(iface: str, ap: dict) -> None:
    with network_binding_lock:
        current = (network_binding_runtime.get("dns_threads") or {}).get(iface)
        if isinstance(current, dict) and current.get("running"):
            return
        state = {"running": False, "error": "", "thread": None}
        network_binding_runtime.setdefault("dns_threads", {})[iface] = state
    th = Thread(target=_dns_server_loop, args=(iface, dict(ap), state), daemon=True)
    state["thread"] = th
    th.start()


def _ap_internet_enabled(ap: dict) -> bool:
    return bool(ap.get("internet_enabled") and _network_safe_iface_name(ap.get("uplink_iface")))


def _ap_network_cidr(ap: dict) -> str:
    try:
        return str(ipaddress.ip_network(str(ap.get("cidr") or AP_WEB_CIDR_DEFAULT), strict=False))
    except Exception:
        return "172.16.0.0/24"


def _iptables_ensure_rule(args: list[str], *, privileged: bool = False,
                          sudo_password: str | None = None) -> tuple[bool, str, int]:
    cmd = [_command_path("iptables") or "iptables"] + [str(x) for x in args]
    check_cmd = cmd[:]
    try:
        check_cmd[check_cmd.index("-A")] = "-C"
    except ValueError:
        return False, "iptables rule must use -A", -1
    runner = _run_privileged if privileged else _run_program
    if privileged:
        ok, out, rc = runner(check_cmd, timeout=10, sudo_password=sudo_password)
    else:
        ok, out, rc = runner(check_cmd, timeout=10)
    if ok:
        return True, out, rc
    if privileged:
        return runner(cmd, timeout=10, sudo_password=sudo_password)
    return runner(cmd, timeout=10)


def _apply_ap_internet_sharing_steps(ap_iface: str, ap: dict, *,
                                     privileged: bool = False,
                                     sudo_password: str | None = None) -> list[dict]:
    steps: list[dict] = []
    uplink = _network_safe_iface_name(ap.get("uplink_iface"))
    if not _ap_internet_enabled(ap) or not uplink:
        return steps
    if uplink == ap_iface:
        steps.append({"label": "enable AP Internet sharing", "ok": False, "returncode": -1, "output": "uplink iface must differ from AP iface"})
        return steps
    iptables = _command_path("iptables")
    if not iptables:
        steps.append({"label": "enable AP Internet sharing", "ok": False, "returncode": -1, "output": "iptables not installed"})
        return steps

    def run_step(label: str, args: list[str]) -> bool:
        if privileged:
            ok, out, rc = _run_privileged(args, timeout=10, sudo_password=sudo_password)
        else:
            ok, out, rc = _run_program(args, timeout=10)
        steps.append({"label": label, "ok": ok, "returncode": rc, "output": out})
        return bool(ok)

    def ipt_step(label: str, args: list[str]) -> bool:
        ok, out, rc = _iptables_ensure_rule(args, privileged=privileged, sudo_password=sudo_password)
        steps.append({"label": label, "ok": ok, "returncode": rc, "output": out})
        return bool(ok)

    net = _ap_network_cidr(ap)
    run_step("enable IPv4 forwarding", ["sysctl", "-w", "net.ipv4.ip_forward=1"])
    ipt_step("NAT AP clients to uplink", ["-t", "nat", "-A", "POSTROUTING", "-s", net, "-o", uplink, "-j", "MASQUERADE"])
    ipt_step("allow AP to uplink forwarding", ["-A", "FORWARD", "-i", ap_iface, "-o", uplink, "-j", "ACCEPT"])
    ipt_step("allow uplink replies to AP", ["-A", "FORWARD", "-i", uplink, "-o", ap_iface, "-m", "conntrack", "--ctstate", "RELATED,ESTABLISHED", "-j", "ACCEPT"])
    return steps


def _stop_hostapd_process(proc) -> None:
    if proc is None:
        return
    try:
        proc.terminate()
        proc.wait(timeout=2)
        return
    except Exception:
        pass
    try:
        proc.kill()
    except Exception:
        pass


def _kill_hostapd_pid(pid: int) -> bool:
    if pid <= 1:
        return False
    try:
        os.kill(pid, 15)
        for _ in range(20):
            try:
                os.kill(pid, 0)
                time.sleep(0.05)
            except OSError:
                return True
        os.kill(pid, 9)
        return True
    except Exception:
        return False


def _stop_stale_hostapd(iface: str, cfg_path: str, pid_path: str) -> list[int]:
    stopped: list[int] = []
    try:
        raw = _sysfs_read_text(pid_path).strip() if os.path.exists(pid_path) else ""
        if raw.isdigit() and _kill_hostapd_pid(int(raw)):
            stopped.append(int(raw))
    except Exception:
        pass
    pgrep = _command_path("pgrep")
    if pgrep:
        ok, out, _rc = _run_program([pgrep, "-f", f"hostapd .*{re.escape(cfg_path)}"], timeout=5)
        if ok:
            for line in str(out or "").splitlines():
                raw = line.strip()
                if raw.isdigit():
                    pid = int(raw)
                    if pid not in stopped and _kill_hostapd_pid(pid):
                        stopped.append(pid)
    try:
        if os.path.exists(pid_path):
            os.unlink(pid_path)
    except Exception:
        pass
    return stopped


def _start_hostapd(iface: str, ap: dict) -> dict:
    hostapd = _command_path("hostapd")
    if not hostapd:
        return {"running": False, "error": "hostapd not installed", "pid": None}
    if not (_is_root_user() or _process_has_capabilities(("CAP_NET_ADMIN", "CAP_NET_RAW"))):
        return {"running": False, "error": "hostapd requires root or CAP_NET_ADMIN/CAP_NET_RAW", "pid": None}
    try:
        with network_binding_lock:
            old = (network_binding_runtime.get("hostapd") or {}).get(iface)
        old_proc = old.get("process") if isinstance(old, dict) else None
        _stop_hostapd_process(old_proc)
        cfg_path = os.path.join(tempfile.gettempdir(), f"light_rid_hostapd_{iface}.conf")
        log_path = os.path.join(tempfile.gettempdir(), f"light_rid_hostapd_{iface}.log")
        pid_path = os.path.join(tempfile.gettempdir(), f"light_rid_hostapd_{iface}.pid")
        ctrl_dir = os.path.join(tempfile.gettempdir(), f"light_rid_hostapd_ctrl_{iface}")
        stopped = _stop_stale_hostapd(iface, cfg_path, pid_path)
        try:
            os.makedirs(ctrl_dir, mode=0o770, exist_ok=True)
        except Exception:
            pass
        ssid = re.sub(r"[\r\n]+", "", str(ap.get("ssid") or "LightRID-HotSpot"))[:32] or "LightRID-HotSpot"
        channel = max(1, min(196, int(ap.get("channel") or 6)))
        password = str(ap.get("password") or "")
        lines = [
            f"interface={iface}",
            "driver=nl80211",
            f"ssid={ssid}",
            f"ctrl_interface={ctrl_dir}",
            "ctrl_interface_group=netdev",
            "country_code=CN",
            "ieee80211d=1",
            "wmm_enabled=1",
            "ieee80211n=1",
            "hw_mode=" + ("a" if channel > 14 else "g"),
            f"channel={channel}",
            "auth_algs=1",
            "ignore_broadcast_ssid=0",
        ]
        if password:
            if len(password) < 8:
                return {"running": False, "error": "AP password must be at least 8 characters", "pid": None}
            lines.extend(["wpa=2", f"wpa_passphrase={password}", "wpa_key_mgmt=WPA-PSK", "rsn_pairwise=CCMP"])
        with open(cfg_path, "w", encoding="utf-8") as f:
            f.write("\n".join(lines) + "\n")
        log_f = open(log_path, "wb")
        proc = subprocess.Popen([hostapd, cfg_path], stdout=log_f, stderr=log_f)
        time.sleep(1.2)
        if proc.poll() is not None:
            try:
                log_f.close()
            except Exception:
                pass
            err = _sysfs_read_text(log_path)[-1200:] if os.path.exists(log_path) else ""
            return {"running": False, "error": err or f"hostapd exited with code {proc.returncode}", "pid": None, "config": cfg_path, "log": log_path}
        err_log = _sysfs_read_text(log_path)[-1200:] if os.path.exists(log_path) else ""
        if "Interface initialization failed" in err_log or "Unable to setup interface" in err_log:
            _stop_hostapd_process(proc)
            return {"running": False, "error": err_log, "pid": None, "config": cfg_path, "log": log_path}
        state = {"running": True, "error": "", "pid": proc.pid, "process": proc, "config": cfg_path, "log": log_path, "ctrl": ctrl_dir}
        if stopped:
            state["stopped_stale_pids"] = stopped
        return state
    except Exception as e:
        return {"running": False, "error": str(e), "pid": None}


def _apply_network_bindings_os(cfg: dict, sudo_password: str | None = None) -> dict:
    norm = _normalize_network_bindings_cfg(cfg)
    steps: list[dict] = []
    ok_all = True
    ap = dict(norm.get("ap") or {})
    if not _is_linux_host():
        return {"ok": False, "error": "network binding apply is only supported on Linux", "steps": steps}
    if not (_is_root_user() or _sudo_available()):
        return {"ok": False, "error": "applying NIC roles requires root or sudo", "steps": steps}

    def step(label: str, args: list[str], optional: bool = False) -> bool:
        ok, out, rc = _run_privileged(args, timeout=20, sudo_password=sudo_password)
        steps.append({"label": label, "ok": ok, "returncode": rc, "output": out})
        return bool(ok or optional)

    for item in norm.get("items") or []:
        iface = str(item.get("iface") or "")
        role = _network_role_key(item.get("role"))
        if not iface:
            continue
        if role == "disabled":
            ok_all = step(f"disable {iface}", ["ip", "link", "set", iface, "down"]) and ok_all
        elif role == "ap_web":
            if _command_path("nmcli"):
                step(f"release {iface} from NetworkManager", ["nmcli", "device", "set", iface, "managed", "no"], optional=True)
            ok_all = step(f"stop {iface}", ["ip", "link", "set", iface, "down"]) and ok_all
            step(f"set {iface} AP type", ["iw", "dev", iface, "set", "type", "__ap"], optional=True)
            step(f"flush {iface} addresses", ["ip", "addr", "flush", "dev", iface], optional=True)
            ok_all = step(f"assign {iface} {ap.get('cidr')}", ["ip", "addr", "add", str(ap.get("cidr") or AP_WEB_CIDR_DEFAULT), "dev", iface]) and ok_all
            ok_all = step(f"start {iface}", ["ip", "link", "set", iface, "up"]) and ok_all
            hostapd_state = _start_hostapd(iface, ap)
            with network_binding_lock:
                network_binding_runtime.setdefault("hostapd", {})[iface] = hostapd_state
            if not hostapd_state.get("running"):
                ok_all = False
                steps.append({"label": f"start hostapd {iface}", "ok": False, "returncode": -1, "output": hostapd_state.get("error") or ""})
            if hostapd_state.get("running"):
                _start_dhcp_server(iface, ap)
                _start_dns_server(iface, ap)
                share_steps = _apply_ap_internet_sharing_steps(iface, ap, privileged=True, sudo_password=sudo_password)
                steps.extend(share_steps)
                if any(not bool(s.get("ok")) for s in share_steps):
                    ok_all = False
        elif role in ("web", "idle", "none"):
            step(f"ensure {iface} up", ["ip", "link", "set", iface, "up"], optional=True)
    with network_binding_lock:
        network_binding_runtime["last_apply"] = {
            "ok": bool(ok_all),
            "ts": time.time(),
            "steps": steps[-20:],
        }
    return {"ok": bool(ok_all), "steps": steps, "bindings": _network_bindings_visual_payload(cfg)}


def _network_bindings_apply_payload(body: dict | None) -> dict:
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else APP_CONFIG
    rsp = _apply_network_bindings_os(cfg, sudo_password=_sudo_password_from_body(body))
    rsp["runtime"] = _network_bindings_runtime_payload()
    if not rsp.get("ok") and not rsp.get("error"):
        rsp["error"] = "one or more network binding steps failed"
    return rsp


def start_bound_http_servers(server_cls, handler_cls) -> None:
    cfg = _normalize_network_bindings_cfg(APP_CONFIG)
    ap = dict(cfg.get("ap") or {})
    enabled = any(_network_role_key(item.get("role")) == "ap_web" for item in cfg.get("items") or [])
    if not enabled:
        return
    host = str(ap.get("address") or AP_WEB_ADDRESS_DEFAULT)
    port = int(ap.get("http_port") or AP_WEB_HTTP_PORT_DEFAULT)
    key = f"{host}:{port}"
    with network_binding_lock:
        current = (network_binding_runtime.get("http_servers") or {}).get(key)
        if isinstance(current, dict) and current.get("running"):
            return
    state = {"running": False, "error": "", "server": None}
    try:
        srv = server_cls((host, port), handler_cls)
        state.update({"running": True, "server": srv})
        with network_binding_lock:
            network_binding_runtime.setdefault("http_servers", {})[key] = state
        Thread(target=srv.serve_forever, daemon=True).start()
        _log(f"[INFO] AP HTTP service started: http://{host}:{port}/")
    except Exception as e:
        state["error"] = str(e)
        with network_binding_lock:
            network_binding_runtime.setdefault("http_servers", {})[key] = state
        _log(f"[WARN] AP HTTP service failed on {key}: {e}")


def start_network_binding_services() -> None:
    cfg = _normalize_network_bindings_cfg(APP_CONFIG)
    ap = dict(cfg.get("ap") or {})
    for item in cfg.get("items") or []:
        iface = str(item.get("iface") or "")
        if iface and _network_role_key(item.get("role")) == "ap_web":
            can_configure = _is_root_user() or _process_has_capabilities(("CAP_NET_ADMIN", "CAP_NET_RAW"))
            if can_configure:
                if _command_path("nmcli"):
                    _run_program(["nmcli", "device", "set", iface, "managed", "no"], timeout=10)
                for args in (
                    ["ip", "link", "set", iface, "down"],
                    ["iw", "dev", iface, "set", "type", "__ap"],
                    ["ip", "addr", "flush", "dev", iface],
                    ["ip", "addr", "add", str(ap.get("cidr") or AP_WEB_CIDR_DEFAULT), "dev", iface],
                    ["ip", "link", "set", iface, "up"],
                ):
                    _run_program(args, timeout=10)
                hostapd_state = _start_hostapd(iface, ap)
                with network_binding_lock:
                    network_binding_runtime.setdefault("hostapd", {})[iface] = hostapd_state
                if hostapd_state.get("running"):
                    _start_dhcp_server(iface, ap)
                    _start_dns_server(iface, ap)
                    share_steps = _apply_ap_internet_sharing_steps(iface, ap, privileged=False)
                    if share_steps and any(not bool(s.get("ok")) for s in share_steps):
                        bad = "; ".join(str(s.get("label") or "") + ": " + str(s.get("output") or "") for s in share_steps if not bool(s.get("ok")))
                        _log(f"[WARN] AP Internet sharing failed on {iface}: {bad}")
