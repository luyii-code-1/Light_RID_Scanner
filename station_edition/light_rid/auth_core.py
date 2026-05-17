def _api_token_enabled() -> bool:
    if _portable_edition_enabled():
        return False
    return bool(API_CFG.get("enabled")) and bool(_auth_enabled()) and _auth_hashes_present(AUTH_CFG) and _api_tokens_have_secret(API_CFG)

def _api_token_check_value(token: str | None) -> dict | None:
    if not _api_token_enabled():
        return None
    raw = str(token or "").strip()
    if not raw:
        return None
    for item in _normalize_api_tokens(API_CFG.get("tokens"), API_CFG.get("token") or "", API_CFG.get("token_hash") or ""):
        token_hash = str(item.get("token_hash") or "").strip()
        if token_hash and _verify_auth_secret(raw, token_hash) and bool(_sso_link_state(item).get("active")):
            return dict(item)
    return None

def _api_token_from_request(headers, query: dict | None = None) -> str:
    authz = str(headers.get("Authorization") or "").strip()
    if authz.lower().startswith("bearer "):
        return authz[7:].strip()
    token = str(headers.get("X-API-Token") or "").strip()
    if token:
        return token
    if isinstance(query, dict):
        try:
            arr = query.get("token") or [""]
            return str(arr[0] or "").strip()
        except Exception:
            return ""
    return ""

def _api_mark_token_used(token_id: str | None) -> bool:
    raw_id = str(token_id or "").strip()
    if not raw_id:
        return False
    changed = False
    now_wall = time.time()
    def _mark(tokens):
        nonlocal changed
        out = []
        for item in tokens:
            row = dict(item or {})
            if str(row.get("id") or "") == raw_id:
                row["used_count"] = int(row.get("used_count") or 0) + 1
                row["used_ts"] = now_wall
                changed = True
            out.append(row)
        return out
    ok, _msg, _tokens = _api_mutate_tokens(_mark, tag="api_token_use")
    return bool(ok and changed)

def _api_mutate_tokens(mutator, *, tag: str = "api_token") -> tuple[bool, str, list[dict]]:
    if not APP_CONFIG_PATH:
        return False, "config path missing", _api_tokens_public()
    try:
        with api_token_lock:
            cfg = load_app_config(APP_CONFIG_PATH)
            api = cfg.setdefault("api", {})
            if not isinstance(api, dict):
                api = {}
                cfg["api"] = api
            tokens = _normalize_api_tokens(api.get("tokens"), api.get("token") or "", api.get("token_hash") or "")
            api["tokens"] = _normalize_api_tokens(mutator(list(tokens)))
            first = api["tokens"][0] if api["tokens"] else {}
            api["token"] = str(first.get("token") or "")
            api["token_hash"] = str(first.get("token_hash") or "")
            cfg, guard_err = _prepare_security_cfg_for_save(cfg)
            if guard_err:
                return False, guard_err, _api_tokens_public()
            b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag=tag)
            if not b_ok:
                return False, f"backup failed: {backup_path}", _api_tokens_public()
            ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
            if not ok:
                return False, msg, _api_tokens_public()
            cfg_loaded = load_app_config(APP_CONFIG_PATH)
            r_ok, r_msg = reload_runtime_config(cfg_loaded)
            if not r_ok:
                return False, f"reload failed: {r_msg}", _api_tokens_public()
            api_loaded = cfg_loaded.get("api") if isinstance(cfg_loaded, dict) else None
            return True, "ok", _api_tokens_public(api_loaded if isinstance(api_loaded, dict) else None)
    except Exception as e:
        return False, str(e), _api_tokens_public()

def _build_api_token_create_payload(body: dict | None, *, headers=None, client_ip: str | None = None) -> tuple[dict, int]:
    if not _auth_enabled() or (not _auth_hashes_present(AUTH_CFG)):
        return {"ok": False, "error": "网页登录鉴权未启用或未完成配置，不能生成 API Token"}, 400
    src = body if isinstance(body, dict) else {}
    subject = str(src.get("username") or "-")
    reauth_ok = _auth_check_userpass(str(src.get("username") or ""), str(src.get("password") or ""))
    if not reauth_ok and headers is not None and headers.get("Authorization"):
        reauth_ok = _auth_check_basic_header(headers.get("Authorization"))
    if not reauth_ok:
        _op_log("api-token-create", "", actor=subject, ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": "账号或密码错误"}, 401
    now_wall = time.time()
    expires_at, expiry_err = _api_token_expiry_from_row(src, now_wall=now_wall, fallback=0.0)
    if expiry_err:
        return {"ok": False, "error": expiry_err}, 400
    name = str(src.get("name") or "").strip()
    if not name:
        name = "API Token " + time.strftime("%Y-%m-%d %H:%M:%S")
    token_plain = secrets.token_urlsafe(32)
    token_hash = _auth_secret_hash(token_plain)
    token_id = _api_token_id_from_hash(token_hash)
    item = {
        "id": token_id,
        "name": name[:80],
        "token": "",
        "token_hash": token_hash,
        "enabled": True,
        "created_ts": now_wall,
        "expires_at": expires_at,
        "single_use": _to_bool(src.get("single_use"), False),
        "used_ts": 0.0,
        "used_count": 0,
    }
    def _add_token(tokens):
        tokens.append(item)
        return tokens[-64:]
    ok, msg, tokens = _api_mutate_tokens(_add_token, tag="api_token_create")
    if not ok:
        return {"ok": False, "error": msg, "tokens": tokens}, 500
    _op_log("api-token-create", "name=" + name[:40], actor=subject, ip=str(client_ip or "-"), ok=True)
    return {
        "ok": True,
        "id": token_id,
        "name": name,
        "token": token_plain,
        "expires_at": expires_at,
        "expires_in_sec": None if expires_at <= 0 else int(max(0.0, expires_at - now_wall)),
        "single_use": bool(item.get("single_use")),
        "tokens": tokens,
    }, 200

def _api_token_docs_payload() -> dict:
    return {
        "ok": True,
        "api": _api_meta(),
        "auth": {
            "type": "token",
            "usage": [
                "Header: X-API-Token: <token>",
                "or Authorization: Bearer <token>",
                "Query fallback: ?token=<token> (not recommended for browser history/privacy)",
            ],
            "disabled_behavior": "When public API is disabled, /api/docs, /api/health and /api/v1/* only work from the built-in web pages via page session requests.",
            "token_policy": "API tokens support multiple entries, per-token expiry, single-use mode, and retained expired records.",
            "create_sso_link": {
                "method": "POST",
                "path": "/api/v1/auth/sso-links/create",
                "body": {
                    "name": "optional display name",
                    "next": "/",
                    "ttl_sec": 86400,
                    "expires": "never",
                    "single_use": False,
                },
                "expiry_fields": "Use one of ttl_sec, ttl_min, expires_at, or expires=never.",
            },
        },
        "endpoints": _api_endpoint_index(),
    }

def _api_v1_home_payload() -> dict:
    meta = _api_meta()
    return {
        "ok": True,
        "api": meta,
        "auth": {
            "token_api": {
                "enabled": bool(_api_token_enabled()),
                "headers": ["X-API-Token", "Authorization: Bearer <token>"],
                "query_fallback": "token",
                "supports_multiple_tokens": True,
                "supports_single_use": True,
                "supports_never_expires": True,
                "expired_tokens_auto_delete": False,
                "token_count": len(_api_tokens_public(API_CFG)),
                "whitelist_enabled": bool(API_CFG.get("whitelist_enabled")),
                "whitelist_count": len(API_CFG.get("whitelist") or []),
            },
            "web_login": meta.get("web_auth") or {},
            "sso_links": {
                "create_endpoint": "/api/v1/auth/sso-links/create",
                "supports_single_use": True,
                "supports_never_expires": True,
                "expired_links_auto_delete": False,
            },
        },
        "endpoints": _api_endpoint_index(),
    }

def _settings_runtime_payload(limit: int = 180) -> dict:
    try:
        n = max(20, min(1000, int(limit)))
    except Exception:
        n = 180
    aps, aps_seq, aps_total = _ap_snapshot()
    with log_lock:
        event_logs = list(log_buf)[-n:]
        scan_logs = list(scan_buf)[-n:]
        ap_logs = list(ap_buf)[-n:]
    return {
        "ok": True,
        "aps": aps,
        "aps_seq": aps_seq,
        "aps_total": aps_total,
        "metrics": _host_metrics_payload(24 * 3600),
        "event_logs": event_logs,
        "scan_logs": scan_logs,
        "ap_logs": ap_logs,
    }

def _logs_snapshot(log_type: str = "runtime", limit: int = 500) -> dict:
    try:
        n = max(1, min(5000, int(limit)))
    except Exception:
        n = 500
    kind = str(log_type or "runtime").strip().lower()
    with log_lock:
        runtime_rows = list(log_buf)[-n:]
        operation_rows = list(op_buf)[-n:]
        scan_rows = list(scan_buf)[-n:]
        ap_rows = list(ap_buf)[-n:]
    if kind in ("op", "ops", "operation", "audit"):
        kind = "operation"
        rows = operation_rows
    elif kind in ("scan", "scanner"):
        kind = "scan"
        rows = scan_rows
    elif kind in ("ap", "ap_scan"):
        kind = "ap"
        rows = ap_rows
    elif kind in ("diff", "scan_diff"):
        kind = "scan_diff"
        rows = list(difflib.unified_diff(
            runtime_rows,
            scan_rows,
            fromfile="runtime.log",
            tofile="scan.log",
            lineterm="",
        ))[-n:]
    else:
        kind = "runtime"
        rows = runtime_rows
    return {
        "ok": True,
        "type": kind,
        "limit": n,
        "count": len(rows),
        "items": rows,
        "available": ["runtime", "operation", "scan", "scan_diff", "ap"],
    }

def _logs_export_bytes(log_type: str = "all", limit: int = 5000) -> tuple[bytes, str, str]:
    stamp = time.strftime("%Y%m%d_%H%M%S")
    kind = str(log_type or "all").strip().lower()
    if kind == "all":
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
            for name in ("runtime", "operation", "scan", "scan_diff", "ap"):
                snap = _logs_snapshot(name, limit=limit)
                zf.writestr(f"{name}.log", "\n".join(str(x) for x in snap.get("items") or []) + "\n")
        return buf.getvalue(), f"light-rid-logs-{stamp}.zip", "application/zip"
    snap = _logs_snapshot(kind, limit=limit)
    body = ("\n".join(str(x) for x in snap.get("items") or []) + "\n").encode("utf-8")
    return body, f"light-rid-{snap.get('type')}-{stamp}.log", "text/plain; charset=utf-8"

def _oobe_status_payload() -> dict:
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else default_app_config()
    basic = cfg.get("basic") if isinstance(cfg, dict) else {}
    web = cfg.get("web") if isinstance(cfg, dict) else {}
    auth = cfg.get("auth") if isinstance(cfg, dict) else {}
    if not isinstance(basic, dict): basic = {}
    if not isinstance(web, dict): web = {}
    if not isinstance(auth, dict): auth = {}
    return {
        "ok": True,
        "oobe": _oobe_state(),
        "config_path": APP_CONFIG_PATH or "",
        "interfaces": _iface_options_snapshot(),
        "selected_iface": _cfg_preferred_iface_from_cfg(cfg),
        "network_bindings": _network_bindings_visual_payload(cfg),
        "channel": basic.get("channel"),
        "base_name": str(web.get("base_name") or "基站"),
        "base_lat": web.get("base_lat"),
        "base_lon": web.get("base_lon"),
        "auth_enabled": bool(auth.get("enabled")),
        "auth_configured": _auth_hashes_present(auth),
        "host": _host_resource_snapshot(),
    }

def _oobe_save_config(body: dict | None) -> dict:
    if not APP_CONFIG_PATH:
        return {"ok": False, "error": "config path missing"}
    payload = body if isinstance(body, dict) else {}
    iface = str(payload.get("iface") or "").strip()
    if not iface:
        return {"ok": False, "error": "必须选择默认网卡"}
    safe_iface = _hw_safe_iface(iface)
    if not safe_iface:
        return {"ok": False, "error": f"网卡不可用: {iface}"}
    iface = safe_iface
    try:
        channel = int(payload.get("channel") or 6)
    except Exception:
        channel = 6
    if channel < 1 or channel > 196:
        return {"ok": False, "error": "信道超出范围"}
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else default_app_config()
    basic = cfg.setdefault("basic", {})
    web = cfg.setdefault("web", {})
    auth = cfg.setdefault("auth", {})
    if not isinstance(basic, dict): basic = {}; cfg["basic"] = basic
    if not isinstance(web, dict): web = {}; cfg["web"] = web
    if not isinstance(auth, dict): auth = {}; cfg["auth"] = auth
    basic["iface"] = iface
    basic["channel"] = channel
    basic["no_tui"] = True
    basic["auto_self_heal"] = True
    nb_payload = payload.get("network_bindings") if isinstance(payload.get("network_bindings"), dict) else {}
    if nb_payload:
        cfg, bind_err = _network_bindings_apply_visual(cfg, nb_payload)
        if bind_err:
            return {"ok": False, "error": bind_err}
    else:
        cfg["network_bindings"] = _normalize_network_bindings_cfg({
            "basic": basic,
            "network_bindings": cfg.get("network_bindings") if isinstance(cfg.get("network_bindings"), dict) else {},
        })
    web["base_name"] = str(payload.get("base_name") or web.get("base_name") or "基站").strip() or "基站"
    for k, lo, hi in (("base_lat", -90.0, 90.0), ("base_lon", -180.0, 180.0)):
        raw_v = payload.get(k)
        if raw_v in (None, ""):
            continue
        try:
            val = float(raw_v)
        except Exception:
            return {"ok": False, "error": f"{k} 格式错误"}
        if not (lo <= val <= hi):
            return {"ok": False, "error": f"{k} 超出范围"}
        web[k] = val
    username = str(payload.get("username") or "").strip()
    password = str(payload.get("password") or "")
    if username or password:
        if not username or not password:
            return {"ok": False, "error": "账号和密码必须同时填写"}
        auth["enabled"] = True
        auth["username_hash"] = _auth_secret_hash(username)
        auth["password_hash"] = _auth_secret_hash(password)
        auth["realm"] = str(auth.get("realm") or "Light RID Scanner")
    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="oobe")
    if not b_ok:
        return {"ok": False, "error": f"backup failed: {backup_path}"}
    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
    if not ok:
        return {"ok": False, "error": f"save failed: {msg}"}
    cfg_loaded = load_app_config(APP_CONFIG_PATH)
    r_ok, r_msg = reload_runtime_config(cfg_loaded)
    if not r_ok:
        restore_config_backup(APP_CONFIG_PATH, backup_path)
        return {"ok": False, "error": f"reload failed: {r_msg}", "backup_path": backup_path}
    _set_oobe_required("", False)
    _op_log("oobe-save", f"iface={iface} channel={channel} backup={backup_path}", ok=True)
    return {
        "ok": True,
        "saved_to": APP_CONFIG_PATH,
        "backup_path": backup_path,
        "iface": iface,
        "channel": channel,
        "reload_msg": r_msg,
        "login_required": bool(_normalize_auth_cfg(cfg_loaded).get("enabled")),
        "next": ("/login" if bool(_normalize_auth_cfg(cfg_loaded).get("enabled")) else "/"),
    }

def _diagnostic_run(cmd: str, timeout: int = 8) -> str:
    try:
        r = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        out = (r.stdout or "")
        err = (r.stderr or "")
        text = out
        if err:
            text += ("\n--- STDERR ---\n" + err)
        if not text.strip():
            text = f"(empty, rc={getattr(r, 'returncode', '')})\n"
        return text
    except Exception as e:
        return f"command failed: {e}\n"

def _diagnostic_redact(obj):
    sensitive = ("token", "password", "secret", "webhook", "key", "sha256", "authorization", "cookie")
    if isinstance(obj, dict):
        out = {}
        for k, v in obj.items():
            ks = str(k).lower()
            if any(s in ks for s in sensitive):
                out[k] = "***REDACTED***" if v not in (None, "", []) else v
            else:
                out[k] = _diagnostic_redact(v)
        return out
    if isinstance(obj, list):
        return [_diagnostic_redact(x) for x in obj]
    return obj

def _diagnostic_zip_bytes() -> tuple[bytes, str]:
    now_wall = time.time()
    stamp = time.strftime("%Y%m%d_%H%M%S", time.localtime(now_wall))
    buf = io.BytesIO()
    now_mono = time.monotonic()
    meta = {
        "generated_at": _fmt_wall_ts(now_wall),
        "uptime_sec": int(max(0.0, now_wall - APP_START_WALL)),
        "cwd": APP_START_CWD,
        "config_path": APP_CONFIG_PATH or "",
        "history_store": HISTORY_STORE_PATH or "",
        "app_version": _app_version_label(),
        "python": sys.version,
        "platform": platform.platform(),
        "argv": list(sys.argv),
        "current_channel": current_channel,
        "sniff": _sniff_health_meta(now_mono, now_wall),
        "api": _api_meta(),
    }
    with log_lock:
        event_logs = list(log_buf)
        scan_logs = list(scan_buf)
        ap_logs = list(ap_buf)
        operation_logs = list(op_buf)
    with state_lock:
        state_summary = {
            "live_count": len(state_table),
            "history_count": len(history_table),
            "live_keys": sorted([str(k) for k in state_table.keys()])[:500],
            "history_keys": sorted([str(k) for k in history_table.keys()])[:500],
        }
    commands = {
        "system_uname.txt": "uname -a",
        "system_uptime.txt": "uptime",
        "system_free.txt": "free -h",
        "system_df.txt": "df -h",
        "system_ip_addr.txt": "ip addr",
        "system_ip_link.txt": "ip link",
        "wifi_iw_dev.txt": "iw dev",
        "wifi_iw_info.txt": "iw dev 2>/dev/null",
        "wifi_iw_phy.txt": "iw phy",
        "wifi_rfkill.txt": "rfkill list",
        "usb_lsusb.txt": "lsusb",
        "service_status.txt": "systemctl status light-rid-scanner.service --no-pager -l",
        "service_journal.txt": "journalctl -u light-rid-scanner.service -n 500 --no-pager",
        "process_ps.txt": "ps -eo pid,ppid,stat,pcpu,pmem,comm,args --sort=-pcpu | head -80",
    }
    if sniff_iface_name:
        safe_iface = shlex.quote(str(sniff_iface_name))
        commands[f"wifi_{sniff_iface_name}_info.txt"] = f"iw dev {safe_iface} info"
        commands[f"wifi_{sniff_iface_name}_link.txt"] = f"iw dev {safe_iface} link"
    with zipfile.ZipFile(buf, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
        zf.writestr("README.txt", (
            "Light RID Scanner quality report\n"
            "Sensitive config values are redacted. Logs may still contain observed SN/MAC/location data.\n"
        ))
        zf.writestr("meta.json", json.dumps(meta, ensure_ascii=False, indent=2))
        zf.writestr("state_summary.json", json.dumps(state_summary, ensure_ascii=False, indent=2))
        zf.writestr("snapshot.json", json.dumps(_state_snapshot(), ensure_ascii=False, indent=2))
        zf.writestr("config_redacted.json", json.dumps(_diagnostic_redact(APP_CONFIG), ensure_ascii=False, indent=2))
        zf.writestr("logs/event.log", "\n".join(event_logs) + ("\n" if event_logs else ""))
        zf.writestr("logs/scan.log", "\n".join(scan_logs) + ("\n" if scan_logs else ""))
        zf.writestr("logs/ap.log", "\n".join(ap_logs) + ("\n" if ap_logs else ""))
        zf.writestr("logs/operation.log", "\n".join(operation_logs) + ("\n" if operation_logs else ""))
        for name, cmd in commands.items():
            zf.writestr("commands/" + name, "$ " + cmd + "\n\n" + _diagnostic_run(cmd, timeout=10))
    data = buf.getvalue()
    if len(data) < 128:
        fallback = io.BytesIO()
        with zipfile.ZipFile(fallback, "w", compression=zipfile.ZIP_STORED) as zf:
            zf.writestr("README.txt", "Light RID Scanner quality report fallback\n")
            zf.writestr("meta.json", json.dumps(meta, ensure_ascii=False, indent=2))
        data = fallback.getvalue()
    filename = f"light-rid-quality-{stamp}.zip"
    return data, filename

def _path_uses_api_token(req_path: str | None) -> bool:
    path = str(req_path or "").split("?", 1)[0]
    if path == "/api/docs":
        return True
    if path == "/api/health":
        return True
    if path in ("/api/v1", "/api/v1/"):
        return True
    return path.startswith("/api/v1/")

def _path_is_page_api(req_path: str | None) -> bool:
    path = str(req_path or "").split("?", 1)[0]
    return path.startswith("/api/") and (not _path_uses_api_token(path))

def _path_is_oobe_public(req_path: str | None) -> bool:
    path = str(req_path or "").split("?", 1)[0]
    return path in ("/oobe", "/oobe.html", "/api/oobe/status", "/api/oobe/save", "/api/health")

def _oobe_redirect_required(req_path: str | None) -> bool:
    if not _oobe_state().get("required"):
        return False
    path = str(req_path or "").split("?", 1)[0]
    if _path_is_oobe_public(path):
        return False
    return True

def _oobe_auth_required() -> bool:
    return bool(_oobe_state().get("required")) and _auth_enabled() and _auth_hashes_present(AUTH_CFG)

def _auth_enabled() -> bool:
    if _portable_edition_enabled():
        return False
    return bool(AUTH_CFG.get("enabled"))

def _auth_check_userpass(username: str, password: str) -> bool:
    if not _auth_enabled():
        return True
    u_hash = str(AUTH_CFG.get("username_hash") or "").strip()
    p_hash = str(AUTH_CFG.get("password_hash") or "").strip()
    if not u_hash or not p_hash:
        return False
    u_ok = _verify_auth_secret(username, u_hash)
    p_ok = _verify_auth_secret(password, p_hash)
    return bool(u_ok and p_ok)

def _webauthn_b64u_encode(data: bytes | None) -> str:
    raw = bytes(data or b"")
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode("ascii")

def _webauthn_b64u_decode(text: str | None) -> bytes:
    raw = str(text or "").strip()
    if not raw:
        return b""
    raw += "=" * (-len(raw) % 4)
    return base64.urlsafe_b64decode(raw.encode("ascii"))

def _webauthn_host_from_header(host_header: str | None) -> str:
    host = str(host_header or "").strip().lower()
    if not host:
        return "localhost"
    if host.startswith("[") and "]" in host:
        host = host[1:host.index("]")]
    elif ":" in host:
        host = host.rsplit(":", 1)[0]
    return host or "localhost"

def _webauthn_origin_from_headers(headers) -> str:
    host = _webauthn_host_from_header(headers.get("Host") if headers is not None else None)
    if headers is not None:
        proto = str(headers.get("X-Forwarded-Proto") or "").strip().lower()
        if proto not in ("http", "https"):
            origin = str(headers.get("Origin") or "").strip()
            m = re.match(r"^(https?)://([^/]+)", origin)
            if m:
                proto = m.group(1).lower()
        if proto not in ("http", "https"):
            proto = "https" if str(headers.get("Upgrade-Insecure-Requests") or "") == "1" else "http"
    else:
        proto = "http"
    return f"{proto}://{host}"

def _webauthn_rp_id_from_headers(headers) -> str:
    return _webauthn_host_from_header(headers.get("Host") if headers is not None else None)

def _webauthn_user_handle() -> bytes:
    seed = str(AUTH_CFG.get("username_hash") or AUTH_CFG.get("realm") or "Light RID Scanner").strip()
    if not seed:
        seed = "Light RID Scanner"
    return hashlib.sha256((seed + "|passkey").encode("utf-8", errors="ignore")).digest()

_CBOR_BREAK = object()

def _cbor_read_length(data: bytes, offset: int, ai: int) -> tuple[int | None, int]:
    if ai < 24:
        return ai, offset
    if ai == 24:
        return data[offset], offset + 1
    if ai == 25:
        return int.from_bytes(data[offset:offset + 2], "big"), offset + 2
    if ai == 26:
        return int.from_bytes(data[offset:offset + 4], "big"), offset + 4
    if ai == 27:
        return int.from_bytes(data[offset:offset + 8], "big"), offset + 8
    if ai == 31:
        return None, offset
    raise ValueError("unsupported cbor length")

def _cbor_decode_one(data: bytes, offset: int = 0):
    if offset >= len(data):
        raise ValueError("cbor truncated")
    initial = data[offset]
    offset += 1
    major = initial >> 5
    ai = initial & 31
    if major in (0, 1):
        n, offset = _cbor_read_length(data, offset, ai)
        if n is None:
            raise ValueError("indefinite integer")
        return (n if major == 0 else -1 - n), offset
    if major in (2, 3):
        length, offset = _cbor_read_length(data, offset, ai)
        if length is None:
            chunks: list[bytes] = []
            while True:
                if offset >= len(data):
                    raise ValueError("cbor truncated")
                if data[offset] == 0xFF:
                    offset += 1
                    break
                part, offset = _cbor_decode_one(data, offset)
                if major == 2:
                    if not isinstance(part, (bytes, bytearray)):
                        raise ValueError("invalid cbor chunk")
                    chunks.append(bytes(part))
                else:
                    if not isinstance(part, str):
                        raise ValueError("invalid cbor chunk")
                    chunks.append(part.encode("utf-8"))
            raw = b"".join(chunks)
            return (raw if major == 2 else raw.decode("utf-8", errors="replace")), offset
        raw = data[offset:offset + length]
        offset += length
        return (bytes(raw) if major == 2 else raw.decode("utf-8", errors="replace")), offset
    if major == 4:
        length, offset = _cbor_read_length(data, offset, ai)
        items = []
        if length is None:
            while True:
                if offset >= len(data):
                    raise ValueError("cbor truncated")
                if data[offset] == 0xFF:
                    offset += 1
                    break
                item, offset = _cbor_decode_one(data, offset)
                items.append(item)
        else:
            for _ in range(length):
                item, offset = _cbor_decode_one(data, offset)
                items.append(item)
        return items, offset
    if major == 5:
        length, offset = _cbor_read_length(data, offset, ai)
        items = {}
        if length is None:
            while True:
                if offset >= len(data):
                    raise ValueError("cbor truncated")
                if data[offset] == 0xFF:
                    offset += 1
                    break
                key, offset = _cbor_decode_one(data, offset)
                val, offset = _cbor_decode_one(data, offset)
                items[key] = val
        else:
            for _ in range(length):
                key, offset = _cbor_decode_one(data, offset)
                val, offset = _cbor_decode_one(data, offset)
                items[key] = val
        return items, offset
    if major == 6:
        _tag, offset = _cbor_read_length(data, offset, ai)
        return _cbor_decode_one(data, offset)
    if major == 7:
        if ai == 20:
            return False, offset
        if ai == 21:
            return True, offset
        if ai in (22, 23):
            return None, offset
        if ai == 24:
            return data[offset], offset + 1
        if ai == 25:
            raw = int.from_bytes(data[offset:offset + 2], "big")
            offset += 2
            sign = (raw >> 15) & 1
            exp = (raw >> 10) & 0x1F
            frac = raw & 0x3FF
            val = (1 if sign == 0 else -1) * (2 ** (exp - 15)) * (1 + frac / 1024.0)
            return val, offset
        if ai == 26:
            return struct.unpack(">f", data[offset:offset + 4])[0], offset + 4
        if ai == 27:
            return struct.unpack(">d", data[offset:offset + 8])[0], offset + 8
        if ai == 31:
            return _CBOR_BREAK, offset
    raise ValueError("unsupported cbor type")

def _cbor_loads(data: bytes):
    value, offset = _cbor_decode_one(bytes(data or b""))
    if offset != len(data):
        raise ValueError("cbor trailing data")
    return value

def _webauthn_decode_json(data: bytes | str | None) -> dict:
    raw = data.decode("utf-8", errors="replace") if isinstance(data, (bytes, bytearray)) else str(data or "")
    parsed = json.loads(raw)
    if not isinstance(parsed, dict):
        raise ValueError("client data must be object")
    return parsed

def _webauthn_public_key_coords(public_key) -> tuple[int, int]:
    if not isinstance(public_key, dict):
        raise ValueError("public key missing")
    x_raw = public_key.get("x")
    y_raw = public_key.get("y")
    if not x_raw or not y_raw:
        raise ValueError("public key missing coordinates")
    def _decode_coord(raw):
        text = str(raw or "").strip()
        if not text:
            raise ValueError("empty coordinate")
        if re.fullmatch(r"[0-9a-fA-F]{64}", text):
            return int.from_bytes(bytes.fromhex(text), "big")
        buf = _webauthn_b64u_decode(text)
        if len(buf) != 32:
            raise ValueError("invalid coordinate length")
        return int.from_bytes(buf, "big")
    return _decode_coord(x_raw), _decode_coord(y_raw)

_P256_P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
_P256_A = (_P256_P - 3) % _P256_P
_P256_B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
_P256_GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
_P256_GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
_P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
_P256_G = (_P256_GX, _P256_GY)

def _p256_on_curve(point: tuple[int, int] | None) -> bool:
    if point is None:
        return True
    x, y = point
    if not (0 <= x < _P256_P and 0 <= y < _P256_P):
        return False
    return (y * y - (x * x * x + _P256_A * x + _P256_B)) % _P256_P == 0

def _p256_point_add(p: tuple[int, int] | None, q: tuple[int, int] | None) -> tuple[int, int] | None:
    if p is None:
        return q
    if q is None:
        return p
    x1, y1 = p
    x2, y2 = q
    if x1 == x2:
        if (y1 + y2) % _P256_P == 0:
            return None
        slope = ((3 * x1 * x1 + _P256_A) * pow(2 * y1, -1, _P256_P)) % _P256_P
    else:
        slope = ((y2 - y1) * pow((x2 - x1) % _P256_P, -1, _P256_P)) % _P256_P
    x3 = (slope * slope - x1 - x2) % _P256_P
    y3 = (slope * (x1 - x3) - y1) % _P256_P
    return x3, y3

def _p256_point_mul(k: int, point: tuple[int, int] | None) -> tuple[int, int] | None:
    if point is None:
        return None
    if k % _P256_N == 0:
        return None
    result = None
    addend = point
    n = k % _P256_N
    while n:
        if n & 1:
            result = _p256_point_add(result, addend)
        addend = _p256_point_add(addend, addend)
        n >>= 1
    return result

def _ecdsa_parse_der_signature(sig: bytes) -> tuple[int, int]:
    raw = bytes(sig or b"")
    if len(raw) < 8 or raw[0] != 0x30:
        raise ValueError("invalid signature")
    total_len = raw[1]
    idx = 2
    if total_len & 0x80:
        n_len = total_len & 0x7F
        total_len = int.from_bytes(raw[idx:idx + n_len], "big")
        idx += n_len
    if idx + total_len > len(raw):
        raise ValueError("invalid signature length")
    def read_int() -> int:
        nonlocal idx
        if idx >= len(raw) or raw[idx] != 0x02:
            raise ValueError("invalid signature integer")
        idx += 1
        if idx >= len(raw):
            raise ValueError("invalid signature integer length")
        ln = raw[idx]
        idx += 1
        if ln & 0x80:
            n_len = ln & 0x7F
            ln = int.from_bytes(raw[idx:idx + n_len], "big")
            idx += n_len
        val = int.from_bytes(raw[idx:idx + ln], "big")
        idx += ln
        return val
    r = read_int()
    s = read_int()
    return r, s

def _ecdsa_verify_p256(public_key: dict, message_hash: bytes, signature: bytes) -> bool:
    try:
        x, y = _webauthn_public_key_coords(public_key)
    except Exception:
        return False
    if not _p256_on_curve((x, y)):
        return False
    try:
        r, s = _ecdsa_parse_der_signature(signature)
    except Exception:
        return False
    if not (1 <= r < _P256_N and 1 <= s < _P256_N):
        return False
    e = int.from_bytes(bytes(message_hash or b""), "big")
    w = pow(s, -1, _P256_N)
    u1 = (e * w) % _P256_N
    u2 = (r * w) % _P256_N
    p = _p256_point_add(_p256_point_mul(u1, _P256_G), _p256_point_mul(u2, (x, y)))
    if p is None:
        return False
    return (p[0] % _P256_N) == r

def _webauthn_parse_attestation_object(raw: bytes) -> dict:
    obj = _cbor_loads(bytes(raw or b""))
    if not isinstance(obj, dict):
        raise ValueError("attestation object must be map")
    fmt = str(obj.get("fmt") or "").strip().lower()
    auth_data = obj.get("authData")
    if fmt != "none":
        raise ValueError("only none attestation is supported")
    if not isinstance(auth_data, (bytes, bytearray)) or len(auth_data) < 37:
        raise ValueError("authData missing")
    auth = bytes(auth_data)
    rp_id_hash = auth[:32]
    flags = auth[32]
    sign_count = int.from_bytes(auth[33:37], "big")
    offset = 37
    if not (flags & 0x40):
        raise ValueError("credential data missing")
    if offset + 16 + 2 > len(auth):
        raise ValueError("credential data truncated")
    aaguid = auth[offset:offset + 16]
    offset += 16
    cred_len = int.from_bytes(auth[offset:offset + 2], "big")
    offset += 2
    if offset + cred_len > len(auth):
        raise ValueError("credential id truncated")
    cred_id = auth[offset:offset + cred_len]
    offset += cred_len
    public_key, offset = _cbor_decode_one(auth, offset)
    if offset > len(auth):
        raise ValueError("public key truncated")
    if not isinstance(public_key, dict):
        raise ValueError("public key missing")
    cose_kty = public_key.get(1)
    cose_alg = public_key.get(3)
    cose_crv = public_key.get(-1)
    x = public_key.get(-2)
    y = public_key.get(-3)
    if cose_kty != 2 or cose_alg != -7 or cose_crv != 1 or not x or not y:
        raise ValueError("unsupported credential public key")
    return {
        "auth_data": auth,
        "rp_id_hash": rp_id_hash,
        "flags": flags,
        "credential_id": bytes(cred_id),
        "sign_count": sign_count,
        "public_key": {
            "kty": "EC",
            "crv": "P-256",
            "x": _webauthn_b64u_encode(bytes(x) if isinstance(x, (bytes, bytearray)) else b""),
            "y": _webauthn_b64u_encode(bytes(y) if isinstance(y, (bytes, bytearray)) else b""),
        },
        "aaguid": _webauthn_b64u_encode(aaguid),
    }

# -----------------------------------------------------------------------------
# WebAuthn / passkey helpers
# -----------------------------------------------------------------------------
def _auth_passkeys_public(auth_cfg: dict | None = None) -> list[dict]:
    source = auth_cfg if isinstance(auth_cfg, dict) else AUTH_CFG
    out: list[dict] = []
    for item in _normalize_passkeys(source.get("passkeys")):
        out.append({
            "id": str(item.get("id") or ""),
            "name": str(item.get("name") or ""),
            "enabled": bool(item.get("enabled", True)),
            "created_ts": float(item.get("created_ts") or 0.0),
            "last_used_ts": float(item.get("last_used_ts") or 0.0),
            "sign_count": int(item.get("sign_count") or 0),
        })
    return out

def _passkey_timeout_ms() -> int:
    return int(PASSKEY_CHALLENGE_TTL_SEC * 1000)

def _auth_mutate_passkeys(mutator, *, tag: str = "passkey") -> tuple[bool, str, list[dict]]:
    if not APP_CONFIG_PATH:
        return False, "config path missing", _auth_passkeys_public()
    try:
        with auth_passkey_lock:
            cfg = load_app_config(APP_CONFIG_PATH)
            auth = cfg.setdefault("auth", {})
            if not isinstance(auth, dict):
                auth = {}
                cfg["auth"] = auth
            items = _normalize_passkeys(auth.get("passkeys"))
            auth["passkeys"] = _normalize_passkeys(mutator(list(items)))
            # Passkey changes must stay aligned with the saved config and the
            # in-memory auth runtime, so save + reload are handled as one flow.
            cfg, guard_err = _prepare_security_cfg_for_save(cfg)
            if guard_err:
                return False, guard_err, _auth_passkeys_public()
            b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag=tag)
            if not b_ok:
                return False, f"backup failed: {backup_path}", _auth_passkeys_public()
            ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
            if not ok:
                return False, msg, _auth_passkeys_public()
            cfg_loaded = load_app_config(APP_CONFIG_PATH)
            r_ok, r_msg = reload_runtime_config(cfg_loaded)
            if not r_ok:
                return False, f"reload failed: {r_msg}", _auth_passkeys_public()
            auth_loaded = cfg_loaded.get("auth") if isinstance(cfg_loaded, dict) else None
            return True, "ok", _auth_passkeys_public(auth_loaded if isinstance(auth_loaded, dict) else None)
    except Exception as e:
        return False, str(e), _auth_passkeys_public()

def _passkey_cleanup(now_wall: float | None = None) -> None:
    now_wall = float(now_wall or time.time())
    with passkey_challenge_lock:
        stale = [k for k, v in passkey_challenges.items() if float((v or {}).get("expires_at") or 0.0) <= now_wall]
        for key in stale:
            passkey_challenges.pop(key, None)

def _passkey_challenge_new(kind: str, data: dict | None = None, *, ttl_sec: int = PASSKEY_CHALLENGE_TTL_SEC) -> dict:
    now_wall = time.time()
    token = secrets.token_urlsafe(24)
    row = dict(data or {})
    row.update({
        "kind": kind,
        "challenge": token,
        "created_ts": now_wall,
        "expires_at": now_wall + max(60, int(ttl_sec or PASSKEY_CHALLENGE_TTL_SEC)),
    })
    with passkey_challenge_lock:
        passkey_challenges[token] = row
        if len(passkey_challenges) > 1024:
            _passkey_cleanup(now_wall=now_wall)
    return row

def _passkey_challenge_take(token: str | None, kind: str | None = None) -> dict | None:
    raw = str(token or "").strip()
    if not raw:
        return None
    now_wall = time.time()
    with passkey_challenge_lock:
        row = passkey_challenges.pop(raw, None)
    if not isinstance(row, dict):
        return None
    if float(row.get("expires_at") or 0.0) <= now_wall:
        return None
    if kind and str(row.get("kind") or "") != kind:
        return None
    return row

def _passkey_options_public(passkeys: list[dict]) -> list[dict]:
    out: list[dict] = []
    for item in passkeys:
        cred_id = str(item.get("id") or "").strip()
        if not cred_id or not bool(item.get("enabled", True)):
            continue
        out.append({
            "type": "public-key",
            "id": cred_id,
            "transports": ["internal", "hybrid", "usb", "nfc", "ble"],
        })
    return out

def _passkey_record_payload(passkey_name: str | None = None) -> str:
    name = str(passkey_name or "").strip()
    if name:
        return name[:80]
    return "通行密钥 " + time.strftime("%Y-%m-%d %H:%M:%S")

def _passkey_login_begin(headers) -> dict:
    if not _auth_enabled() or not _auth_hashes_present(AUTH_CFG):
        return {"ok": False, "error": "网页登录账号密码未配置完整"}
    if not _auth_login_method_enabled("passkey"):
        return {"ok": False, "error": "PassKey 登录已关闭"}
    items = [item for item in _normalize_passkeys(AUTH_CFG.get("passkeys")) if bool(item.get("enabled", True))]
    if not items:
        return {"ok": False, "error": "暂无可用的通行密钥"}
    rp_id = _webauthn_rp_id_from_headers(headers)
    origin = _webauthn_origin_from_headers(headers)
    row = _passkey_challenge_new("login", {
        "rp_id": rp_id,
        "origin": origin,
        "allow_credentials": [str(item.get("id") or "") for item in items],
    })
    return {
        "ok": True,
        "challenge": row["challenge"],
        "challenge_token": row["challenge"],
        "rp_id": rp_id,
        "origin": origin,
        "timeout_ms": _passkey_timeout_ms(),
        "allow_credentials": _passkey_options_public(items),
        "passkeys": _auth_passkeys_public(),
        "realm": str(AUTH_CFG.get("realm") or "Light RID Scanner"),
    }

def _passkey_register_begin(body: dict | None, headers, *, client_ip: str | None = None) -> dict:
    if not _auth_enabled() or not _auth_hashes_present(AUTH_CFG):
        return {"ok": False, "error": "网页登录账号密码未配置完整"}, 400
    if not _auth_login_method_enabled("passkey"):
        return {"ok": False, "error": "PassKey 登录已关闭"}, 403
    src = body if isinstance(body, dict) else {}
    user = str(src.get("username") or "").strip()
    pwd = str(src.get("password") or "")
    if not user or not pwd:
        return {"ok": False, "error": "请同时提供账号和密码"}, 400
    if not _auth_check_userpass(user, pwd):
        _op_log("passkey-register", "start auth failed", actor=user or "-", ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": "账号或密码错误"}, 401
    rp_id = _webauthn_rp_id_from_headers(headers)
    origin = _webauthn_origin_from_headers(headers)
    realm = str(AUTH_CFG.get("realm") or "Light RID Scanner")
    passkey_name = _passkey_record_payload(src.get("name") or src.get("label"))
    row = _passkey_challenge_new("register", {
        "rp_id": rp_id,
        "origin": origin,
        "passkey_name": passkey_name,
        "user_handle": _webauthn_b64u_encode(_webauthn_user_handle()),
    })
    return {
        "ok": True,
        "challenge": row["challenge"],
        "challenge_token": row["challenge"],
        "rp_id": rp_id,
        "origin": origin,
        "timeout_ms": _passkey_timeout_ms(),
        "publicKey": {
            "challenge": row["challenge"],
            "rp": {"name": realm, "id": rp_id},
            "user": {
                "id": _webauthn_b64u_encode(_webauthn_user_handle()),
                "name": user,
                "displayName": passkey_name,
            },
            "pubKeyCredParams": [{"type": "public-key", "alg": -7}],
            "timeout": _passkey_timeout_ms(),
            "attestation": "none",
            "authenticatorSelection": {
                "userVerification": "preferred",
                "residentKey": "preferred",
            },
            "excludeCredentials": _passkey_options_public(_normalize_passkeys(AUTH_CFG.get("passkeys"))),
        },
        "passkey_name": passkey_name,
        "realm": realm,
    }

def _passkey_finish_register(body: dict | None, headers, *, client_ip: str | None = None) -> dict:
    if not _auth_login_method_enabled("passkey"):
        return {"ok": False, "error": "PassKey 登录已关闭"}, 403
    src = body if isinstance(body, dict) else {}
    token = str(src.get("challenge") or src.get("challenge_token") or "").strip()
    row = _passkey_challenge_take(token, "register")
    if not row:
        return {"ok": False, "error": "challenge expired"}, 400
    expected_origin = str(row.get("origin") or "")
    expected_rp_id = str(row.get("rp_id") or "")
    response = src.get("response") if isinstance(src.get("response"), dict) else {}
    try:
        # Registration accepts a new credential only after challenge, origin,
        # and rpId validation succeed against the stored single-use challenge.
        client_data_raw = _webauthn_b64u_decode(str(response.get("clientDataJSON") or ""))
        client_data = _webauthn_decode_json(client_data_raw)
        if str(client_data.get("type") or "") != "webauthn.create":
            raise ValueError("invalid client data type")
        if str(client_data.get("challenge") or "") != token:
            raise ValueError("challenge mismatch")
        if str(client_data.get("origin") or "") != expected_origin:
            raise ValueError("origin mismatch")
        att_obj = _webauthn_parse_attestation_object(_webauthn_b64u_decode(str(response.get("attestationObject") or "")))
        cred_id = bytes(att_obj.get("credential_id") or b"")
        if not cred_id:
            raise ValueError("credential id missing")
        if str(expected_rp_id) and hashlib.sha256(expected_rp_id.encode("utf-8", errors="ignore")).digest() != bytes(att_obj.get("rp_id_hash") or b""):
            raise ValueError("rpId mismatch")
        passkey_name = str(src.get("name") or row.get("passkey_name") or "通行密钥").strip() or "通行密钥"
        cred_id_text = _webauthn_b64u_encode(cred_id)
        public_key = att_obj.get("public_key") if isinstance(att_obj.get("public_key"), dict) else {}
        sign_count = int(att_obj.get("sign_count") or 0)
    except Exception as e:
        _op_log("passkey-register", f"finish error={e}", actor=str(src.get("username") or "-"), ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": str(e)}, 400
    def _add_passkey(items):
        items = [dict(item or {}) for item in items]
        items = [item for item in items if str(item.get("id") or "") != cred_id_text]
        items.append({
            "id": cred_id_text,
            "name": passkey_name,
            "user_handle": str(row.get("user_handle") or ""),
            "public_key": public_key,
            "sign_count": sign_count,
            "created_ts": time.time(),
            "last_used_ts": 0.0,
            "enabled": True,
        })
        return items[-32:]
    ok, msg, passkeys = _auth_mutate_passkeys(_add_passkey, tag="passkey_create")
    if not ok:
        return {"ok": False, "error": msg, "passkeys": passkeys}, 500
    _op_log("passkey-register", f"ok name={passkey_name}", actor=str(src.get("username") or "-"), ip=str(client_ip or "-"), ok=True)
    return {"ok": True, "passkeys": passkeys, "passkey_name": passkey_name}, 200

def _passkey_finish_login(body: dict | None, headers, *, client_ip: str | None = None) -> dict:
    if not _auth_enabled() or not _auth_hashes_present(AUTH_CFG):
        return {"ok": False, "error": "网页登录账号密码未配置完整"}, 400
    if not _auth_login_method_enabled("passkey"):
        return {"ok": False, "error": "PassKey 登录已关闭"}, 403
    src = body if isinstance(body, dict) else {}
    token = str(src.get("challenge") or src.get("challenge_token") or "").strip()
    row = _passkey_challenge_take(token, "login")
    if not row:
        return {"ok": False, "error": "challenge expired"}, 400
    expected_origin = str(row.get("origin") or "")
    expected_rp_id = str(row.get("rp_id") or "")
    response = src.get("response") if isinstance(src.get("response"), dict) else {}
    cred_id = str(src.get("id") or src.get("rawId") or "").strip()
    if not cred_id:
        return {"ok": False, "error": "credential id required"}, 400
    passkey_row = None
    for item in _normalize_passkeys(AUTH_CFG.get("passkeys")):
        if str(item.get("id") or "") == cred_id and bool(item.get("enabled", True)):
            passkey_row = dict(item)
            break
    if not passkey_row:
        return {"ok": False, "error": "unknown passkey"}, 401
    try:
        # Login verification stays fully local: validate challenge/origin/rpId,
        # then verify the signature against the stored credential public key.
        client_data_raw = _webauthn_b64u_decode(str(response.get("clientDataJSON") or ""))
        client_data = _webauthn_decode_json(client_data_raw)
        if str(client_data.get("type") or "") != "webauthn.get":
            raise ValueError("invalid client data type")
        if str(client_data.get("challenge") or "") != token:
            raise ValueError("challenge mismatch")
        if str(client_data.get("origin") or "") != expected_origin:
            raise ValueError("origin mismatch")
        auth_data = _webauthn_b64u_decode(str(response.get("authenticatorData") or ""))
        signature = _webauthn_b64u_decode(str(response.get("signature") or ""))
        if len(auth_data) < 37 or not signature:
            raise ValueError("invalid assertion response")
        if expected_rp_id and hashlib.sha256(expected_rp_id.encode("utf-8", errors="ignore")).digest() != auth_data[:32]:
            raise ValueError("rpId mismatch")
        flags = auth_data[32]
        if not (flags & 0x01):
            raise ValueError("user presence required")
        message_hash = hashlib.sha256(auth_data + hashlib.sha256(client_data_raw).digest()).digest()
        if not _ecdsa_verify_p256(passkey_row.get("public_key") or {}, message_hash, signature):
            raise ValueError("signature mismatch")
        sign_count = int.from_bytes(auth_data[33:37], "big")
    except Exception as e:
        _op_log("passkey-login", f"finish error={e}", actor=str(passkey_row.get("name") or "-"), ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": str(e)}, 401
    def _touch_passkey(items):
        now_wall = time.time()
        out = []
        for item in items:
            row_item = dict(item or {})
            if str(row_item.get("id") or "") == cred_id:
                row_item["last_used_ts"] = now_wall
                if sign_count > int(row_item.get("sign_count") or 0):
                    row_item["sign_count"] = sign_count
            out.append(row_item)
        return out
    ok, _msg, _ = _auth_mutate_passkeys(_touch_passkey, tag="passkey_use")
    if not ok:
        _log("[WARN] passkey usage update failed: " + str(_msg))
    self_tok = _auth_issue_session()
    _op_log("passkey-login", "login ok", actor=str(passkey_row.get("name") or "-"), ip=str(client_ip or "-"), ok=True)
    return {"ok": True, "next": str(src.get("next") or "/") or "/", "session": self_tok}, 200

def _auth_sso_path(check: str, next_path: str = "/") -> str:
    from urllib.parse import quote
    target = str(next_path or "/").strip() or "/"
    if not target.startswith("/") or target.startswith("//"):
        target = "/"
    return (
        "/login?check=" + quote(str(check or "").strip(), safe="")
        + "&next=" + quote(target, safe="/")
    )

def _auth_sso_public_links(auth_cfg: dict | None = None, *, include_paths: bool = False) -> list[dict]:
    from urllib.parse import quote
    source = auth_cfg if isinstance(auth_cfg, dict) else AUTH_CFG
    out: list[dict] = []
    for item in _prune_expired_sso_links(source.get("sso_links")):
        check = str(item.get("check") or "").strip()
        next_path = str(item.get("next") or "/")
        path = (
            "/login?check=" + quote(check, safe="")
            + "&next=" + quote(next_path, safe="/")
        )
        state = _sso_link_state(item)
        row = {
            "name": str(item.get("name") or ""),
            "check": check,
            "enabled": bool(item.get("enabled", True)),
            "created_ts": float(item.get("created_ts") or 0.0),
            "expires_at": float(item.get("expires_at") or 0.0),
            "expires_in_sec": state.get("expires_in_sec"),
            "single_use": bool(item.get("single_use")),
            "used_ts": float(item.get("used_ts") or 0.0),
            "used_count": int(item.get("used_count") or 0),
            "next": next_path,
            "active": bool(state.get("active")),
            "status": str(state.get("status") or ""),
            "status_label": str(state.get("status_label") or ""),
        }
        if include_paths:
            row["path"] = path
        out.append(row)
    return out

def _auth_check_sso_link(check: str | None) -> dict | None:
    raw_check = str(check or "").strip()
    if not raw_check:
        return None
    for item in _prune_expired_sso_links(AUTH_CFG.get("sso_links")):
        if hmac.compare_digest(str(item.get("check") or ""), raw_check) and bool(_sso_link_state(item).get("active")):
            return dict(item)
    return None

def _auth_mark_sso_used(check: str | None) -> bool:
    raw_check = str(check or "").strip()
    if not raw_check:
        return False
    changed = False
    now_wall = time.time()
    def _mark(links):
        nonlocal changed
        out = []
        for item in links:
            row = dict(item or {})
            if hmac.compare_digest(str(row.get("check") or ""), raw_check):
                row["used_count"] = int(row.get("used_count") or 0) + 1
                row["used_ts"] = now_wall
                changed = True
            out.append(row)
        return out
    ok, _msg, _links = _auth_mutate_sso_links(_mark, tag="sso_use")
    return bool(ok and changed)

def _build_sso_link_payload(body: dict | None, *, require_reauth: bool = True, headers=None, client_ip: str | None = None) -> tuple[dict, int]:
    if not _auth_enabled() or (not _auth_hashes_present(AUTH_CFG)):
        return {"ok": False, "error": "网页登录鉴权未启用或未完成配置"}, 400
    src = body if isinstance(body, dict) else {}
    subject = str(src.get("username") or "-")
    if require_reauth:
        reauth_ok = _auth_check_userpass(str(src.get("username") or ""), str(src.get("password") or ""))
        if not reauth_ok and headers is not None and headers.get("Authorization"):
            reauth_ok = _auth_check_basic_header(headers.get("Authorization"))
        if not reauth_ok:
            _op_log("login-link-create", "", actor=subject, ip=str(client_ip or "-"), ok=False)
            return {"ok": False, "error": "账号或密码错误"}, 401
    next_path = str(src.get("next") or "/").strip() or "/"
    if not next_path.startswith("/") or next_path.startswith("//"):
        next_path = "/"
    name = str(src.get("name") or "").strip()
    if not name:
        name = "SSO " + time.strftime("%Y-%m-%d %H:%M:%S")
    now_wall = time.time()
    expires_at, expiry_err = _sso_expiry_from_payload(src, now_wall=now_wall)
    if expiry_err:
        return {"ok": False, "error": expiry_err}, 400
    single_use = _to_bool(src.get("single_use"), False)
    check = secrets.token_urlsafe(16)
    def _add_link(links):
        links.append({
            "name": name,
            "check": check,
            "enabled": True,
            "created_ts": now_wall,
            "expires_at": expires_at,
            "single_use": single_use,
            "used_ts": 0.0,
            "used_count": 0,
            "next": next_path,
        })
        return links[-64:]
    ok, msg, links = _auth_mutate_sso_links(_add_link, tag="sso_create")
    if not ok:
        return {"ok": False, "error": msg, "links": links}, 500
    path_url = _auth_sso_path(check, next_path=next_path)
    return {
        "ok": True,
        "check": check,
        "name": name,
        "path": path_url,
        "expires_at": expires_at,
        "expires_in_sec": None if expires_at <= 0 else int(max(0.0, expires_at - now_wall)),
        "single_use": single_use,
        "next": next_path,
        "links": links,
    }, 200

def _auth_mutate_sso_links(mutator, *, tag: str = "sso") -> tuple[bool, str, list[dict]]:
    if not APP_CONFIG_PATH:
        return False, "config path missing", _auth_sso_public_links()
    try:
        with auth_sso_lock:
            cfg = load_app_config(APP_CONFIG_PATH)
            auth = cfg.setdefault("auth", {})
            if not isinstance(auth, dict):
                auth = {}
                cfg["auth"] = auth
            links = _prune_expired_sso_links(auth.get("sso_links"))
            auth["sso_links"] = _prune_expired_sso_links(mutator(list(links)))
            cfg, guard_err = _prepare_security_cfg_for_save(cfg)
            if guard_err:
                return False, guard_err, _auth_sso_public_links()
            b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag=tag)
            if not b_ok:
                return False, f"backup failed: {backup_path}", _auth_sso_public_links()
            ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
            if not ok:
                return False, msg, _auth_sso_public_links()
            cfg_loaded = load_app_config(APP_CONFIG_PATH)
            r_ok, r_msg = reload_runtime_config(cfg_loaded)
            if not r_ok:
                return False, f"reload failed: {r_msg}", _auth_sso_public_links()
            auth_loaded = cfg_loaded.get("auth") if isinstance(cfg_loaded, dict) else None
            return True, "ok", _auth_sso_public_links(auth_loaded if isinstance(auth_loaded, dict) else None)
    except Exception as e:
        return False, str(e), _auth_sso_public_links()

def _auth_check_basic_header(header_value: str | None) -> bool:
    if not _auth_enabled():
        return True
    raw = str(header_value or "").strip()
    if not raw.startswith("Basic "):
        return False
    token = raw[6:].strip()
    if not token:
        return False
    try:
        text = base64.b64decode(token).decode("utf-8", errors="replace")
    except Exception:
        return False
    if ":" not in text:
        return False
    user, pwd = text.split(":", 1)
    return _auth_check_userpass(user, pwd)

def _rate_key(scope: str, ip: str | None, subject: str | None = "") -> str:
    return f"{str(scope or 'default')}:{str(ip or '-')}:{str(subject or '-')[:96]}"

def _rate_limited(scope: str, ip: str | None, subject: str | None = "", *, limit: int = 8, window_sec: int = 300, block_sec: int = 900) -> tuple[bool, int]:
    now_wall = time.time()
    key = _rate_key(scope, ip, subject)
    with security_rate_lock:
        st = security_rate_state.get(key) or {"fails": [], "blocked_until": 0.0}
        blocked_until = float(st.get("blocked_until") or 0.0)
        if blocked_until > now_wall:
            return True, int(max(1.0, blocked_until - now_wall))
        fails = [float(x) for x in (st.get("fails") or []) if now_wall - float(x) <= float(window_sec)]
        st["fails"] = fails
        security_rate_state[key] = st
        if len(security_rate_state) > 4096:
            stale = [k for k, v in security_rate_state.items()
                     if float((v or {}).get("blocked_until") or 0.0) <= now_wall and not (v or {}).get("fails")]
            for k in stale[:2048]:
                security_rate_state.pop(k, None)
        if len(fails) >= int(limit):
            st["blocked_until"] = now_wall + float(block_sec)
            return True, int(block_sec)
    return False, 0

def _rate_note(scope: str, ip: str | None, subject: str | None = "", *, success: bool, limit: int = 8, window_sec: int = 300, block_sec: int = 900) -> None:
    key = _rate_key(scope, ip, subject)
    now_wall = time.time()
    with security_rate_lock:
        if success:
            security_rate_state.pop(key, None)
            return
        st = security_rate_state.get(key) or {"fails": [], "blocked_until": 0.0}
        fails = [float(x) for x in (st.get("fails") or []) if now_wall - float(x) <= float(window_sec)]
        fails.append(now_wall)
        st["fails"] = fails
        if len(fails) >= int(limit):
            st["blocked_until"] = now_wall + float(block_sec)
            _op_log("rate-limit", f"scope={scope} subject={str(subject or '-')[:96]} blocked={block_sec}s fails={len(fails)}", ip=str(ip or "-"), ok=False)
        security_rate_state[key] = st
        if len(security_rate_state) > 4096:
            ordered = sorted(security_rate_state.items(), key=lambda kv: max([float(x) for x in ((kv[1] or {}).get("fails") or [0.0])] + [float((kv[1] or {}).get("blocked_until") or 0.0)]), reverse=True)
            security_rate_state.clear()
            security_rate_state.update(dict(ordered[:2048]))

def _auth_cookie_parse(cookie_header: str | None, key: str) -> str:
    raw = str(cookie_header or "")
    if not raw:
        return ""
    for part in raw.split(";"):
        p = str(part or "").strip()
        if not p or "=" not in p:
            continue
        k, v = p.split("=", 1)
        if k.strip() == key:
            return v.strip()
    return ""

def _auth_cleanup_sessions(now_wall: float | None = None) -> None:
    now_wall = float(now_wall or time.time())
    with auth_session_lock:
        stale = [tok for tok, exp in auth_sessions.items() if float(exp or 0.0) <= now_wall]
        for tok in stale:
            auth_sessions.pop(tok, None)

def _auth_issue_session() -> str:
    now_wall = time.time()
    tok_src = f"{now_wall}:{random.random()}:{auth_session_secret}:{os.getpid()}"
    token = hashlib.sha256(tok_src.encode("utf-8", errors="ignore")).hexdigest().lower()
    exp = now_wall + float(AUTH_SESSION_TTL_SEC)
    with auth_session_lock:
        auth_sessions[token] = exp
        if len(auth_sessions) > 4096:
            stale = [tok for tok, ts in auth_sessions.items() if float(ts or 0.0) <= now_wall]
            for tok in stale:
                auth_sessions.pop(tok, None)
            if len(auth_sessions) > 4096:
                # keep most recently expiring sessions
                keep = sorted(auth_sessions.items(), key=lambda kv: float(kv[1]), reverse=True)[:2048]
                auth_sessions.clear()
                auth_sessions.update({k: v for k, v in keep})
    return token

def _auth_check_session_cookie(cookie_header: str | None, *, refresh: bool = True) -> bool:
    if not _auth_enabled():
        return True
    token = _auth_cookie_parse(cookie_header, AUTH_SESSION_COOKIE)
    if not token:
        return False
    now_wall = time.time()
    with auth_session_lock:
        exp = auth_sessions.get(token)
        if not exp or float(exp) <= now_wall:
            auth_sessions.pop(token, None)
            return False
        if refresh:
            auth_sessions[token] = now_wall + float(AUTH_SESSION_TTL_SEC)
    return True

def _request_same_origin(headers) -> bool:
    host = str(headers.get("Host") or "").strip().lower()
    if not host:
        return True
    for header_name in ("Origin", "Referer"):
        raw = str(headers.get(header_name) or "").strip()
        if not raw:
            continue
        try:
            from urllib.parse import urlparse as _urlparse
            parsed = _urlparse(raw)
            if parsed.netloc and parsed.netloc.lower() != host:
                return False
        except Exception:
            return False
    return True

def _page_api_header_ok(headers) -> bool:
    value = str(headers.get(PAGE_API_HEADER) or "").strip()
    return value == PAGE_API_HEADER_VALUE

def _hw_safe_iface(iface: str) -> str | None:
    name = str(iface or "").strip()
    if not name:
        return None
    if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,32}", name):
        return None
    iftypes = _sniff_iface_candidates()
    if name not in iftypes:
        return None
    return name

def _hw_cmd_result(cmd: str, timeout: int = 8) -> dict:
    try:
        proc = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        out = (proc.stdout or "").strip()
        err = (proc.stderr or "").strip()
        ok = (proc.returncode == 0)
        return {
            "ok": ok,
            "cmd": cmd,
            "code": int(proc.returncode),
            "stdout": out,
            "stderr": err,
        }
    except Exception as e:
        return {
            "ok": False,
            "cmd": cmd,
            "code": -1,
            "stdout": "",
            "stderr": str(e),
        }

_HOST_CPU_LOCK = Lock()
_HOST_CPU_CACHE: tuple[float, float] | None = None


def _read_proc_cpu_totals() -> tuple[float, float] | None:
    try:
        with open("/proc/stat", "r", encoding="utf-8", errors="ignore") as f:
            first = f.readline().strip()
        if not first.startswith("cpu "):
            return None
        parts = [float(x) for x in first.split()[1:] if x.strip()]
        if len(parts) < 4:
            return None
        idle = parts[3] + (parts[4] if len(parts) > 4 else 0.0)
        total = float(sum(parts))
        return idle, total
    except Exception:
        return None


def _host_cpu_percent() -> float | None:
    global _HOST_CPU_CACHE
    snap = _read_proc_cpu_totals()
    if snap:
        idle, total = snap
        with _HOST_CPU_LOCK:
            prev = _HOST_CPU_CACHE
            _HOST_CPU_CACHE = (idle, total)
        if prev:
            idle_prev, total_prev = prev
            total_delta = total - total_prev
            idle_delta = idle - idle_prev
            if total_delta > 0:
                busy = max(0.0, min(1.0, 1.0 - (idle_delta / total_delta)))
                return round(busy * 100.0, 1)
    try:
        load1 = os.getloadavg()[0]
        cpu_count = max(1, int(os.cpu_count() or 1))
        return round(max(0.0, min(100.0, (float(load1) / float(cpu_count)) * 100.0)), 1)
    except Exception:
        return None


def _host_mem_stats() -> dict:
    try:
        data: dict[str, int] = {}
        with open("/proc/meminfo", "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                if ":" not in line:
                    continue
                k, v = line.split(":", 1)
                try:
                    data[k.strip()] = int(v.strip().split()[0])
                except Exception:
                    continue
        total_kb = int(data.get("MemTotal") or 0)
        avail_kb = int(data.get("MemAvailable") or data.get("MemFree") or 0)
        if total_kb <= 0:
            return {"percent": None, "used_mb": None, "total_mb": None}
        used_kb = max(0, total_kb - avail_kb)
        return {
            "percent": round((used_kb / total_kb) * 100.0, 1),
            "used_mb": int(round(used_kb / 1024.0)),
            "total_mb": int(round(total_kb / 1024.0)),
        }
    except Exception:
        return {"percent": None, "used_mb": None, "total_mb": None}


def _host_temperature_parse_text(text: str) -> float | None:
    m = re.search(r"temp\s*=\s*(-?\d+(?:\.\d+)?)\s*'?\s*c", str(text or ""), re.I)
    if not m:
        m = re.search(r"^\s*(-?\d+(?:\.\d+)?)\s*(?:'?\s*c)?\s*$", str(text or ""), re.I)
    if not m:
        return None
    try:
        value = float(m.group(1))
        if -40.0 <= value <= 140.0:
            return round(value, 1)
    except Exception:
        pass
    return None


def _host_temperature_from_vcgencmd(*extra_args: str) -> float | None:
    try:
        out = subprocess.run(["vcgencmd", "measure_temp", *extra_args], capture_output=True, text=True, timeout=3)
        text = out.stdout or (out.stderr if int(getattr(out, "returncode", 1) or 0) == 0 else "")
        return _host_temperature_parse_text(text)
    except Exception:
        return None


def _host_temperature_from_vcgencmd_pmic() -> float | None:
    return _host_temperature_from_vcgencmd("pmic")


def _host_temperature_value_from_file(path: str, *, min_c: float = -40.0, max_c: float = 140.0) -> float | None:
    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            raw = f.read().strip()
        if not raw:
            return None
        value = float(raw)
        if abs(value) > 250:
            value = value / 1000.0
        if min_c <= value <= max_c:
            return round(value, 1)
    except Exception:
        pass
    return None


def _host_temperature_best_candidate(candidates: list[tuple[int, float, str]]) -> float | None:
    if not candidates:
        return None
    candidates.sort(key=lambda item: (item[0], abs(item[1] - 55.0), item[1]))
    best = candidates[0]
    if best[1] >= 95.0:
        for item in candidates[1:]:
            if item[1] < 95.0 and item[0] <= best[0] + 8:
                best = item
                break
    return round(best[1], 1)


def _host_temperature_candidates_from_thermal(root: str = "/sys/class/thermal") -> list[tuple[int, float, str]]:
    candidates: list[tuple[int, float, str]] = []
    try:
        names = sorted(os.listdir(root))
    except Exception:
        return candidates
    for name in names:
        if not name.startswith("thermal_zone"):
            continue
        dirpath = os.path.join(root, name)
        temp_path = os.path.join(dirpath, "temp")
        if not os.path.exists(temp_path):
            continue
        label = ""
        try:
            with open(os.path.join(dirpath, "type"), "r", encoding="utf-8", errors="ignore") as f:
                label = f.read().strip().lower()
        except Exception:
            label = ""
        value = _host_temperature_value_from_file(temp_path)
        if value is None:
            continue
        score = 12
        if any(k in label for k in ("cpu", "soc", "board", "thermal", "system")):
            score -= 10
        if any(k in label for k in ("max", "crit", "limit", "trip", "hot")):
            score += 12
        if value >= 95.0 and not any(k in label for k in ("cpu", "soc", "board")):
            score += 8
        candidates.append((score, float(value), temp_path))
    return candidates


def _host_temperature_candidates_from_hwmon(root: str = "/sys/class/hwmon") -> list[tuple[int, float, str]]:
    candidates: list[tuple[int, float, str]] = []
    try:
        names = sorted(os.listdir(root))
    except Exception:
        return candidates
    for name in names:
        if not name.startswith("hwmon"):
            continue
        dirpath = os.path.join(root, name)
        device_label = ""
        try:
            with open(os.path.join(dirpath, "name"), "r", encoding="utf-8", errors="ignore") as f:
                device_label = f.read().strip().lower()
        except Exception:
            device_label = ""
        try:
            files = sorted(os.listdir(dirpath))
        except Exception:
            continue
        for fname in files:
            if not re.match(r"^temp\d+_input$", fname):
                continue
            path = os.path.join(dirpath, fname)
            label = device_label
            label_name = fname[:-6] + "_label"
            try:
                with open(os.path.join(dirpath, label_name), "r", encoding="utf-8", errors="ignore") as f:
                    label = (f.read().strip().lower() or device_label)
            except Exception:
                pass
            value = _host_temperature_value_from_file(path)
            if value is None:
                continue
            score = 20
            if any(k in label for k in ("cpu", "package", "soc", "board", "thermal", "system", "tctl", "tdie")):
                score -= 10
            if any(k in label for k in ("max", "crit", "limit", "trip", "hot")):
                score += 12
            if value >= 95.0 and not any(k in label for k in ("cpu", "package", "soc", "board", "tctl", "tdie")):
                score += 8
            candidates.append((score, float(value), path))
    return candidates


def _host_temperature_from_w1(root: str = "/sys/bus/w1/devices") -> float | None:
    candidates: list[tuple[int, float, str]] = []
    try:
        names = sorted(os.listdir(root))
    except Exception:
        return None
    for name in names:
        if not name.startswith("28-"):
            continue
        path = os.path.join(root, name, "temperature")
        value = _host_temperature_value_from_file(path, min_c=-55.0, max_c=125.0)
        if value is None:
            continue
        try:
            with open(path, "r", encoding="utf-8", errors="ignore") as f:
                if f.read().strip() == "85000":
                    continue
        except Exception:
            pass
        candidates.append((30, float(value), path))
    return _host_temperature_best_candidate(candidates)


def _host_temperature_from_sysfs(*roots: str) -> float | None:
    candidates: list[tuple[int, float, str]] = []
    for root in roots:
        root_text = str(root or "")
        base = os.path.basename(os.path.normpath(root_text)).lower()
        if base == "thermal":
            candidates.extend(_host_temperature_candidates_from_thermal(root_text))
        elif base == "hwmon":
            candidates.extend(_host_temperature_candidates_from_hwmon(root_text))
        elif base == "devices" and "w1" in root_text:
            value = _host_temperature_from_w1(root_text)
            if value is not None:
                candidates.append((30, float(value), root_text))
    return _host_temperature_best_candidate(candidates)


def _host_temperature_read() -> tuple[float | None, str]:
    source = str(METRICS_CFG.get("temperature_source") or "auto")
    if source == "off":
        return None, "off"
    probes = []
    if source == "vcgencmd":
        probes = [
            ("vcgencmd", _host_temperature_from_vcgencmd),
            ("vcgencmd_pmic", _host_temperature_from_vcgencmd_pmic),
        ]
    elif source == "vcgencmd_pmic":
        probes = [("vcgencmd_pmic", _host_temperature_from_vcgencmd_pmic)]
    elif source == "thermal_zone":
        probes = [("thermal_zone", lambda: _host_temperature_from_sysfs("/sys/class/thermal"))]
    elif source == "hwmon":
        probes = [("hwmon", lambda: _host_temperature_from_sysfs("/sys/class/hwmon"))]
    elif source == "w1":
        probes = [("w1", _host_temperature_from_w1)]
    else:
        probes = [
            ("vcgencmd", _host_temperature_from_vcgencmd),
            ("vcgencmd_pmic", _host_temperature_from_vcgencmd_pmic),
            ("thermal_zone", lambda: _host_temperature_from_sysfs("/sys/class/thermal")),
            ("hwmon", lambda: _host_temperature_from_sysfs("/sys/class/hwmon")),
            ("w1", _host_temperature_from_w1),
        ]
    for key, probe in probes:
        value = probe()
        if value is not None:
            return value, key
    return None, source


def _host_temperature_c() -> float | None:
    value, _source = _host_temperature_read()
    return value


def _host_temperature_source_label(source: str | None) -> str:
    key = str(source or "").strip().lower().replace("-", "_")
    labels = {
        "auto": "自动",
        "vcgencmd": "vcgencmd",
        "vcgencmd_pmic": "vcgencmd pmic",
        "thermal_zone": "/sys/class/thermal",
        "hwmon": "/sys/class/hwmon",
        "w1": "DS18B20 / w1",
        "off": "关闭",
    }
    return labels.get(key, "自动")


def _host_local_ips() -> list[str]:
    ips: list[str] = []
    try:
        text = subprocess.run("hostname -I", shell=True, capture_output=True, text=True, timeout=3).stdout or ""
        for part in text.split():
            s = part.strip()
            if s and s not in ips:
                ips.append(s)
    except Exception:
        pass
    if not ips:
        try:
            host = socket.gethostname()
            for item in socket.getaddrinfo(host, None):
                addr = str(item[4][0] or "").strip()
                if addr and not addr.startswith("127.") and addr != "::1" and addr not in ips:
                    ips.append(addr)
        except Exception:
            pass
    return ips[:12]


def _host_resource_snapshot() -> dict:
    temperature_c, temperature_source = _host_temperature_read()
    mem = _host_mem_stats()
    uptime_sec = None
    try:
        with open("/proc/uptime", "r", encoding="utf-8", errors="ignore") as f:
            uptime_sec = int(float((f.read().strip().split() or ["0"])[0]))
    except Exception:
        uptime_sec = None
    load1 = load5 = load15 = None
    try:
        load1, load5, load15 = os.getloadavg()
    except Exception:
        pass
    return {
        "hostname": str(platform.node() or os.environ.get("COMPUTERNAME") or "host"),
        "cpu_percent": _host_cpu_percent(),
        "cpu_count": int(os.cpu_count() or 1),
        "mem_percent": mem.get("percent"),
        "mem_used_mb": mem.get("used_mb"),
        "mem_total_mb": mem.get("total_mb"),
        "temperature_c": temperature_c,
        "temperature_source": temperature_source,
        "temperature_source_label": _host_temperature_source_label(temperature_source),
        "local_ips": _host_local_ips(),
        "load1": (None if load1 is None else round(float(load1), 2)),
        "load5": (None if load5 is None else round(float(load5), 2)),
        "load15": (None if load15 is None else round(float(load15), 2)),
        "uptime_sec": uptime_sec,
    }

def _host_metrics_ensure_store() -> None:
    parent = os.path.dirname(HOST_METRICS_PATH)
    if parent:
        os.makedirs(parent, exist_ok=True)
    if not os.path.exists(HOST_METRICS_PATH):
        with open(HOST_METRICS_PATH, "a", encoding="utf-8"):
            pass

def _host_metric_point() -> dict:
    host = _host_resource_snapshot()
    aps, _seq, aps_total = _ap_snapshot()
    cpu_count = max(1, int(host.get("cpu_count") or os.cpu_count() or 1))
    load1 = host.get("load1")
    load_percent = None
    try:
        if load1 is not None:
            load_percent = round(max(0.0, min(100.0, (float(load1) / float(cpu_count)) * 100.0)), 1)
    except Exception:
        load_percent = None
    return {
        "ts": time.time(),
        "cpu": host.get("cpu_percent"),
        "mem": host.get("mem_percent"),
        "temp": host.get("temperature_c"),
        "load": load_percent,
        "load1": load1,
        "ap": int(aps_total if aps_total is not None else len(aps)),
    }

def _host_metrics_read_all() -> list[dict]:
    _host_metrics_ensure_store()
    rows: list[dict] = []
    try:
        with open(HOST_METRICS_PATH, "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if isinstance(obj, dict) and obj.get("ts") is not None:
                    rows.append(obj)
    except Exception:
        return []
    rows.sort(key=lambda x: float(x.get("ts") or 0.0))
    return rows

def _host_metrics_prune_and_write(rows: list[dict]) -> None:
    retention = int(METRICS_CFG.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT)
    cutoff = time.time() - max(1, retention) * 86400.0
    kept = [x for x in rows if float(x.get("ts") or 0.0) >= cutoff]
    tmp_path = HOST_METRICS_PATH + ".tmp"
    _host_metrics_ensure_store()
    with open(tmp_path, "w", encoding="utf-8") as f:
        for item in kept:
            f.write(json.dumps(item, ensure_ascii=False, separators=(",", ":")) + "\n")
    os.replace(tmp_path, HOST_METRICS_PATH)

def _host_metrics_sample(force: bool = False) -> dict | None:
    global host_metrics_last_sample_wall
    if not bool(METRICS_CFG.get("enabled")):
        return None
    now = time.time()
    with host_metrics_lock:
        if (not force) and host_metrics_last_sample_wall and (now - host_metrics_last_sample_wall) < HOST_METRICS_SAMPLE_SEC:
            return None
        host_metrics_last_sample_wall = now
    point = _host_metric_point()
    with host_metrics_lock:
        rows = _host_metrics_read_all()
        rows.append(point)
        _host_metrics_prune_and_write(rows)
    return point

def _decimate_points(rows: list[dict], max_points: int = 720) -> list[dict]:
    if len(rows) <= max_points:
        return rows
    step = max(1, int(math.ceil(len(rows) / float(max_points))))
    out = rows[::step]
    if rows and out[-1] is not rows[-1]:
        out.append(rows[-1])
    return out

def _host_metrics_payload(window_sec: int = 24 * 3600) -> dict:
    try:
        window_sec = max(3600, min(7 * 86400, int(window_sec)))
    except Exception:
        window_sec = 24 * 3600
    enabled = bool(METRICS_CFG.get("enabled"))
    if enabled:
        try:
            _host_metrics_sample(force=False)
        except Exception:
            pass
    cutoff = time.time() - float(window_sec)
    if enabled:
        with host_metrics_lock:
            rows = [x for x in _host_metrics_read_all() if float(x.get("ts") or 0.0) >= cutoff]
    else:
        rows = []
    return {
        "ok": True,
        "enabled": enabled,
        "window_sec": int(window_sec),
        "retention_days": int(METRICS_CFG.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT),
        "temperature_source": str(METRICS_CFG.get("temperature_source") or "auto"),
        "temperature_source_label": _host_temperature_source_label(METRICS_CFG.get("temperature_source")),
        "sample_interval_sec": int(HOST_METRICS_SAMPLE_SEC),
        "store_path": HOST_METRICS_PATH,
        "count": len(rows),
        "items": _decimate_points(rows, max_points=900),
    }

def host_metrics_loop() -> None:
    if bool(METRICS_CFG.get("enabled")):
        try:
            _host_metrics_sample(force=True)
        except Exception as e:
            _log(f"[WARN] host metrics initial sample failed: {e}")
    while True:
        try:
            _host_metrics_sample(force=False)
        except Exception as e:
            _log(f"[WARN] host metrics sample failed: {e}")
        time.sleep(HOST_METRICS_SAMPLE_SEC)


def _hw_status_snapshot() -> dict:
    items = _iface_options_snapshot()
    host = _host_resource_snapshot()
    host["ifaces"] = items
    return {
        "items": items,
        "active_iface": str(sniff_iface_name or ""),
        "sniff_state": _sniff_health_meta(time.monotonic(), time.time()),
        "current_channel": int(current_channel or 0),
        "scan_wifi_fast": bool(SCAN_WIFI_FAST),
        "wifi_fast_supported": WIFI_FAST_SUPPORTED,
        "wifi_fast_msg": str(WIFI_FAST_SUPPORT_MSG or ""),
        "host": host,
    }

def _hw_execute_task(task: dict) -> dict:
    global current_channel
    op = str(task.get("op") or "").strip().lower()
    iface = _hw_safe_iface(task.get("iface"))
    if op == "status":
        return {"ok": True, "data": _hw_status_snapshot()}
    if op == "list_ifaces":
        return {"ok": True, "items": _iface_options_snapshot(), "active_iface": str(sniff_iface_name or "")}
    if op == "iw_dev":
        return _hw_cmd_result("iw dev", timeout=8)
    if op == "iw_info":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        return _hw_cmd_result(f"iw dev {iface} info", timeout=8)
    if op == "iw_link":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        return _hw_cmd_result(f"iw dev {iface} link", timeout=8)
    if op == "set_monitor":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        steps = [
            _hw_cmd_result(f"ip link set {iface} down", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set type monitor", timeout=8),
            _hw_cmd_result(f"ip link set {iface} up", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set power_save off", timeout=8),
        ]
        return {"ok": all(s.get("ok") for s in steps), "steps": steps}
    if op == "set_managed":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        steps = [
            _hw_cmd_result(f"ip link set {iface} down", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set type managed", timeout=8),
            _hw_cmd_result(f"ip link set {iface} up", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set power_save off", timeout=8),
        ]
        return {"ok": all(s.get("ok") for s in steps), "steps": steps}
    if op == "restart_iface":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        steps = [
            _hw_cmd_result(f"ip link set {iface} down", timeout=8),
            _hw_cmd_result(f"ip link set {iface} up", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set power_save off", timeout=8),
        ]
        return {"ok": all(s.get("ok") for s in steps), "steps": steps}
    if op == "set_channel":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        try:
            ch = int(task.get("channel"))
        except Exception:
            return {"ok": False, "error": "invalid channel"}
        if ch < 1 or ch > 196:
            return {"ok": False, "error": "channel out of range"}
        r = _hw_cmd_result(f"iw dev {iface} set channel {ch}", timeout=8)
        if r.get("ok"):
            current_channel = ch
        return r
    if op == "restart_program":
        ok, msg = _schedule_self_restart(list(sys.argv[1:]))
        return {"ok": bool(ok), "msg": msg}
    return {"ok": False, "error": f"unsupported op: {op}"}

def _hw_worker_loop() -> None:
    while True:
        task = hw_task_queue.get()
        if not isinstance(task, dict):
            continue
        rsp_q = task.get("_rsp_q")
        try:
            out = _hw_execute_task(task)
        except Exception as e:
            out = {"ok": False, "error": str(e)}
        if isinstance(rsp_q, queue.Queue):
            try:
                rsp_q.put_nowait(out)
            except Exception:
                pass

def start_hw_worker() -> None:
    global hw_worker_started
    with hw_worker_lock:
        if hw_worker_started:
            return
        hw_worker_started = True
    Thread(target=_hw_worker_loop, daemon=True).start()

def _hw_submit_task(task: dict, timeout_sec: float = 12.0) -> dict:
    start_hw_worker()
    rsp_q: "queue.Queue[dict]" = queue.Queue(maxsize=1)
    item = dict(task or {})
    item["_rsp_q"] = rsp_q
    try:
        hw_task_queue.put_nowait(item)
    except queue.Full:
        return {"ok": False, "error": "hardware helper busy"}
    try:
        out = rsp_q.get(timeout=max(0.5, float(timeout_sec)))
    except Exception:
        return {"ok": False, "error": "hardware helper timeout"}
    return out if isinstance(out, dict) else {"ok": False, "error": "invalid helper response"}

