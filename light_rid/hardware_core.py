from light_rid.platform_compat import (
    local_group_exists as _platform_local_group_exists,
    local_user_exists as _platform_local_user_exists,
    username_for_uid as _platform_username_for_uid,
)


def _wecom_send_text(key: str, content: str, timeout_sec: int = 8) -> tuple[bool, str]:
    body = json.dumps({
        "msgtype": "text",
        "text": {"content": content},
    }, ensure_ascii=False).encode("utf-8")
    req = urllib.request.Request(
        _wecom_webhook_url(key),
        data=body,
        headers={"Content-Type": "application/json; charset=utf-8"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_sec) as resp:
            raw = (resp.read() or b"").decode("utf-8", errors="replace")
    except urllib.error.URLError as e:
        return False, f"network error: {e}"
    except Exception as e:
        return False, f"send error: {e}"
    try:
        obj = json.loads(raw) if raw else {}
    except Exception:
        obj = {}
    if isinstance(obj, dict) and int(obj.get("errcode", -1)) == 0:
        return True, raw or "ok"
    return False, raw or "unknown response"

def _notify_queue_put(item: dict) -> None:
    try:
        notify_queue.put_nowait(item)
    except queue.Full:
        _log("[WARN] notification queue full, dropping one message")

def _notify_online_text(e: dict, event_title: str, now_wall: float) -> str:
    def _f(v, fmt_str: str, unit: str = "N/A") -> str:
        if v is None:
            return "N/A"
        try:
            return f"{v:{fmt_str}}{unit if unit != 'N/A' else ''}"
        except Exception:
            return str(v)
    sn = str(e.get("sn",""))
    model = str(e.get("model","N/A"))
    it = str(e.get("id_type",""))
    mac = str(e.get("src_mac",""))
    ch = e.get("last_ch") or 0
    ch_s = f"{'~' if e.get('ch_assumed') else ''}ch{ch}" if ch else "ch?"
    rssi = _f(e.get("rssi"), "d", "dBm")
    lat = e.get("lat")
    lon = e.get("lon")
    loc_s = f"{lat:.6f}, {lon:.6f}" if lat is not None and lon is not None else "N/A"
    alt_s = _f(e.get("alt"), ".1f", "m")
    spd_s = _f(e.get("speed"), ".1f", "m/s")
    vsp_s = _f(e.get("vspeed"), ".1f", "m/s")
    pkts = int(e.get("pkt_count") or 0)
    ts_s = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now_wall))
    alarm_hits = e.get("alarm_zone_hits")
    if not isinstance(alarm_hits, list):
        alarm_hits = _alarm_zone_names_for_point(lat, lon)
    alarm_s = ""
    if alarm_hits:
        alarm_s = "\n报警区域: " + "、".join(str(x) for x in alarm_hits if str(x).strip())
    return (
        f"[RID{event_title}] {ts_s}\n"
        f"SN: {sn}\n"
        f"机型/ID: {model} / {it}\n"
        f"MAC/信道/信号: {mac} / {ch_s} / {rssi}\n"
        f"位置: {loc_s}  高程: {alt_s}\n"
        f"速度: {spd_s}  垂速: {vsp_s}  包数: {pkts}"
        f"{alarm_s}"
    )

def _notify_zone_alarm_text(e: dict, zone_names: list[str], now_wall: float) -> str:
    sn = str(e.get("sn", ""))
    model = str(e.get("model", "N/A"))
    lat = e.get("lat")
    lon = e.get("lon")
    try:
        loc_s = f"{float(lat):.6f}, {float(lon):.6f}" if lat is not None and lon is not None else "N/A"
    except Exception:
        loc_s = "N/A"
    alt = e.get("alt")
    spd = e.get("speed")
    try:
        alt_s = f"{float(alt):.1f}m" if alt is not None else "N/A"
    except Exception:
        alt_s = "N/A"
    try:
        spd_s = f"{float(spd):.1f}m/s" if spd is not None else "N/A"
    except Exception:
        spd_s = "N/A"
    ts_s = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now_wall))
    zones = "、".join(str(x) for x in (zone_names or []) if str(x).strip()) or "报警区域"
    return (
        f"[RID区域告警] {ts_s}\n"
        f"SN: {sn}\n"
        f"机型: {model}\n"
        f"进入区域: {zones}\n"
        f"位置: {loc_s}  高程: {alt_s}\n"
        f"速度: {spd_s}"
    )

def _notify_lost_text(e: dict, age_sec: float, now_wall: float) -> str:
    sn = str(e.get("sn", ""))
    model = str(e.get("model", "N/A"))
    mac = str(e.get("src_mac") or "-")
    ts_s = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now_wall))
    try:
        age_s = f"{float(age_sec):.0f}s"
    except Exception:
        age_s = "N/A"
    return (
        f"[RID离线] {ts_s}\n"
        f"SN: {sn}\n"
        f"机型: {model}\n"
        f"MAC: {mac}\n"
        f"未收到数据: {age_s}"
    )

def _notification_kind(kind: str | None) -> str:
    k = str(kind or "info").strip().lower()
    return k if k in ("info", "ok", "warn") else "info"

def _notification_add(text: str, kind: str = "info", source: str = "server") -> dict | None:
    global notification_seq
    msg = str(text or "").strip()
    if not msg:
        return None
    if len(msg) > 2000:
        msg = msg[:1997] + "..."
    with notification_lock:
        notification_seq += 1
        item = {
            "id": notification_seq,
            "text": msg,
            "kind": _notification_kind(kind),
            "source": str(source or "server")[:40],
            "ts": int(time.time() * 1000),
        }
        notification_items.appendleft(item)
        return dict(item)

def _notification_payload(limit: int = NOTIFICATION_CENTER_MAX) -> dict:
    try:
        limit = int(limit)
    except Exception:
        limit = NOTIFICATION_CENTER_MAX
    limit = max(1, min(NOTIFICATION_CENTER_MAX, limit))
    with notification_lock:
        items = [dict(x) for x in list(notification_items)[:limit]]
        seq = int(notification_seq)
    return {"ok": True, "seq": seq, "count": len(items), "items": items}

def _notification_delete(item_id) -> bool:
    target = str(item_id or "").strip()
    if not target:
        return False
    with notification_lock:
        before = len(notification_items)
        kept = [x for x in notification_items if str((x or {}).get("id") or "") != target]
        notification_items.clear()
        notification_items.extend(kept[:NOTIFICATION_CENTER_MAX])
        return len(notification_items) != before

def _notification_clear() -> int:
    with notification_lock:
        n = len(notification_items)
        notification_items.clear()
        return n

def _notify_worker_loop() -> None:
    while True:
        item = notify_queue.get()
        try:
            if not isinstance(item, dict):
                continue
            if item.get("type") != "wecom_text":
                continue
            key = str(item.get("key") or "")
            content = str(item.get("content") or "")
            if not key or not content:
                continue
            ok, resp = _wecom_send_text(key, content, timeout_sec=int(item.get("timeout_sec") or 8))
            if not ok:
                _log(f"[WARN] WeCom notification send failed: {resp}")
        except Exception as e:
            _log(f"[WARN] 通知线程异常: {e}")
        finally:
            try:
                notify_queue.task_done()
            except Exception:
                pass

def start_notify_worker() -> None:
    global notify_worker_started
    with notify_worker_lock:
        if notify_worker_started:
            return
        Thread(target=_notify_worker_loop, daemon=True).start()
        notify_worker_started = True

def queue_online_notification(e: dict, event_title: str, now_wall: float | None = None) -> bool:
    if not NOTIFY_CFG.get("enabled"):
        return False
    targets = _notify_wecom_targets(NOTIFY_CFG)
    if not targets:
        return False
    now_wall = float(now_wall or time.time())
    content = _notify_online_text(e, event_title, now_wall)
    for item in targets:
        _notify_queue_put({
            "type": "wecom_text",
            "key": str(item.get("key") or "").strip(),
            "content": content,
            "timeout_sec": int(NOTIFY_CFG.get("send_timeout_sec") or 8),
        })
    return True

def queue_zone_alarm_notification(e: dict, zone_names: list[str], now_wall: float | None = None) -> bool:
    if not NOTIFY_CFG.get("enabled"):
        return False
    targets = _notify_wecom_targets(NOTIFY_CFG)
    if not targets:
        return False
    now_wall = float(now_wall or time.time())
    content = _notify_zone_alarm_text(e, zone_names, now_wall)
    for item in targets:
        _notify_queue_put({
            "type": "wecom_text",
            "key": str(item.get("key") or "").strip(),
            "content": content,
            "timeout_sec": int(NOTIFY_CFG.get("send_timeout_sec") or 8),
        })
    return True

def send_test_notification_from_config(cfg: dict | None = None) -> tuple[bool, str]:
    notify_cfg = _normalize_notify_cfg(cfg) if isinstance(cfg, dict) else dict(NOTIFY_CFG)
    if not notify_cfg.get("enabled"):
        return False, "notify disabled"
    targets = _notify_wecom_targets(notify_cfg)
    if not targets:
        return False, "missing wecom webhook"
    now_wall = time.time()
    test_e = {
        "sn": "TEST-RID-ONLINE",
        "model": "Config/Test",
        "id_type": "Test",
        "src_mac": "00:11:22:33:44:55",
        "last_ch": current_channel or 6,
        "ch_assumed": True,
        "rssi": -45,
        "lat": None,
        "lon": None,
        "alt": None,
        "speed": None,
        "vspeed": None,
        "pkt_count": 1,
    }
    content = _notify_online_text(test_e, "上线(测试)", now_wall)
    timeout_sec = int(notify_cfg.get("send_timeout_sec") or 8)
    results: list[str] = []
    ok_count = 0
    for item in targets:
        ok, resp = _wecom_send_text(str(item.get("key") or "").strip(), content, timeout_sec=timeout_sec)
        if ok:
            ok_count += 1
        results.append(f"{item.get('name') or '通道'}: {'OK' if ok else 'FAIL'} {resp}")
    return (ok_count > 0), " | ".join(results)

def _mac_oui_key(mac: str | None) -> str:
    if not mac:
        return ""
    h = "".join(ch for ch in str(mac) if ch in "0123456789abcdefABCDEF")
    if len(h) < 6:
        return ""
    return h[:6].upper()

def _mac_hex12(mac: str | None) -> str:
    if not mac:
        return ""
    h = "".join(ch for ch in str(mac) if ch in "0123456789abcdefABCDEF").lower()
    if len(h) < 12:
        return ""
    return h[:12]

def _is_wifi_fast_mac(mac: str | None) -> bool:
    return _mac_oui_key(mac).lower() == WIFI_FAST_OUI_PREFIX.replace(":", "").lower()

def _wifi_fast_sn(mac: str | None) -> str:
    h12 = _mac_hex12(mac).upper()
    if not h12:
        return "WIFIFAST000000000000"
    return f"WIFIFAST{h12}"

def _hex_preview(data: bytes | None, max_bytes: int = 220) -> str:
    if not data:
        return ""
    b = bytes(data)
    if len(b) <= max_bytes:
        return b.hex(" ")
    head = b[:max_bytes].hex(" ")
    return f"{head} ...( +{len(b) - max_bytes}B )"

def _ap_vendor_type(vendor: str, ssid: str | None) -> str:
    v = (vendor or "").lower()
    s = (ssid or "").strip()
    if s.startswith("RID-") or "dji" in v:
        return "DJI/RID"
    if any(k in v for k in ("apple", "samsung", "huawei", "honor", "xiaomi", "oppo", "vivo", "google")):
        return "手机/热点"
    if any(k in v for k in ("tp-link", "h3c", "ruijie", "ubiquiti", "mikrotik", "netgear", "asus", "cisco", "tenda", "meraki")):
        return "路由/AP"
    if s.startswith("DIRECT-"):
        return "直连/Wi-Fi"
    return "AP"

def _parse_oui_text(raw: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in raw.splitlines():
        m = _oui_line_re.match(line)
        if not m:
            continue
        key = (m.group(1) + m.group(2) + m.group(3)).upper()
        vendor = m.group(4).strip()
        if key and vendor:
            out[key] = vendor
    return out

def _load_oui_map_from_file(path: str | None) -> dict[str, str]:
    if not path or not os.path.exists(path):
        return {}
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        raw = f.read()
    return _parse_oui_text(raw)

def _download_oui_db(path: str) -> tuple[bool, str]:
    req = urllib.request.Request(
        OUI_DB_URL,
        headers={"User-Agent": APP_HTTP_USER_AGENT + " (+OUI cache)"},
        method="GET",
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            data = resp.read()
    except Exception as e:
        return False, str(e)
    if not data:
        return False, "empty response"
    tmp_path = path + ".tmp"
    try:
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        with open(tmp_path, "wb") as f:
            f.write(data)
        os.replace(tmp_path, path)
        return True, path
    except Exception as e:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass
        return False, str(e)

def _oui_load_worker() -> None:
    global oui_loaded, oui_loading_started, oui_last_attempt_wall, oui_map, ap_list_seq
    path = AP_CFG.get("vendor_db_file")
    loaded_map: dict[str, str] = {}
    try:
        with oui_db_lock:
            oui_last_attempt_wall = time.time()
        loaded_map = _load_oui_map_from_file(path)
        if not loaded_map and bool(AP_CFG.get("vendor_auto_download", True)) and path:
            ok, info = _download_oui_db(path)
            if ok:
                _log(f"[INFO] OUI 数据库已下载: {info}")
                loaded_map = _load_oui_map_from_file(path)
            else:
                _log(f"[WARN] OUI database download failed: {info}")
        if loaded_map:
            with oui_db_lock:
                oui_map = loaded_map
                oui_loaded = True
                oui_vendor_cache.clear()
            with ap_lock:
                ap_list_seq += 1
            _log(f"[INFO] OUI database loaded: {len(loaded_map)} entries")
        else:
            with oui_db_lock:
                oui_map = {}
                oui_loaded = True  # Stop returning "加载中" forever when DB is unavailable.
                oui_vendor_cache.clear()
            with ap_lock:
                ap_list_seq += 1
            _log("[WARN] OUI 数据库未加载（AP 厂商将显示未知）")
    except Exception as e:
        with oui_db_lock:
            oui_map = {}
            oui_loaded = True  # Fallback to unknown vendor instead of endless loading state.
            oui_vendor_cache.clear()
        with ap_lock:
            ap_list_seq += 1
        _log(f"[WARN] OUI database load exception: {e}")
    finally:
        with oui_db_lock:
            oui_loading_started = False

def start_oui_loader() -> None:
    global oui_loading_started
    with oui_db_lock:
        if oui_loaded or oui_loading_started:
            return
        oui_loading_started = True
    Thread(target=_oui_load_worker, daemon=True).start()

def _lookup_oui_vendor(mac: str | None) -> str:
    key = _mac_oui_key(mac)
    if not key:
        return ""
    with oui_db_lock:
        cached = oui_vendor_cache.get(key)
        loaded = oui_loaded
        vendor = oui_map.get(key) if loaded else None
    if cached is not None:
        return cached
    if vendor:
        with oui_db_lock:
            oui_vendor_cache[key] = vendor
        return vendor
    if not loaded:
        start_oui_loader()
        return "加载中"
    with oui_db_lock:
        oui_vendor_cache[key] = "未知"
    return "未知"

def _ap_trim_locked(now_wall: float | None = None) -> None:
    now_wall = float(now_wall or time.time())
    if len(ap_table) <= max(80, int(AP_CFG.get("list_max") or AP_LIST_MAX_DEFAULT) * 2):
        # Still prune very old entries to keep the table "realtime".
        victims = [mac for mac, e in ap_table.items()
                   if (now_wall - float(e.get("last_seen_wall_ts") or now_wall)) > (AP_STALE_TIMEOUT * 3)]
        for mac in victims:
            ap_table.pop(mac, None)
        return
    items = sorted(ap_table.items(), key=lambda kv: kv[1].get("last_seen_wall_ts", 0.0), reverse=True)
    keep = {mac for mac, _ in items[:max(80, int(AP_CFG.get("list_max") or AP_LIST_MAX_DEFAULT) * 2)]}
    for mac in list(ap_table.keys()):
        if mac not in keep:
            ap_table.pop(mac, None)

def _ap_touch(mac: str, ssid: str | None, rssi: int | None, ch: int | None, subtype: str) -> None:
    global ap_list_seq
    now_wall = time.time()
    now_mono = time.monotonic()
    vendor = _lookup_oui_vendor(mac)
    with ap_lock:
        e = ap_table.get(mac)
        if e is None:
            e = {
                "mac": mac,
                "ssid": ssid or "",
                "rssi": rssi,
                "ch": ch,
                "subtype": subtype,
                "first_seen_wall_ts": now_wall,
                "last_seen_wall_ts": now_wall,
                "first_seen_ts": now_mono,
                "last_seen_ts": now_mono,
                "hits": 0,
                "vendor": "",
                "vendor_type": "",
            }
            ap_table[mac] = e
        if ssid is not None:
            e["ssid"] = ssid
        if rssi is not None:
            e["rssi"] = rssi
        if ch:
            e["ch"] = ch
        e["subtype"] = subtype or e.get("subtype") or "AP"
        e["last_seen_wall_ts"] = now_wall
        e["last_seen_ts"] = now_mono
        e["hits"] = int(e.get("hits") or 0) + 1
        if vendor and ((not e.get("vendor")) or (e.get("vendor") in ("加载中", "未知")) or (vendor not in ("加载中", "未知"))):
            e["vendor"] = vendor
        vname = str(e.get("vendor") or vendor or "")
        if _is_wifi_fast_mac(mac):
            e["vendor_type"] = "WiFi快传"
        else:
            e["vendor_type"] = _ap_vendor_type(vname, e.get("ssid"))
        _ap_trim_locked(now_wall)
        ap_list_seq += 1

def _ap_snapshot() -> tuple[list[dict], int, int]:
    now_wall = time.time()
    with ap_lock:
        _ap_trim_locked(now_wall)
        items = list(ap_table.values())
        seq = ap_list_seq
    rows: list[dict] = []
    for e in items:
        mac = str(e.get("mac") or "")
        vendor = _lookup_oui_vendor(mac) or str(e.get("vendor") or "")
        last_seen_wall = float(e.get("last_seen_wall_ts") or now_wall)
        age = max(0, int(now_wall - last_seen_wall))
        rows.append({
            "mac": mac,
            "ssid": str(e.get("ssid") or ""),
            "rssi": e.get("rssi"),
            "ch": e.get("ch"),
            "hits": int(e.get("hits") or 0),
            "subtype": str(e.get("subtype") or "AP"),
            "vendor": vendor or str(e.get("vendor") or "未知"),
            "vendor_type": ("WiFi快传" if _is_wifi_fast_mac(mac) else _ap_vendor_type(vendor or str(e.get("vendor") or ""), e.get("ssid"))),
            "age": age,
            "last_seen": _fmt_wall_ts(last_seen_wall),
        })
    # realtime list sorted by signal strength (higher RSSI first)
    rows.sort(
        key=lambda x: (
            -float(x.get("rssi")) if x.get("rssi") is not None else float("inf"),
            x["age"],
            x.get("mac") or "",
        )
    )
    limit = int(AP_CFG.get("list_max") or AP_LIST_MAX_DEFAULT)
    total = len(rows)
    return rows[:limit], seq, total

# -----------------------------------------------------------------------------
# 机型映射
# -----------------------------------------------------------------------------
def _model_from_sn(sn: str) -> str:
    if not sn or sn.startswith("MAC:"):
        return "N/A"
    sn_key = re.sub(r"[^0-9A-Za-z]+", "", str(sn or "")).upper()
    if not sn_key:
        return "N/A"
    items = sorted(MODEL_MAP.items(), key=lambda kv: len(str(kv[0] or "")), reverse=True)
    for pref, model in items:
        pref_key = re.sub(r"[^0-9A-Za-z]+", "", str(pref or "")).upper()
        if pref_key and sn_key.startswith(pref_key):
            return model
    return "N/A"

def _resolve_model_name(sn: str, scan_type: str | None = None, current_model: str | None = None) -> str:
    if _scan_type_key(scan_type) == "phone":
        return "WiFi快传"
    mapped = _model_from_sn(sn)
    if mapped != "N/A":
        return mapped
    cur = str(current_model or "").strip()
    return cur if (cur and cur.upper() != "N/A") else "N/A"

def _refresh_models_locked(*, only_na: bool = False) -> tuple[int, int]:
    """Refresh model names from SN mapping for both history/state tables.
    Must be called with `state_lock` held.
    Returns (history_changed, state_changed).
    """
    history_changed = 0
    state_changed = 0
    for sn, h in history_table.items():
        if not isinstance(h, dict):
            continue
        old = str(h.get("model") or "").strip()
        if only_na and old and old.upper() != "N/A":
            continue
        sn_key = str(h.get("sn") or sn or "")
        new = _resolve_model_name(sn_key, h.get("scan_type"), old)
        old_norm = old if old else "N/A"
        if new != old_norm:
            h["model"] = new
            history_changed += 1
    for sn, e in state_table.items():
        if not isinstance(e, dict):
            continue
        old = str(e.get("model") or "").strip()
        if only_na and old and old.upper() != "N/A":
            continue
        sn_key = str(e.get("sn") or sn or "")
        new = _resolve_model_name(sn_key, e.get("scan_type"), old)
        old_norm = old if old else "N/A"
        if new != old_norm:
            e["model"] = new
            state_changed += 1
    return history_changed, state_changed

def load_model_map(path: str) -> None:
    global MODEL_MAP
    try:
        with open(path, "r", encoding="utf-8") as f:
            obj = json.load(f)
        if isinstance(obj, dict):
            MODEL_MAP = {str(k): str(v) for k, v in obj.items()}
            _log(f"[INFO] model map loaded: {path} ({len(MODEL_MAP)} entries)")
            with state_lock:
                h_changed, s_changed = _refresh_models_locked(only_na=False)
                if h_changed:
                    _history_mark_dirty()
            if h_changed or s_changed:
                _log(f"[INFO] model remap applied: history={h_changed}, live={s_changed}")
        else:
            _log(f"[WARN] model map format invalid: {path}")
    except FileNotFoundError:
        _log(f"[WARN] model map not found: {path}")
    except Exception as e:
        _log(f"[WARN] model map load failed: {e}")

def _model_map_target_path() -> str:
    try:
        basic = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
        if isinstance(basic, dict):
            raw = str(basic.get("model_map") or "").strip()
            if raw:
                return os.path.abspath(raw)
    except Exception:
        pass
    return os.path.abspath(os.path.join(os.getcwd(), "rid_models.json"))

def _model_map_items_from_dict(obj: dict | None) -> list[dict]:
    src = obj if isinstance(obj, dict) else {}
    return [
        {"prefix": str(k), "model": str(v)}
        for k, v in sorted(src.items(), key=lambda kv: str(kv[0]).upper())
    ]

def _read_model_map_file(path: str) -> dict[str, str]:
    with open(path, "r", encoding="utf-8") as f:
        obj = json.load(f)
    return _validate_model_map_payload(obj)

def _model_map_editor_payload(warning: str = "") -> dict:
    target = _model_map_target_path()
    data: dict[str, str] = {}
    warn = warning
    try:
        data = _read_model_map_file(target)
    except FileNotFoundError:
        data = dict(MODEL_MAP)
        warn = warn or "识别库文件不存在，保存后会创建。"
    except Exception as e:
        data = dict(MODEL_MAP)
        warn = warn or f"识别库文件读取失败，当前显示内存中的识别库：{e}"
    return {
        "ok": True,
        "path": target,
        "count": len(data),
        "items": _model_map_items_from_dict(data),
        "state": _model_update_status_payload(),
        "warning": warn,
    }

def _model_update_status_payload() -> dict:
    with model_update_lock:
        state = dict(MODEL_UPDATE_STATE)
    state["enabled"] = bool(MODEL_UPDATE_CFG.get("enabled", True))
    state["url"] = str(MODEL_UPDATE_CFG.get("url") or RID_MODELS_UPDATE_URL_DEFAULT)
    state["target"] = _model_map_target_path()
    state["interval_sec"] = int(MODEL_UPDATE_CHECK_INTERVAL_SEC)
    state["loaded_count"] = int(len(MODEL_MAP))
    return state

def _validate_model_map_payload(obj) -> dict[str, str]:
    if not isinstance(obj, dict):
        raise ValueError("识别库格式错误：根节点必须是对象")
    out: dict[str, str] = {}
    for k, v in obj.items():
        key = re.sub(r"[^0-9A-Za-z]+", "", str(k or "")).upper()
        val = str(v or "").strip()
        if not key or not val:
            continue
        if not re.fullmatch(r"[0-9A-Z]{4,32}", key):
            continue
        out[key] = val
    if not out:
        raise ValueError("识别库为空或没有有效前缀")
    return out

def _model_map_from_editor_items(items) -> dict[str, str]:
    if isinstance(items, dict):
        return _validate_model_map_payload(items)
    if not isinstance(items, list):
        raise ValueError("items must be a list")
    raw: dict[str, str] = {}
    for row in items:
        if not isinstance(row, dict):
            continue
        pref = re.sub(r"[^0-9A-Za-z]+", "", str(row.get("prefix") or "")).upper()
        model = str(row.get("model") or "").strip()
        if not pref and not model:
            continue
        raw[pref] = model
    return _validate_model_map_payload(raw)

def _write_model_map_file(next_map: dict[str, str], tag: str = "models") -> dict:
    target = _model_map_target_path()
    with model_map_file_lock:
        running = False
        with model_update_lock:
            running = bool(MODEL_UPDATE_STATE.get("running"))
        if running:
            return {"ok": False, "error": "识别库在线更新正在运行，请稍后再保存。", "state": _model_update_status_payload()}
        parent = os.path.dirname(target)
        if parent:
            os.makedirs(parent, exist_ok=True)
        b_ok, backup_path = create_config_backup(target, tag=tag)
        if not b_ok:
            return {"ok": False, "error": "backup failed: " + backup_path, "state": _model_update_status_payload()}
        tmp_path = target + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(next_map, f, ensure_ascii=False, indent=2)
            f.write("\n")
        os.replace(tmp_path, target)
        load_model_map(target)
    try:
        save_history_store(force=True)
    except Exception:
        pass
    msg = f"识别库已保存：{len(next_map)} 条"
    _op_log("model-map-save", f"count={len(next_map)} target={target}", ok=True)
    _notification_add(msg, "ok", "server")
    payload = _model_map_editor_payload()
    payload.update({"ok": True, "message": msg, "backup_path": backup_path})
    return payload

def save_model_map_entries(items) -> dict:
    next_map = _model_map_from_editor_items(items)
    return _write_model_map_file(next_map, tag="models")

def upsert_model_map_entry(prefix: str = "", model: str = "", sn: str = "") -> dict:
    clean_prefix = re.sub(r"[^0-9A-Za-z]+", "", str(prefix or "")).upper()
    clean_sn = re.sub(r"[^0-9A-Za-z]+", "", str(sn or "")).upper()
    if not clean_prefix and clean_sn and not str(sn or "").upper().startswith("MAC:"):
        clean_prefix = clean_sn[:8]
    clean_model = str(model or "").strip()
    single = _validate_model_map_payload({clean_prefix: clean_model})
    target = _model_map_target_path()
    try:
        current = _read_model_map_file(target)
    except FileNotFoundError:
        current = dict(MODEL_MAP)
    current.update(single)
    return _write_model_map_file(_validate_model_map_payload(current), tag="models_upsert")

def update_model_map_from_url(manual: bool = False, url_override: str | None = None) -> dict:
    url = str(url_override or MODEL_UPDATE_CFG.get("url") or RID_MODELS_UPDATE_URL_DEFAULT).strip()
    if not (url.startswith("https://") or url.startswith("http://")):
        return {"ok": False, "error": "识别库更新地址必须以 http:// 或 https:// 开头", "state": _model_update_status_payload()}
    target = _model_map_target_path()
    busy = False
    with model_update_lock:
        if MODEL_UPDATE_STATE.get("running"):
            busy = True
        else:
            MODEL_UPDATE_STATE["running"] = True
            MODEL_UPDATE_STATE["last_check_ts"] = time.time()
            MODEL_UPDATE_STATE["last_error"] = ""
            MODEL_UPDATE_STATE["last_message"] = "正在检查识别库"
    if busy:
        return {"ok": False, "error": "识别库更新正在运行", "state": _model_update_status_payload()}
    try:
        req = urllib.request.Request(
            url,
            headers={"User-Agent": APP_HTTP_USER_AGENT + " (+model-map update)"},
            method="GET",
        )
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = resp.read(2 * 1024 * 1024)
        if not data:
            raise ValueError("远端返回为空")
        obj = json.loads(data.decode("utf-8", errors="replace"))
        next_map = _validate_model_map_payload(obj)
        with model_map_file_lock:
            parent = os.path.dirname(target)
            if parent:
                os.makedirs(parent, exist_ok=True)
            if os.path.exists(target):
                try:
                    shutil.copy2(target, target + ".bak")
                except Exception:
                    pass
            tmp_path = target + ".tmp"
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(next_map, f, ensure_ascii=False, indent=2)
                f.write("\n")
            os.replace(tmp_path, target)
            load_model_map(target)
        try:
            save_history_store(force=True)
        except Exception:
            pass
        msg = f"识别库已更新：{len(next_map)} 条"
        with model_update_lock:
            MODEL_UPDATE_STATE["running"] = False
            MODEL_UPDATE_STATE["last_success_ts"] = time.time()
            MODEL_UPDATE_STATE["last_error"] = ""
            MODEL_UPDATE_STATE["last_message"] = msg
            MODEL_UPDATE_STATE["last_count"] = len(next_map)
        _op_log("model-update", f"manual={manual} count={len(next_map)} target={target}", ok=True)
        _notification_add(msg, "ok", "server")
        return {"ok": True, "message": msg, "count": len(next_map), "target": target, "state": _model_update_status_payload()}
    except Exception as e:
        msg = str(e)
        with model_update_lock:
            MODEL_UPDATE_STATE["running"] = False
            MODEL_UPDATE_STATE["last_error"] = msg
            MODEL_UPDATE_STATE["last_message"] = "识别库更新失败"
        _op_log("model-update", f"manual={manual} error={msg}", ok=False)
        if manual:
            _notification_add("识别库更新失败：" + msg, "warn", "server")
        return {"ok": False, "error": msg, "target": target, "state": _model_update_status_payload()}

def model_update_loop() -> None:
    time.sleep(10.0)
    while True:
        try:
            if bool(MODEL_UPDATE_CFG.get("enabled", True)):
                with model_update_lock:
                    last = float(MODEL_UPDATE_STATE.get("last_check_ts") or 0.0)
                    running = bool(MODEL_UPDATE_STATE.get("running"))
                if (not running) and (time.time() - last >= MODEL_UPDATE_CHECK_INTERVAL_SEC):
                    update_model_map_from_url(manual=False)
        except Exception as e:
            _log(f"[WARN] model update loop failed: {e}")
        time.sleep(300.0)

# -----------------------------------------------------------------------------
# Remote config update
# -----------------------------------------------------------------------------
def _config_update_status_payload() -> dict:
    with config_update_lock:
        state = dict(CONFIG_UPDATE_STATE)
    state["enabled"] = bool(CONFIG_UPDATE_CFG.get("enabled", False))
    state["url"] = str(CONFIG_UPDATE_CFG.get("url") or "")
    state["target"] = APP_CONFIG_PATH or ""
    return state

def update_config_from_url(manual: bool = False, url_override: str | None = None) -> dict:
    url = str(url_override or CONFIG_UPDATE_CFG.get("url") or "").strip()
    if not url:
        return {"ok": False, "error": "config update url missing", "state": _config_update_status_payload()}
    if not (url.startswith("https://") or url.startswith("http://")):
        return {"ok": False, "error": "config update url must start with http:// or https://", "state": _config_update_status_payload()}
    if not APP_CONFIG_PATH:
        return {"ok": False, "error": "config path missing", "state": _config_update_status_payload()}
    busy = False
    with config_update_lock:
        if CONFIG_UPDATE_STATE.get("running"):
            busy = True
        else:
            CONFIG_UPDATE_STATE["running"] = True
            CONFIG_UPDATE_STATE["last_check_ts"] = time.time()
            CONFIG_UPDATE_STATE["last_error"] = ""
            CONFIG_UPDATE_STATE["last_message"] = "downloading config"
    if busy:
        return {"ok": False, "error": "config update already running", "state": _config_update_status_payload()}
    try:
        req = urllib.request.Request(
            url,
            headers={"User-Agent": APP_HTTP_USER_AGENT + " (+config update)"},
            method="GET",
        )
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = resp.read(2 * 1024 * 1024)
        if not data:
            raise ValueError("empty response")
        parsed = json.loads(data.decode("utf-8", errors="replace"))
        if not isinstance(parsed, dict):
            raise ValueError("remote config root must be object")
        # Remote config updates follow the same guard rails as manual saves:
        # merge defaults, validate security, backup, save, reload, rollback.
        candidate = _deep_merge_dict(default_app_config(), parsed)
        candidate, guard_err = _prepare_security_cfg_for_save(candidate)
        if guard_err:
            raise ValueError(guard_err)
        b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="config_update")
        if not b_ok:
            raise ValueError("backup failed: " + backup_path)
        ok, msg = save_app_config(APP_CONFIG_PATH, candidate)
        if not ok:
            raise ValueError("save failed: " + msg)
        cfg_loaded = load_app_config(APP_CONFIG_PATH)
        r_ok, r_msg = reload_runtime_config(cfg_loaded)
        if not r_ok:
            restore_config_backup(APP_CONFIG_PATH, backup_path)
            raise ValueError("reload failed: " + r_msg)
        msg = f"config updated from url; keys={len(candidate.keys())}"
        with config_update_lock:
            CONFIG_UPDATE_STATE["running"] = False
            CONFIG_UPDATE_STATE["last_success_ts"] = time.time()
            CONFIG_UPDATE_STATE["last_error"] = ""
            CONFIG_UPDATE_STATE["last_message"] = msg
            CONFIG_UPDATE_STATE["last_count"] = len(candidate.keys())
        _op_log("config-update", f"manual={manual} target={APP_CONFIG_PATH}", ok=True)
        return {"ok": True, "message": msg, "saved_to": APP_CONFIG_PATH, "state": _config_update_status_payload()}
    except Exception as e:
        msg = str(e)
        with config_update_lock:
            CONFIG_UPDATE_STATE["running"] = False
            CONFIG_UPDATE_STATE["last_error"] = msg
            CONFIG_UPDATE_STATE["last_message"] = "config update failed"
        _op_log("config-update", f"manual={manual} error={msg}", ok=False)
        return {"ok": False, "error": msg, "state": _config_update_status_payload()}

def config_update_loop() -> None:
    time.sleep(20.0)
    while True:
        try:
            if bool(CONFIG_UPDATE_CFG.get("enabled", False)):
                with config_update_lock:
                    last = float(CONFIG_UPDATE_STATE.get("last_check_ts") or 0.0)
                    running = bool(CONFIG_UPDATE_STATE.get("running"))
                if (not running) and (time.time() - last >= 24 * 3600):
                    update_config_from_url(manual=False)
        except Exception as e:
            _log(f"[WARN] config update loop failed: {e}")
        time.sleep(300.0)

def start_config_update_worker() -> None:
    global config_update_worker_started
    if config_update_worker_started:
        return
    config_update_worker_started = True
    Thread(target=config_update_loop, daemon=True).start()

def start_model_update_worker() -> None:
    global model_update_worker_started
    if model_update_worker_started:
        return
    model_update_worker_started = True
    Thread(target=model_update_loop, daemon=True).start()

# -----------------------------------------------------------------------------
# Formatting helpers
# -----------------------------------------------------------------------------
def _fmt(v, fmt=".6f", unit="", na="N/A") -> str:
    return f"{v:{fmt}}{unit}" if v is not None else na

# -----------------------------------------------------------------------------
# 地理
# -----------------------------------------------------------------------------
def _haversine(lat1, lon1, lat2, lon2) -> float:
    R  = 6371000.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    a  = (math.sin(math.radians(lat2-lat1)/2)**2
          + math.cos(p1)*math.cos(p2)*math.sin(math.radians(lon2-lon1)/2)**2)
    return 2*R*math.asin(min(1.0, math.sqrt(a)))

def _bearing(lat1, lon1, lat2, lon2) -> float | None:
    try:
        p1, p2 = math.radians(lat1), math.radians(lat2)
        dl     = math.radians(lon2-lon1)
        return (math.degrees(math.atan2(
            math.sin(dl)*math.cos(p2),
            math.cos(p1)*math.sin(p2)-math.sin(p1)*math.cos(p2)*math.cos(dl)
        ))+360)%360
    except Exception:
        return None

def _bearing8(deg: float) -> str:
    return ["N","NE","E","SE","S","SW","W","NW"][int((deg+22.5)//45)%8]

# -----------------------------------------------------------------------------
# 系统命令 / 接口
# -----------------------------------------------------------------------------
def run_cmd(cmd: str, timeout: int = 5) -> str:
    try:
        r = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        return (r.stdout or "").strip()
    except Exception:
        return ""

def _is_linux_host() -> bool:
    return platform.system().lower() == "linux"

def _is_root_user() -> bool:
    try:
        return bool(hasattr(os, "geteuid") and os.geteuid() == 0)
    except Exception:
        return False

def _command_path(name: str) -> str:
    try:
        return str(shutil.which(str(name or "").strip()) or "")
    except Exception:
        return ""

def _current_uid() -> int | None:
    try:
        if hasattr(os, "geteuid"):
            return int(os.geteuid())
    except Exception:
        pass
    return None

def _capability_bit(name: str) -> int | None:
    caps = {
        "CAP_NET_ADMIN": 12,
        "CAP_NET_RAW": 13,
        "CAP_NET_BIND_SERVICE": 10,
    }
    return caps.get(str(name or "").strip().upper())

def _process_has_capabilities(names: tuple[str, ...] | list[str]) -> bool:
    if not _is_linux_host():
        return False
    try:
        wanted = [_capability_bit(str(x)) for x in names]
        wanted = [int(x) for x in wanted if x is not None]
        if not wanted:
            return False
        with open("/proc/self/status", "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                if line.startswith("CapEff:"):
                    value = int(line.split(":", 1)[1].strip(), 16)
                    return all((value & (1 << bit)) for bit in wanted)
    except Exception:
        pass
    return False

def _username_for_uid(uid: int | None) -> str:
    try:
        if uid is not None and _is_linux_host():
            return _platform_username_for_uid(uid)
    except (OSError, TypeError, ValueError):
        pass
    try:
        return str(os.environ.get("USER") or os.environ.get("USERNAME") or "")
    except Exception:
        return ""

def _local_user_exists(name: str) -> bool:
    user = str(name or "").strip()
    if not user or not _is_linux_host():
        return False
    try:
        exists = _platform_local_user_exists(user)
    except (OSError, TypeError, ValueError):
        exists = None
    if exists is not None:
        return bool(exists)
    ok, _out, _rc = _run_program(["id", "-u", user], timeout=4)
    return bool(ok)

def _local_group_exists(name: str) -> bool:
    group = str(name or "").strip()
    if not group or not _is_linux_host():
        return False
    try:
        exists = _platform_local_group_exists(group)
    except (OSError, TypeError, ValueError):
        exists = None
    if exists is not None:
        return bool(exists)
    ok, _out, _rc = _run_program(["getent", "group", group], timeout=4)
    return bool(ok)

def _sudo_available() -> bool:
    return bool(_is_linux_host() and _command_path("sudo"))

def _sudo_password_from_body(body: dict | None) -> str:
    if not isinstance(body, dict):
        return ""
    try:
        return str(body.get("sudo_password") or body.get("password") or "")
    except Exception:
        return ""

def _truncate_text(text: str, limit: int = 3600) -> str:
    raw = str(text or "").strip()
    if len(raw) <= limit:
        return raw
    return raw[:limit] + "\n...输出已截断..."

def _run_program(args: list[str], timeout: int = 30, env: dict | None = None, input_text: str | None = None) -> tuple[bool, str, int]:
    try:
        r = subprocess.run(
            [str(x) for x in args],
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
            input=input_text,
        )
        out = ((r.stdout or "") + ("\n" if r.stdout and r.stderr else "") + (r.stderr or "")).strip()
        return r.returncode == 0, _truncate_text(out), int(r.returncode)
    except Exception as e:
        return False, str(e), -1

def _run_privileged(args: list[str], timeout: int = 30, env: dict | None = None, sudo_password: str | None = None) -> tuple[bool, str, int]:
    cmd = [str(x) for x in args]
    if not cmd:
        return False, "empty command", -1
    if _is_root_user():
        return _run_program(cmd, timeout=timeout, env=env)
    sudo = _command_path("sudo")
    if not sudo:
        return False, "当前进程不是 root，且未检测到 sudo。", -1
    password = "" if sudo_password is None else str(sudo_password)
    if password:
        return _run_program([sudo, "-S", "-p", "", "--"] + cmd, timeout=timeout, env=env, input_text=password + "\n")
    return _run_program([sudo, "-n", "--"] + cmd, timeout=timeout, env=env)

def _systemctl(args: list[str], timeout: int = 20, sudo_password: str | None = None, privileged: bool = False) -> tuple[bool, str, int]:
    cmd = [_command_path("systemctl") or "systemctl"] + [str(x) for x in args]
    if privileged:
        return _run_privileged(cmd, timeout=timeout, sudo_password=sudo_password)
    return _run_program(cmd, timeout=timeout)

def _systemctl_privileged(args: list[str], timeout: int = 20, sudo_password: str | None = None) -> tuple[bool, str, int]:
    return _systemctl(args, timeout=timeout, sudo_password=sudo_password, privileged=True)

def _iw_manual_install_hint() -> str:
    return "请手动安装: sudo apt-get update && sudo apt-get install -y iw hostapd"

def _iw_missing_message() -> str:
    return "未检测到 iw 命令，无法枚举或切换无线网卡。"

def _set_iw_check_state(**updates) -> dict:
    with iw_check_lock:
        IW_CHECK_STATE.update(updates)
        return dict(IW_CHECK_STATE)

def _refresh_iw_check_state(message: str | None = None) -> dict:
    path = _command_path(IW_PACKAGE_NAME)
    hostapd_path = _command_path("hostapd")
    available = bool(path)
    msg = str(message or "").strip()
    if not msg:
        if available and hostapd_path:
            msg = f"无线工具可用: iw={path} hostapd={hostapd_path}"
        elif not available:
            msg = _iw_missing_message()
        else:
            msg = "未检测到 hostapd，AP 热点无法广播。"
    return _set_iw_check_state(
        checked=True,
        available=available,
        path=path,
        hostapd_available=bool(hostapd_path),
        hostapd_path=hostapd_path,
        message=msg,
        manual_hint=("" if available and hostapd_path else _iw_manual_install_hint()),
    )

def _iw_status_payload(refresh: bool = True) -> dict:
    with iw_check_lock:
        checked = bool(IW_CHECK_STATE.get("checked"))
    if refresh or not checked:
        snap = _refresh_iw_check_state()
    else:
        with iw_check_lock:
            snap = dict(IW_CHECK_STATE)
    snap["sudo_available"] = _sudo_available()
    snap["can_install"] = bool(_is_linux_host() and (_is_root_user() or _sudo_available()) and _command_path("apt-get"))
    snap["package"] = IW_PACKAGE_NAME
    return snap

def _install_iw_package(sudo_password: str | None = None) -> dict:
    existing = _iw_status_payload(refresh=True)
    if existing.get("available") and existing.get("hostapd_available"):
        return {
            "ok": True,
            "installed": False,
            "message": "无线工具已可用，无需安装。",
            "iw": existing,
        }
    _set_iw_check_state(install_attempted=True, install_ok=False)
    if not _is_linux_host():
        snap = _refresh_iw_check_state("当前主机不是 Linux，无法通过网页自动安装无线工具。")
        return {"ok": False, "installed": False, "error": snap.get("message"), "iw": snap}
    if not _command_path("apt-get"):
        snap = _refresh_iw_check_state("未检测到 apt-get，无法通过网页自动安装无线工具。")
        return {"ok": False, "installed": False, "error": snap.get("message"), "iw": snap}
    if not (_is_root_user() or _sudo_available()):
        snap = _refresh_iw_check_state("网页安装无线工具需要 root 或 sudo 提权。")
        return {"ok": False, "installed": False, "error": snap.get("message"), "iw": snap}

    env = dict(os.environ)
    env["DEBIAN_FRONTEND"] = "noninteractive"
    ok_update, out_update, rc_update = _run_privileged(["apt-get", "update"], timeout=300, env=env, sudo_password=sudo_password)
    if not ok_update:
        snap = _refresh_iw_check_state("apt-get update 失败，无法通过网页安装无线工具。")
        return {
            "ok": False,
            "installed": False,
            "error": snap.get("message"),
            "returncode": rc_update,
            "output": out_update,
            "iw": snap,
        }
    ok_install, out_install, rc_install = _run_privileged(["apt-get", "install", "-y", IW_PACKAGE_NAME, "hostapd"], timeout=300, env=env, sudo_password=sudo_password)
    snap = _refresh_iw_check_state("无线工具安装完成。" if ok_install else "apt-get install iw hostapd 失败。")
    installed = bool(ok_install and snap.get("available") and snap.get("hostapd_available"))
    _set_iw_check_state(install_ok=installed)
    snap = _iw_status_payload(refresh=False)
    return {
        "ok": installed,
        "installed": installed,
        "error": "" if installed else str(snap.get("message") or "wireless tools install failed"),
        "returncode": rc_install,
        "output": _truncate_text((out_update + "\n" + out_install).strip()),
        "iw": snap,
    }

def _prompt_install_iw_on_startup() -> bool:
    try:
        return bool(sys.stdin and sys.stdin.isatty() and sys.stdout and sys.stdout.isatty())
    except Exception:
        return False

def check_iw_available_on_startup() -> bool:
    snap = _iw_status_payload(refresh=True)
    if snap.get("available"):
        _log(f"[INFO] iw command available: {snap.get('path')}")
        return True

    msg = f"{snap.get('message') or _iw_missing_message()} {snap.get('manual_hint') or _iw_manual_install_hint()}"
    _log(f"[WARN] {msg}")
    _sniff_note_error(msg)
    if not (_is_linux_host() and _is_root_user() and _command_path("apt-get") and _prompt_install_iw_on_startup()):
        _log("[WARN] 启动环境无法交互确认自动安装 iw，请手动安装后重启服务。")
        return False

    try:
        answer = input("未检测到 iw，是否现在自动安装？这将执行 apt-get update && apt-get install -y iw [y/N]: ")
    except Exception:
        answer = ""
    if str(answer or "").strip().lower() not in ("y", "yes"):
        _log(f"[WARN] 已跳过 iw 自动安装。{_iw_manual_install_hint()}")
        return False

    rsp = _install_iw_package()
    if rsp.get("ok"):
        _log("[INFO] iw installed successfully")
        return True
    _log(f"[WARN] iw 自动安装失败: {rsp.get('error') or rsp.get('output') or 'unknown error'}")
    _log(f"[WARN] {_iw_manual_install_hint()}")
    return False

# -----------------------------------------------------------------------------
# Privileged runtime repair / systemd helpers
# -----------------------------------------------------------------------------
def _systemd_supported() -> tuple[bool, str]:
    if not _is_linux_host():
        return False, "当前主机不是 Linux。"
    if not _command_path("systemctl"):
        return False, "未检测到 systemctl。"
    return True, ""

def _systemd_quote_arg(value: str) -> str:
    s = str(value or "")
    if not s:
        return '""'
    if re.search(r"\s|[\"\\]", s):
        return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'
    return s

def _systemd_service_spec() -> dict:
    # Always point the generated unit at the current script/config pair and
    # force no-TUI mode for unattended service execution.
    script = os.path.abspath(_runtime_entrypoint_path())
    workdir = os.path.abspath(APP_START_CWD or os.path.dirname(script) or ".")
    config_path = os.path.abspath(APP_CONFIG_PATH or os.path.join(workdir, CONFIG_FILE_DEFAULT))
    py = os.path.abspath(sys.executable or "python3")
    if getattr(sys, "frozen", False):
        exec_parts = [_systemd_quote_arg(py)]
    else:
        exec_parts = [_systemd_quote_arg(py), _systemd_quote_arg(script)]
    exec_start = " ".join([
        *exec_parts,
        "--config",
        _systemd_quote_arg(config_path),
        "--no-tui",
    ])
    service_lines = [
        "[Unit]",
        "Description=Light RID Scanner",
        "Wants=network-online.target",
        "After=network-online.target",
        "",
        "[Service]",
        "Type=simple",
        "Environment=PYTHONUNBUFFERED=1",
        f"WorkingDirectory={_systemd_quote_arg(workdir)}",
        f"ExecStart={exec_start}",
        f"User={RUNTIME_SERVICE_USER}",
    ]
    if _local_group_exists(RUNTIME_SERVICE_USER):
        service_lines.append(f"Group={RUNTIME_SERVICE_USER}")
    if _local_group_exists("netdev"):
        service_lines.append("SupplementaryGroups=netdev")
    caps = " ".join(RUNTIME_SERVICE_CAPABILITIES)
    service_lines.extend([
        f"AmbientCapabilities={caps}",
        f"CapabilityBoundingSet={caps}",
        "Restart=on-failure",
        "RestartSec=3",
        "",
        "[Install]",
        "WantedBy=multi-user.target",
        "",
    ])
    unit = "\n".join(service_lines)
    return {
        "service_name": SYSTEMD_SERVICE_NAME,
        "service_path": SYSTEMD_SERVICE_PATH,
        "python": py,
        "script": script,
        "cwd": workdir,
        "config_path": config_path,
        "exec_start": exec_start,
        "service_user": RUNTIME_SERVICE_USER,
        "service_home": RUNTIME_SERVICE_HOME,
        "service_capabilities": list(RUNTIME_SERVICE_CAPABILITIES),
        "unit_text": unit,
    }

def _read_systemd_unit_text() -> tuple[str, str]:
    try:
        if os.path.exists(SYSTEMD_SERVICE_PATH):
            with open(SYSTEMD_SERVICE_PATH, "r", encoding="utf-8", errors="ignore") as f:
                return f.read(), ""
    except Exception as e:
        return "", str(e)
    return "", ""

def _unit_declared_user(unit_text: str) -> str:
    try:
        for line in str(unit_text or "").splitlines():
            s = line.strip()
            if s.startswith("User="):
                return s.split("=", 1)[1].strip()
    except Exception:
        pass
    return ""

def _runtime_security_payload(unit_text: str | None = None) -> dict:
    uid = _current_uid()
    current_user = _username_for_uid(uid)
    running_as_root = _is_root_user()
    if unit_text is None:
        unit_text, _err = _read_systemd_unit_text()
    actual_service_user = _unit_declared_user(unit_text or "")
    dedicated_exists = _local_user_exists(RUNTIME_SERVICE_USER)
    sudo_available = _sudo_available()
    caps_ok = bool(_process_has_capabilities(list(RUNTIME_SERVICE_CAPABILITIES)))
    risk = "当前程序以 root 权限运行，网页接口和采集进程拥有过高权限。"
    no_caps = f"当前程序以 {current_user or '非 root'} 权限运行，但未检测到采集所需网络能力。"
    ok_msg = f"当前程序以 {current_user or '非 root'} 权限运行。"
    level = "warn" if running_as_root or (not running_as_root and _is_linux_host() and not caps_ok) else "ok"
    return {
        "ok": True,
        "current_uid": uid,
        "current_user": current_user,
        "running_as_root": bool(running_as_root),
        "has_network_capabilities": bool(caps_ok),
        "risk": "root-runtime" if running_as_root else ("" if caps_ok or not _is_linux_host() else "missing-capabilities"),
        "level": level,
        "message": risk if running_as_root else (ok_msg if caps_ok or not _is_linux_host() else no_caps),
        "dedicated_user": RUNTIME_SERVICE_USER,
        "dedicated_user_exists": bool(dedicated_exists),
        "service_user": actual_service_user,
        "service_uses_dedicated_user": actual_service_user == RUNTIME_SERVICE_USER,
        "sudo_available": bool(sudo_available),
        "can_elevate": bool(_is_linux_host() and (running_as_root or sudo_available)),
        "password_saved": False,
    }

def _runtime_path_targets() -> tuple[list[str], list[str]]:
    dirs: set[str] = set()
    files: set[str] = set()

    def add_file(path: str | None) -> None:
        p = str(path or "").strip()
        if not p:
            return
        p = os.path.abspath(p)
        files.add(p)
        parent = os.path.dirname(p)
        if parent:
            dirs.add(parent)
            dirs.add(os.path.join(parent, "backups"))

    def add_dir(path: str | None) -> None:
        p = str(path or "").strip()
        if p:
            dirs.add(os.path.abspath(p))

    add_dir(APP_START_CWD)
    add_file(APP_CONFIG_PATH)
    if APP_CONFIG_PATH:
        add_file(str(APP_CONFIG_PATH) + CONFIG_ROLLBACK_SUFFIX)
    add_file(HISTORY_STORE_PATH)
    add_file(_model_map_target_path())
    add_file(_eula_set_path())
    try:
        add_file(str(AP_CFG.get("vendor_db_file") or ""))
    except Exception:
        pass
    add_dir(os.path.dirname(os.path.abspath(HOST_METRICS_PATH)))
    return sorted(dirs), sorted(files)

def _runtime_traverse_dirs(dirs: list[str]) -> list[str]:
    out: set[str] = set()
    for raw in dirs:
        try:
            path = os.path.abspath(str(raw or ""))
        except Exception:
            continue
        parent = os.path.dirname(path)
        while parent and parent != path:
            if parent == os.path.abspath(os.sep):
                break
            out.add(parent)
            path = parent
            parent = os.path.dirname(path)
    return sorted(out, key=lambda p: len(p))

def _run_repair_step(label: str, args: list[str], steps: list[dict], sudo_password: str | None = None, timeout: int = 30, optional: bool = False) -> bool:
    ok, out, rc = _run_privileged(args, timeout=timeout, sudo_password=sudo_password)
    steps.append({"label": label, "ok": bool(ok), "returncode": rc, "output": out})
    return bool(ok or optional)

def _run_as_runtime_user(args: list[str], sudo_password: str | None, timeout: int = 20) -> tuple[bool, str, int]:
    cmd = [str(x) for x in args]
    if not cmd:
        return False, "empty command", -1
    if _command_path("runuser"):
        return _run_privileged(["runuser", "-u", RUNTIME_SERVICE_USER, "--"] + cmd, timeout=timeout, sudo_password=sudo_password)
    sudo = _command_path("sudo")
    if sudo:
        return _run_privileged([sudo, "-u", RUNTIME_SERVICE_USER, "--"] + cmd, timeout=timeout, sudo_password=sudo_password)
    return False, "未检测到 runuser/sudo，无法以 rid 账号验收权限。", -1

def _verify_runtime_path_access(sudo_password: str | None, steps: list[dict]) -> bool:
    dirs, files = _runtime_path_targets()
    for d in dirs:
        if not d:
            continue
        ok, out, rc = _run_as_runtime_user(["test", "-d", d, "-a", "-r", d, "-a", "-w", d, "-a", "-x", d], sudo_password=sudo_password)
        steps.append({"label": f"rid 目录权限验收 {d}", "ok": bool(ok), "returncode": rc, "output": out})
        if not ok:
            return False
    for f in files:
        if not f or not os.path.exists(f):
            continue
        ok, out, rc = _run_as_runtime_user(["test", "-r", f, "-a", "-w", f], sudo_password=sudo_password)
        steps.append({"label": f"rid 文件权限验收 {f}", "ok": bool(ok), "returncode": rc, "output": out})
        if not ok:
            return False
    return True

def _grant_runtime_path_access(sudo_password: str | None, steps: list[dict]) -> bool:
    dirs, files = _runtime_path_targets()
    for d in _runtime_traverse_dirs(dirs):
        if not d or not os.path.isdir(d):
            continue
        acl_cmd = ["setfacl", "-m", f"u:{RUNTIME_SERVICE_USER}:x", d]
        if _command_path("setfacl"):
            if not _run_repair_step(f"上级目录进入权限 {d}", acl_cmd, steps, sudo_password=sudo_password, optional=False):
                return False
        else:
            if not _run_repair_step(f"上级目录进入权限 {d}", ["chmod", "o+x", d], steps, sudo_password=sudo_password, optional=False):
                return False
    for d in dirs:
        if not d:
            continue
        if not _run_repair_step(f"创建目录 {d}", ["mkdir", "-p", d], steps, sudo_password=sudo_password):
            return False
        if not _run_repair_step(f"目录授权 {d}", ["chgrp", RUNTIME_SERVICE_USER, d], steps, sudo_password=sudo_password, optional=False):
            return False
        if not _run_repair_step(f"目录写权限 {d}", ["chmod", "g+rwx,g+s", d], steps, sudo_password=sudo_password):
            return False
    for f in files:
        if not f or not os.path.exists(f):
            continue
        if not _run_repair_step(f"文件授权 {f}", ["chgrp", RUNTIME_SERVICE_USER, f], steps, sudo_password=sudo_password):
            return False
        if not _run_repair_step(f"文件写权限 {f}", ["chmod", "g+rw", f], steps, sudo_password=sudo_password):
            return False
    return True

def _write_systemd_unit_privileged(unit_text: str, sudo_password: str | None, steps: list[dict]) -> tuple[bool, str]:
    backup_path = ""
    tmp_path = ""
    try:
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False, prefix="light-rid-service-", suffix=".service") as f:
            tmp_path = f.name
            f.write(unit_text)
    except Exception as e:
        steps.append({"label": "生成临时服务文件", "ok": False, "returncode": -1, "output": str(e)})
        return False, backup_path
    try:
        if os.path.exists(SYSTEMD_SERVICE_PATH):
            backup_path = SYSTEMD_SERVICE_PATH + "." + time.strftime("%Y%m%d_%H%M%S") + ".bak"
            if not _run_repair_step("备份 systemd 服务文件", ["cp", "-a", SYSTEMD_SERVICE_PATH, backup_path], steps, sudo_password=sudo_password):
                return False, backup_path
        if not _run_repair_step("写入 systemd 服务文件", ["install", "-m", "0644", tmp_path, SYSTEMD_SERVICE_PATH], steps, sudo_password=sudo_password):
            return False, backup_path
        return True, backup_path
    finally:
        try:
            if tmp_path:
                os.remove(tmp_path)
        except Exception:
            pass

def _schedule_systemd_restart(sudo_password: str | None, steps: list[dict], delay_sec: int = 3) -> bool:
    delay = max(1, int(delay_sec or 3))
    systemctl = _command_path("systemctl") or "systemctl"
    systemd_run = _command_path("systemd-run")
    if systemd_run:
        unit_name = f"light-rid-scanner-restart-{os.getpid()}-{int(time.time())}"
        args = [
            systemd_run,
            f"--unit={unit_name}",
            f"--on-active={delay}s",
            "--collect",
            systemctl,
            "restart",
            SYSTEMD_SERVICE_NAME,
        ]
        ok, out, rc = _run_privileged(args, timeout=20, sudo_password=sudo_password)
        steps.append({"label": f"安排 {delay} 秒后自动重启服务", "ok": bool(ok), "returncode": rc, "output": out})
        return bool(ok)

    shell = f"sleep {delay}; exec {shlex.quote(systemctl)} restart {shlex.quote(SYSTEMD_SERVICE_NAME)}"
    try:
        if _is_root_user():
            subprocess.Popen(
                ["sh", "-c", shell],
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                start_new_session=True,
                close_fds=True,
            )
        else:
            sudo = _command_path("sudo")
            if not sudo:
                steps.append({"label": "安排自动重启服务", "ok": False, "returncode": -1, "output": "当前进程不是 root，且未检测到 sudo。"})
                return False
            password = "" if sudo_password is None else str(sudo_password)
            if password:
                proc = subprocess.Popen(
                    [sudo, "-S", "-p", "", "--", "sh", "-c", shell],
                    stdin=subprocess.PIPE,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    text=True,
                    start_new_session=True,
                    close_fds=True,
                )
                try:
                    if proc.stdin:
                        proc.stdin.write(password + "\n")
                        proc.stdin.close()
                finally:
                    password = ""
            else:
                subprocess.Popen(
                    [sudo, "-n", "--", "sh", "-c", shell],
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    start_new_session=True,
                    close_fds=True,
                )
        steps.append({"label": f"安排 {delay} 秒后自动重启服务", "ok": True, "returncode": 0, "output": "已安排后台重启。"})
        return True
    except Exception as e:
        steps.append({"label": "安排自动重启服务", "ok": False, "returncode": -1, "output": str(e)})
        return False

def repair_runtime_security(sudo_password: str | None = None) -> dict:
    supported, reason = _systemd_supported()
    steps: list[dict] = []
    if not supported:
        return {"ok": False, "error": reason, "status": _systemd_service_status_payload(), "steps": steps}
    if not (_is_root_user() or _sudo_available()):
        return {"ok": False, "error": "创建专用运行账号需要 root 或 sudo 提权。", "status": _systemd_service_status_payload(), "steps": steps}
    if not _local_user_exists(RUNTIME_SERVICE_USER):
        shell_path = "/usr/sbin/nologin" if os.path.exists("/usr/sbin/nologin") else "/bin/false"
        useradd_cmd = [
            _command_path("useradd") or "useradd",
            "--system",
            "--create-home",
            "--home-dir",
            RUNTIME_SERVICE_HOME,
            "--shell",
            shell_path,
            "--user-group",
            RUNTIME_SERVICE_USER,
        ]
        if not _run_repair_step(f"创建 {RUNTIME_SERVICE_USER} 账号", useradd_cmd, steps, sudo_password=sudo_password, timeout=30):
            return {"ok": False, "error": f"创建 {RUNTIME_SERVICE_USER} 账号失败。", "status": _systemd_service_status_payload(), "steps": steps}
    else:
        steps.append({"label": f"{RUNTIME_SERVICE_USER} 账号已存在", "ok": True, "returncode": 0, "output": ""})
    if not _run_repair_step("准备专用运行目录", ["install", "-d", "-o", RUNTIME_SERVICE_USER, "-g", RUNTIME_SERVICE_USER, "-m", "0750", RUNTIME_SERVICE_HOME], steps, sudo_password=sudo_password):
        return {"ok": False, "error": "准备专用运行目录失败。", "status": _systemd_service_status_payload(), "steps": steps}
    if _local_group_exists("netdev"):
        _run_repair_step("加入 netdev 组", ["usermod", "-a", "-G", "netdev", RUNTIME_SERVICE_USER], steps, sudo_password=sudo_password, optional=True)
    if not _grant_runtime_path_access(sudo_password, steps):
        return {"ok": False, "error": "授予运行文件写权限失败。", "status": _systemd_service_status_payload(), "steps": steps}
    if not _verify_runtime_path_access(sudo_password, steps):
        return {"ok": False, "error": "rid 账号权限验收失败。请检查上方失败步骤后重试。", "status": _systemd_service_status_payload(), "steps": steps}
    rsp = register_systemd_service(sudo_password=sudo_password, require_dedicated_user=True, _steps=steps)
    payload = dict(rsp)
    payload["steps"] = steps
    if rsp.get("ok"):
        restart_delay = 3
        restart_scheduled = _schedule_systemd_restart(sudo_password, steps, delay_sec=restart_delay)
        payload["steps"] = steps
        payload["restart_scheduled"] = bool(restart_scheduled)
        payload["restart_delay_sec"] = restart_delay
        if restart_scheduled:
            payload["message"] = "已创建/确认 rid 专用账号，并更新 systemd 服务为 rid 账号运行。服务将在几秒后自动重启，页面可能短暂断开。"
        else:
            payload["message"] = "已创建/确认 rid 专用账号，并更新 systemd 服务为 rid 账号运行；但自动重启安排失败，请手动重启 light-rid-scanner.service。"
    return payload

def _systemd_service_status_payload() -> dict:
    supported, reason = _systemd_supported()
    spec = _systemd_service_spec()
    registered = os.path.exists(SYSTEMD_SERVICE_PATH)
    enabled = "unknown"
    active = "unknown"
    unit_matches = False
    last_error = ""
    unit_text = ""
    if registered:
        unit_text, last_error = _read_systemd_unit_text()
        unit_matches = (unit_text.strip() == str(spec.get("unit_text") or "").strip())
    if supported and registered:
        ok_enabled, out_enabled, _rc_enabled = _systemctl(["is-enabled", SYSTEMD_SERVICE_NAME], timeout=8)
        enabled = (out_enabled.splitlines() or ["enabled" if ok_enabled else "disabled"])[0].strip() or ("enabled" if ok_enabled else "disabled")
        ok_active, out_active, _rc_active = _systemctl(["is-active", SYSTEMD_SERVICE_NAME], timeout=8)
        active = (out_active.splitlines() or ["active" if ok_active else "inactive"])[0].strip() or ("active" if ok_active else "inactive")
    security = _runtime_security_payload(unit_text=unit_text)
    return {
        "ok": True,
        "supported": bool(supported),
        "reason": reason,
        "running_as_root": _is_root_user(),
        "current_user": security.get("current_user"),
        "current_uid": security.get("current_uid"),
        "registered": bool(registered),
        "enabled": enabled,
        "active": active,
        "unit_matches": bool(unit_matches),
        "last_error": last_error,
        "dedicated_user": RUNTIME_SERVICE_USER,
        "dedicated_user_exists": bool(security.get("dedicated_user_exists")),
        "actual_service_user": security.get("service_user"),
        "service_uses_dedicated_user": bool(security.get("service_uses_dedicated_user")),
        "sudo_available": bool(security.get("sudo_available")),
        "can_elevate": bool(security.get("can_elevate")),
        "security": security,
        "manual_hint": "需要 root 或临时 sudo 提权写入 /etc/systemd/system 并执行 systemctl daemon-reload、systemctl enable。",
        "iw": _iw_status_payload(refresh=True),
        **spec,
    }

def register_systemd_service(sudo_password: str | None = None, require_dedicated_user: bool = True, _steps: list[dict] | None = None) -> dict:
    supported, reason = _systemd_supported()
    steps = _steps if isinstance(_steps, list) else []
    if not supported:
        return {"ok": False, "error": reason, "status": _systemd_service_status_payload(), "steps": steps}
    if require_dedicated_user and not _local_user_exists(RUNTIME_SERVICE_USER):
        return {
            "ok": False,
            "error": f"专用运行账号 {RUNTIME_SERVICE_USER} 不存在，请先执行一键修复。",
            "status": _systemd_service_status_payload(),
            "steps": steps,
        }
    if not (_is_root_user() or _sudo_available()):
        return {"ok": False, "error": "注册 systemd 服务需要 root 或临时 sudo 提权。", "status": _systemd_service_status_payload(), "steps": steps}
    spec = _systemd_service_spec()
    unit_text = str(spec.get("unit_text") or "")
    ok_write, backup_path = _write_systemd_unit_privileged(unit_text, sudo_password, steps)
    if not ok_write:
        return {"ok": False, "error": "写入服务文件失败。", "status": _systemd_service_status_payload(), "steps": steps}

    ok_reload, out_reload, rc_reload = _systemctl_privileged(["daemon-reload"], timeout=20, sudo_password=sudo_password)
    steps.append({"label": "systemctl daemon-reload", "ok": bool(ok_reload), "returncode": rc_reload, "output": out_reload})
    if not ok_reload:
        return {
            "ok": False,
            "error": "systemctl daemon-reload 失败",
            "returncode": rc_reload,
            "output": out_reload,
            "backup_path": backup_path,
            "status": _systemd_service_status_payload(),
            "steps": steps,
        }
    ok_enable, out_enable, rc_enable = _systemctl_privileged(["enable", SYSTEMD_SERVICE_NAME], timeout=20, sudo_password=sudo_password)
    steps.append({"label": "systemctl enable", "ok": bool(ok_enable), "returncode": rc_enable, "output": out_enable})
    status = _systemd_service_status_payload()
    if not ok_enable:
        return {
            "ok": False,
            "error": "systemctl enable 失败",
            "returncode": rc_enable,
            "output": out_enable,
            "backup_path": backup_path,
            "status": status,
            "steps": steps,
        }
    return {
        "ok": True,
        "message": f"systemd 服务已注册并设为开机自启；服务文件将以 {RUNTIME_SERVICE_USER} 账号运行，当前进程不会被自动重启。",
        "backup_path": backup_path,
        "output": out_enable,
        "status": status,
        "steps": steps,
    }

def _sniff_note_packet() -> None:
    global sniff_last_pkt_mono, sniff_last_pkt_wall, sniff_last_error, sniff_last_error_wall
    now_mono = time.monotonic()
    now_wall = time.time()
    with sniff_health_lock:
        sniff_last_pkt_mono = now_mono
        sniff_last_pkt_wall = now_wall
        sniff_last_error = ""
        sniff_last_error_wall = 0.0

def _sniff_idle_sec(now_mono: float | None = None) -> float | None:
    now_mono = float(now_mono or time.monotonic())
    with sniff_health_lock:
        last = sniff_last_pkt_mono
    if not last:
        return None
    return max(0.0, now_mono - float(last))

def _sniff_note_error(msg: str) -> None:
    global sniff_last_error, sniff_last_error_wall
    text = str(msg or "").strip()
    if len(text) > 220:
        text = text[:220]
    with sniff_health_lock:
        sniff_last_error = text
        sniff_last_error_wall = time.time()

def _sniff_health_meta(now_mono: float, now_wall: float) -> dict:
    with sniff_health_lock:
        last_pkt_mono = float(sniff_last_pkt_mono or 0.0)
        last_pkt_wall = float(sniff_last_pkt_wall or 0.0)
        last_err = str(sniff_last_error or "")
        last_err_wall = float(sniff_last_error_wall or 0.0)
        iface = str(sniff_iface_name or "")
    idle_sec = None
    if last_pkt_mono > 0.0:
        idle_sec = max(0.0, now_mono - last_pkt_mono)
    state = "ok"
    msg = ""
    if last_err:
        state = "error"
        msg = last_err
    elif idle_sec is None:
        state = "warn"
        msg = "尚未收到无线管理帧"
    elif idle_sec >= SNIFF_STALL_RECOVER_SEC:
        state = "warn"
        msg = f"{int(idle_sec)}s no wireless management frame"
    return {
        "state": state,
        "msg": msg,
        "iface": iface,
        "idle_sec": (None if idle_sec is None else int(round(idle_sec))),
        "last_pkt": _fmt_wall_ts(last_pkt_wall if last_pkt_wall > 0 else None),
        "last_err_at": _fmt_wall_ts(last_err_wall if last_err_wall > 0 else None),
    }

def _sniff_recover_iface(iface: str, reason: str, force: bool = False) -> bool:
    global sniff_last_recover_wall, sniff_iface_name
    iface = str(iface or "").strip()
    if not iface:
        _sniff_note_error(f"iface empty: {reason}")
        return False
    now_wall = time.time()
    with sniff_health_lock:
        if (not force) and sniff_last_recover_wall and (now_wall - sniff_last_recover_wall) < SNIFF_RECOVER_COOLDOWN_SEC:
            return False
        sniff_last_recover_wall = now_wall
        sniff_iface_name = iface
    _sniff_note_error(reason)
    _log(f"[WARN] sniff recover: {reason}, reset iface {iface}")
    steps = (
        (f"ip link set {iface} down", 0.15),
        (f"iw dev {iface} set type managed", 0.35),
        (f"ip link set {iface} up", 0.25),
        (f"ip link set {iface} down", 0.15),
        (f"iw dev {iface} set type monitor", 0.35),
        (f"ip link set {iface} up", 0.25),
        (f"iw dev {iface} set power_save off", 0.0),
    )
    for c, pause_sec in steps:
        run_cmd(c, timeout=6)
        if pause_sec > 0:
            time.sleep(pause_sec)
    if current_channel:
        run_cmd(f"iw dev {iface} set channel {current_channel}", timeout=6)
    info_raw = run_cmd(f"iw dev {iface} info")
    if not info_raw or ("Interface" not in info_raw):
        _sniff_note_error(f"iface unavailable: {iface}")
        return False
    info_lines = []
    for ln in info_raw.splitlines():
        t = ln.strip()
        if re.search(r"\b(type|channel)\b", t):
            info_lines.append(t)
    if info_lines:
        _log(f"[INFO] sniff recover result: {' | '.join(info_lines)}")
    with sniff_health_lock:
        sniff_iface_name = iface
    return True

def _sniff_close_socket(sock) -> None:
    if not sock:
        return
    try:
        sock.close()
    except Exception:
        pass

def _sniff_open_socket(iface: str):
    try:
        return conf.L2listen(iface=iface, monitor=True)
    except TypeError:
        return conf.L2listen(iface=iface)

def _sniff_run_once(iface: str, timeout_sec: float = SNIFF_POLL_TIMEOUT) -> tuple[str, str]:
    iface = str(iface or "").strip()
    if not iface:
        return "error", "iface empty"
    timeout_sec = max(1.0, float(timeout_sec or SNIFF_POLL_TIMEOUT))
    hard_deadline = time.monotonic() + timeout_sec + SNIFF_WORKER_HARD_GRACE_SEC
    result = {"error": "", "done": False}
    sock_ref = {"sock": None}

    def _worker() -> None:
        sock = None
        try:
            sock = _sniff_open_socket(iface)
            sock_ref["sock"] = sock
            sniff(opened_socket=sock, prn=parse_frame, store=False, timeout=timeout_sec)
        except Exception as ex:
            result["error"] = str(ex or "")
        finally:
            result["done"] = True
            if sock_ref.get("sock") is sock:
                sock_ref["sock"] = None
            _sniff_close_socket(sock)

    th = Thread(target=_worker, daemon=True)
    th.start()
    while th.is_alive():
        if time.monotonic() >= hard_deadline:
            _sniff_close_socket(sock_ref.get("sock"))
            th.join(SNIFF_WORKER_JOIN_GRACE_SEC)
            if th.is_alive():
                return "hung", f"worker exceeded {timeout_sec + SNIFF_WORKER_HARD_GRACE_SEC:.0f}s"
            return "hung", f"worker forced close after {timeout_sec + SNIFF_WORKER_HARD_GRACE_SEC:.0f}s"
        time.sleep(0.25)
    if result["error"]:
        return "error", result["error"]
    return "ok", ""

def _sniff_iface_candidates() -> dict[str, str]:
    iw = run_cmd("iw dev")
    iftypes: dict[str, str] = {}
    cur = None
    for line in (iw or "").splitlines():
        m = re.match(r"\s*Interface\s+(\S+)", line)
        if m:
            cur = m.group(1)
            continue
        m2 = re.match(r"\s*type\s+(\S+)", line)
        if m2 and cur:
            iftypes[cur] = m2.group(1)
    return iftypes

def _ip_json_snapshot(args: list[str]) -> dict:
    try:
        ok, out, _rc = _run_program(["ip", "-j"] + [str(x) for x in args], timeout=4)
        if not ok or not out:
            return {}
        data = json.loads(out)
        if not isinstance(data, list):
            return {}
        return {
            str(item.get("ifname") or ""): item
            for item in data
            if isinstance(item, dict) and str(item.get("ifname") or "")
        }
    except Exception:
        return {}

def _iface_sysfs_flags(name: str) -> int | None:
    try:
        with open(os.path.join("/sys/class/net", name, "flags"), "r", encoding="utf-8", errors="ignore") as f:
            return int(f.read().strip(), 16)
    except Exception:
        return None

def _iface_addr_lists(name: str, addr_item: dict | None = None) -> tuple[list[str], list[str]]:
    ipv4: list[str] = []
    ipv6: list[str] = []
    item = addr_item if isinstance(addr_item, dict) else {}
    for addr in item.get("addr_info") or []:
        if not isinstance(addr, dict):
            continue
        local = str(addr.get("local") or "").strip()
        prefix = addr.get("prefixlen")
        if not local:
            continue
        text = local + (f"/{prefix}" if prefix not in (None, "") else "")
        if str(addr.get("family") or "").lower() == "inet":
            ipv4.append(text)
        elif str(addr.get("family") or "").lower() == "inet6":
            ipv6.append(text)
    return ipv4, ipv6

def _sysfs_read_text(path: str) -> str:
    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            return f.read().strip()
    except Exception:
        return ""

def _iface_device_model(name: str) -> dict:
    out = {"model": "", "driver": "", "bus": "", "vendor_id": "", "product_id": ""}
    try:
        dev_path = os.path.realpath(os.path.join("/sys/class/net", name, "device"))
    except Exception:
        dev_path = ""
    if not dev_path or not os.path.exists(dev_path):
        return out
    try:
        driver_link = os.path.realpath(os.path.join(dev_path, "driver"))
        if driver_link and os.path.exists(driver_link):
            out["driver"] = os.path.basename(driver_link)
    except Exception:
        pass
    cur = dev_path
    for _ in range(8):
        vid = _sysfs_read_text(os.path.join(cur, "idVendor"))
        pid = _sysfs_read_text(os.path.join(cur, "idProduct"))
        if vid or pid:
            manufacturer = _sysfs_read_text(os.path.join(cur, "manufacturer"))
            product = _sysfs_read_text(os.path.join(cur, "product"))
            out.update({
                "bus": "usb",
                "vendor_id": vid.lower(),
                "product_id": pid.lower(),
                "model": " ".join(x for x in (manufacturer, product) if x) or f"USB {vid}:{pid}",
            })
            return out
        parent = os.path.dirname(cur)
        if not parent or parent == cur or parent == "/sys":
            break
        cur = parent
    modalias = _sysfs_read_text(os.path.join(dev_path, "modalias"))
    if modalias.startswith("pci:"):
        slot = os.path.basename(dev_path)
        ok, desc, _rc = _run_program(["lspci", "-D", "-s", slot], timeout=4)
        out["bus"] = "pci"
        if ok and desc:
            out["model"] = re.sub(r"^[0-9a-fA-F:.]+\\s+", "", desc.strip())
        else:
            out["vendor_id"] = _sysfs_read_text(os.path.join(dev_path, "vendor")).replace("0x", "").lower()
            out["product_id"] = _sysfs_read_text(os.path.join(dev_path, "device")).replace("0x", "").lower()
            if out["vendor_id"] or out["product_id"]:
                out["model"] = f"PCI {out['vendor_id']}:{out['product_id']}"
    return out

def _iface_detected_role(item: dict) -> str:
    if bool(item.get("is_loopback")):
        return "none"
    if item.get("admin_up") is False:
        return "disabled"
    mode = str(item.get("mode") or "").strip().lower()
    ipv4 = [str(x) for x in (item.get("ipv4") or [])]
    if mode in ("__ap", "ap"):
        return "ap_web"
    if any(x.startswith("172.16.0.1/") or x == "172.16.0.1" for x in ipv4):
        return "ap_web"
    if mode == "monitor":
        return "scan"
    if ipv4:
        return "web"
    if str(item.get("state") or "").strip().lower() in ("up", "unknown", "dormant"):
        return "idle"
    return "none"

def _iface_options_snapshot() -> list[dict]:
    iftypes = _sniff_iface_candidates()
    names: set[str] = set(iftypes.keys())
    link_json = _ip_json_snapshot(["-details", "link", "show"])
    addr_json = _ip_json_snapshot(["addr", "show"])
    names.update([x for x in link_json.keys() if x])
    names.update([x for x in addr_json.keys() if x])
    try:
        for name in os.listdir("/sys/class/net"):
            if name:
                names.add(str(name))
    except Exception:
        pass
    if not names:
        ip_out = run_cmd("ip -o link show", timeout=4)
        for line in (ip_out or "").splitlines():
            m = re.match(r"\d+:\s+([^:@]+)", line)
            if m:
                names.add(m.group(1))
    out: list[dict] = []
    for name in names:
        link_item = link_json.get(name) or {}
        addr_item = addr_json.get(name) or {}
        mode = iftypes.get(name, "")
        if not mode:
            linkinfo = link_item.get("linkinfo") if isinstance(link_item.get("linkinfo"), dict) else {}
            info_kind = str(linkinfo.get("info_kind") or "").strip()
            if info_kind:
                mode = info_kind
        try:
            supports_5g = bool(detect_5g(name))
        except Exception:
            supports_5g = False
        is_wireless = bool(mode)
        try:
            is_wireless = is_wireless or os.path.isdir(os.path.join("/sys/class/net", name, "wireless"))
        except Exception:
            pass
        mac = ""
        state = ""
        try:
            with open(os.path.join("/sys/class/net", name, "address"), "r", encoding="utf-8", errors="ignore") as f:
                mac = f.read().strip()
        except Exception:
            mac = ""
        try:
            with open(os.path.join("/sys/class/net", name, "operstate"), "r", encoding="utf-8", errors="ignore") as f:
                state = f.read().strip()
        except Exception:
            state = str(link_item.get("operstate") or "")
        flags_raw = _iface_sysfs_flags(name)
        flags = list(link_item.get("flags") or []) if isinstance(link_item.get("flags"), list) else []
        admin_up = None
        if flags_raw is not None:
            admin_up = bool(flags_raw & 0x1)
        elif flags:
            admin_up = "UP" in [str(x).upper() for x in flags]
        ipv4, ipv6 = _iface_addr_lists(name, addr_item)
        device = _iface_device_model(name)
        item = {
            "name": str(name),
            "mode": str(mode or ""),
            "is_monitor": (str(mode or "") == "monitor"),
            "is_wireless": bool(is_wireless),
            "is_loopback": str(name) == "lo",
            "state": state,
            "admin_up": admin_up,
            "flags": flags,
            "mac": mac,
            "ipv4": ipv4,
            "ipv6": ipv6,
            "supports_5g": supports_5g,
            "model": device.get("model") or "",
            "driver": device.get("driver") or "",
            "bus": device.get("bus") or "",
            "vendor_id": device.get("vendor_id") or "",
            "product_id": device.get("product_id") or "",
        }
        item["detected_role"] = _iface_detected_role(item)
        out.append(item)
    out.sort(key=lambda x: (
        1 if x.get("is_loopback") else 0,
        1 if x.get("detected_role") == "disabled" else 0,
        0 if x.get("is_wireless") else 1,
        0 if x.get("is_monitor") else 1,
        x.get("name") or "",
    ))
    return out

def _cfg_preferred_iface() -> str | None:
    return _cfg_preferred_iface_from_cfg(APP_CONFIG)

def _cfg_auto_self_heal() -> bool:
    try:
        basic = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
        if not isinstance(basic, dict):
            return True
        return bool(basic.get("auto_self_heal", True))
    except Exception:
        return True

def _sniff_pick_iface(prefer: str | None = None) -> str | None:
    iftypes = _sniff_iface_candidates()
    if not iftypes:
        return None
    if prefer and prefer in iftypes:
        return prefer
    if prefer:
        _sniff_note_error(f"配置的默认网卡未检测到: {prefer}")
        return None
    _sniff_note_error("未绑定默认网卡，请打开 OOBE 或设置页选择网卡")
    return None

def _sniff_is_no_device_error(ex: Exception) -> bool:
    s = str(ex or "")
    return (
        ("No such device" in s) or
        ("Errno 19" in s) or
        ("Network is down" in s) or
        ("Errno 100" in s)
    )

def _freq_to_ch(freq) -> int | None:
    try:
        f = int(freq)
    except Exception:
        return None
    if 2412 <= f <= 2484: return 14 if f==2484 else (f-2407)//5
    if 5000 <= f <= 5900: return (f-5000)//5
    return None

def _rt_channel(pkt) -> int | None:
    if not pkt.haslayer(RadioTap): return None
    rt = pkt[RadioTap]
    for attr in ("ChannelFrequency","ChannelFreq","channel_freq","Channel"):
        if hasattr(rt, attr):
            v = getattr(rt, attr)
            if isinstance(v, tuple) and v: v = v[0]
            if isinstance(v, (int,float)):
                ch = _freq_to_ch(int(v))
                if ch: return ch
    return None

def _ssid_to_sn(ssid: str) -> str | None:
    m = SSID_SN_RE.search(ssid) if ssid else None
    return m.group(1) if m else None

def interface_detect(prefer: str | None = None) -> str | None:
    iw      = run_cmd("iw dev")
    if not iw and not _command_path(IW_PACKAGE_NAME):
        snap = _iw_status_payload(refresh=True)
        msg = f"{snap.get('message') or _iw_missing_message()} {snap.get('manual_hint') or _iw_manual_install_hint()}"
        _log(f"[WARN] {msg}")
        _sniff_note_error(msg)
        _set_oobe_required(msg, True)
        return None
    iftypes: dict[str, str] = {}
    cur     = None
    for line in iw.splitlines():
        m = re.match(r"\s*Interface\s+(\S+)", line)
        if m: cur = m.group(1)
        m2 = re.match(r"\s*type\s+(\S+)", line)
        if m2 and cur: iftypes[cur] = m2.group(1)

    if not prefer:
        msg = "未绑定默认网卡，请进入 OOBE 或设置页选择固定网卡"
        _log(f"[WARN] {msg}")
        _sniff_note_error(msg)
        _set_oobe_required(msg, True)
        return None
    if prefer and prefer in iftypes:
        iface = prefer
    else:
        iface = None
    if not iface:
        msg = f"默认网卡未检测到: {prefer}" if iftypes else NO_IFACE_DEGRADE_HINT
        _log(f"[WARN] {msg}")
        _sniff_note_error(msg + "。请打开 OOBE 或设置页检查默认网卡。")
        _set_oobe_required(msg, True)
        return None

    mode = iftypes.get(iface, "unknown")
    _log(f"[INFO] iface={iface} mode={mode}")
    if mode != "monitor":
        _log("[INFO] switching to monitor mode...")
        for c in (f"ip link set {iface} down",
                  f"iw dev {iface} set type monitor",
                  f"ip link set {iface} up"):
            run_cmd(c)
        new = run_cmd(f"iw dev {iface} info | grep type").strip()
        _log(f"[INFO] monitor switch result: {new}")
    run_cmd(f"iw dev {iface} set power_save off")
    ch_info = run_cmd(f"iw dev {iface} info | grep channel").strip()
    _log(f"[INFO] current channel: {ch_info or 'unknown'}")
    return iface

def detect_5g(iface: str) -> bool:
    out = run_cmd(f"iw dev {iface} info")
    m   = re.search(r"\bwiphy\s+(\d+)", out)
    if not m: return False
    phy = run_cmd(f"iw phy{m.group(1)} info")
    if "Band 2:" in phy: return True
    return any(5000<=int(x)<=5999 for x in re.findall(r"\b(5\d{3})\s+MHz\b", phy))

# -----------------------------------------------------------------------------
# Channel hopper
# -----------------------------------------------------------------------------
def channel_hopper(iface, ch2g, ch5g, dw2, dw5, settle_ms, hit_ms, cap_ms):
    global current_channel
    dw2, dw5, settle = dw2/1000, dw5/1000, settle_ms/1000
    hit_until = 0.0
    lk = Lock()

    def note_hit():
        nonlocal hit_until
        now  = time.monotonic()
        ext  = max(0, hit_ms)/1000
        hold = max(0, cap_ms)/1000
        if ext <= 0: return
        with lk:
            cap = now+hold if hold>0 else now+ext
            hit_until = min(max(hit_until, now+ext), cap)

    globals()["_hopper_note_hit"] = note_hit

    def do_hold():
        with lk: u = hit_until
        rem = u - time.monotonic()
        if rem > 0: time.sleep(rem)

    while True:
        for ch in random.sample(ch2g, len(ch2g)):
            run_cmd(f"iw dev {iface} set channel {ch}")
            current_channel = ch
            if settle: time.sleep(settle)
            do_hold(); time.sleep(dw2)
        for ch in (random.sample(ch5g, len(ch5g)) if ch5g else []):
            run_cmd(f"iw dev {iface} set channel {ch}")
            current_channel = ch
            if settle: time.sleep(settle)
            do_hold(); time.sleep(dw5)

