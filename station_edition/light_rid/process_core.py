def _snap(e: dict) -> dict:
    s = {k: e.get(k) for k in
         ("sn","src_mac","id_type","uas_id","model","lat","lon","alt","speed","vspeed","last_ch","move_dir")}
    if CHANGE_ON_RSSI: s["rssi"]  = e.get("rssi")
    if CHANGE_ON_PL:   s["pl_sig"] = e.get("pl_sig")
    return s

NEW_FW_DETAIL_KEYS = (
    "kind", "rid_format", "dji_rid_kind", "parse_note", "raw_vendor",
    "gb_version", "gb_identifiers",
    "gb_data_type", "gb_version_raw", "gb_data_len", "dji_dynamic",
    "reg_mark", "status", "coord_type",
    "operation_category", "operation_category_text",
    "aircraft_category", "aircraft_category_text",
    "pilot_alt", "track_deg", "ground_speed", "vertical_speed",
    "alt_relative", "alt_geoid", "alt_baro",
    "operation_state", "operation_state_text",
    "coord_sys", "coord_sys_text",
    "horizontal_accuracy", "vertical_accuracy", "speed_accuracy",
    "timestamp_ms", "timestamp_accuracy", "timestamp_accuracy_text",
    "home_lat", "home_lon", "aux_lat", "aux_lon", "alt_candidates",
)

def _copy_new_fw_detail(dst: dict, src: dict | None) -> None:
    if not isinstance(src, dict):
        return
    for key in NEW_FW_DETAIL_KEYS:
        if key in src:
            dst[key] = src.get(key)

def _history_merge(dst: dict, src: dict) -> None:
    if not src:
        return
    if src.get("first_seen_ts") is not None:
        if dst.get("first_seen_ts") is None or src["first_seen_ts"] < dst["first_seen_ts"]:
            dst["first_seen_ts"] = src["first_seen_ts"]
    if src.get("first_seen_wall_ts") is not None:
        if dst.get("first_seen_wall_ts") is None or src["first_seen_wall_ts"] < dst["first_seen_wall_ts"]:
            dst["first_seen_wall_ts"] = src["first_seen_wall_ts"]
    if src.get("last_seen_ts") is not None:
        if dst.get("last_seen_ts") is None or src["last_seen_ts"] > dst["last_seen_ts"]:
            dst["last_seen_ts"] = src["last_seen_ts"]
    if src.get("last_seen_wall_ts") is not None:
        if dst.get("last_seen_wall_ts") is None or src["last_seen_wall_ts"] > dst["last_seen_wall_ts"]:
            dst["last_seen_wall_ts"] = src["last_seen_wall_ts"]
    if bool(src.get("notify_first_online_sent")):
        dst["notify_first_online_sent"] = True
    src_nt = src.get("notify_last_wall_ts")
    dst_nt = dst.get("notify_last_wall_ts")
    if src_nt is not None and (dst_nt is None or float(src_nt) > float(dst_nt)):
        dst["notify_last_wall_ts"] = src_nt
    src_lod = src.get("last_online_duration_sec")
    if src_lod is not None:
        src_last_wall = float(src.get("last_seen_wall_ts") or 0.0)
        dst_last_wall = float(dst.get("last_seen_wall_ts") or 0.0)
        if dst.get("last_online_duration_sec") is None or src_last_wall >= dst_last_wall:
            dst["last_online_duration_sec"] = src_lod
    if src.get("ssid"):
        dst["ssid"] = src.get("ssid")
    if src.get("capture_type"):
        dst["capture_type"] = src.get("capture_type")
    src_uas = _uas_id_clean(src.get("uas_id"))
    if src_uas:
        dst["uas_id"] = src_uas
    src_fw = _firmware_type_key(src.get("firmware_type"))
    dst_fw = _firmware_type_key(dst.get("firmware_type"))
    if src_fw == "new" or not dst_fw:
        dst["firmware_type"] = src_fw
    if src.get("pilot_lat") is not None and src.get("pilot_lon") is not None:
        dst["pilot_lat"] = src.get("pilot_lat")
        dst["pilot_lon"] = src.get("pilot_lon")
        dst["pilot_loc_type"] = src.get("pilot_loc_type")
        dst["pilot_loc_type_text"] = src.get("pilot_loc_type_text")
    _copy_new_fw_detail(dst, src)
    src_cap_ts = src.get("last_capture_wall_ts")
    dst_cap_ts = dst.get("last_capture_wall_ts")
    if src_cap_ts is not None and (dst_cap_ts is None or float(src_cap_ts) > float(dst_cap_ts)):
        dst["last_capture_wall_ts"] = src_cap_ts
    src_rp = list(src.get("raw_packets") or [])
    if src_rp:
        dst_rp = list(dst.get("raw_packets") or [])
        merged = (dst_rp + src_rp)[-HISTORY_RAW_PACKET_LIMIT:]
        dst["raw_packets"] = merged
    src_track = _sanitize_track(src.get("track") or [])
    if src_track:
        dst_track = _sanitize_track(dst.get("track") or [])
        merged_track = _sanitize_track(dst_track + src_track)
        dst["track"] = merged_track
        if merged_track:
            dst["track_updated_wall_ts"] = float(merged_track[-1].get("ts") or time.time())
    src_st = _scan_type_key(src.get("scan_type"))
    if src_st and (not dst.get("scan_type")):
        dst["scan_type"] = src_st
    dst["pkt_count_total"] = dst.get("pkt_count_total", 0) + src.get("pkt_count_total", 0)

def _history_touch(e: dict, now: float, now_wall: float) -> None:
    sn = str(e.get("sn",""))
    if not sn:
        return
    h = history_table.get(sn)
    if h is None:
        h = {
            "sn": sn,
            "first_seen_ts": e.get("first_seen_ts", now),
            "first_seen_wall_ts": e.get("first_seen_wall_ts", now_wall),
            "last_seen_ts": now,
            "last_seen_wall_ts": now_wall,
            "pkt_count_total": 0,
            "notify_first_online_sent": False,
            "notify_last_wall_ts": 0.0,
            "last_online_duration_sec": e.get("last_online_duration_sec"),
            "ssid": e.get("ssid"),
            "capture_type": e.get("capture_type"),
            "uas_id": _uas_id_clean(e.get("uas_id")),
            "firmware_type": _firmware_type_key(e.get("firmware_type")),
            "pilot_lat": e.get("pilot_lat"),
            "pilot_lon": e.get("pilot_lon"),
            "pilot_loc_type": e.get("pilot_loc_type"),
            "pilot_loc_type_text": e.get("pilot_loc_type_text"),
            "pilot_alt": e.get("pilot_alt"),
            "last_capture_wall_ts": e.get("last_capture_wall_ts"),
            "raw_packets": list(e.get("raw_packets") or [])[-HISTORY_RAW_PACKET_LIMIT:],
            "scan_type": _scan_type_key(e.get("scan_type")),
            "track": _sanitize_track(e.get("track") or []),
            "track_updated_wall_ts": e.get("track_updated_wall_ts"),
        }
        history_table[sn] = h
    h["sn"] = sn
    h["src_mac"] = e.get("src_mac")
    h["id_type"] = e.get("id_type")
    h["model"] = _resolve_model_name(sn, e.get("scan_type"), e.get("model"))
    h["last_ch"] = e.get("last_ch")
    h["ch_assumed"] = e.get("ch_assumed")
    h["lat"] = e.get("lat")
    h["lon"] = e.get("lon")
    h["alt"] = e.get("alt")
    h["speed"] = e.get("speed")
    h["vspeed"] = e.get("vspeed")
    h["pilot_lat"] = e.get("pilot_lat")
    h["pilot_lon"] = e.get("pilot_lon")
    h["pilot_loc_type"] = e.get("pilot_loc_type")
    h["pilot_loc_type_text"] = e.get("pilot_loc_type_text")
    _copy_new_fw_detail(h, e)
    h["rssi"] = e.get("rssi")
    h["move_dir"] = e.get("move_dir")
    h["ssid"] = e.get("ssid")
    h["capture_type"] = e.get("capture_type")
    h["uas_id"] = _uas_id_clean(e.get("uas_id"))
    h["firmware_type"] = _firmware_type_key(e.get("firmware_type"))
    h["last_capture_wall_ts"] = e.get("last_capture_wall_ts")
    h["raw_packets"] = list(e.get("raw_packets") or [])[-HISTORY_RAW_PACKET_LIMIT:]
    h["scan_type"] = _scan_type_key(e.get("scan_type"))
    h["track"] = _sanitize_track(h.get("track") or [])
    if e.get("lat") is not None and e.get("lon") is not None:
        _track_append_point(h, float(e.get("lat")), float(e.get("lon")), float(now_wall))
    h["last_seen_ts"] = now
    h["last_seen_wall_ts"] = now_wall
    h["pkt_count_total"] = h.get("pkt_count_total", 0) + 1
    h.setdefault("notify_first_online_sent", False)
    h.setdefault("notify_last_wall_ts", 0.0)
    h.setdefault("last_online_duration_sec", e.get("last_online_duration_sec"))
    h.setdefault("pilot_lat", e.get("pilot_lat"))
    h.setdefault("pilot_lon", e.get("pilot_lon"))
    h.setdefault("pilot_loc_type", e.get("pilot_loc_type"))
    h.setdefault("pilot_loc_type_text", e.get("pilot_loc_type_text"))
    h.setdefault("pilot_alt", e.get("pilot_alt"))
    h.setdefault("raw_packets", list(e.get("raw_packets") or [])[-HISTORY_RAW_PACKET_LIMIT:])
    h.setdefault("scan_type", _scan_type_key(e.get("scan_type")))
    h.setdefault("uas_id", _uas_id_clean(e.get("uas_id")))
    h.setdefault("firmware_type", _firmware_type_key(e.get("firmware_type")))
    h.setdefault("track", _sanitize_track(e.get("track") or []))
    h.setdefault("track_updated_wall_ts", e.get("track_updated_wall_ts"))
    _history_mark_dirty()

def _history_raw_packet_wall_ts(raw: dict, fallback: float | None = None) -> float:
    if isinstance(raw, dict):
        ts_text = str(raw.get("ts") or "").strip()
        if ts_text and ts_text != "-":
            try:
                return float(time.mktime(time.strptime(ts_text, "%Y-%m-%d %H:%M:%S")))
            except Exception:
                pass
    try:
        return float(fallback or 0.0)
    except Exception:
        return 0.0

def _history_recent_raw_packet_candidates_locked(limit: int = HISTORY_RAW_PACKET_LIMIT) -> list[dict]:
    try:
        per_aircraft_limit = int(limit)
    except Exception:
        per_aircraft_limit = HISTORY_RAW_PACKET_LIMIT
    per_aircraft_limit = max(1, min(per_aircraft_limit, HISTORY_RAW_PACKET_LIMIT))
    out: list[dict] = []
    seq = 0
    for sn, hist in history_table.items():
        if not isinstance(hist, dict):
            continue
        fallback_ts = hist.get("last_capture_wall_ts") or hist.get("last_seen_wall_ts") or 0.0
        raw_packets = list(hist.get("raw_packets") or [])[-per_aircraft_limit:]
        for packet_index, raw in enumerate(raw_packets):
            seq += 1
            if not isinstance(raw, dict):
                continue
            if not str(raw.get("hex") or "").strip():
                continue
            wall_ts = _history_raw_packet_wall_ts(raw, fallback_ts)
            out.append({
                "wall_ts": wall_ts,
                "seq": seq,
                "sn": str(sn or ""),
                "hist": dict(hist),
                "raw": dict(raw),
                "packet_index": packet_index,
                "packet_count": len(raw_packets),
            })
    out.sort(key=lambda x: (str(x.get("sn") or ""), float(x.get("wall_ts") or 0.0), int(x.get("seq") or 0)))
    return out

def _history_raw_hex_to_bytes(raw_hex: str) -> bytes:
    text = str(raw_hex or "")
    if "..." in text:
        text = text.split("...", 1)[0]
    pairs = re.findall(r"(?i)(?<![0-9a-f])([0-9a-f]{2})(?![0-9a-f])", text)
    if not pairs:
        compact = re.sub(r"(?i)[^0-9a-f]", "", text)
        if len(compact) >= 2:
            if len(compact) % 2:
                compact = compact[:-1]
            pairs = [compact[i:i + 2] for i in range(0, len(compact), 2)]
    if not pairs:
        return b""
    return bytes(int(p, 16) for p in pairs)

def _history_ssid_hint(hist: dict, target_sn: str) -> str:
    ssid = str(hist.get("ssid") or "").strip()
    rid = _ssid_to_sn(ssid) if ssid else None
    if rid:
        return rid
    target = str(target_sn or "").strip()
    if len(target) == RID_NEW_FW_SN_LEN and target.isalnum():
        return target
    return ""

def _history_decode_old_payloads(data: bytes) -> dict:
    merged = {"basic_id": None, "location": None, "system": None}
    payloads = []
    try:
        payloads = list(extract_from_raw(data) or [])
    except Exception:
        payloads = []
    try:
        if not payloads and _valid_payload(data):
            payloads = [data]
    except Exception:
        pass
    for payload in payloads:
        try:
            decoded = decode_odid(payload)
        except Exception:
            continue
        if decoded.get("basic_id") and not merged.get("basic_id"):
            merged["basic_id"] = decoded.get("basic_id")
        if decoded.get("location") and not merged.get("location"):
            merged["location"] = decoded.get("location")
        if decoded.get("system") and not merged.get("system"):
            merged["system"] = decoded.get("system")
    return merged

def _history_decode_raw_packet(data: bytes, hist: dict, target_sn: str) -> tuple[dict | None, str, bytes]:
    ssid_hint = _history_ssid_hint(hist, target_sn)
    try:
        new_payloads = list(extract_new_firmware_from_raw(data, ssid_hint) or [])
    except Exception:
        new_payloads = []
    if new_payloads:
        body, decoded = new_payloads[-1]
        return decoded, "new", bytes(body or b"")
    pos = data.find(DJI_RID_VENDOR_PREFIX)
    if pos >= 0:
        body = data[pos:]
        decoded = decode_new_firmware_payload(body, ssid_hint)
        if decoded:
            return decoded, "new", body
    decoded = _history_decode_old_payloads(data)
    if decoded.get("basic_id") or decoded.get("location") or decoded.get("system"):
        return decoded, "old", data
    return None, "", data

def _history_track_replace_latest(record: dict, lat, lon, wall_ts: float) -> None:
    try:
        lat_f = float(lat)
        lon_f = float(lon)
    except Exception:
        return
    if not ((-90.0 <= lat_f <= 90.0) and (-180.0 <= lon_f <= 180.0)):
        return
    track = _sanitize_track(record.get("track") or [])
    point = {"lat": round(lat_f, 7), "lon": round(lon_f, 7), "ts": float(wall_ts or time.time())}
    if track:
        try:
            last_ts = float(track[-1].get("ts") or 0.0)
        except Exception:
            last_ts = 0.0
        if not wall_ts or abs(last_ts - float(wall_ts)) <= 120.0 or last_ts <= float(wall_ts):
            track[-1] = point
        else:
            track.append(point)
    else:
        track.append(point)
    record["track"] = _sanitize_track(track)
    record["track_updated_wall_ts"] = float(record["track"][-1].get("ts") or time.time())

def _history_raw_packet_matches(a: dict, b: dict) -> bool:
    if not isinstance(a, dict) or not isinstance(b, dict):
        return False
    if str(a.get("hex") or "").strip() != str(b.get("hex") or "").strip():
        return False
    b_ts = str(b.get("ts") or "").strip()
    if b_ts:
        return str(a.get("ts") or "").strip() == b_ts
    return True

def _history_update_raw_packet_metadata(record: dict, hist: dict, raw: dict) -> None:
    packets = list(record.get("raw_packets") or hist.get("raw_packets") or [])[-HISTORY_RAW_PACKET_LIMIT:]
    if isinstance(raw, dict) and raw.get("hex"):
        replaced = False
        for idx in range(len(packets) - 1, -1, -1):
            if _history_raw_packet_matches(packets[idx], raw):
                packets[idx] = dict(raw)
                replaced = True
                break
        if not replaced:
            packets.append(dict(raw))
    record["raw_packets"] = packets[-HISTORY_RAW_PACKET_LIMIT:]

def _history_apply_reidentified_locked(target_sn: str, hist: dict, raw: dict, decoded: dict, firmware_type: str, body: bytes) -> dict:
    basic = decoded.get("basic_id") if isinstance(decoded, dict) else None
    loc = decoded.get("location") if isinstance(decoded, dict) else None
    sys_loc = decoded.get("system") if isinstance(decoded, dict) else None
    meta = decoded.get("metadata") if isinstance(decoded, dict) else None
    parsed_sn = ""
    id_type = hist.get("id_type")
    if isinstance(basic, dict):
        parsed_sn = str(basic.get("uas_id") or "").strip()
        id_type = basic.get("id_type") or id_type
    old_sn = str(target_sn or "").strip()
    sn = parsed_sn if parsed_sn and (old_sn.startswith("MAC:") or old_sn != parsed_sn) else old_sn
    if not sn:
        sn = parsed_sn or old_sn
    existing = history_table.get(sn) if sn != old_sn else None
    record = dict(existing) if isinstance(existing, dict) else dict(hist)
    if sn != old_sn and old_sn in history_table:
        old_record = history_table.pop(old_sn)
        if existing:
            _history_merge(record, old_record)
    record["sn"] = sn
    if id_type:
        record["id_type"] = id_type
    uas_id_value = _uas_id_clean(decoded.get("uas_id"))
    record["uas_id"] = uas_id_value
    record["firmware_type"] = _firmware_type_key(firmware_type)
    record["scan_type"] = _scan_type_key(record.get("scan_type"))
    record["model"] = _resolve_model_name(sn, record.get("scan_type"), record.get("model"))
    cap_wall = _history_raw_packet_wall_ts(raw, record.get("last_capture_wall_ts") or record.get("last_seen_wall_ts"))
    if cap_wall:
        record["last_capture_wall_ts"] = cap_wall
        record["last_seen_wall_ts"] = max(float(record.get("last_seen_wall_ts") or 0.0), float(cap_wall))
    if isinstance(raw, dict):
        raw["firmware_type"] = record["firmware_type"]
        raw["uas_id"] = uas_id_value
    _history_update_raw_packet_metadata(record, hist, raw)
    if record["firmware_type"] == "new":
        for key in NEW_FW_DETAIL_KEYS:
            record[key] = meta.get(key) if isinstance(meta, dict) else None
        if body:
            record["raw_vendor"] = body.hex()
    elif isinstance(meta, dict):
        _copy_new_fw_detail(record, meta)
    if isinstance(loc, dict):
        for key, src_key in (
            ("lat", "lat"),
            ("lon", "lon"),
            ("alt", "alt_geodetic"),
            ("speed", "speed_ms"),
            ("vspeed", "vspeed_ms"),
            ("move_dir", "direction_deg"),
            ("alt_relative", "alt_relative"),
            ("alt_geoid", "alt_geoid"),
            ("alt_baro", "alt_baro"),
        ):
            if src_key in loc:
                record[key] = loc.get(src_key)
    elif record["firmware_type"] == "new":
        for key in ("lat", "lon", "alt", "speed", "vspeed", "move_dir", "alt_relative", "alt_geoid", "alt_baro"):
            record[key] = None
    if isinstance(sys_loc, dict):
        record["pilot_lat"] = sys_loc.get("pilot_lat")
        record["pilot_lon"] = sys_loc.get("pilot_lon")
        record["pilot_alt"] = sys_loc.get("pilot_alt")
        record["pilot_loc_type"] = sys_loc.get("pilot_loc_type")
        record["pilot_loc_type_text"] = str(sys_loc.get("pilot_loc_type_text") or "")
    elif record["firmware_type"] == "new":
        for key in ("pilot_lat", "pilot_lon", "pilot_alt", "pilot_loc_type", "pilot_loc_type_text"):
            record[key] = None if key != "pilot_loc_type_text" else ""
    if record.get("lat") is not None and record.get("lon") is not None:
        _history_track_replace_latest(record, record.get("lat"), record.get("lon"), cap_wall or time.time())
    history_table[sn] = record
    if sn != old_sn and old_sn in state_table:
        if sn not in state_table:
            state_table[sn] = state_table.pop(old_sn)
            state_table[sn]["sn"] = sn
        else:
            state_table.pop(old_sn, None)
    state_entry = state_table.get(sn)
    if isinstance(state_entry, dict):
        for key in (
            "id_type", "uas_id", "model", "lat", "lon", "alt", "speed", "vspeed", "move_dir",
            "pilot_lat", "pilot_lon", "pilot_alt", "pilot_loc_type", "pilot_loc_type_text",
            "firmware_type", "last_capture_wall_ts", "raw_packets", "track", "track_updated_wall_ts",
        ) + NEW_FW_DETAIL_KEYS:
            if key in record:
                state_entry[key] = record.get(key)
    _history_mark_dirty()
    return record

def reidentify_recent_history_packets(limit: int = HISTORY_RAW_PACKET_LIMIT) -> dict:
    try:
        effective_limit = max(1, min(int(limit or HISTORY_RAW_PACKET_LIMIT), HISTORY_RAW_PACKET_LIMIT))
    except Exception:
        effective_limit = HISTORY_RAW_PACKET_LIMIT
    with state_lock:
        candidates = _history_recent_raw_packet_candidates_locked(effective_limit)
    if not candidates:
        return {"ok": False, "error": "no history raw packet"}
    decoded_count = 0
    skipped_count = 0
    failed_count = 0
    migrated_count = 0
    updated_sns: set[str] = set()
    formats: dict[str, int] = {}
    errors: list[dict] = []
    aircraft_seen = {str(item.get("sn") or "") for item in candidates if str(item.get("sn") or "")}
    for item in candidates:
        target_sn = str(item.get("sn") or "")
        hist = item.get("hist") if isinstance(item.get("hist"), dict) else {}
        raw = item.get("raw") if isinstance(item.get("raw"), dict) else {}
        data = _history_raw_hex_to_bytes(str(raw.get("hex") or ""))
        if not data:
            skipped_count += 1
            if len(errors) < 8:
                errors.append({"sn": target_sn, "error": "raw packet has no usable hex"})
            continue
        decoded, firmware_type, body = _history_decode_raw_packet(data, hist, target_sn)
        if not decoded:
            failed_count += 1
            if len(errors) < 8:
                errors.append({"sn": target_sn, "error": "raw packet could not be decoded"})
            continue
        with state_lock:
            record = _history_apply_reidentified_locked(target_sn, hist, raw, decoded, firmware_type, body)
        decoded_count += 1
        sn_now = str(record.get("sn") or target_sn)
        updated_sns.add(sn_now)
        if sn_now and sn_now != target_sn:
            migrated_count += 1
        fmt = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or firmware_type or "unknown")
        formats[fmt] = int(formats.get(fmt, 0)) + 1
    saved = save_history_store(force=True)
    _log(
        "[INFO] history recent packets reidentified: "
        f"aircraft={len(updated_sns)}/{len(aircraft_seen)} packets={decoded_count}/{len(candidates)} "
        f"skipped={skipped_count} failed={failed_count} migrated={migrated_count}"
    )
    return {
        "ok": True,
        "limit": effective_limit,
        "aircraft_count": len(aircraft_seen),
        "updated_aircraft": len(updated_sns),
        "packet_count": len(candidates),
        "decoded": decoded_count,
        "skipped": skipped_count,
        "failed": failed_count,
        "migrated": migrated_count,
        "formats": formats,
        "errors": errors,
        "saved": bool(saved),
    }

def reidentify_latest_history_packet() -> dict:
    return reidentify_recent_history_packets(limit=HISTORY_RAW_PACKET_LIMIT)

def state_update(src_mac: str, decoded: dict, rssi: int | None,
                 ch: int, ch_assumed: bool, pl_sig: int,
                 *, scan_type: str = "rid", ssid: str | None = None,
                 capture_type: str | None = None, raw_pkt_hex: str | None = None,
                 firmware_type: str | None = "old") -> None:
    basic = decoded.get("basic_id")
    loc   = decoded.get("location")
    sys_loc = decoded.get("system")
    meta = decoded.get("metadata") if isinstance(decoded, dict) else None
    uas_id_value = _uas_id_clean(decoded.get("uas_id"))

    if basic and basic.get("uas_id"):
        mac_to_basic[src_mac] = {"basic": basic, "ts": time.monotonic()}
        if len(mac_to_basic) > MAC_BASIC_CACHE_MAX:
            old = sorted(mac_to_basic.items(), key=lambda kv: kv[1].get("ts",0))
            for k,_ in old[:max(1,MAC_BASIC_CACHE_MAX//10)]: mac_to_basic.pop(k,None)

    ssid_sn = mac_to_ssid_sn.get(src_mac,{}).get("sn")
    mac_key = f"MAC:{src_mac}"

    if basic and basic.get("uas_id"):
        sn, it = basic["uas_id"].strip(), basic.get("id_type","unknown")
    elif ssid_sn:
        sn, it = ssid_sn, "SSID"
    elif src_mac in mac_to_basic:
        c  = mac_to_basic[src_mac].get("basic",{})
        sn = (c.get("uas_id","") or "").strip() or mac_key
        it = c.get("id_type","unknown")
    else:
        sn, it = mac_key, "unknown"

    scan_type_key = _scan_type_key(scan_type)
    firmware_type_key = _firmware_type_key(firmware_type)
    model = _resolve_model_name(sn, scan_type_key, None)
    now   = time.monotonic()
    now_wall = time.time()

    with state_lock:
        # MAC -> SN migration
        if sn != mac_key and mac_key in state_table and sn not in state_table:
            state_table[sn] = state_table.pop(mac_key)
            state_table[sn].update({"sn":sn, "id_type":it, "_first_printed":False})
        if sn != mac_key and mac_key in history_table:
            if sn in history_table:
                _history_merge(history_table[sn], history_table.pop(mac_key))
            else:
                history_table[sn] = history_table.pop(mac_key)
                history_table[sn]["sn"] = sn

        created = False
        if sn not in state_table:
            created = True
            state_table[sn] = {
                "sn":sn, "src_mac":src_mac, "id_type":it, "model":model,
                "first_seen_ts":now, "last_seen_ts":now,
                "first_seen_wall_ts":now_wall, "last_seen_wall_ts":now_wall,
                "session_start_ts":now, "session_start_wall_ts":now_wall,
                "last_online_duration_sec":None,
                "last_print_ts":0.0,
                "pl_sig":None, "rssi":None, "last_ch":None, "ch_assumed":False,
                "lat":None, "lon":None, "alt":None, "speed":None, "vspeed":None,
                "pilot_lat":None, "pilot_lon":None,
                "pilot_alt":None,
                "pilot_loc_type":None, "pilot_loc_type_text":"",
                "scan_type":scan_type_key,
                "firmware_type":firmware_type_key,
                "uas_id":uas_id_value,
                "ssid":(ssid or ""),
                "capture_type":(capture_type or ""),
                "last_capture_wall_ts":now_wall,
                "raw_packets":[],
                "track":[],
                "track_updated_wall_ts":None,
                "pkt_count":0, "rx_avg":None, "last_pkt_ts":now,
                "reported_lost":False, "_last_shown":None, "_first_printed":False,
                "_prev_lat":None, "_prev_lon":None, "move_dir":None, "move_dist":None,
                "_dirty":True, "_dirty_keys":set(), "_hl":{},
                "_notify_online_sent": False,
                "_notify_last_wall_ts": 0.0,
            }

        e = state_table[sn]
        was_lost = bool(e.get("reported_lost"))
        e["last_seen_ts"]  = now
        e["last_seen_wall_ts"] = now_wall
        e["reported_lost"] = False
        if created or was_lost:
            e["session_start_ts"] = now
            e["session_start_wall_ts"] = now_wall
            e["last_online_duration_sec"] = None
        e["pkt_count"]    += 1
        if e["pkt_count"] > 1:
            iv = now - e["last_pkt_ts"]
            e["rx_avg"] = 0.3*iv + 0.7*(e["rx_avg"] or iv)
        e["last_pkt_ts"] = now
        e["id_type"] = it or e.get("id_type")
        e["model"]   = _resolve_model_name(sn, scan_type_key, e.get("model"))
        e["scan_type"] = scan_type_key
        if firmware_type_key == "new" or _firmware_type_key(e.get("firmware_type")) != "new":
            e["firmware_type"] = firmware_type_key
        if uas_id_value:
            e["uas_id"] = uas_id_value
        if firmware_type_key == "new":
            _copy_new_fw_detail(e, meta)
        if ssid is not None:
            e["ssid"] = str(ssid)
        e["capture_type"] = str(capture_type or e.get("capture_type") or "")
        e["last_capture_wall_ts"] = now_wall
        if raw_pkt_hex:
            rp = list(e.get("raw_packets") or [])
            if (not rp) or (str(rp[-1].get("hex") or "") != str(raw_pkt_hex)):
                rp.append({
                    "ts": _fmt_wall_ts(now_wall),
                    "capture_type": str(capture_type or ""),
                    "firmware_type": firmware_type_key,
                    "uas_id": uas_id_value,
                    "hex": str(raw_pkt_hex),
                })
                if len(rp) > HISTORY_RAW_PACKET_LIMIT:
                    rp = rp[-HISTORY_RAW_PACKET_LIMIT:]
                e["raw_packets"] = rp

        if CHANGE_ON_PL:   e["pl_sig"] = pl_sig
        if rssi is not None:
            old = e.get("rssi")
            if old is None or not CHANGE_ON_RSSI or abs(rssi-old)>=RSSI_DELTA:
                e["rssi"] = rssi
        if ch:
            e["last_ch"]   = ch
            e["ch_assumed"] = bool(ch_assumed)

        new_fw_base = _web_base_coord_pair() if firmware_type_key == "new" else None
        if loc:
            cands = loc.get("_cands") if isinstance(loc, dict) else None
            if cands and e.get("lat") is not None and e.get("lon") is not None:
                prev_lat = float(e.get("lat"))
                prev_lon = float(e.get("lon"))
                best_c = None
                best_d = None
                cur_d = None
                try:
                    if loc.get("lat") is not None and loc.get("lon") is not None:
                        cur_d = _haversine(prev_lat, prev_lon, float(loc["lat"]), float(loc["lon"]))
                except Exception:
                    cur_d = None
                for c in cands:
                    try:
                        lat_c = float(c.get("lat"))
                        lon_c = float(c.get("lon"))
                    except Exception:
                        continue
                    d_c = _haversine(prev_lat, prev_lon, lat_c, lon_c)
                    if best_d is None or d_c < best_d:
                        best_d = d_c
                        best_c = c
                if best_c is not None and (cur_d is None or (best_d is not None and best_d + 50.0 < cur_d)):
                    loc = best_c
            if firmware_type_key == "new":
                try:
                    cur_lat = None if e.get("lat") is None else float(e.get("lat"))
                    cur_lon = None if e.get("lon") is None else float(e.get("lon"))
                    ref_lat = new_fw_base[0] if new_fw_base else None
                    ref_lon = new_fw_base[1] if new_fw_base else None
                    if loc.get("lat") is not None and loc.get("lon") is not None:
                        if _new_fw_coord_anomalous(float(loc.get("lat")), float(loc.get("lon")),
                                                   prev_lat=cur_lat, prev_lon=cur_lon,
                                                   ref_lat=ref_lat, ref_lon=ref_lon):
                            loc = None
                except Exception:
                    loc = None

            if loc:
                nlat, nlon = loc.get("lat"), loc.get("lon")
                if nlat is not None and nlon is not None and (abs(nlat)>0.001 or abs(nlon)>0.001):
                    if e["lat"] is not None:
                        e["_prev_lat"], e["_prev_lon"] = e["lat"], e["lon"]
                    e["lat"], e["lon"] = nlat, nlon
                    if e.get("_prev_lat") is not None:
                        d = _haversine(e["_prev_lat"],e["_prev_lon"],nlat,nlon)
                        if d >= HEADING_MIN_MOVE_M:
                            b = _bearing(e["_prev_lat"],e["_prev_lon"],nlat,nlon)
                            if b is not None:
                                e["move_dir"]  = _bearing8(b)
                                e["move_dist"] = d
                e["alt"]    = loc.get("alt_geodetic")
                e["speed"]  = loc.get("speed_ms")
                e["vspeed"] = loc.get("vspeed_ms")
                if loc.get("direction_deg") is not None:
                    e["move_dir"] = loc.get("direction_deg")
                if firmware_type_key == "new":
                    for key, src_key in (
                        ("alt_relative", "alt_relative"),
                        ("alt_geoid", "alt_geoid"),
                        ("alt_baro", "alt_baro"),
                    ):
                        if loc.get(src_key) is not None:
                            e[key] = loc.get(src_key)
                if e.get("lat") is not None and e.get("lon") is not None:
                    _track_append_point(e, float(e.get("lat")), float(e.get("lon")), float(now_wall))

        if sys_loc and (sys_loc.get("pilot_lat") is not None) and (sys_loc.get("pilot_lon") is not None):
            try:
                plat = float(sys_loc.get("pilot_lat"))
                plon = float(sys_loc.get("pilot_lon"))
                if firmware_type_key == "new":
                    cur_lat = None if e.get("lat") is None else float(e.get("lat"))
                    cur_lon = None if e.get("lon") is None else float(e.get("lon"))
                    ref_lat = new_fw_base[0] if new_fw_base else None
                    ref_lon = new_fw_base[1] if new_fw_base else None
                    if _new_fw_coord_anomalous(plat, plon,
                                               prev_lat=cur_lat, prev_lon=cur_lon,
                                               ref_lat=ref_lat, ref_lon=ref_lon):
                        raise ValueError("pilot coord anomaly")
                if (-90.0 <= plat <= 90.0) and (-180.0 <= plon <= 180.0):
                    e["pilot_lat"] = plat
                    e["pilot_lon"] = plon
                    e["pilot_alt"] = sys_loc.get("pilot_alt")
                    e["pilot_loc_type"] = sys_loc.get("pilot_loc_type")
                    e["pilot_loc_type_text"] = str(sys_loc.get("pilot_loc_type_text") or "")
            except Exception:
                pass

        alarm_zone_hits = _alarm_zone_names_for_point(e.get("lat"), e.get("lon"))
        prev_alarm_zone_hits = {str(x) for x in (e.get("_alarm_zone_hits_current") or [])}
        new_alarm_zone_hits = [z for z in alarm_zone_hits if str(z) not in prev_alarm_zone_hits]
        e["_alarm_zone_hits_current"] = list(alarm_zone_hits)
        e["alarm_zone_hits"] = list(alarm_zone_hits)

        _history_touch(e, now, now_wall)
        h_notify = history_table.get(sn) or {}

        notify_event_title = None
        sn_now = str(e.get("sn",""))
        skip_mac_only = bool(NOTIFY_CFG.get("skip_mac_only", True))
        if not (skip_mac_only and sn_now.startswith("MAC:")):
            if not bool(h_notify.get("notify_first_online_sent")):
                notify_event_title = "上线"
                h_notify["notify_first_online_sent"] = True
                h_notify["notify_last_wall_ts"] = now_wall
                _history_mark_dirty()
            elif was_lost and bool(NOTIFY_CFG.get("notify_reonline", True)):
                last_nt = float(h_notify.get("notify_last_wall_ts") or 0.0)
                cd_sec = float(NOTIFY_CFG.get("reonline_cooldown_sec") or NOTIFY_REONLINE_COOLDOWN_DEFAULT)
                if (now_wall - last_nt) >= max(0.0, cd_sec):
                    notify_event_title = "重新上线"
                    h_notify["notify_last_wall_ts"] = now_wall
                    _history_mark_dirty()
        notify_payload = dict(e) if notify_event_title else None
        zone_notify_payload = None
        zone_notify_names: list[str] = []
        if new_alarm_zone_hits and not (skip_mac_only and sn_now.startswith("MAC:")):
            zone_notify_payload = dict(e)
            zone_notify_names = list(new_alarm_zone_hits)

        _SNAP_TO_COL = {"lat":"lat_s","lon":"lon_s","alt":"alt_s","speed":"spd_s",
                        "vspeed":"vsp_s","last_ch":"ch_s","move_dir":"dir_s",
                        "rssi":"rssi_s","model":"model","sn":"sn_s","uas_id":"uas_id"}
        cur     = _snap(e)
        changed = {k for k,v in cur.items() if (e.get("_last_shown") or {}).get(k)!=v}
        if changed:
            e["_dirty"] = True
            e["_dirty_keys"].update(changed)
            hl_until = now + 3.0
            if "_hl" not in e: e["_hl"] = {}
            for k in changed:
                e["_hl"][_SNAP_TO_COL.get(k, k)] = hl_until

        elapsed = now - e.get("last_print_ts", 0.0)
        do_print = False
        reason   = ""
        if not e.get("_first_printed"):
            do_print, reason = True, "first"
        elif e.get("_dirty") and elapsed >= MIN_GAP:
            do_print = True
            reason = "changed" if changed else "tick"
        elif e.get("_dirty") and elapsed >= PRINT_INTERVAL:
            do_print, reason = True, "heartbeat"

        if do_print:
            _emit_log(e, set(e.get("_dirty_keys") or set()), reason)
            e["last_print_ts"]  = now
            e["_last_shown"]    = cur
            e["_first_printed"] = True
            e["_dirty"]         = False
            e["_dirty_keys"]    = set()

    if notify_payload is not None and notify_event_title:
        _notification_add(_notify_online_text(notify_payload, notify_event_title, now_wall), "ok", "rid")
        queue_online_notification(notify_payload, notify_event_title, now_wall=now_wall)
    if zone_notify_payload is not None and zone_notify_names:
        _notification_add(_notify_zone_alarm_text(zone_notify_payload, zone_notify_names, now_wall), "warn", "rid")
        queue_zone_alarm_notification(zone_notify_payload, zone_notify_names, now_wall=now_wall)

def _emit_log(e: dict, changed_keys: set, reason: str) -> None:
    sn    = str(e.get("sn",""))
    model = str(e.get("model","N/A"))
    it    = str(e.get("id_type",""))
    mac   = str(e.get("src_mac",""))
    uas   = _uas_id_clean(e.get("uas_id"))
    lat   = _fmt(e.get("lat"),".6f")
    lon   = _fmt(e.get("lon"),".6f")
    alt   = _fmt(e.get("alt"),".1f","m")
    spd   = _fmt(e.get("speed"),".2f","m/s")
    vsp   = _fmt(e.get("vspeed"),".1f","m/s")
    rssi  = _fmt(e.get("rssi"),"d","dBm")
    ch    = e.get("last_ch") or 0
    ch_s  = f"{'~' if e.get('ch_assumed') else ''}ch{ch}" if ch else "ch?"
    pkts  = e.get("pkt_count",0)
    avg   = e.get("rx_avg")
    avg_s = f"{avg:.1f}s" if avg else "N/A"
    mv    = e.get("move_dir")
    md    = e.get("move_dist")
    mv_s  = f" dir={mv} d={md:.1f}m" if mv and md else ""
    uas_s = f" uas={uas}" if uas else ""
    pfx   = "★" if reason=="first" else "→"
    _log(f"{pfx} SN={sn}{uas_s} model={model} id={it} MAC={mac} "
         f"loc={lat},{lon} alt={alt} spd={spd} vspd={vsp} rssi={rssi} {ch_s} "
         f"pkts={pkts} avg={avg_s}{mv_s}")

# -----------------------------------------------------------------------------
# Lost checker
# -----------------------------------------------------------------------------
def lost_checker() -> None:
    while True:
        time.sleep(1.0)
        now = time.monotonic()
        with state_lock:
            for sn, e in list(state_table.items()):
                age = now - e["last_seen_ts"]
                if age > LOST_TIMEOUT and not e["reported_lost"]:
                    dur = None
                    try:
                        st = e.get("session_start_ts")
                        ls = e.get("last_seen_ts")
                        if st is not None and ls is not None:
                            dur = max(0.0, float(ls) - float(st))
                    except Exception:
                        dur = None
                    if dur is None:
                        try:
                            stw = e.get("session_start_wall_ts")
                            lsw = e.get("last_seen_wall_ts")
                            if stw is not None and lsw is not None:
                                dur = max(0.0, float(lsw) - float(stw))
                        except Exception:
                            dur = None
                    if dur is not None:
                        e["last_online_duration_sec"] = dur
                        h = history_table.get(sn)
                        if h is not None:
                            h["last_online_duration_sec"] = dur
                            _history_mark_dirty()
                    _log(f"[LOST] SN={sn!r} unseen {age:.0f}s MAC={e.get('src_mac')}")
                    _notification_add(_notify_lost_text(e, age, time.time()), "warn", "rid")
                    e["reported_lost"] = True
                if e["reported_lost"] and age > PURGE_TIMEOUT:
                    del state_table[sn]

# -----------------------------------------------------------------------------
# HTTP + WebSocket service (port 4600)
# -----------------------------------------------------------------------------
HTTP_PORT = 4600

# Connected websocket client sockets
_ws_clients: list = []
_ws_lock = Lock()

def _ws_push_loop() -> None:
    """Push latest state JSON to all websocket clients every second."""
    import json as _json
    while True:
        time.sleep(1.0)
        payload = _json.dumps(_state_snapshot(), ensure_ascii=False)
        frame   = _ws_frame(payload.encode())
        dead    = []
        with _ws_lock:
            clients = list(_ws_clients)
        for sock in clients:
            try:
                sock.sendall(frame)
            except Exception:
                dead.append(sock)
        if dead:
            with _ws_lock:
                for s in dead:
                    try: s.close()
                    except Exception: pass
                    if s in _ws_clients: _ws_clients.remove(s)

def _ws_frame(data: bytes) -> bytes:
    """Build a server-side websocket text frame (RFC 6455, no masking)."""
    n = len(data)
    if n <= 125:
        return bytes([0x81, n]) + data
    if n <= 65535:
        return bytes([0x81, 126, (n>>8)&0xFF, n&0xFF]) + data
    return bytes([0x81, 127]) + n.to_bytes(8,"big") + data


def _fmt_wall_ts(ts: float | None) -> str:
    if not ts:
        return "-"
    try:
        return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(ts))
    except Exception:
        return "-"

def _state_snapshot() -> dict:
    """Return a JSON-serializable snapshot of current runtime state."""
    now = time.monotonic()
    now_wall = time.time()
    with state_lock:
        live_by_sn = {str(e.get("sn","")): e for e in state_table.values() if e.get("sn")}
        drones = []
        for sn in (set(history_table.keys()) | set(live_by_sn.keys())):
            sn = str(sn or "")
            cur = live_by_sn.get(sn) or {}
            hist = history_table.get(sn) or cur
            scan_type_key = _scan_type_key(cur.get("scan_type", hist.get("scan_type", "rid")))
            firmware_type_key = _firmware_type_key(cur.get("firmware_type", hist.get("firmware_type", "old")))
            if scan_type_key != "phone" and (len(sn) != 20 or (not sn.isalnum())):
                continue
            model_name = _resolve_model_name(sn, scan_type_key, cur.get("model", hist.get("model")))
            if cur:
                last_seen_ts = cur.get("last_seen_ts")
                if last_seen_ts is None:
                    last_seen_ts = now
                age = max(0.0, now - last_seen_ts)
            else:
                last_seen_wall = hist.get("last_seen_wall_ts")
                if last_seen_wall is None:
                    age = 0.0
                else:
                    try:
                        age = max(0.0, now_wall - float(last_seen_wall))
                    except Exception:
                        age = 0.0
            lost = age > LOST_TIMEOUT
            id_src = str(cur.get("id_type", hist.get("id_type","")) or "")
            sn_src = _sn_source_display(id_src)
            scan_type = _scan_type_display(scan_type_key)
            firmware_type = _firmware_type_display(firmware_type_key)
            online_dur = None
            if cur:
                if lost:
                    online_dur = cur.get("last_online_duration_sec")
                    if online_dur is None:
                        try:
                            st = cur.get("session_start_ts")
                            ls = cur.get("last_seen_ts")
                            if st is not None and ls is not None:
                                online_dur = max(0.0, float(ls) - float(st))
                        except Exception:
                            online_dur = None
                else:
                    try:
                        st = cur.get("session_start_ts", cur.get("first_seen_ts"))
                        if st is not None:
                            online_dur = max(0.0, now - float(st))
                    except Exception:
                        online_dur = None
                if online_dur is None:
                    online_dur = hist.get("last_online_duration_sec")
            else:
                online_dur = hist.get("last_online_duration_sec")
            ch = cur.get("last_ch", hist.get("last_ch")) or 0
            ch_assumed = bool(cur.get("ch_assumed", hist.get("ch_assumed")))
            cap_wall_ts = cur.get("last_capture_wall_ts", hist.get("last_capture_wall_ts"))
            track_data = _track_for_query(cur.get("track", hist.get("track", [])) or [],
                                          firmware_type=firmware_type_key)
            drones.append({
                "sn": sn,
                "sn_src": sn_src,
                "uas_id": _uas_id_clean(cur.get("uas_id") or hist.get("uas_id","")),
                "scan_type": scan_type,
                "firmware_type": firmware_type,
                "firmware_type_key": firmware_type_key,
                "kind": cur.get("kind", hist.get("kind")),
                "rid_format": cur.get("rid_format", hist.get("rid_format")),
                "dji_rid_kind": cur.get("dji_rid_kind", hist.get("dji_rid_kind")),
                "parse_note": cur.get("parse_note", hist.get("parse_note")),
                "raw_vendor": cur.get("raw_vendor", hist.get("raw_vendor")),
                "model": model_name,
                "lost": lost,
                "archived": sn not in live_by_sn,
                "mac": cur.get("src_mac", hist.get("src_mac","")),
                "id_type": id_src or "-",
                "ch": f"{'~' if ch_assumed else ''}{ch}" if ch else "?",
                "ch_assumed": ch_assumed,
                "lat": cur.get("lat", hist.get("lat")),
                "lon": cur.get("lon", hist.get("lon")),
                "alt": cur.get("alt", hist.get("alt")),
                "spd": cur.get("speed", hist.get("speed")),
                "vspd": cur.get("vspeed", hist.get("vspeed")),
                "pilot_lat": cur.get("pilot_lat", hist.get("pilot_lat")),
                "pilot_lon": cur.get("pilot_lon", hist.get("pilot_lon")),
                "pilot_alt": cur.get("pilot_alt", hist.get("pilot_alt")),
                "pilot_loc_type": cur.get("pilot_loc_type", hist.get("pilot_loc_type")),
                "pilot_loc_type_text": cur.get("pilot_loc_type_text", hist.get("pilot_loc_type_text","")) or "",
                "home_lat": cur.get("home_lat", hist.get("home_lat")),
                "home_lon": cur.get("home_lon", hist.get("home_lon")),
                "aux_lat": cur.get("aux_lat", hist.get("aux_lat")),
                "aux_lon": cur.get("aux_lon", hist.get("aux_lon")),
                "alt_candidates": cur.get("alt_candidates", hist.get("alt_candidates")),
                "gb_version": cur.get("gb_version", hist.get("gb_version")),
                "gb_identifiers": cur.get("gb_identifiers", hist.get("gb_identifiers")),
                "operation_category": cur.get("operation_category", hist.get("operation_category")),
                "operation_category_text": cur.get("operation_category_text", hist.get("operation_category_text")),
                "aircraft_category": cur.get("aircraft_category", hist.get("aircraft_category")),
                "aircraft_category_text": cur.get("aircraft_category_text", hist.get("aircraft_category_text")),
                "track_deg": cur.get("track_deg", hist.get("track_deg")),
                "ground_speed": cur.get("ground_speed", hist.get("ground_speed")),
                "vertical_speed": cur.get("vertical_speed", hist.get("vertical_speed")),
                "alt_relative": cur.get("alt_relative", hist.get("alt_relative")),
                "alt_geoid": cur.get("alt_geoid", hist.get("alt_geoid")),
                "alt_baro": cur.get("alt_baro", hist.get("alt_baro")),
                "operation_state": cur.get("operation_state", hist.get("operation_state")),
                "operation_state_text": cur.get("operation_state_text", hist.get("operation_state_text")),
                "coord_sys": cur.get("coord_sys", hist.get("coord_sys")),
                "coord_sys_text": cur.get("coord_sys_text", hist.get("coord_sys_text")),
                "horizontal_accuracy": cur.get("horizontal_accuracy", hist.get("horizontal_accuracy")),
                "vertical_accuracy": cur.get("vertical_accuracy", hist.get("vertical_accuracy")),
                "speed_accuracy": cur.get("speed_accuracy", hist.get("speed_accuracy")),
                "timestamp_ms": cur.get("timestamp_ms", hist.get("timestamp_ms")),
                "timestamp_accuracy": cur.get("timestamp_accuracy", hist.get("timestamp_accuracy")),
                "timestamp_accuracy_text": cur.get("timestamp_accuracy_text", hist.get("timestamp_accuracy_text")),
                "rssi": cur.get("rssi", hist.get("rssi")),
                "pkts": hist.get("pkt_count_total", cur.get("pkt_count",0)),
                "dir": cur.get("move_dir", hist.get("move_dir")) or "-",
                "ssid": cur.get("ssid", hist.get("ssid","")) or "",
                "capture_type": cur.get("capture_type", hist.get("capture_type","")) or "",
                "capture_time": _fmt_wall_ts(cap_wall_ts),
                "last_pkt_time": _fmt_wall_ts(cap_wall_ts),
                "raw_packets": list(cur.get("raw_packets", hist.get("raw_packets", [])) or [])[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:],
                "scan_type_key": scan_type_key,
                "age": round(age),
                "age_text": _fmt_age_compact(age),
                "online_dur": (None if online_dur is None else int(round(float(online_dur)))),
                "first_seen": _fmt_wall_ts(hist.get("first_seen_wall_ts", cur.get("first_seen_wall_ts"))),
                "last_seen": _fmt_wall_ts(hist.get("last_seen_wall_ts", cur.get("last_seen_wall_ts"))),
                "track_count": len(track_data),
                "track_updated": _fmt_wall_ts(hist.get("track_updated_wall_ts", cur.get("track_updated_wall_ts"))),
            })
        drones.sort(key=lambda d: (d["lost"], d.get("archived", False), d["age"], d["sn"]))
        map_drones = [d for d in drones if not d.get("archived")]
    with log_lock:
        logs = list(ap_buf)[-80:]
        logs_seq = ap_seq
    aps, aps_seq, aps_total = _ap_snapshot()
    sniff_meta = _sniff_health_meta(now, now_wall)
    basic_cfg = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
    if not isinstance(basic_cfg, dict):
        basic_cfg = {}
    return {
        "ts": time.strftime("%H:%M:%S"),
        "ch": f"ch{current_channel}" if current_channel else "ch?",
        "drones": drones,
        "map_drones": map_drones,
        "logs": logs,
        "logs_seq": logs_seq,
        "aps": aps,
        "aps_seq": aps_seq,
        "aps_total": aps_total,
        "meta": {
            "dji_lookup_url": str(WEB_CFG.get("dji_lookup_url") or ""),
            "allow_restart": bool(WEB_CFG.get("allow_restart", True)),
            "restart_args_current": " ".join(sys.argv[1:]),
            "restart_args_saved": str(WEB_CFG.get("last_restart_args") or ""),
            "base_name": str(WEB_CFG.get("base_name") or "基站"),
            "base_lat": WEB_CFG.get("base_lat"),
            "base_lon": WEB_CFG.get("base_lon"),
            "base_zoom": WEB_CFG.get("base_zoom"),
            "heading_ref_deg": WEB_CFG.get("heading_ref_deg"),
            "map_auto_center_idle_sec": WEB_CFG.get("map_auto_center_idle_sec"),
            "config_path": APP_CONFIG_PATH or "",
            "iface_selected": (None if basic_cfg.get("iface") in (None, "") else str(basic_cfg.get("iface"))),
            "scan_wifi_fast": bool(basic_cfg.get("scan_wifi_fast")),
            "wifi_fast_supported": WIFI_FAST_SUPPORTED,
            "wifi_fast_msg": str(WIFI_FAST_SUPPORT_MSG or ""),
            "sniff_state": sniff_meta.get("state"),
            "sniff_msg": sniff_meta.get("msg"),
            "sniff_iface": sniff_meta.get("iface"),
            "sniff_idle_sec": sniff_meta.get("idle_sec"),
            "sniff_last_pkt": sniff_meta.get("last_pkt"),
            "sniff_last_err_at": sniff_meta.get("last_err_at"),
            "oobe": _oobe_state(),
            "runtime_security": _runtime_security_payload(unit_text=""),
            "alert_zone": _normalize_web_cfg({"web": {"alarm_zone": WEB_CFG.get("alarm_zone"), "alarm_zones": WEB_CFG.get("alarm_zones")}}).get("alarm_zone"),
            "alert_zones": _normalize_web_cfg({"web": {"alarm_zone": WEB_CFG.get("alarm_zone"), "alarm_zones": WEB_CFG.get("alarm_zones")}}).get("alarm_zones"),
            "settings_path": "/settings",
        },
    }

def _api_iso_now(ts: float | None = None) -> str:
    try:
        return time.strftime("%Y-%m-%dT%H:%M:%S%z", time.localtime(ts if ts is not None else time.time()))
    except Exception:
        return ""

def _load_build_info() -> dict:
    path = _app_file_path(BUILD_INFO_FILE)
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _local_git_commit() -> str:
    repo = _app_root_dir()
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo,
            capture_output=True,
            text=True,
            timeout=3,
        )
        if proc.returncode == 0:
            commit = (proc.stdout or "").strip()
            if re.fullmatch(r"[0-9a-fA-F]{40}", commit or ""):
                return commit.lower()
    except Exception:
        pass
    return ""

def _local_app_commit() -> str:
    commit = _local_git_commit()
    if commit:
        return commit
    commit = str(_load_build_info().get("commit") or "").strip()
    if re.fullmatch(r"[0-9a-fA-F]{7,40}", commit or ""):
        return commit.lower()
    return ""

def _fallback_private_commit() -> str:
    try:
        path = os.path.abspath(_runtime_entrypoint_path())
        st = os.stat(path)
        raw = f"{path}|{st.st_size}|{int(st.st_mtime)}".encode("utf-8", errors="replace")
        return hashlib.sha256(raw).hexdigest()[:7]
    except Exception:
        return "local"

def _app_version_label() -> str:
    info = _load_build_info()
    commit = _local_app_commit()
    try:
        build = int(info.get("build") or 0)
    except Exception:
        build = 0
    if not commit:
        commit = _fallback_private_commit()
    if build <= 0:
        try:
            build = int(os.stat(os.path.abspath(_runtime_entrypoint_path())).st_mtime)
        except Exception:
            build = int(time.time())
    return f"commit:{commit}#{build}"

def _short_commit(commit: str) -> str:
    text = str(commit or "").strip()
    return text[:12] if text else ""

def _app_update_status_payload() -> dict:
    current = _local_app_commit() or _fallback_private_commit()
    with app_update_lock:
        cfg = dict(APP_UPDATE_CFG)
        state = dict(APP_UPDATE_STATE)
    state["current_commit"] = current
    state["current_short"] = _short_commit(current)
    state["latest_short"] = _short_commit(state.get("latest_commit") or "")
    state["commit_url"] = str(cfg.get("commit_url") or APP_UPDATE_COMMIT_URL_DEFAULT)
    state["checked"] = bool(state.get("last_check_ts"))
    return state

def _check_app_update_once(manual: bool = False) -> dict:
    if not manual and not bool(APP_UPDATE_CFG.get("enabled", True)):
        return {"ok": True, "skipped": True, "state": _app_update_status_payload()}
    with app_update_lock:
        if bool(APP_UPDATE_STATE.get("running")):
            busy = True
        else:
            busy = False
            APP_UPDATE_STATE["running"] = True
            APP_UPDATE_STATE["last_error"] = ""
            commit_url = str(APP_UPDATE_CFG.get("commit_url") or APP_UPDATE_COMMIT_URL_DEFAULT)
    if busy:
        return {"ok": False, "error": "程序更新检查正在运行", "state": _app_update_status_payload()}
    try:
        local_commit = _local_app_commit()
        if not local_commit:
            local_commit = _fallback_private_commit()
        req = urllib.request.Request(
            commit_url,
            headers={"User-Agent": APP_HTTP_USER_AGENT + " (+version check)"},
        )
        with urllib.request.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read(256 * 1024).decode("utf-8", errors="replace"))
        remote_commit = str((data if isinstance(data, dict) else {}).get("sha") or "").strip()
        update_available = bool(remote_commit and local_commit and not remote_commit.startswith(local_commit) and not local_commit.startswith(remote_commit[:7]))
        with app_update_lock:
            APP_UPDATE_STATE.update({
                "running": False,
                "last_check_ts": time.time(),
                "latest_commit": remote_commit,
                "current_commit": local_commit,
                "update_available": update_available,
                "last_error": "",
            })
        if update_available:
            _log(f"[INFO] 检测到程序更新: local={local_commit[:12]} remote={remote_commit[:12]}")
        elif remote_commit:
            _log(f"[INFO] 程序更新检查完成: local={local_commit[:12]} remote={remote_commit[:12]}")
        return {"ok": True, "manual": bool(manual), "state": _app_update_status_payload()}
    except Exception as e:
        with app_update_lock:
            APP_UPDATE_STATE.update({
                "running": False,
                "last_check_ts": time.time(),
                "current_commit": _local_app_commit() or _fallback_private_commit(),
                "last_error": str(e),
            })
        _log(f"[WARN] 程序更新检查失败: {e}")
        return {"ok": False, "error": str(e), "state": _app_update_status_payload()}

def start_app_update_check() -> None:
    Thread(target=_check_app_update_once, daemon=True).start()

def _api_meta() -> dict:
    auth_configured = _auth_hashes_present(AUTH_CFG)
    api_configured = _api_tokens_have_secret(API_CFG)
    public_enabled = bool(API_CFG.get("enabled")) and bool(_auth_enabled()) and auth_configured and api_configured
    login_methods = _auth_login_methods()
    return {
        "name": API_NAME,
        "version": API_VERSION,
        "app_version": _app_version_label(),
        "time": _api_iso_now(),
        "web_auth": {
            "type": "login+session",
            "enabled": bool(_auth_enabled()),
            "configured": bool(auth_configured),
            "realm": str(AUTH_CFG.get("realm") or "Light RID Scanner"),
            "session_ttl_min": int(AUTH_CFG.get("session_ttl_min") or 30),
            "login_methods": login_methods,
        },
        "public_api": {
            "enabled": bool(public_enabled),
            "configured": bool(api_configured),
            "header": "X-API-Token",
            "authorization": "Bearer <token>",
            "token_count": len(_api_tokens_public(API_CFG)),
            "supports_multiple_tokens": True,
            "supports_single_use": True,
            "supports_never_expires": True,
            "whitelist_enabled": bool(API_CFG.get("whitelist_enabled")),
            "whitelist_count": len(API_CFG.get("whitelist") or []),
            "mode_when_disabled": "page-session-only",
        },
    }

def _api_endpoint_index() -> list[dict]:
    return [
        {"method": "GET", "path": "/api/docs", "desc": "API docs and auth guide"},
        {"method": "GET", "path": "/api/health", "desc": "Service health"},
        {"method": "GET", "path": "/api/v1/", "desc": "API v1 home and auth summary"},
        {"method": "GET", "path": "/api/v1/snapshot", "desc": "Full runtime snapshot"},
        {"method": "GET", "path": "/api/v1/auth/status", "desc": "Auth status"},
        {"method": "POST", "path": "/api/v1/auth/sso-links/create", "desc": "Create SSO login link"},
        {"method": "GET", "path": "/api/v1/drones", "desc": "Drone list"},
        {"method": "GET", "path": "/api/v1/drones/{sn}", "desc": "Drone detail"},
        {"method": "GET", "path": "/api/v1/tracks/{sn}", "desc": "Track by SN"},
        {"method": "GET", "path": "/api/v1/aps", "desc": "Realtime AP list"},
        {"method": "GET", "path": "/api/v1/logs?type=event|scan|ap&limit=200", "desc": "Logs"},
        {"method": "GET", "path": "/api/settings/export/settings", "desc": "Export settings file"},
        {"method": "GET", "path": "/api/settings/export/scan-data", "desc": "Export scan data"},
        {"method": "POST", "path": "/api/settings/import/settings", "desc": "Import settings file"},
        {"method": "POST", "path": "/api/settings/import/scan-data", "desc": "Import scan data"},
        {"method": "GET", "path": "/api/logs/view?type=runtime|operation|scan|scan_diff|ap", "desc": "Built-in page log viewer"},
        {"method": "GET", "path": "/api/logs/export?type=all|runtime|operation|scan|scan_diff|ap", "desc": "Built-in page log export"},
        {"method": "POST", "path": "/api/v1/history/clear", "desc": "Clear history cache"},
        {"method": "POST", "path": "/api/v1/history/delete", "desc": "Delete one history item"},
        {"method": "POST", "path": "/api/v1/tracks/clear", "desc": "Clear tracks"},
        {"method": "POST", "path": "/api/v1/config/reload", "desc": "Reload config file"},
    ]

