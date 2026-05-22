from station_edition.light_rid.analize_core import normalize_parse_mode, parse_raw_packet

def _snap(e: dict) -> dict:
    s = {k: e.get(k) for k in
         ("sn","src_mac","id_type","uas_id","model","lat","lon","alt","speed","vspeed","last_ch","move_dir")}
    if CHANGE_ON_RSSI: s["rssi"]  = e.get("rssi")
    if CHANGE_ON_PL:   s["pl_sig"] = e.get("pl_sig")
    return s

NEW_FW_DETAIL_KEYS = (
    "kind", "format", "rid_format", "dji_rid_kind", "sub_format",
    "parse_level", "confidence", "coordinate_system", "warnings", "parse_note", "raw_vendor",
    "gb_version", "gb_identifiers",
    "gb_data_type", "gb_version_raw", "gb_data_len", "gb_header", "gb_basic_like", "dji_dynamic",
    "reg_mark", "status", "coord_type",
    "operation_category", "operation_category_text",
    "aircraft_category", "aircraft_category_text",
    "pilot_alt", "track_deg", "ground_speed", "vertical_speed",
    "alt_relative", "alt_geoid", "alt_baro",
    "operation_state", "operation_state_text",
    "coord_sys", "coord_sys_text",
    "horizontal_accuracy", "vertical_accuracy", "speed_accuracy",
    "timestamp_ms", "timestamp_accuracy", "timestamp_accuracy_text",
    "home_lat", "home_lon", "aux_lat", "aux_lon",
    "pos_a_lat", "pos_a_lon", "pos_b_lat", "pos_b_lon",
    "operator_positions", "raw_coords", "aircraft_position", "marker_offset",
)

def _copy_new_fw_detail(dst: dict, src: dict | None) -> None:
    if not isinstance(src, dict):
        return
    for key in NEW_FW_DETAIL_KEYS:
        if key in src:
            dst[key] = src.get(key)

def _role_coord_valid(item: dict | None) -> bool:
    if not isinstance(item, dict):
        return False
    try:
        return bool(_coord_pair_valid(float(item.get("lat")), float(item.get("lon"))))
    except Exception:
        return False

def _aircraft_position_from_decoded(loc: dict | None, meta: dict | None = None) -> dict | None:
    if isinstance(meta, dict):
        pos = meta.get("aircraft_position")
        if _role_coord_valid(pos):
            return dict(pos)
    if not isinstance(loc, dict) or loc.get("lat") is None or loc.get("lon") is None:
        return None
    try:
        lat = float(loc.get("lat"))
        lon = float(loc.get("lon"))
    except Exception:
        return None
    if not _coord_pair_valid(lat, lon):
        return None
    return {
        "lat": round(lat, 7),
        "lon": round(lon, 7),
        "alt": loc.get("alt_geodetic"),
        "role": "aircraft",
        "source": "ODID_LOCATION",
        "offset": None,
        "coordinate_system": "WGS84",
    }

def _operator_positions_from_decoded(sys_loc: dict | None, meta: dict | None = None) -> list[dict]:
    if isinstance(meta, dict):
        positions = [dict(x) for x in (meta.get("operator_positions") or []) if _role_coord_valid(x)]
        if positions:
            return positions
    if not isinstance(sys_loc, dict) or sys_loc.get("pilot_lat") is None or sys_loc.get("pilot_lon") is None:
        return []
    try:
        lat = float(sys_loc.get("pilot_lat"))
        lon = float(sys_loc.get("pilot_lon"))
    except Exception:
        return []
    if not _coord_pair_valid(lat, lon):
        return []
    return [{
        "lat": round(lat, 7),
        "lon": round(lon, 7),
        "alt": sys_loc.get("pilot_alt"),
        "role": "operator",
        "source": "ODID_SYSTEM",
        "offset": None,
        "coordinate_system": "WGS84",
    }]

def _apply_decoded_role_positions(dst: dict, loc: dict | None, sys_loc: dict | None, meta: dict | None = None) -> None:
    aircraft = _aircraft_position_from_decoded(loc, meta)
    if aircraft:
        dst["aircraft_position"] = aircraft
        dst["pos_a_lat"] = aircraft.get("lat")
        dst["pos_a_lon"] = aircraft.get("lon")
    operators = _operator_positions_from_decoded(sys_loc, meta)
    if operators:
        dst["operator_positions"] = operators
        first = operators[0]
        dst["pos_b_lat"] = first.get("lat")
        dst["pos_b_lon"] = first.get("lon")
    raw_coords = []
    if aircraft:
        raw_coords.append(aircraft)
    raw_coords.extend(operators)
    if raw_coords:
        dst["raw_coords"] = raw_coords

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

def _history_parse_mode_key(mode: str | None) -> str:
    return normalize_parse_mode(mode)

def _history_decode_dji_vendor_mode(
    data: bytes,
    hist: dict,
    target_sn: str,
    mode: str,
) -> tuple[dict | None, str, bytes]:
    ssid_hint = _history_ssid_hint(hist, target_sn)
    model_hint = str(hist.get("model") or "")
    result = parse_raw_packet(data, mode, ssid_sn=ssid_hint, model_hint=model_hint)
    body = data
    body_hex = str(result.get("body_hex") or "")
    if body_hex:
        try:
            body = bytes.fromhex(body_hex)
        except Exception:
            body = data
    if result.get("ok") and isinstance(result.get("decoded"), dict):
        return result.get("decoded"), str(result.get("firmware_type") or ""), body
    return None, "", body

def _history_decode_raw_packet(
    data: bytes,
    hist: dict,
    target_sn: str,
    mode: str | None = "auto",
) -> tuple[dict | None, str, bytes, str]:
    mode_key = _history_parse_mode_key(mode)
    ssid_hint = _history_ssid_hint(hist, target_sn)
    model_hint = str(hist.get("model") or "")
    result = parse_raw_packet(data, mode_key, ssid_sn=ssid_hint, model_hint=model_hint)
    body = data
    body_hex = str(result.get("body_hex") or "")
    if body_hex:
        try:
            body = bytes.fromhex(body_hex)
        except Exception:
            body = data
    if result.get("ok") and isinstance(result.get("decoded"), dict):
        return (
            result.get("decoded"),
            str(result.get("firmware_type") or ""),
            body,
            str(result.get("used_mode") or mode_key),
        )
    return None, "", body, str(result.get("used_mode") or mode_key)

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

def _history_track_point_from_decoded(decoded: dict, raw: dict, fallback_ts: float | None = None) -> dict | None:
    loc = decoded.get("location") if isinstance(decoded, dict) else None
    if not isinstance(loc, dict):
        return None
    try:
        lat_f = float(loc.get("lat"))
        lon_f = float(loc.get("lon"))
    except Exception:
        return None
    if not ((-90.0 <= lat_f <= 90.0) and (-180.0 <= lon_f <= 180.0)):
        return None
    if abs(lat_f) < 0.001 and abs(lon_f) < 0.001:
        return None
    return {
        "lat": round(lat_f, 7),
        "lon": round(lon_f, 7),
        "ts": float(_history_raw_packet_wall_ts(raw, fallback_ts or time.time()) or time.time()),
    }

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

def _history_apply_reidentified_locked(
    target_sn: str,
    hist: dict,
    raw: dict,
    decoded: dict,
    firmware_type: str,
    body: bytes,
    *,
    update_track: bool = True,
) -> dict:
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
    _apply_decoded_role_positions(record, loc, sys_loc, meta if isinstance(meta, dict) else None)
    if update_track and record.get("lat") is not None and record.get("lon") is not None:
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
        decoded, firmware_type, body, used_mode = _history_decode_raw_packet(data, hist, target_sn, "auto")
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
        fmt = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or firmware_type or used_mode or "unknown")
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

def reidentify_history_packet_for_sn(sn: str, mode: str | None = "auto") -> dict:
    target_sn = str(sn or "").strip()
    if not target_sn:
        return {"ok": False, "error": "sn required"}
    mode_key = _history_parse_mode_key(mode)
    with state_lock:
        hist = history_table.get(target_sn) or state_table.get(target_sn)
        if not isinstance(hist, dict):
            return {"ok": False, "error": "aircraft not found", "sn": target_sn, "mode": mode_key}
        raw_packets = [
            dict(x)
            for x in list(hist.get("raw_packets") or [])
            if isinstance(x, dict) and str(x.get("hex") or "").strip()
        ]
        hist_copy = dict(hist)
    if not raw_packets:
        return {"ok": False, "error": "no raw packet for aircraft", "sn": target_sn, "mode": mode_key}

    decoded_count = 0
    skipped_count = 0
    failed_count = 0
    errors: list[dict] = []
    formats: dict[str, int] = {}
    used_modes: dict[str, int] = {}
    track_points: list[dict] = []
    sn_now = target_sn
    record: dict | None = None
    for index, raw in enumerate(raw_packets):
        data = _history_raw_hex_to_bytes(str(raw.get("hex") or ""))
        if not data:
            skipped_count += 1
            if len(errors) < 8:
                errors.append({"packet_index": index, "error": "raw packet has no usable hex"})
            continue
        decoded, firmware_type, body, used_mode = _history_decode_raw_packet(data, hist_copy, sn_now, mode_key)
        if not decoded:
            failed_count += 1
            if len(errors) < 8:
                errors.append({"packet_index": index, "error": "raw packet could not be decoded with selected mode"})
            continue
        point = _history_track_point_from_decoded(
            decoded,
            raw,
            hist_copy.get("last_capture_wall_ts") or hist_copy.get("last_seen_wall_ts") or time.time(),
        )
        if point:
            track_points.append(point)
        with state_lock:
            current_hist = history_table.get(sn_now) or history_table.get(target_sn) or hist_copy
            record = _history_apply_reidentified_locked(
                sn_now,
                current_hist,
                raw,
                decoded,
                firmware_type,
                body,
                update_track=False,
            )
        decoded_count += 1
        sn_now = str(record.get("sn") or sn_now)
        hist_copy = dict(record)
        fmt_item = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or firmware_type or used_mode or "unknown")
        formats[fmt_item] = int(formats.get(fmt_item, 0)) + 1
        used_key = str(used_mode or mode_key or "auto")
        used_modes[used_key] = int(used_modes.get(used_key, 0)) + 1
    if not record:
        return {
            "ok": False,
            "error": "no raw packet could be decoded with selected mode",
            "sn": target_sn,
            "mode": mode_key,
            "packet_count": len(raw_packets),
            "decoded": decoded_count,
            "skipped": skipped_count,
            "failed": failed_count,
            "errors": errors,
        }

    track_points = _sanitize_track(sorted(track_points, key=lambda p: float(p.get("ts") or 0.0)))
    with state_lock:
        current = history_table.get(sn_now) or record
        current["track"] = track_points
        current["track_updated_wall_ts"] = float(track_points[-1].get("ts") or time.time()) if track_points else time.time()
        history_table[sn_now] = current
        state_entry = state_table.get(sn_now)
        if isinstance(state_entry, dict):
            state_entry["track"] = list(track_points)
            state_entry["track_updated_wall_ts"] = current.get("track_updated_wall_ts")
        record = dict(current)
        _history_mark_dirty()
    saved = save_history_store(force=True)
    fmt = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or record.get("firmware_type") or "unknown")
    used_summary = ",".join(f"{k}:{v}" for k, v in sorted(used_modes.items())) or mode_key
    _log(
        f"[INFO] history packets reidentified: sn={target_sn} -> {sn_now} "
        f"mode={mode_key} used={used_summary} decoded={decoded_count}/{len(raw_packets)} "
        f"track={len(track_points)} format={fmt}"
    )
    return {
        "ok": True,
        "sn": target_sn,
        "sn_now": sn_now,
        "mode": mode_key,
        "used_mode": used_summary,
        "packet_count": len(raw_packets),
        "decoded": decoded_count,
        "skipped": skipped_count,
        "failed": failed_count,
        "formats": formats,
        "track_count": len(track_points),
        "track": track_points[-TRACK_MAX_POINTS:],
        "errors": errors,
        "firmware_type": record.get("firmware_type"),
        "format": fmt,
        "saved": bool(saved),
        "refresh": True,
        "message": f"reparsed {sn_now} with {mode_key}; rebuilt {len(track_points)} track points",
    }

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
    parser_format = str(meta.get("format") or meta.get("rid_format") or "") if isinstance(meta, dict) else ""
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
            if firmware_type_key == "new" and parser_format != "GB46750_2025":
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
                if firmware_type_key == "new" and parser_format != "GB46750_2025":
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

        _apply_decoded_role_positions(e, loc, sys_loc, meta if isinstance(meta, dict) else None)

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
                "format": cur.get("format", hist.get("format")),
                "rid_format": cur.get("rid_format", hist.get("rid_format")),
                "dji_rid_kind": cur.get("dji_rid_kind", hist.get("dji_rid_kind")),
                "sub_format": cur.get("sub_format", hist.get("sub_format")),
                "parse_level": cur.get("parse_level", hist.get("parse_level")),
                "confidence": cur.get("confidence", hist.get("confidence")),
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
                "pos_a_lat": cur.get("pos_a_lat", hist.get("pos_a_lat")),
                "pos_a_lon": cur.get("pos_a_lon", hist.get("pos_a_lon")),
                "pos_b_lat": cur.get("pos_b_lat", hist.get("pos_b_lat")),
                "pos_b_lon": cur.get("pos_b_lon", hist.get("pos_b_lon")),
                "operator_positions": cur.get("operator_positions", hist.get("operator_positions")),
                "raw_coords": cur.get("raw_coords", hist.get("raw_coords")),
                "aircraft_position": cur.get("aircraft_position", hist.get("aircraft_position")),
                "marker_offset": cur.get("marker_offset", hist.get("marker_offset")),
                "gb_header": cur.get("gb_header", hist.get("gb_header")),
                "gb_basic_like": cur.get("gb_basic_like", hist.get("gb_basic_like")),
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
            "app_update": _app_update_status_payload(consume_notice=True),
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

def _app_update_state_dir() -> str:
    if str(platform.system() or "").lower() == "linux":
        return os.path.join(RUNTIME_SERVICE_HOME, "app_update")
    return os.path.join(tempfile.gettempdir(), "light_rid_app_update")

def _app_update_lock_path() -> str:
    return os.path.join(_app_update_state_dir(), "lock.json")

def _app_update_notice_path() -> str:
    return os.path.join(_app_update_state_dir(), "notice.json")

def _app_update_current_path() -> str:
    return os.path.join(_app_update_state_dir(), "current.json")

def _app_update_stage_root() -> str:
    return os.path.join(tempfile.gettempdir(), "light_rid_app_update_stage")

def _app_update_ensure_dir(path: str) -> str:
    os.makedirs(path, exist_ok=True)
    return path

def _app_update_read_json(path: str) -> dict:
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _app_update_write_json(path: str, payload: dict) -> None:
    parent = os.path.dirname(os.path.abspath(path))
    if parent:
        _app_update_ensure_dir(parent)
    fd, tmp_path = tempfile.mkstemp(prefix="light-rid-update-", suffix=".json", dir=parent or None)
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(payload if isinstance(payload, dict) else {}, f, ensure_ascii=False, indent=2)
            f.write("\n")
        os.replace(tmp_path, path)
    finally:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass

def _app_update_remove_file(path: str) -> None:
    try:
        if os.path.exists(path):
            os.remove(path)
    except Exception:
        pass

def _app_update_pop_notice() -> dict:
    path = _app_update_notice_path()
    data = _app_update_read_json(path)
    if data:
        _app_update_remove_file(path)
    return data

def _local_git_tag() -> str:
    repo = _app_root_dir()
    try:
        proc = subprocess.run(
            ["git", "describe", "--tags", "--exact-match", "HEAD"],
            cwd=repo,
            capture_output=True,
            text=True,
            timeout=3,
        )
        if proc.returncode == 0:
            return str((proc.stdout or "").strip())
    except Exception:
        pass
    return ""

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

def _local_app_tag() -> str:
    tag = _local_git_tag()
    if tag:
        return tag
    info = _load_build_info()
    tag = str(info.get("release_tag") or info.get("tag") or "").strip()
    if tag:
        return tag
    return str(_app_update_read_json(_app_update_current_path()).get("installed_tag") or "").strip()

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

def _app_update_target_arch() -> str:
    machine = ""
    try:
        if hasattr(os, "uname"):
            machine = str(os.uname().machine or "")
    except Exception:
        machine = ""
    if not machine:
        machine = str(platform.machine() or "")
    aliases = {
        "x86_64": "x86_64",
        "amd64": "x86_64",
        "x64": "x86_64",
        "i386": "x32",
        "i686": "x32",
        "x86": "x32",
        "aarch64": "arm64",
        "arm64": "arm64",
        "armv7l": "armv7",
        "armv7": "armv7",
        "armhf": "armv7",
        "arm": "armv7",
    }
    return aliases.get(str(machine or "").strip().lower(), "")

def _app_update_runtime_support() -> dict:
    if str(platform.system() or "").lower() != "linux":
        return {"supported": False, "reason": "自动更新仅支持 Linux systemd 部署。", "target_arch": "", "target_path": ""}
    if not _command_path("systemctl"):
        return {"supported": False, "reason": "未检测到 systemctl，无法自动更新 systemd 服务。", "target_arch": "", "target_path": ""}
    target_arch = _app_update_target_arch()
    if not target_arch:
        return {"supported": False, "reason": "未识别当前系统架构，无法匹配 GitHub Release 资产。", "target_arch": "", "target_path": ""}
    if not getattr(sys, "frozen", False):
        return {"supported": False, "reason": "当前为源码/Python 运行模式；自动更新仅支持单文件发布版。", "target_arch": target_arch, "target_path": ""}
    target_path = os.path.abspath(sys.executable or _runtime_entrypoint_path())
    if not os.path.isfile(target_path):
        return {"supported": False, "reason": "当前可执行文件路径无效，无法执行替换。", "target_arch": target_arch, "target_path": target_path}
    return {"supported": True, "reason": "", "target_arch": target_arch, "target_path": target_path}

def _fetch_latest_release(release_url: str) -> dict:
    req = urllib.request.Request(
        release_url,
        headers={
            "User-Agent": APP_HTTP_USER_AGENT + " (+release update)",
            "Accept": "application/vnd.github+json",
        },
    )
    with urllib.request.urlopen(req, timeout=12) as resp:
        data = json.loads(resp.read(1024 * 1024).decode("utf-8", errors="replace"))
    if not isinstance(data, dict):
        raise RuntimeError("GitHub Release 响应无效")
    assets = data.get("assets")
    return {
        "tag_name": str(data.get("tag_name") or "").strip(),
        "name": str(data.get("name") or "").strip(),
        "target_commitish": str(data.get("target_commitish") or "").strip(),
        "html_url": str(data.get("html_url") or "").strip(),
        "published_at": str(data.get("published_at") or "").strip(),
        "assets": list(assets) if isinstance(assets, list) else [],
    }

def _pick_release_asset(assets: list[dict], target_arch: str) -> dict:
    expected = [
        f"light_rid_station-linux-{target_arch}",
        f"light_rid_station-{target_arch}",
    ]
    normalized: list[dict] = []
    for item in assets:
        if not isinstance(item, dict):
            continue
        name = str(item.get("name") or "").strip()
        url = str(item.get("browser_download_url") or item.get("url") or "").strip()
        if not name or not url:
            continue
        normalized.append({
            "name": name,
            "url": url,
            "size": int(item.get("size") or 0),
            "content_type": str(item.get("content_type") or "").strip(),
        })
    for candidate in expected:
        for item in normalized:
            if item["name"] == candidate:
                return item
    for candidate in expected:
        for item in normalized:
            if item["name"].endswith(candidate):
                return item
    return {}

def _app_update_download_asset(asset: dict, latest_tag: str) -> tuple[str, str]:
    name = str((asset or {}).get("name") or "").strip()
    url = str((asset or {}).get("url") or "").strip()
    if not name or not url:
        raise RuntimeError("未找到可下载的 Release 资产。")
    stage_root = _app_update_ensure_dir(_app_update_stage_root())
    stamp = time.strftime("%Y%m%d_%H%M%S")
    safe_tag = re.sub(r"[^0-9A-Za-z._-]+", "_", str(latest_tag or "latest"))[:40] or "latest"
    stage_dir = tempfile.mkdtemp(prefix=f"{safe_tag}_{stamp}_", dir=stage_root)
    download_path = os.path.join(stage_dir, name)
    req = urllib.request.Request(
        url,
        headers={"User-Agent": APP_HTTP_USER_AGENT + " (+asset download)"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp, open(download_path, "wb") as f:
        shutil.copyfileobj(resp, f, length=1024 * 1024)
    return stage_dir, download_path

def _app_update_helper_command(plan_path: str) -> list[str]:
    if getattr(sys, "frozen", False):
        return [os.path.abspath(sys.executable or _runtime_entrypoint_path()), "--update-helper-plan", plan_path]
    return [os.path.abspath(sys.executable or "python3"), os.path.abspath(_runtime_entrypoint_path()), "--update-helper-plan", plan_path]

def _app_update_spawn_helper(plan_path: str, sudo_password: str | None = None) -> tuple[bool, str]:
    helper_cmd = _app_update_helper_command(plan_path)
    unit_name = f"light-rid-update-{os.getpid()}-{int(time.time())}"
    systemd_run = _command_path("systemd-run")
    if not systemd_run:
        return False, "未检测到 systemd-run，无法创建独立更新进程。"
    args = [
        systemd_run,
        f"--unit={unit_name}",
        "--collect",
        "--property=Type=simple",
        "--same-dir",
        *helper_cmd,
    ]
    ok, out, _rc = _run_privileged(args, timeout=20, sudo_password=sudo_password)
    if not ok:
        return False, out or "启动更新进程失败"
    return True, unit_name

def _app_update_lock_state(payload: dict) -> dict:
    lock_path = _app_update_lock_path()
    current = _app_update_read_json(lock_path)
    merged = dict(current)
    merged.update(payload if isinstance(payload, dict) else {})
    merged["updated_at"] = time.time()
    _app_update_write_json(lock_path, merged)
    return merged

def _app_update_write_notice(payload: dict) -> None:
    notice = dict(payload if isinstance(payload, dict) else {})
    notice["id"] = str(notice.get("id") or f"update-{int(time.time())}")
    notice["ts"] = float(notice.get("ts") or time.time())
    _app_update_write_json(_app_update_notice_path(), notice)

def _app_update_status_payload(consume_notice: bool = False) -> dict:
    current_commit = _local_app_commit() or _fallback_private_commit()
    current_tag = _local_app_tag()
    with app_update_lock:
        cfg = dict(APP_UPDATE_CFG)
        state = dict(APP_UPDATE_STATE)
    support = _app_update_runtime_support()
    lock_state = _app_update_read_json(_app_update_lock_path())
    if lock_state:
        status = str(lock_state.get("status") or "")
        state["installing"] = status not in ("", "completed", "failed", "rolled_back")
        state["install_status"] = status
        state["asset_name"] = str(lock_state.get("asset_name") or state.get("asset_name") or "")
        state["asset_url"] = str(lock_state.get("asset_url") or state.get("asset_url") or "")
        state["latest_tag"] = str(lock_state.get("latest_tag") or state.get("latest_tag") or "")
        state["latest_commit"] = str(lock_state.get("latest_commit") or state.get("latest_commit") or "")
        state["last_error"] = str(lock_state.get("last_error") or state.get("last_error") or "")
        state["install_message"] = str(lock_state.get("message") or "")
        state["helper_pid"] = int(lock_state.get("helper_pid") or 0)
        state["backup_path"] = str(lock_state.get("backup_path") or "")
        state["rolled_back"] = bool(lock_state.get("rolled_back"))
    else:
        state["installing"] = False
        state["install_status"] = ""
        state["install_message"] = ""
        state["helper_pid"] = 0
        state["backup_path"] = ""
        state["rolled_back"] = False
    state["current_commit"] = current_commit
    state["current_tag"] = current_tag
    state["current_short"] = _short_commit(current_commit)
    state["latest_short"] = _short_commit(state.get("latest_commit") or "")
    state["release_url"] = str(cfg.get("release_url") or APP_UPDATE_RELEASE_URL_DEFAULT)
    state["install_supported"] = bool(support.get("supported"))
    state["support_reason"] = str(support.get("reason") or "")
    state["target_arch"] = str(support.get("target_arch") or state.get("target_arch") or "")
    state["checked"] = bool(state.get("last_check_ts"))
    notice = _app_update_pop_notice() if consume_notice else {}
    if notice:
        state["completion_notice"] = notice
    return state

def _check_app_update_once(manual: bool = False, auto_apply: bool = False) -> dict:
    if not manual and not bool(APP_UPDATE_CFG.get("enabled", True)):
        return {"ok": True, "skipped": True, "state": _app_update_status_payload()}
    with app_update_lock:
        if bool(APP_UPDATE_STATE.get("running")):
            busy = True
        else:
            busy = False
            APP_UPDATE_STATE["running"] = True
            APP_UPDATE_STATE["last_error"] = ""
            release_url = str(APP_UPDATE_CFG.get("release_url") or APP_UPDATE_RELEASE_URL_DEFAULT)
    if busy:
        return {"ok": False, "error": "程序更新检查正在运行", "state": _app_update_status_payload()}
    try:
        release = _fetch_latest_release(release_url)
        latest_tag = str(release.get("tag_name") or "")
        latest_commit = str(release.get("target_commitish") or "")
        current_tag = _local_app_tag()
        current_commit = _local_app_commit() or _fallback_private_commit()
        support = _app_update_runtime_support()
        asset = _pick_release_asset(release.get("assets") or [], str(support.get("target_arch") or ""))
        update_available = bool(latest_tag and current_tag and latest_tag != current_tag)
        with app_update_lock:
            APP_UPDATE_STATE.update({
                "running": False,
                "last_check_ts": time.time(),
                "latest_tag": latest_tag,
                "latest_commit": latest_commit,
                "current_tag": current_tag,
                "current_commit": current_commit,
                "target_arch": str(support.get("target_arch") or ""),
                "asset_name": str(asset.get("name") or ""),
                "asset_url": str(asset.get("url") or ""),
                "install_supported": bool(support.get("supported")),
                "support_reason": str(support.get("reason") or ""),
                "update_available": update_available,
                "last_error": "",
            })
        if update_available:
            _log(f"[INFO] 检测到程序更新: local_tag={current_tag} latest_tag={latest_tag}")
        elif latest_tag:
            _log(f"[INFO] 程序更新检查完成: current_tag={current_tag or '-'} latest_tag={latest_tag}")
        rsp = {"ok": True, "manual": bool(manual), "state": _app_update_status_payload()}
        if auto_apply and update_available and bool(support.get("supported")):
            return _start_app_update_install(manual=False, sudo_password=None)
        return rsp
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
                "current_tag": _local_app_tag(),
                "current_commit": _local_app_commit() or _fallback_private_commit(),
                "last_error": str(e),
            })
        _log(f"[WARN] 程序更新检查失败: {e}")
        return {"ok": False, "error": str(e), "state": _app_update_status_payload()}

def _start_app_update_install(*, manual: bool = False, sudo_password: str | None = None) -> dict:
    check_rsp = _check_app_update_once(manual=manual, auto_apply=False)
    if not check_rsp.get("ok"):
        return check_rsp
    state = dict(check_rsp.get("state") or {})
    if bool(state.get("installing")):
        return {"ok": False, "error": "更新进程已在运行。", "state": state}
    if not bool(state.get("install_supported")):
        return {"ok": False, "error": str(state.get("support_reason") or "当前运行模式不支持自动更新。"), "state": state}
    if not bool(state.get("update_available")):
        return {"ok": False, "error": "当前已是最新 Tag，或本地 Tag 无法比较。", "state": state}
    release_url = str(APP_UPDATE_CFG.get("release_url") or APP_UPDATE_RELEASE_URL_DEFAULT)
    release = _fetch_latest_release(release_url)
    asset = _pick_release_asset(release.get("assets") or [], str(state.get("target_arch") or ""))
    if not asset:
        return {"ok": False, "error": "最新 Release 中没有匹配当前架构的资产。", "state": _app_update_status_payload()}
    stage_dir, download_path = _app_update_download_asset(asset, str(release.get("tag_name") or ""))
    plan = {
        "version": 1,
        "requested_at": time.time(),
        "requested_by": "manual" if manual else "auto",
        "latest_tag": str(release.get("tag_name") or ""),
        "latest_commit": str(release.get("target_commitish") or ""),
        "current_tag": str(state.get("current_tag") or ""),
        "current_commit": str(state.get("current_commit") or ""),
        "target_arch": str(state.get("target_arch") or ""),
        "target_path": str(_app_update_runtime_support().get("target_path") or ""),
        "asset_name": str(asset.get("name") or ""),
        "asset_url": str(asset.get("url") or ""),
        "download_path": download_path,
        "stage_dir": stage_dir,
        "response_grace_sec": 2,
    }
    plan_path = os.path.join(stage_dir, "plan.json")
    _app_update_write_json(plan_path, plan)
    _app_update_lock_state({
        "status": "scheduled",
        "requested_at": plan["requested_at"],
        "latest_tag": plan["latest_tag"],
        "latest_commit": plan["latest_commit"],
        "target_arch": plan["target_arch"],
        "target_path": plan["target_path"],
        "asset_name": plan["asset_name"],
        "asset_url": plan["asset_url"],
        "stage_dir": stage_dir,
        "download_path": download_path,
        "message": "更新进程已创建，等待接管 systemd 服务。",
    })
    ok, helper_ref = _app_update_spawn_helper(plan_path, sudo_password=sudo_password)
    if not ok:
        _app_update_lock_state({"status": "failed", "last_error": helper_ref, "message": helper_ref})
        return {"ok": False, "error": helper_ref, "state": _app_update_status_payload()}
    with app_update_lock:
        APP_UPDATE_STATE["installing"] = True
        APP_UPDATE_STATE["install_status"] = "scheduled"
        APP_UPDATE_STATE["asset_name"] = str(asset.get("name") or "")
        APP_UPDATE_STATE["asset_url"] = str(asset.get("url") or "")
        APP_UPDATE_STATE["latest_tag"] = str(release.get("tag_name") or "")
        APP_UPDATE_STATE["latest_commit"] = str(release.get("target_commitish") or "")
    _op_log("app-update-start", f"tag={plan['latest_tag']} asset={plan['asset_name']} helper={helper_ref}", ok=True)
    return {
        "ok": True,
        "message": "更新进程已启动，服务将短暂重启。",
        "helper": helper_ref,
        "restart_expected": True,
        "state": _app_update_status_payload(),
    }

def start_app_update_check() -> None:
    Thread(target=lambda: _check_app_update_once(auto_apply=True), daemon=True).start()

def _app_update_mark_startup_ready() -> None:
    lock = _app_update_read_json(_app_update_lock_path())
    if not lock:
        return
    target_path = os.path.abspath(str(lock.get("target_path") or ""))
    current_path = os.path.abspath(sys.executable or _runtime_entrypoint_path())
    status = str(lock.get("status") or "")
    if target_path and current_path != target_path:
        return
    if status not in ("scheduled", "installing", "starting", "waiting_start"):
        return
    _app_update_lock_state({
        "status": "activated",
        "activated_at": time.time(),
        "current_pid": os.getpid(),
        "message": "新版本已启动，等待更新进程收尾。",
    })
    _log("[INFO] 检测到更新锁，已标记新版本启动成功")

def _app_update_health_url() -> str:
    return f"http://127.0.0.1:{int(HTTP_PORT)}/api/update-health"

def _app_update_probe_health(timeout: float = 3.0) -> tuple[bool, str]:
    try:
        req = urllib.request.Request(
            _app_update_health_url(),
            headers={
                "User-Agent": APP_HTTP_USER_AGENT + " (+update health)",
                UPDATE_PROBE_HEADER: UPDATE_PROBE_HEADER_VALUE,
            },
        )
        with urllib.request.urlopen(req, timeout=max(1.0, float(timeout or 0.0))) as resp:
            if int(getattr(resp, "status", 200) or 200) != 200:
                return False, f"http {getattr(resp, 'status', '?')}"
            payload = json.loads(resp.read(256 * 1024).decode("utf-8", errors="replace"))
        if not isinstance(payload, dict):
            return False, "invalid json payload"
        if not bool(payload.get("ok")):
            return False, str(payload.get("error") or "health payload not ok")
        return True, "ok"
    except urllib.error.HTTPError as e:
        return False, f"http {e.code}"
    except urllib.error.URLError as e:
        return False, str(getattr(e, "reason", None) or e)
    except socket.timeout:
        return False, "timeout"
    except Exception as e:
        return False, str(e)

def _app_update_restore_backup(target_path: str, backup_path: str) -> tuple[bool, str]:
    target_path = os.path.abspath(str(target_path or ""))
    backup_path = os.path.abspath(str(backup_path or ""))
    if not target_path or not backup_path:
        return False, "backup path missing"
    if not os.path.isfile(backup_path):
        return False, f"backup not found: {backup_path}"
    rollback_tmp = target_path + ".rollback"
    try:
        shutil.copy2(backup_path, rollback_tmp)
        try:
            os.chmod(rollback_tmp, 0o755)
        except Exception:
            pass
        os.replace(rollback_tmp, target_path)
        try:
            os.chmod(target_path, 0o755)
        except Exception:
            pass
        return True, backup_path
    except Exception as e:
        return False, str(e)
    finally:
        try:
            if os.path.exists(rollback_tmp):
                os.remove(rollback_tmp)
        except Exception:
            pass

def _app_update_wait_health(deadline: float, require_activation: bool = False) -> tuple[bool, str]:
    activated_seen = not require_activation
    last_error = "waiting for service health"
    while time.time() < deadline:
        time.sleep(1.0)
        lock = _app_update_read_json(_app_update_lock_path())
        status = str(lock.get("status") or "")
        if status == "failed":
            return False, str(lock.get("last_error") or "update helper marked failed")
        if status == "activated":
            activated_seen = True
        ok_health, health_msg = _app_update_probe_health(timeout=2.5)
        if activated_seen and ok_health:
            return True, "ok"
        last_error = health_msg if not ok_health else "waiting for startup activation"
    return False, last_error

def _app_update_rollback_after_failure(plan: dict, backup_path: str, failure_text: str) -> tuple[bool, str]:
    target_path = os.path.abspath(str(plan.get("target_path") or ""))
    latest_tag = str(plan.get("latest_tag") or "")
    asset_name = str(plan.get("asset_name") or "")
    _app_update_lock_state({
        "status": "rollback",
        "rolled_back": False,
        "backup_path": backup_path,
        "last_error": failure_text,
        "message": "new version health check failed, restoring backup",
    })
    _systemctl(["stop", SYSTEMD_SERVICE_NAME], timeout=30)
    ok_restore, restore_msg = _app_update_restore_backup(target_path, backup_path)
    if not ok_restore:
        return False, f"rollback restore failed: {restore_msg}"
    _app_update_lock_state({
        "status": "rollback",
        "rolled_back": False,
        "backup_path": backup_path,
        "last_error": failure_text,
        "message": "backup restored, restarting previous service",
    })
    ok_start, out_start, rc_start = _systemctl(["start", SYSTEMD_SERVICE_NAME], timeout=40)
    if not ok_start:
        return False, f"rollback start failed: rc={rc_start} {out_start}"
    ok_health, health_msg = _app_update_wait_health(time.time() + 90.0, require_activation=False)
    if not ok_health:
        return False, f"rollback health check failed: {health_msg}"
    _app_update_lock_state({
        "status": "rolled_back",
        "rolled_back": True,
        "backup_path": backup_path,
        "last_error": failure_text,
        "message": "update failed and the previous version has been restored",
        "rollback_at": time.time(),
    })
    _app_update_write_notice({
        "kind": "warn",
        "title": "更新已回退",
        "text": f"更新到 {latest_tag or asset_name or '新版本'} 失败，已自动恢复旧版本。",
        "tag": latest_tag,
        "asset_name": asset_name,
        "backup_path": backup_path,
        "error": failure_text,
        "rolled_back": True,
    })
    return True, "rolled back"

def _run_app_update_helper_legacy(plan_path: str) -> int:
    plan = _app_update_read_json(str(plan_path or ""))
    if not plan:
        print("update helper plan missing", file=sys.stderr)
        return 2
    lock_path = _app_update_lock_path()
    stage_dir = str(plan.get("stage_dir") or "")
    download_path = os.path.abspath(str(plan.get("download_path") or ""))
    target_path = os.path.abspath(str(plan.get("target_path") or ""))
    asset_name = str(plan.get("asset_name") or "")
    latest_tag = str(plan.get("latest_tag") or "")
    response_grace = max(1, int(plan.get("response_grace_sec") or 2))
    backup_path = ""
    try:
        _app_update_lock_state({
            "status": "installing",
            "helper_pid": os.getpid(),
            "asset_name": asset_name,
            "asset_url": str(plan.get("asset_url") or ""),
            "latest_tag": latest_tag,
            "latest_commit": str(plan.get("latest_commit") or ""),
            "target_arch": str(plan.get("target_arch") or ""),
            "target_path": target_path,
            "message": "更新进程已接管，准备停止服务。",
        })
        time.sleep(response_grace)
        ok_stop, out_stop, rc_stop = _systemctl(["stop", SYSTEMD_SERVICE_NAME], timeout=40)
        if not ok_stop:
            raise RuntimeError(f"停止 systemd 服务失败: rc={rc_stop} {out_stop}")
        _app_update_lock_state({"status": "installing", "message": "服务已停止，正在备份旧文件。"})
        if not os.path.isfile(download_path):
            raise RuntimeError("下载好的更新文件不存在。")
        if not os.path.isfile(target_path):
            raise RuntimeError("当前安装目标不存在，无法备份。")
        backup_dir = os.path.join(os.path.dirname(target_path), "backups")
        os.makedirs(backup_dir, exist_ok=True)
        backup_path = os.path.join(
            backup_dir,
            os.path.basename(target_path) + ".bak_" + time.strftime("%Y%m%d_%H%M%S"),
        )
        shutil.copy2(target_path, backup_path)
        staged_target = target_path + ".new"
        shutil.copy2(download_path, staged_target)
        os.chmod(staged_target, 0o755)
        os.replace(staged_target, target_path)
        try:
            os.chmod(target_path, 0o755)
        except Exception:
            pass
        _app_update_lock_state({
            "status": "starting",
            "backup_path": backup_path,
            "message": "新文件已替换，正在启动 systemd 服务。",
        })
        ok_start, out_start, rc_start = _systemctl(["start", SYSTEMD_SERVICE_NAME], timeout=40)
        if not ok_start:
            raise RuntimeError(f"启动 systemd 服务失败: rc={rc_start} {out_start}")
        deadline = time.time() + 120.0
        while time.time() < deadline:
            time.sleep(1.0)
            lock = _app_update_read_json(lock_path)
            status = str(lock.get("status") or "")
            if status == "activated":
                _app_update_write_json(_app_update_current_path(), {
                    "installed_tag": latest_tag,
                    "installed_commit": str(plan.get("latest_commit") or ""),
                    "asset_name": asset_name,
                    "target_arch": str(plan.get("target_arch") or ""),
                    "target_path": target_path,
                    "installed_at": time.time(),
                    "backup_path": backup_path,
                })
                _app_update_write_notice({
                    "kind": "ok",
                    "title": "更新完成",
                    "text": f"已升级到 {latest_tag or asset_name or '新版本'}。",
                    "tag": latest_tag,
                    "asset_name": asset_name,
                    "backup_path": backup_path,
                })
                _app_update_remove_file(lock_path)
                try:
                    if stage_dir and os.path.isdir(stage_dir):
                        shutil.rmtree(stage_dir, ignore_errors=True)
                except Exception:
                    pass
                return 0
            if status == "failed":
                raise RuntimeError(str(lock.get("last_error") or "更新流程失败"))
        raise RuntimeError("新版本启动确认超时，更新进程未收到启动握手。")
    except Exception as e:
        _app_update_lock_state({
            "status": "failed",
            "backup_path": backup_path,
            "last_error": str(e),
            "message": str(e),
        })
        print(str(e), file=sys.stderr)
        return 1

def _run_app_update_helper(plan_path: str) -> int:
    plan = _app_update_read_json(str(plan_path or ""))
    if not plan:
        print("update helper plan missing", file=sys.stderr)
        return 2
    lock_path = _app_update_lock_path()
    stage_dir = str(plan.get("stage_dir") or "")
    download_path = os.path.abspath(str(plan.get("download_path") or ""))
    target_path = os.path.abspath(str(plan.get("target_path") or ""))
    asset_name = str(plan.get("asset_name") or "")
    latest_tag = str(plan.get("latest_tag") or "")
    response_grace = max(1, int(plan.get("response_grace_sec") or 2))
    backup_path = ""
    try:
        _app_update_lock_state({
            "status": "installing",
            "helper_pid": os.getpid(),
            "asset_name": asset_name,
            "asset_url": str(plan.get("asset_url") or ""),
            "latest_tag": latest_tag,
            "latest_commit": str(plan.get("latest_commit") or ""),
            "target_arch": str(plan.get("target_arch") or ""),
            "target_path": target_path,
            "message": "update helper is taking over",
        })
        time.sleep(response_grace)
        ok_stop, out_stop, rc_stop = _systemctl(["stop", SYSTEMD_SERVICE_NAME], timeout=40)
        if not ok_stop:
            raise RuntimeError(f"failed to stop systemd service: rc={rc_stop} {out_stop}")
        _app_update_lock_state({"status": "installing", "message": "service stopped, backing up old binary"})
        if not os.path.isfile(download_path):
            raise RuntimeError("downloaded release asset is missing")
        if not os.path.isfile(target_path):
            raise RuntimeError("installed target is missing, cannot create backup")
        backup_dir = os.path.join(os.path.dirname(target_path), "backups")
        os.makedirs(backup_dir, exist_ok=True)
        backup_path = os.path.join(
            backup_dir,
            os.path.basename(target_path) + ".bak_" + time.strftime("%Y%m%d_%H%M%S"),
        )
        shutil.copy2(target_path, backup_path)
        staged_target = target_path + ".new"
        shutil.copy2(download_path, staged_target)
        os.chmod(staged_target, 0o755)
        os.replace(staged_target, target_path)
        try:
            os.chmod(target_path, 0o755)
        except Exception:
            pass
        _app_update_lock_state({
            "status": "starting",
            "backup_path": backup_path,
            "message": "new binary installed, restarting service",
        })
        ok_start, out_start, rc_start = _systemctl(["start", SYSTEMD_SERVICE_NAME], timeout=40)
        if not ok_start:
            raise RuntimeError(f"failed to start systemd service: rc={rc_start} {out_start}")
        ok_health, health_msg = _app_update_wait_health(time.time() + 120.0, require_activation=True)
        if not ok_health:
            raise RuntimeError(f"new version health check failed: {health_msg}")
        _app_update_write_json(_app_update_current_path(), {
            "installed_tag": latest_tag,
            "installed_commit": str(plan.get("latest_commit") or ""),
            "asset_name": asset_name,
            "target_arch": str(plan.get("target_arch") or ""),
            "target_path": target_path,
            "installed_at": time.time(),
            "backup_path": backup_path,
        })
        _app_update_write_notice({
            "kind": "ok",
            "title": "更新完成",
            "text": f"已升级到 {latest_tag or asset_name or '新版本'}。",
            "tag": latest_tag,
            "asset_name": asset_name,
            "backup_path": backup_path,
        })
        _app_update_remove_file(lock_path)
        try:
            if stage_dir and os.path.isdir(stage_dir):
                shutil.rmtree(stage_dir, ignore_errors=True)
        except Exception:
            pass
        return 0
    except Exception as e:
        err_text = str(e)
        rollback_ok = False
        rollback_msg = ""
        if backup_path:
            rollback_ok, rollback_msg = _app_update_rollback_after_failure(plan, backup_path, err_text)
        if rollback_ok:
            print(f"{err_text}; rolled back", file=sys.stderr)
            try:
                if stage_dir and os.path.isdir(stage_dir):
                    shutil.rmtree(stage_dir, ignore_errors=True)
            except Exception:
                pass
            return 0
        final_error = err_text if not rollback_msg else f"{err_text}; rollback failed: {rollback_msg}"
        _app_update_lock_state({
            "status": "failed",
            "rolled_back": False,
            "backup_path": backup_path,
            "last_error": final_error,
            "message": final_error,
        })
        _app_update_write_notice({
            "kind": "warn",
            "title": "更新失败",
            "text": final_error,
            "tag": latest_tag,
            "asset_name": asset_name,
            "backup_path": backup_path,
            "error": final_error,
        })
        print(final_error, file=sys.stderr)
        return 1

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
        {"method": "GET", "path": "/api/v1/metrics?window=12h|24h|7d", "desc": "Host metrics for token API clients"},
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

