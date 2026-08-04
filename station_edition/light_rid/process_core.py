import json

from station_edition.light_rid.analize_core import normalize_parse_mode, parse_raw_packet

def _snap(e: dict) -> dict:
    s = {k: e.get(k) for k in
         ("sn","src_mac","id_type","uas_id","model","lat","lon","alt","speed","vspeed","last_ch","move_dir")}
    if CHANGE_ON_RSSI: s["rssi"]  = e.get("rssi")
    if CHANGE_ON_PL:   s["pl_sig"] = e.get("pl_sig")
    return s

SCAN_DIFF_FIELDS = (
    "sn", "src_mac", "id_type", "uas_id", "model", "scan_type", "firmware_type",
    "capture_type", "ssid", "rid_format", "dji_rid_kind", "sub_format",
    "parse_level", "parse_note", "coordinate_system", "warnings",
    "last_ch", "ch_assumed", "rssi", "pl_sig",
    "lat", "lon", "alt", "speed", "vspeed",
    "pilot_lat", "pilot_lon", "pilot_alt",
    "home_lat", "home_lon", "aux_lat", "aux_lon",
    "pos_a_lat", "pos_a_lon", "pos_b_lat", "pos_b_lon",
    "operator_positions", "raw_coords", "raw_packets_count",
)
SCAN_DIFF_LABELS = {
    "scan_type": "scan",
    "firmware_type": "firmware",
    "capture_type": "capture",
    "rid_format": "format",
    "dji_rid_kind": "dji_kind",
    "sub_format": "sub_format",
    "parse_level": "parse_level",
    "parse_note": "parse_note",
    "coordinate_system": "coord_sys",
    "last_ch": "channel",
    "ch_assumed": "channel_assumed",
    "pilot_lat": "pilot_lat",
    "pilot_lon": "pilot_lon",
    "pilot_alt": "pilot_alt",
    "raw_packets_count": "raw_packets",
    "operator_positions": "operators",
    "raw_coords": "raw_coords",
}
SCAN_DIFF_NOISE_FIELDS = {"rssi", "pl_sig", "raw_packets_count"}
RID_TARGET_SN_RE = re.compile(r"^[A-Za-z0-9]{4,64}$")


def _rid_target_sn_valid(value) -> bool:
    try:
        text = str(value or "").strip()
    except Exception:
        return False
    return bool(text and RID_TARGET_SN_RE.fullmatch(text))


def _decoded_has_valid_coord(loc: dict | None, sys_loc: dict | None, meta: dict | None) -> bool:
    try:
        if isinstance(loc, dict) and _coord_pair_valid(loc.get("lat"), loc.get("lon")):
            return True
    except Exception:
        pass
    try:
        if isinstance(sys_loc, dict) and _coord_pair_valid(sys_loc.get("pilot_lat"), sys_loc.get("pilot_lon")):
            return True
    except Exception:
        pass
    for key in ("operator_positions", "raw_coords"):
        for item in list((meta or {}).get(key) or []):
            if not isinstance(item, dict):
                continue
            try:
                if _coord_pair_valid(item.get("lat"), item.get("lon")):
                    return True
            except Exception:
                continue
    return False


def _rid_realtime_candidate_valid(has_valid_coord: bool) -> bool:
    return bool(has_valid_coord)

def _scan_diff_round(value):
    try:
        if value is None:
            return None
        return round(float(value), 7)
    except Exception:
        return value

def _scan_diff_position_digest(items) -> tuple[str, ...]:
    out: list[str] = []
    for item in list(items or [])[:4]:
        if not isinstance(item, dict):
            continue
        role = str(item.get("role") or item.get("source") or "?").strip() or "?"
        lat = _fmt(_scan_diff_round(item.get("lat")), ".6f")
        lon = _fmt(_scan_diff_round(item.get("lon")), ".6f")
        alt = _fmt(item.get("alt"), ".1f", "m")
        out.append(f"{role}@{lat},{lon},{alt}")
    return tuple(out)

def _scan_diff_state_snapshot(entry: dict | None) -> dict:
    if not isinstance(entry, dict):
        return {}
    snap = {
        "warnings": tuple(str(x) for x in (entry.get("warnings") or []) if str(x)),
        "operator_positions": _scan_diff_position_digest(entry.get("operator_positions")),
        "raw_coords": _scan_diff_position_digest(entry.get("raw_coords")),
        "raw_packets_count": len(list(entry.get("raw_packets") or [])),
    }
    for key in SCAN_DIFF_FIELDS:
        if key in snap:
            continue
        value = entry.get(key)
        if key in (
            "lat", "lon", "alt", "speed", "vspeed",
            "pilot_lat", "pilot_lon", "pilot_alt",
            "home_lat", "home_lon", "aux_lat", "aux_lon",
            "pos_a_lat", "pos_a_lon", "pos_b_lat", "pos_b_lon",
        ):
            value = _scan_diff_round(value)
        elif key == "parse_note":
            value = str(value or "").strip()[:240]
        elif key in ("scan_type", "firmware_type", "capture_type", "ssid", "rid_format", "dji_rid_kind", "sub_format", "parse_level", "coordinate_system", "sn", "src_mac", "id_type", "uas_id", "model"):
            value = str(value or "").strip()
        snap[key] = value
    return snap

def _scan_diff_format_value(value) -> str:
    if value in (None, "", (), [], {}):
        return "-"
    if isinstance(value, bool):
        return "yes" if value else "no"
    if isinstance(value, float):
        return f"{value:.6f}".rstrip("0").rstrip(".")
    if isinstance(value, tuple):
        return "; ".join(_scan_diff_format_value(x) for x in value) or "-"
    return str(value)

def _scan_diff_change_lines(before: dict, after: dict, limit: int = 18) -> list[str]:
    keys = [key for key in SCAN_DIFF_FIELDS if before.get(key) != after.get(key)]
    lines: list[str] = []
    for key in keys[:limit]:
        label = SCAN_DIFF_LABELS.get(key, key)
        lines.append(f"  ~ {label}: {_scan_diff_format_value(before.get(key))} -> {_scan_diff_format_value(after.get(key))}")
    extra = len(keys) - limit
    if extra > 0:
        lines.append(f"  ... {extra} more fields changed")
    return lines


def _scan_diff_changed_keys(before: dict, after: dict) -> list[str]:
    return [key for key in SCAN_DIFF_FIELDS if before.get(key) != after.get(key)]

def _scan_diff_header(after: dict) -> str:
    return (
        f"[SCAN_DIFF] sn={after.get('sn') or '-'} uas={after.get('uas_id') or '-'} "
        f"model={after.get('model') or '-'} scan={after.get('scan_type') or '-'} fw={after.get('firmware_type') or '-'}"
    )

def _scan_diff_summary_lines(after: dict) -> list[str]:
    lines = [
        "  parser: "
        f"format={after.get('rid_format') or after.get('dji_rid_kind') or '-'} "
        f"sub={after.get('sub_format') or '-'} "
        f"level={after.get('parse_level') or '-'} "
        f"coord={after.get('coordinate_system') or '-'}",
        "  radio: "
        f"capture={after.get('capture_type') or '-'} "
        f"ch={_scan_diff_format_value(after.get('last_ch'))}{'~' if after.get('ch_assumed') else ''} "
        f"rssi={_scan_diff_format_value(after.get('rssi'))} "
        f"pl={_scan_diff_format_value(after.get('pl_sig'))} "
        f"raw_packets={_scan_diff_format_value(after.get('raw_packets_count'))}",
        "  aircraft: "
        f"lat={_scan_diff_format_value(after.get('lat'))} "
        f"lon={_scan_diff_format_value(after.get('lon'))} "
        f"alt={_scan_diff_format_value(after.get('alt'))} "
        f"spd={_scan_diff_format_value(after.get('speed'))} "
        f"vspd={_scan_diff_format_value(after.get('vspeed'))}",
        "  operator: "
        f"pilot={_scan_diff_format_value(after.get('pilot_lat'))},{_scan_diff_format_value(after.get('pilot_lon'))},{_scan_diff_format_value(after.get('pilot_alt'))} "
        f"roles={_scan_diff_format_value(after.get('operator_positions'))}",
    ]
    note = str(after.get("parse_note") or "").strip()
    if note:
        lines.append(f"  note: {note}")
    warnings = after.get("warnings") or ()
    if warnings:
        lines.append(f"  warnings: {_scan_diff_format_value(warnings)}")
    return lines

def _build_scan_diff_entry(before: dict, after: dict, *, reason: str) -> str:
    title = _scan_diff_header(after)
    lines = [f"{title} reason={reason}"]
    lines.extend(_scan_diff_summary_lines(after))
    change_lines = _scan_diff_change_lines(before, after)
    if change_lines:
        lines.append("  changes:")
        lines.extend(change_lines)
    else:
        lines.append("  changes: (none)")
    return "\n".join(lines)

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
    "operator_positions", "raw_coords", "aircraft_position", "track_samples", "marker_offset",
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


def _track_samples_from_decoded(
    decoded: dict | None,
    receive_time_ms: int | None = None,
    packet_hash: str | None = None,
) -> list[dict]:
    if not isinstance(decoded, dict):
        return []
    meta = decoded.get("metadata") if isinstance(decoded.get("metadata"), dict) else {}
    samples = _sanitize_track_samples(meta.get("track_samples") or [])
    if samples:
        out: list[dict] = []
        for sample in samples:
            item = dict(sample)
            if receive_time_ms is not None:
                item["receive_time_ms"] = int(receive_time_ms)
            if packet_hash:
                item["packet_hash"] = str(packet_hash)
            out.append(item)
        return out
    sn = ""
    basic = decoded.get("basic_id") if isinstance(decoded.get("basic_id"), dict) else {}
    if basic:
        sn = str(basic.get("uas_id") or "").strip()
    uas_id_value = _uas_id_clean(decoded.get("uas_id"))
    out: list[dict] = []
    aircraft = _aircraft_position_from_decoded(decoded.get("location"), meta)
    if aircraft:
        out.extend(_sanitize_track_samples([{
            "sample_type": "aircraft",
            "track_type": "aircraft",
            "sn": sn or None,
            "uas_id": uas_id_value,
            "lat": aircraft.get("lat"),
            "lon": aircraft.get("lon"),
            "alt": aircraft.get("alt"),
            "timestamp_ms": aircraft.get("timestamp_ms"),
            "receive_time_ms": receive_time_ms,
            "packet_hash": packet_hash,
            "source": aircraft.get("source"),
            "coordinate_system": aircraft.get("coordinate_system"),
        }]))
    for operator in _operator_positions_from_decoded(decoded.get("system"), meta):
        out.extend(_sanitize_track_samples([{
            "sample_type": "operator",
            "track_type": "operator",
            "sn": sn or None,
            "uas_id": uas_id_value,
            "lat": operator.get("lat"),
            "lon": operator.get("lon"),
            "alt": operator.get("alt"),
            "timestamp_ms": operator.get("timestamp_ms"),
            "receive_time_ms": receive_time_ms,
            "packet_hash": packet_hash,
            "source": operator.get("source"),
            "coordinate_system": operator.get("coordinate_system"),
        }]))
    return out

def _history_packet_parsed_snapshot(
    decoded: dict | None,
    firmware_type: str | None = None,
    used_mode: str | None = None,
) -> dict | None:
    if not isinstance(decoded, dict):
        return None
    snapshot = {
        "basic_id": decoded.get("basic_id"),
        "location": decoded.get("location"),
        "system": decoded.get("system"),
        "metadata": decoded.get("metadata"),
        "uas_id": decoded.get("uas_id"),
        "firmware_type": _firmware_type_key(firmware_type),
    }
    mode_text = str(used_mode or "").strip()
    if mode_text:
        snapshot["mode"] = mode_text
    try:
        return json.loads(json.dumps(snapshot, ensure_ascii=False, default=str))
    except Exception:
        return None

def _history_track_updated_wall_ts(raw_tracks) -> float | None:
    tracks = _sanitize_tracks(raw_tracks)
    last_aircraft = tracks.get("last_aircraft")
    if isinstance(last_aircraft, dict):
        try:
            recv_ms = last_aircraft.get("receive_time_ms")
            if recv_ms:
                return float(recv_ms) / 1000.0
            ts_ms = last_aircraft.get("timestamp_ms")
            if ts_ms:
                return float(ts_ms) / 1000.0
        except Exception:
            return None
    return None

def _history_copy_tracks(dst: dict, src: dict | None) -> None:
    tracks = _sanitize_tracks((src or {}).get("tracks") or (src or {}).get("track") or [])
    dst["tracks"] = tracks
    dst["track"] = _track_store_primary(tracks, "aircraft")
    track_ts = (src or {}).get("track_updated_wall_ts")
    if track_ts is None:
        track_ts = _history_track_updated_wall_ts(tracks)
    dst["track_updated_wall_ts"] = track_ts

def _history_merge_tracks(dst: dict, src: dict | None) -> None:
    merged = _sanitize_tracks(dst)
    incoming = _sanitize_tracks(src)
    for track_type in ("aircraft", "operator"):
        cur_seq = list(merged.get(track_type) or [])
        next_seq = list(incoming.get(track_type) or [])
        use_incoming = len(next_seq) > len(cur_seq)
        if not use_incoming and next_seq and len(next_seq) == len(cur_seq):
            cur_last = merged.get(f"last_{track_type}") or {}
            next_last = incoming.get(f"last_{track_type}") or {}
            cur_ts = max(int(cur_last.get("receive_time_ms") or 0), int(cur_last.get("timestamp_ms") or 0))
            next_ts = max(int(next_last.get("receive_time_ms") or 0), int(next_last.get("timestamp_ms") or 0))
            use_incoming = next_ts > cur_ts
        if use_incoming:
            _track_store_set_sequence(merged, track_type, next_seq)
    dst["tracks"] = merged
    dst["track"] = _track_store_primary(merged, "aircraft")
    dst_ts = dst.get("track_updated_wall_ts")
    src_ts = (src or {}).get("track_updated_wall_ts")
    computed_ts = _history_track_updated_wall_ts(merged)
    candidates = [x for x in (dst_ts, src_ts, computed_ts) if x not in (None, "")]
    dst["track_updated_wall_ts"] = max(candidates) if candidates else None

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
        merged = (dst_rp + src_rp)[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:]
        dst["raw_packets"] = merged
    _history_merge_tracks(dst, src)
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
            "raw_packets": list(e.get("raw_packets") or [])[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:],
            "scan_type": _scan_type_key(e.get("scan_type")),
            "tracks": _sanitize_tracks(e.get("tracks") or e.get("track") or []),
            "track": _track_store_primary(e.get("tracks") or e.get("track") or [], "aircraft"),
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
    h["raw_packets"] = list(e.get("raw_packets") or [])[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:]
    h["scan_type"] = _scan_type_key(e.get("scan_type"))
    _history_copy_tracks(h, e)
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
    h.setdefault("raw_packets", list(e.get("raw_packets") or [])[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:])
    h.setdefault("scan_type", _scan_type_key(e.get("scan_type")))
    h.setdefault("uas_id", _uas_id_clean(e.get("uas_id")))
    h.setdefault("firmware_type", _firmware_type_key(e.get("firmware_type")))
    h.setdefault("tracks", _sanitize_tracks(e.get("tracks") or e.get("track") or []))
    h.setdefault("track", _track_store_primary(h.get("tracks"), "aircraft"))
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

def _history_recent_raw_packet_candidates_locked(limit: int | None = None) -> list[dict]:
    try:
        per_aircraft_limit = int(limit)
    except Exception:
        per_aircraft_limit = _track_store_points_limit()
    per_aircraft_limit = max(1, min(per_aircraft_limit, _track_store_points_limit()))
    out: list[dict] = []
    seq = 0
    for sn, hist in history_table.items():
        if not isinstance(hist, dict):
            continue
        fallback_ts = hist.get("last_capture_wall_ts") or hist.get("last_seen_wall_ts") or 0.0
        raw_packets = _history_storage_fetch_raw_packets(sn, per_aircraft_limit, newest_first=True, path=HISTORY_STORE_PATH)
        if not raw_packets:
            raw_packets = list(hist.get("raw_packets") or [])[-per_aircraft_limit:]
            for item in raw_packets:
                if isinstance(item, dict) and "_wall_ts" not in item:
                    item["_wall_ts"] = fallback_ts
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


def _history_storage_fetch_recent_raw_packets_by_sn(sns: list[str], limit: int, path: str | None = None) -> dict[str, list[dict]]:
    clean_sns: list[str] = []
    seen: set[str] = set()
    for sn in sns or []:
        text = str(sn or "").strip()
        if not text or text in seen:
            continue
        seen.add(text)
        clean_sns.append(text)
    if not clean_sns:
        return {}
    try:
        per_sn_limit = max(1, int(limit or 1))
    except Exception:
        per_sn_limit = 1
    db_path = os.path.abspath(str(path or HISTORY_STORE_PATH or _history_store_default_path()))
    if not os.path.exists(db_path):
        return {}
    placeholders = ",".join("?" for _ in clean_sns)
    sql = (
        "WITH ranked AS ("
        "SELECT id, sn, capture_wall_ts, capture_time_text, capture_type, firmware_type, uas_id, payload, hex_text, decoded_json, parse_mode, parse_format, "
        "ROW_NUMBER() OVER (PARTITION BY sn ORDER BY capture_wall_ts DESC, id DESC) AS rn "
        "FROM raw_packets WHERE sn IN (" + placeholders + ")"
        ") "
        "SELECT id, sn, capture_wall_ts, capture_time_text, capture_type, firmware_type, uas_id, payload, hex_text, decoded_json, parse_mode, parse_format "
        "FROM ranked WHERE rn <= ? ORDER BY sn ASC, capture_wall_ts ASC, id ASC"
    )
    args = list(clean_sns) + [per_sn_limit]
    conn = None
    try:
        _log(f"[INFO] history raw packet bulk fetch open: sns={len(clean_sns)} limit={per_sn_limit}")
        conn = sqlite3.connect(db_path, timeout=5.0)
        conn.row_factory = sqlite3.Row
        _log("[INFO] history raw packet bulk fetch query")
        rows = conn.execute(sql, args).fetchall()
        _log(f"[INFO] history raw packet bulk fetch rows={len(rows)}")
    except Exception as exc:
        _log(f"[WARN] history raw packet bulk fetch failed: {exc}")
        return {}
    finally:
        try:
            if conn is not None:
                conn.close()
        except Exception:
            pass
    out: dict[str, list[dict]] = {}
    for row in rows:
        item = _history_storage_packet_row_to_dict(row)
        sn = str((row["sn"] if isinstance(row, sqlite3.Row) else row[1]) or "")
        out.setdefault(sn, []).append(item)
    return out


def _history_recent_raw_packet_candidates(limit: int | None = None) -> list[dict]:
    try:
        per_aircraft_limit = int(limit)
    except Exception:
        per_aircraft_limit = _track_store_points_limit()
    per_aircraft_limit = max(1, min(per_aircraft_limit, _track_store_points_limit()))
    started_at = time.perf_counter()
    _log(f"[INFO] history reparse candidate collect start: limit={per_aircraft_limit}")
    with state_lock:
        history_items = [
            (str(sn or ""), dict(hist))
            for sn, hist in history_table.items()
            if isinstance(hist, dict)
            and (_scan_type_key(hist.get("scan_type")) == "phone" or (len(str(sn or "")) == 20 and str(sn or "").isalnum()))
        ]
    _log(f"[INFO] history reparse candidate collect copied: aircraft={len(history_items)} elapsed={time.perf_counter() - started_at:.2f}s")
    raw_by_sn = _history_storage_fetch_recent_raw_packets_by_sn(
        [sn for sn, _hist in history_items],
        per_aircraft_limit,
        path=HISTORY_STORE_PATH,
    )
    _log(f"[INFO] history reparse candidate collect fetched: aircraft={len(raw_by_sn)} elapsed={time.perf_counter() - started_at:.2f}s")
    out: list[dict] = []
    for item_index, (sn, hist) in enumerate(history_items, 1):
        fallback_ts = hist.get("last_capture_wall_ts") or hist.get("last_seen_wall_ts") or 0.0
        raw_packets = list(raw_by_sn.get(sn) or [])
        if not raw_packets:
            raw_packets = list(hist.get("raw_packets") or [])[-per_aircraft_limit:]
            for item in raw_packets:
                if isinstance(item, dict) and "_wall_ts" not in item:
                    item["_wall_ts"] = fallback_ts
        for packet_index, raw in enumerate(raw_packets):
            if not isinstance(raw, dict):
                continue
            if not str(raw.get("hex") or "").strip():
                continue
            out.append({
                "wall_ts": _history_raw_packet_wall_ts(raw, fallback_ts),
                "seq": (item_index * max(1, per_aircraft_limit)) + packet_index,
                "sn": sn,
                "hist": dict(hist),
                "raw": dict(raw),
                "packet_index": packet_index,
                "packet_count": len(raw_packets),
            })
    out.sort(key=lambda x: (str(x.get("sn") or ""), float(x.get("wall_ts") or 0.0), int(x.get("seq") or 0)))
    _log(f"[INFO] history reparse candidate collect done: packets={len(out)} elapsed={time.perf_counter() - started_at:.2f}s")
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
    tracks = _sanitize_tracks(record.get("tracks") or record.get("track") or [])
    sample = {
        "sample_type": "aircraft",
        "track_type": "aircraft",
        "sn": str(record.get("sn") or "") or None,
        "uas_id": _uas_id_clean(record.get("uas_id")),
        "lat": round(lat_f, 7),
        "lon": round(lon_f, 7),
        "alt": record.get("alt"),
        "timestamp_ms": None,
        "receive_time_ms": int(float(wall_ts or time.time()) * 1000.0),
        "source": "history_reparse_aircraft",
        "coordinate_system": "WGS84",
    }
    if _track_store_append_sample(tracks, sample):
        record["tracks"] = tracks
        record["track"] = _track_store_primary(tracks, "aircraft")
        record["track_updated_wall_ts"] = float(wall_ts or time.time())

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
    packets = list(record.get("raw_packets") or hist.get("raw_packets") or [])[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:]
    if isinstance(raw, dict) and raw.get("hex"):
        replaced = False
        for idx in range(len(packets) - 1, -1, -1):
            if _history_raw_packet_matches(packets[idx], raw):
                packets[idx] = dict(raw)
                replaced = True
                break
        if not replaced:
            packets.append(dict(raw))
    record["raw_packets"] = packets[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:]

def _history_apply_reidentified_locked(
    target_sn: str,
    hist: dict,
    raw: dict,
    decoded: dict,
    firmware_type: str,
    body: bytes,
    *,
    used_mode: str | None = None,
    update_track: bool = True,
    update_raw_packet: bool = True,
    update_memory: bool = True,
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
    existing = history_table.get(sn) if (update_memory and sn != old_sn) else None
    record = dict(existing) if isinstance(existing, dict) else dict(hist)
    if update_memory and sn != old_sn and old_sn in history_table:
        old_record = history_table.pop(old_sn)
        if existing:
            _history_merge(record, old_record)
        try:
            _history_storage_reassign_sn(old_sn, sn, HISTORY_STORE_PATH)
        except Exception:
            pass
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
        raw["parsed"] = _history_packet_parsed_snapshot(decoded, record["firmware_type"], used_mode)
        raw["parse_mode"] = str(used_mode or raw.get("parse_mode") or "").strip()
        raw["parse_format"] = str(
            (meta.get("rid_format") if isinstance(meta, dict) else None)
            or (meta.get("dji_rid_kind") if isinstance(meta, dict) else None)
            or (meta.get("format") if isinstance(meta, dict) else None)
            or record.get("rid_format")
            or record.get("dji_rid_kind")
            or record.get("kind")
            or record["firmware_type"]
            or ""
        ).strip()
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
            ("alt_relative", "relative_alt"),
            ("alt_geoid", "alt_geodetic"),
            ("alt_baro", "alt_baro"),
        ):
            if src_key in loc:
                record[key] = loc.get(src_key)
        if record["firmware_type"] == "new":
            for key, src_key in (
                ("track_deg", "direction_deg"),
                ("ground_speed", "speed_ms"),
                ("vertical_speed", "vspeed_ms"),
                ("alt_relative", "relative_alt"),
                ("alt_geoid", "alt_geodetic"),
                ("alt_baro", "alt_baro"),
                ("horizontal_accuracy", "horizontal_accuracy"),
                ("vertical_accuracy", "vertical_accuracy"),
                ("speed_accuracy", "speed_accuracy"),
                ("horizontal_accuracy_text", "horizontal_accuracy_text"),
                ("vertical_accuracy_text", "vertical_accuracy_text"),
                ("speed_accuracy_text", "speed_accuracy_text"),
                ("timestamp_ms", "timestamp_ms"),
                ("timestamp_accuracy", "timestamp_accuracy"),
                ("timestamp_accuracy_text", "timestamp_accuracy_text"),
            ):
                if loc.get(src_key) is not None:
                    record[key] = loc.get(src_key)
    elif record["firmware_type"] == "new":
        for key in (
            "lat", "lon", "alt", "speed", "vspeed", "move_dir",
            "track_deg", "ground_speed", "vertical_speed",
            "alt_relative", "alt_geoid", "alt_baro",
            "horizontal_accuracy", "vertical_accuracy", "speed_accuracy",
            "horizontal_accuracy_text", "vertical_accuracy_text", "speed_accuracy_text",
            "timestamp_ms", "timestamp_accuracy", "timestamp_accuracy_text",
        ):
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
    if update_track:
        record["track_samples"] = []
        record["tracks"] = _empty_track_store()
        record["track"] = []
        record["track_updated_wall_ts"] = None
    if update_memory:
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
                "firmware_type", "last_capture_wall_ts", "raw_packets",
            ) + NEW_FW_DETAIL_KEYS:
                if key in record:
                    state_entry[key] = record.get(key)
    if update_raw_packet and isinstance(raw, dict):
        try:
            _history_storage_update_raw_packet(sn, raw, HISTORY_STORE_PATH)
        except Exception as exc:
            _log(f"[WARN] raw packet database update failed for {sn}: {exc}")
    if update_memory:
        _history_mark_dirty()
    return record


def _history_reidentify_finalize_tracks(
    existing_raw,
    rebuilt_raw,
) -> tuple[dict, dict, dict, bool, list[str]]:
    existing_tracks = _sanitize_tracks(existing_raw)
    rebuilt_tracks = _sanitize_tracks(rebuilt_raw)
    existing_counts = _track_store_counts(existing_tracks)
    rebuilt_counts = _track_store_counts(rebuilt_tracks)
    final_tracks = _sanitize_tracks(existing_tracks)
    preserved_types: list[str] = []
    for track_type in ("aircraft", "operator"):
        existing_len = int(existing_counts.get(track_type) or 0)
        rebuilt_len = int(rebuilt_counts.get(track_type) or 0)
        if rebuilt_len >= existing_len:
            _track_store_set_sequence(final_tracks, track_type, list(rebuilt_tracks.get(track_type) or []))
        elif existing_len > rebuilt_len:
            preserved_types.append(track_type)
            rebuilt_last = rebuilt_tracks.get(f"last_{track_type}")
            if isinstance(rebuilt_last, dict):
                final_tracks[f"last_{track_type}"] = dict(rebuilt_last)
    return (
        final_tracks,
        existing_counts,
        rebuilt_counts,
        bool(preserved_types),
        preserved_types,
    )


HISTORY_REPARSE_PACKET_LIMIT_DEFAULT = 4000


def _history_reparse_effective_limit(limit: int | None = None) -> int:
    try:
        store_limit = _track_store_points_limit()
    except Exception:
        store_limit = HISTORY_REPARSE_PACKET_LIMIT_DEFAULT
    try:
        requested = int(limit) if limit not in (None, "") else HISTORY_REPARSE_PACKET_LIMIT_DEFAULT
    except Exception:
        requested = HISTORY_REPARSE_PACKET_LIMIT_DEFAULT
    return max(1, min(requested, store_limit, HISTORY_REPARSE_PACKET_LIMIT_DEFAULT))


def reidentify_recent_history_packets(limit: int | None = None) -> dict:
    effective_limit = _history_reparse_effective_limit(limit)
    candidates = _history_recent_raw_packet_candidates(effective_limit)
    if not candidates:
        return {"ok": False, "error": "no history raw packet"}
    return _reidentify_recent_history_packets_sync(candidates, effective_limit)

def _reidentify_recent_history_packets_sync(
    candidates: list[dict],
    effective_limit: int,
    *,
    progress_cb=None,
) -> dict:
    decoded_count = 0
    skipped_count = 0
    failed_count = 0
    migrated_count = 0
    updated_sns: set[str] = set()
    formats: dict[str, int] = {}
    errors: list[dict] = []
    aircraft_seen = {str(item.get("sn") or "") for item in candidates if str(item.get("sn") or "")}
    for index, item in enumerate(candidates, 1):
        started_at = time.perf_counter()
        target_sn = str(item.get("sn") or "")
        hist = item.get("hist") if isinstance(item.get("hist"), dict) else {}
        raw = item.get("raw") if isinstance(item.get("raw"), dict) else {}
        data = _history_raw_hex_to_bytes(str(raw.get("hex") or ""))
        if not data:
            skipped_count += 1
            if len(errors) < 8:
                errors.append({"sn": target_sn, "error": "raw packet has no usable hex"})
            _packet_parse_diag_note_parse((time.perf_counter() - started_at) * 1000.0, queue_depth=max(0, len(candidates) - index))
            if progress_cb:
                progress_cb(index, decoded_count, skipped_count, failed_count, migrated_count, len(updated_sns), formats, errors)
            continue
        decoded, firmware_type, body, used_mode = _history_decode_raw_packet(data, hist, target_sn, "auto")
        if not decoded:
            failed_count += 1
            if len(errors) < 8:
                errors.append({"sn": target_sn, "error": "raw packet could not be decoded"})
            _packet_parse_diag_note_parse((time.perf_counter() - started_at) * 1000.0, queue_depth=max(0, len(candidates) - index))
            if progress_cb:
                progress_cb(index, decoded_count, skipped_count, failed_count, migrated_count, len(updated_sns), formats, errors)
            continue
        with state_lock:
            record = _history_apply_reidentified_locked(target_sn, hist, raw, decoded, firmware_type, body, used_mode=used_mode)
        _packet_parse_diag_note_parse((time.perf_counter() - started_at) * 1000.0, queue_depth=max(0, len(candidates) - index))
        decoded_count += 1
        sn_now = str(record.get("sn") or target_sn)
        updated_sns.add(sn_now)
        if sn_now and sn_now != target_sn:
            migrated_count += 1
        fmt = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or firmware_type or used_mode or "unknown")
        formats[fmt] = int(formats.get(fmt, 0)) + 1
        if progress_cb:
            progress_cb(index, decoded_count, skipped_count, failed_count, migrated_count, len(updated_sns), formats, errors)
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

def _history_reparse_queue_depth() -> int:
    try:
        return max(0, int(history_reparse_queue.qsize()))
    except Exception:
        return 0


def _history_reparse_clear_pending_queue() -> int:
    drained = 0
    while True:
        try:
            history_reparse_queue.get_nowait()
            drained += 1
        except queue.Empty:
            break
        except Exception:
            break
    return drained


def _history_reparse_dynamic_worker_count(total_aircraft: int, total_packets: int) -> int:
    if max(0, int(total_aircraft or 0), int(total_packets or 0)) <= 0:
        return 1
    return 12


def _history_reparse_group_candidates(candidates: list[dict]) -> list[dict]:
    groups: dict[str, dict] = {}
    for item in candidates:
        if not isinstance(item, dict):
            continue
        sn = str(item.get("sn") or "").strip()
        if not sn:
            continue
        group = groups.setdefault(sn, {
            "sn": sn,
            "hist": dict(item.get("hist") or {}) if isinstance(item.get("hist"), dict) else {},
            "items": [],
        })
        group["items"].append(item)
    out = list(groups.values())
    for group in out:
        group["items"].sort(key=lambda x: (float(x.get("wall_ts") or 0.0), int(x.get("packet_index") or 0), int(x.get("seq") or 0)))
    out.sort(key=lambda x: str(x.get("sn") or ""))
    return out


def _history_reparse_task_active(task_id: str) -> bool:
    with history_reparse_lock:
        return bool(history_reparse_state.get("running")) and str(history_reparse_state.get("task_id") or "") == str(task_id or "")


def _history_reparse_note_result(
    task_id: str,
    *,
    index: int,
    batch_size: int,
    updated_sn: str = "",
    fmt: str = "",
    error: str = "",
    decoded: bool = False,
    skipped: bool = False,
    failed: bool = False,
    migrated: bool = False,
) -> dict:
    now_wall = time.time()
    with history_reparse_runtime_lock:
        if decoded and updated_sn:
            history_reparse_runtime_updated_sns.add(str(updated_sn))
        updated_aircraft = len(history_reparse_runtime_updated_sns)
    with history_reparse_lock:
        if (not bool(history_reparse_state.get("running"))) or str(history_reparse_state.get("task_id") or "") != str(task_id or ""):
            return _history_reparse_workflow_snapshot()
        total = max(0, int(history_reparse_state.get("total") or 0))
        step = max(0, min(total, int(index or 0)))
        completed_now = min(total, int(history_reparse_state.get("completed") or 0) + 1)
        history_reparse_state["completed"] = completed_now
        if decoded:
            history_reparse_state["decoded"] = int(history_reparse_state.get("decoded") or 0) + 1
        if skipped:
            history_reparse_state["skipped"] = int(history_reparse_state.get("skipped") or 0) + 1
        if failed:
            history_reparse_state["failed"] = int(history_reparse_state.get("failed") or 0) + 1
        if migrated:
            history_reparse_state["migrated"] = int(history_reparse_state.get("migrated") or 0) + 1
        history_reparse_state["updated_aircraft"] = updated_aircraft
        if fmt:
            formats = dict(history_reparse_state.get("formats") or {})
            formats[str(fmt)] = int(formats.get(str(fmt)) or 0) + 1
            history_reparse_state["formats"] = formats
        if error:
            errors = list(history_reparse_state.get("errors") or [])
            if len(errors) < 8:
                errors.append({"index": step, "error": str(error), "sn": str(updated_sn or "")})
            history_reparse_state["errors"] = errors
            history_reparse_state["last_error"] = str(error)
        active_batch = int(math.ceil(float(completed_now or 1) / float(max(1, int(batch_size or 1))))) if completed_now > 0 else 0
        history_reparse_state["active_batch"] = active_batch
        history_reparse_state["active_batch_size"] = (
            min(max(1, int(batch_size or 1)), max(0, total - ((active_batch - 1) * max(1, int(batch_size or 1)))))
            if active_batch > 0 else 0
        )
        history_reparse_state["message"] = f"processing {history_reparse_state['completed']}/{total}"
        history_reparse_state["updated_wall"] = now_wall
    return _history_reparse_workflow_snapshot()


def _history_reparse_finish_if_ready(task_id: str) -> bool:
    with history_reparse_lock:
        if (not bool(history_reparse_state.get("running"))) or str(history_reparse_state.get("task_id") or "") != str(task_id or ""):
            return False
        total = max(0, int(history_reparse_state.get("total") or 0))
        completed = max(0, int(history_reparse_state.get("completed") or 0))
        producer_done = bool(history_reparse_state.get("producer_done"))
        batch_size = max(1, int(history_reparse_state.get("batch_size") or HISTORY_REPARSE_BATCH_SIZE))
        decoded = max(0, int(history_reparse_state.get("decoded") or 0))
        skipped = max(0, int(history_reparse_state.get("skipped") or 0))
        failed = max(0, int(history_reparse_state.get("failed") or 0))
        migrated = max(0, int(history_reparse_state.get("migrated") or 0))
    if (not producer_done) or completed < total:
        return False
    with history_reparse_runtime_lock:
        updated_aircraft = len(history_reparse_runtime_updated_sns)
    saved = save_history_store(force=True)
    _log(
        "[INFO] history recent packets reidentified: "
        f"aircraft={updated_aircraft} packets={decoded}/{total} "
        f"skipped={skipped} failed={failed} migrated={migrated}"
    )
    _history_reparse_workflow_finish(
        ok=True,
        message="history reparse completed",
        completed=completed,
        decoded=decoded,
        skipped=skipped,
        failed=failed,
        migrated=migrated,
        updated_aircraft=updated_aircraft,
        saved=bool(saved),
        producer_done=True,
        active_batch=int(math.ceil(float(total) / float(batch_size))) if total > 0 else 0,
    )
    return True


def _history_reparse_process_item(item: dict) -> None:
    task_id = str(item.get("task_id") or "")
    if not task_id or not _history_reparse_task_active(task_id):
        return
    index = max(0, int(item.get("index") or 0))
    batch_size = max(1, int(item.get("batch_size") or HISTORY_REPARSE_BATCH_SIZE))
    target_sn = str(item.get("sn") or "")
    hist = item.get("hist") if isinstance(item.get("hist"), dict) else {}
    raw = item.get("raw") if isinstance(item.get("raw"), dict) else {}
    started_at = time.perf_counter()
    updated_sn = target_sn
    fmt = ""
    err = ""
    decoded_ok = False
    skipped = False
    failed = False
    migrated = False
    try:
        data = _history_raw_hex_to_bytes(str(raw.get("hex") or ""))
        if not data:
            skipped = True
            err = "raw packet has no usable hex"
            return
        decoded, firmware_type, body, used_mode = _history_decode_raw_packet(data, hist, target_sn, "auto")
        if not decoded:
            failed = True
            err = "raw packet could not be decoded"
            return
        with state_lock:
            record = _history_apply_reidentified_locked(target_sn, hist, raw, decoded, firmware_type, body, used_mode=used_mode)
        decoded_ok = True
        updated_sn = str(record.get("sn") or target_sn)
        migrated = bool(updated_sn and updated_sn != target_sn)
        fmt = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or firmware_type or used_mode or "unknown")
    except Exception as exc:
        failed = True
        err = str(exc)
        _log(f"[WARN] history reparse item failed: {exc}")
    finally:
        _packet_parse_diag_note_parse((time.perf_counter() - started_at) * 1000.0, queue_depth=_history_reparse_queue_depth())
        _history_reparse_note_result(
            task_id,
            index=index,
            batch_size=batch_size,
            updated_sn=updated_sn if decoded_ok else target_sn,
            fmt=fmt,
            error=err,
            decoded=decoded_ok,
            skipped=skipped,
            failed=failed,
            migrated=migrated,
        )
        _history_reparse_finish_if_ready(task_id)


def _history_reparse_process_aircraft_group(group: dict, task_id: str, batch_size: int) -> list[dict]:
    if not task_id or not _history_reparse_task_active(task_id):
        return []
    target_sn = str(group.get("sn") or "")
    items = list(group.get("items") or [])
    hist_seed = dict(group.get("hist") or {}) if isinstance(group.get("hist"), dict) else {}
    with state_lock:
        current_hist = history_table.get(target_sn)
        hist_copy = dict(current_hist) if isinstance(current_hist, dict) else dict(hist_seed)
    before_tracks = _sanitize_tracks(hist_copy)
    rebuilt_tracks = _empty_track_store()
    sn_now = target_sn
    record: dict | None = None
    parse_result_updates: list[dict] = []
    for item in items:
        if not _history_reparse_task_active(task_id):
            return parse_result_updates
        index = max(0, int(item.get("index") or 0))
        raw = dict(item.get("raw") or {}) if isinstance(item.get("raw"), dict) else {}
        started_at = time.perf_counter()
        updated_sn = sn_now
        fmt = ""
        err = ""
        decoded_ok = False
        skipped = False
        failed = False
        migrated = False
        try:
            data = _history_raw_hex_to_bytes(str(raw.get("hex") or ""))
            if not data:
                skipped = True
                err = "raw packet has no usable hex"
                continue
            decoded, firmware_type, body, used_mode = _history_decode_raw_packet(data, hist_copy, sn_now, "auto")
            if not decoded:
                failed = True
                err = "raw packet could not be decoded"
                continue
            receive_time_ms = None
            try:
                fallback_wall = hist_copy.get("last_capture_wall_ts") or hist_copy.get("last_seen_wall_ts") or time.time()
                receive_time_ms = int(float(_history_raw_packet_wall_ts(raw, fallback_wall) or 0.0) * 1000.0)
            except Exception:
                receive_time_ms = None
            packet_hash = str(raw.get("hex") or f"history-{index}")[:128]
            for sample in _track_samples_from_decoded(decoded, receive_time_ms, packet_hash=packet_hash):
                _track_store_append_sample(rebuilt_tracks, sample)
            with state_lock:
                live_hist = history_table.get(sn_now) or history_table.get(target_sn) or hist_copy
                record = _history_apply_reidentified_locked(
                    sn_now,
                    live_hist,
                    raw,
                    decoded,
                    firmware_type,
                    body,
                    used_mode=used_mode,
                    update_track=False,
                    update_raw_packet=False,
                    update_memory=False,
                )
            decoded_ok = True
            updated_sn = str(record.get("sn") or sn_now)
            migrated = bool(updated_sn and updated_sn != sn_now)
            sn_now = updated_sn or sn_now
            hist_copy = dict(record)
            fmt = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or firmware_type or used_mode or "unknown")
            parse_result_updates.append({
                "sn": sn_now,
                "raw": dict(raw),
                "parsed": raw.get("parsed") if isinstance(raw, dict) else None,
                "parse_mode": raw.get("parse_mode") if isinstance(raw, dict) else used_mode,
                "parse_format": raw.get("parse_format") if isinstance(raw, dict) else fmt,
            })
        except Exception as exc:
            failed = True
            err = str(exc)
            _log(f"[WARN] history reparse item failed: {exc}")
        finally:
            _packet_parse_diag_note_parse((time.perf_counter() - started_at) * 1000.0, queue_depth=0)
            _history_reparse_note_result(
                task_id,
                index=index,
                batch_size=batch_size,
                updated_sn=updated_sn if decoded_ok else target_sn,
                fmt=fmt,
                error=err,
                decoded=decoded_ok,
                skipped=skipped,
                failed=failed,
                migrated=migrated,
            )
    return parse_result_updates


def _history_reparse_reload_from_db() -> bool:
    try:
        load_history_store(HISTORY_STORE_PATH)
        return bool(save_history_store(force=True))
    except Exception as exc:
        _log(f"[WARN] history reparse db reload failed: {exc}")
        return False


def _history_reparse_worker_loop() -> None:
    while True:
        item = history_reparse_queue.get()
        try:
            if isinstance(item, dict):
                _history_reparse_process_item(item)
        except Exception as exc:
            _log(f"[WARN] history reparse worker error: {exc}")
            task_id = str(item.get("task_id") or "") if isinstance(item, dict) else ""
            if task_id and _history_reparse_task_active(task_id):
                _history_reparse_workflow_finish(
                    ok=False,
                    message="history reparse failed",
                    error=str(exc),
                )


def start_history_reparse_worker() -> None:
    global history_reparse_worker_started
    if history_reparse_worker_started:
        return
    history_reparse_worker_started = True
    Thread(target=_history_reparse_worker_loop, daemon=True).start()


def _recent_history_reidentify_producer(candidates: list[dict], effective_limit: int, task_id: str) -> None:
    total = len(candidates)
    groups = _history_reparse_group_candidates(candidates)
    worker_count = _history_reparse_dynamic_worker_count(len(groups), total)
    batch_size = max(1, int(math.ceil(float(total or 1) / float(worker_count or 1))))
    try:
        _history_reparse_workflow_update(
            total=total,
            aircraft_total=len(groups),
            batches_total=int(math.ceil(float(total or 0) / float(batch_size or 1))) if total else 0,
            message=f"starting parallel reparse: {worker_count} threads",
            active_batch=0,
            active_batch_size=0,
            worker_total=worker_count,
            worker_busy=0,
            worker_idle=worker_count,
            enqueued=total,
            producer_done=True,
            batch_size=batch_size,
        )
        from concurrent.futures import ThreadPoolExecutor, as_completed
        parse_result_updates: list[dict] = []
        with ThreadPoolExecutor(max_workers=worker_count, thread_name_prefix="history-reparse") as pool:
            futures = [
                pool.submit(_history_reparse_process_aircraft_group, group, task_id, batch_size)
                for group in groups
            ]
            _history_reparse_workflow_update(
                active_batch_size=min(len(groups), worker_count),
                worker_total=worker_count,
                worker_busy=min(len(groups), worker_count),
                worker_idle=max(0, worker_count - min(len(groups), worker_count)),
                message=f"processing {total} packets across {len(groups)} aircraft with {worker_count} threads",
            )
            for future in as_completed(futures):
                if not _history_reparse_task_active(task_id):
                    return
                try:
                    result = future.result()
                    if isinstance(result, list):
                        parse_result_updates.extend([item for item in result if isinstance(item, dict)])
                except Exception as exc:
                    _log(f"[WARN] history reparse parallel task failed: {exc}")
        if parse_result_updates:
            _history_reparse_workflow_update(message=f"saving {len(parse_result_updates)} parsed packets to database")
            try:
                save_started = time.perf_counter()
                saved_packets = _history_storage_update_raw_packet_parse_results(parse_result_updates, HISTORY_STORE_PATH)
                _log(f"[INFO] history reparse parsed packet db update: rows={saved_packets}/{len(parse_result_updates)} elapsed={time.perf_counter() - save_started:.2f}s")
            except Exception as exc:
                _log(f"[WARN] raw packet parse-result database batch update failed: {exc}")
        saved = _history_reparse_reload_from_db()
        _history_reparse_workflow_update(
            saved=bool(saved),
            worker_busy=0,
            worker_idle=worker_count,
            message="history reparse parsed results saved; refreshing history from database",
        )
        _history_reparse_finish_if_ready(task_id)
    except Exception as exc:
        _log(f"[WARN] history reparse producer failed: {exc}")
        if _history_reparse_task_active(task_id):
            _history_reparse_workflow_finish(
                ok=False,
                message="history reparse failed",
                error=str(exc),
            )


def _recent_history_reidentify_prepare_and_run(effective_limit: int, task_id: str) -> None:
    try:
        _history_reparse_workflow_update(message="collecting history raw packets", producer_done=False)
        candidates = _history_recent_raw_packet_candidates(effective_limit)
        if not candidates:
            if _history_reparse_task_active(task_id):
                _history_reparse_workflow_finish(
                    ok=False,
                    message="history reparse failed",
                    error="no history raw packet",
                    producer_done=True,
                )
            return
        _recent_history_reidentify_producer(candidates, effective_limit, task_id)
    except Exception as exc:
        _log(f"[WARN] history reparse prepare failed: {exc}")
        if _history_reparse_task_active(task_id):
            _history_reparse_workflow_finish(
                ok=False,
                message="history reparse failed",
                error=str(exc),
                producer_done=True,
            )


def start_recent_history_reidentify_workflow(limit: int | None = None) -> dict:
    effective_limit = _history_reparse_effective_limit(limit)
    _history_reparse_clear_pending_queue()
    with history_reparse_runtime_lock:
        history_reparse_runtime_updated_sns.clear()
    with state_lock:
        aircraft_total = len([
            sn for sn, hist in history_table.items()
            if sn and isinstance(hist, dict)
            and (_scan_type_key(hist.get("scan_type")) == "phone" or (len(str(sn or "")) == 20 and str(sn or "").isalnum()))
        ])
    started, workflow = _history_reparse_workflow_start(
        kind="history_recent",
        title="最近历史重解析",
        limit=effective_limit,
        total=0,
        aircraft_total=aircraft_total,
        batch_size=HISTORY_REPARSE_BATCH_SIZE,
    )
    if not started:
        return {
            "ok": True,
            "started": False,
            "busy": True,
            "message": str(workflow.get("message") or "history reparse already running"),
            "workflow": workflow,
        }
    task_id = str(workflow.get("task_id") or "")
    Thread(target=lambda: _recent_history_reidentify_prepare_and_run(effective_limit, task_id), daemon=True).start()
    return {
        "ok": True,
        "started": True,
        "message": "history reparse started; collecting raw packets in background",
        "workflow": _history_reparse_workflow_snapshot(),
    }

def history_reparse_workflow_status() -> dict:
    return {
        "ok": True,
        "workflow": _history_reparse_workflow_snapshot(),
    }

def reidentify_latest_history_packet() -> dict:
    return reidentify_recent_history_packets(limit=_track_store_points_limit())

def reidentify_history_packet_for_sn(sn: str, mode: str | None = "auto") -> dict:
    target_sn = str(sn or "").strip()
    if not target_sn:
        return {"ok": False, "error": "sn required"}
    mode_key = _history_parse_mode_key(mode)
    with state_lock:
        hist = history_table.get(target_sn) or state_table.get(target_sn)
        if not isinstance(hist, dict):
            return {"ok": False, "error": "aircraft not found", "sn": target_sn, "mode": mode_key}
        hist_copy = dict(hist)
    before_tracks = _sanitize_tracks(hist_copy)
    raw_packets = _history_storage_fetch_raw_packets(target_sn, path=HISTORY_STORE_PATH)
    if not raw_packets:
        fallback_wall_ts = hist_copy.get("last_capture_wall_ts") or hist_copy.get("last_seen_wall_ts") or time.time()
        raw_packets = list(hist_copy.get("raw_packets") or [])
        for item in raw_packets:
            if isinstance(item, dict) and "_wall_ts" not in item:
                item["_wall_ts"] = fallback_wall_ts
    if not raw_packets:
        return {"ok": False, "error": "no raw packet for aircraft", "sn": target_sn, "mode": mode_key}

    workflow_task_id = ""
    workflow_started = False
    with history_reparse_runtime_lock:
        history_reparse_runtime_updated_sns.clear()
    workflow_started, workflow = _history_reparse_workflow_start(
        kind="history_single",
        title=f"历史重解析 {target_sn}",
        limit=len(raw_packets),
        total=len(raw_packets),
        aircraft_total=1,
        batch_size=max(1, len(raw_packets)),
    )
    if workflow_started:
        workflow_task_id = str(workflow.get("task_id") or "")
        _history_reparse_workflow_update(
            message=f"processing {target_sn}",
            producer_done=True,
            enqueued=len(raw_packets),
            active_batch=1,
            active_batch_size=len(raw_packets),
        )

    decoded_count = 0
    skipped_count = 0
    failed_count = 0
    errors: list[dict] = []
    formats: dict[str, int] = {}
    used_modes: dict[str, int] = {}
    warnings: list[str] = []
    sn_now = target_sn
    record: dict | None = None
    rebuilt_tracks = _empty_track_store()
    for index, raw in enumerate(raw_packets):
        decoded_ok = False
        skipped_ok = False
        failed_ok = False
        packet_fmt = ""
        packet_err = ""
        data = _history_raw_hex_to_bytes(str(raw.get("hex") or ""))
        if not data:
            skipped_count += 1
            skipped_ok = True
            packet_err = "raw packet has no usable hex"
            if len(errors) < 8:
                errors.append({"packet_index": index, "error": packet_err})
            if workflow_task_id:
                _history_reparse_note_result(
                    workflow_task_id,
                    index=index + 1,
                    batch_size=max(1, len(raw_packets)),
                    updated_sn=sn_now,
                    error=packet_err,
                    skipped=skipped_ok,
                )
            continue
        decoded, firmware_type, body, used_mode = _history_decode_raw_packet(data, hist_copy, sn_now, mode_key)
        if not decoded:
            failed_count += 1
            failed_ok = True
            packet_err = "raw packet could not be decoded with selected mode"
            if len(errors) < 8:
                errors.append({"packet_index": index, "error": packet_err})
            if workflow_task_id:
                _history_reparse_note_result(
                    workflow_task_id,
                    index=index + 1,
                    batch_size=max(1, len(raw_packets)),
                    updated_sn=sn_now,
                    error=packet_err,
                    failed=failed_ok,
                )
            continue
        receive_time_ms = None
        try:
            receive_time_ms = int(float(_history_raw_packet_wall_ts(raw, hist_copy.get("last_capture_wall_ts") or time.time()) or 0.0) * 1000.0)
        except Exception:
            receive_time_ms = None
        packet_hash = str(raw.get("hex") or f"history-{index}")[:128]
        for sample in _track_samples_from_decoded(decoded, receive_time_ms, packet_hash=packet_hash):
            _track_store_append_sample(rebuilt_tracks, sample)
        with state_lock:
            current_hist = history_table.get(sn_now) or history_table.get(target_sn) or hist_copy
            record = _history_apply_reidentified_locked(
                sn_now,
                current_hist,
                raw,
                decoded,
                firmware_type,
                body,
                used_mode=used_mode,
                update_track=False,
            )
        decoded_count += 1
        decoded_ok = True
        sn_now = str(record.get("sn") or sn_now)
        hist_copy = dict(record)
        fmt_item = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or firmware_type or used_mode or "unknown")
        packet_fmt = fmt_item
        formats[fmt_item] = int(formats.get(fmt_item, 0)) + 1
        used_key = str(used_mode or mode_key or "auto")
        used_modes[used_key] = int(used_modes.get(used_key, 0)) + 1
        if workflow_task_id:
            _history_reparse_note_result(
                workflow_task_id,
                index=index + 1,
                batch_size=max(1, len(raw_packets)),
                updated_sn=sn_now,
                fmt=packet_fmt,
                decoded=decoded_ok,
            )
    if not record:
        if workflow_task_id:
            _history_reparse_workflow_finish(
                ok=False,
                message="history reparse failed",
                error="no raw packet could be decoded with selected mode",
                completed=len(raw_packets),
                decoded=decoded_count,
                skipped=skipped_count,
                failed=failed_count,
                producer_done=True,
                active_batch=1,
            )
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
            "workflow": _history_reparse_workflow_snapshot(),
        }

    final_tracks, before_counts, rebuilt_counts, preserve_existing_longer_tracks, preserved_track_types = _history_reidentify_finalize_tracks(
        before_tracks,
        rebuilt_tracks,
    )
    final_counts = _track_store_counts(final_tracks)
    final_track = _track_store_primary(final_tracks, "aircraft")
    if len(raw_packets) <= 1:
        warnings.append(f"history for {sn_now} only has 1 raw packet; rebuilt track detail is limited")
    with state_lock:
        current = history_table.get(sn_now) or record
        current["tracks"] = final_tracks
        current["track"] = final_track
        last_aircraft = final_tracks.get("last_aircraft")
        current["track_updated_wall_ts"] = None
        if isinstance(last_aircraft, dict):
            try:
                current["track_updated_wall_ts"] = float((last_aircraft.get("receive_time_ms") or last_aircraft.get("timestamp_ms") or 0) / 1000.0)
            except Exception:
                current["track_updated_wall_ts"] = None
        history_table[sn_now] = current
        state_entry = state_table.get(sn_now)
        if isinstance(state_entry, dict):
            state_entry["tracks"] = _sanitize_tracks(final_tracks)
            state_entry["track"] = list(final_track)
            state_entry["track_updated_wall_ts"] = current.get("track_updated_wall_ts")
        record = dict(current)
        _history_mark_dirty()
    saved = save_history_store(force=True)
    fmt = str(record.get("rid_format") or record.get("dji_rid_kind") or record.get("kind") or record.get("firmware_type") or "unknown")
    used_summary = ",".join(f"{k}:{v}" for k, v in sorted(used_modes.items())) or mode_key
    _log(
        f"[INFO] history packets reidentified: sn={target_sn} -> {sn_now} "
        f"mode={mode_key} used={used_summary} decoded={decoded_count}/{len(raw_packets)} "
        f"format={fmt}"
    )
    if workflow_task_id:
        _history_reparse_workflow_finish(
            ok=True,
            message="history reparse completed",
            completed=len(raw_packets),
            decoded=decoded_count,
            skipped=skipped_count,
            failed=failed_count,
            migrated=1 if sn_now != target_sn else 0,
            updated_aircraft=1,
            saved=bool(saved),
            producer_done=True,
            active_batch=1,
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
        "track_count": len(final_track),
        "track": final_track,
        "tracks": final_tracks,
        "before_counts": before_counts,
        "rebuilt_counts": rebuilt_counts,
        "final_counts": final_counts,
        "preserve_existing_longer_tracks": preserve_existing_longer_tracks,
        "preserved_track_types": preserved_track_types,
        "errors": errors,
        "warnings": warnings,
        "firmware_type": record.get("firmware_type"),
        "format": fmt,
        "saved": bool(saved),
        "workflow": _history_reparse_workflow_snapshot(),
        "refresh": True,
        "message": f"reparsed {sn_now} with {mode_key}; metadata and trajectory refreshed",
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
    firmware_type_key = _firmware_type_key(firmware_type)
    uas_id_value = _uas_id_clean(decoded.get("uas_id"))
    if firmware_type_key == "old":
        uas_id_value = ""

    if firmware_type_key != "old" and basic and basic.get("uas_id"):
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
    elif firmware_type_key != "old" and src_mac in mac_to_basic:
        c  = mac_to_basic[src_mac].get("basic",{})
        sn = (c.get("uas_id","") or "").strip() or mac_key
        it = c.get("id_type","unknown")
    else:
        sn, it = mac_key, "unknown"

    scan_type_key = _scan_type_key(scan_type)
    parser_format = str(meta.get("format") or meta.get("rid_format") or "") if isinstance(meta, dict) else ""
    rid_coord_ok = _decoded_has_valid_coord(loc, sys_loc, meta if isinstance(meta, dict) else None)
    model = _resolve_model_name(sn, scan_type_key, None)
    now   = time.monotonic()
    now_wall = time.time()
    scan_diff_entry = ""
    raw_packet_to_store = None

    with state_lock:
        existing_entry = state_table.get(sn) or state_table.get(mac_key)
        if scan_type_key == "rid":
            if not _rid_target_sn_valid(sn):
                return
            if existing_entry is None and not _rid_realtime_candidate_valid(rid_coord_ok):
                return
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
            try:
                _history_storage_reassign_sn(mac_key, sn, HISTORY_STORE_PATH)
            except Exception:
                pass
        prev_scan_state = _scan_diff_state_snapshot(state_table.get(sn))

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
                "tracks":_empty_track_store(),
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
            raw_packet_to_store = {
                "ts": _fmt_wall_ts(now_wall),
                "capture_type": str(capture_type or ""),
                "firmware_type": firmware_type_key,
                "uas_id": uas_id_value,
                "_wall_ts": now_wall,
                "hex": str(raw_pkt_hex),
                "parsed": _history_packet_parsed_snapshot(decoded, firmware_type_key, "live"),
                "parse_mode": "live",
                "parse_format": parser_format or firmware_type_key,
            }
            rp.append(dict(raw_packet_to_store))
            if len(rp) > HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:
                rp = rp[-HISTORY_RAW_PACKET_SNAPSHOT_LIMIT:]
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
                if firmware_type_key == "new":
                    for key, src_key in (
                        ("track_deg", "direction_deg"),
                        ("ground_speed", "speed_ms"),
                        ("vertical_speed", "vspeed_ms"),
                        ("alt_relative", "relative_alt"),
                        ("alt_geoid", "alt_geodetic"),
                        ("alt_baro", "alt_baro"),
                        ("horizontal_accuracy", "horizontal_accuracy"),
                        ("vertical_accuracy", "vertical_accuracy"),
                        ("speed_accuracy", "speed_accuracy"),
                        ("horizontal_accuracy_text", "horizontal_accuracy_text"),
                        ("vertical_accuracy_text", "vertical_accuracy_text"),
                        ("speed_accuracy_text", "speed_accuracy_text"),
                        ("timestamp_ms", "timestamp_ms"),
                        ("timestamp_accuracy", "timestamp_accuracy"),
                        ("timestamp_accuracy_text", "timestamp_accuracy_text"),
                    ):
                        if loc.get(src_key) is not None:
                            e[key] = loc.get(src_key)

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
        track_samples = _track_samples_from_decoded(decoded, int(now_wall * 1000.0), packet_hash=str(pl_sig))
        e["track_samples"] = track_samples
        e["tracks"] = _sanitize_tracks(e.get("tracks") or e.get("track") or [])
        for sample in track_samples:
            _track_store_append_sample(e["tracks"], sample)
        e["track"] = _track_store_primary(e["tracks"], "aircraft")
        last_aircraft = e["tracks"].get("last_aircraft")
        if isinstance(last_aircraft, dict):
            e["track_updated_wall_ts"] = float((last_aircraft.get("receive_time_ms") or last_aircraft.get("timestamp_ms") or 0) / 1000.0)

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

        next_scan_state = _scan_diff_state_snapshot(e)
        if created or was_lost or prev_scan_state != next_scan_state:
            changed_keys = _scan_diff_changed_keys(prev_scan_state, next_scan_state)
            if created or was_lost or any(key not in SCAN_DIFF_NOISE_FIELDS for key in changed_keys):
                diff_reason = "first" if created else ("reonline" if was_lost else "changed")
                scan_diff_entry = _build_scan_diff_entry(prev_scan_state, next_scan_state, reason=diff_reason)

    if notify_payload is not None and notify_event_title:
        _notification_add(_notify_online_text(notify_payload, notify_event_title, now_wall), "ok", "rid")
        queue_online_notification(notify_payload, notify_event_title, now_wall=now_wall)
    if zone_notify_payload is not None and zone_notify_names:
        _notification_add(_notify_zone_alarm_text(zone_notify_payload, zone_notify_names, now_wall), "warn", "rid")
        queue_zone_alarm_notification(zone_notify_payload, zone_notify_names, now_wall=now_wall)
    if raw_packet_to_store is not None:
        try:
            _history_storage_append_raw_packet(sn, raw_packet_to_store, HISTORY_STORE_PATH)
        except Exception as exc:
            _log(f"[WARN] raw packet database append failed for {sn}: {exc}")
    if scan_diff_entry:
        _scan_diff(scan_diff_entry)

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

# Connected websocket clients
_ws_clients: list[dict] = []
_ws_lock = Lock()


def _ws_settings_runtime_payload() -> dict:
    aps, aps_seq, aps_total = _ap_snapshot()
    return {
        "ok": True,
        "kind": "settings_runtime",
        "aps": aps,
        "aps_seq": aps_seq,
        "aps_total": aps_total,
        "workflow": _history_reparse_workflow_snapshot(),
    }

_HOME_LIST_DRONE_FIELDS = (
    "sn",
    "sn_src",
    "uas_id",
    "scan_type",
    "firmware_type",
    "firmware_type_key",
    "model",
    "lost",
    "archived",
    "mac",
    "id_type",
    "ch",
    "ch_assumed",
    "lat",
    "lon",
    "alt",
    "spd",
    "vspd",
    "pilot_lat",
    "pilot_lon",
    "pilot_alt",
    "pilot_loc_type",
    "pilot_loc_type_text",
    "home_lat",
    "home_lon",
    "aux_lat",
    "aux_lon",
    "pos_a_lat",
    "pos_a_lon",
    "pos_b_lat",
    "pos_b_lon",
    "rssi",
    "pkts",
    "dir",
    "ssid",
    "capture_type",
    "capture_time",
    "last_pkt_time",
    "scan_type_key",
    "age",
    "age_text",
    "online_dur",
    "first_seen",
    "last_seen",
)

def _home_list_drone(row: dict) -> dict:
    if not isinstance(row, dict):
        return {}
    return {key: row.get(key) for key in _HOME_LIST_DRONE_FIELDS if key in row}

def _home_workflow_summary(state: dict | None) -> dict:
    if not isinstance(state, dict):
        return {}
    keys = (
        "task_id",
        "kind",
        "title",
        "status",
        "running",
        "limit",
        "total",
        "completed",
        "decoded",
        "skipped",
        "failed",
        "migrated",
        "saved",
        "aircraft_total",
        "updated_aircraft",
        "enqueued",
        "producer_done",
        "batch_size",
        "batches_total",
        "active_batch",
        "active_batch_size",
        "message",
        "last_error",
        "worker_total",
        "worker_busy",
        "worker_idle",
        "pending",
        "batches_pending",
        "queue_depth",
        "progress_pct",
        "elapsed_sec",
        "rate_per_sec",
        "decoded_rate_per_sec",
        "eta_sec",
    )
    out = {key: state.get(key) for key in keys if key in state}
    errors = state.get("errors")
    if isinstance(errors, list) and errors:
        out["errors_count"] = len(errors)
    return out

def _home_runtime_security_summary(state: dict | None) -> dict:
    if not isinstance(state, dict):
        return {}
    keys = (
        "ok",
        "current_uid",
        "current_user",
        "running_as_root",
        "has_network_capabilities",
        "risk",
        "level",
        "message",
        "dedicated_user",
        "dedicated_user_exists",
        "service_user",
        "service_uses_dedicated_user",
        "sudo_available",
        "can_elevate",
        "password_saved",
    )
    return {key: state.get(key) for key in keys if key in state}

def _home_meta_summary(meta: dict) -> dict:
    if not isinstance(meta, dict):
        return {}
    keys = (
        "dji_lookup_url",
        "allow_restart",
        "restart_args_current",
        "restart_args_saved",
        "base_name",
        "base_lat",
        "base_lon",
        "base_zoom",
        "heading_ref_deg",
        "map_auto_center_idle_sec",
        "map_tile_url",
        "map_tile_subdomains",
        "map_tile_attribution",
        "map_tile_max_native_zoom",
        "map_api_configured",
        "map_default_legal_notice",
        "config_path",
        "iface_selected",
        "scan_wifi_fast",
        "wifi_fast_supported",
        "wifi_fast_msg",
        "sniff_state",
        "sniff_msg",
        "sniff_iface",
        "sniff_idle_sec",
        "sniff_last_pkt",
        "sniff_last_err_at",
        "oobe",
        "alert_zone",
        "alert_zones",
        "settings_path",
    )
    out = {key: meta.get(key) for key in keys if key in meta}
    out["runtime_security"] = _home_runtime_security_summary(meta.get("runtime_security"))
    out["workflow"] = _home_workflow_summary(meta.get("workflow"))
    app_update = meta.get("app_update")
    if isinstance(app_update, dict) and app_update.get("completion_notice"):
        out["app_update"] = {"completion_notice": app_update.get("completion_notice")}
    return out

def _ws_push_loop() -> None:
    """Push latest state JSON to home/settings websocket clients."""
    import json as _json
    last_home_logs_seq = None
    last_home_aps_seq = None
    while True:
        time.sleep(1.0)
        home_frame = None
        settings_frame = None
        now = time.monotonic()
        dead: list[dict] = []
        with _ws_lock:
            clients = list(_ws_clients)
        for client in clients:
            sock = client.get("sock")
            if sock is None:
                dead.append(client)
                continue
            try:
                if str(client.get("mode") or "home") == "settings":
                    if now < float(client.get("next_send_at") or 0.0):
                        continue
                    if settings_frame is None:
                        settings_payload = _json.dumps(_ws_settings_runtime_payload(), ensure_ascii=False)
                        settings_frame = _ws_frame(settings_payload.encode())
                    sock.sendall(settings_frame)
                    client["next_send_at"] = now + 5.0
                else:
                    if home_frame is None:
                        home_snapshot = _state_snapshot(lightweight=True)
                        logs_seq = home_snapshot.get("logs_seq")
                        aps_seq = home_snapshot.get("aps_seq")
                        if last_home_logs_seq == logs_seq:
                            home_snapshot.pop("logs", None)
                        if last_home_aps_seq == aps_seq:
                            home_snapshot.pop("aps", None)
                        home_payload = _json.dumps(home_snapshot, ensure_ascii=False)
                        home_frame = _ws_frame(home_payload.encode())
                        last_home_logs_seq = logs_seq
                        last_home_aps_seq = aps_seq
                    sock.sendall(home_frame)
            except Exception:
                dead.append(client)
        if dead:
            with _ws_lock:
                for client in dead:
                    sock = client.get("sock")
                    try:
                        if sock is not None:
                            sock.close()
                    except Exception: pass
                    if client in _ws_clients:
                        _ws_clients.remove(client)

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

def _state_snapshot(lightweight: bool = False) -> dict:
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
            if lightweight:
                drone = {
                    "sn": sn,
                    "sn_src": sn_src,
                    "uas_id": _uas_id_clean(cur.get("uas_id") or hist.get("uas_id","")),
                    "scan_type": scan_type,
                    "firmware_type": firmware_type,
                    "firmware_type_key": firmware_type_key,
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
                    "rssi": cur.get("rssi", hist.get("rssi")),
                    "pkts": hist.get("pkt_count_total", cur.get("pkt_count",0)),
                    "dir": cur.get("move_dir", hist.get("move_dir")) or "-",
                    "ssid": cur.get("ssid", hist.get("ssid","")) or "",
                    "capture_type": cur.get("capture_type", hist.get("capture_type","")) or "",
                    "capture_time": _fmt_wall_ts(cap_wall_ts),
                    "last_pkt_time": _fmt_wall_ts(cap_wall_ts),
                    "scan_type_key": scan_type_key,
                    "age": round(age),
                    "age_text": _fmt_age_compact(age),
                    "online_dur": (None if online_dur is None else int(round(float(online_dur)))),
                    "first_seen": _fmt_wall_ts(hist.get("first_seen_wall_ts", cur.get("first_seen_wall_ts"))),
                    "last_seen": _fmt_wall_ts(hist.get("last_seen_wall_ts", cur.get("last_seen_wall_ts"))),
                }
                drones.append(_home_list_drone(drone))
                continue
            track_store = _sanitize_tracks(cur.get("tracks", hist.get("tracks", cur.get("track", hist.get("track", [])))) or [])
            aircraft_track_count = _track_display_count(track_store, "aircraft", firmware_type=firmware_type_key)
            operator_track_count = _track_display_count(track_store, "operator", firmware_type=firmware_type_key)
            drone = {
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
                "raw_packets_count": len(list(cur.get("raw_packets", hist.get("raw_packets", [])) or [])),
                "scan_type_key": scan_type_key,
                "age": round(age),
                "age_text": _fmt_age_compact(age),
                "online_dur": (None if online_dur is None else int(round(float(online_dur)))),
                "first_seen": _fmt_wall_ts(hist.get("first_seen_wall_ts", cur.get("first_seen_wall_ts"))),
                "last_seen": _fmt_wall_ts(hist.get("last_seen_wall_ts", cur.get("last_seen_wall_ts"))),
                "track_count": aircraft_track_count,
                "aircraft_track_count": aircraft_track_count,
                "operator_track_count": operator_track_count,
                "track_updated": _fmt_wall_ts(hist.get("track_updated_wall_ts", cur.get("track_updated_wall_ts"))),
            }
            drones.append(drone)
        drones.sort(key=lambda d: (d["lost"], d.get("archived", False), d["age"], d["sn"]))
        map_drones = [d for d in drones if not d.get("archived")]
    sniff_meta = _sniff_health_meta(now, now_wall)
    basic_cfg = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
    if not isinstance(basic_cfg, dict):
        basic_cfg = {}
    map_tile_url = str(WEB_CFG.get("map_tile_url") or "").strip()
    payload = {
        "ts": time.strftime("%H:%M:%S"),
        "server_wall_ms": int(now_wall * 1000.0),
        "ch": f"ch{current_channel}" if current_channel else "ch?",
        "drones": drones,
        "map_drones": map_drones,
        "lightweight": bool(lightweight),
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
            "map_tile_url": map_tile_url,
            "map_tile_subdomains": str(WEB_CFG.get("map_tile_subdomains") or ""),
            "map_tile_attribution": str(WEB_CFG.get("map_tile_attribution") or ""),
            "map_tile_max_native_zoom": WEB_CFG.get("map_tile_max_native_zoom"),
            "map_api_configured": bool(map_tile_url),
            "map_default_legal_notice": not bool(map_tile_url),
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
            "workflow": _history_reparse_workflow_snapshot(),
            "settings_path": "/settings",
        },
    }
    if lightweight:
        payload.pop("map_drones", None)
        payload["meta"] = _home_meta_summary(payload.get("meta") or {})
    if not lightweight:
        with log_lock:
            logs = list(ap_buf)[-80:]
            logs_seq = ap_seq
        aps, aps_seq, aps_total = _ap_snapshot()
        payload.update({
            "logs": logs,
            "logs_seq": logs_seq,
            "aps": aps,
            "aps_seq": aps_seq,
            "aps_total": aps_total,
            "notifications": _notification_payload(200),
        })
    return payload

def _api_iso_now(ts: float | None = None) -> str:
    try:
        return time.strftime("%Y-%m-%dT%H:%M:%S%z", time.localtime(ts if ts is not None else time.time()))
    except Exception:
        return ""

def _load_build_info() -> dict:
    paths: list[str] = [_app_file_path(BUILD_INFO_FILE)]
    frozen_root = getattr(sys, "_MEIPASS", None)
    if frozen_root:
        paths.append(os.path.join(str(frozen_root), BUILD_INFO_FILE))
    seen: set[str] = set()
    for path in paths:
        key = os.path.normcase(os.path.abspath(str(path or "")))
        if not key or key in seen:
            continue
        seen.add(key)
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data if isinstance(data, dict) else {}
        except Exception:
            continue
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

def _app_update_download_state_path() -> str:
    return os.path.join(_app_update_state_dir(), "download.json")

def _app_update_staged_meta_path() -> str:
    return os.path.join(_app_update_state_dir(), "staged.json")

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

def _app_update_persist_download_state(payload: dict) -> dict:
    merged = dict(payload if isinstance(payload, dict) else {})
    merged["updated_at"] = time.time()
    _app_update_write_json(_app_update_download_state_path(), merged)
    return merged

def _app_update_download_state() -> dict:
    return _app_update_read_json(_app_update_download_state_path())

def _app_update_update_runtime_state(payload: dict) -> None:
    if not isinstance(payload, dict):
        return
    with app_update_lock:
        APP_UPDATE_STATE.update(payload)

def _app_update_set_download_state(**payload) -> dict:
    state = _app_update_download_state()
    state.update(payload)
    persisted = _app_update_persist_download_state(state)
    runtime = {
        "download_running": bool(persisted.get("running")),
        "download_status": str(persisted.get("status") or ""),
        "download_message": str(persisted.get("message") or ""),
        "downloaded_bytes": int(persisted.get("downloaded_bytes") or 0),
        "download_total_bytes": int(persisted.get("download_total_bytes") or 0),
        "download_percent": float(persisted.get("download_percent") or 0.0),
        "last_error": str(persisted.get("last_error") or ""),
    }
    _app_update_update_runtime_state(runtime)
    return persisted

def _app_update_stage_meta() -> dict:
    return _app_update_read_json(_app_update_staged_meta_path())

def _app_update_write_stage_meta(payload: dict) -> dict:
    merged = dict(payload if isinstance(payload, dict) else {})
    merged["updated_at"] = time.time()
    _app_update_write_json(_app_update_staged_meta_path(), merged)
    _app_update_update_runtime_state({
        "staged_ready": bool(merged.get("ready")),
        "staged_source": str(merged.get("source") or ""),
        "staged_tag": str(merged.get("latest_tag") or ""),
        "staged_asset_name": str(merged.get("asset_name") or ""),
        "staged_sha256": str(merged.get("sha256") or ""),
        "staged_expected_sha256": str(merged.get("expected_sha256") or ""),
        "staged_verified": bool(merged.get("verified")),
        "staged_size": int(merged.get("size") or 0),
    })
    return merged

def _app_update_clear_stage_meta(remove_file: bool = True) -> None:
    if remove_file:
        _app_update_remove_file(_app_update_staged_meta_path())
    _app_update_update_runtime_state({
        "staged_ready": False,
        "staged_source": "",
        "staged_tag": "",
        "staged_asset_name": "",
        "staged_sha256": "",
        "staged_expected_sha256": "",
        "staged_verified": False,
        "staged_size": 0,
    })

def _app_update_upload_sessions_purge(now_ts: float | None = None) -> None:
    now = float(now_ts or time.time())
    with app_update_upload_lock:
        stale = [
            key
            for key, item in app_update_upload_sessions.items()
            if now >= float((item or {}).get("expires_at") or 0.0)
        ]
        for key in stale:
            app_update_upload_sessions.pop(key, None)

def _app_update_upload_session_create(file_name: str, total_bytes: int) -> dict:
    safe_name = _app_update_safe_filename(file_name)
    size = int(total_bytes or 0)
    if size <= 0:
        raise ValueError("empty upload")
    if size > APP_UPDATE_MAX_BYTES:
        raise ValueError(f"upload too large (>{APP_UPDATE_MAX_BYTES} bytes)")
    release_url = str(APP_UPDATE_CFG.get("release_url") or APP_UPDATE_RELEASE_URL_DEFAULT)
    release = _fetch_latest_release(release_url)
    support = _app_update_runtime_support()
    asset = _pick_release_asset(release.get("assets") or [], str(support.get("target_arch") or ""))
    if not asset:
        raise ValueError("latest release has no matching asset for this architecture")
    digest = _app_update_normalize_digest(asset.get("digest") or "")
    force_update = bool(APP_UPDATE_CFG.get("force_update"))
    if not digest and not force_update:
        raise ValueError("GitHub release asset digest is missing")
    if not safe_name:
        safe_name = _app_update_safe_filename(str(asset.get("name") or "")) or "package.bin"
    token = secrets.token_urlsafe(24)
    payload = {
        "token": token,
        "expires_at": time.time() + float(APP_UPDATE_UPLOAD_SESSION_TTL_SEC),
        "latest_tag": str(release.get("tag_name") or ""),
        "latest_commit": str(release.get("target_commitish") or ""),
        "asset": dict(asset),
        "release": {
            "tag_name": str(release.get("tag_name") or ""),
            "target_commitish": str(release.get("target_commitish") or ""),
            "html_url": str(release.get("html_url") or ""),
            "published_at": str(release.get("published_at") or ""),
        },
    }
    _app_update_upload_sessions_purge()
    with app_update_upload_lock:
        app_update_upload_sessions[token] = payload
    return {
        "token": token,
        "asset_name": str(asset.get("name") or safe_name),
        "expected_sha256": digest,
        "latest_tag": str(release.get("tag_name") or ""),
        "latest_commit": str(release.get("target_commitish") or ""),
        "release_url": str(release.get("html_url") or ""),
        "expires_at": float(payload.get("expires_at") or 0.0),
    }

def _app_update_upload_session_get(token: str) -> dict:
    raw_token = str(token or "").strip()
    if not raw_token:
        return {}
    _app_update_upload_sessions_purge()
    with app_update_upload_lock:
        payload = dict(app_update_upload_sessions.get(raw_token) or {})
    if not payload:
        raise ValueError("upload session expired, please reselect the package")
    return payload

def _app_update_upload_session_remove(token: str) -> None:
    raw_token = str(token or "").strip()
    if not raw_token:
        return
    with app_update_upload_lock:
        app_update_upload_sessions.pop(raw_token, None)

def _discard_upload_stream(body_stream, total_bytes: int) -> None:
    remain = max(0, int(total_bytes or 0))
    while remain > 0:
        chunk = body_stream.read(min(1024 * 512, remain))
        if not chunk:
            break
        remain -= len(chunk)

def _app_update_requires_sudo() -> bool:
    try:
        return hasattr(os, "geteuid") and int(os.geteuid()) != 0
    except Exception:
        return False

def _app_update_sudo_blocked_reason(raw_error: str = "") -> str:
    text = str(raw_error or "").strip()
    if text:
        lower = text.lower()
        if "unable to change to root gid" in lower or "sudoers_audit" in lower:
            return (
                "当前服务进程无法执行 sudo 提权：systemd 权限边界阻止切换到 root。"
                "请通过 SSH/root 执行安装或使用同步部署。原始错误: " + text
            )
        return "sudo 提权不可用: " + text
    return (
        "当前服务进程无法执行 sudo 提权。"
        "如果服务以 rid 用户并带 CapabilityBoundingSet 运行，请通过 SSH/root 执行安装或使用同步部署。"
    )

def _app_update_can_elevate() -> bool:
    if not _app_update_requires_sudo():
        return True
    try:
        return bool(_can_run_privileged_actions())
    except Exception:
        return False

def _app_update_normalize_digest(text: str) -> str:
    raw = str(text or "").strip().lower()
    if raw.startswith("sha256:"):
        raw = raw.split(":", 1)[1].strip()
    return raw if re.fullmatch(r"[0-9a-f]{64}", raw or "") else ""

def _app_update_file_sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            chunk = f.read(1024 * 1024)
            if not chunk:
                break
            h.update(chunk)
    return h.hexdigest().lower()

def _app_update_safe_filename(name: str) -> str:
    base = os.path.basename(str(name or "").strip())
    safe = re.sub(r"[^0-9A-Za-z._-]+", "_", base)[:160]
    if not safe or safe in (".", ".."):
        raise ValueError("invalid file name")
    return safe

def _app_update_prepare_stage_dir(prefix: str) -> str:
    root = _app_update_ensure_dir(_app_update_stage_root())
    stamp = time.strftime("%Y%m%d_%H%M%S")
    safe_prefix = re.sub(r"[^0-9A-Za-z._-]+", "_", str(prefix or "pkg"))[:40] or "pkg"
    return tempfile.mkdtemp(prefix=f"{safe_prefix}_{stamp}_", dir=root)

def _app_update_cleanup_stage_meta(meta: dict | None) -> None:
    if not isinstance(meta, dict):
        return
    try:
        file_path = os.path.abspath(str(meta.get("file_path") or ""))
        stage_dir = os.path.abspath(str(meta.get("stage_dir") or ""))
        if file_path and os.path.isfile(file_path):
            os.remove(file_path)
        if stage_dir and os.path.isdir(stage_dir):
            shutil.rmtree(stage_dir, ignore_errors=True)
    except Exception:
        pass

def _app_update_valid_stage_meta() -> dict:
    meta = _app_update_stage_meta()
    if not meta:
        return {}
    file_path = os.path.abspath(str(meta.get("file_path") or ""))
    if not file_path or not os.path.isfile(file_path):
        _app_update_clear_stage_meta(remove_file=True)
        return {}
    return meta

def _app_update_register_staged_package(
    *,
    source: str,
    file_path: str,
    stage_dir: str,
    release: dict,
    asset: dict,
    sha256_hex: str,
    size: int,
    verified: bool = True,
) -> dict:
    previous = _app_update_valid_stage_meta()
    if previous:
        _app_update_cleanup_stage_meta(previous)
    meta = {
        "ready": True,
        "source": str(source or ""),
        "file_path": os.path.abspath(str(file_path or "")),
        "stage_dir": os.path.abspath(str(stage_dir or "")),
        "latest_tag": str((release or {}).get("tag_name") or ""),
        "latest_commit": str((release or {}).get("target_commitish") or ""),
        "asset_name": str((asset or {}).get("name") or ""),
        "asset_url": str((asset or {}).get("url") or ""),
        "expected_sha256": _app_update_normalize_digest((asset or {}).get("digest") or ""),
        "sha256": _app_update_normalize_digest(sha256_hex or ""),
        "verified": bool(verified),
        "size": int(size or 0),
        "prepared_at": time.time(),
    }
    return _app_update_write_stage_meta(meta)

def _app_update_stage_install_plan(stage_meta: dict, state: dict, manual: bool) -> dict:
    return {
        "version": 1,
        "requested_at": time.time(),
        "requested_by": "manual" if manual else "auto",
        "latest_tag": str(stage_meta.get("latest_tag") or ""),
        "latest_commit": str(stage_meta.get("latest_commit") or ""),
        "current_tag": str((state or {}).get("current_tag") or ""),
        "current_commit": str((state or {}).get("current_commit") or ""),
        "target_arch": str((state or {}).get("target_arch") or ""),
        "target_path": str(_app_update_runtime_support().get("target_path") or ""),
        "asset_name": str(stage_meta.get("asset_name") or ""),
        "asset_url": str(stage_meta.get("asset_url") or ""),
        "download_path": os.path.abspath(str(stage_meta.get("file_path") or "")),
        "stage_dir": os.path.abspath(str(stage_meta.get("stage_dir") or "")),
        "response_grace_sec": 2,
        "package_source": str(stage_meta.get("source") or ""),
        "package_sha256": str(stage_meta.get("sha256") or ""),
        "package_expected_sha256": str(stage_meta.get("expected_sha256") or ""),
    }

def _app_update_download_worker(release_url: str) -> None:
    stage_dir = ""
    download_path = ""
    try:
        release = _fetch_latest_release(release_url)
        support = _app_update_runtime_support()
        asset = _pick_release_asset(release.get("assets") or [], str(support.get("target_arch") or ""))
        if not asset:
            raise RuntimeError("latest release has no matching asset for this architecture")
        digest = _app_update_normalize_digest(asset.get("digest") or "")
        force_update = bool(APP_UPDATE_CFG.get("force_update"))
        if not digest and not force_update:
            raise RuntimeError("GitHub release asset digest is missing")
        stage_dir = _app_update_prepare_stage_dir(str(release.get("tag_name") or "download"))
        download_path = os.path.join(stage_dir, str(asset.get("name") or "package.bin"))
        total_size = int(asset.get("size") or 0)
        _app_update_set_download_state(
            running=True,
            status="downloading",
            message=f"downloading {asset.get('name') or 'package'}",
            downloaded_bytes=0,
            download_total_bytes=total_size,
            download_percent=0.0,
            latest_tag=str(release.get("tag_name") or ""),
            asset_name=str(asset.get("name") or ""),
            last_error="",
        )
        h = hashlib.sha256()
        downloaded = 0
        last_update = 0.0
        with _app_update_http_open(
            str(asset.get("url") or ""),
            headers={"User-Agent": APP_HTTP_USER_AGENT + " (+asset download)"},
            timeout=30,
        ) as resp, open(download_path, "wb") as f:
            while True:
                chunk = resp.read(1024 * 512)
                if not chunk:
                    break
                f.write(chunk)
                h.update(chunk)
                downloaded += len(chunk)
                now = time.time()
                if (now - last_update) >= 0.5:
                    percent = (downloaded * 100.0 / total_size) if total_size > 0 else 0.0
                    _app_update_set_download_state(
                        running=True,
                        status="downloading",
                        message=f"downloading {asset.get('name') or 'package'}",
                        downloaded_bytes=downloaded,
                        download_total_bytes=total_size,
                        download_percent=percent,
                        latest_tag=str(release.get("tag_name") or ""),
                        asset_name=str(asset.get("name") or ""),
                        last_error="",
                    )
                    last_update = now
        actual_digest = h.hexdigest().lower()
        verified = bool(digest and actual_digest == digest)
        if not verified and not force_update:
            raise RuntimeError("downloaded package SHA256 does not match GitHub asset digest")
        meta = _app_update_register_staged_package(
            source="download",
            file_path=download_path,
            stage_dir=stage_dir,
            release=release,
            asset=asset,
            sha256_hex=actual_digest,
            size=os.path.getsize(download_path),
            verified=verified,
        )
        _app_update_set_download_state(
            running=False,
            status="completed" if verified else "completed_unverified",
            message=(f"downloaded and verified {meta.get('asset_name') or 'package'}" if verified else f"downloaded without valid SHA256: {meta.get('asset_name') or 'package'}"),
            downloaded_bytes=int(meta.get("size") or 0),
            download_total_bytes=int(meta.get("size") or 0),
            download_percent=100.0,
            latest_tag=str(meta.get("latest_tag") or ""),
            asset_name=str(meta.get("asset_name") or ""),
            last_error="",
        )
        _app_update_write_notice({
            "kind": "ok",
            "title": "安装包已就绪",
            "text": (f"{meta.get('asset_name') or '安装包'} 已下载并通过 SHA256 校验，可开始更新。" if verified else f"{meta.get('asset_name') or '安装包'} 已下载，但未通过 SHA256 校验；已按强制更新设置允许继续。"),
            "tag": str(meta.get("latest_tag") or ""),
            "asset_name": str(meta.get("asset_name") or ""),
        })
    except Exception as e:
        _app_update_set_download_state(
            running=False,
            status="failed",
            message=str(e),
            last_error=str(e),
        )
        try:
            if download_path and os.path.isfile(download_path):
                os.remove(download_path)
            if stage_dir and os.path.isdir(stage_dir):
                shutil.rmtree(stage_dir, ignore_errors=True)
        except Exception:
            pass

def _start_app_update_download(manual: bool = False) -> dict:
    state = _app_update_status_payload()
    if bool(state.get("download_running")):
        return {"ok": False, "error": "下载任务已经在运行", "state": state}
    if bool(state.get("installing")):
        return {"ok": False, "error": "更新安装流程正在运行", "state": state}
    if not bool(state.get("install_supported")):
        return {"ok": False, "error": str(state.get("support_reason") or "当前运行模式不支持自动更新"), "state": state}
    if not bool(state.get("update_available")):
        check_rsp = _check_app_update_once(manual=manual, auto_apply=False)
        state = dict(check_rsp.get("state") or {})
        if not check_rsp.get("ok"):
            return check_rsp
        if not bool(state.get("update_available")):
            return {"ok": False, "error": "当前没有可下载的新版本", "state": state}
    _app_update_clear_stage_meta(remove_file=True)
    release_url = str(APP_UPDATE_CFG.get("release_url") or APP_UPDATE_RELEASE_URL_DEFAULT)
    _app_update_set_download_state(
        running=True,
        status="queued",
        message="download task queued",
        downloaded_bytes=0,
        download_total_bytes=0,
        download_percent=0.0,
        latest_tag=str(state.get("latest_tag") or ""),
        asset_name=str(state.get("asset_name") or ""),
        last_error="",
    )
    Thread(target=lambda: _app_update_download_worker(release_url), daemon=True).start()
    return {
        "ok": True,
        "message": "下载任务已开始，离开页面后仍会继续。",
        "state": _app_update_status_payload(),
    }

def _prepare_uploaded_app_update_package(file_name: str, total_bytes: int) -> dict:
    info = _app_update_upload_session_create(file_name, total_bytes)
    return {
        "ok": True,
        "prepare": info,
        "message": f"ready to upload {info.get('asset_name') or _app_update_safe_filename(file_name)}",
        "state": _app_update_status_payload(),
    }

def _accept_uploaded_app_update_package(file_name: str, body_stream, total_bytes: int, upload_token: str = "") -> dict:
    safe_name = _app_update_safe_filename(file_name)
    if int(total_bytes or 0) <= 0:
        raise ValueError("empty upload")
    if int(total_bytes) > APP_UPDATE_MAX_BYTES:
        raise ValueError(f"upload too large (>{APP_UPDATE_MAX_BYTES} bytes)")
    session = _app_update_upload_session_get(upload_token) if upload_token else {}
    if session:
        release = dict(session.get("release") or {})
        asset = dict(session.get("asset") or {})
    else:
        release_url = str(APP_UPDATE_CFG.get("release_url") or APP_UPDATE_RELEASE_URL_DEFAULT)
        release = _fetch_latest_release(release_url)
        support = _app_update_runtime_support()
        asset = _pick_release_asset(release.get("assets") or [], str(support.get("target_arch") or ""))
        if not asset:
            raise ValueError("latest release has no matching asset for this architecture")
    digest = _app_update_normalize_digest(asset.get("digest") or "")
    force_update = bool(APP_UPDATE_CFG.get("force_update"))
    if not digest and not force_update:
        raise ValueError("GitHub release asset digest is missing")
    asset_file_name = _app_update_safe_filename(str(asset.get("name") or "")) or safe_name or "package.bin"
    stage_dir = _app_update_prepare_stage_dir(str(release.get("tag_name") or "upload"))
    file_path = os.path.join(stage_dir, asset_file_name)
    h = hashlib.sha256()
    written = 0
    try:
        with open(file_path, "wb") as f:
            remain = int(total_bytes)
            while remain > 0:
                chunk = body_stream.read(min(1024 * 512, remain))
                if not chunk:
                    break
                f.write(chunk)
                h.update(chunk)
                written += len(chunk)
                remain -= len(chunk)
        if written != int(total_bytes):
            raise ValueError("upload truncated before all bytes were received")
        actual_digest = h.hexdigest().lower()
        verified = bool(digest and actual_digest == digest)
        if not verified and not force_update:
            raise ValueError("uploaded package SHA256 does not match GitHub asset digest")
        meta = _app_update_register_staged_package(
            source="upload",
            file_path=file_path,
            stage_dir=stage_dir,
            release=release,
            asset=asset,
            sha256_hex=actual_digest,
            size=written,
            verified=verified,
        )
        _app_update_set_download_state(
            running=False,
            status="uploaded" if verified else "uploaded_unverified",
            message=(f"uploaded and verified {meta.get('asset_name') or safe_name}" if verified else f"uploaded without valid SHA256: {meta.get('asset_name') or safe_name}"),
            downloaded_bytes=written,
            download_total_bytes=written,
            download_percent=100.0,
            latest_tag=str(meta.get("latest_tag") or ""),
            asset_name=str(meta.get("asset_name") or ""),
            last_error="",
        )
        _app_update_upload_session_remove(upload_token)
        return meta
    except Exception:
        try:
            if os.path.isfile(file_path):
                os.remove(file_path)
            if os.path.isdir(stage_dir):
                shutil.rmtree(stage_dir, ignore_errors=True)
        except Exception:
            pass
        raise

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
    tag = str(_app_update_read_json(_app_update_current_path()).get("installed_tag") or "").strip()
    if tag:
        return tag
    return f"v{APP_RELEASE_VERSION}"

def _normalize_commit_ref(text: str) -> str:
    raw = str(text or "").strip().lower()
    return raw if re.fullmatch(r"[0-9a-f]{7,40}", raw or "") else ""

def _app_update_available(current_tag: str, latest_tag: str, current_commit: str, latest_commit: str) -> bool:
    cur_tag = str(current_tag or "").strip()
    new_tag = str(latest_tag or "").strip()
    if cur_tag and new_tag:
        return cur_tag != new_tag
    cur_commit = _normalize_commit_ref(current_commit)
    new_commit = _normalize_commit_ref(latest_commit)
    if cur_commit and new_commit:
        return cur_commit != new_commit
    return False

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
    tag = _local_app_tag()
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
    return f"{tag} commit:{commit}#{build}"

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

def _app_update_mirror_url(url: str) -> str:
    raw = str(url or "").strip()
    if not raw:
        return raw
    mirror = str(APP_UPDATE_CFG.get("mirror") or "github").strip().lower()
    if mirror == "github":
        return raw
    if mirror == "gh-proxy":
        return raw if raw.startswith(GITHUB_PROXY_PREFIX) else (GITHUB_PROXY_PREFIX + raw)
    if mirror == "custom":
        base = str(APP_UPDATE_CFG.get("custom_mirror") or "").strip()
        if not base:
            return raw
        if "{url}" in base:
            return base.replace("{url}", raw)
        if "{encoded_url}" in base:
            return base.replace("{encoded_url}", urllib.parse.quote(raw, safe=""))
        return base.rstrip("/") + "/" + raw
    return raw

def _app_update_http_read(url: str, headers: dict | None = None, timeout: float = 12, max_bytes: int | None = None) -> bytes:
    final_url = _app_update_mirror_url(url)
    req = urllib.request.Request(final_url, headers=headers or {})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        if max_bytes is None or max_bytes <= 0:
            return resp.read()
        return resp.read(max_bytes + 1)[:max_bytes]

def _app_update_http_open(url: str, headers: dict | None = None, timeout: float = 30):
    final_url = _app_update_mirror_url(url)
    req = urllib.request.Request(final_url, headers=headers or {})
    return urllib.request.urlopen(req, timeout=timeout)

def _fetch_latest_release(release_url: str) -> dict:
    raw = _app_update_http_read(
        release_url,
        headers={
            "User-Agent": APP_HTTP_USER_AGENT + " (+release update)",
            "Accept": "application/vnd.github+json",
        },
        timeout=12,
        max_bytes=1024 * 1024,
    )
    data = json.loads(raw.decode("utf-8", errors="replace"))
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
            "digest": _app_update_normalize_digest(item.get("digest") or ""),
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
    with _app_update_http_open(
        url,
        headers={"User-Agent": APP_HTTP_USER_AGENT + " (+asset download)"},
        timeout=30,
    ) as resp, open(download_path, "wb") as f:
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
    download_state = _app_update_download_state()
    stage_meta = _app_update_valid_stage_meta()
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
    state["download_running"] = bool(download_state.get("running"))
    state["download_status"] = str(download_state.get("status") or state.get("download_status") or "")
    state["download_message"] = str(download_state.get("message") or state.get("download_message") or "")
    state["downloaded_bytes"] = int(download_state.get("downloaded_bytes") or 0)
    state["download_total_bytes"] = int(download_state.get("download_total_bytes") or 0)
    state["download_percent"] = float(download_state.get("download_percent") or 0.0)
    if download_state.get("last_error"):
        state["last_error"] = str(download_state.get("last_error") or state.get("last_error") or "")
    state["staged_ready"] = bool(stage_meta.get("ready"))
    state["staged_source"] = str(stage_meta.get("source") or "")
    state["staged_tag"] = str(stage_meta.get("latest_tag") or "")
    state["staged_asset_name"] = str(stage_meta.get("asset_name") or "")
    state["staged_sha256"] = str(stage_meta.get("sha256") or "")
    state["staged_expected_sha256"] = str(stage_meta.get("expected_sha256") or "")
    state["staged_verified"] = bool(stage_meta.get("verified"))
    state["staged_size"] = int(stage_meta.get("size") or 0)
    requires_sudo = _app_update_requires_sudo()
    can_elevate = _app_update_can_elevate()
    state["requires_sudo"] = bool(requires_sudo)
    state["can_elevate"] = bool(can_elevate)
    state["sudo_blocked_reason"] = _app_update_sudo_blocked_reason() if requires_sudo and not can_elevate else ""
    state["current_commit"] = current_commit
    state["current_tag"] = current_tag
    state["current_short"] = _short_commit(current_commit)
    state["latest_short"] = _short_commit(state.get("latest_commit") or "")
    state["release_url"] = str(cfg.get("release_url") or APP_UPDATE_RELEASE_URL_DEFAULT)
    state["mirror"] = str(cfg.get("mirror") or "github")
    state["custom_mirror"] = str(cfg.get("custom_mirror") or "")
    state["force_update"] = bool(cfg.get("force_update"))
    state["mirror_url"] = _app_update_mirror_url(state["release_url"])
    state["mirror_options"] = list(APP_UPDATE_MIRROR_OPTIONS)
    state["max_upload_bytes"] = int(APP_UPDATE_MAX_BYTES)
    state["install_supported"] = bool(support.get("supported"))
    state["support_reason"] = str(support.get("reason") or "")
    state["target_arch"] = str(support.get("target_arch") or state.get("target_arch") or "")
    state["checked"] = bool(state.get("last_check_ts"))
    notice = _app_update_pop_notice() if consume_notice else {}
    if notice:
        state["completion_notice"] = notice
    return state

def _check_app_update_once(manual: bool = False, auto_apply: bool = False) -> dict:
    _ = auto_apply
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
        update_available = _app_update_available(current_tag, latest_tag, current_commit, latest_commit)
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
            _log(
                "[INFO] 检测到程序更新: "
                f"local_tag={current_tag or '-'} latest_tag={latest_tag or '-'} "
                f"local_commit={_short_commit(current_commit)} latest_commit={_short_commit(latest_commit)}"
            )
        elif latest_tag or latest_commit:
            _log(
                "[INFO] 程序更新检查完成: "
                f"current_tag={current_tag or '-'} latest_tag={latest_tag or '-'} "
                f"current_commit={_short_commit(current_commit)} latest_commit={_short_commit(latest_commit)}"
            )
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
    state = _app_update_status_payload()
    if bool(state.get("installing")):
        return {"ok": False, "error": "更新流程已经在运行", "state": state}
    if not bool(state.get("install_supported")):
        return {"ok": False, "error": str(state.get("support_reason") or "当前运行模式不支持自动更新"), "state": state}
    if bool(state.get("download_running")):
        return {"ok": False, "error": "安装包仍在下载中，请等待校验完成", "state": state}
    stage_meta = _app_update_valid_stage_meta()
    if not stage_meta or not bool(stage_meta.get("ready")):
        return {"ok": False, "error": "请先下载或上传安装包", "state": _app_update_status_payload()}
    if not bool(stage_meta.get("verified")) and not bool(APP_UPDATE_CFG.get("force_update")):
        return {"ok": False, "error": "安装包未通过 SHA256 校验；如确认仍要继续，请在设置中启用强制更新", "state": _app_update_status_payload()}
    requires_sudo = _app_update_requires_sudo()
    if requires_sudo and not _app_update_can_elevate():
        reason = _app_update_sudo_blocked_reason()
        return {"ok": False, "error": reason, "need_sudo": False, "state": _app_update_status_payload()}
    if requires_sudo and not str(sudo_password or "").strip():
        return {"ok": False, "error": "sudo required", "need_sudo": True, "state": _app_update_status_payload()}
    if requires_sudo:
        ok_sudo, out_sudo, _rc_sudo = _run_privileged(["true"], timeout=8, sudo_password=sudo_password)
        if not ok_sudo:
            reason = _app_update_sudo_blocked_reason(out_sudo)
            return {"ok": False, "error": reason, "need_sudo": False, "state": _app_update_status_payload()}
    stage_dir = os.path.abspath(str(stage_meta.get("stage_dir") or ""))
    plan = _app_update_stage_install_plan(stage_meta, state, manual)
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
        "download_path": plan["download_path"],
        "message": "已准备安装已校验的安装包，等待更新进程接管 systemd 服务。",
    })
    ok, helper_ref = _app_update_spawn_helper(plan_path, sudo_password=sudo_password)
    if not ok:
        _app_update_lock_state({"status": "failed", "last_error": helper_ref, "message": helper_ref})
        return {"ok": False, "error": helper_ref, "state": _app_update_status_payload()}
    with app_update_lock:
        APP_UPDATE_STATE["installing"] = True
        APP_UPDATE_STATE["install_status"] = "scheduled"
        APP_UPDATE_STATE["asset_name"] = str(stage_meta.get("asset_name") or "")
        APP_UPDATE_STATE["asset_url"] = str(stage_meta.get("asset_url") or "")
        APP_UPDATE_STATE["latest_tag"] = str(stage_meta.get("latest_tag") or "")
        APP_UPDATE_STATE["latest_commit"] = str(stage_meta.get("latest_commit") or "")
        APP_UPDATE_STATE["last_install_ts"] = time.time()
    _op_log("app-update-start", f"tag={plan['latest_tag']} asset={plan['asset_name']} helper={helper_ref}", ok=True)
    return {
        "ok": True,
        "message": "更新进程已启动，服务将短暂重启。",
        "helper": helper_ref,
        "restart_expected": True,
        "state": _app_update_status_payload(),
    }

def start_app_update_check() -> None:
    Thread(target=lambda: _check_app_update_once(auto_apply=False), daemon=True).start()

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
        {"method": "GET", "path": "/api/simulation/status", "desc": "Ephemeral simulation status (page session)"},
        {"method": "POST", "path": "/api/simulation/start", "desc": "Start ephemeral target simulation (page session)"},
        {"method": "POST", "path": "/api/simulation/stop", "desc": "Stop and clear simulated targets (page session)"},
        {"method": "GET", "path": "/api/settings/export/settings", "desc": "Export settings file"},
        {"method": "GET", "path": "/api/settings/export/scan-data", "desc": "Export scan data"},
        {"method": "POST", "path": "/api/settings/import/settings", "desc": "Import settings file"},
        {"method": "POST", "path": "/api/settings/import/scan-data", "desc": "Import scan data"},
        {"method": "GET", "path": "/api/router/status", "desc": "GL-AR750S router status and redacted UCI configuration"},
        {"method": "POST", "path": "/api/router/validate", "desc": "Validate router configuration without applying it"},
        {"method": "POST", "path": "/api/router/wifi/scan", "desc": "Scan radio0 for 5GHz repeater uplinks"},
        {"method": "POST", "path": "/api/router/apply", "desc": "Schedule a router transaction with 90-second rollback"},
        {"method": "POST", "path": "/api/router/confirm", "desc": "Confirm a pending router transaction"},
        {"method": "POST", "path": "/api/router/rollback", "desc": "Roll back a pending router transaction"},
        {"method": "POST", "path": "/api/router/reset-network", "desc": "Restore the pre-install OpenWrt network baseline"},
        {"method": "GET", "path": "/api/logs/view?type=runtime|operation|scan|scan_diff|ap|system", "desc": "Built-in page log viewer"},
        {"method": "GET", "path": "/api/logs/export?type=all|runtime|operation|scan|scan_diff|ap|system", "desc": "Built-in page log export"},
        {"method": "POST", "path": "/api/v1/history/clear", "desc": "Clear history cache"},
        {"method": "POST", "path": "/api/v1/history/delete", "desc": "Delete one history item"},
        {"method": "GET", "path": "/api/v1/history/reidentify-status", "desc": "Background history reidentify workflow status"},
        {"method": "POST", "path": "/api/v1/history/reidentify-recent", "desc": "Queue recent history raw packets for background reidentify"},
        {"method": "POST", "path": "/api/v1/tracks/clear", "desc": "Clear tracks"},
        {"method": "POST", "path": "/api/v1/config/reload", "desc": "Reload config file"},
    ]


