def _notify_hit(ch: int):
    try:
        fn = globals().get("_hopper_note_hit")
        if callable(fn) and ch: fn()
    except Exception:
        pass

# -----------------------------------------------------------------------------
# ODID 解码
# -----------------------------------------------------------------------------
def decode_basic_id(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE: return None
    try:
        if ((msg25[0]>>4)&0xF) != MSG_TYPE_BASIC_ID: return None
        id_type = msg25[1] & 0x0F
        raw = msg25[2:22].rstrip(b"\x00")
        if not raw: return None
        # Lenient: allow >=4 bytes; non-ASCII bytes are replaced on decode.
        try:
            s = raw.decode("ascii", errors="replace").strip()
        except Exception:
            return None
        # Filter out strings that are mostly replacement chars.
        if not s or s.count("?") > len(s)//2: return None
        # Remove non-printable chars.
        s = "".join(c if 32<=ord(c)<=126 else "" for c in s)
        if len(s) < 4: return None
        return {"uas_id": s, "id_type": UA_ID_TYPE.get(id_type, f"Unk{id_type}")}
    except Exception:
        return None

def _coord_raw_invalid(raw: int) -> bool:
    try:
        v = int(raw)
    except Exception:
        return True
    return v in (-1, 0x7FFFFFFF, -0x80000000)

def _coord_raw_bytes_invalid(raw: bytes) -> bool:
    b = bytes(raw or b"")
    if len(b) != 4:
        return True
    return b == b"\xff" * 4 or b.count(0xff) >= 3

def _coord_pair_valid(lat: float, lon: float) -> bool:
    try:
        lat_f = float(lat)
        lon_f = float(lon)
    except Exception:
        return False
    if not (-90.0 <= lat_f <= 90.0 and -180.0 <= lon_f <= 180.0):
        return False
    # DJI invalid/sentinel coordinates can decode as non-zero values near 0,0;
    # treat that area as unavailable data for this scanner.
    if abs(lat_f) < 5.0 and abs(lon_f) < 5.0:
        return False
    return True

def _web_base_coord_pair() -> tuple[float, float] | None:
    web = globals().get("WEB_CFG")
    if not isinstance(web, dict):
        return None
    try:
        lat_raw = web.get("base_lat")
        lon_raw = web.get("base_lon")
        if lat_raw in (None, "") or lon_raw in (None, ""):
            return None
        lat = float(lat_raw)
        lon = float(lon_raw)
    except Exception:
        return None
    if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
        return None
    return (lat, lon)

def _coord_farther_than_limit(lat: float, lon: float, ref_lat: float | None, ref_lon: float | None,
                              limit_m: float = TRACK_ANOMALY_MAX_METERS) -> bool:
    if ref_lat is None or ref_lon is None:
        return False
    try:
        return _haversine(float(lat), float(lon), float(ref_lat), float(ref_lon)) > float(limit_m)
    except Exception:
        return False

def _new_fw_coord_anomalous(lat: float, lon: float, *,
                            prev_lat: float | None = None, prev_lon: float | None = None,
                            ref_lat: float | None = None, ref_lon: float | None = None,
                            limit_m: float = TRACK_ANOMALY_MAX_METERS) -> bool:
    if not _coord_pair_valid(lat, lon):
        return True
    if _coord_farther_than_limit(lat, lon, prev_lat, prev_lon, limit_m):
        return True
    if _coord_farther_than_limit(lat, lon, ref_lat, ref_lon, limit_m):
        return True
    return False

def _track_points_for_display(track: list[dict], firmware_type: str | None = None) -> list[dict]:
    if _firmware_type_key(firmware_type) != "new":
        return track
    base = _web_base_coord_pair()
    ref_lat = base[0] if base else None
    ref_lon = base[1] if base else None
    out: list[dict] = []
    prev_lat = None
    prev_lon = None
    for p in track:
        try:
            lat = float(p.get("lat"))
            lon = float(p.get("lon"))
        except Exception:
            continue
        if _new_fw_coord_anomalous(lat, lon, prev_lat=prev_lat, prev_lon=prev_lon,
                                   ref_lat=ref_lat, ref_lon=ref_lon):
            continue
        out.append(p)
        prev_lat = lat
        prev_lon = lon
    return out

def decode_location(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE: return None
    try:
        # Follow opendroneid-core-c ODID_Location_encoded layout exactly.
        if ((msg25[0] >> 4) & 0xF) != MSG_TYPE_LOCATION:
            return None

        b1 = msg25[1]
        speed_mult = b1 & 0x01

        spd_enc = int(msg25[3])
        if speed_mult:
            speed = float(spd_enc) * 0.75 + (255.0 * 0.25)
        else:
            speed = float(spd_enc) * 0.25
        if speed >= 255.0:
            speed = None

        vs_enc = struct.unpack_from("<b", msg25, 4)[0]
        vspeed = float(vs_enc) * 0.5
        if abs(vspeed - 63.0) < 1e-6:
            vspeed = None

        lat_raw = struct.unpack_from("<i", msg25, 5)[0]
        lon_raw = struct.unpack_from("<i", msg25, 9)[0]
        if _coord_raw_invalid(lat_raw) or _coord_raw_invalid(lon_raw):
            return None
        lat = float(lat_raw) * 1e-7
        lon = float(lon_raw) * 1e-7
        if not _coord_pair_valid(lat, lon):
            return None

        alt_baro_raw = struct.unpack_from("<H", msg25, 13)[0]
        alt_geo_raw = struct.unpack_from("<H", msg25, 15)[0]
        alt_baro = float(alt_baro_raw) * 0.5 - 1000.0
        alt_geo = float(alt_geo_raw) * 0.5 - 1000.0
        if abs(alt_baro + 1000.0) < 1e-6:
            alt_baro = None
        if abs(alt_geo + 1000.0) < 1e-6:
            alt_geo = None

        return {
            "lat": lat,
            "lon": lon,
            "alt_geodetic": (alt_geo if alt_geo is not None else alt_baro),
            "speed_ms": speed,
            "vspeed_ms": vspeed,
            # Heading is derived locally from consecutive valid coordinates.
            "direction_deg": None,
        }
    except Exception:
        return None

def _pilot_loc_type_text(v: int | None) -> str:
    m = {
        0: "unknown",
        1: "live_gnss",
        2: "takeoff",
        3: "fixed",
    }
    try:
        return m.get(int(v), "unknown")
    except Exception:
        return "unknown"

def decode_system(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE:
        return None
    try:
        if ((msg25[0] >> 4) & 0xF) != MSG_TYPE_SYSTEM:
            return None
        # OpenDroneID System encoded layout (opendroneid-core-c):
        # byte1: [reserved:3][classification:3][operator_location_type:2]
        lat_raw = struct.unpack_from("<i", msg25, 2)[0]
        lon_raw = struct.unpack_from("<i", msg25, 6)[0]
        if _coord_raw_invalid(lat_raw) or _coord_raw_invalid(lon_raw):
            return None
        lat = float(lat_raw) * 1e-7
        lon = float(lon_raw) * 1e-7
        if not _coord_pair_valid(lat, lon):
            return None
        b1 = int(msg25[1])
        loc_type = int(b1 & 0x03)
        cls_type = int((b1 >> 2) & 0x07)
        area_count = struct.unpack_from("<H", msg25, 10)[0]
        area_radius = int(msg25[12])
        return {
            "pilot_lat": lat,
            "pilot_lon": lon,
            "pilot_loc_type": loc_type,
            "pilot_loc_type_text": _pilot_loc_type_text(loc_type),
            "system_classification_type": cls_type,
            "system_area_count": int(area_count),
            "system_area_radius_m": area_radius,
        }
    except Exception:
        return None

def _decode_odid_pack_layout(p: bytes) -> tuple[int, int, int] | None:
    """Return (base, msg_size, qty) for packed ODID payload.
    Supports both:
      - New layout: [Fv][msg_size=25][qty][msgs...]
      - Legacy layout used in older parser: [Fv][qty][msgs...]
    """
    if not p or len(p) < 2:
        return None
    # Preferred / spec-like layout.
    if len(p) >= 3 and int(p[1]) == ODID_MSG_SIZE:
        qty = int(p[2])
        if 1 <= qty <= 15 and 3 + qty * ODID_MSG_SIZE <= len(p):
            return (3, ODID_MSG_SIZE, qty)
    # Legacy fallback.
    qty = int(p[1])
    if 1 <= qty <= 15 and 2 + qty * ODID_MSG_SIZE <= len(p):
        return (2, ODID_MSG_SIZE, qty)
    return None

def _valid_msg_header_byte(b: int) -> bool:
    mt = (int(b) >> 4) & 0xF
    pv = int(b) & 0xF
    return (mt in ODID_MSG_TYPES_OK) and (0 <= pv <= ODID_PROTOCOL_MAX)

def _valid_payload(p: bytes) -> bool:
    if not p or len(p) < 1: return False
    if not _valid_msg_header_byte(p[0]):
        return False
    mt = (p[0]>>4)&0xF
    if mt == MSG_TYPE_PACK:
        layout = _decode_odid_pack_layout(p)
        if not layout:
            return False
        base, msg_size, qty = layout
        for i in range(qty):
            if not _valid_msg_header_byte(p[base + i * msg_size]):
                return False
        return True
    return len(p) >= ODID_MSG_SIZE

def decode_odid(payload: bytes) -> dict:
    res: dict = {"basic_id": None, "location": None, "system": None}
    if not payload: return res
    mt = (payload[0]>>4)&0xF
    if mt == MSG_TYPE_PACK:
        layout = _decode_odid_pack_layout(payload)
        if not layout:
            return res
        base, msg_size, qty = layout
        for i in range(qty):
            s, e = base + i * msg_size, base + (i + 1) * msg_size
            if e > len(payload): break
            sub = payload[s:e]
            st  = (sub[0]>>4)&0xF
            if st==MSG_TYPE_BASIC_ID  and not res["basic_id"]:  res["basic_id"]  = decode_basic_id(sub)
            elif st==MSG_TYPE_LOCATION and not res["location"]: res["location"]  = decode_location(sub)
            elif st==MSG_TYPE_SYSTEM and not res["system"]:     res["system"]    = decode_system(sub)
        return res
    if len(payload) >= ODID_MSG_SIZE:
        m = payload[:ODID_MSG_SIZE]
        if mt==MSG_TYPE_BASIC_ID:   res["basic_id"]  = decode_basic_id(m)
        elif mt==MSG_TYPE_LOCATION: res["location"]  = decode_location(m)
        elif mt==MSG_TYPE_SYSTEM:   res["system"]    = decode_system(m)
    return res

def _payload_quality(payload: bytes) -> int:
    """Score payload quality; higher means more likely a real ODID payload."""
    if not _valid_payload(payload):
        return -1
    score = 1
    try:
        mt = (payload[0] >> 4) & 0xF
        if mt == MSG_TYPE_PACK:
            score += 1
        dec = decode_odid(payload)
        if dec.get("basic_id"):
            score += 2
        loc = dec.get("location")
        if isinstance(loc, dict) and loc.get("lat") is not None and loc.get("lon") is not None:
            score += 3
        sys_loc = dec.get("system")
        if isinstance(sys_loc, dict) and sys_loc.get("pilot_lat") is not None and sys_loc.get("pilot_lon") is not None:
            score += 2
    except Exception:
        pass
    return score

def _pick_payload_candidate(buf: bytes) -> bytes | None:
    """Pick best payload from bytes after OUI+type.
    Some frames include a 1-byte ODID service-info counter before payload.
    """
    if not buf:
        return None
    cands: list[tuple[int, int, bytes]] = []
    for off in (1, 0):  # Prefer skipping service-info counter first.
        if off >= len(buf):
            continue
        p = buf[off:]
        q = _payload_quality(p)
        if q >= 0:
            cands.append((q, off, p))
    if not cands:
        return None
    cands.sort(reverse=True)
    return cands[0][2]

def _new_fw_ascii_printable(raw: bytes) -> str:
    try:
        return "".join(chr(b) for b in bytes(raw or b"") if 32 <= int(b) <= 126).strip()
    except Exception:
        return ""

def _new_fw_ssid_rid(ssid_sn: str | None) -> str:
    s = str(ssid_sn or "").strip()
    if len(s) != RID_NEW_FW_SN_LEN:
        return ""
    if not re.fullmatch(r"[A-Za-z0-9]{20}", s):
        return ""
    return s

def _new_fw_read_rid_at(buf: bytes, off: int) -> str:
    if off < 0 or off + RID_NEW_FW_SN_LEN > len(buf):
        return ""
    s = _new_fw_ascii_printable(buf[off:off + RID_NEW_FW_SN_LEN])
    if len(s) != RID_NEW_FW_SN_LEN:
        return ""
    if not re.fullmatch(r"[A-Za-z0-9]{20}", s):
        return ""
    return s

def _new_fw_read_uas_id(buf: bytes, off: int) -> str:
    if off < 0 or off + RID_NEW_FW_UAS_LEN > len(buf):
        return ""
    raw = bytes(buf[off:off + RID_NEW_FW_UAS_LEN])
    if raw == b"\xff" * RID_NEW_FW_UAS_LEN:
        return ""
    s = _new_fw_ascii_printable(raw).rstrip("\x00").strip()
    return s[:RID_NEW_FW_UAS_LEN]

def _new_fw_read_ascii(buf: bytes, off: int, ln: int) -> str:
    if off < 0 or ln <= 0 or off + ln > len(buf):
        return ""
    raw = bytes(buf[off:off + ln])
    if raw == b"\xff" * ln:
        return ""
    try:
        return raw.decode("ascii", errors="ignore").rstrip("\x00").strip()
    except Exception:
        return ""

def _new_fw_decode_coord_pair(buf: bytes, off: int) -> dict | None:
    if off < 0 or off + 8 > len(buf):
        return None
    chunk = bytes(buf[off:off + 8])
    if chunk == b"\xff" * 8 or chunk[:4] == b"\xff" * 4 or chunk[4:] == b"\xff" * 4:
        return None
    if _coord_raw_bytes_invalid(chunk[:4]) or _coord_raw_bytes_invalid(chunk[4:]):
        return None
    try:
        lon_raw = struct.unpack_from("<i", buf, off)[0]
        lat_raw = struct.unpack_from("<i", buf, off + 4)[0]
    except Exception:
        return None
    if _coord_raw_invalid(lon_raw) or _coord_raw_invalid(lat_raw):
        return None
    lon = float(lon_raw) * 1e-7
    lat = float(lat_raw) * 1e-7
    if not _coord_pair_valid(lat, lon):
        return None
    return {
        "lat": round(lat, 7),
        "lon": round(lon, 7),
        "_coord_off": off,
    }

def _new_fw_decode_coord_pair_at(buf: bytes, lon_off: int, lat_off: int) -> dict | None:
    if lon_off < 0 or lat_off < 0 or lon_off + 4 > len(buf) or lat_off + 4 > len(buf):
        return None
    lon_b = bytes(buf[lon_off:lon_off + 4])
    lat_b = bytes(buf[lat_off:lat_off + 4])
    if _coord_raw_bytes_invalid(lon_b) or _coord_raw_bytes_invalid(lat_b):
        return None
    try:
        lon_raw = struct.unpack_from("<i", buf, lon_off)[0]
        lat_raw = struct.unpack_from("<i", buf, lat_off)[0]
    except Exception:
        return None
    if _coord_raw_invalid(lon_raw) or _coord_raw_invalid(lat_raw):
        return None
    lon = float(lon_raw) * 1e-7
    lat = float(lat_raw) * 1e-7
    if not _coord_pair_valid(lat, lon):
        return None
    return {
        "lat": round(lat, 7),
        "lon": round(lon, 7),
        "_coord_off": min(lon_off, lat_off),
    }

def _new_fw_decode_altitude(buf: bytes, off: int) -> float | None:
    if off < 0 or off + 2 > len(buf):
        return None
    try:
        raw = struct.unpack_from("<H", buf, off)[0]
    except Exception:
        return None
    return round(float(raw) * 0.5 - 1000.0, 1)

def _new_fw_decode_u16_scaled(buf: bytes, off: int, scale: float, offset: float,
                              invalid: int | None = None) -> float | None:
    if off < 0 or off + 2 > len(buf):
        return None
    try:
        raw = struct.unpack_from("<H", buf, off)[0]
    except Exception:
        return None
    if invalid is not None and raw == invalid:
        return None
    return round(float(raw) * float(scale) + float(offset), 1)

def _new_fw_decode_track_deg(buf: bytes, off: int) -> float | None:
    if off < 0 or off + 2 > len(buf):
        return None
    try:
        raw = struct.unpack_from("<H", buf, off)[0]
    except Exception:
        return None
    if raw == 0xFFFF or raw > 3599:
        return None
    return round(float(raw) / 10.0, 1)

def _new_fw_decode_ground_speed(buf: bytes, off: int) -> float | None:
    return _new_fw_decode_u16_scaled(buf, off, 0.1, 0.0, invalid=0xFFFF)

def _new_fw_decode_vertical_speed(buf: bytes, off: int) -> float | None:
    if off < 0 or off >= len(buf):
        return None
    raw = int(buf[off])
    if raw == 0xFF:
        return None
    speed = float(raw & 0x7F) / 2.0
    if raw & 0x80:
        speed = -speed
    return round(speed, 1)

def _new_fw_decode_uint48_le(buf: bytes, off: int) -> int | None:
    if off < 0 or off + 6 > len(buf):
        return None
    raw = bytes(buf[off:off + 6])
    if raw == b"\x00" * 6:
        return None
    return int.from_bytes(raw, "little", signed=False)

def _new_fw_identifier_present(identifiers: bytes, index: int) -> bool:
    if index < 1 or index > 21 or len(identifiers) != 3:
        return False
    bits = int.from_bytes(identifiers, "big")
    return bool(bits & (1 << (24 - index)))

RID_NEW_FW_GB_FIELDS = [
    (1, "sn", 20),
    (2, "uas_id", 8),
    (3, "operation_category", 1),
    (4, "aircraft_category", 1),
    (5, "pilot_loc_type", 1),
    (6, "pilot_coord", 8),
    (7, "pilot_alt", 2),
    (8, "drone_coord", 8),
    (9, "track_deg", 2),
    (10, "ground_speed", 2),
    (11, "relative_alt", 2),
    (12, "vertical_speed", 1),
    (13, "geoid_alt", 2),
    (14, "baro_alt", 2),
    (15, "operation_state", 1),
    (16, "coord_sys", 1),
    (17, "horizontal_accuracy", 1),
    (18, "vertical_accuracy", 1),
    (19, "speed_accuracy", 1),
    (20, "timestamp_ms", 6),
    (21, "timestamp_accuracy", 1),
]

RID_NEW_FW_OPERATION_CATEGORY = {0: "未定义", 1: "开放类", 2: "特定类", 3: "审定类"}
RID_NEW_FW_AIRCRAFT_CATEGORY = {0: "微型", 1: "轻型", 2: "小型", 3: "中型", 4: "大型"}
RID_NEW_FW_PILOT_LOC_TYPE = {0: "起飞点位置", 1: "遥控站位置"}
RID_NEW_FW_OPERATION_STATE = {
    0: "未报告",
    1: "地面",
    2: "空中",
    3: "紧急",
    4: "运行识别失效/非紧急",
    5: "运行识别失效/紧急",
}
RID_NEW_FW_COORD_SYS = {0: "WGS-84", 1: "CGCS2000"}
RID_NEW_FW_TS_ACCURACY = {
    0: ">0.5s 或未知",
    1: "<=0.5s",
    2: "<=0.4s",
    3: "<=0.3s",
    4: "<=0.2s",
    5: "<=0.1s",
    6: "<=50ms",
    7: "<=20ms",
    8: "<=10ms",
}

def _new_fw_label(mapping: dict, value) -> str:
    try:
        v = int(value)
    except Exception:
        return ""
    return str(mapping.get(v, v))

def _decode_new_fw_gb_items(vendor: bytes) -> dict | None:
    if len(vendor) < RID_NEW_FW_BODY_MIN:
        return None
    if vendor[0:3] != ODID_OUI or int(vendor[3]) != DJI_RID_VENDOR_TYPE:
        return None
    gb = bytes(vendor[RID_NEW_FW_GB_OFF:])
    if len(gb) < 6 or int(gb[0]) != 0xFF:
        return None
    data_len = int(gb[2])
    identifiers = bytes(gb[3:6])
    cursor = RID_NEW_FW_GB_OFF + 6
    data_end = min(len(vendor), cursor + data_len)
    fields: dict = {
        "dji_prefix": vendor[0:5].hex(" "),
        "gb_data_type": int(gb[0]),
        "gb_version_raw": int(gb[1]),
        "gb_version": f"V{int(gb[1]) >> 5}.{int(gb[1]) & 0x1F}",
        "gb_data_len": data_len,
        "gb_identifiers": identifiers.hex(" "),
    }
    for index, name, ln in RID_NEW_FW_GB_FIELDS:
        if not _new_fw_identifier_present(identifiers, index):
            continue
        if cursor + ln > len(vendor) or cursor + ln > data_end:
            return None
        off = cursor
        raw = bytes(vendor[off:off + ln])
        cursor += ln
        if name == "sn":
            fields["sn"] = _new_fw_read_ascii(vendor, off, ln)
        elif name == "uas_id":
            fields["uas_id"] = _new_fw_read_ascii(vendor, off, ln)
        elif name == "operation_category":
            fields["operation_category"] = int(raw[0])
            fields["operation_category_text"] = _new_fw_label(RID_NEW_FW_OPERATION_CATEGORY, raw[0])
        elif name == "aircraft_category":
            fields["aircraft_category"] = int(raw[0])
            fields["aircraft_category_text"] = _new_fw_label(RID_NEW_FW_AIRCRAFT_CATEGORY, raw[0])
        elif name == "pilot_loc_type":
            fields["pilot_loc_type"] = int(raw[0])
            fields["pilot_loc_type_text"] = _new_fw_label(RID_NEW_FW_PILOT_LOC_TYPE, raw[0])
        elif name == "pilot_coord":
            fields["pilot_coord"] = _new_fw_decode_coord_pair(vendor, off)
        elif name == "pilot_alt":
            fields["pilot_alt"] = _new_fw_decode_u16_scaled(vendor, off, 0.5, -1000.0, invalid=0)
        elif name == "drone_coord":
            fields["drone_coord"] = _new_fw_decode_coord_pair(vendor, off)
        elif name == "track_deg":
            fields["track_deg"] = _new_fw_decode_track_deg(vendor, off)
        elif name == "ground_speed":
            fields["ground_speed"] = _new_fw_decode_ground_speed(vendor, off)
        elif name == "relative_alt":
            fields["relative_alt"] = _new_fw_decode_u16_scaled(vendor, off, 0.5, -9000.0, invalid=0)
        elif name == "vertical_speed":
            fields["vertical_speed"] = _new_fw_decode_vertical_speed(vendor, off)
        elif name == "geoid_alt":
            fields["geoid_alt"] = _new_fw_decode_u16_scaled(vendor, off, 0.5, -1000.0, invalid=0)
        elif name == "baro_alt":
            fields["baro_alt"] = _new_fw_decode_u16_scaled(vendor, off, 0.5, -1000.0, invalid=0)
        elif name == "operation_state":
            fields["operation_state"] = int(raw[0])
            fields["operation_state_text"] = _new_fw_label(RID_NEW_FW_OPERATION_STATE, raw[0])
        elif name == "coord_sys":
            fields["coord_sys"] = int(raw[0])
            fields["coord_sys_text"] = _new_fw_label(RID_NEW_FW_COORD_SYS, raw[0])
        elif name == "horizontal_accuracy":
            fields["horizontal_accuracy"] = int(raw[0])
        elif name == "vertical_accuracy":
            fields["vertical_accuracy"] = int(raw[0])
        elif name == "speed_accuracy":
            fields["speed_accuracy"] = int(raw[0])
        elif name == "timestamp_ms":
            fields["timestamp_ms"] = _new_fw_decode_uint48_le(vendor, off)
        elif name == "timestamp_accuracy":
            fields["timestamp_accuracy"] = int(raw[0])
            fields["timestamp_accuracy_text"] = _new_fw_label(RID_NEW_FW_TS_ACCURACY, raw[0])
    return fields

def _new_fw_coord_rank(coord: dict) -> tuple[int, int]:
    try:
        lat = float(coord.get("lat"))
        lon = float(coord.get("lon"))
        off = int(coord.get("_coord_off") or 0)
    except Exception:
        return (9, 999999)
    # When only one group exists, byte-by-byte fallback can otherwise treat
    # status bytes as a coordinate. Prefer the operating region before offset.
    in_cn_region = 3.0 <= lat <= 55.0 and 70.0 <= lon <= 140.0
    return (0 if in_cn_region else 1, off)

def _new_fw_find_coord_groups(buf: bytes, start: int) -> tuple[dict | None, dict | None]:
    if start < 0 or start + 8 > len(buf):
        return None, None
    max_off = min(len(buf) - 8, start + RID_NEW_FW_COORD_SEARCH_MAX)
    singles: list[dict] = []
    paired: list[tuple[float, int, dict, dict]] = []
    for off in range(start, max_off + 1):
        first = _new_fw_decode_coord_pair(buf, off)
        if not first:
            continue
        second = _new_fw_decode_coord_pair(buf, off + 8)
        if second:
            try:
                dist = _haversine(first["lat"], first["lon"], second["lat"], second["lon"])
            except Exception:
                dist = 1_000_000_000.0
            paired.append((float(dist), off, first, second))
        singles.append(first)
    if paired:
        paired.sort(key=lambda item: (item[0], item[1]))
        return paired[0][2], paired[0][3]
    if singles:
        singles.sort(key=_new_fw_coord_rank)
        return singles[0], None
    return None, None

def _new_fw_decode_lat_lon_pair(buf: bytes, off: int) -> dict | None:
    if off < 0 or off + 8 > len(buf):
        return None
    chunk = bytes(buf[off:off + 8])
    if chunk == b"\xff" * 8:
        return None
    lat_b = chunk[:4]
    lon_b = chunk[4:]
    if _coord_raw_bytes_invalid(lat_b) or _coord_raw_bytes_invalid(lon_b):
        return None
    try:
        lat_raw = struct.unpack_from("<i", buf, off)[0]
        lon_raw = struct.unpack_from("<i", buf, off + 4)[0]
    except Exception:
        return None
    if _coord_raw_invalid(lat_raw) or _coord_raw_invalid(lon_raw):
        return None
    lat = float(lat_raw) * 1e-7
    lon = float(lon_raw) * 1e-7
    if not _coord_pair_valid(lat, lon):
        return None
    return {
        "lat": round(lat, 7),
        "lon": round(lon, 7),
        "_coord_off": off,
    }

def _dji_vendor_parse_note_unknown() -> str:
    return "\u65e0\u6cd5\u89e3\u6790\u5185\u5bb9\uff08\u672a\u77e5\u683c\u5f0f\uff09"

def _dji_vendor_ssid_matches(sn: str, ssid: str | None) -> bool:
    ssid_rid = _new_fw_ssid_rid(ssid)
    return not ssid_rid or not sn or sn == ssid_rid

def parse_dji_gb46750(vendor: bytes, ssid: str | None = None) -> dict | None:
    vendor = bytes(vendor or b"")
    if len(vendor) < RID_DJI_GB46750_MIN:
        return None
    if vendor[0:3] != ODID_OUI or int(vendor[3]) != DJI_RID_VENDOR_TYPE:
        return None
    if vendor[5:11] != RID_DJI_GB46750_HEADER:
        return None

    sn = _new_fw_read_ascii(vendor, 11, 20)
    if not sn or not _dji_vendor_ssid_matches(sn, ssid):
        return None
    reg_mark = _new_fw_read_ascii(vendor, 31, 8)
    pilot_coord = _new_fw_decode_coord_pair(vendor, 42)
    air_coord = _new_fw_decode_coord_pair(vendor, 52)
    track_deg = _new_fw_decode_track_deg(vendor, 60)
    speed = _new_fw_decode_ground_speed(vendor, 62)
    relative_alt = _new_fw_decode_u16_scaled(vendor, 64, 0.5, -9000.0, invalid=0)
    vspeed = _new_fw_decode_vertical_speed(vendor, 66)
    geoid_alt = _new_fw_decode_u16_scaled(vendor, 67, 0.5, -1000.0, invalid=0)
    baro_alt = _new_fw_decode_u16_scaled(vendor, 69, 0.5, -1000.0, invalid=0)
    ts_raw = _new_fw_decode_uint48_le(vendor, 76)
    operation_category = int(vendor[39])
    aircraft_category = int(vendor[40])
    pilot_loc_type = int(vendor[41])
    status = int(vendor[71])
    coord_type = int(vendor[72])

    return {
        "kind": "DJI_GB46750",
        "rid_format": "DJI_GB46750",
        "dji_rid_kind": "DJI_GB46750",
        "ssid": ssid,
        "sn": sn,
        "uas_id": reg_mark,
        "reg_mark": reg_mark,
        "lat": air_coord["lat"] if air_coord else None,
        "lon": air_coord["lon"] if air_coord else None,
        "alt": geoid_alt,
        "baro_alt": baro_alt,
        "relative_alt": relative_alt,
        "speed": speed,
        "vspeed": vspeed,
        "move_dir": track_deg,
        "pilot_lat": pilot_coord["lat"] if pilot_coord else None,
        "pilot_lon": pilot_coord["lon"] if pilot_coord else None,
        "pilot_alt": _new_fw_decode_u16_scaled(vendor, 50, 0.5, -1000.0, invalid=0),
        "pilot_loc_type": pilot_loc_type,
        "pilot_loc_type_text": _new_fw_label(RID_NEW_FW_PILOT_LOC_TYPE, pilot_loc_type),
        "operation_category": operation_category,
        "operation_category_text": _new_fw_label(RID_NEW_FW_OPERATION_CATEGORY, operation_category),
        "aircraft_category": aircraft_category,
        "aircraft_category_text": _new_fw_label(RID_NEW_FW_AIRCRAFT_CATEGORY, aircraft_category),
        "status": status,
        "operation_state": status,
        "operation_state_text": _new_fw_label(RID_NEW_FW_OPERATION_STATE, status),
        "coord_type": coord_type,
        "coord_sys": coord_type,
        "coord_sys_text": _new_fw_label(RID_NEW_FW_COORD_SYS, coord_type),
        "h_acc": int(vendor[73]),
        "v_acc": int(vendor[74]),
        "speed_acc": int(vendor[75]),
        "horizontal_accuracy": int(vendor[73]),
        "vertical_accuracy": int(vendor[74]),
        "speed_accuracy": int(vendor[75]),
        "timestamp_ms": ts_raw,
        "timestamp_acc": int(vendor[82]),
        "timestamp_accuracy": int(vendor[82]),
        "timestamp_accuracy_text": _new_fw_label(RID_NEW_FW_TS_ACCURACY, int(vendor[82])),
        "gb_version": "V1.0",
        "gb_identifiers": vendor[8:11].hex(" "),
        "gb_data_type": int(vendor[5]),
        "gb_version_raw": int(vendor[6]),
        "gb_data_len": int(vendor[7]),
        "dji_dynamic": int(vendor[4]),
        "track_deg": track_deg,
        "ground_speed": speed,
        "vertical_speed": vspeed,
        "alt_relative": relative_alt,
        "alt_geoid": geoid_alt,
        "alt_baro": baro_alt,
        "raw_vendor": vendor.hex(),
    }

def _dji_enterprise_valid_lat_lon(lat, lon) -> bool:
    try:
        lat_f = float(lat)
        lon_f = float(lon)
    except Exception:
        return False
    return -90.0 <= lat_f <= 90.0 and -180.0 <= lon_f <= 180.0

def _decode_dji_enterprise_lat_lon(raw: bytes) -> tuple[float | None, float | None]:
    raw = bytes(raw or b"")
    if len(raw) != 8 or raw == b"\xff" * 8:
        return None, None
    try:
        lat = int.from_bytes(raw[0:4], "little", signed=True) / 1e7
        lon = int.from_bytes(raw[4:8], "little", signed=True) / 1e7
    except Exception:
        return None, None
    if not _dji_enterprise_valid_lat_lon(lat, lon):
        return None, None
    return round(float(lat), 7), round(float(lon), 7)

def _decode_dji_enterprise_alt_candidate(raw: bytes) -> float | None:
    raw = bytes(raw or b"")
    if len(raw) != 2:
        return None
    try:
        value = int.from_bytes(raw, "little", signed=False)
    except Exception:
        return None
    if value == 0:
        return None
    return round(value / 2.0 - 1000.0, 1)

def detect_enterprise_model(sn: str, model_hint: str | None = None) -> str:
    candidates = [str(model_hint or "")]
    model_from_sn = globals().get("_model_from_sn")
    if callable(model_from_sn):
        try:
            candidates.append(str(model_from_sn(sn) or ""))
        except Exception:
            pass
    for text in candidates:
        model = re.sub(r"[^0-9A-Z]+", "", str(text or "").upper())
        if "MINI4K" in model:
            return "MINI_4K"
        if "M350" in model or "MATRICE350" in model:
            return "M350_RTK"
        if "M400" in model or "MATRICE400" in model:
            return "M400"
    return ""

def parse_dji_enterprise_private(
    vendor: bytes,
    ssid: str | None = None,
    model_hint: str | None = None,
) -> dict | None:
    vendor = bytes(vendor or b"")
    if len(vendor) < RID_DJI_ENTERPRISE_PRIVATE_MIN:
        return None
    if vendor[0:3] != ODID_OUI or int(vendor[3]) != DJI_RID_VENDOR_TYPE:
        return None
    if vendor[5:10] != RID_DJI_ENTERPRISE_PRIVATE_HEADER:
        return None

    sn = _new_fw_read_ascii(vendor, 10, 20)
    if not sn or not _dji_vendor_ssid_matches(sn, ssid):
        return None
    pos_a_lat, pos_a_lon = _decode_dji_enterprise_lat_lon(vendor[38:46])
    pos_b_lat, pos_b_lon = _decode_dji_enterprise_lat_lon(vendor[60:68])
    alt_candidates = [
        _decode_dji_enterprise_alt_candidate(vendor[46:48]),
        _decode_dji_enterprise_alt_candidate(vendor[48:50]),
        _decode_dji_enterprise_alt_candidate(vendor[50:52]),
    ]

    model = detect_enterprise_model(sn, model_hint)
    air_lat = air_lon = None
    pilot_lat = pilot_lon = None
    home_lat = home_lon = None
    aux_lat = aux_lon = None

    if model in ("M350_RTK", "MINI_4K"):
        air_lat, air_lon = pos_a_lat, pos_a_lon
        pilot_lat, pilot_lon = pos_b_lat, pos_b_lon
    elif model == "M400":
        air_lat, air_lon = pos_b_lat, pos_b_lon
        home_lat, home_lon = pos_a_lat, pos_a_lon
        aux_lat, aux_lon = pos_a_lat, pos_a_lon

    return {
        "kind": "DJI_ENTERPRISE_PRIVATE",
        "rid_format": "DJI_ENTERPRISE_PRIVATE",
        "dji_rid_kind": "DJI_ENTERPRISE_PRIVATE",
        "ssid": ssid,
        "sn": sn,
        "uas_id": "",
        "lat": air_lat,
        "lon": air_lon,
        "alt": None,
        "speed": None,
        "vspeed": None,
        "move_dir": None,
        "pilot_lat": pilot_lat,
        "pilot_lon": pilot_lon,
        "pilot_alt": None,
        "coord_sys": 0,
        "coord_sys_text": "WGS-84",
        "home_lat": home_lat,
        "home_lon": home_lon,
        "aux_lat": aux_lat,
        "aux_lon": aux_lon,
        "pos_a_lat": pos_a_lat,
        "pos_a_lon": pos_a_lon,
        "pos_b_lat": pos_b_lat,
        "pos_b_lon": pos_b_lon,
        "alt_candidates": alt_candidates,
        "enterprise_model": model,
        "enterprise_dynamic": int(vendor[4]),
        "enterprise_signature": vendor[5:10].hex(),
        "raw_vendor": vendor.hex(),
    }

def parse_dji_vendor(
    vendor: bytes,
    ssid: str | None = None,
    model_hint: str | None = None,
) -> dict | None:
    vendor = bytes(vendor or b"")
    if len(vendor) < RID_DJI_VENDOR_MIN:
        return None
    if vendor[0:3] != ODID_OUI:
        return None
    if int(vendor[3]) != DJI_RID_VENDOR_TYPE:
        return None
    if len(vendor) >= RID_DJI_GB46750_MIN and vendor[5:11] == RID_DJI_GB46750_HEADER:
        return parse_dji_gb46750(vendor, ssid)
    if (
        len(vendor) >= RID_DJI_ENTERPRISE_PRIVATE_MIN
        and vendor[5:10] == RID_DJI_ENTERPRISE_PRIVATE_HEADER
    ):
        return parse_dji_enterprise_private(vendor, ssid, model_hint)
    ssid_rid = _new_fw_ssid_rid(ssid)
    return {
        "kind": "DJI_UNKNOWN_RID",
        "rid_format": "DJI_UNKNOWN_RID",
        "dji_rid_kind": "DJI_UNKNOWN_RID",
        "ssid": ssid,
        "sn": ssid_rid,
        "uas_id": "",
        "parse_note": _dji_vendor_parse_note_unknown(),
        "raw_vendor": vendor.hex(),
    }

def _dji_vendor_parsed_to_decoded(parsed: dict | None) -> dict | None:
    if not isinstance(parsed, dict):
        return None
    sn = str(parsed.get("sn") or "").strip()
    basic = {"uas_id": sn, "id_type": "Serial"} if sn else None
    loc = None
    if any(parsed.get(k) is not None for k in ("lat", "lon", "alt", "speed", "vspeed", "move_dir")):
        loc = {
            "lat": parsed.get("lat"),
            "lon": parsed.get("lon"),
            "alt_geodetic": parsed.get("alt"),
            "alt_relative": parsed.get("relative_alt"),
            "alt_geoid": parsed.get("alt"),
            "alt_baro": parsed.get("baro_alt"),
            "speed_ms": parsed.get("speed"),
            "vspeed_ms": parsed.get("vspeed"),
            "direction_deg": parsed.get("move_dir"),
        }
    system = None
    if parsed.get("pilot_lat") is not None and parsed.get("pilot_lon") is not None:
        system = {
            "pilot_lat": parsed.get("pilot_lat"),
            "pilot_lon": parsed.get("pilot_lon"),
            "pilot_alt": parsed.get("pilot_alt"),
            "pilot_loc_type": parsed.get("pilot_loc_type"),
            "pilot_loc_type_text": str(parsed.get("pilot_loc_type_text") or ""),
        }
    metadata = {}
    for key in (
        "kind", "rid_format", "dji_rid_kind", "parse_note", "raw_vendor",
        "reg_mark", "gb_version", "gb_identifiers", "gb_data_type",
        "gb_version_raw", "gb_data_len", "dji_dynamic",
        "operation_category", "operation_category_text",
        "aircraft_category", "aircraft_category_text",
        "track_deg", "ground_speed", "vertical_speed",
        "relative_alt", "alt_relative", "alt_geoid", "baro_alt", "alt_baro",
        "pilot_alt", "status", "operation_state", "operation_state_text",
        "coord_type", "coord_sys", "coord_sys_text",
        "h_acc", "v_acc", "speed_acc", "horizontal_accuracy",
        "vertical_accuracy", "speed_accuracy", "timestamp_ms",
        "timestamp_acc", "timestamp_accuracy", "timestamp_accuracy_text",
        "home_lat", "home_lon", "aux_lat", "aux_lon",
        "pos_a_lat", "pos_a_lon", "pos_b_lat", "pos_b_lon",
        "alt_candidates", "enterprise_model", "enterprise_dynamic", "enterprise_signature",
    ):
        if key in parsed:
            metadata[key] = parsed.get(key)
    return {
        "basic_id": basic,
        "uas_id": str(parsed.get("uas_id") or ""),
        "location": loc,
        "system": system,
        "metadata": metadata,
    }

def _new_fw_payload_sig(body: bytes) -> int:
    head = bytes(body or b"")[:RID_NEW_FW_SIG_BYTES]
    return zlib.crc32(head) & 0xFFFFFFFF

def decode_new_firmware_payload(
    buf: bytes,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict | None:
    """Decode DJI's newer Beacon vendor body starting at FA:0B:BC:0D.

    This path is intentionally separate from the standard ODID decoder. DJI's
    subtype 0x0d Beacon has multiple incompatible inner layouts, so dispatch
    by the format signature before reading fixed offsets.
    """
    if not buf or len(buf) < RID_DJI_VENDOR_MIN:
        return None
    vendor = bytes(buf)
    parsed = parse_dji_vendor(vendor, ssid_sn, model_hint)
    return _dji_vendor_parsed_to_decoded(parsed)

def _append_new_firmware_result(
    results: list[tuple[bytes, dict]],
    dedup: set[int],
    body: bytes,
    ssid_sn: str | None,
    model_hint: str | None = None,
) -> None:
    decoded = decode_new_firmware_payload(body, ssid_sn=ssid_sn, model_hint=model_hint)
    if not decoded:
        return
    sig = _new_fw_payload_sig(body)
    if sig in dedup:
        return
    dedup.add(sig)
    results.append((body, decoded))

# -----------------------------------------------------------------------------
# IE / NAN extraction (more robust)
# -----------------------------------------------------------------------------
def extract_from_ies(pkt) -> list[bytes]:
    results: list[bytes] = []
    dedup: set[int] = set()
    elt = pkt.getlayer(Dot11Elt)
    while elt and isinstance(elt, Dot11Elt):
        if elt.ID == 221:
            info = bytes(elt.info) if elt.info else b""
            # Standard OUI prefix: 4 bytes (OUI + subtype).
            if len(info) >= 4 and info[:3] == ODID_OUI:
                p = _pick_payload_candidate(info[4:])
                if p:
                    sig = zlib.crc32(p) & 0xFFFFFFFF
                    if sig not in dedup:
                        dedup.add(sig)
                        results.append(p)
            else:
                # Also search OUI inside IE body to cover variant layouts.
                idx = 0
                while True:
                    pos = info.find(ODID_OUI, idx)
                    if pos < 0: break
                    p = _pick_payload_candidate(info[pos+4:])
                    if p:
                        sig = zlib.crc32(p) & 0xFFFFFFFF
                        if sig not in dedup:
                            dedup.add(sig)
                            results.append(p)
                    idx = pos + 1
        try:
            nxt = elt.payload
            if not isinstance(nxt, Dot11Elt): break
            elt = nxt
        except Exception:
            break
    return results

def extract_from_raw(pkt) -> list[bytes]:
    """Search ODID OUI inside raw frame bytes (for NAN/Action frames)."""
    try: raw = bytes(pkt)
    except Exception: return []
    results: list[bytes] = []
    dedup: set[int] = set()
    idx = 0
    while True:
        pos = raw.find(ODID_OUI, idx)
        if pos < 0: break
        p = _pick_payload_candidate(raw[pos+4 : pos+4+2+9*ODID_MSG_SIZE+2])
        if p:
            sig = zlib.crc32(p) & 0xFFFFFFFF
            if sig not in dedup:
                dedup.add(sig)
                results.append(p)
        idx = pos + 1
    return results

def extract_new_firmware_from_ies(
    pkt,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> list[tuple[bytes, dict]]:
    results: list[tuple[bytes, dict]] = []
    dedup: set[int] = set()
    elt = pkt.getlayer(Dot11Elt)
    while elt and isinstance(elt, Dot11Elt):
        if elt.ID == 221:
            info = bytes(elt.info) if elt.info else b""
            idx = 0
            while True:
                pos = info.find(DJI_RID_VENDOR_PREFIX, idx)
                if pos < 0:
                    break
                if pos < len(info):
                    _append_new_firmware_result(results, dedup, info[pos:], ssid_sn, model_hint)
                idx = pos + 1
        try:
            nxt = elt.payload
            if not isinstance(nxt, Dot11Elt):
                break
            elt = nxt
        except Exception:
            break
    return results

def extract_new_firmware_from_raw(
    pkt,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> list[tuple[bytes, dict]]:
    """Search the newer DJI RID vendor-IE body in raw frame bytes."""
    try:
        raw = bytes(pkt)
    except Exception:
        return []
    results: list[tuple[bytes, dict]] = []
    dedup: set[int] = set()
    idx = 0
    while True:
        pos = raw.find(DJI_RID_VENDOR_PREFIX, idx)
        if pos < 0:
            break
        if pos < len(raw):
            _append_new_firmware_result(
                results, dedup, raw[pos:pos + RID_NEW_FW_SIG_BYTES], ssid_sn, model_hint
            )
        idx = pos + 1
    return results

# -----------------------------------------------------------------------------
# State update
# -----------------------------------------------------------------------------
mac_to_basic:   dict[str, dict] = {}
mac_to_ssid_sn: dict[str, dict] = {}

