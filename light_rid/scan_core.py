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
        ew_direction = (b1 >> 1) & 0x01

        dir_enc = int(msg25[2])
        direction = float(dir_enc + (180 if ew_direction else 0))
        if direction >= 360.0:
            direction -= 360.0

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
            "direction_deg": direction,
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
    s = _new_fw_ascii_printable(raw)
    return s[:RID_NEW_FW_UAS_LEN]

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

def _new_fw_payload_sig(body: bytes) -> int:
    head = bytes(body or b"")[:RID_NEW_FW_SIG_BYTES]
    return zlib.crc32(head) & 0xFFFFFFFF

def decode_new_firmware_payload(buf: bytes, ssid_sn: str | None = None) -> dict | None:
    """Decode DJI's newer Beacon Vendor IE body after FA:0B:BC:0D.

    This path is intentionally separate from the standard ODID decoder. The new
    layout is keyed by the 20-byte RID copied from the SSID, followed by an
    8-byte ASCII UAS ID and little-endian int32 coordinate groups.
    """
    if not buf or len(buf) < RID_NEW_FW_BODY_MIN:
        return None
    ssid_rid = _new_fw_ssid_rid(ssid_sn)
    if not ssid_rid:
        return None
    rid_bytes = ssid_rid.encode("ascii", errors="ignore")
    pos = bytes(buf).find(rid_bytes)
    while pos >= 0:
        rid = _new_fw_read_rid_at(buf, pos)
        if rid == ssid_rid:
            uas_off = pos + RID_NEW_FW_SN_LEN
            if uas_off + RID_NEW_FW_UAS_LEN > len(buf):
                return None
            uas_id = _new_fw_read_uas_id(buf, uas_off)
            coord_start = uas_off + RID_NEW_FW_UAS_LEN
            drone_coord, second_coord = _new_fw_find_coord_groups(buf, coord_start)
            loc = None
            if drone_coord:
                loc = {
                    "lat": drone_coord["lat"],
                    "lon": drone_coord["lon"],
                    "alt_geodetic": None,
                    "speed_ms": None,
                    "vspeed_ms": None,
                    "direction_deg": None,
                }
            system = None
            if second_coord:
                system = {
                    "pilot_lat": second_coord["lat"],
                    "pilot_lon": second_coord["lon"],
                    "pilot_loc_type": None,
                    "pilot_loc_type_text": "new_fw_coord_2",
                }
            return {
                "basic_id": {"uas_id": rid, "id_type": "Serial"},
                "uas_id": uas_id,
                "location": loc,
                "system": system,
            }
        pos = bytes(buf).find(rid_bytes, pos + 1)
    return None

def _append_new_firmware_result(results: list[tuple[bytes, dict]], dedup: set[int], body: bytes, ssid_sn: str | None) -> None:
    decoded = decode_new_firmware_payload(body, ssid_sn=ssid_sn)
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

def extract_new_firmware_from_ies(pkt, ssid_sn: str | None = None) -> list[tuple[bytes, dict]]:
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
                if pos + 4 < len(info):
                    _append_new_firmware_result(results, dedup, info[pos + 4:], ssid_sn)
                idx = pos + 1
        try:
            nxt = elt.payload
            if not isinstance(nxt, Dot11Elt):
                break
            elt = nxt
        except Exception:
            break
    return results

def extract_new_firmware_from_raw(pkt, ssid_sn: str | None = None) -> list[tuple[bytes, dict]]:
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
        if pos + 4 < len(raw):
            _append_new_firmware_result(results, dedup, raw[pos + 4:pos + 4 + RID_NEW_FW_SIG_BYTES], ssid_sn)
        idx = pos + 1
    return results

# -----------------------------------------------------------------------------
# State update
# -----------------------------------------------------------------------------
mac_to_basic:   dict[str, dict] = {}
mac_to_ssid_sn: dict[str, dict] = {}

