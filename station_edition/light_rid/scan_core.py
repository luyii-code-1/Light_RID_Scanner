from station_edition.light_rid import analize_core as _analize_core


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
    return _analize_core.decode_basic_id(msg25)

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
    return _analize_core.decode_location(msg25)

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
    return _analize_core.decode_system(msg25)

def _decode_odid_pack_layout(p: bytes) -> tuple[int, int, int] | None:
    return _analize_core._decode_odid_pack_layout(p)

def _valid_msg_header_byte(b: int) -> bool:
    return _analize_core._valid_msg_header_byte(b)

def _valid_payload(p: bytes) -> bool:
    return _analize_core._valid_payload(p)

def decode_odid(payload: bytes) -> dict:
    return _analize_core.decode_odid(payload)

def _payload_quality(payload: bytes) -> int:
    return _analize_core._payload_quality(payload)

def _pick_payload_candidate(buf: bytes) -> bytes | None:
    return _analize_core._pick_payload_candidate(buf)

def _rid_ascii(raw: bytes) -> str:
    raw_b = bytes(raw or b"")
    if not raw_b or raw_b == b"\xff" * len(raw_b):
        return ""
    try:
        text = raw_b.decode("ascii", errors="ignore").rstrip("\x00").strip()
    except Exception:
        return ""
    return "".join(ch for ch in text if 32 <= ord(ch) <= 126).strip()

def _new_fw_ssid_rid(ssid_sn: str | None) -> str:
    s = str(ssid_sn or "").strip()
    if len(s) != RID_NEW_FW_SN_LEN:
        return ""
    return s if re.fullmatch(r"[A-Za-z0-9]{20}", s) else ""

def _dji_vendor_ssid_matches(sn: str | None, ssid: str | None) -> bool:
    ssid_rid = _new_fw_ssid_rid(ssid)
    return not ssid_rid or not sn or str(sn) == ssid_rid

def _rid_unknown(
    warnings: list[str] | None = None,
    *,
    body: bytes | None = None,
    sub_format: str = "",
) -> dict:
    return {
        "ok": False,
        "format": "UNKNOWN",
        "sub_format": sub_format,
        "sn": None,
        "uas_id": None,
        "aircraft_position": None,
        "operator_positions": [],
        "raw_coords": [],
        "coordinate_system": "WGS84",
        "parse_level": "unknown",
        "warnings": list(warnings or []),
        "body_hex": bytes(body or b"").hex(),
    }

def _rid_result(
    fmt: str,
    sub_format: str,
    *,
    sn: str | None = None,
    uas_id: str | None = None,
    aircraft_position: dict | None = None,
    operator_positions: list[dict] | None = None,
    raw_coords: list[dict] | None = None,
    parse_level: str,
    warnings: list[str] | None = None,
    body: bytes | None = None,
    extra: dict | None = None,
) -> dict:
    result = {
        "ok": True,
        "format": fmt,
        "sub_format": sub_format,
        "sn": sn or None,
        "uas_id": uas_id if uas_id else None,
        "aircraft_position": aircraft_position,
        "operator_positions": list(operator_positions or []),
        "raw_coords": list(raw_coords or []),
        "coordinate_system": "WGS84",
        "parse_level": parse_level,
        "warnings": list(warnings or []),
        "body_hex": bytes(body or b"").hex(),
    }
    if extra:
        result.update(extra)
    return result

def _rid_coord(
    lat: float,
    lon: float,
    *,
    role: str,
    source: str,
    offset: int | None,
    alt: float | None = None,
) -> dict | None:
    if not _coord_pair_valid(lat, lon):
        return None
    return {
        "lat": round(float(lat), 7),
        "lon": round(float(lon), 7),
        "alt": alt,
        "role": role,
        "source": source,
        "offset": offset,
        "coordinate_system": "WGS84",
    }

def _rid_decode_lon_lat_coord(buf: bytes, off: int, role: str, source: str) -> dict | None:
    if off < 0 or off + 8 > len(buf):
        return None
    raw = bytes(buf[off:off + 8])
    if raw == b"\x00" * 8 or raw == b"\xff" * 8:
        return None
    if _coord_raw_bytes_invalid(raw[:4]) or _coord_raw_bytes_invalid(raw[4:]):
        return None
    try:
        lon_raw = struct.unpack_from("<i", buf, off)[0]
        lat_raw = struct.unpack_from("<i", buf, off + 4)[0]
    except Exception:
        return None
    if _coord_raw_invalid(lon_raw) or _coord_raw_invalid(lat_raw):
        return None
    return _rid_coord(lat_raw * 1e-7, lon_raw * 1e-7, role=role, source=source, offset=off)

def _rid_decode_lat_lon_coord(buf: bytes, off: int, role: str, source: str) -> dict | None:
    if off < 0 or off + 8 > len(buf):
        return None
    raw = bytes(buf[off:off + 8])
    if raw == b"\x00" * 8 or raw == b"\xff" * 8:
        return None
    if _coord_raw_bytes_invalid(raw[:4]) or _coord_raw_bytes_invalid(raw[4:]):
        return None
    try:
        lat_raw = struct.unpack_from("<i", buf, off)[0]
        lon_raw = struct.unpack_from("<i", buf, off + 4)[0]
    except Exception:
        return None
    if _coord_raw_invalid(lat_raw) or _coord_raw_invalid(lon_raw):
        return None
    return _rid_coord(lat_raw * 1e-7, lon_raw * 1e-7, role=role, source=source, offset=off)

def _rid_dedup_coords(items: list[dict]) -> list[dict]:
    out: list[dict] = []
    seen: set[tuple[float, float, str]] = set()
    for item in items:
        if not isinstance(item, dict):
            continue
        try:
            key = (float(item["lat"]), float(item["lon"]), str(item.get("role") or ""))
        except Exception:
            continue
        if key in seen:
            continue
        seen.add(key)
        out.append(item)
    return out

def _rid_vendor_starts(vendor: bytes) -> bool:
    return (
        len(vendor) >= 4
        and vendor[0:3] == ODID_OUI
        and int(vendor[3]) == DJI_RID_VENDOR_TYPE
    )

def _find_dji_vendor_payloads(data: bytes) -> list[bytes]:
    raw = bytes(data or b"")
    out: list[bytes] = []
    seen: set[int] = set()
    idx = 0
    while True:
        pos = raw.find(DJI_RID_VENDOR_PREFIX, idx)
        if pos < 0:
            break
        if pos not in seen:
            seen.add(pos)
            out.append(raw[pos:])
        idx = pos + 1
    if out:
        return out
    idx = 0
    while True:
        pos = raw.find(ODID_OUI, idx)
        if pos < 0:
            break
        if pos + 4 <= len(raw) and int(raw[pos + 3]) == DJI_RID_VENDOR_TYPE and pos not in seen:
            seen.add(pos)
            out.append(raw[pos:])
        idx = pos + 1
    return out

def _rid_vendor_is_ff2048(vendor: bytes) -> bool:
    return _rid_vendor_starts(vendor) and len(vendor) >= 11 and vendor[5:11] == RID_GB_FF2048_MARKER

def _rid_vendor_is_odid_like_gb(vendor: bytes) -> bool:
    return (
        _rid_vendor_starts(vendor)
        and len(vendor) >= RID_DJI_GB46750_MIN
        and int(vendor[4]) == 0x24
        and vendor[5:8] == RID_DJI_GB46750_HEADER
        and ((int(vendor[8]) >> 4) & 0x0F) == MSG_TYPE_BASIC_ID
    )

def _rid_vendor_is_gb_candidate(vendor: bytes) -> bool:
    return _rid_vendor_is_ff2048(vendor) or _rid_vendor_is_odid_like_gb(vendor)

def _dji_vendor_is_gb46750(vendor: bytes) -> bool:
    return _rid_vendor_is_gb_candidate(bytes(vendor or b""))

def _dji_vendor_should_skip_legacy_odid(vendor: bytes) -> bool:
    return _analize_core._dji_vendor_should_skip_legacy_odid(vendor)

def _parse_gb_vendor(vendor: bytes, ssid: str | None = None) -> dict:
    vendor = bytes(vendor or b"")
    if not _rid_vendor_starts(vendor):
        return _rid_unknown(["not a DJI RID vendor payload"], body=vendor)

    if _rid_vendor_is_ff2048(vendor):
        dynamic = int(vendor[4])
        sn = _rid_ascii(vendor[11:31])
        uas_id = _rid_ascii(vendor[31:39])
        warnings: list[str] = []
        if sn and not _dji_vendor_ssid_matches(sn, ssid):
            warnings.append("SSID RID does not match GB SN")
        if dynamic == 0x29:
            aircraft = _rid_decode_lon_lat_coord(vendor, 42, "aircraft", "gb_ff2048_aircraft")
            operator = _rid_decode_lon_lat_coord(vendor, 52, "operator", "gb_ff2048_operator")
            if aircraft is None:
                warnings.append("GB 0x29 aircraft coordinate missing or invalid")
            operator_positions = _rid_dedup_coords([operator] if operator else [])
            raw_coords = _rid_dedup_coords(([aircraft] if aircraft else []) + operator_positions)
            return _rid_result(
                "GB46750_2025",
                "FF2048_EXTENDED_COORD_PAIR",
                sn=sn,
                uas_id=uas_id,
                aircraft_position=aircraft,
                operator_positions=operator_positions,
                raw_coords=raw_coords,
                parse_level="strict",
                warnings=warnings,
                body=vendor,
                extra={
                    "raw_vendor": vendor.hex(),
                    "gb_header": vendor[5:11].hex(" "),
                    "dji_dynamic": dynamic,
                },
            )
        if dynamic == 0x2E:
            operator = _rid_decode_lon_lat_coord(vendor, 42, "operator", "gb_ff2048_operator")
            if operator is None:
                warnings.append("GB 0x2e operator coordinate missing or invalid")
            operator_positions = _rid_dedup_coords([operator] if operator else [])
            return _rid_result(
                "GB46750_2025",
                "FF2048_EXTENDED_SINGLE_OR_OPERATOR_ONLY",
                sn=sn,
                uas_id=uas_id,
                aircraft_position=None,
                operator_positions=operator_positions,
                raw_coords=operator_positions,
                parse_level="strict",
                warnings=warnings,
                body=vendor,
                extra={
                    "raw_vendor": vendor.hex(),
                    "gb_header": vendor[5:11].hex(" "),
                    "dji_dynamic": dynamic,
                },
            )
        return _rid_unknown(
            [f"unsupported GB ff2048 dynamic byte 0x{dynamic:02x}; legacy ODID blocked"],
            body=vendor,
            sub_format="GB_FF2048_UNSUPPORTED",
        )

    if _rid_vendor_is_odid_like_gb(vendor):
        sn = _rid_ascii(vendor[10:30])
        warnings: list[str] = []
        if sn and not _dji_vendor_ssid_matches(sn, ssid):
            warnings.append("SSID RID does not match GB SN")
        loc = _rid_decode_lat_lon_coord(vendor, 38, "operator", "gb_odid_like_location")
        sys_pos = _rid_decode_lat_lon_coord(vendor, 60, "operator", "gb_odid_like_system")
        operator_positions = _rid_dedup_coords([x for x in (loc, sys_pos) if x])
        return _rid_result(
            "GB46750_2025",
            "ODID_LIKE_GB_BUNDLE",
            sn=sn,
            uas_id=None,
            aircraft_position=None,
            operator_positions=operator_positions,
            raw_coords=operator_positions,
            parse_level="strict",
            warnings=warnings,
            body=vendor,
            extra={
                "raw_vendor": vendor.hex(),
                "gb_header": vendor[5:8].hex(" "),
                "gb_basic_like": vendor[8:10].hex(" "),
                "dji_dynamic": int(vendor[4]),
            },
        )

    return _rid_unknown(["not a supported GB46750_2025 profile"], body=vendor)

def parse_gb46750_2025(data: bytes, ssid: str | None = None) -> dict:
    return _analize_core.parse_gb46750_2025(data, ssid)

def _legacy_payload_candidates(data: bytes) -> list[bytes]:
    raw = bytes(data or b"")
    candidates: list[bytes] = []
    seen: set[int] = set()

    def add(payload: bytes | None) -> None:
        if not payload:
            return
        payload = bytes(payload)
        if not _valid_payload(payload):
            return
        sig = zlib.crc32(payload) & 0xFFFFFFFF
        if sig in seen:
            return
        seen.add(sig)
        candidates.append(payload)

    add(raw)
    for vendor in _find_dji_vendor_payloads(raw):
        if _rid_vendor_is_gb_candidate(vendor):
            continue
        pack_pos = vendor.find(b"\xf1\x19\x03", 4)
        if pack_pos >= 0:
            add(vendor[pack_pos:])
        if _rid_vendor_starts(vendor):
            add(_pick_payload_candidate(vendor[4:]))
    return candidates

def parse_legacy_odid_payload(data: bytes, ssid: str | None = None) -> dict:
    return _analize_core.parse_legacy_odid_payload(data, ssid)

def _has_gb_blocking_marker(data: bytes) -> bool:
    raw = bytes(data or b"")
    if RID_GB_FF2048_MARKER in raw:
        return True
    return any(_rid_vendor_is_gb_candidate(vendor) for vendor in _find_dji_vendor_payloads(raw))

def parse_rid_payload(
    data: bytes,
    mode: str | None = "auto",
    *,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict:
    return _analize_core.parse_rid_payload(
        data,
        mode,
        ssid_sn=ssid_sn,
        model_hint=model_hint,
    )

def rid_parse_result_to_decoded(result: dict | None) -> dict | None:
    return _analize_core.rid_parse_result_to_decoded(result)

def parse_dji_gb46750(vendor: bytes, ssid: str | None = None) -> dict | None:
    return _analize_core.parse_dji_gb46750(vendor, ssid)

def parse_dji_vendor(
    vendor: bytes,
    ssid: str | None = None,
    model_hint: str | None = None,
) -> dict | None:
    return _analize_core.parse_dji_vendor(vendor, ssid, model_hint)

def _dji_vendor_parsed_to_decoded(parsed: dict | None) -> dict | None:
    return _analize_core._dji_vendor_parsed_to_decoded(parsed)

def _gb_payload_sig(body: bytes) -> int:
    head = bytes(body or b"")[:RID_NEW_FW_SIG_BYTES]
    return zlib.crc32(head) & 0xFFFFFFFF

def decode_gb46750_payload(
    buf: bytes,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict | None:
    return _analize_core.decode_gb46750_payload(buf, ssid_sn=ssid_sn, model_hint=model_hint)

def _append_gb46750_result(
    results: list[tuple[bytes, dict]],
    dedup: set[int],
    body: bytes,
    ssid_sn: str | None,
    model_hint: str | None = None,
) -> None:
    result = parse_rid_payload(body, mode="gb46750_2025", ssid_sn=ssid_sn, model_hint=model_hint)
    decoded = rid_parse_result_to_decoded(result)
    if not decoded:
        return
    sig = _gb_payload_sig(body)
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
                if _dji_vendor_should_skip_legacy_odid(info):
                    try:
                        nxt = elt.payload
                        if not isinstance(nxt, Dot11Elt): break
                        elt = nxt
                        continue
                    except Exception:
                        break
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
                    if _dji_vendor_should_skip_legacy_odid(info[pos:]):
                        idx = pos + 1
                        continue
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
        if _dji_vendor_should_skip_legacy_odid(raw[pos:pos + RID_NEW_FW_SIG_BYTES]):
            idx = pos + 1
            continue
        p = _pick_payload_candidate(raw[pos+4 : pos+4+2+9*ODID_MSG_SIZE+2])
        if p:
            sig = zlib.crc32(p) & 0xFFFFFFFF
            if sig not in dedup:
                dedup.add(sig)
                results.append(p)
        idx = pos + 1
    return results

def extract_gb46750_from_ies(
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
                    _append_gb46750_result(results, dedup, info[pos:], ssid_sn, model_hint)
                idx = pos + 1
        try:
            nxt = elt.payload
            if not isinstance(nxt, Dot11Elt):
                break
            elt = nxt
        except Exception:
            break
    return results

def extract_gb46750_from_raw(
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
            _append_gb46750_result(
                results, dedup, raw[pos:pos + RID_NEW_FW_SIG_BYTES], ssid_sn, model_hint
            )
        idx = pos + 1
    return results

# -----------------------------------------------------------------------------
# State update
# -----------------------------------------------------------------------------
mac_to_basic:   dict[str, dict] = {}
mac_to_ssid_sn: dict[str, dict] = {}

