"""Standalone RID parser core and CLI entrypoint.

The filename intentionally follows the existing user-facing spelling
``analize_core.py``.
"""

from __future__ import annotations

import argparse
import json
import re
import struct
import sys
import zlib
from typing import Any

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


_COMMON_NS: dict[str, Any] | None = None


def _common_namespace() -> dict[str, Any]:
    global _COMMON_NS
    if _COMMON_NS is None:
        ctx = create_runtime_context(
            chunk_files=("common_core.py",),
            module_name="station_edition.light_rid._analize_core_common",
        )
        _COMMON_NS = load_namespace(ctx)
    return _COMMON_NS


def _ensure_common_bindings() -> None:
    if "ODID_OUI" in globals():
        return
    ns = _common_namespace()
    for name in (
        "ODID_OUI",
        "MSG_TYPE_BASIC_ID",
        "MSG_TYPE_LOCATION",
        "MSG_TYPE_SYSTEM",
        "MSG_TYPE_PACK",
        "ODID_MSG_SIZE",
        "ODID_PROTOCOL_MAX",
        "DJI_RID_VENDOR_TYPE",
        "DJI_RID_VENDOR_PREFIX",
        "RID_DJI_VENDOR_MIN",
        "RID_DJI_GB46750_MIN",
        "RID_NEW_FW_SN_LEN",
        "RID_NEW_FW_EXT_MARKER",
        "RID_GB_FF2048_MARKER",
        "RID_DJI_GB46750_HEADER",
        "RID_NEW_FW_SIG_BYTES",
        "ODID_MSG_TYPES_OK",
        "UA_ID_TYPE",
    ):
        globals()[name] = ns[name]


_ensure_common_bindings()


def normalize_parse_mode(mode: str | None) -> str:
    raw = str(mode or "auto").strip().lower().replace("-", "_")
    aliases = {
        "": "auto",
        "default": "auto",
        "auto": "auto",
        "gb": "gb46750_2025",
        "gb46750": "gb46750_2025",
        "dji_gb46750": "gb46750_2025",
        "old": "dji_old_odid",
        "legacy": "dji_old_odid",
        "odid": "dji_old_odid",
        "odid_legacy": "dji_old_odid",
        "dji_old": "dji_old_odid",
        "dji_old_odid": "dji_old_odid",
    }
    raw = aliases.get(raw, raw)
    allowed = {"auto", "gb46750_2025", "dji_old_odid"}
    return raw if raw in allowed else "auto"


def raw_packet_string_to_bytes(raw_packet: str | bytes | bytearray) -> bytes:
    if isinstance(raw_packet, (bytes, bytearray)):
        return bytes(raw_packet)
    text = str(raw_packet or "").strip()
    if not text:
        return b""
    if "..." in text:
        text = text.split("...", 1)[0]
    if text.lower().startswith("hex:"):
        text = text[4:]
    text = text.replace("\\x", " ")
    text = re.sub(r"0x", " ", text, flags=re.IGNORECASE)
    hex_text = re.sub(r"[^0-9A-Fa-f]", "", text)
    if len(hex_text) % 2:
        hex_text = hex_text[:-1]
    if not hex_text:
        return b""
    try:
        return bytes.fromhex(hex_text)
    except ValueError:
        return b""


def decode_basic_id(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE:
        return None
    try:
        if ((msg25[0] >> 4) & 0xF) != MSG_TYPE_BASIC_ID:
            return None
        id_type = msg25[1] & 0x0F
        raw = msg25[2:22].rstrip(b"\x00")
        if not raw:
            return None
        try:
            text = raw.decode("ascii", errors="replace").strip()
        except Exception:
            return None
        if not text or text.count("?") > len(text) // 2:
            return None
        text = "".join(ch if 32 <= ord(ch) <= 126 else "" for ch in text)
        if len(text) < 4:
            return None
        return {"uas_id": text, "id_type": UA_ID_TYPE.get(id_type, f"Unk{id_type}")}
    except Exception:
        return None


def _coord_raw_invalid(raw: int) -> bool:
    try:
        value = int(raw)
    except Exception:
        return True
    return value in (-1, 0x7FFFFFFF, -0x80000000)


def _coord_raw_bytes_invalid(raw: bytes) -> bool:
    data = bytes(raw or b"")
    if len(data) != 4:
        return True
    return data == b"\xff" * 4 or data.count(0xFF) >= 3


def _coord_pair_valid(lat: float, lon: float) -> bool:
    try:
        lat_f = float(lat)
        lon_f = float(lon)
    except Exception:
        return False
    if not (-90.0 <= lat_f <= 90.0 and -180.0 <= lon_f <= 180.0):
        return False
    if abs(lat_f) < 5.0 and abs(lon_f) < 5.0:
        return False
    return True


def decode_location(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE:
        return None
    try:
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
            "alt_geodetic": alt_geo if alt_geo is not None else alt_baro,
            "speed_ms": speed,
            "vspeed_ms": vspeed,
            "direction_deg": None,
        }
    except Exception:
        return None


def _pilot_loc_type_text(value: int | None) -> str:
    mapping = {
        0: "unknown",
        1: "live_gnss",
        2: "takeoff",
        3: "fixed",
    }
    try:
        return mapping.get(int(value), "unknown")
    except Exception:
        return "unknown"


def decode_system(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE:
        return None
    try:
        if ((msg25[0] >> 4) & 0xF) != MSG_TYPE_SYSTEM:
            return None
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


def _decode_odid_pack_layout(payload: bytes) -> tuple[int, int, int] | None:
    if not payload or len(payload) < 2:
        return None
    if len(payload) >= 3 and int(payload[1]) == ODID_MSG_SIZE:
        qty = int(payload[2])
        if 1 <= qty <= 15 and 3 + qty * ODID_MSG_SIZE <= len(payload):
            return (3, ODID_MSG_SIZE, qty)
    qty = int(payload[1])
    if 1 <= qty <= 15 and 2 + qty * ODID_MSG_SIZE <= len(payload):
        return (2, ODID_MSG_SIZE, qty)
    return None


def _valid_msg_header_byte(value: int) -> bool:
    msg_type = (int(value) >> 4) & 0xF
    protocol = int(value) & 0xF
    return (msg_type in ODID_MSG_TYPES_OK) and (0 <= protocol <= ODID_PROTOCOL_MAX)


def _valid_payload(payload: bytes) -> bool:
    if not payload or len(payload) < 1:
        return False
    if RID_NEW_FW_EXT_MARKER in bytes(payload):
        return False
    if not _valid_msg_header_byte(payload[0]):
        return False
    msg_type = (payload[0] >> 4) & 0xF
    if msg_type == MSG_TYPE_PACK:
        layout = _decode_odid_pack_layout(payload)
        if not layout:
            return False
        base, msg_size, qty = layout
        for index in range(qty):
            if not _valid_msg_header_byte(payload[base + index * msg_size]):
                return False
        return True
    return len(payload) >= ODID_MSG_SIZE


def decode_odid(payload: bytes) -> dict:
    result: dict = {"basic_id": None, "location": None, "system": None}
    if not payload:
        return result
    if RID_NEW_FW_EXT_MARKER in bytes(payload):
        return result
    msg_type = (payload[0] >> 4) & 0xF
    if msg_type == MSG_TYPE_PACK:
        layout = _decode_odid_pack_layout(payload)
        if not layout:
            return result
        base, msg_size, qty = layout
        for index in range(qty):
            start = base + index * msg_size
            end = base + (index + 1) * msg_size
            if end > len(payload):
                break
            sub = payload[start:end]
            sub_type = (sub[0] >> 4) & 0xF
            if sub_type == MSG_TYPE_BASIC_ID and not result["basic_id"]:
                result["basic_id"] = decode_basic_id(sub)
            elif sub_type == MSG_TYPE_LOCATION and not result["location"]:
                result["location"] = decode_location(sub)
            elif sub_type == MSG_TYPE_SYSTEM and not result["system"]:
                result["system"] = decode_system(sub)
        return result
    if len(payload) >= ODID_MSG_SIZE:
        msg = payload[:ODID_MSG_SIZE]
        if msg_type == MSG_TYPE_BASIC_ID:
            result["basic_id"] = decode_basic_id(msg)
        elif msg_type == MSG_TYPE_LOCATION:
            result["location"] = decode_location(msg)
        elif msg_type == MSG_TYPE_SYSTEM:
            result["system"] = decode_system(msg)
    return result


def _payload_quality(payload: bytes) -> int:
    if not _valid_payload(payload):
        return -1
    score = 1
    try:
        msg_type = (payload[0] >> 4) & 0xF
        if msg_type == MSG_TYPE_PACK:
            score += 1
        decoded = decode_odid(payload)
        if decoded.get("basic_id"):
            score += 2
        loc = decoded.get("location")
        if isinstance(loc, dict) and loc.get("lat") is not None and loc.get("lon") is not None:
            score += 3
        sys_loc = decoded.get("system")
        if isinstance(sys_loc, dict) and sys_loc.get("pilot_lat") is not None and sys_loc.get("pilot_lon") is not None:
            score += 2
    except Exception:
        pass
    return score


def _pick_payload_candidate(buf: bytes) -> bytes | None:
    if not buf:
        return None
    if RID_NEW_FW_EXT_MARKER in bytes(buf):
        return None
    candidates: list[tuple[int, int, bytes]] = []
    for offset in (1, 0):
        if offset >= len(buf):
            continue
        payload = buf[offset:]
        quality = _payload_quality(payload)
        if quality >= 0:
            candidates.append((quality, offset, payload))
    if not candidates:
        return None
    candidates.sort(reverse=True)
    return candidates[0][2]


def _rid_ascii(raw: bytes) -> str:
    raw_bytes = bytes(raw or b"")
    if not raw_bytes or raw_bytes == b"\xff" * len(raw_bytes):
        return ""
    try:
        text = raw_bytes.decode("ascii", errors="ignore").rstrip("\x00").strip()
    except Exception:
        return ""
    return "".join(ch for ch in text if 32 <= ord(ch) <= 126).strip()


def _new_fw_ssid_rid(ssid_sn: str | None) -> str:
    text = str(ssid_sn or "").strip()
    if len(text) != RID_NEW_FW_SN_LEN:
        return ""
    return text if re.fullmatch(r"[A-Za-z0-9]{20}", text) else ""


def _dji_vendor_ssid_matches(sn: str | None, ssid_sn: str | None) -> bool:
    ssid_rid = _new_fw_ssid_rid(ssid_sn)
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


def _dji_vendor_should_skip_legacy_odid(vendor: bytes) -> bool:
    vendor = bytes(vendor or b"")
    if len(vendor) < RID_DJI_VENDOR_MIN:
        return False
    return RID_GB_FF2048_MARKER in vendor or _rid_vendor_is_gb_candidate(vendor)


def _gb_ff2048_fixed_offset_result(
    vendor: bytes,
    dynamic: int,
    ssid_sn: str | None = None,
    warnings: list[str] | None = None,
) -> dict:
    sn = _rid_ascii(vendor[11:31]) or (ssid_sn or "")
    uas_id = _rid_ascii(vendor[31:39])
    aircraft = _rid_decode_lon_lat_coord(vendor, 42, "aircraft", "gb_ff2048_aircraft")
    operator = _rid_decode_lon_lat_coord(vendor, 52, "operator", "gb_ff2048_operator")
    merged_warnings = list(warnings or [])
    if aircraft is None:
        merged_warnings.append("GB ff2048 aircraft coordinate missing or invalid")
    if operator is None:
        merged_warnings.append("GB ff2048 operator coordinate missing or invalid")
    operator_positions = _rid_dedup_coords([operator] if operator else [])
    raw_coords = _rid_dedup_coords(([aircraft] if aircraft else []) + operator_positions)
    return _rid_result(
        "GB46750_2025",
        "GB_FF2048",
        sn=sn,
        uas_id=uas_id,
        aircraft_position=aircraft,
        operator_positions=operator_positions,
        raw_coords=raw_coords,
        parse_level="strict_fixed_offset",
        warnings=merged_warnings,
        body=vendor,
        extra={
            "raw_vendor": vendor.hex(),
            "gb_header": vendor[5:11].hex(" "),
            "dji_dynamic": dynamic,
            "subtype": dynamic,
            "dynamic_byte": dynamic,
            "marker": RID_GB_FF2048_MARKER.hex(),
        },
    )


def _parse_gb_vendor(vendor: bytes, ssid_sn: str | None = None) -> dict:
    vendor = bytes(vendor or b"")
    if not _rid_vendor_starts(vendor):
        return _rid_unknown(["not a DJI RID vendor payload"], body=vendor)

    if _rid_vendor_is_ff2048(vendor):
        dynamic = int(vendor[4])
        sn = _rid_ascii(vendor[11:31])
        uas_id = _rid_ascii(vendor[31:39])
        warnings: list[str] = []
        if sn and not _dji_vendor_ssid_matches(sn, ssid_sn):
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
                    "subtype": dynamic,
                    "dynamic_byte": dynamic,
                    "marker": RID_GB_FF2048_MARKER.hex(),
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
                    "subtype": dynamic,
                    "dynamic_byte": dynamic,
                    "marker": RID_GB_FF2048_MARKER.hex(),
                },
            )
        return _gb_ff2048_fixed_offset_result(vendor, dynamic, ssid_sn=ssid_sn, warnings=warnings)

    if _rid_vendor_is_odid_like_gb(vendor):
        sn = _rid_ascii(vendor[10:30])
        warnings: list[str] = []
        if sn and not _dji_vendor_ssid_matches(sn, ssid_sn):
            warnings.append("SSID RID does not match GB SN")
        loc = _rid_decode_lat_lon_coord(vendor, 38, "operator", "gb_odid_like_location")
        sys_pos = _rid_decode_lat_lon_coord(vendor, 60, "operator", "gb_odid_like_system")
        operator_positions = _rid_dedup_coords([item for item in (loc, sys_pos) if item])
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
    raw = bytes(data or b"")
    candidates = _find_dji_vendor_payloads(raw)
    if _rid_vendor_starts(raw):
        candidates.insert(0, raw)
    for vendor in candidates:
        if _rid_vendor_is_gb_candidate(vendor):
            return _parse_gb_vendor(vendor, ssid)
    return _rid_unknown(["GB46750_2025 profile not found"], body=raw)


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
    del ssid
    merged: dict = {"basic_id": None, "location": None, "system": None}
    sub_format = ""
    body = bytes(data or b"")
    for payload in _legacy_payload_candidates(body):
        decoded = decode_odid(payload)
        if decoded.get("basic_id") and not merged["basic_id"]:
            merged["basic_id"] = decoded.get("basic_id")
        if decoded.get("location") and not merged["location"]:
            merged["location"] = decoded.get("location")
        if decoded.get("system") and not merged["system"]:
            merged["system"] = decoded.get("system")
        msg_type = (payload[0] >> 4) & 0x0F if payload else -1
        if msg_type == MSG_TYPE_PACK:
            sub_format = "LEGACY_ODID_PACK"
        elif msg_type == MSG_TYPE_BASIC_ID and not sub_format:
            sub_format = "BASIC_ID_ONLY"
        elif not sub_format:
            sub_format = "LEGACY_ODID_FRAGMENT"
    if not any(merged.values()):
        return _rid_unknown(["legacy DJI ODID payload not found"], body=body)

    basic = merged.get("basic_id") if isinstance(merged.get("basic_id"), dict) else {}
    loc = merged.get("location") if isinstance(merged.get("location"), dict) else {}
    sys_loc = merged.get("system") if isinstance(merged.get("system"), dict) else {}
    sn = str(basic.get("uas_id") or "").strip() or None
    aircraft = None
    operator = None
    raw_coords: list[dict] = []
    if loc.get("lat") is not None and loc.get("lon") is not None:
        aircraft = _rid_coord(
            float(loc.get("lat")),
            float(loc.get("lon")),
            role="aircraft",
            source="ODID_LOCATION",
            offset=None,
            alt=loc.get("alt_geodetic"),
        )
        if aircraft:
            raw_coords.append(aircraft)
    if sys_loc.get("pilot_lat") is not None and sys_loc.get("pilot_lon") is not None:
        operator = _rid_coord(
            float(sys_loc.get("pilot_lat")),
            float(sys_loc.get("pilot_lon")),
            role="operator",
            source="ODID_SYSTEM",
            offset=None,
            alt=sys_loc.get("pilot_alt"),
        )
        if operator:
            raw_coords.append(operator)
    operator_positions = _rid_dedup_coords([operator] if operator else [])
    if not sub_format:
        sub_format = "LEGACY_ODID"
    return _rid_result(
        "DJI_OLD_ODID",
        sub_format,
        sn=sn,
        uas_id=None,
        aircraft_position=aircraft,
        operator_positions=operator_positions,
        raw_coords=_rid_dedup_coords(raw_coords),
        parse_level="legacy",
        body=body,
    )


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
    del model_hint
    raw = bytes(data or b"")
    mode_key = normalize_parse_mode(mode)

    if mode_key in ("auto", "gb46750_2025"):
        gb = parse_gb46750_2025(raw, ssid_sn)
        if gb.get("ok") or _has_gb_blocking_marker(raw):
            return gb
        if mode_key == "gb46750_2025":
            return gb
    if mode_key in ("auto", "dji_old_odid"):
        old = parse_legacy_odid_payload(raw, ssid_sn)
        if old.get("ok") or mode_key == "dji_old_odid":
            return old
    return _rid_unknown(["RID payload did not match GB46750_2025 or DJI_OLD_ODID"], body=raw)


def rid_parse_result_to_decoded(result: dict | None) -> dict | None:
    if not isinstance(result, dict) or not result.get("ok"):
        return None
    sn = str(result.get("sn") or "").strip()
    basic = {"uas_id": sn, "id_type": "Serial"} if sn else None
    aircraft = result.get("aircraft_position") if isinstance(result.get("aircraft_position"), dict) else None
    loc = None
    if aircraft:
        loc = {
            "lat": aircraft.get("lat"),
            "lon": aircraft.get("lon"),
            "alt_geodetic": aircraft.get("alt"),
            "speed_ms": None,
            "vspeed_ms": None,
            "direction_deg": None,
        }
    operators = result.get("operator_positions") if isinstance(result.get("operator_positions"), list) else []
    first_op = operators[0] if operators and isinstance(operators[0], dict) else None
    system = None
    if first_op:
        system = {
            "pilot_lat": first_op.get("lat"),
            "pilot_lon": first_op.get("lon"),
            "pilot_alt": first_op.get("alt"),
            "pilot_loc_type": None,
            "pilot_loc_type_text": "operator",
        }
    fmt = str(result.get("format") or "UNKNOWN")
    metadata = {
        "kind": fmt,
        "format": fmt,
        "rid_format": fmt,
        "dji_rid_kind": fmt,
        "sub_format": result.get("sub_format"),
        "parse_level": result.get("parse_level"),
        "coordinate_system": "WGS84",
        "coord_sys": 0,
        "coord_sys_text": "WGS84",
        "warnings": result.get("warnings") or [],
        "operator_positions": operators,
        "raw_coords": result.get("raw_coords") or [],
        "aircraft_position": aircraft,
    }
    for key in ("raw_vendor", "gb_header", "gb_basic_like", "dji_dynamic", "dynamic_byte", "marker"):
        if key in result:
            metadata[key] = result.get(key)
    if result.get("uas_id"):
        metadata["reg_mark"] = result.get("uas_id")
    if aircraft:
        metadata["pos_a_lat"] = aircraft.get("lat")
        metadata["pos_a_lon"] = aircraft.get("lon")
    if first_op:
        metadata["pos_b_lat"] = first_op.get("lat")
        metadata["pos_b_lon"] = first_op.get("lon")
    return {
        "basic_id": basic,
        "uas_id": str(result.get("uas_id") or ""),
        "location": loc,
        "system": system,
        "metadata": metadata,
    }


def parse_dji_gb46750(vendor: bytes, ssid: str | None = None) -> dict | None:
    result = parse_gb46750_2025(bytes(vendor or b""), ssid)
    return result if result.get("ok") else None


def parse_dji_vendor(
    vendor: bytes,
    ssid: str | None = None,
    model_hint: str | None = None,
) -> dict | None:
    result = parse_rid_payload(vendor, mode="gb46750_2025", ssid_sn=ssid, model_hint=model_hint)
    return result if result.get("ok") else None


def _dji_vendor_parsed_to_decoded(parsed: dict | None) -> dict | None:
    return rid_parse_result_to_decoded(parsed)


def _gb_payload_sig(body: bytes) -> int:
    head = bytes(body or b"")[:RID_NEW_FW_SIG_BYTES]
    return zlib.crc32(head) & 0xFFFFFFFF


def decode_gb46750_payload(
    buf: bytes,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict | None:
    result = parse_rid_payload(buf, mode="gb46750_2025", ssid_sn=ssid_sn, model_hint=model_hint)
    return rid_parse_result_to_decoded(result)


def _wrap_success_payload(mode_key: str, result: dict[str, Any], decoded: dict[str, Any]) -> dict[str, Any]:
    fmt = str(result.get("format") or "UNKNOWN")
    firmware_type = "new" if fmt == "GB46750_2025" else ("old" if fmt == "DJI_OLD_ODID" else "")
    payload = {
        "ok": True,
        "mode": mode_key,
        "used_mode": mode_key,
        "firmware_type": firmware_type,
        "format": fmt,
        "body_hex": str(result.get("body_hex") or ""),
        "decoded": decoded,
        "result": result,
    }
    for key in (
        "sub_format",
        "subtype",
        "dynamic_byte",
        "marker",
        "sn",
        "uas_id",
        "aircraft_position",
        "operator_positions",
        "raw_coords",
        "coordinate_system",
        "parse_level",
        "warnings",
    ):
        if key in result:
            payload[key] = result.get(key)
    return payload


def parse_raw_packet(
    raw_packet: str | bytes | bytearray,
    mode: str | None = "auto",
    *,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict[str, Any]:
    mode_key = normalize_parse_mode(mode)
    data = raw_packet_string_to_bytes(raw_packet)
    if not data:
        return {
            "ok": False,
            "error": "raw packet has no usable hex",
            "mode": mode_key,
            "used_mode": mode_key,
            "format": "UNKNOWN",
            "decoded": None,
            "result": {
                "ok": False,
                "format": "UNKNOWN",
                "sub_format": "",
                "sn": None,
                "uas_id": None,
                "aircraft_position": None,
                "operator_positions": [],
                "raw_coords": [],
                "coordinate_system": "WGS84",
                "parse_level": "unknown",
                "warnings": ["raw packet has no usable hex"],
            },
        }

    try:
        result = parse_rid_payload(data, mode_key, ssid_sn=ssid_sn, model_hint=model_hint)
        decoded = rid_parse_result_to_decoded(result)
    except Exception as exc:
        return {
            "ok": False,
            "error": str(exc),
            "mode": mode_key,
            "used_mode": mode_key,
            "format": "UNKNOWN",
            "decoded": None,
        }

    fmt = str(result.get("format") or "UNKNOWN")
    firmware_type = "new" if fmt == "GB46750_2025" else ("old" if fmt == "DJI_OLD_ODID" else "")
    body_hex = str(result.get("body_hex") or data.hex())
    if not result.get("ok") or not isinstance(decoded, dict):
        return {
            "ok": False,
            "error": "raw packet could not be decoded with selected mode",
            "mode": mode_key,
            "used_mode": mode_key,
            "firmware_type": firmware_type,
            "format": fmt,
            "body_hex": body_hex,
            "decoded": None,
            "result": result,
        }

    if body_hex and "body_hex" not in result:
        result = {**result, "body_hex": body_hex}
    return _wrap_success_payload(mode_key, result, decoded)


def parse_raw_packet_string(
    raw_packet: str,
    mode: str | None = "auto",
    *,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict[str, Any]:
    return parse_raw_packet(raw_packet, mode, ssid_sn=ssid_sn, model_hint=model_hint)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Analyze a RID raw packet string.")
    parser.add_argument("raw_packet", help="Raw packet hex string")
    parser.add_argument("--mode", default="auto", help="auto, gb46750_2025, dji_old_odid")
    parser.add_argument("--ssid", default="", help="Optional SSID/SN hint")
    parser.add_argument("--model-hint", default="", help="Optional aircraft model hint")
    args = parser.parse_args(argv)
    payload = parse_raw_packet_string(
        args.raw_packet,
        args.mode,
        ssid_sn=args.ssid or None,
        model_hint=args.model_hint or None,
    )
    json.dump(payload, sys.stdout, ensure_ascii=False, indent=2)
    sys.stdout.write("\n")
    return 0 if payload.get("ok") else 1


if __name__ == "__main__":
    raise SystemExit(main())
