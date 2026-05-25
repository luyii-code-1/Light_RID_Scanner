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
        "track_samples": [],
        "decoded": None,
        "metadata": {},
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
        "track_samples": [],
        "decoded": None,
        "metadata": {},
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


def _position_timestamp_ms(item: dict | None) -> int | None:
    if not isinstance(item, dict):
        return None
    value = item.get("timestamp_ms")
    try:
        return int(value) if value is not None else None
    except Exception:
        return None


def _track_sample_from_position(
    position: dict | None,
    *,
    sample_type: str,
    track_type: str,
    sn: str | None,
    uas_id: str | None,
) -> dict | None:
    if not isinstance(position, dict):
        return None
    try:
        lat = float(position.get("lat"))
        lon = float(position.get("lon"))
    except Exception:
        return None
    if not _coord_pair_valid(lat, lon):
        return None
    return {
        "sample_type": sample_type,
        "track_type": track_type,
        "sn": sn or None,
        "uas_id": uas_id or None,
        "lat": round(lat, 7),
        "lon": round(lon, 7),
        "alt": position.get("alt"),
        "timestamp_ms": _position_timestamp_ms(position),
        "receive_time_ms": None,
        "source": str(position.get("source") or ""),
        "coordinate_system": str(position.get("coordinate_system") or "WGS84"),
    }


def _build_track_samples(result: dict) -> list[dict]:
    if not isinstance(result, dict):
        return []
    samples: list[dict] = []
    aircraft = _track_sample_from_position(
        result.get("aircraft_position"),
        sample_type="aircraft",
        track_type="aircraft",
        sn=result.get("sn"),
        uas_id=result.get("uas_id"),
    )
    if aircraft:
        samples.append(aircraft)
    operators = result.get("operator_positions") if isinstance(result.get("operator_positions"), list) else []
    for operator in operators:
        sample = _track_sample_from_position(
            operator,
            sample_type="operator",
            track_type="operator",
            sn=result.get("sn"),
            uas_id=result.get("uas_id"),
        )
        if sample:
            samples.append(sample)
    return samples


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



GB46750_ITEM_BITS = (0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02)

GB46750_ITEM_LENGTHS: dict[int, int] = {
    1: 20,   # unique product identification code
    2: 8,    # real-name registration mark
    3: 1,    # UAS operation category
    4: 1,    # UAS classification
    5: 1,    # remote station position type
    6: 8,    # remote station longitude|latitude
    7: 2,    # remote station geodetic altitude
    8: 8,    # unmanned aircraft longitude|latitude
    9: 2,    # track angle
    10: 2,   # ground speed
    11: 2,   # relative altitude
    12: 1,   # vertical speed
    13: 2,   # geodetic altitude
    14: 2,   # barometric altitude
    15: 1,   # operational status
    16: 1,   # coordinate system type
    17: 1,   # horizontal accuracy
    18: 1,   # vertical accuracy
    19: 1,   # speed accuracy
    20: 6,   # timestamp, Unix ms
    21: 1,   # timestamp accuracy
}

GB46750_ITEM_NAMES: dict[int, str] = {
    1: "unique_product_id",
    2: "real_name_registration_mark",
    3: "operation_category",
    4: "aircraft_classification",
    5: "remote_station_position_type",
    6: "remote_station_position",
    7: "remote_station_altitude",
    8: "aircraft_position",
    9: "track_angle",
    10: "ground_speed",
    11: "relative_altitude",
    12: "vertical_speed",
    13: "geodetic_altitude",
    14: "barometric_altitude",
    15: "operational_status",
    16: "coordinate_system_type",
    17: "horizontal_accuracy",
    18: "vertical_accuracy",
    19: "speed_accuracy",
    20: "timestamp",
    21: "timestamp_accuracy",
}

GB46750_OPERATION_CATEGORY_TEXT = {
    0: "undefined",
    1: "open",
    2: "specific",
    3: "certified",
}

GB46750_AIRCRAFT_CLASS_TEXT = {
    0: "micro",
    1: "light",
    2: "small",
    3: "medium",
    4: "large",
}

GB46750_REMOTE_STATION_POSITION_TYPE_TEXT = {
    0: "takeoff_position",
    1: "remote_station_position",
}

GB46750_OPERATIONAL_STATUS_TEXT = {
    0: "not_reported",
    1: "ground",
    2: "airborne",
    3: "emergency",
    4: "rid_failure_non_emergency",
    5: "rid_failure_emergency",
}

GB46750_COORDINATE_SYSTEM_TEXT = {
    0: "WGS84",
    1: "CGCS2000",
}

GB46750_HORIZONTAL_ACCURACY_TEXT = {
    0: ">=18.52km_or_unknown",
    1: "<18.52km",
    2: "<7.41km",
    3: "<3.70km",
    4: "<1852m",
    5: "<926m",
    6: "<556m",
    7: "<185m",
    8: "<92.6m",
    9: "<30m",
    10: "<10m",
    11: "<3m",
    12: "<1m",
}

GB46750_VERTICAL_ACCURACY_TEXT = {
    0: ">=150m_or_unknown",
    1: "<150m",
    2: "<45m",
    3: "<25m",
    4: "<10m",
    5: "<3m",
    6: "<1m",
}

GB46750_SPEED_ACCURACY_TEXT = {
    0: ">=10m/s_or_unknown",
    1: "<10m/s",
    2: "<3m/s",
    3: "<1m/s",
    4: "<0.3m/s",
}

GB46750_TIMESTAMP_ACCURACY_TEXT = {
    0: ">0.5s_or_unknown",
    1: "<=0.5s",
    2: "<=0.4s",
    3: "<=0.3s",
    4: "<=0.2s",
    5: "<=0.1s",
    6: "<=50ms",
    7: "<=20ms",
    8: "<=10ms",
}


def _gb46750_version_text(version_raw: int) -> str:
    try:
        value = int(version_raw) & 0xFF
    except Exception:
        return ""
    major = (value >> 5) & 0x07
    minor = value & 0x1F
    if major == 0:
        return f"raw_0x{value:02x}"
    return f"V{major}.{minor}"


def _gb46750_decode_identifier(packet: bytes) -> tuple[list[int], list[int], int, list[str]]:
    warnings: list[str] = []
    flag_bytes: list[int] = []
    pos = 3
    # GB 46750-2025 defines a 3+N byte data identifier. The low bit
    # is the extension bit, while the upper seven bits select items.
    while pos < len(packet):
        flag = int(packet[pos])
        flag_bytes.append(flag)
        pos += 1
        if len(flag_bytes) >= 3 and (flag & 0x01) == 0:
            break
        if len(flag_bytes) > 32:
            warnings.append("GB46750 data identifier is too long")
            break
    if len(flag_bytes) < 3:
        warnings.append("GB46750 data identifier shorter than 3 bytes")
    present: list[int] = []
    for byte_index, flag in enumerate(flag_bytes):
        for bit_index, bit in enumerate(GB46750_ITEM_BITS):
            if flag & bit:
                present.append(byte_index * 7 + bit_index + 1)
    return flag_bytes, present, pos, warnings


def _gb46750_decode_lon_lat_raw(
    raw: bytes,
    *,
    role: str,
    source: str,
    offset: int | None,
    coordinate_system: str,
) -> dict | None:
    data = bytes(raw or b"")
    if len(data) != 8:
        return None
    if data == b"\x00" * 8 or data == b"\xff" * 8:
        return None
    if _coord_raw_bytes_invalid(data[:4]) or _coord_raw_bytes_invalid(data[4:]):
        return None
    try:
        lon_raw = struct.unpack_from("<i", data, 0)[0]
        lat_raw = struct.unpack_from("<i", data, 4)[0]
    except Exception:
        return None
    if _coord_raw_invalid(lon_raw) or _coord_raw_invalid(lat_raw):
        return None
    coord = _rid_coord(
        lat_raw * 1e-7,
        lon_raw * 1e-7,
        role=role,
        source=source,
        offset=offset,
    )
    if coord is not None:
        coord["coordinate_system"] = coordinate_system
    return coord


def _gb46750_decode_altitude_u16(raw: bytes, *, base_m: float) -> float | None:
    data = bytes(raw or b"")
    if len(data) != 2:
        return None
    try:
        encoded = struct.unpack_from("<H", data, 0)[0]
    except Exception:
        return None
    if encoded == 0:
        return None
    return round(float(encoded) * 0.5 - float(base_m), 1)


def _gb46750_decode_u16_scaled(raw: bytes, *, scale: float, unknown: int = 0xFFFF) -> float | None:
    data = bytes(raw or b"")
    if len(data) != 2:
        return None
    try:
        encoded = struct.unpack_from("<H", data, 0)[0]
    except Exception:
        return None
    if encoded == unknown:
        return None
    return round(float(encoded) * float(scale), 3)


def _gb46750_decode_vertical_speed(raw: bytes) -> float | None:
    data = bytes(raw or b"")
    if len(data) != 1:
        return None
    value = int(data[0])
    if value == 0xFF:
        return None
    sign = -1.0 if (value & 0x80) else 1.0
    magnitude = float(value & 0x7F) * 0.5
    return round(sign * magnitude, 3)


def _gb46750_decode_timestamp(raw: bytes) -> int | None:
    data = bytes(raw or b"")
    if len(data) != 6:
        return None
    value = int.from_bytes(data, "little", signed=False)
    return value or None


def _gb46750_decode_item(item_id: int, raw: bytes, abs_offset: int | None, coordinate_system: str) -> dict:
    raw_bytes = bytes(raw or b"")
    item = {
        "id": item_id,
        "name": GB46750_ITEM_NAMES.get(item_id, f"reserved_{item_id:03d}"),
        "offset": abs_offset,
        "length": len(raw_bytes),
        "raw_hex": raw_bytes.hex(),
    }
    if item_id in (1, 2):
        item["value"] = _rid_ascii(raw_bytes)
    elif item_id in (3, 4, 5, 15, 16, 17, 18, 19, 21):
        value = int(raw_bytes[0]) if raw_bytes else None
        item["value"] = value
        if item_id == 3:
            item["text"] = GB46750_OPERATION_CATEGORY_TEXT.get(value, "reserved")
        elif item_id == 4:
            item["text"] = GB46750_AIRCRAFT_CLASS_TEXT.get(value, "reserved")
        elif item_id == 5:
            item["text"] = GB46750_REMOTE_STATION_POSITION_TYPE_TEXT.get(value, "reserved")
        elif item_id == 15:
            item["text"] = GB46750_OPERATIONAL_STATUS_TEXT.get(value, "reserved")
        elif item_id == 16:
            item["text"] = GB46750_COORDINATE_SYSTEM_TEXT.get(value, "reserved")
        elif item_id == 17:
            item["text"] = GB46750_HORIZONTAL_ACCURACY_TEXT.get(value, "reserved")
        elif item_id == 18:
            item["text"] = GB46750_VERTICAL_ACCURACY_TEXT.get(value, "reserved")
        elif item_id == 19:
            item["text"] = GB46750_SPEED_ACCURACY_TEXT.get(value, "reserved")
        elif item_id == 21:
            item["text"] = GB46750_TIMESTAMP_ACCURACY_TEXT.get(value, "reserved")
    elif item_id == 6:
        item["coord"] = _gb46750_decode_lon_lat_raw(
            raw_bytes,
            role="operator",
            source="GB46750_ITEM006_REMOTE_STATION_POSITION",
            offset=abs_offset,
            coordinate_system=coordinate_system,
        )
    elif item_id == 7:
        item["value_m"] = _gb46750_decode_altitude_u16(raw_bytes, base_m=1000.0)
    elif item_id == 8:
        item["coord"] = _gb46750_decode_lon_lat_raw(
            raw_bytes,
            role="aircraft",
            source="GB46750_ITEM008_AIRCRAFT_POSITION",
            offset=abs_offset,
            coordinate_system=coordinate_system,
        )
    elif item_id == 9:
        item["value_deg"] = _gb46750_decode_u16_scaled(raw_bytes, scale=0.1)
    elif item_id == 10:
        item["value_ms"] = _gb46750_decode_u16_scaled(raw_bytes, scale=0.1)
    elif item_id == 11:
        item["value_m"] = _gb46750_decode_altitude_u16(raw_bytes, base_m=9000.0)
    elif item_id == 12:
        item["value_ms"] = _gb46750_decode_vertical_speed(raw_bytes)
    elif item_id == 13:
        item["value_m"] = _gb46750_decode_altitude_u16(raw_bytes, base_m=1000.0)
    elif item_id == 14:
        item["value_m"] = _gb46750_decode_altitude_u16(raw_bytes, base_m=1000.0)
    elif item_id == 20:
        item["value_ms"] = _gb46750_decode_timestamp(raw_bytes)
    return item


def _gb46750_standard_packet_result(
    vendor: bytes,
    dynamic: int,
    *,
    packet_offset: int,
    ssid_sn: str | None = None,
    warnings: list[str] | None = None,
) -> dict:
    packet = bytes(vendor[packet_offset:])
    merged_warnings = list(warnings or [])
    if len(packet) < 6:
        return _rid_unknown(["GB46750 packet is too short"], body=vendor, sub_format="GB46750_STANDARD_PACKET")

    data_type = int(packet[0])
    version_raw = int(packet[1])
    data_len = int(packet[2])
    flag_bytes, present_ids, content_start, id_warnings = _gb46750_decode_identifier(packet)
    merged_warnings.extend(id_warnings)

    if data_type != 0xFF:
        merged_warnings.append(f"GB46750 data type is 0x{data_type:02x}, expected 0xff")
    if ((version_raw >> 5) & 0x07) != 0x01:
        merged_warnings.append(f"GB46750 version high bits are not 001: 0x{version_raw:02x}")

    content_end = content_start + data_len
    if content_start > len(packet):
        return _rid_unknown(
            merged_warnings + ["GB46750 content offset exceeds packet length"],
            body=vendor,
            sub_format="GB46750_STANDARD_PACKET",
        )
    if content_end > len(packet):
        merged_warnings.append(
            f"GB46750 data content truncated: need {data_len} bytes, have {max(0, len(packet) - content_start)}"
        )
        content_end = len(packet)
    elif content_end < len(packet):
        trailing = len(packet) - content_end
        if trailing:
            merged_warnings.append(f"GB46750 packet has {trailing} trailing byte(s) after declared data content")

    # Decode coordinate-system first, because coordinate items carry that label.
    coord_sys_value = 0
    tmp_pos = 0
    content = packet[content_start:content_end]
    for item_id in present_ids:
        length = GB46750_ITEM_LENGTHS.get(item_id)
        if length is None:
            merged_warnings.append(f"GB46750 item {item_id:03d} is not supported; remaining content cannot be decoded")
            break
        if tmp_pos + length > len(content):
            break
        if item_id == 16:
            coord_sys_value = int(content[tmp_pos]) if length == 1 else 0
            break
        tmp_pos += length
    coordinate_system = GB46750_COORDINATE_SYSTEM_TEXT.get(coord_sys_value, "UNKNOWN")

    items: dict[int, dict] = {}
    content_pos = 0
    for item_id in present_ids:
        length = GB46750_ITEM_LENGTHS.get(item_id)
        if length is None:
            merged_warnings.append(f"GB46750 item {item_id:03d} has no known length; skipped")
            break
        if content_pos + length > len(content):
            merged_warnings.append(
                f"GB46750 item {item_id:03d} truncated: need {length} byte(s), have {max(0, len(content) - content_pos)}"
            )
            break
        raw_item = content[content_pos:content_pos + length]
        abs_offset = packet_offset + content_start + content_pos
        items[item_id] = _gb46750_decode_item(item_id, raw_item, abs_offset, coordinate_system)
        content_pos += length

    if content_pos < len(content):
        merged_warnings.append(f"GB46750 data content has {len(content) - content_pos} undecoded byte(s)")

    sn = str(items.get(1, {}).get("value") or "").strip()
    uas_id = str(items.get(2, {}).get("value") or "").strip()

    if sn and not _dji_vendor_ssid_matches(sn, ssid_sn):
        merged_warnings.append("SSID RID does not match GB unique product ID")
    if not sn and ssid_sn:
        sn = str(ssid_sn or "").strip()

    aircraft = items.get(8, {}).get("coord")
    operator = items.get(6, {}).get("coord")

    remote_alt = items.get(7, {}).get("value_m")
    if isinstance(operator, dict):
        operator["alt"] = remote_alt
        operator["remote_station_alt_m"] = remote_alt
        operator["position_type"] = items.get(5, {}).get("value")
        operator["position_type_text"] = items.get(5, {}).get("text")

    geodetic_alt = items.get(13, {}).get("value_m")
    barometric_alt = items.get(14, {}).get("value_m")
    if isinstance(aircraft, dict):
        aircraft["alt"] = geodetic_alt if geodetic_alt is not None else barometric_alt
        aircraft["alt_geodetic"] = geodetic_alt
        aircraft["alt_baro"] = barometric_alt
        aircraft["relative_alt"] = items.get(11, {}).get("value_m")
        aircraft["speed_ms"] = items.get(10, {}).get("value_ms")
        aircraft["vspeed_ms"] = items.get(12, {}).get("value_ms")
        aircraft["direction_deg"] = items.get(9, {}).get("value_deg")
        aircraft["operational_status"] = items.get(15, {}).get("value")
        aircraft["operational_status_text"] = items.get(15, {}).get("text")
        aircraft["horizontal_accuracy"] = items.get(17, {}).get("value")
        aircraft["horizontal_accuracy_text"] = items.get(17, {}).get("text")
        aircraft["vertical_accuracy"] = items.get(18, {}).get("value")
        aircraft["vertical_accuracy_text"] = items.get(18, {}).get("text")
        aircraft["speed_accuracy"] = items.get(19, {}).get("value")
        aircraft["speed_accuracy_text"] = items.get(19, {}).get("text")
        aircraft["timestamp_ms"] = items.get(20, {}).get("value_ms")
        aircraft["timestamp_accuracy"] = items.get(21, {}).get("value")
        aircraft["timestamp_accuracy_text"] = items.get(21, {}).get("text")

    if aircraft is None and 8 in present_ids:
        merged_warnings.append("GB46750 item 008 aircraft position missing or invalid")
    if operator is None and 6 in present_ids:
        merged_warnings.append("GB46750 item 006 remote station position missing or invalid")

    operator_positions = _rid_dedup_coords([operator] if operator else [])
    raw_coords = _rid_dedup_coords(([aircraft] if aircraft else []) + operator_positions)

    gb_items = {
        f"{item_id:03d}_{GB46750_ITEM_NAMES.get(item_id, 'unknown')}": value
        for item_id, value in sorted(items.items())
    }

    return _rid_result(
        "GB46750_2025",
        "GB46750_STANDARD_PACKET",
        sn=sn,
        uas_id=uas_id,
        aircraft_position=aircraft,
        operator_positions=operator_positions,
        raw_coords=raw_coords,
        parse_level="standard_table_1_3",
        warnings=merged_warnings,
        body=vendor,
        extra={
            "coordinate_system": coordinate_system,
            "raw_vendor": vendor.hex(),
            "gb_header": vendor[5:11].hex(" "),
            "gb_packet_offset": packet_offset,
            "gb_data_type": data_type,
            "gb_version_raw": version_raw,
            "gb_version_text": _gb46750_version_text(version_raw),
            "gb_data_length": data_len,
            "gb_identifier": bytes(flag_bytes).hex(" "),
            "gb_present_items": present_ids,
            "gb_items": gb_items,
            "dji_dynamic": dynamic,
            "dynamic_byte": dynamic,
            "subtype": dynamic,
            "marker": RID_GB_FF2048_MARKER.hex(),
            "operation_category": items.get(3, {}).get("value"),
            "operation_category_text": items.get(3, {}).get("text"),
            "aircraft_classification": items.get(4, {}).get("value"),
            "aircraft_classification_text": items.get(4, {}).get("text"),
            "remote_station_position_type": items.get(5, {}).get("value"),
            "remote_station_position_type_text": items.get(5, {}).get("text"),
            "operational_status": items.get(15, {}).get("value"),
            "operational_status_text": items.get(15, {}).get("text"),
            "coord_sys": coord_sys_value,
            "coord_sys_text": coordinate_system,
        },
    )


def _gb_ff2048_fixed_offset_result(
    vendor: bytes,
    dynamic: int,
    ssid_sn: str | None = None,
    warnings: list[str] | None = None,
) -> dict:
    # Backward-compatible function name. FF2048 packets are GB 46750-2025
    # standard packets beginning at vendor[5], not dynamic-byte-specific
    # proprietary fixed layouts.
    return _gb46750_standard_packet_result(
        bytes(vendor or b""),
        int(dynamic),
        packet_offset=5,
        ssid_sn=ssid_sn,
        warnings=warnings,
    )


def _parse_gb_vendor(vendor: bytes, ssid_sn: str | None = None) -> dict:
    vendor = bytes(vendor or b"")
    if not _rid_vendor_starts(vendor):
        return _rid_unknown(["not a DJI RID vendor payload"], body=vendor)

    if _rid_vendor_is_ff2048(vendor):
        dynamic = int(vendor[4])
        return _gb46750_standard_packet_result(
            vendor,
            dynamic,
            packet_offset=5,
            ssid_sn=ssid_sn,
            warnings=[],
        )

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
            qty = int(vendor[pack_pos + 2]) if pack_pos + 2 < len(vendor) else 0
            pack_len = 3 + max(0, qty) * ODID_MSG_SIZE
            add(vendor[pack_pos:pack_pos + pack_len])
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
            return _enrich_rid_result(gb)
        if mode_key == "gb46750_2025":
            return _enrich_rid_result(gb)
    if mode_key in ("auto", "dji_old_odid"):
        old = parse_legacy_odid_payload(raw, ssid_sn)
        if old.get("ok") or mode_key == "dji_old_odid":
            return _enrich_rid_result(old)
    return _enrich_rid_result(_rid_unknown(["RID payload did not match GB46750_2025 or DJI_OLD_ODID"], body=raw))


def parse_rid_payloads(
    data: bytes,
    mode: str | None = "auto",
    *,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict:
    mode_key = normalize_parse_mode(mode)
    raw = bytes(data or b"")
    packets: list[dict] = []
    track_samples: list[dict] = []
    tracks: dict[str, dict[str, list[dict]]] = {}
    candidates: list[tuple[str, bytes]] = []
    if mode_key in ("auto", "gb46750_2025"):
        if _rid_vendor_starts(raw):
            candidates.append(("gb46750_2025", raw))
        for vendor in _find_dji_vendor_payloads(raw):
            vendor_bytes = bytes(vendor or b"")
            if vendor_bytes and _rid_vendor_is_gb_candidate(vendor_bytes):
                candidates.append(("gb46750_2025", vendor_bytes))
    if mode_key in ("auto", "dji_old_odid"):
        for payload in _legacy_payload_candidates(raw):
            payload_bytes = bytes(payload or b"")
            if payload_bytes:
                candidates.append(("dji_old_odid", payload_bytes))
    for candidate_mode, candidate in candidates:
        parsed = parse_rid_payload(candidate, candidate_mode, ssid_sn=ssid_sn, model_hint=model_hint)
        if not parsed.get("ok"):
            continue
        packets.append(parsed)
        for sample in parsed.get("track_samples") or []:
            if not isinstance(sample, dict):
                continue
            key = str(sample.get("sn") or sample.get("uas_id") or "").strip()
            if not key:
                continue
            track_type = str(sample.get("track_type") or sample.get("sample_type") or "aircraft").strip() or "aircraft"
            store = tracks.setdefault(key, {"aircraft": [], "operator": []})
            if track_type not in store:
                store[track_type] = []
            store[track_type].append(dict(sample))
            track_samples.append(dict(sample))
    return {
        "ok": bool(packets),
        "mode": mode_key,
        "packets": packets,
        "track_samples": track_samples,
        "tracks": tracks,
        "count": len(packets),
        "warnings": [] if packets else ["no RID payload decoded"],
    }


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
            "alt_geodetic": aircraft.get("alt_geodetic", aircraft.get("alt")),
            "alt_baro": aircraft.get("alt_baro"),
            "relative_alt": aircraft.get("relative_alt"),
            "speed_ms": aircraft.get("speed_ms"),
            "vspeed_ms": aircraft.get("vspeed_ms"),
            "direction_deg": aircraft.get("direction_deg"),
            "operational_status": aircraft.get("operational_status"),
            "operational_status_text": aircraft.get("operational_status_text"),
            "horizontal_accuracy": aircraft.get("horizontal_accuracy"),
            "horizontal_accuracy_text": aircraft.get("horizontal_accuracy_text"),
            "vertical_accuracy": aircraft.get("vertical_accuracy"),
            "vertical_accuracy_text": aircraft.get("vertical_accuracy_text"),
            "speed_accuracy": aircraft.get("speed_accuracy"),
            "speed_accuracy_text": aircraft.get("speed_accuracy_text"),
            "timestamp_ms": aircraft.get("timestamp_ms"),
            "timestamp_accuracy": aircraft.get("timestamp_accuracy"),
            "timestamp_accuracy_text": aircraft.get("timestamp_accuracy_text"),
        }
    operators = result.get("operator_positions") if isinstance(result.get("operator_positions"), list) else []
    first_op = operators[0] if operators and isinstance(operators[0], dict) else None
    system = None
    if first_op:
        system = {
            "pilot_lat": first_op.get("lat"),
            "pilot_lon": first_op.get("lon"),
            "pilot_alt": first_op.get("alt"),
            "pilot_loc_type": first_op.get("position_type"),
            "pilot_loc_type_text": first_op.get("position_type_text") or "operator",
        }
    fmt = str(result.get("format") or "UNKNOWN")
    coordinate_system = str(result.get("coordinate_system") or "WGS84")
    metadata = {
        "kind": fmt,
        "format": fmt,
        "rid_format": fmt,
        "dji_rid_kind": fmt,
        "sub_format": result.get("sub_format"),
        "parse_level": result.get("parse_level"),
        "coordinate_system": coordinate_system,
        "coord_sys": result.get("coord_sys", 0 if coordinate_system == "WGS84" else None),
        "coord_sys_text": result.get("coord_sys_text", coordinate_system),
        "warnings": result.get("warnings") or [],
        "operator_positions": operators,
        "raw_coords": result.get("raw_coords") or [],
        "aircraft_position": aircraft,
    }
    for key in (
        "raw_vendor",
        "gb_header",
        "gb_basic_like",
        "gb_packet_offset",
        "gb_data_type",
        "gb_version_raw",
        "gb_version_text",
        "gb_data_length",
        "gb_identifier",
        "gb_present_items",
        "gb_items",
        "dji_dynamic",
        "dynamic_byte",
        "subtype",
        "marker",
        "operation_category",
        "operation_category_text",
        "aircraft_classification",
        "aircraft_classification_text",
        "remote_station_position_type",
        "remote_station_position_type_text",
        "operational_status",
        "operational_status_text",
    ):
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


def _enrich_rid_result(result: dict) -> dict:
    if not isinstance(result, dict):
        return _rid_unknown(["invalid RID parse result"])
    if not result.get("ok"):
        if "track_samples" not in result:
            result["track_samples"] = []
        if "decoded" not in result:
            result["decoded"] = None
        if "metadata" not in result:
            result["metadata"] = {}
        return result
    result["track_samples"] = _build_track_samples(result)
    decoded = rid_parse_result_to_decoded(result)
    result["decoded"] = decoded
    result["metadata"] = decoded.get("metadata") if isinstance(decoded, dict) else {}
    return result


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
        "metadata": decoded.get("metadata") if isinstance(decoded, dict) else {},
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
        "track_samples",
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
                "track_samples": [],
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
