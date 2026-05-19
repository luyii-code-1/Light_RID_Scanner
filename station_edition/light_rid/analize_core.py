"""Standalone raw-packet parser entrypoint for RID payload analysis.

The filename intentionally follows the existing user-facing spelling
``analize_core.py``.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from typing import Any

from station_edition.light_rid.runtime import create_runtime_context, load_namespace


_NS: dict[str, Any] | None = None


def _parser_namespace() -> dict[str, Any]:
    global _NS
    if _NS is None:
        ctx = create_runtime_context(
            chunk_files=("common_core.py", "scan_core.py"),
            module_name="station_edition.light_rid._analize_core_runtime",
        )
        _NS = load_namespace(ctx)
    return _NS


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


def parse_raw_packet(
    raw_packet: str | bytes | bytearray,
    mode: str | None = "auto",
    *,
    ssid_sn: str | None = None,
    model_hint: str | None = None,
) -> dict[str, Any]:
    ns = _parser_namespace()
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
        result = ns["parse_rid_payload"](data, mode_key, ssid_sn=ssid_sn, model_hint=model_hint)
        decoded = ns["rid_parse_result_to_decoded"](result)
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

    return {
        "ok": True,
        "mode": mode_key,
        "used_mode": mode_key,
        "firmware_type": firmware_type,
        "format": fmt,
        "body_hex": body_hex,
        "decoded": decoded,
        "result": result,
    }


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
