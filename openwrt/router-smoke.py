#!/usr/bin/env python3
"""Read-only target smoke test for the GL-AR750S router adapter."""

from pathlib import Path
import hashlib
import ipaddress
import json
import os
import re
import secrets
import shlex
import shutil
import subprocess
import sys
import time
from threading import Lock, Thread


def main() -> None:
    source = Path(sys.argv[1] if len(sys.argv) > 1 else "/usr/share/light-rid/station_edition/light_rid/router_core.py")
    namespace = {
        "Path": Path,
        "hashlib": hashlib,
        "ipaddress": ipaddress,
        "json": json,
        "os": os,
        "re": re,
        "secrets": secrets,
        "shlex": shlex,
        "shutil": shutil,
        "subprocess": subprocess,
        "sys": sys,
        "time": time,
        "Lock": Lock,
        "Thread": Thread,
        "HTTP_PORT": 4600,
        "current_channel": 0,
    }
    exec(compile(source.read_text(encoding="utf-8"), str(source), "exec"), namespace)
    payload = namespace["_router_status_payload"]()
    config = json.loads(json.dumps(payload.get("config") or {}))
    for section in ("wan", "ap", "repeater", "guest"):
        if isinstance(config.get(section), dict) and "password" in config[section]:
            config[section]["password"] = ""
    _normalized, validation_errors = namespace["_router_validate_config"](config)
    scan_summary = {"tested": False}
    if "--scan" in sys.argv[2:]:
        scan_payload, scan_code = namespace["_router_wifi_scan_payload"]()
        scan_summary = {
            "tested": True,
            "ok": bool(scan_payload.get("ok")),
            "status": scan_code,
            "count": len(scan_payload.get("items") or []),
        }
    summary = {
        "ok": payload.get("ok"),
        "capabilities": payload.get("capabilities"),
        "mode": (payload.get("config") or {}).get("mode"),
        "secret_fields_redacted": all(
            isinstance(value, dict) and set(value) == {"configured", "value"} and value.get("value") == ""
            for value in (
                ((payload.get("config") or {}).get("ap") or {}).get("password"),
                ((payload.get("config") or {}).get("repeater") or {}).get("password"),
                ((payload.get("config") or {}).get("guest") or {}).get("password"),
                ((payload.get("config") or {}).get("wan") or {}).get("password"),
            )
        ),
        "current_config_valid": not validation_errors,
        "validation_errors": validation_errors,
        "wifi_scan": scan_summary,
        "interfaces_up": {
            name: bool(value.get("up"))
            for name, value in (payload.get("runtime") or {}).items()
            if isinstance(value, dict) and "up" in value
        },
    }
    print(json.dumps(summary, ensure_ascii=False, sort_keys=True))
    if not summary["ok"] or not (summary["capabilities"] or {}).get("supported") or not summary["secret_fields_redacted"] or validation_errors or (scan_summary["tested"] and not scan_summary["ok"]):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
