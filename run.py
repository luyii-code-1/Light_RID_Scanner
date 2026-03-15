#!/usr/bin/env python3
"""run.py - OpenDroneID (Remote ID) WiFi monitor/parser (WLAN-only).

Features:
1) More robust parsing: looser BasicID validation and more complete IE/NAN search.
2) Better CJK alignment in TUI without third-party width libraries.
3) `--debug` logs are written into the TUI scan buffer instead of `stderr`.
4) Press `d` to view full scan logs (including raw debug frame info).
5) Table is force-refreshed every 0.5s.

Usage:
  sudo python3 run.py --channel 6 --time 2
  sudo python3 run.py --hop --time 2
  sudo python3 run.py --no-tui --debug
"""

from __future__ import annotations

import argparse
import curses
import json
import logging
import math
import os
import queue
import random
import re
import shlex
import struct
import subprocess
import sys
import time
import urllib.error
import urllib.request
import zlib
from collections import deque
from threading import Lock, Thread

try:
    from scapy.all import Dot11, Dot11Elt, Dot11Beacon, RadioTap, sniff, conf
    conf.verb = 0
except ImportError:
    sys.exit("[FATAL] scapy not installed. Run: pip3 install scapy")

# -----------------------------------------------------------------------------
# 常量
# -----------------------------------------------------------------------------
ODID_OUI             = bytes([0xFA, 0x0B, 0xBC])
MSG_TYPE_BASIC_ID    = 0x0
MSG_TYPE_LOCATION    = 0x1
MSG_TYPE_SYSTEM      = 0x4
MSG_TYPE_PACK        = 0xF
ODID_MSG_SIZE        = 25
ODID_PROTOCOL_MAX    = 2

UA_ID_TYPE = {0:"None", 1:"Serial", 2:"CAA", 3:"UTM", 4:"Session"}

LOC_LAT_LON_MULT = 1e-7
LOC_ALT_OFFSET   = -1000.0
LOC_ALT_MULT     = 0.5
# OpenDroneID WiFi payload follows ODID_*_encoded packed layout (little-endian).
LOC_ENDIAN       = "<"

DEFAULT_PRINT_INTERVAL = 2.0
DEFAULT_MIN_GAP        = 1.0
LOST_TIMEOUT           = 15.0
PURGE_TIMEOUT          = 300.0

CHANNELS_2G         = [1, 6, 11]
CHANNELS_5G         = [36, 40, 44, 48, 149, 153, 157, 161]
# Common 5GHz channels for WiFi fast-transfer scan.
CHANNELS_5G_COMMON  = [36, 40, 44, 48, 52, 56, 60, 64,
                       100, 104, 108, 112, 116, 120, 124, 128,
                       132, 136, 140, 149, 153, 157, 161, 165]
DWELL_2G_DEFAULT    = 250
DWELL_5G_DEFAULT    = 800
SETTLE_DEFAULT      = 30
MAC_BASIC_CACHE_MAX = 1000
ODID_MSG_TYPES_OK   = {0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xF}
HEADING_MIN_MOVE_M  = 2.0
SSID_SN_RE          = re.compile(r"\bRID-([A-Za-z0-9]{4,64})\b")

LOG_BUF_SIZE = 4000   # Log ring buffer size
TUI_REFRESH  = 0.5    # Forced TUI refresh interval (seconds)
CONFIG_FILE_DEFAULT = "rid_config.json"
HISTORY_STORE_DEFAULT = "rid_history_cache.json"
HISTORY_SAVE_INTERVAL = 5.0
OUI_DB_DEFAULT = "oui.txt"
OUI_DB_URL = "https://standards-oui.ieee.org/oui/oui.txt"
AP_LIST_MAX_DEFAULT = 80
AP_STALE_TIMEOUT = 900.0
NOTIFY_REONLINE_COOLDOWN_DEFAULT = 300.0
DJI_LOOKUP_URL_DEFAULT = "https://repair.dji.com/device/search?re=cn&lang=zh-CN"
SNIFF_POLL_TIMEOUT = 20.0
SNIFF_STALL_RECOVER_SEC = 180.0
SNIFF_RECOVER_COOLDOWN_SEC = 45.0
SNIFF_RESTART_AFTER_FAILS = 5
WIFI_FAST_OUI_PREFIX = "0c:9a:e6"
TRACK_MAX_POINTS = 12000
TRACK_MIN_INTERVAL_SEC = 0.8

# -----------------------------------------------------------------------------
# Global runtime state (initialized in `main()`)
# -----------------------------------------------------------------------------
state_table: dict[str, dict] = {}
# Web side history cache: keep all seen drones after live-state purge.
history_table: dict[str, dict] = {}
state_lock = Lock()

log_buf:  deque[str] = deque(maxlen=LOG_BUF_SIZE)   # Normal logs (LOST/INFO/etc.)
scan_buf: deque[str] = deque(maxlen=LOG_BUF_SIZE)   # Full scan logs (with debug frame info)
ap_buf:   deque[str] = deque(maxlen=500)            # AP scan logs (for HTTP page)
ap_seq:   int = 0
ap_table: dict[str, dict] = {}
ap_list_seq: int = 0
ap_lock = Lock()
log_lock = Lock()

HISTORY_STORE_PATH: str | None = None
history_persist_dirty: bool = False
history_persist_last_save_wall: float = 0.0
history_io_lock = Lock()

APP_CONFIG: dict = {}
APP_CONFIG_PATH: str | None = None
APP_CONFIG_PATH_IS_DEFAULT: bool = True
APP_START_CWD: str = os.getcwd()
WEB_CFG: dict = {
    "dji_lookup_url": DJI_LOOKUP_URL_DEFAULT,
    "allow_restart": True,
    "last_restart_args": "",
    "scan_type_rid": "RID报送",
    "scan_type_phone": "手机快传",
    "sn_source_rid": "RID包",
    "sn_source_ssid": "SSID",
    "base_name": "基站",
    "base_lat": None,
    "base_lon": None,
    "base_zoom": 13,
}
AP_CFG: dict = {
    "list_max": AP_LIST_MAX_DEFAULT,
    "vendor_db_file": os.path.join(os.getcwd(), OUI_DB_DEFAULT),
    "vendor_auto_download": True,
}
NOTIFY_CFG: dict = {
    "enabled": False,
    "only_online": True,
    "notify_reonline": True,
    "reonline_cooldown_sec": NOTIFY_REONLINE_COOLDOWN_DEFAULT,
    "skip_mac_only": True,
    "wecom_webhook_key": "",
    "send_timeout_sec": 8,
}
notify_queue: "queue.Queue[dict]" = queue.Queue(maxsize=256)
notify_worker_started = False
notify_worker_lock = Lock()

current_channel: int = 0

_oui_line_re = re.compile(
    r"^\s*([0-9A-Fa-f]{2})-([0-9A-Fa-f]{2})-([0-9A-Fa-f]{2})\s+\(hex\)\s+(.+?)\s*$"
)
oui_db_lock = Lock()
oui_map: dict[str, str] = {}
oui_vendor_cache: dict[str, str] = {}
oui_loaded = False
oui_loading_started = False
oui_last_attempt_wall = 0.0

restart_lock = Lock()
restart_pending = False

sniff_health_lock = Lock()
sniff_last_pkt_mono: float = 0.0
sniff_last_pkt_wall: float = 0.0
sniff_last_recover_wall: float = 0.0
sniff_last_error: str = ""
sniff_last_error_wall: float = 0.0
sniff_iface_name: str = ""

# Runtime parameters (set in `main()`)
PRINT_INTERVAL: float = DEFAULT_PRINT_INTERVAL
MIN_GAP:        float = DEFAULT_MIN_GAP
CHANGE_ON_RSSI: bool  = False
CHANGE_ON_PL:   bool  = False
RSSI_DELTA:     int   = 3
MODEL_MAP:      dict[str, str] = {}
NO_TUI:         bool  = False
DEBUG_MODE:     bool  = False
SCAN_WIFI_FAST: bool  = False
WIFI_FAST_SUPPORTED: bool | None = None
WIFI_FAST_SUPPORT_MSG: str = ""

# -----------------------------------------------------------------------------
# CJK width helpers (without wcwidth dependency)
# -----------------------------------------------------------------------------
def _cw(c: str) -> int:
    """Return display width for one char (CJK=2, others=1)."""
    cp = ord(c)
    if ((0x1100 <= cp <= 0x115F) or (0x2E80 <= cp <= 0x303E) or
        (0x3040 <= cp <= 0x33FF) or (0x3400 <= cp <= 0x4DBF) or
        (0x4E00 <= cp <= 0xA4CF) or (0xAC00 <= cp <= 0xD7FF) or
        (0xF900 <= cp <= 0xFAFF) or (0xFE10 <= cp <= 0xFE1F) or
        (0xFE30 <= cp <= 0xFE6F) or (0xFF01 <= cp <= 0xFF60) or
        (0xFFE0 <= cp <= 0xFFE6)):
        return 2
    return 1

def _sw(s: str) -> int:
    """Return display width for a string."""
    return sum(_cw(c) for c in s)

def _pad(s: str, w: int) -> str:
    """Pad/truncate a string to display width `w` with CJK-safe behavior."""
    out, cur = "", 0
    for c in s:
        cw = _cw(c)
        if cur + cw > w:
            break
        out += c
        cur += cw
    return out + " " * (w - cur)

# -----------------------------------------------------------------------------
# 日志
# -----------------------------------------------------------------------------
def _log(msg: str) -> None:
    ts   = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    with log_lock:
        log_buf.append(line)
        scan_buf.append(line)   # Mirror normal logs into scan stream
    if NO_TUI:
        print(line, flush=True)

def _scan(msg: str) -> None:
    """Write only to scan log buffer (without normal log/print)."""
    ts   = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    with log_lock:
        scan_buf.append(line)

def _history_mark_dirty() -> None:
    global history_persist_dirty
    history_persist_dirty = True

def _fmt_age_compact(sec: float | int | None) -> str:
    if sec is None:
        return "-"
    try:
        s = int(max(0, float(sec)))
    except Exception:
        return "-"
    if s < 60:
        return f"{s}s"
    if s < 3600:
        return f"{s // 60}m"
    if s <= 216000:  # 60h
        return f"{s // 3600}h"
    return f"{s // 86400}d"

def _sanitize_track(raw) -> list[dict]:
    out: list[dict] = []
    if not isinstance(raw, list):
        return out
    for it in raw:
        if not isinstance(it, dict):
            continue
        try:
            lat = float(it.get("lat"))
            lon = float(it.get("lon"))
            ts = float(it.get("ts"))
        except Exception:
            continue
        if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
            continue
        if ts <= 0:
            continue
        out.append({
            "lat": round(lat, 7),
            "lon": round(lon, 7),
            "ts": ts,
        })
    out.sort(key=lambda x: (x.get("ts") or 0.0))
    if len(out) > TRACK_MAX_POINTS:
        out = out[-TRACK_MAX_POINTS:]
    return out

def _track_append_point(entry: dict, lat: float, lon: float, wall_ts: float) -> bool:
    if entry is None:
        return False
    if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
        return False
    tr = _sanitize_track(entry.get("track") or [])
    if tr:
        last = tr[-1]
        try:
            dt = float(wall_ts) - float(last.get("ts") or 0.0)
        except Exception:
            dt = TRACK_MIN_INTERVAL_SEC
        if (abs(float(last.get("lat", 0.0)) - lat) < 1e-7 and
            abs(float(last.get("lon", 0.0)) - lon) < 1e-7):
            if wall_ts > float(last.get("ts") or 0.0):
                last["ts"] = float(wall_ts)
                entry["track"] = tr
                entry["track_updated_wall_ts"] = float(wall_ts)
                return True
            return False
        if dt < TRACK_MIN_INTERVAL_SEC:
            return False
    tr.append({
        "lat": round(float(lat), 7),
        "lon": round(float(lon), 7),
        "ts": float(wall_ts),
    })
    if len(tr) > TRACK_MAX_POINTS:
        tr = tr[-TRACK_MAX_POINTS:]
    entry["track"] = tr
    entry["track_updated_wall_ts"] = float(wall_ts)
    return True

def _history_disk_items_locked() -> list[dict]:
    items: list[dict] = []
    for sn, e in history_table.items():
        if not sn:
            continue
        items.append({
            "sn": sn,
            "src_mac": e.get("src_mac"),
            "id_type": e.get("id_type"),
            "model": e.get("model"),
            "last_ch": e.get("last_ch"),
            "ch_assumed": bool(e.get("ch_assumed")),
            "lat": e.get("lat"),
            "lon": e.get("lon"),
            "alt": e.get("alt"),
            "speed": e.get("speed"),
            "vspeed": e.get("vspeed"),
            "pilot_lat": e.get("pilot_lat"),
            "pilot_lon": e.get("pilot_lon"),
            "pilot_loc_type": e.get("pilot_loc_type"),
            "pilot_loc_type_text": e.get("pilot_loc_type_text"),
            "rssi": e.get("rssi"),
            "move_dir": e.get("move_dir"),
            "ssid": e.get("ssid"),
            "capture_type": e.get("capture_type"),
            "last_capture_wall_ts": e.get("last_capture_wall_ts"),
            "raw_packets": list(e.get("raw_packets") or [])[-3:],
            "scan_type": _scan_type_key(e.get("scan_type")),
            "track": _sanitize_track(e.get("track") or []),
            "track_updated_wall_ts": e.get("track_updated_wall_ts"),
            "first_seen_wall_ts": e.get("first_seen_wall_ts"),
            "last_seen_wall_ts": e.get("last_seen_wall_ts"),
            "pkt_count_total": int(e.get("pkt_count_total") or 0),
            "notify_first_online_sent": bool(e.get("notify_first_online_sent")),
            "notify_last_wall_ts": e.get("notify_last_wall_ts"),
            "last_online_duration_sec": e.get("last_online_duration_sec"),
        })
    items.sort(key=lambda x: (-(x.get("last_seen_wall_ts") or 0.0), x.get("sn") or ""))
    return items

def load_history_store(path: str | None) -> None:
    global history_persist_dirty, history_persist_last_save_wall
    if not path:
        return
    try:
        if not os.path.exists(path):
            return
        with open(path, "r", encoding="utf-8") as f:
            obj = json.load(f)
        items = obj.get("items") if isinstance(obj, dict) else obj
        if not isinstance(items, list):
            _log(f"[WARN] history cache format invalid: {path}")
            return
        loaded = 0
        with state_lock:
            for raw in items:
                if not isinstance(raw, dict):
                    continue
                sn = str(raw.get("sn","") or "").strip()
                if not sn:
                    continue
                h = history_table.get(sn) or {"sn": sn}
                h["sn"] = sn
                for k in HISTORY_DETAIL_KEYS:
                    if k in raw:
                        h[k] = raw.get(k)
                h["scan_type"] = _scan_type_key(h.get("scan_type"))
                h["raw_packets"] = list(h.get("raw_packets") or [])[-3:]
                h["track"] = _sanitize_track(h.get("track") or [])
                h["pkt_count_total"] = max(0, int(raw.get("pkt_count_total") or 0))
                # Monotonic timestamps are process-local; keep them unset until new packets arrive.
                h.setdefault("first_seen_ts", None)
                h.setdefault("last_seen_ts", None)
                history_table[sn] = h
                loaded += 1
            history_persist_dirty = False
            history_persist_last_save_wall = time.time()
        _log(f"[INFO] history cache loaded: {path} ({loaded} items)")
    except Exception as e:
        _log(f"[WARN] history cache load failed: {e}")

def save_history_store(force: bool = False) -> bool:
    global history_persist_dirty, history_persist_last_save_wall
    path = HISTORY_STORE_PATH
    if not path:
        return False
    now_wall = time.time()
    if not force and (not history_persist_dirty or (now_wall - history_persist_last_save_wall) < HISTORY_SAVE_INTERVAL):
        return False
    with history_io_lock:
        now_wall = time.time()
        with state_lock:
            if not force and (not history_persist_dirty or (now_wall - history_persist_last_save_wall) < HISTORY_SAVE_INTERVAL):
                return False
            payload = {
                "version": 2,
                "saved_at": now_wall,
                "items": _history_disk_items_locked(),
            }
            history_persist_dirty = False
        tmp_path = path + ".tmp"
        try:
            parent = os.path.dirname(path)
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(payload, f, ensure_ascii=False, separators=(",", ":"))
            os.replace(tmp_path, path)
            history_persist_last_save_wall = now_wall
            return True
        except Exception:
            with state_lock:
                history_persist_dirty = True
            try:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except Exception:
                pass
            if force:
                _log(f"[WARN] history cache save failed: {path}")
            return False

def history_persist_loop() -> None:
    while True:
        time.sleep(HISTORY_SAVE_INTERVAL)
        try:
            save_history_store(force=False)
        except Exception:
            pass

def clear_history_store(delete_file: bool = True) -> tuple[int, bool]:
    global history_persist_dirty, history_persist_last_save_wall
    path = HISTORY_STORE_PATH
    removed_file = False
    with history_io_lock:
        with state_lock:
            cleared = len(history_table)
            history_table.clear()
            history_persist_dirty = False
            history_persist_last_save_wall = time.time()
        if delete_file and path:
            try:
                if os.path.exists(path):
                    os.remove(path)
                    removed_file = True
            except Exception as e:
                _log(f"[WARN] history cache file delete failed: {e}")
            try:
                tmp_path = path + ".tmp"
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except Exception:
                pass
    _log(f"[INFO] history cache cleared: {cleared}" + (f" (deleted file {path})" if removed_file else ""))
    return cleared, removed_file

def delete_history_item(sn: str) -> bool:
    sn = str(sn or "").strip()
    if not sn:
        return False
    removed = False
    with state_lock:
        if sn in history_table:
            history_table.pop(sn, None)
            removed = True
            _history_mark_dirty()
        if sn in state_table:
            state_table.pop(sn, None)
            removed = True
    return removed

def clear_track_store(sn: str | None = None) -> int:
    """Clear stored trajectory points. Returns affected drone count."""
    affected = 0
    target = str(sn or "").strip()
    with state_lock:
        if target:
            h = history_table.get(target)
            if h is not None and h.get("track"):
                h["track"] = []
                h["track_updated_wall_ts"] = time.time()
                affected += 1
            e = state_table.get(target)
            if e is not None:
                e["track"] = []
                e["track_updated_wall_ts"] = time.time()
            if affected:
                _history_mark_dirty()
            return affected
        for h in history_table.values():
            if h.get("track"):
                h["track"] = []
                h["track_updated_wall_ts"] = time.time()
                affected += 1
        for e in state_table.values():
            e["track"] = []
            e["track_updated_wall_ts"] = time.time()
        if affected:
            _history_mark_dirty()
    return affected

HISTORY_DETAIL_KEYS = (
    "src_mac","id_type","model","last_ch","ch_assumed","lat","lon",
    "alt","speed","vspeed","pilot_lat","pilot_lon","pilot_loc_type","pilot_loc_type_text",
    "rssi","move_dir","ssid",
    "capture_type","last_capture_wall_ts","raw_packets",
    "scan_type","track","track_updated_wall_ts",
    "first_seen_wall_ts","last_seen_wall_ts",
    "notify_first_online_sent","notify_last_wall_ts",
    "last_online_duration_sec",
)

def _history_apply_raw_locked(raw: dict) -> tuple[bool, bool]:
    """Apply one imported history/detail record into `history_table`.
    Must be called with `state_lock` held.
    Returns (applied, is_new).
    """
    if not isinstance(raw, dict):
        return False, False
    sn = str(raw.get("sn", "") or "").strip()
    if not sn:
        return False, False
    old = history_table.get(sn)
    is_new = old is None
    h = dict(old) if isinstance(old, dict) else {"sn": sn}
    h["sn"] = sn
    for k in HISTORY_DETAIL_KEYS:
        if k not in raw:
            continue
        if k == "raw_packets":
            h[k] = list(raw.get(k) or [])[-3:]
        else:
            h[k] = raw.get(k)
    h["scan_type"] = _scan_type_key(h.get("scan_type"))
    h["track"] = _sanitize_track(h.get("track") or [])
    if h.get("track") and h.get("track_updated_wall_ts") is None:
        try:
            h["track_updated_wall_ts"] = float(h["track"][-1].get("ts") or time.time())
        except Exception:
            h["track_updated_wall_ts"] = time.time()
    try:
        h["pkt_count_total"] = max(0, int(raw.get("pkt_count_total", h.get("pkt_count_total", 0)) or 0))
    except Exception:
        h["pkt_count_total"] = max(0, int(h.get("pkt_count_total") or 0))
    # Monotonic timestamps are process-local; keep them unset unless produced at runtime.
    h.setdefault("first_seen_ts", None)
    h.setdefault("last_seen_ts", None)
    history_table[sn] = h
    return True, is_new

def import_details_payload(payload) -> tuple[int, int, int]:
    """Import detail records payload. Returns (added, updated, skipped)."""
    items = None
    if isinstance(payload, dict):
        if isinstance(payload.get("items"), list):
            items = payload.get("items")
        elif isinstance(payload.get("drones"), list):
            items = payload.get("drones")
    elif isinstance(payload, list):
        items = payload
    if not isinstance(items, list):
        return 0, 0, 0
    added = 0
    updated = 0
    skipped = 0
    with state_lock:
        for raw in items:
            if not isinstance(raw, dict):
                skipped += 1
                continue
            if "src_mac" not in raw and "mac" in raw:
                raw = dict(raw)
                raw["src_mac"] = raw.get("mac")
            if "speed" not in raw and "spd" in raw:
                raw = dict(raw)
                raw["speed"] = raw.get("spd")
            if "vspeed" not in raw and "vspd" in raw:
                raw = dict(raw)
                raw["vspeed"] = raw.get("vspd")
            if "move_dir" not in raw and "dir" in raw:
                raw = dict(raw)
                raw["move_dir"] = raw.get("dir")
            ok, is_new = _history_apply_raw_locked(raw)
            if not ok:
                skipped += 1
            elif is_new:
                added += 1
            else:
                updated += 1
        if added or updated:
            _history_mark_dirty()
    return added, updated, skipped

def _deep_merge_dict(base: dict, override: dict) -> dict:
    out = dict(base)
    for k, v in (override or {}).items():
        if isinstance(v, dict) and isinstance(out.get(k), dict):
            out[k] = _deep_merge_dict(out[k], v)
        else:
            out[k] = v
    return out

def default_app_config() -> dict:
    return {
        "basic": {
            "iface": None,
            "channel": None,
            "hop": False,
            "hop_5g": False,
            "scan_wifi_fast": False,
            "dwell_2g": DWELL_2G_DEFAULT,
            "dwell_5g": DWELL_5G_DEFAULT,
            "settle": SETTLE_DEFAULT,
            "dwell_on_hit": 2500,
            "hit_cap": 6000,
            "time": DEFAULT_PRINT_INTERVAL,
            "min_gap": DEFAULT_MIN_GAP,
            "rssi_delta": 3,
            "change_on_rssi": False,
            "change_on_payload": False,
            "model_map": os.path.join(os.getcwd(), "rid_models.json"),
            "history_file": os.path.join(os.getcwd(), HISTORY_STORE_DEFAULT),
            "no_tui": False,
            "debug": False,
        },
        "notify": {
            "enabled": True,
            "only_online": True,
            "notify_reonline": True,
            "reonline_cooldown_sec": int(NOTIFY_REONLINE_COOLDOWN_DEFAULT),
            "skip_mac_only": True,
            "send_timeout_sec": 8,
            "wecom_webhook_key": "",
        },
        "web": {
            "dji_lookup_url": DJI_LOOKUP_URL_DEFAULT,
            "allow_restart": True,
            "last_restart_args": "",
            "scan_type_rid": "RID报送",
            "scan_type_phone": "手机快传",
            "sn_source_rid": "RID包",
            "sn_source_ssid": "SSID",
            "base_name": "基站",
            "base_lat": None,
            "base_lon": None,
            "base_zoom": 13,
        },
        "ap": {
            "list_max": AP_LIST_MAX_DEFAULT,
            "vendor_db_file": os.path.join(os.getcwd(), OUI_DB_DEFAULT),
            "vendor_auto_download": True,
        },
    }

def ensure_config_file(path: str) -> None:
    if not path:
        return
    if os.path.exists(path):
        return
    cfg = default_app_config()
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
    _log(f"[INFO] config file created: {path}")

def load_app_config(path: str | None) -> dict:
    if not path:
        return default_app_config()
    try:
        ensure_config_file(path)
        with open(path, "r", encoding="utf-8") as f:
            raw = json.load(f)
        if not isinstance(raw, dict):
            raise ValueError("root must be object")
        cfg = _deep_merge_dict(default_app_config(), raw)
        _log(f"[INFO] config loaded: {path}")
        return cfg
    except Exception as e:
        _log(f"[WARN] config load failed, using defaults: {e}")
        cfg = default_app_config()
        try:
            if path and os.path.exists(path):
                broken = f"{path}.broken.{time.strftime('%Y%m%d%H%M%S')}"
                os.replace(path, broken)
                _log(f"[WARN] 配置文件已隔离为: {broken}")
            if path:
                ok, msg = save_app_config(path, cfg)
                if ok:
                    _log(f"[INFO] 已写入默认配置: {msg}")
        except Exception as e2:
            _log(f"[WARN] 配置守护写回失败: {e2}")
        return cfg

def save_app_config(path: str | None, cfg: dict) -> tuple[bool, str]:
    if not path:
        return False, "missing config path"
    tmp_path = path + ".tmp"
    try:
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
            f.write("\n")
        os.replace(tmp_path, path)
        return True, path
    except Exception as e:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass
        return False, str(e)

def _parser_explicit_dests(parser: argparse.ArgumentParser, argv: list[str]) -> set[str]:
    explicit: set[str] = set()
    opt_to_dest: dict[str, str] = {}
    for act in parser._actions:
        if not getattr(act, "option_strings", None):
            continue
        for opt in act.option_strings:
            opt_to_dest[opt] = act.dest
    for tok in argv:
        if not tok.startswith("-"):
            continue
        key = tok.split("=", 1)[0]
        dest = opt_to_dest.get(key)
        if dest and dest != "help":
            explicit.add(dest)
    return explicit

def _to_bool(v, default: bool = False) -> bool:
    if isinstance(v, bool):
        return v
    if v is None:
        return default
    if isinstance(v, (int, float)):
        return bool(v)
    s = str(v).strip().lower()
    if s in ("1", "true", "yes", "y", "on", "t"):
        return True
    if s in ("0", "false", "no", "n", "off", "f", ""):
        return False
    return default

def apply_config_to_args(parser: argparse.ArgumentParser, args, cfg: dict) -> None:
    basic = cfg.get("basic") if isinstance(cfg, dict) else {}
    if not isinstance(basic, dict):
        return
    explicit = _parser_explicit_dests(parser, sys.argv[1:])
    for dest in (
        "iface", "channel", "hop", "hop_5g", "scan_wifi_fast",
        "dwell_2g", "dwell_5g", "settle", "dwell_on_hit", "hit_cap",
        "time", "min_gap", "rssi_delta",
        "change_on_rssi", "change_on_payload",
        "model_map", "history_file",
        "no_tui", "debug",
    ):
        if dest in explicit:
            continue
        if dest in basic:
            raw_v = basic.get(dest)
            cur_v = getattr(args, dest, None)
            try:
                if isinstance(cur_v, bool):
                    v = _to_bool(raw_v, cur_v)
                elif isinstance(cur_v, int) and not isinstance(cur_v, bool):
                    v = int(raw_v)
                elif isinstance(cur_v, float):
                    v = float(raw_v)
                elif raw_v is None:
                    v = None
                else:
                    v = str(raw_v)
                setattr(args, dest, v)
            except Exception:
                # Guard mode: ignore invalid config value and keep parser default.
                continue

def _normalize_notify_cfg(cfg: dict | None) -> dict:
    base = dict(NOTIFY_CFG)
    if isinstance(cfg, dict):
        notify = cfg.get("notify")
        if isinstance(notify, dict):
            for k in base.keys():
                if k in notify:
                    base[k] = notify.get(k)
    try:
        base["send_timeout_sec"] = max(2, int(base.get("send_timeout_sec") or 8))
    except Exception:
        base["send_timeout_sec"] = 8
    try:
        base["reonline_cooldown_sec"] = max(0, int(base.get("reonline_cooldown_sec") or NOTIFY_REONLINE_COOLDOWN_DEFAULT))
    except Exception:
        base["reonline_cooldown_sec"] = int(NOTIFY_REONLINE_COOLDOWN_DEFAULT)
    base["enabled"] = bool(base.get("enabled"))
    base["only_online"] = bool(base.get("only_online", True))
    base["notify_reonline"] = bool(base.get("notify_reonline", True))
    base["skip_mac_only"] = bool(base.get("skip_mac_only", True))
    base["wecom_webhook_key"] = str(base.get("wecom_webhook_key") or "").strip()
    return base

def _normalize_web_cfg(cfg: dict | None) -> dict:
    base = dict(WEB_CFG)
    if isinstance(cfg, dict):
        web = cfg.get("web")
        if isinstance(web, dict):
            for k in base.keys():
                if k in web:
                    base[k] = web.get(k)
    base["dji_lookup_url"] = str(base.get("dji_lookup_url") or DJI_LOOKUP_URL_DEFAULT).strip()
    base["allow_restart"] = bool(base.get("allow_restart", True))
    base["last_restart_args"] = str(base.get("last_restart_args") or "")
    base["scan_type_rid"] = str(base.get("scan_type_rid") or "RID报送").strip() or "RID报送"
    base["scan_type_phone"] = str(base.get("scan_type_phone") or "手机快传").strip() or "手机快传"
    base["sn_source_rid"] = str(base.get("sn_source_rid") or "RID包").strip() or "RID包"
    base["sn_source_ssid"] = str(base.get("sn_source_ssid") or "SSID").strip() or "SSID"
    base["base_name"] = str(base.get("base_name") or "基站").strip() or "基站"
    try:
        lat_raw = base.get("base_lat")
        base["base_lat"] = None if lat_raw in (None, "") else float(lat_raw)
        if base["base_lat"] is not None and not (-90.0 <= base["base_lat"] <= 90.0):
            base["base_lat"] = None
    except Exception:
        base["base_lat"] = None
    try:
        lon_raw = base.get("base_lon")
        base["base_lon"] = None if lon_raw in (None, "") else float(lon_raw)
        if base["base_lon"] is not None and not (-180.0 <= base["base_lon"] <= 180.0):
            base["base_lon"] = None
    except Exception:
        base["base_lon"] = None
    try:
        base_zoom = int(base.get("base_zoom") if base.get("base_zoom") is not None else 13)
    except Exception:
        base_zoom = 13
    base["base_zoom"] = max(3, min(19, base_zoom))
    return base

def _normalize_ap_cfg(cfg: dict | None) -> dict:
    base = dict(AP_CFG)
    if isinstance(cfg, dict):
        ap = cfg.get("ap")
        if isinstance(ap, dict):
            for k in base.keys():
                if k in ap:
                    base[k] = ap.get(k)
    try:
        base["list_max"] = max(10, min(500, int(base.get("list_max") or AP_LIST_MAX_DEFAULT)))
    except Exception:
        base["list_max"] = AP_LIST_MAX_DEFAULT
    base["vendor_auto_download"] = bool(base.get("vendor_auto_download", True))
    db_path = str(base.get("vendor_db_file") or os.path.join(os.getcwd(), OUI_DB_DEFAULT)).strip()
    base["vendor_db_file"] = os.path.abspath(db_path) if db_path else None
    return base

def init_web_from_config(cfg: dict | None) -> None:
    global WEB_CFG
    WEB_CFG = _normalize_web_cfg(cfg)

def _scan_type_key(v: str | None) -> str:
    s = str(v or "").strip()
    low = s.lower()
    if not s:
        return "rid"
    if low in ("rid", "rid_report", "rid_reporting", "rid_reporting_type"):
        return "rid"
    if low in ("phone", "phone_fast", "mobile", "mobile_fast"):
        return "phone"
    if "RID" in s or "rid" in low or "报送" in s:
        return "rid"
    if "手机" in s or "快传" in s:
        return "phone"
    return s

def _scan_type_display(v: str | None) -> str:
    key = _scan_type_key(v)
    if key == "phone":
        return str(WEB_CFG.get("scan_type_phone") or "手机快传")
    if key == "rid":
        return str(WEB_CFG.get("scan_type_rid") or "RID报送")
    return key

def _sn_source_display(id_type: str | None) -> str:
    if str(id_type or "").strip().upper() == "SSID":
        return str(WEB_CFG.get("sn_source_ssid") or "SSID")
    return str(WEB_CFG.get("sn_source_rid") or "RID包")

def init_ap_from_config(cfg: dict | None) -> None:
    global AP_CFG
    AP_CFG = _normalize_ap_cfg(cfg)

def init_notify_from_config(cfg: dict | None) -> None:
    global NOTIFY_CFG
    NOTIFY_CFG = _normalize_notify_cfg(cfg)
    key = NOTIFY_CFG.get("wecom_webhook_key") or ""
    if NOTIFY_CFG.get("enabled") and key:
        _log("[INFO] WeCom robot notification enabled (online-only)")
    else:
        _log("[INFO] notify disabled (missing key or disabled)")

def reload_runtime_config(cfg: dict | None) -> tuple[bool, str]:
    global APP_CONFIG, PRINT_INTERVAL, MIN_GAP, CHANGE_ON_RSSI, CHANGE_ON_PL, RSSI_DELTA, DEBUG_MODE
    if not isinstance(cfg, dict):
        return False, "invalid config root"
    APP_CONFIG = _deep_merge_dict(default_app_config(), cfg)
    init_web_from_config(APP_CONFIG)
    init_ap_from_config(APP_CONFIG)
    init_notify_from_config(APP_CONFIG)

    basic = APP_CONFIG.get("basic")
    if not isinstance(basic, dict):
        basic = {}
    try:
        PRINT_INTERVAL = max(0.2, float(basic.get("time", PRINT_INTERVAL)))
    except Exception:
        pass
    try:
        MIN_GAP = max(0.0, float(basic.get("min_gap", MIN_GAP)))
    except Exception:
        pass
    try:
        RSSI_DELTA = max(1, int(basic.get("rssi_delta", RSSI_DELTA)))
    except Exception:
        pass
    CHANGE_ON_RSSI = bool(basic.get("change_on_rssi", CHANGE_ON_RSSI))
    CHANGE_ON_PL = bool(basic.get("change_on_payload", CHANGE_ON_PL))
    DEBUG_MODE = bool(basic.get("debug", DEBUG_MODE))
    try:
        root_logger = logging.getLogger()
        root_logger.setLevel(logging.DEBUG if DEBUG_MODE else logging.WARNING)
    except Exception:
        pass
    return True, "runtime config reloaded"

def _wecom_webhook_url(key: str) -> str:
    return f"https://qyapi.weixin.qq.com/cgi-bin/webhook/send?key={key}"

def _wecom_send_text(key: str, content: str, timeout_sec: int = 8) -> tuple[bool, str]:
    body = json.dumps({
        "msgtype": "text",
        "text": {"content": content},
    }, ensure_ascii=False).encode("utf-8")
    req = urllib.request.Request(
        _wecom_webhook_url(key),
        data=body,
        headers={"Content-Type": "application/json; charset=utf-8"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout_sec) as resp:
            raw = (resp.read() or b"").decode("utf-8", errors="replace")
    except urllib.error.URLError as e:
        return False, f"network error: {e}"
    except Exception as e:
        return False, f"send error: {e}"
    try:
        obj = json.loads(raw) if raw else {}
    except Exception:
        obj = {}
    if isinstance(obj, dict) and int(obj.get("errcode", -1)) == 0:
        return True, raw or "ok"
    return False, raw or "unknown response"

def _notify_queue_put(item: dict) -> None:
    try:
        notify_queue.put_nowait(item)
    except queue.Full:
        _log("[WARN] notification queue full, dropping one message")

def _notify_online_text(e: dict, event_title: str, now_wall: float) -> str:
    def _f(v, fmt_str: str, unit: str = "N/A") -> str:
        if v is None:
            return "N/A"
        try:
            return f"{v:{fmt_str}}{unit if unit != 'N/A' else ''}"
        except Exception:
            return str(v)
    sn = str(e.get("sn",""))
    model = str(e.get("model","N/A"))
    it = str(e.get("id_type",""))
    mac = str(e.get("src_mac",""))
    ch = e.get("last_ch") or 0
    ch_s = f"{'~' if e.get('ch_assumed') else ''}ch{ch}" if ch else "ch?"
    rssi = _f(e.get("rssi"), "d", "dBm")
    lat = e.get("lat")
    lon = e.get("lon")
    loc_s = f"{lat:.6f}, {lon:.6f}" if lat is not None and lon is not None else "N/A"
    alt_s = _f(e.get("alt"), ".1f", "m")
    spd_s = _f(e.get("speed"), ".1f", "m/s")
    vsp_s = _f(e.get("vspeed"), ".1f", "m/s")
    pkts = int(e.get("pkt_count") or 0)
    ts_s = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now_wall))
    return (
        f"[RID{event_title}] {ts_s}\n"
        f"SN: {sn}\n"
        f"机型/ID: {model} / {it}\n"
        f"MAC/信道/信号: {mac} / {ch_s} / {rssi}\n"
        f"位置: {loc_s}  高程: {alt_s}\n"
        f"速度: {spd_s}  垂速: {vsp_s}  包数: {pkts}"
    )

def _notify_worker_loop() -> None:
    while True:
        item = notify_queue.get()
        try:
            if not isinstance(item, dict):
                continue
            if item.get("type") != "wecom_text":
                continue
            key = str(item.get("key") or "")
            content = str(item.get("content") or "")
            if not key or not content:
                continue
            ok, resp = _wecom_send_text(key, content, timeout_sec=int(item.get("timeout_sec") or 8))
            if not ok:
                _log(f"[WARN] WeCom notification send failed: {resp}")
        except Exception as e:
            _log(f"[WARN] 通知线程异常: {e}")
        finally:
            try:
                notify_queue.task_done()
            except Exception:
                pass

def start_notify_worker() -> None:
    global notify_worker_started
    with notify_worker_lock:
        if notify_worker_started:
            return
        Thread(target=_notify_worker_loop, daemon=True).start()
        notify_worker_started = True

def queue_online_notification(e: dict, event_title: str, now_wall: float | None = None) -> bool:
    if not NOTIFY_CFG.get("enabled"):
        return False
    key = str(NOTIFY_CFG.get("wecom_webhook_key") or "").strip()
    if not key:
        return False
    now_wall = float(now_wall or time.time())
    content = _notify_online_text(e, event_title, now_wall)
    _notify_queue_put({
        "type": "wecom_text",
        "key": key,
        "content": content,
        "timeout_sec": int(NOTIFY_CFG.get("send_timeout_sec") or 8),
    })
    return True

def send_test_notification_from_config() -> tuple[bool, str]:
    if not NOTIFY_CFG.get("enabled"):
        return False, "notify disabled"
    key = str(NOTIFY_CFG.get("wecom_webhook_key") or "").strip()
    if not key:
        return False, "missing wecom_webhook_key"
    now_wall = time.time()
    test_e = {
        "sn": "TEST-RID-ONLINE",
        "model": "Config/Test",
        "id_type": "Test",
        "src_mac": "00:11:22:33:44:55",
        "last_ch": current_channel or 6,
        "ch_assumed": True,
        "rssi": -45,
        "lat": None,
        "lon": None,
        "alt": None,
        "speed": None,
        "vspeed": None,
        "pkt_count": 1,
    }
    return _wecom_send_text(
        key,
        _notify_online_text(test_e, "上线(测试)", now_wall),
        timeout_sec=int(NOTIFY_CFG.get("send_timeout_sec") or 8),
    )

def _mac_oui_key(mac: str | None) -> str:
    if not mac:
        return ""
    h = "".join(ch for ch in str(mac) if ch in "0123456789abcdefABCDEF")
    if len(h) < 6:
        return ""
    return h[:6].upper()

def _mac_hex12(mac: str | None) -> str:
    if not mac:
        return ""
    h = "".join(ch for ch in str(mac) if ch in "0123456789abcdefABCDEF").lower()
    if len(h) < 12:
        return ""
    return h[:12]

def _is_wifi_fast_mac(mac: str | None) -> bool:
    return _mac_oui_key(mac).lower() == WIFI_FAST_OUI_PREFIX.replace(":", "").lower()

def _wifi_fast_sn(mac: str | None) -> str:
    h12 = _mac_hex12(mac).upper()
    if not h12:
        return "WIFIFAST000000000000"
    return f"WIFIFAST{h12}"

def _hex_preview(data: bytes | None, max_bytes: int = 220) -> str:
    if not data:
        return ""
    b = bytes(data)
    if len(b) <= max_bytes:
        return b.hex(" ")
    head = b[:max_bytes].hex(" ")
    return f"{head} ...( +{len(b) - max_bytes}B )"

def _ap_vendor_type(vendor: str, ssid: str | None) -> str:
    v = (vendor or "").lower()
    s = (ssid or "").strip()
    if s.startswith("RID-") or "dji" in v:
        return "DJI/RID"
    if any(k in v for k in ("apple", "samsung", "huawei", "honor", "xiaomi", "oppo", "vivo", "google")):
        return "\u624b\u673a/\u70ed\u70b9"
    if any(k in v for k in ("tp-link", "h3c", "ruijie", "ubiquiti", "mikrotik", "netgear", "asus", "cisco", "tenda", "meraki")):
        return "\u8def\u7531/AP"
    if s.startswith("DIRECT-"):
        return "\u76f4\u8fde/Wi-Fi"
    return "AP"

def _parse_oui_text(raw: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for line in raw.splitlines():
        m = _oui_line_re.match(line)
        if not m:
            continue
        key = (m.group(1) + m.group(2) + m.group(3)).upper()
        vendor = m.group(4).strip()
        if key and vendor:
            out[key] = vendor
    return out

def _load_oui_map_from_file(path: str | None) -> dict[str, str]:
    if not path or not os.path.exists(path):
        return {}
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        raw = f.read()
    return _parse_oui_text(raw)

def _download_oui_db(path: str) -> tuple[bool, str]:
    req = urllib.request.Request(
        OUI_DB_URL,
        headers={"User-Agent": "RIDMonitor/1.0 (+OUI cache)"},
        method="GET",
    )
    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            data = resp.read()
    except Exception as e:
        return False, str(e)
    if not data:
        return False, "empty response"
    tmp_path = path + ".tmp"
    try:
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        with open(tmp_path, "wb") as f:
            f.write(data)
        os.replace(tmp_path, path)
        return True, path
    except Exception as e:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass
        return False, str(e)

def _oui_load_worker() -> None:
    global oui_loaded, oui_loading_started, oui_last_attempt_wall, oui_map, ap_list_seq
    path = AP_CFG.get("vendor_db_file")
    loaded_map: dict[str, str] = {}
    try:
        with oui_db_lock:
            oui_last_attempt_wall = time.time()
        loaded_map = _load_oui_map_from_file(path)
        if not loaded_map and bool(AP_CFG.get("vendor_auto_download", True)) and path:
            ok, info = _download_oui_db(path)
            if ok:
                _log(f"[INFO] OUI 数据库已下载: {info}")
                loaded_map = _load_oui_map_from_file(path)
            else:
                _log(f"[WARN] OUI database download failed: {info}")
        if loaded_map:
            with oui_db_lock:
                oui_map = loaded_map
                oui_loaded = True
                oui_vendor_cache.clear()
            with ap_lock:
                ap_list_seq += 1
            _log(f"[INFO] OUI database loaded: {len(loaded_map)} entries")
        else:
            with oui_db_lock:
                oui_map = {}
                oui_loaded = True  # Stop returning "加载中" forever when DB is unavailable.
                oui_vendor_cache.clear()
            with ap_lock:
                ap_list_seq += 1
            _log("[WARN] OUI 数据库未加载（AP 厂商将显示未知）")
    except Exception as e:
        with oui_db_lock:
            oui_map = {}
            oui_loaded = True  # Fallback to unknown vendor instead of endless loading state.
            oui_vendor_cache.clear()
        with ap_lock:
            ap_list_seq += 1
        _log(f"[WARN] OUI database load exception: {e}")
    finally:
        with oui_db_lock:
            oui_loading_started = False

def start_oui_loader() -> None:
    global oui_loading_started
    with oui_db_lock:
        if oui_loaded or oui_loading_started:
            return
        oui_loading_started = True
    Thread(target=_oui_load_worker, daemon=True).start()

def _lookup_oui_vendor(mac: str | None) -> str:
    key = _mac_oui_key(mac)
    if not key:
        return ""
    with oui_db_lock:
        cached = oui_vendor_cache.get(key)
        loaded = oui_loaded
        vendor = oui_map.get(key) if loaded else None
    if cached is not None:
        return cached
    if vendor:
        with oui_db_lock:
            oui_vendor_cache[key] = vendor
        return vendor
    if not loaded:
        start_oui_loader()
        return "\u52a0\u8f7d\u4e2d"
    with oui_db_lock:
        oui_vendor_cache[key] = "\u672a\u77e5"
    return "\u672a\u77e5"

def _ap_trim_locked(now_wall: float | None = None) -> None:
    now_wall = float(now_wall or time.time())
    if len(ap_table) <= max(80, int(AP_CFG.get("list_max") or AP_LIST_MAX_DEFAULT) * 2):
        # Still prune very old entries to keep the table "realtime".
        victims = [mac for mac, e in ap_table.items()
                   if (now_wall - float(e.get("last_seen_wall_ts") or now_wall)) > (AP_STALE_TIMEOUT * 3)]
        for mac in victims:
            ap_table.pop(mac, None)
        return
    items = sorted(ap_table.items(), key=lambda kv: kv[1].get("last_seen_wall_ts", 0.0), reverse=True)
    keep = {mac for mac, _ in items[:max(80, int(AP_CFG.get("list_max") or AP_LIST_MAX_DEFAULT) * 2)]}
    for mac in list(ap_table.keys()):
        if mac not in keep:
            ap_table.pop(mac, None)

def _ap_touch(mac: str, ssid: str | None, rssi: int | None, ch: int | None, subtype: str) -> None:
    global ap_list_seq
    now_wall = time.time()
    now_mono = time.monotonic()
    vendor = _lookup_oui_vendor(mac)
    with ap_lock:
        e = ap_table.get(mac)
        if e is None:
            e = {
                "mac": mac,
                "ssid": ssid or "",
                "rssi": rssi,
                "ch": ch,
                "subtype": subtype,
                "first_seen_wall_ts": now_wall,
                "last_seen_wall_ts": now_wall,
                "first_seen_ts": now_mono,
                "last_seen_ts": now_mono,
                "hits": 0,
                "vendor": "",
                "vendor_type": "",
            }
            ap_table[mac] = e
        if ssid is not None:
            e["ssid"] = ssid
        if rssi is not None:
            e["rssi"] = rssi
        if ch:
            e["ch"] = ch
        e["subtype"] = subtype or e.get("subtype") or "AP"
        e["last_seen_wall_ts"] = now_wall
        e["last_seen_ts"] = now_mono
        e["hits"] = int(e.get("hits") or 0) + 1
        if vendor and ((not e.get("vendor")) or (e.get("vendor") in ("加载中", "未知")) or (vendor not in ("加载中", "未知"))):
            e["vendor"] = vendor
        vname = str(e.get("vendor") or vendor or "")
        if _is_wifi_fast_mac(mac):
            e["vendor_type"] = "WiFi快传"
        else:
            e["vendor_type"] = _ap_vendor_type(vname, e.get("ssid"))
        _ap_trim_locked(now_wall)
        ap_list_seq += 1

def _ap_snapshot() -> tuple[list[dict], int, int]:
    now_wall = time.time()
    with ap_lock:
        _ap_trim_locked(now_wall)
        items = list(ap_table.values())
        seq = ap_list_seq
    rows: list[dict] = []
    for e in items:
        mac = str(e.get("mac") or "")
        vendor = _lookup_oui_vendor(mac) or str(e.get("vendor") or "")
        last_seen_wall = float(e.get("last_seen_wall_ts") or now_wall)
        age = max(0, int(now_wall - last_seen_wall))
        rows.append({
            "mac": mac,
            "ssid": str(e.get("ssid") or ""),
            "rssi": e.get("rssi"),
            "ch": e.get("ch"),
            "hits": int(e.get("hits") or 0),
            "subtype": str(e.get("subtype") or "AP"),
            "vendor": vendor or str(e.get("vendor") or "\u672a\u77e5"),
            "vendor_type": ("WiFi快传" if _is_wifi_fast_mac(mac) else _ap_vendor_type(vendor or str(e.get("vendor") or ""), e.get("ssid"))),
            "age": age,
            "last_seen": _fmt_wall_ts(last_seen_wall),
        })
    # realtime list sorted by signal strength (higher RSSI first)
    rows.sort(
        key=lambda x: (
            -float(x.get("rssi")) if x.get("rssi") is not None else float("inf"),
            x["age"],
            x.get("mac") or "",
        )
    )
    limit = int(AP_CFG.get("list_max") or AP_LIST_MAX_DEFAULT)
    total = len(rows)
    return rows[:limit], seq, total

# -----------------------------------------------------------------------------
# 机型映射
# -----------------------------------------------------------------------------
def _model_from_sn(sn: str) -> str:
    if not sn or sn.startswith("MAC:"):
        return "N/A"
    p8 = sn[:8].upper()
    for pref, model in MODEL_MAP.items():
        if p8 == str(pref)[:8].upper():
            return model
    return "N/A"

def load_model_map(path: str) -> None:
    global MODEL_MAP
    try:
        with open(path, "r", encoding="utf-8") as f:
            obj = json.load(f)
        if isinstance(obj, dict):
            MODEL_MAP = {str(k): str(v) for k, v in obj.items()}
            _log(f"[INFO] model map loaded: {path} ({len(MODEL_MAP)} entries)")
        else:
            _log(f"[WARN] model map format invalid: {path}")
    except FileNotFoundError:
        _log(f"[WARN] model map not found: {path}")
    except Exception as e:
        _log(f"[WARN] model map load failed: {e}")

# -----------------------------------------------------------------------------
# Formatting helpers
# -----------------------------------------------------------------------------
def _fmt(v, fmt=".6f", unit="", na="N/A") -> str:
    return f"{v:{fmt}}{unit}" if v is not None else na

# -----------------------------------------------------------------------------
# 地理
# -----------------------------------------------------------------------------
def _haversine(lat1, lon1, lat2, lon2) -> float:
    R  = 6371000.0
    p1, p2 = math.radians(lat1), math.radians(lat2)
    a  = (math.sin(math.radians(lat2-lat1)/2)**2
          + math.cos(p1)*math.cos(p2)*math.sin(math.radians(lon2-lon1)/2)**2)
    return 2*R*math.asin(min(1.0, math.sqrt(a)))

def _bearing(lat1, lon1, lat2, lon2) -> float | None:
    try:
        p1, p2 = math.radians(lat1), math.radians(lat2)
        dl     = math.radians(lon2-lon1)
        return (math.degrees(math.atan2(
            math.sin(dl)*math.cos(p2),
            math.cos(p1)*math.sin(p2)-math.sin(p1)*math.cos(p2)*math.cos(dl)
        ))+360)%360
    except Exception:
        return None

def _bearing8(deg: float) -> str:
    return ["N","NE","E","SE","S","SW","W","NW"][int((deg+22.5)//45)%8]

# -----------------------------------------------------------------------------
# 系统命令 / 接口
# -----------------------------------------------------------------------------
def run_cmd(cmd: str, timeout: int = 5) -> str:
    try:
        r = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        return (r.stdout or "").strip()
    except Exception:
        return ""

def _sniff_note_packet() -> None:
    global sniff_last_pkt_mono, sniff_last_pkt_wall, sniff_last_error, sniff_last_error_wall
    now_mono = time.monotonic()
    now_wall = time.time()
    with sniff_health_lock:
        sniff_last_pkt_mono = now_mono
        sniff_last_pkt_wall = now_wall
        sniff_last_error = ""
        sniff_last_error_wall = 0.0

def _sniff_idle_sec(now_mono: float | None = None) -> float | None:
    now_mono = float(now_mono or time.monotonic())
    with sniff_health_lock:
        last = sniff_last_pkt_mono
    if not last:
        return None
    return max(0.0, now_mono - float(last))

def _sniff_note_error(msg: str) -> None:
    global sniff_last_error, sniff_last_error_wall
    text = str(msg or "").strip()
    if len(text) > 220:
        text = text[:220]
    with sniff_health_lock:
        sniff_last_error = text
        sniff_last_error_wall = time.time()

def _sniff_health_meta(now_mono: float, now_wall: float) -> dict:
    with sniff_health_lock:
        last_pkt_mono = float(sniff_last_pkt_mono or 0.0)
        last_pkt_wall = float(sniff_last_pkt_wall or 0.0)
        last_err = str(sniff_last_error or "")
        last_err_wall = float(sniff_last_error_wall or 0.0)
        iface = str(sniff_iface_name or "")
    idle_sec = None
    if last_pkt_mono > 0.0:
        idle_sec = max(0.0, now_mono - last_pkt_mono)
    state = "ok"
    msg = ""
    if last_err:
        state = "error"
        msg = last_err
    elif idle_sec is None:
        state = "warn"
        msg = "尚未收到无线管理帧"
    elif idle_sec >= SNIFF_STALL_RECOVER_SEC:
        state = "warn"
        msg = f"{int(idle_sec)}s no wireless management frame"
    return {
        "state": state,
        "msg": msg,
        "iface": iface,
        "idle_sec": (None if idle_sec is None else int(round(idle_sec))),
        "last_pkt": _fmt_wall_ts(last_pkt_wall if last_pkt_wall > 0 else None),
        "last_err_at": _fmt_wall_ts(last_err_wall if last_err_wall > 0 else None),
    }

def _sniff_recover_iface(iface: str, reason: str, force: bool = False) -> bool:
    global sniff_last_recover_wall, sniff_iface_name
    iface = str(iface or "").strip()
    if not iface:
        _sniff_note_error(f"iface empty: {reason}")
        return False
    now_wall = time.time()
    with sniff_health_lock:
        if (not force) and sniff_last_recover_wall and (now_wall - sniff_last_recover_wall) < SNIFF_RECOVER_COOLDOWN_SEC:
            return False
        sniff_last_recover_wall = now_wall
        sniff_iface_name = iface
    _sniff_note_error(reason)
    _log(f"[WARN] sniff recover: {reason}, reset iface {iface}")
    for c in (
        f"ip link set {iface} down",
        f"iw dev {iface} set type monitor",
        f"ip link set {iface} up",
        f"iw dev {iface} set power_save off",
    ):
        run_cmd(c, timeout=6)
    if current_channel:
        run_cmd(f"iw dev {iface} set channel {current_channel}", timeout=6)
    info_raw = run_cmd(f"iw dev {iface} info")
    if not info_raw or ("Interface" not in info_raw):
        _sniff_note_error(f"iface unavailable: {iface}")
        return False
    info_lines = []
    for ln in info_raw.splitlines():
        t = ln.strip()
        if re.search(r"\b(type|channel)\b", t):
            info_lines.append(t)
    if info_lines:
        _log(f"[INFO] sniff recover result: {' | '.join(info_lines)}")
    with sniff_health_lock:
        sniff_iface_name = iface
    return True
def _sniff_iface_candidates() -> dict[str, str]:
    iw = run_cmd("iw dev")
    iftypes: dict[str, str] = {}
    cur = None
    for line in (iw or "").splitlines():
        m = re.match(r"\s*Interface\s+(\S+)", line)
        if m:
            cur = m.group(1)
            continue
        m2 = re.match(r"\s*type\s+(\S+)", line)
        if m2 and cur:
            iftypes[cur] = m2.group(1)
    return iftypes

def _iface_options_snapshot() -> list[dict]:
    out: list[dict] = []
    iftypes = _sniff_iface_candidates()
    for name, mode in iftypes.items():
        try:
            supports_5g = bool(detect_5g(name))
        except Exception:
            supports_5g = False
        out.append({
            "name": str(name),
            "mode": str(mode or ""),
            "is_monitor": (str(mode or "") == "monitor"),
            "supports_5g": supports_5g,
        })
    out.sort(key=lambda x: (0 if x.get("is_monitor") else 1, x.get("name") or ""))
    return out

def _sniff_pick_iface(prefer: str | None = None) -> str | None:
    iftypes = _sniff_iface_candidates()
    if not iftypes:
        return None
    if prefer and prefer in iftypes and iftypes.get(prefer) == "monitor":
        return prefer
    mon = [i for i, t in iftypes.items() if t == "monitor"]
    if mon:
        return mon[0]
    if prefer and prefer in iftypes:
        return prefer
    for k in iftypes.keys():
        return k
    return None
def _sniff_is_no_device_error(ex: Exception) -> bool:
    s = str(ex or "")
    return (
        ("No such device" in s) or
        ("Errno 19" in s) or
        ("Network is down" in s) or
        ("Errno 100" in s)
    )

def _freq_to_ch(freq) -> int | None:
    try:
        f = int(freq)
    except Exception:
        return None
    if 2412 <= f <= 2484: return 14 if f==2484 else (f-2407)//5
    if 5000 <= f <= 5900: return (f-5000)//5
    return None

def _rt_channel(pkt) -> int | None:
    if not pkt.haslayer(RadioTap): return None
    rt = pkt[RadioTap]
    for attr in ("ChannelFrequency","ChannelFreq","channel_freq","Channel"):
        if hasattr(rt, attr):
            v = getattr(rt, attr)
            if isinstance(v, tuple) and v: v = v[0]
            if isinstance(v, (int,float)):
                ch = _freq_to_ch(int(v))
                if ch: return ch
    return None

def _ssid_to_sn(ssid: str) -> str | None:
    m = SSID_SN_RE.search(ssid) if ssid else None
    return m.group(1) if m else None

def interface_detect(prefer: str | None = None) -> str:
    iw      = run_cmd("iw dev")
    iftypes: dict[str, str] = {}
    cur     = None
    for line in iw.splitlines():
        m = re.match(r"\s*Interface\s+(\S+)", line)
        if m: cur = m.group(1)
        m2 = re.match(r"\s*type\s+(\S+)", line)
        if m2 and cur: iftypes[cur] = m2.group(1)

    if prefer and prefer in iftypes:
        iface = prefer
    else:
        mon = [i for i,t in iftypes.items() if t=="monitor"]
        iface = mon[0] if mon else (list(iftypes.keys())[0] if iftypes else None)
    if not iface:
        sys.exit("[FATAL] 未找到无线接口")

    mode = iftypes.get(iface, "unknown")
    _log(f"[INFO] iface={iface} mode={mode}")
    if mode != "monitor":
        _log("[INFO] switching to monitor mode...")
        for c in (f"ip link set {iface} down",
                  f"iw dev {iface} set type monitor",
                  f"ip link set {iface} up"):
            run_cmd(c)
        new = run_cmd(f"iw dev {iface} info | grep type").strip()
        _log(f"[INFO] monitor switch result: {new}")
    run_cmd(f"iw dev {iface} set power_save off")
    ch_info = run_cmd(f"iw dev {iface} info | grep channel").strip()
    _log(f"[INFO] current channel: {ch_info or 'unknown'}")
    return iface

def detect_5g(iface: str) -> bool:
    out = run_cmd(f"iw dev {iface} info")
    m   = re.search(r"\bwiphy\s+(\d+)", out)
    if not m: return False
    phy = run_cmd(f"iw phy{m.group(1)} info")
    if "Band 2:" in phy: return True
    return any(5000<=int(x)<=5999 for x in re.findall(r"\b(5\d{3})\s+MHz\b", phy))

# -----------------------------------------------------------------------------
# Channel hopper
# -----------------------------------------------------------------------------
def channel_hopper(iface, ch2g, ch5g, dw2, dw5, settle_ms, hit_ms, cap_ms):
    global current_channel
    dw2, dw5, settle = dw2/1000, dw5/1000, settle_ms/1000
    hit_until = 0.0
    lk = Lock()

    def note_hit():
        nonlocal hit_until
        now  = time.monotonic()
        ext  = max(0, hit_ms)/1000
        hold = max(0, cap_ms)/1000
        if ext <= 0: return
        with lk:
            cap = now+hold if hold>0 else now+ext
            hit_until = min(max(hit_until, now+ext), cap)

    globals()["_hopper_note_hit"] = note_hit

    def do_hold():
        with lk: u = hit_until
        rem = u - time.monotonic()
        if rem > 0: time.sleep(rem)

    while True:
        for ch in random.sample(ch2g, len(ch2g)):
            run_cmd(f"iw dev {iface} set channel {ch}")
            current_channel = ch
            if settle: time.sleep(settle)
            do_hold(); time.sleep(dw2)
        for ch in (random.sample(ch5g, len(ch5g)) if ch5g else []):
            run_cmd(f"iw dev {iface} set channel {ch}")
            current_channel = ch
            if settle: time.sleep(settle)
            do_hold(); time.sleep(dw5)

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
        lat = float(lat_raw) * 1e-7
        lon = float(lon_raw) * 1e-7
        if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
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
        lat = float(lat_raw) * 1e-7
        lon = float(lon_raw) * 1e-7
        if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
            return None
        if abs(lat) < 1e-6 and abs(lon) < 1e-6:
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

# -----------------------------------------------------------------------------
# State update
# -----------------------------------------------------------------------------
mac_to_basic:   dict[str, dict] = {}
mac_to_ssid_sn: dict[str, dict] = {}

def _snap(e: dict) -> dict:
    s = {k: e.get(k) for k in
         ("sn","src_mac","id_type","model","lat","lon","alt","speed","vspeed","last_ch","move_dir")}
    if CHANGE_ON_RSSI: s["rssi"]  = e.get("rssi")
    if CHANGE_ON_PL:   s["pl_sig"] = e.get("pl_sig")
    return s

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
    if src.get("pilot_lat") is not None and src.get("pilot_lon") is not None:
        dst["pilot_lat"] = src.get("pilot_lat")
        dst["pilot_lon"] = src.get("pilot_lon")
        dst["pilot_loc_type"] = src.get("pilot_loc_type")
        dst["pilot_loc_type_text"] = src.get("pilot_loc_type_text")
    src_cap_ts = src.get("last_capture_wall_ts")
    dst_cap_ts = dst.get("last_capture_wall_ts")
    if src_cap_ts is not None and (dst_cap_ts is None or float(src_cap_ts) > float(dst_cap_ts)):
        dst["last_capture_wall_ts"] = src_cap_ts
    src_rp = list(src.get("raw_packets") or [])
    if src_rp:
        dst_rp = list(dst.get("raw_packets") or [])
        merged = (dst_rp + src_rp)[-6:]
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
            "pilot_lat": e.get("pilot_lat"),
            "pilot_lon": e.get("pilot_lon"),
            "pilot_loc_type": e.get("pilot_loc_type"),
            "pilot_loc_type_text": e.get("pilot_loc_type_text"),
            "last_capture_wall_ts": e.get("last_capture_wall_ts"),
            "raw_packets": list(e.get("raw_packets") or [])[-3:],
            "scan_type": _scan_type_key(e.get("scan_type")),
            "track": _sanitize_track(e.get("track") or []),
            "track_updated_wall_ts": e.get("track_updated_wall_ts"),
        }
        history_table[sn] = h
    h["sn"] = sn
    h["src_mac"] = e.get("src_mac")
    h["id_type"] = e.get("id_type")
    h["model"] = e.get("model")
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
    h["rssi"] = e.get("rssi")
    h["move_dir"] = e.get("move_dir")
    h["ssid"] = e.get("ssid")
    h["capture_type"] = e.get("capture_type")
    h["last_capture_wall_ts"] = e.get("last_capture_wall_ts")
    h["raw_packets"] = list(e.get("raw_packets") or [])[-3:]
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
    h.setdefault("raw_packets", list(e.get("raw_packets") or [])[-3:])
    h.setdefault("scan_type", _scan_type_key(e.get("scan_type")))
    h.setdefault("track", _sanitize_track(e.get("track") or []))
    h.setdefault("track_updated_wall_ts", e.get("track_updated_wall_ts"))
    _history_mark_dirty()

def state_update(src_mac: str, decoded: dict, rssi: int | None,
                 ch: int, ch_assumed: bool, pl_sig: int,
                 *, scan_type: str = "rid", ssid: str | None = None,
                 capture_type: str | None = None, raw_pkt_hex: str | None = None) -> None:
    basic = decoded.get("basic_id")
    loc   = decoded.get("location")
    sys_loc = decoded.get("system")

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
    model = ("WiFi快传" if scan_type_key == "phone" else _model_from_sn(sn))
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
                "pilot_loc_type":None, "pilot_loc_type_text":"",
                "scan_type":scan_type_key,
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
        e["model"]   = model
        e["scan_type"] = scan_type_key
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
                    "hex": str(raw_pkt_hex),
                })
                if len(rp) > 6:
                    rp = rp[-6:]
                e["raw_packets"] = rp

        if CHANGE_ON_PL:   e["pl_sig"] = pl_sig
        if rssi is not None:
            old = e.get("rssi")
            if old is None or not CHANGE_ON_RSSI or abs(rssi-old)>=RSSI_DELTA:
                e["rssi"] = rssi
        if ch:
            e["last_ch"]   = ch
            e["ch_assumed"] = bool(ch_assumed)

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
            if e.get("lat") is not None and e.get("lon") is not None:
                _track_append_point(e, float(e.get("lat")), float(e.get("lon")), float(now_wall))

        if sys_loc and (sys_loc.get("pilot_lat") is not None) and (sys_loc.get("pilot_lon") is not None):
            try:
                plat = float(sys_loc.get("pilot_lat"))
                plon = float(sys_loc.get("pilot_lon"))
                if (-90.0 <= plat <= 90.0) and (-180.0 <= plon <= 180.0):
                    e["pilot_lat"] = plat
                    e["pilot_lon"] = plon
                    e["pilot_loc_type"] = sys_loc.get("pilot_loc_type")
                    e["pilot_loc_type_text"] = str(sys_loc.get("pilot_loc_type_text") or "")
            except Exception:
                pass

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

        _SNAP_TO_COL = {"lat":"lat_s","lon":"lon_s","alt":"alt_s","speed":"spd_s",
                        "vspeed":"vsp_s","last_ch":"ch_s","move_dir":"dir_s",
                        "rssi":"rssi_s","model":"model","sn":"sn_s"}
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
        queue_online_notification(notify_payload, notify_event_title, now_wall=now_wall)

def _emit_log(e: dict, changed_keys: set, reason: str) -> None:
    sn    = str(e.get("sn",""))
    model = str(e.get("model","N/A"))
    it    = str(e.get("id_type",""))
    mac   = str(e.get("src_mac",""))
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
    pfx   = "★" if reason=="first" else "→"
    _log(f"{pfx} SN={sn} model={model} id={it} MAC={mac} "
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
    elif n <= 65535:
        return bytes([0x81, 126, (n>>8)&0xFF, n&0xFF]) + data
    else:
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
            if scan_type_key != "phone" and (len(sn) != 20 or (not sn.isalnum())):
                continue
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
            track_data = _sanitize_track(cur.get("track", hist.get("track", [])) or [])
            drones.append({
                "sn": sn,
                "sn_src": sn_src,
                "scan_type": scan_type,
                "model": cur.get("model", hist.get("model","N/A")),
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
                "pilot_loc_type": cur.get("pilot_loc_type", hist.get("pilot_loc_type")),
                "pilot_loc_type_text": cur.get("pilot_loc_type_text", hist.get("pilot_loc_type_text","")) or "",
                "rssi": cur.get("rssi", hist.get("rssi")),
                "pkts": hist.get("pkt_count_total", cur.get("pkt_count",0)),
                "dir": cur.get("move_dir", hist.get("move_dir")) or "-",
                "ssid": cur.get("ssid", hist.get("ssid","")) or "",
                "capture_type": cur.get("capture_type", hist.get("capture_type","")) or "",
                "capture_time": _fmt_wall_ts(cap_wall_ts),
                "last_pkt_time": _fmt_wall_ts(cap_wall_ts),
                "raw_packets": list(cur.get("raw_packets", hist.get("raw_packets", [])) or [])[-3:],
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
        },
    }

_PAGE_HTML = """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>RID Monitor</title>
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"/>
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<style>
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
:root{
  --font-ui:"Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:ui-monospace,SFMono-Regular,Menlo,Consolas,"Liberation Mono","Courier New",monospace;
  --bg:#070b12;--bg2:#0d1117;--border:#1e2a38;--txt:#c5cdd9;
  --green:#3fb950;--yellow:#d29922;--dim:#6e7681;--blue:#58a6ff;
  --purple:#d2a8ff;--cyan:#79c0ff;--glow:rgba(88,166,255,.12)
}
body{background:var(--bg);color:var(--txt);font-family:var(--font-ui);font-size:16px;
     height:100dvh;display:grid;grid-template-rows:auto minmax(0,1fr) minmax(240px,38vh) auto;
     row-gap:12px;overflow:hidden;position:relative;
     transition:background-color .18s,color .18s}
body.theme-light{
  --bg:#f4f7fb;--bg2:#eef3f9;--border:#cfd8e3;--txt:#1f2937;
  --green:#1f883d;--yellow:#9a6700;--dim:#6b7280;--blue:#0969da;
  --purple:#8250df;--cyan:#1d4ed8;--glow:rgba(9,105,218,.08)
}
body::before{
  content:""; position:fixed; inset:0; pointer-events:none; z-index:0;
  background:
    radial-gradient(900px 420px at 8% -5%, rgba(88,166,255,.16), transparent 55%),
    radial-gradient(820px 380px at 95% 110%, rgba(121,192,255,.10), transparent 60%),
    linear-gradient(180deg, rgba(255,255,255,.015), rgba(255,255,255,0));
}
body.theme-light::before{
  background:
    radial-gradient(900px 420px at 8% -5%, rgba(9,105,218,.10), transparent 55%),
    radial-gradient(820px 380px at 95% 110%, rgba(37,99,235,.06), transparent 60%),
    linear-gradient(180deg, rgba(255,255,255,.45), rgba(255,255,255,0));
}
header,.tbl-wrap,.panel,footer{position:relative;z-index:1}
.mono, code, .logbox, .aplist, .adv-input, .stat b{font-family:var(--font-mono)}

/* -- Header -- */
header{background:linear-gradient(180deg, rgba(16,23,33,.96), rgba(13,17,23,.96));border-bottom:1px solid var(--border);
       padding:10px 14px;display:grid;grid-template-columns:auto 1fr;
       align-items:center;gap:8px 16px;position:sticky;top:0;z-index:10;
       box-shadow:0 8px 24px rgba(0,0,0,.22), inset 0 1px 0 rgba(121,192,255,.06)}
header .head-stats{display:flex;align-items:center;justify-content:flex-end;
       gap:8px 16px;flex-wrap:wrap;min-width:0}
header h1{font-size:20px;font-weight:700;color:var(--blue);letter-spacing:.04em}
header details.adv{grid-column:1/-1;border:1px solid var(--border);border-radius:6px;background:#0b1320}
header details.adv > summary{cursor:pointer;list-style:none;padding:8px 10px;color:#8b949e;font-size:14px}
header details.adv > summary::-webkit-details-marker{display:none}
header details.adv[open] > summary{border-bottom:1px solid var(--border);color:var(--blue)}
.adv-body{
  padding:10px;
  display:grid;
  grid-template-columns:repeat(2,minmax(0,1fr));
  gap:10px;
}
.adv-col{display:grid;gap:8px;min-width:0;align-content:start}
.adv-row{display:flex;gap:8px;align-items:center;flex-wrap:wrap;min-width:0}
.adv-row label{font-size:13px;color:#8b949e}
.adv-input{min-width:260px;flex:1 1 420px;background:#0a0e14;color:var(--txt);border:1px solid #2b3a4b;border-radius:6px;padding:7px 9px;font:inherit}
.adv-note{font-size:13px;color:#8b949e;word-break:break-all}
.adv-note code{color:#c5cdd9}
.adv-actions{display:flex;gap:8px;flex-wrap:wrap}
.cfg-editor{
  width:100%;min-height:220px;resize:vertical;
  background:#0a0e14;color:#cbd8e8;border:1px solid #2b3a4b;border-radius:6px;
  padding:8px 10px;font:13px/1.5 var(--font-mono);
}
.stat{font-size:15px;color:#8b949e;white-space:nowrap}
.stat b{color:var(--green)}
.stat.ls b{color:var(--dim)}
.stat.cs b{color:var(--purple)}
.stat.ts b{color:var(--cyan);font-weight:400}
.stat.snf b.ok{color:var(--green)}
.stat.snf b.warn{color:var(--yellow)}
.stat.snf b.err{color:#ff7b72}
.sniff-banner{
  display:none;
  grid-column:1/-1;
  margin-top:6px;
  padding:8px 12px;
  border:1px solid #7f3f3f;
  border-radius:8px;
  background:rgba(127,63,63,.18);
  color:#ffb4b4;
  font-size:13px;
  line-height:1.35;
  z-index:12;
}
.sniff-banner.warn{
  border-color:#7a622a;
  background:rgba(122,98,42,.18);
  color:#f1d08b;
}
.banner-stack{
  position:fixed;top:10px;left:50%;transform:translateX(-50%);
  display:flex;flex-direction:column;gap:8px;z-index:9998;
  width:min(92vw, 860px);pointer-events:none;
}
.banner{
  opacity:0;transform:translateY(-8px);
  transition:opacity .24s ease,transform .24s ease;
  border:1px solid #33516f;border-radius:8px;
  background:rgba(14,25,38,.9);color:#d6e5f7;
  padding:9px 12px;font-size:13px;line-height:1.35;
  box-shadow:0 10px 26px rgba(0,0,0,.35);
}
.banner.show{opacity:1;transform:translateY(0)}
.banner.ok{border-color:#2d6f4d;background:rgba(21,52,35,.92);color:#b8f5cf}
.banner.warn{border-color:#8a5c34;background:rgba(61,38,20,.94);color:#ffd9a9}
#dot-ws{width:9px;height:9px;border-radius:50%;background:var(--dim);
        display:inline-block;margin-right:4px;transition:background .3s}
#dot-ws.on{background:var(--green)}

/* -- Table -- */
.tbl-wrap{margin:0 12px;min-height:0;overflow:auto;
          border:1px solid var(--border);border-radius:8px;background:linear-gradient(180deg, rgba(13,17,23,.98), rgba(10,14,20,.98));
          box-shadow:0 10px 28px rgba(0,0,0,.20), 0 0 0 1px rgba(88,166,255,.03) inset}
table{width:100%;border-collapse:collapse;table-layout:fixed;min-width:980px}
thead tr{background:var(--bg2);position:sticky;top:0;z-index:9}
thead th{padding:9px 10px;text-align:left;font-size:14px;color:#8b949e;
         border-bottom:1px solid var(--border);white-space:nowrap}
tbody tr{border-bottom:1px solid #161b22;transition:background .12s}
tbody tr:hover{background:rgba(88,166,255,.06)}
tbody tr.lost{opacity:.4}
tbody tr.selected{background:rgba(88,166,255,.10)}
td{padding:8px 10px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:16px}
.empty{text-align:center;padding:40px;color:var(--dim);font-size:15px}
th:nth-child(1),td:nth-child(1){width:46px}
th:nth-child(2),td:nth-child(2){width:46px}
th:nth-child(3),td:nth-child(3){width:360px}
th:nth-child(4),td:nth-child(4){width:132px}
th:nth-child(5),td:nth-child(5){width:96px}
th:nth-child(6),td:nth-child(6){width:62px}
th:nth-child(7),td:nth-child(7){width:68px}
th:nth-child(8),td:nth-child(8){width:92px}
th:nth-child(9),td:nth-child(9),th:nth-child(10),td:nth-child(10){width:176px}
.sel-wrap{display:flex;align-items:center;justify-content:center}
.sel-sn{width:16px;height:16px;accent-color:var(--blue);cursor:pointer}
.idx-cell{color:var(--dim);text-align:center}

/* -- Bottom Panels: Map + Logs -- */
.bottom{display:grid;grid-template-columns:minmax(0,1.15fr) minmax(0,1fr) minmax(0,.95fr);gap:12px;
        margin:0 12px;min-height:0}
.bottom.map-collapsed{grid-template-columns:max-content minmax(0,1fr) minmax(0,1.35fr)}
.bottom.log-collapsed{grid-template-columns:minmax(0,1.15fr) max-content minmax(0,1.35fr)}
.bottom.ap-collapsed{grid-template-columns:minmax(0,1.2fr) minmax(0,1fr) max-content}
.bottom.map-collapsed.log-collapsed{grid-template-columns:max-content max-content minmax(0,1fr)}
.bottom.map-collapsed.ap-collapsed{grid-template-columns:max-content minmax(0,1fr) max-content}
.bottom.log-collapsed.ap-collapsed{grid-template-columns:minmax(0,1fr) max-content max-content}
.bottom.all-collapsed{display:none}
body.bottom-all-collapsed{
  grid-template-rows:auto minmax(0,1fr) 0 auto;
  row-gap:8px;
}
@media(max-width:960px){
  header{
    grid-template-columns:1fr;
    padding:8px 10px;
    gap:8px 10px;
  }
  header h1{font-size:18px}
  header .head-stats{
    justify-content:flex-start;
    gap:6px 10px;
  }
  .stat{font-size:13px}
  .head-stats .btn-mini{padding:6px 8px}
  .head-stats .stat:last-child{margin-left:auto}
  .tbl-wrap,.bottom{margin:0 8px}
  .adv-body{grid-template-columns:1fr}
}
@media(max-width:1180px){
  .bottom{grid-template-columns:minmax(0,1fr) minmax(0,1fr)}
  .bottom.map-collapsed,.bottom.log-collapsed,.bottom.ap-collapsed,.bottom.map-collapsed.log-collapsed,.bottom.map-collapsed.ap-collapsed,.bottom.log-collapsed.ap-collapsed{
    grid-template-columns:minmax(0,1fr) minmax(0,1fr)
  }
  .bottom .panel.ap-panel{grid-column:1/-1;min-height:220px}
}
@media(max-width:800px){
  body{
    grid-template-rows:auto minmax(0,1fr) minmax(0,1fr) auto;
    row-gap:8px;
  }
  .tbl-wrap{margin:0 8px}
  table{min-width:680px}
  thead th{padding:7px 8px;font-size:13px}
  td{padding:6px 8px;font-size:13px}
  th:nth-child(3),td:nth-child(3){width:260px}
  th:nth-child(7),td:nth-child(7),
  th:nth-child(9),td:nth-child(9),
  th:nth-child(10),td:nth-child(10){display:none}
  .bottom{
    grid-template-columns:1fr;
    grid-template-rows:none;
    grid-auto-rows:minmax(170px,auto);
    gap:8px;
    margin:0 8px;
  }
  .bottom.map-collapsed,.bottom.log-collapsed,.bottom.ap-collapsed,.bottom.map-collapsed.log-collapsed,.bottom.map-collapsed.ap-collapsed,.bottom.log-collapsed.ap-collapsed{
    grid-template-columns:1fr
  }
  .bottom .panel.ap-panel{grid-column:auto;min-height:180px}
  .panel-hdr{padding:7px 10px;font-size:13px}
  .panel-hdr span.sub{font-size:12px}
  .btn-mini{min-height:30px;padding:6px 8px;font-size:12px}
  .icon-btn{width:22px;height:22px}
  .sn-badge{font-size:10px;padding:1px 5px}
  .adv-row{flex-direction:column;align-items:stretch}
  .map-mini-list{
    width:min(92vw,340px);
    right:8px;
    top:54px;
    max-height:55vh;
  }
  .aprow{
    grid-template-columns:30px minmax(96px, 13ch) 54px 72px minmax(0,1fr);
    gap:6px;
    padding:5px 4px;
  }
  .aprow > :nth-child(6){display:none}
  .adv-input{min-width:0;flex-basis:100%}
}
@media(max-width:600px){
  header h1{font-size:16px}
  .stat{font-size:12px}
  table{min-width:500px}
  th:nth-child(4),td:nth-child(4){display:none}
  th:nth-child(6),td:nth-child(6){display:none}
  th:nth-child(3),td:nth-child(3){width:200px}
  th:nth-child(8),td:nth-child(8){width:96px}
  .info-row{grid-template-columns:86px 1fr}
  .info-card{width:calc(100vw - 14px);max-height:84vh}
  .info-card-body{padding:10px 12px;font-size:13px}
  .cfg-editor{min-height:170px}
}
@media(max-width:480px){
  header{padding:7px 8px;gap:6px 8px}
  header h1{font-size:15px}
  header .head-stats{gap:5px 8px}
  .head-stats .btn-mini{padding:5px 7px;font-size:11px}
  .tbl-wrap,.bottom{margin:0 6px}
  table{min-width:440px}
  th:nth-child(2),td:nth-child(2){display:none}
  th:nth-child(3),td:nth-child(3){width:186px}
  th:nth-child(5),td:nth-child(5){width:72px}
  th:nth-child(8),td:nth-child(8){width:88px}
  thead th{padding:6px 7px;font-size:12px}
  td{padding:5px 7px;font-size:12px}
  .bottom{gap:6px}
  .panel-hdr{padding:6px 9px;font-size:12px}
  .panel-hdr span.sub{font-size:11px}
  .map-mini-list{width:min(94vw,320px);right:6px;top:46px;max-height:52vh}
  .info-row{grid-template-columns:78px 1fr;gap:6px}
  .info-card-hd{padding:8px 10px}
}

.panel{border:1px solid var(--border);border-radius:8px;overflow:hidden;
       display:flex;flex-direction:column;min-height:0;
       box-shadow:0 10px 24px rgba(0,0,0,.18), 0 0 0 1px rgba(88,166,255,.02) inset}
.panel-hdr{background:linear-gradient(180deg, rgba(13,17,23,.98), rgba(12,18,27,.95));padding:8px 14px;font-size:14px;
           color:var(--blue);font-weight:700;border-bottom:1px solid var(--border);
           display:flex;justify-content:space-between;align-items:center}
.panel-hdr span.sub{color:#8b949e;font-size:13px;font-weight:400}
.panel-hdr .hdr-actions{display:flex;align-items:center;gap:8px}
.panel.collapsible.collapsed{align-self:start;min-height:0}
.panel.collapsible.collapsed .panel-hdr{padding:8px 10px;gap:8px}
.panel.collapsible.collapsed .panel-hdr .sub{display:none}
.panel.collapsible.collapsed .panel-hdr label{display:none}
.panel.collapsible.collapsed .panel-hdr .hdr-actions{gap:6px}
.panel.log-panel.collapsed .logbox{display:none}
.panel.log-panel.collapsed .panel-hdr{border-bottom:none}
.panel.map-panel.collapsed #map{display:none}
.panel.map-panel.collapsed .panel-hdr{border-bottom:none}
.panel.ap-panel.collapsed .aplist{display:none}
.panel.ap-panel.collapsed .panel-hdr{border-bottom:none}

/* -- Leaflet Map -- */
#map{flex:1;width:100%;min-height:0}
.panel.map-panel.fullscreen{
  position:fixed;inset:0;z-index:9997;border-radius:0;margin:0;background:var(--bg);
}
.panel.map-panel.fullscreen .panel-hdr{
  position:absolute;left:12px;right:12px;top:10px;z-index:1200;border-radius:8px;
}
.panel.map-panel.fullscreen #map{
  position:absolute;inset:0;height:100%;width:100%;
}
.map-mini-list{
  display:none;
  position:absolute;right:14px;top:62px;z-index:1201;
  width:min(320px,45vw);max-height:48vh;overflow:auto;
  border:1px solid var(--border);border-radius:8px;
  background:rgba(8,12,20,.88);backdrop-filter:blur(2px);
  padding:8px;
}
.map-mini-list .mini-title{font-size:12px;color:#8b949e;margin-bottom:6px}
.map-mini-list .mini-item{
  display:flex;align-items:center;gap:8px;padding:4px 2px;font-size:13px;white-space:nowrap;
}
.map-mini-list .mini-item .sn{overflow:hidden;text-overflow:ellipsis}
.panel.map-panel.fullscreen .map-mini-list{display:block}

/* -- Log Box -- */
.logbox{flex:1;overflow-y:auto;padding:7px 12px;
        font-size:14px;line-height:1.65;
        background:var(--bg);min-height:0}
.logbox .ap{color:var(--txt)}
.logbox .rid{color:var(--green);font-weight:700}
.panel-hdr label{display:flex;align-items:center;gap:6px;cursor:pointer;
                 color:#8b949e;font-weight:400;font-size:13px}
.btn-mini{
  border:1px solid #334556;background:linear-gradient(180deg,#121b27,#0f1721);color:#c5cdd9;
  padding:5px 9px;border-radius:6px;font:inherit;font-size:13px;cursor:pointer;
  transition:background .12s,border-color .12s,box-shadow .12s,color .12s;
}
.btn-mini:hover{background:linear-gradient(180deg,#182334,#152131);border-color:#4f6a85;box-shadow:0 0 0 2px rgba(88,166,255,.08)}
.btn-mini:disabled{opacity:.55;cursor:wait}
.btn-mini.warn{border-color:#7f3f3f;color:#ffb4b4}
.btn-mini.warn:hover{background:#2a1717}
#bottom-restore{
  position:fixed;right:12px;bottom:12px;z-index:9996;display:none;
  box-shadow:0 8px 24px rgba(0,0,0,.26);
}
body.bottom-all-collapsed #bottom-restore{display:inline-flex}
.sn-cell{display:flex;align-items:center;gap:6px;min-width:0}
.sn-cell .mono{min-width:0;overflow:hidden;text-overflow:ellipsis}
.sn-badge{
  display:inline-block;padding:1px 6px;border-radius:10px;font-size:11px;
  border:1px solid #7d6118;background:#3b2e09;color:#ffd85f;line-height:1.3;flex:0 0 auto;
}
.icon-btn{
  border:1px solid #314156;background:#0d1622;color:#b6c2d2;
  width:24px;height:24px;display:inline-flex;align-items:center;justify-content:center;
  border-radius:5px;cursor:pointer;font-size:12px;line-height:1;flex:0 0 auto;
}
.icon-btn:hover{background:#172334;color:#fff}
.icon-btn.done{border-color:#2a6a45;color:#9ef0bc}
tbody tr.data-row{cursor:pointer}
tbody td.hl{
  background-color:rgba(255,216,96,calc(var(--hl-alpha,.0) * .58));
}
.info-modal{
  position:fixed;inset:0;display:none;align-items:center;justify-content:center;
  background:rgba(0,0,0,.46);backdrop-filter:blur(2px);z-index:9999;padding:14px;
}
.info-modal.show{display:flex}
.info-card{
  width:min(440px, calc(100vw - 28px));
  max-height:min(78vh, 560px);
  border:1px solid #2a3a4d;border-radius:10px;overflow:hidden;
  background:linear-gradient(180deg,#0f1721,#0c121a);
  box-shadow:0 16px 40px rgba(0,0,0,.42);
  display:flex;flex-direction:column;
}
.info-card-hd{
  display:flex;align-items:center;justify-content:space-between;gap:8px;
  padding:10px 12px;border-bottom:1px solid #203247;color:#8fbde7;font-weight:700;
}
.info-card-close{
  border:1px solid #344a60;background:#111c29;color:#c6d6ea;
  width:26px;height:26px;border-radius:6px;cursor:pointer;line-height:1;
}
.info-card-close:hover{background:#1a2a3d;color:#fff}
.info-card-body{
  padding:12px 14px;overflow:auto;
  white-space:normal;line-height:1.6;color:#d7e2ef;font-size:14px;
}
.info-grid{display:grid;grid-template-columns:1fr;gap:4px}
.info-row{display:grid;grid-template-columns:110px 1fr;gap:8px;align-items:start}
.info-row .k{color:#8fbde7}
.info-row .v{word-break:break-all}
.raw-title{margin:10px 0 6px 0;font-weight:700;color:#9cc7ef}
.raw-meta{font-size:12px;color:#8fa7c2;margin:6px 0 4px 0}
.raw-code{
  margin:0 0 8px 0;padding:8px 10px;border-radius:6px;
  border:1px solid #29405a;background:#0a1320;color:#d4e5f8;
  font:12px/1.45 var(--font-mono);white-space:pre-wrap;word-break:break-all;
}
.raw-empty{color:#8b949e;font-size:13px}
.info-card-body .mono{font-family:var(--font-mono)}
.aplist{flex:1;overflow:auto;background:var(--bg);font-size:13px;line-height:1.45;padding:6px 8px}
.aplist .ap-empty{color:var(--dim);padding:14px 8px}
.aprow{display:grid;grid-template-columns:42px minmax(116px, 15ch) 62px 86px minmax(0,1.15fr) minmax(0,1fr);gap:8px;padding:5px 6px;border-bottom:1px solid #141b23;align-items:start}
.aprow:hover{background:#101722}
.aprow.hd{position:sticky;top:0;background:#0d1117;color:#8b949e;font-weight:700;z-index:1}
.aprow .idx{text-align:right;color:#8fa4bc}
.aprow .mono{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.aprow .ap-mac{font-feature-settings:"tnum" 1}
.aplist.wide .aprow{grid-template-columns:42px minmax(170px, 20ch) 64px 92px minmax(0,1.15fr) minmax(0,1fr)}
.aplist.narrow .aprow{grid-template-columns:30px minmax(96px, 12ch) 54px minmax(0,1fr)}
.aplist.narrow .aprow > :nth-child(4),
.aplist.narrow .aprow > :nth-child(6){display:none}
.aprow .ssid{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all}
.aprow .vendor{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all;color:#c9d5e6}
.aprow .ssid-col,.aprow .vendor-col{min-width:0}
.subline{font-size:11px;color:#8b949e}

body.theme-light header{
  background:linear-gradient(180deg, rgba(255,255,255,.96), rgba(247,250,253,.96));
  box-shadow:0 8px 24px rgba(15,23,42,.08), inset 0 1px 0 rgba(9,105,218,.06);
}
body.theme-light header details.adv{background:#ffffff;border-color:#d8e1eb}
body.theme-light header details.adv > summary{color:#57606a}
body.theme-light header details.adv[open] > summary{color:var(--blue);border-bottom-color:#d8e1eb}
body.theme-light .tbl-wrap{
  background:linear-gradient(180deg, rgba(255,255,255,.98), rgba(250,252,255,.98));
  box-shadow:0 10px 28px rgba(15,23,42,.07), 0 0 0 1px rgba(9,105,218,.03) inset;
}
body.theme-light thead tr{background:#f3f6fa}
body.theme-light thead th{color:#5b6470}
body.theme-light tbody tr{border-bottom-color:#e6ecf2}
body.theme-light tbody tr:hover{background:rgba(9,105,218,.05)}
body.theme-light .panel{
  box-shadow:0 10px 24px rgba(15,23,42,.07), 0 0 0 1px rgba(9,105,218,.02) inset;
}
body.theme-light .panel-hdr{
  background:linear-gradient(180deg, rgba(255,255,255,.98), rgba(244,248,253,.95));
}
body.theme-light .panel-hdr,
body.theme-light .panel-hdr span.sub,
body.theme-light .panel-hdr label,
body.theme-light .adv-row label,
body.theme-light .adv-note,
body.theme-light .stat,
body.theme-light footer,
body.theme-light .subline{color:#5b6470}
body.theme-light .logbox,
body.theme-light .aplist{background:#ffffff}
body.theme-light .aprow{border-bottom-color:#edf1f5}
body.theme-light .aprow:hover{background:#f4f8ff}
body.theme-light .aprow.hd{background:#f3f6fa;color:#5b6470}
body.theme-light .aprow .vendor{color:#334155}
body.theme-light .adv-input{
  background:#ffffff;color:#1f2937;border-color:#c9d4df;
}
body.theme-light .adv-note code{color:#1f2937}
body.theme-light .cfg-editor{
  background:#ffffff;color:#1f2937;border-color:#c9d4df;
}
body.theme-light .btn-mini{
  border-color:#b8c6d6;
  background:linear-gradient(180deg,#ffffff,#f4f7fb);
  color:#334155;
}
body.theme-light .btn-mini:hover{
  background:linear-gradient(180deg,#f9fbff,#edf3fb);
  border-color:#95abc3;
  box-shadow:0 0 0 2px rgba(9,105,218,.08);
}
body.theme-light .btn-mini.warn{border-color:#d6a3a3;color:#9b1c1c}
body.theme-light .btn-mini.warn:hover{background:#fff1f1}
body.theme-light .icon-btn{
  border-color:#b8c6d6;background:#f7faff;color:#475569;
}
body.theme-light .icon-btn:hover{background:#eaf2ff;color:#0f172a}
body.theme-light .icon-btn.done{border-color:#4aa56f;color:#0f7a3b}
body.theme-light .sn-badge{border-color:#cfb061;background:#fff6db;color:#7b5b00}
body.theme-light tbody td.hl{
  background-color:rgba(250,213,97,calc(var(--hl-alpha,.0) * .52));
}
body.theme-light tbody tr.selected{background:rgba(9,105,218,.09)}
body.theme-light .map-mini-list{
  border-color:#cfd8e3;background:rgba(255,255,255,.94);
}
body.theme-light .map-mini-list .mini-title{color:#57606a}
body.theme-light .info-modal{background:rgba(15,23,42,.24)}
body.theme-light .info-card{
  border-color:#ced9e5;
  background:linear-gradient(180deg,#ffffff,#f7fbff);
  box-shadow:0 18px 36px rgba(15,23,42,.18);
}
body.theme-light .info-card-hd{
  color:#2d4e72;border-bottom-color:#d8e4ef;
}
body.theme-light .info-card-close{
  border-color:#b7c6d8;background:#f2f7fd;color:#35506d;
}
body.theme-light .info-card-close:hover{background:#e7f0fb;color:#1e334a}
body.theme-light .info-card-body{color:#1f2937}
body.theme-light .info-row .k{color:#35506d}
body.theme-light .raw-title{color:#35506d}
body.theme-light .raw-meta{color:#64748b}
body.theme-light .raw-code{
  border-color:#c7d7e9;background:#f6faff;color:#1f2937;
}
body.theme-light .raw-empty{color:#64748b}
body.theme-light .sniff-banner{
  border-color:#d7a6a6;
  background:#fff3f3;
  color:#9f2a2a;
}
body.theme-light .sniff-banner.warn{
  border-color:#d4bf8a;
  background:#fff9e8;
  color:#8a6800;
}
body.theme-light .banner{border-color:#b4c8df;background:rgba(255,255,255,.97);color:#334155}
body.theme-light .banner.ok{border-color:#89c49d;background:#ecfff3;color:#14532d}
body.theme-light .banner.warn{border-color:#d5b07f;background:#fff8eb;color:#7c2d12}
 
footer{text-align:center;padding:8px 10px;font-size:12px;color:#5b6470}
</style>
</head><body>
<header>
  <h1>&#x2708; RID Monitor</h1>
  <div class="head-stats">
  <span class="stat">&#x5728;&#x7EBF; <b id="n-live">-</b></span>
  <span class="stat ls">&#x79BB;&#x7EBF; <b id="n-lost">-</b></span>
  <span class="stat cs">&#x4FE1;&#x9053; <b id="cur-ch">-</b></span>
  <span class="stat ts">&#x66F4;&#x65B0; <b id="cur-ts">-</b></span>
  <span class="stat"><span id="dot-ws"></span><span id="ws-status">&#x8FDE;&#x63A5;&#x4E2D;</span></span>
  <button class="btn-mini" id="btn-clear-history" type="button">&#x6E05;&#x7A7A;&#x5386;&#x53F2;</button>
  </div>
</header>

<div class="tbl-wrap">
<table id="dtable">
<thead><tr>
  <th><div class="sel-wrap"><input id="sel-all" class="sel-sn" type="checkbox" title="全选"></div></th><th>#</th><th>SN</th><th>&#x673A;&#x578B;</th><th>&#x4FE1;&#x53F7;</th><th>&#x5305;</th><th>&#x65B9;&#x5411;</th><th>&#x6570;&#x636E;&#x66F4;&#x65B0;</th><th>&#x672B;&#x6B21;&#x53D1;&#x73B0;</th><th>&#x6700;&#x540E;&#x6570;&#x636E;&#x5305;</th>
</tr></thead>
<tbody id="tbody"></tbody>
</table>
</div>

<div class="bottom">
  <div class="panel">
    <div class="panel-hdr">
      &#x1F5FA; &#x5730;&#x56FE;
      <span class="sub" id="map-hint">&#x7B49;&#x5F85;&#x5750;&#x6807;...</span>
    </div>
    <div id="map"></div>
  </div>
  <div class="panel">
    <div class="panel-hdr">
      &#x1F4E1; AP &#x626B;&#x63CF;&#x65E5;&#x5FD7;
      <label><input type="checkbox" id="autoscroll" checked>&#x81EA;&#x52A8;&#x6EDA;&#x52A8;</label>
    </div>
    <div class="logbox" id="logbox"></div>
  </div>
</div>

<footer>Light RID Scanner</footer>

<script>
// -- WebSocket ------------------------------------------------
var ws, reconnTimer;
var lastLogsSeq = -1;
var lastApsSeq = -1;
var clearHistoryBusy = false;
var restartBusy = false;
var metaState = {};
var uiFrozen = false;
var frozenPendingData = null;
var uiTheme = 'dark';
var infoCardEscBound = false;
var webNotifyEnabled = false;
var droneStatePrev = {};
var droneFieldPrev = {};
var droneFieldHl = {};
var latestDroneMap = {};
var latestDroneRows = [];
var latestMapRows = [];
var latestApsRows = [];
var latestApsTotal = 0;
var selectedSnSet = {};
var trackCache = {};
var trackLoading = {};
var HL_FADE_IN_MS = 0;
var HL_HOLD_MS = 0;
var HL_FADE_OUT_MS = 2000;
var HL_TOTAL_MS = HL_FADE_IN_MS + HL_HOLD_MS + HL_FADE_OUT_MS;
var highlightAnimRunning = false;
var ifaceOptionsLoaded = false;
var sniffBannerPrevState = '';
var mapCollapsedBeforeFullscreen = null;
var mapFsUiTimer = null;
var miniListRenderSig = '';

function qs(id){ return document.getElementById(id); }
function fmt(v,dec,unit){ return v==null?'N/A':Number(v).toFixed(dec)+unit; }
function numOrNull(v){
  if(v==null) return null;
  var s = String(v).trim();
  if(!s) return null;
  var n = Number(s);
  return isFinite(n) ? n : null;
}
function intOrDefault(v, defv){
  if(v==null || v==='') return defv;
  var n = parseInt(v, 10);
  return isFinite(n) ? n : defv;
}
function baseFromMeta(meta){
  meta = (meta && typeof meta === 'object') ? meta : {};
  var lat = numOrNull(meta.base_lat);
  var lon = numOrNull(meta.base_lon);
  var zoom = intOrDefault(meta.base_zoom, 13);
  zoom = Math.max(3, Math.min(19, zoom));
  var name = String(meta.base_name || '\u57fa\u7ad9').trim() || '\u57fa\u7ad9';
  if(lat==null || lon==null) return {ok:false, name:name, lat:null, lon:null, zoom:zoom};
  if(lat < -90 || lat > 90 || lon < -180 || lon > 180) return {ok:false, name:name, lat:null, lon:null, zoom:zoom};
  return {ok:true, name:name, lat:lat, lon:lon, zoom:zoom};
}
function baseSignature(meta){
  var b = baseFromMeta(meta);
  if(!b.ok) return 'none';
  return [b.name, b.lat.toFixed(7), b.lon.toFixed(7), String(b.zoom)].join('|');
}
function shortMac(mac){
  mac = String(mac||'');
  if(mac.length <= 11) return mac;
  return mac.slice(0,8)+'...'+mac.slice(-5);
}
function infoRowHtml(label, value){
  return '<div class="info-row"><span class="k">'+esc(label)+'</span><span class="v">'+esc(value==null?'':value)+'</span></div>';
}
function snSourceText(e){
  var idType = String((e && e.id_type) || '').toUpperCase();
  return (idType === 'SSID') ? '\u0053\u0053\u0049\u0044' : '\u0052\u0049\u0044\u5305';
}
function scanTypeText(e){
  var k = String((e && e.scan_type_key) || '').toLowerCase();
  if(k === 'phone') return '\u624b\u673a\u5feb\u4f20';
  return '\u0052\u0049\u0044\u62a5\u9001';
}
function buildInfoHtml(e){
  e = e || {};
  var html = '<div class="info-grid">';
  html += infoRowHtml('SN', String(e.sn || '-'));
  html += infoRowHtml('机型', String(e.model || 'N/A'));
  html += infoRowHtml('在线状态', e.lost ? '离线' : '在线');
  html += infoRowHtml('归档', e.archived ? '是' : '否');
  html += infoRowHtml('MAC', String(e.mac || '-'));
  html += infoRowHtml('SSID', String(e.ssid || '(hidden)'));
  html += infoRowHtml('来源', snSourceText(e));
  html += infoRowHtml('扫描类型', scanTypeText(e));
  html += infoRowHtml('扫描类型Key', String(e.scan_type_key || '-'));
  html += infoRowHtml('捕获类型', String(e.capture_type || '-'));
  html += infoRowHtml('捕获时间', String(e.capture_time || '-'));
  html += infoRowHtml('最后数据包', String(e.last_pkt_time || e.capture_time || '-'));
  html += infoRowHtml('ID类型', String(e.id_type || '-'));
  html += infoRowHtml('信号', e.rssi==null ? 'N/A' : (e.rssi + 'dBm'));
  html += infoRowHtml('信道', String(e.ch || '?') + (e.ch_assumed ? ' (assumed)' : ''));
  html += infoRowHtml('包数', String(e.pkts==null?0:e.pkts));
  html += infoRowHtml('纬度', fmt(e.lat,6,''));
  html += infoRowHtml('经度', fmt(e.lon,6,''));
  html += infoRowHtml('飞手纬度', fmt(e.pilot_lat,6,''));
  html += infoRowHtml('飞手经度', fmt(e.pilot_lon,6,''));
  html += infoRowHtml('飞手位置类型', String(e.pilot_loc_type_text || e.pilot_loc_type || '-'));
  html += infoRowHtml('高度', fmt(e.alt,1,'m'));
  html += infoRowHtml('速度', fmt(e.spd,2,'m/s'));
  html += infoRowHtml('垂直速度', fmt(e.vspd,2,'m/s'));
  html += infoRowHtml('方向', String(e.dir || '-'));
  html += infoRowHtml('首次上线', String(e.first_seen || '-'));
  html += infoRowHtml('最后上线', String(e.last_seen || '-'));
  html += infoRowHtml('在线时长', fmtDurSec(e.online_dur));
  html += infoRowHtml('数据更新时间', String(e.age_text || fmtAge(e.age)));
  html += infoRowHtml('轨迹点数', String(e.track_count==null?0:e.track_count));
  html += '</div>';
  var raws = Array.isArray(e.raw_packets) ? e.raw_packets : [];
  html += '<div class="raw-title">原始包</div>';
  if(raws.length){
    raws.forEach(function(p, idx){
      p = p || {};
      html += '<div class="raw-meta">#'+(idx+1)+' ['+esc(String(p.capture_type || e.capture_type || '-'))+'] '+esc(String(p.ts || e.capture_time || '-'))+'</div>';
      html += '<pre class="raw-code">'+esc(String(p.hex || ''))+'</pre>';
    });
  } else {
    html += '<div class="raw-empty">暂无</div>';
  }
  return html;
}
function fmtDurSec(sec){
  if(sec==null || !isFinite(sec)) return '-';
  sec = Math.max(0, Math.round(Number(sec)||0));
  var d = Math.floor(sec / 86400); sec %= 86400;
  var h = Math.floor(sec / 3600); sec %= 3600;
  var m = Math.floor(sec / 60); sec %= 60;
  if(d) return d+'d'+h+'h';
  if(h) return h+'h'+m+'m';
  if(m) return m+'m'+sec+'s';
  return sec+'s';
}
function fmtAge(sec){
  if(sec==null || !isFinite(sec)) return '-';
  sec = Math.max(0, Math.round(Number(sec)||0));
  if(sec < 60) return sec + 's';
  if(sec < 3600) return Math.floor(sec / 60) + 'm';
  if(sec <= 216000) return Math.floor(sec / 3600) + 'h';
  return Math.floor(sec / 86400) + 'd';
}
function isSnSelected(sn){
  sn = String(sn || '');
  return !!selectedSnSet[sn];
}
function selectedSnList(){
  return Object.keys(selectedSnSet).filter(function(sn){ return !!selectedSnSet[sn]; });
}
async function ensureTrackLoaded(sn, force){
  sn = String(sn || '');
  if(!sn) return;
  if(trackLoading[sn]) return;
  if(trackCache[sn] && !force) return;
  trackLoading[sn] = true;
  try{
    var data = await getJson('/api/tracks/get?sn=' + encodeURIComponent(sn));
    var tr = Array.isArray(data.track) ? data.track : [];
    trackCache[sn] = tr;
    if(isSnSelected(sn)){
      updateMap(latestMapRows.length ? latestMapRows : (latestDroneRows || []));
    }
  }catch(_e){
    if(!trackCache[sn]) trackCache[sn] = [];
  }finally{
    delete trackLoading[sn];
  }
}
function syncSelectedFromRows(rows){
  // Keep historical selections across realtime updates.
  // Selected items are removed explicitly on user delete/clear actions.
  void(rows);
}
function setSnSelected(sn, on){
  sn = String(sn || '');
  if(!sn) return;
  if(on) selectedSnSet[sn] = true;
  else delete selectedSnSet[sn];
  if(on) ensureTrackLoaded(sn, false);
  syncTableSelectionUi();
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  updateMap(latestMapRows.length ? latestMapRows : (latestDroneRows || []));
}
function setAllVisibleSelected(on){
  var rows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
  rows.forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return;
    if(on){
      selectedSnSet[sn] = true;
      ensureTrackLoaded(sn, false);
    }else{
      delete selectedSnSet[sn];
    }
  });
  syncTableSelectionUi();
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  updateMap(latestMapRows.length ? latestMapRows : (latestDroneRows || []));
}
function esc(v){
  return String(v==null?'':v)
    .replace(/&/g,'&amp;')
    .replace(/</g,'&lt;')
    .replace(/>/g,'&gt;')
    .replace(/"/g,'&quot;')
    .replace(/'/g,'&#39;');
}
function escAttr(v){
  return esc(v).replace(/\\n/g,'&#10;');
}
function hideInfoCard(){
  var modal = qs('info-modal');
  if(!modal) return;
  modal.classList.remove('show');
}
function showInfoCard(msg, asHtml){
  var modal = qs('info-modal');
  var body = qs('info-card-body');
  if(!modal || !body) return;
  if(asHtml){
    body.innerHTML = String(msg || '');
  }else{
    body.textContent = String(msg || '无详情');
  }
  modal.classList.add('show');
}
function fieldKey(sn, field){ return String(sn||'') + '|' + String(field||''); }
function markFieldHighlight(sn, field, ms){
  var now = Date.now();
  droneFieldHl[fieldKey(sn, field)] = {start: now, end: now + (ms || HL_TOTAL_MS)};
}
function highlightAlpha(sn, field){
  var it = droneFieldHl[fieldKey(sn, field)];
  if(!it) return 0;
  var now = Date.now();
  var end = Number(it.end || 0);
  if(now >= end){
    delete droneFieldHl[fieldKey(sn, field)];
    return 0;
  }
  var start = Number(it.start || now);
  var t = Math.max(0, now - start);
  var fi = Math.max(0, Number(HL_FADE_IN_MS || 0));
  var ho = Math.max(0, Number(HL_HOLD_MS || 0));
  var fo = Math.max(0, Number(HL_FADE_OUT_MS || 0));
  if(fi > 0 && t <= fi){
    return Math.max(0, Math.min(1, t / fi));
  }
  if(t <= (fi + ho)){
    return 1;
  }
  var elapsedFo = t - fi - ho;
  if(fo <= 0){
    return 0;
  }
  if(elapsedFo >= fo){
    return 0;
  }
  return Math.max(0, 1 - (elapsedFo / fo));
}
function fieldCellAttrs(sn, field, extraCls){
  var cls = extraCls ? String(extraCls) : '';
  var attrs = ' data-hl-sn="'+escAttr(sn)+'" data-hl-field="'+escAttr(field)+'"';
  var a = highlightAlpha(sn, field);
  if(a <= 0){
    return (cls ? (' class="'+cls+'"') : '') + attrs;
  }
  cls = (cls ? (cls + ' ') : '') + 'hl';
  return ' class=\"'+cls+'\"'+attrs+' style=\"--hl-alpha:'+a.toFixed(3)+'\"';
}
function animateHighlightsStep(){
  var nodes = document.querySelectorAll('#tbody td[data-hl-sn][data-hl-field]');
  var active = false;
  for(var i=0;i<nodes.length;i++){
    var td = nodes[i];
    var sn = td.getAttribute('data-hl-sn') || '';
    var field = td.getAttribute('data-hl-field') || '';
    var a = highlightAlpha(sn, field);
    if(a > 0){
      active = true;
      if(!td.classList.contains('hl')) td.classList.add('hl');
      td.style.setProperty('--hl-alpha', a.toFixed(3));
    }else{
      if(td.classList.contains('hl')) td.classList.remove('hl');
      td.style.removeProperty('--hl-alpha');
    }
  }
  if(active){
    requestAnimationFrame(animateHighlightsStep);
  }else{
    highlightAnimRunning = false;
  }
}
function ensureHighlightAnimation(){
  if(highlightAnimRunning) return;
  highlightAnimRunning = true;
  requestAnimationFrame(animateHighlightsStep);
}
function syncFieldHighlights(list){
  var seen = {};
  (list || []).forEach(function(e){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    seen[sn] = true;
    var cur = {
      model: String(e.model || ''),
      rssi: String(e.rssi == null ? '' : e.rssi),
      pkts: String(e.pkts == null ? '' : e.pkts),
      dir: String(e.dir || ''),
      last_seen: String(e.last_seen || ''),
      last_pkt_time: String(e.last_pkt_time || e.capture_time || ''),
      age_text: String(e.age_text || fmtAge(e.age)),
      lat: String(e.lat == null ? '' : e.lat),
      lon: String(e.lon == null ? '' : e.lon),
      alt: String(e.alt == null ? '' : e.alt),
      spd: String(e.spd == null ? '' : e.spd),
      vspd: String(e.vspd == null ? '' : e.vspd)
    };
    var prev = droneFieldPrev[sn];
    if(prev){
      Object.keys(cur).forEach(function(k){
        if(prev[k] !== cur[k]) markFieldHighlight(sn, k, HL_TOTAL_MS);
      });
    }
    droneFieldPrev[sn] = cur;
  });
  Object.keys(droneFieldPrev).forEach(function(sn){
    if(!seen[sn]) delete droneFieldPrev[sn];
  });
}
function showBanner(text, kind, timeoutMs){
  var host = qs('banner-stack');
  if(!host){
    host = document.createElement('div');
    host.id = 'banner-stack';
    host.className = 'banner-stack';
    document.body.appendChild(host);
  }
  var node = document.createElement('div');
  node.className = 'banner ' + (kind || 'info');
  node.textContent = String(text || '');
  host.appendChild(node);
  setTimeout(function(){ node.classList.add('show'); }, 10);
  var ttl = Math.max(1200, Number(timeoutMs || 3200));
  setTimeout(function(){
    node.classList.remove('show');
    setTimeout(function(){ if(node.parentNode) node.parentNode.removeChild(node); }, 280);
  }, ttl);
}
function notifyBtnText(){
  if(!('Notification' in window)) return '\u7f51\u9875\u901a\u77e5(\u4e0d\u652f\u6301)';
  if(webNotifyEnabled && Notification.permission === 'granted') return '\u7f51\u9875\u901a\u77e5(\u5df2\u5f00)';
  if(Notification.permission === 'denied') return '\u7f51\u9875\u901a\u77e5(\u5df2\u62d2\u7edd)';
  return '\u7f51\u9875\u901a\u77e5';
}
function updateNotifyButton(){
  var btn = qs('btn-web-notify');
  if(!btn) return;
  btn.textContent = notifyBtnText();
  btn.disabled = !('Notification' in window) || Notification.permission === 'denied';
}
async function requestWebNotifyPermission(){
  if(!('Notification' in window)){
    showBanner('当前浏览器不支持网页通知', 'warn', 4200);
    return;
  }
  try{
    if(Notification.permission === 'granted'){
      webNotifyEnabled = true;
      updateNotifyButton();
      showBanner('网页通知已启用', 'ok', 2200);
      return;
    }
    var perm = await Notification.requestPermission();
    webNotifyEnabled = (perm === 'granted');
    updateNotifyButton();
    if(webNotifyEnabled){
      try{
        new Notification('RID Monitor 通知已启用', {body:'将推送飞机上下线事件'});
      }catch(_e){}
      showBanner('网页通知权限已授权', 'ok', 2400);
    } else if(perm === 'denied'){
      showBanner('网页通知权限被拒绝', 'warn', 4200);
    }
  }catch(_e){}
}
function pushWebNotification(title, body, tag){
  if(!webNotifyEnabled) return;
  if(!('Notification' in window) || Notification.permission !== 'granted') return;
  try{
    new Notification(title, {body: body || '', tag: tag || ('rid-'+Date.now())});
  }catch(_e){}
}
function handleDroneNotifications(list){
  var seen = {};
  var nowLabel = new Date().toLocaleTimeString();
  (list || []).forEach(function(e){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    seen[sn] = true;
    var isLost = !!e.lost;
    if(typeof droneStatePrev[sn] === 'undefined'){
      droneStatePrev[sn] = isLost;
      return;
    }
    if(droneStatePrev[sn] !== isLost){
      var title = isLost ? '\u98de\u673a\u4e0b\u7ebf' : '\u98de\u673a\u4e0a\u7ebf';
      var body = nowLabel + '  ' + sn + '\\n' + String(e.model || 'N/A') + '  ' +
        (e.rssi == null ? 'N/A' : (e.rssi + 'dBm'));
      pushWebNotification(title, body, 'rid-'+sn+'-'+(isLost?'off':'on'));
      showBanner(title + '  ' + sn, isLost ? 'warn' : 'ok', 2600);
    }
    droneStatePrev[sn] = isLost;
  });
  Object.keys(droneStatePrev).forEach(function(sn){
    if(!seen[sn]) delete droneStatePrev[sn];
  });
}
async function getJson(url){
  var resp = await fetch(url, {cache:'no-store'});
  var data = {};
  try{ data = await resp.json(); }catch(_e){}
  if(!resp.ok || data.ok===false){
    throw new Error((data && data.error) ? data.error : ('HTTP '+resp.status));
  }
  return data;
}
function loadThemePref(){
  try{
    var s = localStorage.getItem('rid_ui_theme');
    if(s === 'dark' || s === 'light') return s;
  }catch(_e){}
  try{
    if(window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches){
      return 'light';
    }
  }catch(_e){}
  return 'dark';
}
function applyTheme(theme){
  uiTheme = (theme === 'light') ? 'light' : 'dark';
  var light = (uiTheme === 'light');
  if(document.body){
    document.body.classList.toggle('theme-light', light);
    document.body.classList.toggle('theme-dark', !light);
  }
  try{ localStorage.setItem('rid_ui_theme', uiTheme); }catch(_e){}
  var btn = qs('btn-theme');
  if(btn){
    btn.textContent = light ? '\u6df1\u8272' : '\u6d45\u8272';
    btn.title = light ? '\u5207\u6362\u4e3a\u6df1\u8272' : '\u5207\u6362\u4e3a\u6d45\u8272';
  }
}
function toggleTheme(){
  applyTheme(uiTheme === 'light' ? 'dark' : 'light');
}
async function postJson(url, body){
  var resp = await fetch(url, {
    method:'POST',
    headers:{'Content-Type':'application/json'},
    body: JSON.stringify(body||{})
  });
  var data = {};
  try{ data = await resp.json(); }catch(_e){}
  if(!resp.ok || data.ok===false){
    throw new Error((data && data.error) ? data.error : ('HTTP '+resp.status));
  }
  return data;
}

async function loadIfaceOptions(force){
  if(ifaceOptionsLoaded && !force) return;
  var sel = qs('iface-select');
  var st = qs('iface-status');
  if(!sel) return;
  try{
    var data = await getJson('/api/interfaces');
    var items = Array.isArray(data.items) ? data.items : [];
    var html = '<option value="">(auto)</option>';
    items.forEach(function(it){
      it = it || {};
      var name = String(it.name || '');
      if(!name) return;
      var mode = String(it.mode || '');
      var s5 = it.supports_5g ? '5G' : '2.4G';
      var lb = name + (mode ? (' ['+mode+']') : '') + ' ' + s5;
      html += '<option value=\"'+escAttr(name)+'\">'+esc(lb)+'</option>';
    });
    sel.innerHTML = html;
    var chosen = (metaState && metaState.iface_selected!=null) ? String(metaState.iface_selected) : String(data.selected_iface || '');
    if(chosen) sel.value = chosen;
    var chk = qs('scan-wifi-fast');
    if(chk && !chk.dataset.edited){
      chk.checked = !!(metaState && metaState.scan_wifi_fast);
      if(typeof data.scan_wifi_fast !== 'undefined') chk.checked = !!data.scan_wifi_fast;
    }
    if(st){
      var active = String((metaState && metaState.sniff_iface) || data.active_iface || '-');
      st.textContent = '当前采集网卡: ' + active;
    }
    ifaceOptionsLoaded = true;
  }catch(e){
    if(st) st.textContent = '网卡加载失败: ' + ((e && e.message) ? e.message : e);
  }
}

function setFreezeState(frozen){
  uiFrozen = !!frozen;
  var btn = qs('btn-freeze');
  if(btn){
    btn.textContent = uiFrozen ? '\u6062\u590d\u540c\u6b65' : '\u51bb\u7ed3\u5217\u8868';
    btn.classList.toggle('warn', uiFrozen);
  }
}

function toggleFreeze(){
  if(!uiFrozen){
    frozenPendingData = null;
    setFreezeState(true);
    return;
  }
  setFreezeState(false);
  if(frozenPendingData){
    var d = frozenPendingData;
    frozenPendingData = null;
    onData(d);
  }
}

function setLogPanelCollapsed(collapsed){
  var panel = qs('log-panel');
  if(!panel) return;
  if(collapsed) panel.classList.add('collapsed');
  else panel.classList.remove('collapsed');
  var btn = qs('log-panel-toggle');
  if(btn) btn.textContent = collapsed ? '\u5c55\u5f00' : '\u6536\u8d77';
  syncBottomPanelLayout();
}

function toggleLogPanel(){
  var panel = qs('log-panel');
  if(!panel) return;
  setLogPanelCollapsed(!panel.classList.contains('collapsed'));
}

function setMapPanelCollapsed(collapsed){
  var panel = qs('map-panel');
  if(!panel) return;
  if(collapsed) panel.classList.add('collapsed');
  else panel.classList.remove('collapsed');
  var btn = qs('map-panel-toggle');
  if(btn) btn.textContent = collapsed ? '\u5c55\u5f00' : '\u6536\u8d77';
  syncBottomPanelLayout();
  if(!collapsed && map){
    setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 0);
  }
}

function toggleMapPanel(){
  var panel = qs('map-panel');
  if(!panel) return;
  setMapPanelCollapsed(!panel.classList.contains('collapsed'));
}

function setApPanelCollapsed(collapsed){
  var panel = qs('ap-panel');
  if(!panel) return;
  if(collapsed) panel.classList.add('collapsed');
  else panel.classList.remove('collapsed');
  var btn = qs('ap-panel-toggle');
  if(btn) btn.textContent = collapsed ? '\u5c55\u5f00' : '\u6536\u8d77';
  syncBottomPanelLayout();
}

function toggleApPanel(){
  var panel = qs('ap-panel');
  if(!panel) return;
  setApPanelCollapsed(!panel.classList.contains('collapsed'));
}

function syncBottomPanelLayout(){
  var bottom = document.querySelector('.bottom');
  if(!bottom) return;
  var mapPanel = qs('map-panel');
  var logPanel = qs('log-panel');
  var apPanel = qs('ap-panel');
  var mapCollapsed = !!(mapPanel && mapPanel.classList.contains('collapsed'));
  var logCollapsed = !!(logPanel && logPanel.classList.contains('collapsed'));
  var apCollapsed = !!(apPanel && apPanel.classList.contains('collapsed'));
  var allCollapsed = mapCollapsed && logCollapsed && apCollapsed;
  bottom.classList.toggle('map-collapsed', mapCollapsed);
  bottom.classList.toggle('log-collapsed', logCollapsed);
  bottom.classList.toggle('ap-collapsed', apCollapsed);
  bottom.classList.toggle('all-collapsed', allCollapsed);
  document.body.classList.toggle('bottom-all-collapsed', allCollapsed);
  if(map && !mapCollapsed && !allCollapsed){
    setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 0);
  }
}

function isMapFullscreen(){
  var panel = qs('map-panel');
  var fe = document.fullscreenElement || document.webkitFullscreenElement || document.msFullscreenElement || null;
  return !!(panel && fe && (fe === panel || panel.contains(fe)));
}

function ensureMapMiniList(){
  var panel = qs('map-panel');
  if(!panel) return null;
  var box = qs('map-mini-list');
  if(!box){
    box = document.createElement('div');
    box.id = 'map-mini-list';
    box.className = 'map-mini-list';
    panel.appendChild(box);
  }
  return box;
}

function updateMapFullscreenButton(){
  var btn = qs('btn-map-fullscreen');
  if(!btn) return;
  btn.textContent = isMapFullscreen() ? '退出全屏' : '全屏';
}

function syncMapFullscreenUi(){
  var panel = qs('map-panel');
  var entering = isMapFullscreen();
  ensureMapMiniList();
  if(panel){
    panel.classList.toggle('fullscreen', entering);
    if(entering && panel.classList.contains('collapsed')){
      setMapPanelCollapsed(false);
    }
    if(!entering && mapCollapsedBeforeFullscreen === true){
      setMapPanelCollapsed(true);
    }
  }
  if(!entering) mapCollapsedBeforeFullscreen = null;
  updateMapFullscreenButton();
  renderMapMiniList(latestDroneRows);
  if(map){
    setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 0);
  }
}

async function toggleMapFullscreen(){
  var panel = qs('map-panel');
  if(!panel) return;
  try{
    if(isMapFullscreen()){
      if(document.exitFullscreen) await document.exitFullscreen();
      else if(document.webkitExitFullscreen) document.webkitExitFullscreen();
    }else{
      mapCollapsedBeforeFullscreen = panel.classList.contains('collapsed');
      if(mapCollapsedBeforeFullscreen){
        setMapPanelCollapsed(false);
      }
      if(panel.requestFullscreen) await panel.requestFullscreen();
      else if(panel.webkitRequestFullscreen) panel.webkitRequestFullscreen();
    }
    if(mapFsUiTimer){
      clearInterval(mapFsUiTimer);
      mapFsUiTimer = null;
    }
    var tries = 0;
    mapFsUiTimer = setInterval(function(){
      syncMapFullscreenUi();
      tries += 1;
      if(tries >= 24){
        clearInterval(mapFsUiTimer);
        mapFsUiTimer = null;
      }
    }, 80);
  }catch(e){
    showBanner('全屏切换失败: ' + ((e && e.message) ? e.message : e), 'warn', 3200);
  }
}

document.addEventListener('fullscreenchange', syncMapFullscreenUi);
document.addEventListener('webkitfullscreenchange', syncMapFullscreenUi);
document.addEventListener('msfullscreenchange', syncMapFullscreenUi);

function renderMapMiniList(list){
  var box = ensureMapMiniList();
  if(!box) return;
  var panel = qs('map-panel');
  var show = isMapFullscreen() || !!(panel && panel.classList && panel.classList.contains('fullscreen'));
  box.style.display = show ? 'block' : '';
  var rows = (Array.isArray(list) ? list : []).slice().filter(function(e){
    return !!String((e && e.sn) || '');
  });
  rows.sort(function(a,b){
    return String(a.sn || '').localeCompare(String(b.sn || ''));
  });
  var snSig = rows.map(function(e){ return String(e.sn || ''); }).join('|');
  var selSig = selectedSnList().slice().sort().join('|');
  var sig = snSig + '::' + selSig + '::' + (show ? '1' : '0');
  if(sig === miniListRenderSig){
    return;
  }
  miniListRenderSig = sig;
  if(!rows.length){
    box.innerHTML = '<div class="mini-title">暂无飞机</div>';
    return;
  }
  var html = '<div class="mini-title">轨迹选择（勾选后显示飞手与轨迹）</div>';
  rows.forEach(function(e, idx){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    var checked = isSnSelected(sn) ? ' checked' : '';
    html += '<label class="mini-item"><input class="mini-sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+checked+'>'+
      '<span class="mono">#'+(idx+1)+'</span><span class="sn" title="'+esc(sn)+'">'+esc(sn)+'</span></label>';
  });
  box.innerHTML = html;
  var cbs = box.querySelectorAll('.mini-sel-sn');
  for(var i=0;i<cbs.length;i++){
    cbs[i].addEventListener('change', function(ev){
      var sn = ev.target.getAttribute('data-sn') || '';
      setSnSelected(sn, !!ev.target.checked);
      syncTableSelectionUi();
    });
  }
}

function refreshTrackMgrOptions(list){
  var sel = qs('track-sn-select');
  if(!sel) return;
  var rows = Array.isArray(list) ? list : [];
  var cur = String(sel.value || '');
  var html = '<option value="">请选择飞机</option>';
  rows.forEach(function(e){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    var model = String(e.model || 'N/A');
    var cnt = Number(e.track_count || 0);
    var t = String(e.last_seen || '-');
    html += '<option value="'+escAttr(sn)+'">'+esc(sn+' | '+model+' | 轨迹'+cnt+'点 | 末次'+t)+'</option>';
  });
  sel.innerHTML = html;
  if(cur && rows.some(function(e){ return String((e && e.sn) || '') === cur; })){
    sel.value = cur;
  }
}

function syncTableSelectionUi(){
  var cbs = document.querySelectorAll('#tbody .sel-sn');
  var total = 0;
  var checked = 0;
  for(var i=0;i<cbs.length;i++){
    var sn = String(cbs[i].getAttribute('data-sn') || '');
    cbs[i].checked = isSnSelected(sn);
    total += 1;
    if(cbs[i].checked) checked += 1;
  }
  var allCb = qs('sel-all');
  if(allCb){
    allCb.disabled = (total === 0);
    allCb.checked = (total > 0 && checked === total);
    allCb.indeterminate = (checked > 0 && checked < total);
  }
}

function buildExtraUi(){
  if(window.__ridExtraUiReady) return;
  window.__ridExtraUiReady = true;

  if(!qs('info-modal')){
    var modal = document.createElement('div');
    modal.id = 'info-modal';
    modal.className = 'info-modal';
    modal.innerHTML =
      '<div class="info-card" role="dialog" aria-modal="true" aria-label="\u8be6\u60c5\u4fe1\u606f">'+
      '  <div class="info-card-hd"><span>详情信息</span><button id="info-card-close" class="info-card-close" type="button" title="关闭">×</button></div>'+
      '  <div id="info-card-body" class="info-card-body"></div>'+
      '</div>';
    document.body.appendChild(modal);
    modal.addEventListener('click', function(ev){
      if(ev.target === modal) hideInfoCard();
    });
  }
  if(qs('info-card-close')) qs('info-card-close').addEventListener('click', hideInfoCard);
  if(!infoCardEscBound){
    document.addEventListener('keydown', function(ev){
      if(ev && ev.key === 'Escape') hideInfoCard();
    });
    infoCardEscBound = true;
  }

  var clearBtn = qs('btn-clear-history');
  if(clearBtn && !qs('sniff-state')){
    var sniffStat = document.createElement('span');
    sniffStat.className = 'stat snf';
    sniffStat.innerHTML = '\u91c7\u96c6 <b id="sniff-state" class="warn">-</b>';
    clearBtn.parentNode.insertBefore(sniffStat, clearBtn);
  }
  if(clearBtn && !qs('btn-theme')){
    var themeBtn = document.createElement('button');
    themeBtn.className = 'btn-mini';
    themeBtn.id = 'btn-theme';
    themeBtn.type = 'button';
    themeBtn.textContent = '\u6d45\u8272';
    clearBtn.parentNode.insertBefore(themeBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-dji-lookup')){
    var djiBtn = document.createElement('button');
    djiBtn.className = 'btn-mini';
    djiBtn.id = 'btn-dji-lookup';
    djiBtn.type = 'button';
    djiBtn.textContent = 'DJI\u67e5\u8be2';
    clearBtn.parentNode.insertBefore(djiBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-freeze')){
    var freezeBtn = document.createElement('button');
    freezeBtn.className = 'btn-mini';
    freezeBtn.id = 'btn-freeze';
    freezeBtn.type = 'button';
    freezeBtn.textContent = '\u51bb\u7ed3\u5217\u8868';
    clearBtn.parentNode.insertBefore(freezeBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-web-notify')){
    var notifyBtn = document.createElement('button');
    notifyBtn.className = 'btn-mini';
    notifyBtn.id = 'btn-web-notify';
    notifyBtn.type = 'button';
    notifyBtn.textContent = '\u7f51\u9875\u901a\u77e5';
    clearBtn.parentNode.insertBefore(notifyBtn, clearBtn);
  }

  var header = document.querySelector('header');
  if(header && !qs('sniff-banner')){
    var banner = document.createElement('div');
    banner.id = 'sniff-banner';
    banner.className = 'sniff-banner';
    header.appendChild(banner);
  }
  if(header && !qs('adv-panel')){
    var details = document.createElement('details');
    details.className = 'adv';
    details.id = 'adv-panel';
    details.innerHTML =
      '<summary>\u9ad8\u7ea7\u9009\u9879</summary>'+
      '<div class="adv-body">'+
      '  <div class="adv-col">'+
      '    <div class="adv-row">'+
      '      <label for="restart-args">\u53c2\u6570</label>'+
      '      <input id="restart-args" class="adv-input" type="text" placeholder="\u4f8b\u5982: --no-tui --channel 6">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="iface-select">\u7f51\u5361</label>'+
      '      <select id="iface-select" class="adv-input"><option value="">(auto)</option></select>'+
      '      <button class="btn-mini" id="btn-iface-refresh" type="button">\u5237\u65b0\u7f51\u5361</button>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label><input id="scan-wifi-fast" type="checkbox"> \u626b\u63cfWiFi\u5feb\u4f20(5GHz\u5e38\u89c1\u4fe1\u9053)</label>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-name">\u57fa\u7ad9\u540d\u79f0</label>'+
      '      <input id="base-name" class="adv-input" type="text" placeholder="\u4f8b\u5982: \u57fa\u7ad9A">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-lat">\u57fa\u7ad9\u7eac\u5ea6</label>'+
      '      <input id="base-lat" class="adv-input" type="text" inputmode="decimal" placeholder="\u4f8b\u5982: 30.0678192">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-lon">\u57fa\u7ad9\u7ecf\u5ea6</label>'+
      '      <input id="base-lon" class="adv-input" type="text" inputmode="decimal" placeholder="\u4f8b\u5982: 121.1854406">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-zoom">\u57fa\u7ad9\u7f29\u653e</label>'+
      '      <input id="base-zoom" class="adv-input" type="number" min="3" max="19" step="1" placeholder="13">'+
      '      <button class="btn-mini" id="btn-base-save" type="button">\u4fdd\u5b58\u57fa\u7ad9</button>'+
      '    </div>'+
      '    <div class="adv-note" id="base-status">-</div>'+
      '    <div class="adv-note" id="iface-status">-</div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-restart-once" type="button">\u4ec5\u672c\u6b21\u91cd\u542f</button>'+
      '      <button class="btn-mini warn" id="btn-restart-save" type="button">\u4fdd\u5b58\u5e76\u91cd\u542f</button>'+
      '    </div>'+
      '    <div class="adv-note">DJI\u5730\u5740: <code id="dji-url-text">-</code></div>'+
      '    <div class="adv-note">\u5f53\u524d\u53c2\u6570: <code id="restart-current-args">-</code></div>'+
      '    <div class="adv-note">\u5df2\u4fdd\u5b58\u53c2\u6570: <code id="restart-saved-args">-</code></div>'+
      '  </div>'+
      '  <div class="adv-col">'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-config-load" type="button">\u8bfb\u53d6\u914d\u7f6e</button>'+
      '      <button class="btn-mini" id="btn-config-save" type="button">\u4fdd\u5b58\u5e76\u70ed\u91cd\u8f7d</button>'+
      '    </div>'+
      '    <div class="adv-note" id="config-editor-status">-</div>'+
      '    <textarea id="config-editor" class="cfg-editor" spellcheck="false" placeholder="\u5728\u8fd9\u91cc\u7f16\u8f91 rid_config.json"></textarea>'+
      '    <div class="adv-row">'+
      '      <label for="track-sn-select">\u5386\u53f2/\u8f68\u8ff9</label>'+
      '      <select id="track-sn-select" class="adv-input"><option value="">\u8bf7\u9009\u62e9\u98de\u673a</option></select>'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini warn" id="btn-history-delete" type="button">\u5220\u9664\u8be5\u98de\u673a</button>'+
      '      <button class="btn-mini" id="btn-track-clear-one" type="button">\u6e05\u7a7a\u8be5\u673a\u8f68\u8ff9</button>'+
      '      <button class="btn-mini warn" id="btn-track-clear-all" type="button">\u6e05\u7a7a\u5168\u90e8\u8f68\u8ff9</button>'+
      '    </div>'+
      '    <div class="adv-note">TOOLS</div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-tools-export-all" type="button">\u5bfc\u51fa\u5168\u90e8\u8be6\u60c5</button>'+
      '      <button class="btn-mini" id="btn-tools-import-all" type="button">\u5bfc\u5165\u5168\u90e8\u8be6\u60c5</button>'+
      '      <input id="tools-import-all-file" type="file" accept=".json,application/json" style="display:none">'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-tools-export-track" type="button">\u5bfc\u51fa\u5355\u673a\u8f68\u8ff9</button>'+
      '      <button class="btn-mini" id="btn-tools-import-track" type="button">\u5bfc\u5165\u5355\u673a\u8f68\u8ff9</button>'+
      '      <input id="tools-import-track-file" type="file" accept=".json,application/json" style="display:none">'+
      '    </div>'+
      '    <div class="adv-note" id="tools-status">-</div>'+
      '    <div class="adv-note" id="track-mgr-status">-</div>'+
      '  </div>'+
      '</div>';
    header.appendChild(details);
  }

  var bottom = document.querySelector('.bottom');
  if(bottom && !qs('aplist')){
    var panel = document.createElement('div');
    panel.className = 'panel ap-panel';
    panel.innerHTML =
      '<div class="panel-hdr">&#x1F4CB; \u5b9e\u65f6AP\u5217\u8868 <span class="sub" id="ap-list-count">0</span></div>'+
      '<div class="aplist" id="aplist"></div>';
    bottom.appendChild(panel);
  }
  if(!qs('bottom-restore')){
    var restoreBtn = document.createElement('button');
    restoreBtn.className = 'btn-mini';
    restoreBtn.id = 'bottom-restore';
    restoreBtn.type = 'button';
    restoreBtn.textContent = '\u5c55\u5f00\u5e95\u90e8\u9762\u677f';
    restoreBtn.addEventListener('click', function(){
      setMapPanelCollapsed(false);
      setLogPanelCollapsed(false);
      setApPanelCollapsed(false);
      syncBottomPanelLayout();
    });
    document.body.appendChild(restoreBtn);
  }

  var mapEl = qs('map');
  if(mapEl){
    var mapPanel = mapEl.closest ? mapEl.closest('.panel') : null;
    if(mapPanel){
      mapPanel.id = 'map-panel';
      mapPanel.classList.add('map-panel', 'collapsible');
      var mapHdr = mapPanel.querySelector('.panel-hdr');
      if(mapHdr && !qs('map-panel-toggle')){
        var mapActions = document.createElement('div');
        mapActions.className = 'hdr-actions';
        var hint = mapHdr.querySelector('#map-hint');
        if(hint) mapActions.appendChild(hint);
        var fsBtn = document.createElement('button');
        fsBtn.className = 'btn-mini';
        fsBtn.id = 'btn-map-fullscreen';
        fsBtn.type = 'button';
        fsBtn.textContent = '全屏';
        fsBtn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleMapFullscreen(); });
        mapActions.appendChild(fsBtn);
        var mapBtn = document.createElement('button');
        mapBtn.className = 'btn-mini';
        mapBtn.id = 'map-panel-toggle';
        mapBtn.type = 'button';
        mapBtn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleMapPanel(); });
        mapActions.appendChild(mapBtn);
        mapHdr.appendChild(mapActions);
        mapHdr.style.cursor = 'pointer';
        mapHdr.addEventListener('click', function(ev){
          var t = ev.target;
          if(t && t.closest && t.closest('button')) return;
          toggleMapPanel();
        });
      }
      ensureMapMiniList();
      setMapPanelCollapsed(false);
    }
  }

  var logBox = qs('logbox');
  if(logBox){
    var logPanel = logBox.closest ? logBox.closest('.panel') : null;
    if(logPanel){
      logPanel.id = 'log-panel';
      logPanel.classList.add('log-panel', 'collapsible');
      var hdr = logPanel.querySelector('.panel-hdr');
      if(hdr && !qs('log-panel-toggle')){
        var actions = document.createElement('div');
        actions.className = 'hdr-actions';
        var label = hdr.querySelector('label');
        if(label) actions.appendChild(label);
        var btn = document.createElement('button');
        btn.className = 'btn-mini';
        btn.id = 'log-panel-toggle';
        btn.type = 'button';
        btn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleLogPanel(); });
        actions.appendChild(btn);
        hdr.appendChild(actions);
        hdr.style.cursor = 'pointer';
        hdr.addEventListener('click', function(ev){
          var t = ev.target;
          if(t && t.closest && t.closest('input,label,button')) return;
          toggleLogPanel();
        });
      }
      setLogPanelCollapsed(true);
    }
  }
  var apBox = qs('aplist');
  if(apBox){
    var apPanel = apBox.closest ? apBox.closest('.panel') : null;
    if(apPanel){
      apPanel.id = 'ap-panel';
      apPanel.classList.add('ap-panel', 'collapsible');
      var apHdr = apPanel.querySelector('.panel-hdr');
      if(apHdr && !qs('ap-panel-toggle')){
        var apActions = document.createElement('div');
        apActions.className = 'hdr-actions';
        var apBtn = document.createElement('button');
        apBtn.className = 'btn-mini';
        apBtn.id = 'ap-panel-toggle';
        apBtn.type = 'button';
        apBtn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleApPanel(); });
        apActions.appendChild(apBtn);
        apHdr.appendChild(apActions);
        apHdr.style.cursor = 'pointer';
        apHdr.addEventListener('click', function(ev){
          var t = ev.target;
          if(t && t.closest && t.closest('button')) return;
          toggleApPanel();
        });
      }
      setApPanelCollapsed(false);
    }
  }
  syncBottomPanelLayout();

  if(qs('btn-clear-history')) qs('btn-clear-history').addEventListener('click', clearHistory);
  if(qs('btn-theme')) qs('btn-theme').addEventListener('click', toggleTheme);
  if(qs('btn-dji-lookup')) qs('btn-dji-lookup').addEventListener('click', openDjiLookup);
  if(qs('btn-freeze')) qs('btn-freeze').addEventListener('click', toggleFreeze);
  if(qs('btn-web-notify')) qs('btn-web-notify').addEventListener('click', requestWebNotifyPermission);
  if(qs('btn-restart-once')) qs('btn-restart-once').addEventListener('click', function(){ restartProgram(false); });
  if(qs('btn-restart-save')) qs('btn-restart-save').addEventListener('click', function(){ restartProgram(true); });
  if(qs('btn-config-load')) qs('btn-config-load').addEventListener('click', loadConfigEditor);
  if(qs('btn-config-save')) qs('btn-config-save').addEventListener('click', saveConfigEditor);
  if(qs('btn-history-delete')) qs('btn-history-delete').addEventListener('click', deleteHistoryBySelect);
  if(qs('btn-track-clear-one')) qs('btn-track-clear-one').addEventListener('click', clearTrackBySelect);
  if(qs('btn-track-clear-all')) qs('btn-track-clear-all').addEventListener('click', clearTrackAll);
  if(qs('btn-iface-refresh')) qs('btn-iface-refresh').addEventListener('click', function(){ loadIfaceOptions(true); });
  if(qs('iface-select')) qs('iface-select').addEventListener('change', function(){ this.dataset.edited='1'; });
  if(qs('scan-wifi-fast')) qs('scan-wifi-fast').addEventListener('change', function(){ this.dataset.edited='1'; });
  if(qs('restart-args')) qs('restart-args').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-name')) qs('base-name').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-lat')) qs('base-lat').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-lon')) qs('base-lon').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-zoom')) qs('base-zoom').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('btn-base-save')) qs('btn-base-save').addEventListener('click', saveBaseConfig);
  if(qs('sel-all')) qs('sel-all').addEventListener('change', function(ev){ setAllVisibleSelected(!!(ev && ev.target && ev.target.checked)); });
  if(qs('tbody')) qs('tbody').addEventListener('click', function(ev){
    var cb = ev.target && ev.target.closest ? ev.target.closest('.sel-sn') : null;
    if(cb){
      ev.stopPropagation();
      var snCb = cb.getAttribute('data-sn') || '';
      setSnSelected(snCb, !!cb.checked);
      return;
    }
    var btn = ev.target && ev.target.closest ? ev.target.closest('.copy-sn') : null;
    if(btn){
      ev.stopPropagation();
      copySn(btn.getAttribute('data-sn') || '');
      return;
    }
    var tr = ev.target && ev.target.closest ? ev.target.closest('tr[data-sn]') : null;
    if(tr){
      var sn = tr.getAttribute('data-sn') || '';
      var e = latestDroneMap[sn];
      if(e) showInfoCard(buildInfoHtml(e), true);
    }
  });
  applyTheme(uiTheme);
  if(('Notification' in window) && Notification.permission === 'granted'){
    webNotifyEnabled = true;
  }
  updateNotifyButton();
  loadConfigEditor();
  loadIfaceOptions(false);
  setFreezeState(false);
  updateMapFullscreenButton();
  renderMapMiniList([]);
}

function applyMeta(meta){
  metaState = (meta && typeof meta === 'object') ? meta : {};
  var djiUrl = String(metaState.dji_lookup_url || '');
  var allowRestart = metaState.allow_restart !== false;
  if(qs('dji-url-text')) qs('dji-url-text').textContent = djiUrl || '-';
  if(qs('restart-current-args')) qs('restart-current-args').textContent = String(metaState.restart_args_current || '-');
  if(qs('restart-saved-args')) qs('restart-saved-args').textContent = String(metaState.restart_args_saved || '-');
  if(qs('btn-dji-lookup')) qs('btn-dji-lookup').disabled = !djiUrl;
  if(qs('btn-restart-once')) qs('btn-restart-once').disabled = restartBusy || !allowRestart;
  if(qs('btn-restart-save')) qs('btn-restart-save').disabled = restartBusy || !allowRestart;
  var input = qs('restart-args');
  if(input && !input.dataset.edited){
    var preset = String(metaState.restart_args_saved || metaState.restart_args_current || '');
    input.value = preset;
  }
  var ifaceSel = qs('iface-select');
  if(ifaceSel && !ifaceSel.dataset.edited){
    var ifaceVal = metaState.iface_selected;
    if(ifaceVal == null || ifaceVal === '') ifaceVal = '';
    ifaceSel.value = String(ifaceVal);
  }
  var scanFast = qs('scan-wifi-fast');
  if(scanFast && !scanFast.dataset.edited){
    scanFast.checked = !!metaState.scan_wifi_fast;
  }
  var baseNameInput = qs('base-name');
  if(baseNameInput && !baseNameInput.dataset.edited){
    baseNameInput.value = String(metaState.base_name || '\u57fa\u7ad9');
  }
  var baseLatInput = qs('base-lat');
  if(baseLatInput && !baseLatInput.dataset.edited){
    baseLatInput.value = (metaState.base_lat==null) ? '' : String(metaState.base_lat);
  }
  var baseLonInput = qs('base-lon');
  if(baseLonInput && !baseLonInput.dataset.edited){
    baseLonInput.value = (metaState.base_lon==null) ? '' : String(metaState.base_lon);
  }
  var baseZoomInput = qs('base-zoom');
  if(baseZoomInput && !baseZoomInput.dataset.edited){
    var bz = intOrDefault(metaState.base_zoom, 13);
    baseZoomInput.value = String(Math.max(3, Math.min(19, bz)));
  }
  var baseCfg = baseFromMeta(metaState);
  var baseStatus = qs('base-status');
  if(baseStatus){
    if(baseCfg.ok){
      baseStatus.textContent = '\u57fa\u7ad9: ' + baseCfg.name + ' (' + baseCfg.lat.toFixed(6) + ', ' + baseCfg.lon.toFixed(6) + ') z' + baseCfg.zoom;
    } else {
      baseStatus.textContent = '\u57fa\u7ad9\u672a\u914d\u7f6e';
    }
  }
  var newBaseSig = baseSignature(metaState);
  if(applyMeta.__baseSig !== newBaseSig){
    applyMeta.__baseSig = newBaseSig;
    if(map){
      map._rid_base_fitted = false;
      applyBaseMarker(false);
      if(baseCfg.ok){
        map.setView([baseCfg.lat, baseCfg.lon], baseCfg.zoom);
        map._rid_base_fitted = true;
      }
    }
  }
  var ifaceStatus = qs('iface-status');
  if(ifaceStatus){
    var activeIface = String(metaState.sniff_iface || '-');
    var extra = '';
    if(!!metaState.scan_wifi_fast){
      var supported = metaState.wifi_fast_supported;
      if(supported === false) extra = ' | 5GHz不支持';
      else if(supported === true) extra = ' | 5GHz可用';
      if(metaState.wifi_fast_msg) extra += ' | ' + String(metaState.wifi_fast_msg);
    }
    ifaceStatus.textContent = '当前采集网卡: ' + activeIface + extra;
  }
  if(!!metaState.scan_wifi_fast && metaState.wifi_fast_supported === false){
    var warnMsg = String(metaState.wifi_fast_msg || '网卡不支持5GHz，WiFi快传扫描不可用');
    if(applyMeta.__fastWarn !== warnMsg){
      showBanner(warnMsg, 'warn', 4200);
      applyMeta.__fastWarn = warnMsg;
    }
  }
  updateNotifyButton();
  applySniffStatus(metaState);
}

function applySniffStatus(meta){
  var state = String((meta && meta.sniff_state) || 'warn');
  var msg = String((meta && meta.sniff_msg) || '');
  var iface = String((meta && meta.sniff_iface) || '');
  var idle = Number((meta && meta.sniff_idle_sec) || 0);
  var lastPkt = String((meta && meta.sniff_last_pkt) || '-');

  var badge = qs('sniff-state');
  if(badge){
    badge.classList.remove('ok','warn','err');
    if(state === 'ok'){
      badge.classList.add('ok');
      badge.textContent = '\u6b63\u5e38';
    } else if(state === 'error'){
      badge.classList.add('err');
      badge.textContent = '\u5f02\u5e38';
    } else {
      badge.classList.add('warn');
      badge.textContent = '\u8b66\u544a';
    }
  }

  var banner = qs('sniff-banner');
  if(!banner) return;
  if(state === 'ok'){
    banner.style.display = 'none';
    banner.textContent = '';
    banner.className = 'sniff-banner';
    sniffBannerPrevState = state;
    return;
  }
  var tip = (state === 'error' ? '\u91c7\u96c6\u5f02\u5e38\uff1a' : '\u91c7\u96c6\u544a\u8b66\uff1a') + (msg || '\u672a\u77e5');
  if(iface) tip += ' [iface: '+iface+']';
  if(idle > 0) tip += ' (' + Math.round(idle) + 's)';
  if(lastPkt && lastPkt !== '-') tip += '  \u4e0a\u6b21\u5e27: ' + lastPkt;
  banner.textContent = tip;
  banner.className = 'sniff-banner ' + (state === 'error' ? 'error' : 'warn');
  banner.style.display = 'block';
  if(state !== sniffBannerPrevState){
    showBanner(tip, state === 'error' ? 'warn' : 'info', 4200);
    sniffBannerPrevState = state;
  }
}

function openDjiLookup(){
  var url = String(metaState.dji_lookup_url || '');
  if(!url){
    alert('\u672a\u914d\u7f6eDJI\u67e5\u8be2\u5730\u5740');
    return;
  }
  var mobile = false;
  try { mobile = window.matchMedia('(max-width: 900px)').matches; } catch(_e) {}
  if(mobile){
    window.open(url, '_blank', 'noopener,noreferrer');
  } else {
    window.open(url, 'dji_lookup_window', 'noopener,noreferrer,width=1180,height=820');
  }
}

async function copyText(text){
  if(!text) return false;
  try{
    if(navigator.clipboard && navigator.clipboard.writeText){
      await navigator.clipboard.writeText(text);
      return true;
    }
  }catch(_e){}
  var ta = document.createElement('textarea');
  ta.value = text;
  ta.setAttribute('readonly', 'readonly');
  ta.style.position = 'fixed';
  ta.style.opacity = '0';
  document.body.appendChild(ta);
  ta.select();
  var ok = false;
  try{ ok = document.execCommand('copy'); }catch(_e){}
  document.body.removeChild(ta);
  return ok;
}

async function copySn(sn){
  if(!sn) return;
  var ok = await copyText(sn);
  var btn = null;
  if(window.CSS && CSS.escape){
    try{ btn = document.querySelector('.copy-sn[data-sn="'+CSS.escape(sn)+'"]'); }catch(_e){}
  }
  if(!btn){
    var all = document.querySelectorAll('.copy-sn');
    for(var i=0;i<all.length;i++){
      if((all[i].getAttribute('data-sn')||'') === sn){ btn = all[i]; break; }
    }
  }
  if(btn){
    var old = btn.textContent;
    btn.classList.add('done');
    btn.textContent = ok ? '\u5df2' : '!';
    setTimeout(function(){ btn.classList.remove('done'); btn.textContent = old; }, 1200);
  }
}

async function clearHistory(){
  if(clearHistoryBusy) return;
  if(!confirm('\u6e05\u7a7a\u5386\u53f2\u65e0\u4eba\u673a\u8bb0\u5f55\uff0c\u5e76\u5220\u9664\u672c\u5730\u7f13\u5b58\u6587\u4ef6\uff1f')) return;
  var btn = qs('btn-clear-history');
  clearHistoryBusy = true;
  if(btn){ btn.disabled = true; btn.textContent = '\u6e05\u7a7a\u4e2d...'; }
  try{
    var data = await postJson('/api/history/clear', {});
    selectedSnSet = {};
    trackCache = {};
    showBanner('历史已清空' + (typeof data.cleared==='number' ? ('（'+data.cleared+'架）') : ''), 'ok', 2600);
  }catch(e){
    showBanner('清空失败: ' + ((e && e.message) ? e.message : e), 'warn', 4200);
  }finally{
    if(btn){ btn.disabled = false; btn.textContent = '\u6e05\u7a7a\u5386\u53f2'; }
    clearHistoryBusy = false;
  }
}

async function deleteHistoryBySelect(){
  var sel = qs('track-sn-select');
  var st = qs('track-mgr-status');
  var sn = sel ? String(sel.value || '').trim() : '';
  if(!sn){
    if(st) st.textContent = '请先选择飞机';
    return;
  }
  if(!confirm('删除该飞机历史记录？\\n' + sn)) return;
  if(st) st.textContent = '删除中...';
  try{
    var data = await postJson('/api/history/delete', {sn: sn});
    delete selectedSnSet[sn];
    delete trackCache[sn];
    if(st) st.textContent = data.removed ? ('已删除: ' + sn) : ('未找到: ' + sn);
    showBanner('已删除历史: ' + sn, 'ok', 2400);
  }catch(e){
    if(st) st.textContent = '删除失败: ' + ((e && e.message) ? e.message : e);
    showBanner('删除失败', 'warn', 3200);
  }
}

async function clearTrackBySelect(){
  var sel = qs('track-sn-select');
  var st = qs('track-mgr-status');
  var sn = sel ? String(sel.value || '').trim() : '';
  if(!sn){
    if(st) st.textContent = '请先选择飞机';
    return;
  }
  if(!confirm('清空该飞机轨迹？\\n' + sn)) return;
  if(st) st.textContent = '清空中...';
  try{
    var data = await postJson('/api/tracks/clear', {sn: sn});
    trackCache[sn] = [];
    if(st) st.textContent = '已清空轨迹: ' + sn + '（影响' + Number(data.affected || 0) + '架）';
    showBanner('轨迹已清空: ' + sn, 'ok', 2400);
  }catch(e){
    if(st) st.textContent = '清空失败: ' + ((e && e.message) ? e.message : e);
    showBanner('清空轨迹失败', 'warn', 3200);
  }
}

async function clearTrackAll(){
  var st = qs('track-mgr-status');
  if(!confirm('清空所有飞机轨迹？')) return;
  if(st) st.textContent = '清空中...';
  try{
    var data = await postJson('/api/tracks/clear', {});
    trackCache = {};
    if(st) st.textContent = '已清空全部轨迹（影响' + Number(data.affected || 0) + '架）';
    showBanner('全部轨迹已清空', 'ok', 2600);
  }catch(e){
    if(st) st.textContent = '清空失败: ' + ((e && e.message) ? e.message : e);
    showBanner('清空全部轨迹失败', 'warn', 3200);
  }
}

async function restartProgram(saveCfg){
  if(restartBusy) return;
  var input = qs('restart-args');
  var argsText = input ? String(input.value || '').trim() : '';
  var ifaceSel = qs('iface-select');
  var iface = ifaceSel ? String(ifaceSel.value || '').trim() : '';
  var scanFast = !!(qs('scan-wifi-fast') && qs('scan-wifi-fast').checked);
  var tip = saveCfg ? '\u4fdd\u5b58\u914d\u7f6e\u5e76\u91cd\u542f\u7a0b\u5e8f\uff1f' : '\u6309\u5f53\u524d\u8f93\u5165\u53c2\u6570\u91cd\u542f\u7a0b\u5e8f\uff08\u4ec5\u672c\u6b21\uff09\uff1f';
  if(!confirm(tip)) return;
  restartBusy = true;
  applyMeta(metaState);
  try{
    await postJson('/api/admin/restart', {
      args: argsText,
      save: !!saveCfg,
      iface: iface,
      scan_wifi_fast: scanFast
    });
    showBanner(saveCfg ? '已提交：保存并重启' : '已提交：仅本次重启', 'ok', 2800);
  }catch(e){
    showBanner('重启失败: ' + ((e && e.message) ? e.message : e), 'warn', 4800);
  }finally{
    restartBusy = false;
    applyMeta(metaState);
  }
}

async function loadConfigEditor(){
  var ta = qs('config-editor');
  var st = qs('config-editor-status');
  if(!ta) return;
  if(st) st.textContent = '读取中...';
  try{
    var data = await getJson('/api/config');
    ta.value = String(data.text || '');
    if(st) st.textContent = '已读取: ' + String(data.path || '-');
  }catch(e){
    if(st) st.textContent = '读取失败: ' + ((e && e.message) ? e.message : e);
  }
}

async function saveConfigEditor(){
  var ta = qs('config-editor');
  var st = qs('config-editor-status');
  if(!ta) return;
  var text = String(ta.value || '');
  if(!text.trim()){
    if(st) st.textContent = '配置内容为空';
    return;
  }
  if(st) st.textContent = '保存中...';
  try{
    var data = await postJson('/api/config/save', {text: text});
    if(st){
      st.textContent = '保存成功: ' + String(data.saved_to || '-') + '，' +
        (data.reloaded ? '已热重载' : '未热重载');
    }
    showBanner('配置已保存', 'ok', 2400);
    loadIfaceOptions(true);
  }catch(e){
    if(st) st.textContent = '保存失败: ' + ((e && e.message) ? e.message : e);
    showBanner('配置保存失败', 'warn', 4200);
  }
}

async function saveBaseConfig(){
  var st = qs('base-status');
  var btn = qs('btn-base-save');
  var nameInput = qs('base-name');
  var latInput = qs('base-lat');
  var lonInput = qs('base-lon');
  var zoomInput = qs('base-zoom');
  var name = nameInput ? String(nameInput.value || '').trim() : '';
  var latRaw = latInput ? String(latInput.value || '').trim() : '';
  var lonRaw = lonInput ? String(lonInput.value || '').trim() : '';
  var zoomRaw = zoomInput ? String(zoomInput.value || '').trim() : '';
  if(!name) name = '\u57fa\u7ad9';

  var lat = (latRaw === '') ? null : numOrNull(latRaw);
  var lon = (lonRaw === '') ? null : numOrNull(lonRaw);
  var zoom = intOrDefault(zoomRaw, 13);
  zoom = Math.max(3, Math.min(19, zoom));

  if((lat === null) !== (lon === null)){
    if(st) st.textContent = '\u57fa\u7ad9\u5750\u6807\u9700\u8981\u540c\u65f6\u586b\u5199\u7ecf\u7eac\u5ea6';
    return;
  }
  if(lat !== null && (lat < -90 || lat > 90)){
    if(st) st.textContent = '\u7eac\u5ea6\u8303\u56f4\u9700\u5728 -90 ~ 90';
    return;
  }
  if(lon !== null && (lon < -180 || lon > 180)){
    if(st) st.textContent = '\u7ecf\u5ea6\u8303\u56f4\u9700\u5728 -180 ~ 180';
    return;
  }

  if(st) st.textContent = '\u4fdd\u5b58\u4e2d...';
  if(btn) btn.disabled = true;
  try{
    var data = await postJson('/api/web/base/save', {
      base_name: name,
      base_lat: lat,
      base_lon: lon,
      base_zoom: zoom
    });
    metaState = Object.assign({}, metaState, {
      base_name: data.base_name,
      base_lat: data.base_lat,
      base_lon: data.base_lon,
      base_zoom: data.base_zoom
    });
    if(nameInput){ delete nameInput.dataset.edited; }
    if(latInput){ delete latInput.dataset.edited; }
    if(lonInput){ delete lonInput.dataset.edited; }
    if(zoomInput){ delete zoomInput.dataset.edited; }
    applyMeta(metaState);
    applyBaseMarker(true);
    if(st){
      st.textContent = '\u57fa\u7ad9\u5df2\u4fdd\u5b58: ' + String(data.base_name || '\u57fa\u7ad9');
    }
    showBanner('\u57fa\u7ad9\u914d\u7f6e\u5df2\u4fdd\u5b58', 'ok', 2200);
  }catch(e){
    if(st) st.textContent = '\u4fdd\u5b58\u5931\u8d25: ' + ((e && e.message) ? e.message : e);
    showBanner('\u57fa\u7ad9\u4fdd\u5b58\u5931\u8d25', 'warn', 4200);
  }finally{
    if(btn) btn.disabled = false;
  }
}

function renderAps(aps, total){
  var box = qs('aplist');
  if(!box) return;
  var rows = Array.isArray(aps) ? aps : [];
  latestApsRows = rows.slice();
  latestApsTotal = Number(total||0);
  var t = Number(total||0);
  if(qs('ap-list-count')){
    qs('ap-list-count').textContent = (t > rows.length) ? (rows.length + '/' + t) : String(rows.length);
  }
  if(!rows.length){
    box.innerHTML = '<div class="ap-empty">\u6682\u65e0AP\u6570\u636e</div>';
    return;
  }
  var wide = (Number(box.clientWidth || 0) >= 780);
  var narrow = (Number(box.clientWidth || 0) <= 520);
  box.classList.toggle('wide', wide);
  box.classList.toggle('narrow', narrow);
  rows.sort(function(a,b){
    var ar = (a && a.rssi != null) ? Number(a.rssi) : -9999;
    var br = (b && b.rssi != null) ? Number(b.rssi) : -9999;
    return br - ar;
  });
  var html = '';
  html += '<div class="aprow hd"><div class="idx">#</div><div>MAC</div><div>\u4fe1\u53f7</div><div>\u7c7b\u578b</div><div>SSID</div><div>\u8bbe\u5907</div></div>';
  for(var i=0;i<rows.length;i++){
    var a = rows[i] || {};
    var rssi = (a.rssi==null) ? 'N/A' : (a.rssi+'dBm');
    var mac = String(a.mac || '');
    var ssid = String(a.ssid || '(hidden)');
    var vt = String(a.vendor_type || 'AP');
    var vn = String(a.vendor || '\u672a\u77e5');
    if(vt === '\u9397\u5b34\u6e80/\u9424\u5059') vt = '\u624b\u673a/\u70ed\u70b9';
    if(vt === '\u7487\u6550/AP') vt = '\u8def\u7531/AP';
    if(vt === '\u9429\u78cb\u7e5b/Wi-Fi') vt = '\u76f4\u8fde/Wi-Fi';
    if(vn === '\u93c8\u7141') vn = '\u672a\u77e5';
    if(vn === '\u52a0\u8f7d\u4e2d' && Number(a.age || 0) >= 10) vn = '\u672a\u77e5';
    html += '<div class="aprow">'+
      '<div class="idx">'+(i+1)+'</div>'+
      '<div class="mono ap-mac" title="'+esc(mac)+'">'+esc(wide ? mac : shortMac(mac))+'</div>'+
      '<div>'+esc(rssi)+'</div>'+
      '<div>'+esc(vt)+'</div>'+
      '<div class="ssid-col"><div class="ssid" title="'+esc(ssid)+'">'+esc(ssid)+'</div></div>'+
      '<div class="vendor-col"><div class="vendor" title="'+esc(vn)+'">'+esc(vn)+'</div></div>'+
      '</div>';
  }
  box.innerHTML = html;
}

function connect(){
  var wsProto = (location.protocol === 'https:') ? 'wss://' : 'ws://';
  ws = new WebSocket(wsProto + location.host + '/ws');
  ws.onopen  = function(){ setWsState(true); };
  ws.onclose = function(){ setWsState(false); reconnTimer=setTimeout(connect,2000); };
  ws.onerror = function(){ ws.close(); };
  ws.onmessage = function(ev){
    var d = JSON.parse(ev.data);
    if(uiFrozen){
      frozenPendingData = d;
      return;
    }
    onData(d);
  };
}
function setWsState(ok){
  qs('dot-ws').className = ok ? 'on' : '';
  qs('ws-status').textContent = ok ? '\u5b9e\u65f6' : '\u91cd\u8fde\u4e2d';
}

function onData(d){
  buildExtraUi();
  applyMeta((d && d.meta) || {});
  qs('cur-ts').textContent = d.ts;
  qs('cur-ch').textContent = d.ch;
  var list = Array.isArray(d.drones) ? d.drones : [];
  var live = list.filter(function(x){ return x && !x.lost; }).length;
  qs('n-live').textContent = live;
  qs('n-lost').textContent = list.length - live;
  syncFieldHighlights(list);
  handleDroneNotifications(list);
  latestDroneMap = {};
  latestDroneRows = list.slice();
  syncSelectedFromRows(latestDroneRows);

  var rows='';
  if(!list.length){
    rows='<tr><td colspan="10" class="empty">\u6682\u65e0\u6570\u636e</td></tr>';
  } else {
    list.forEach(function(e, idx){
      e = e || {};
      var sn = String(e.sn || '');
      if(sn) latestDroneMap[sn] = e;
      var selected = isSnSelected(sn);
      var snSrc = snSourceText(e);
      var scanType = scanTypeText(e);
      var cls = e.lost ? 'lost' : (sn.indexOf('MAC:')===0 ? 'mac' : 'live');
      if(selected) cls += ' selected';
      var snMeta = '<span class="sn-badge">'+esc(snSrc)+'</span><span class="sn-badge">'+esc(scanType)+'</span>';
      var modelCls = fieldCellAttrs(sn, 'model', '');
      var rssiCls = fieldCellAttrs(sn, 'rssi', '');
      var pktCls = fieldCellAttrs(sn, 'pkts', '');
      var dirCls = fieldCellAttrs(sn, 'dir', '');
      var ageCls = fieldCellAttrs(sn, 'age_text', 'mono');
      var lastSeenCls = fieldCellAttrs(sn, 'last_seen', 'mono');
      var lastPktCls = fieldCellAttrs(sn, 'last_pkt_time', 'mono');
      var checked = selected ? ' checked' : '';
      rows += '<tr class="'+cls+' data-row" data-sn="'+escAttr(sn)+'">'+
        '<td><div class="sel-wrap"><input class="sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+checked+'></div></td>'+
        '<td class="idx-cell">'+(idx+1)+'</td>'+
        '<td><div class="sn-cell">'+snMeta+'<span class="mono">'+esc(sn)+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+esc(sn)+'" title="\u590d\u5236SN">&#x29C9;</button></div></td>'+
        '<td'+modelCls+'>'+esc(e.model || 'N/A')+'</td>'+
        '<td'+rssiCls+'>'+fmt(e.rssi,0,'dBm')+'</td>'+
        '<td'+pktCls+'>'+esc(e.pkts==null?'0':e.pkts)+'</td>'+
        '<td'+dirCls+'>'+esc(e.dir || '-')+'</td>'+
        '<td'+ageCls+'>'+esc(e.age_text || fmtAge(e.age))+'</td>'+
        '<td'+lastSeenCls+'>'+esc(e.last_seen || '-')+'</td>'+
        '<td'+lastPktCls+'>'+esc(e.last_pkt_time || e.capture_time || '-')+'</td>'+
        '</tr>';
    });
  }
  qs('tbody').innerHTML = rows;
  syncTableSelectionUi();
  renderMapMiniList(list);
  refreshTrackMgrOptions(list);
  ensureHighlightAnimation();

  var box = qs('logbox');
  var auto = qs('autoscroll').checked;
  var logs = Array.isArray(d.logs) ? d.logs : [];
  if(lastLogsSeq !== d.logs_seq || box.childElementCount !== logs.length){
    box.innerHTML='';
    var frag=document.createDocumentFragment();
    for(var i=0;i<logs.length;i++){
      var line = String(logs[i] || '');
      var dv=document.createElement('div');
      var isRid=line.includes('RID-')||/1581[A-Z0-9]{4}/.test(line);
      dv.className='ap'+(isRid?' rid':'');
      dv.textContent=line;
      frag.appendChild(dv);
    }
    box.appendChild(frag);
    lastLogsSeq = d.logs_seq;
  }
  if(auto) box.scrollTop=box.scrollHeight;

  if(lastApsSeq !== d.aps_seq){
    renderAps(d.aps || [], d.aps_total || 0);
    lastApsSeq = d.aps_seq;
  }

  latestMapRows = Array.isArray(d.map_drones) ? d.map_drones : (Array.isArray(d.drones) ? d.drones : []);
  selectedSnList().forEach(function(sn){
    var e = latestDroneMap[sn];
    if(e && Number(e.track_count || 0) !== Number((trackCache[sn] || []).length)){
      ensureTrackLoaded(sn, true);
    }
  });
  initMap();
  updateMap(latestMapRows);
}

applyTheme(loadThemePref());
buildExtraUi();
connect();

var map = null, markers = {}, pilotMarkers = {}, trackLines = {}, baseMarker = null;
var COLORS = ['#58a6ff','#3fb950','#d29922','#d2a8ff','#79c0ff','#ff7b72'];
var TRACK_COLORS = ['#1f9dff','#12b886','#ff8f1f','#ff4d6d','#8b5cf6','#06b6d4','#84cc16','#eab308'];
var colorIdx = {};
window.addEventListener('resize', function(){
  if(map) map.invalidateSize(false);
  if(latestApsRows.length){
    renderAps(latestApsRows, latestApsTotal);
  }
});

function _gcjOutOfChina(lat, lon){
  return (lon < 72.004 || lon > 137.8347 || lat < 0.8293 || lat > 55.8271);
}
function _gcjTransformLat(x, y){
  var ret = -100.0 + 2.0*x + 3.0*y + 0.2*y*y + 0.1*x*y + 0.2*Math.sqrt(Math.abs(x));
  ret += (20.0*Math.sin(6.0*x*Math.PI) + 20.0*Math.sin(2.0*x*Math.PI)) * 2.0 / 3.0;
  ret += (20.0*Math.sin(y*Math.PI) + 40.0*Math.sin(y/3.0*Math.PI)) * 2.0 / 3.0;
  ret += (160.0*Math.sin(y/12.0*Math.PI) + 320*Math.sin(y*Math.PI/30.0)) * 2.0 / 3.0;
  return ret;
}
function _gcjTransformLon(x, y){
  var ret = 300.0 + x + 2.0*y + 0.1*x*x + 0.1*x*y + 0.1*Math.sqrt(Math.abs(x));
  ret += (20.0*Math.sin(6.0*x*Math.PI) + 20.0*Math.sin(2.0*x*Math.PI)) * 2.0 / 3.0;
  ret += (20.0*Math.sin(x*Math.PI) + 40.0*Math.sin(x/3.0*Math.PI)) * 2.0 / 3.0;
  ret += (150.0*Math.sin(x/12.0*Math.PI) + 300.0*Math.sin(x/30.0*Math.PI)) * 2.0 / 3.0;
  return ret;
}
function wgs84ToGcj02(lat, lon){
  lat = Number(lat);
  lon = Number(lon);
  if(!isFinite(lat) || !isFinite(lon)) return [lat, lon];
  if(_gcjOutOfChina(lat, lon)) return [lat, lon];
  var a = 6378245.0;
  var ee = 0.00669342162296594323;
  var dLat = _gcjTransformLat(lon - 105.0, lat - 35.0);
  var dLon = _gcjTransformLon(lon - 105.0, lat - 35.0);
  var radLat = lat / 180.0 * Math.PI;
  var magic = Math.sin(radLat);
  magic = 1 - ee * magic * magic;
  var sqrtMagic = Math.sqrt(magic);
  dLat = (dLat * 180.0) / ((a * (1 - ee)) / (magic * sqrtMagic) * Math.PI);
  dLon = (dLon * 180.0) / (a / sqrtMagic * Math.cos(radLat) * Math.PI);
  var mgLat = lat + dLat;
  var mgLon = lon + dLon;
  return [mgLat, mgLon];
}
function toMapLatLng(lat, lon){
  return wgs84ToGcj02(lat, lon);
}

function initMap(){
  if(map) return;
  map = L.map('map', {zoomControl:true, attributionControl:true, maxZoom:18});
  L.tileLayer('https://webrd0{s}.is.autonavi.com/appmaptile?lang=zh_cn&size=1&scale=1&style=8&x={x}&y={y}&z={z}',{
    subdomains:['1','2','3','4'],
    maxZoom:18,
    maxNativeZoom:18,
    attribution:'&copy; \u9ad8\u5fb7\u5730\u56fe'
  }).addTo(map);
  var b = baseFromMeta(metaState);
  if(b.ok) map.setView([b.lat, b.lon], b.zoom);
  else map.setView([30, 114], 5);
  applyBaseMarker(false);
  setTimeout(function(){ if(map) map.invalidateSize(false); }, 0);
}

function baseIcon(){
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24">'
    +'<circle cx="12" cy="12" r="10" fill="#2f81f7" fill-opacity="0.88" stroke="#fff" stroke-width="1.4"/>'
    +'<text x="12" y="16" text-anchor="middle" font-size="12" fill="#fff" font-family="monospace" font-weight="bold">&#x2302;</text>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[24,24], iconAnchor:[12,12], popupAnchor:[0,-10]
  });
}

function applyBaseMarker(forceCenter){
  if(!map) return;
  var b = baseFromMeta(metaState);
  if(!b.ok){
    if(baseMarker){
      map.removeLayer(baseMarker);
      baseMarker = null;
    }
    return;
  }
  var popup = '<b>' + esc(b.name) + '</b><br>' + b.lat.toFixed(6) + ', ' + b.lon.toFixed(6) + '<br>z=' + b.zoom;
  var mapPos = [b.lat, b.lon];
  if(baseMarker){
    baseMarker.setLatLng(mapPos).setPopupContent(popup);
  }else{
    baseMarker = L.marker(mapPos, {icon: baseIcon()}).addTo(map).bindPopup(popup);
  }
  if(forceCenter){
    map.setView(mapPos, b.zoom);
  }
}

function trackColorForSn(sn){
  var id = String(sn || '');
  if(!id) return '#1f9dff';
  var h = 0;
  for(var i=0;i<id.length;i++){
    h = ((h * 31) + id.charCodeAt(i)) >>> 0;
  }
  return TRACK_COLORS[h % TRACK_COLORS.length];
}

function droneIcon(color, lost){
  var op = lost ? 0.4 : 1.0;
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="28" height="28" viewBox="0 0 28 28">'
    +'<circle cx="14" cy="14" r="10" fill="'+color+'" fill-opacity="'+op+'" stroke="#fff" stroke-width="1.5"/>'
    +'<text x="14" y="19" text-anchor="middle" font-size="13" fill="#fff" font-family="monospace" font-weight="bold">&#x2708;</text>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[28,28], iconAnchor:[14,14], popupAnchor:[0,-14]
  });
}

function pilotIcon(color, lost){
  var op = lost ? 0.4 : 1.0;
  var fill = color || '#ffb84d';
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="24" height="24" viewBox="0 0 24 24">'
    +'<rect x="3.5" y="3.5" width="17" height="17" rx="4" ry="4" fill="'+fill+'" fill-opacity="'+op+'" stroke="#fff" stroke-width="1.4"/>'
    +'<text x="12" y="16" text-anchor="middle" font-size="12" fill="#fff" font-family="monospace" font-weight="bold">&#x1F464;</text>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[24,24], iconAnchor:[12,12], popupAnchor:[0,-10]
  });
}

function updateMap(drones){
  if(!map) return;
  applyBaseMarker(false);
  var liveAir = drones.filter(function(e){ return e.lat!=null && e.lon!=null; });
  var selected = selectedSnList();
  var selectedSet = {};
  selected.forEach(function(sn){ selectedSet[sn] = true; });
  var livePilot = drones.filter(function(e){
    var sn = String((e && e.sn) || '');
    return !!selectedSet[sn] && e.pilot_lat!=null && e.pilot_lon!=null;
  });
  if(!liveAir.length){
    Object.keys(markers).forEach(function(sn){ map.removeLayer(markers[sn]); delete markers[sn]; });
    Object.keys(pilotMarkers).forEach(function(sn){ map.removeLayer(pilotMarkers[sn]); delete pilotMarkers[sn]; });
    Object.keys(trackLines).forEach(function(sn){ map.removeLayer(trackLines[sn]); delete trackLines[sn]; });
    var b = baseFromMeta(metaState);
    if(b.ok){
      if(!map._rid_base_fitted){
        map.setView([b.lat, b.lon], b.zoom);
        map._rid_base_fitted = true;
      }
      document.getElementById('map-hint').textContent='\u65e0\u98de\u673a\u5750\u6807\uff0c\u5df2\u5b9a\u4f4d\u5230\u57fa\u7ad9';
    } else {
      document.getElementById('map-hint').textContent='\u65e0\u5750\u6807\u6570\u636e';
    }
    return;
  }
  map._rid_base_fitted = false;
  document.getElementById('map-hint').textContent =
    '\u98de\u673a:' + liveAir.length + '  \u5df2\u9009:' + selected.length + '  \u98de\u624b:' + livePilot.length;

  // color assignment by SN
  drones.forEach(function(e){
    if(!colorIdx[e.sn]){
      var n = Object.keys(colorIdx).length;
      colorIdx[e.sn] = COLORS[n % COLORS.length];
    }
  });

  var activeAir = {};
  liveAir.forEach(function(e){
    activeAir[e.sn] = true;
    var col = colorIdx[e.sn];
    var popup = '<b>'+e.sn+'</b><br>'+e.model+'<br>'
      +(e.lat!=null?e.lat.toFixed(5):'-')+', '+(e.lon!=null?e.lon.toFixed(5):'-')
      +'<br>\u9ad8\u5ea6: '+(e.alt!=null?e.alt.toFixed(1)+'m':'N/A')
      +'<br>\u901f\u5ea6: '+(e.spd!=null?e.spd.toFixed(1)+'m/s':'N/A')
      +'<br>\u4fe1\u53f7: '+(e.rssi!=null?e.rssi+'dBm':'N/A')
      +'<br>\u6570\u636e\u66f4\u65b0: '+esc(String(e.age_text || fmtAge(e.age)));

    var airPos = toMapLatLng(e.lat, e.lon);
    if(markers[e.sn]){
      markers[e.sn].setLatLng(airPos)
                   .setIcon(droneIcon(col, e.lost))
                   .setPopupContent(popup);
    } else {
      markers[e.sn] = L.marker(airPos, {icon: droneIcon(col, e.lost)})
        .addTo(map).bindPopup(popup);
    }
  });

  var activePilot = {};
  livePilot.forEach(function(e){
    var sn = String(e.sn || '');
    if(!sn) return;
    activePilot[sn] = true;
    var col = colorIdx[sn] || '#ffb84d';
    var ptxt = String(e.pilot_loc_type_text || e.pilot_loc_type || 'unknown');
    var pilotPos = toMapLatLng(e.pilot_lat, e.pilot_lon);
    var popup = '<b>'+sn+'</b><br>\u98de\u624b\u4f4d\u7f6e<br>'
      +(e.pilot_lat!=null?e.pilot_lat.toFixed(5):'-')+', '+(e.pilot_lon!=null?e.pilot_lon.toFixed(5):'-')
      +'<br>\u7c7b\u578b: '+esc(ptxt);
    if(pilotMarkers[sn]){
      pilotMarkers[sn].setLatLng(pilotPos)
        .setIcon(pilotIcon(col, e.lost))
        .setPopupContent(popup);
    }else{
      pilotMarkers[sn] = L.marker(pilotPos, {icon: pilotIcon(col, e.lost)})
        .addTo(map).bindPopup(popup);
    }
  });

  var activeTrack = {};
  selected.forEach(function(sn){
    sn = String(sn || '');
    if(!sn) return;
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    if(tr.length < 2){
      if(trackLines[sn]){
        map.removeLayer(trackLines[sn]);
        delete trackLines[sn];
      }
      return;
    }
    var latlngs = [];
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var lat = Number(p.lat), lon = Number(p.lon);
      if(isFinite(lat) && isFinite(lon)) latlngs.push(toMapLatLng(lat, lon));
    }
    if(latlngs.length < 2){
      if(trackLines[sn]){
        map.removeLayer(trackLines[sn]);
        delete trackLines[sn];
      }
      return;
    }
    activeTrack[sn] = true;
    var tColor = trackColorForSn(sn);
    if(trackLines[sn]){
      trackLines[sn].setLatLngs(latlngs);
      trackLines[sn].setStyle({color:tColor, weight:4, opacity:0.82});
    } else {
      trackLines[sn] = L.polyline(latlngs, {
        color:tColor,
        weight:4,
        opacity:0.82,
        lineJoin:'round'
      }).addTo(map);
    }
  });

  // remove stale aircraft markers
  Object.keys(markers).forEach(function(sn){
    if(!activeAir[sn]){
      map.removeLayer(markers[sn]); delete markers[sn];
    }
  });
  // remove stale pilot markers
  Object.keys(pilotMarkers).forEach(function(sn){
    if(!activePilot[sn]){
      map.removeLayer(pilotMarkers[sn]); delete pilotMarkers[sn];
    }
  });
  // remove stale or unselected tracks
  Object.keys(trackLines).forEach(function(sn){
    if(!activeTrack[sn]){
      map.removeLayer(trackLines[sn]); delete trackLines[sn];
    }
  });

  // first-time fit bounds for aircraft only
  var latlngs = liveAir.map(function(e){ return toMapLatLng(e.lat, e.lon); });
  if(latlngs.length && !map._rid_fitted){
    if(latlngs.length === 1) map.setView(latlngs[0], 14);
    else map.fitBounds(L.latLngBounds(latlngs).pad(0.3));
    map._rid_fitted = true;
  }
}
</script>
</body></html>"""

def _build_html() -> str:
    return _PAGE_HTML

def http_server_thread() -> None:
    import socket as _socket, threading as _threading
    from http.server import BaseHTTPRequestHandler, HTTPServer
    from socketserver import ThreadingMixIn

    class ThreadingHTTPServer(ThreadingMixIn, HTTPServer):
        daemon_threads = True
        allow_reuse_address = True

    class Handler(BaseHTTPRequestHandler):
        def handle(self):
            try:
                return super().handle()
            except OSError as e:
                # Browser/WebSocket clients may disconnect abruptly; avoid noisy traceback.
                if getattr(e, "errno", None) in (32, 54, 104, 10053, 10054):
                    return
                raise

        def _send_json(self, obj: dict, code: int = 200):
            body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except OSError as e:
                if getattr(e, "errno", None) not in (32, 54, 104, 10053, 10054):
                    raise

        def _read_json_body(self) -> dict:
            try:
                n = int(self.headers.get("Content-Length", "0") or "0")
            except Exception:
                n = 0
            raw = b""
            if n > 0:
                try:
                    raw = self.rfile.read(n)
                except Exception:
                    raw = b""
            if not raw:
                return {}
            try:
                obj = json.loads(raw.decode("utf-8", errors="replace"))
            except Exception:
                return {}
            return obj if isinstance(obj, dict) else {}

        def do_GET(self):
            from urllib.parse import urlparse, parse_qs
            parsed = urlparse(self.path)
            path = parsed.path
            query = parse_qs(parsed.query or "")
            if path in ("/", "/index.html"):
                body = _PAGE_HTML.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path == "/api/config":
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                try:
                    ensure_config_file(APP_CONFIG_PATH)
                    with open(APP_CONFIG_PATH, "r", encoding="utf-8") as f:
                        text = f.read()
                    self._send_json({
                        "ok": True,
                        "path": APP_CONFIG_PATH,
                        "text": text,
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/interfaces":
                try:
                    basic = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
                    if not isinstance(basic, dict):
                        basic = {}
                    self._send_json({
                        "ok": True,
                        "items": _iface_options_snapshot(),
                        "active_iface": str(sniff_iface_name or ""),
                        "selected_iface": (None if basic.get("iface") in (None, "") else str(basic.get("iface"))),
                        "scan_wifi_fast": bool(basic.get("scan_wifi_fast")),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/tracks/get":
                sn = ""
                try:
                    sn = str((query.get("sn") or [""])[0] or "").strip()
                except Exception:
                    sn = ""
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    track = _sanitize_track(src.get("track") or [])
                self._send_json({
                    "ok": True,
                    "sn": sn,
                    "count": len(track),
                    "track": track,
                }, 200)
            elif path == "/api/tools/export/all":
                with state_lock:
                    items = _history_disk_items_locked()
                self._send_json({
                    "ok": True,
                    "version": 1,
                    "exported_at": time.time(),
                    "count": len(items),
                    "items": items,
                }, 200)
            elif path == "/api/tools/export/track":
                sn = ""
                try:
                    sn = str((query.get("sn") or [""])[0] or "").strip()
                except Exception:
                    sn = ""
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    track = _sanitize_track(src.get("track") or [])
                self._send_json({
                    "ok": True,
                    "version": 1,
                    "exported_at": time.time(),
                    "sn": sn,
                    "count": len(track),
                    "track": track,
                }, 200)
            elif path == "/ws":
                # Headers are already parsed by BaseHTTPRequestHandler; read key directly.
                key = self.headers.get("Sec-WebSocket-Key","").strip()
                if not key:
                    self.send_response(400); self.end_headers(); return
                import base64 as _b64, hashlib as _hl
                accept = _b64.b64encode(
                    _hl.sha1((key+"258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode()).digest()
                ).decode()
                resp = ("HTTP/1.1 101 Switching Protocols\r\n"
                        "Upgrade: websocket\r\nConnection: Upgrade\r\n"
                        f"Sec-WebSocket-Accept: {accept}\r\n\r\n")
                self.connection.sendall(resp.encode())
                sock = self.connection
                with _ws_lock:
                    _ws_clients.append(sock)
                import json as _json
                try:
                    sock.sendall(_ws_frame(
                        _json.dumps(_state_snapshot(), ensure_ascii=False).encode()))
                except Exception:
                    pass
                # Keep connection open and drain incoming frames until disconnect.
                try:
                    sock.settimeout(120)
                    while True:
                        hdr = sock.recv(2)
                        if not hdr or len(hdr) < 2: break
                        b1, b2 = hdr[0], hdr[1]
                        masked = bool(b2 & 0x80)
                        pl = b2 & 0x7F
                        if pl == 126:
                            pl = int.from_bytes(sock.recv(2), "big")
                        elif pl == 127:
                            pl = int.from_bytes(sock.recv(8), "big")
                        to_read = (4 if masked else 0) + pl
                        while to_read > 0:
                            chunk = sock.recv(min(to_read, 4096))
                            if not chunk: break
                            to_read -= len(chunk)
                        if (b1 & 0x0F) == 8: break  # close frame
                except Exception:
                    pass
                with _ws_lock:
                    if sock in _ws_clients: _ws_clients.remove(sock)
                try: sock.close()
                except Exception: pass
            else:
                self.send_response(404); self.end_headers()

        def do_POST(self):
            from urllib.parse import urlparse
            path = urlparse(self.path).path
            if path == "/api/history/clear":
                self._read_json_body()
                try:
                    cleared, removed = clear_history_store(delete_file=True)
                    self._send_json({
                        "ok": True,
                        "cleared": cleared,
                        "file_removed": removed,
                        "history_file": HISTORY_STORE_PATH,
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/history/delete":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                removed = delete_history_item(sn)
                self._send_json({"ok": True, "sn": sn, "removed": bool(removed)}, 200)
            elif path == "/api/tracks/clear":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                affected = clear_track_store(sn if sn else None)
                self._send_json({
                    "ok": True,
                    "sn": (sn or None),
                    "affected": int(affected),
                }, 200)
            elif path == "/api/tools/import/all":
                body = self._read_json_body()
                payload = body.get("payload", body) if isinstance(body, dict) else body
                added, updated, skipped = import_details_payload(payload)
                self._send_json({
                    "ok": True,
                    "added": int(added),
                    "updated": int(updated),
                    "skipped": int(skipped),
                }, 200)
            elif path == "/api/tools/import/track":
                body = self._read_json_body()
                payload = body.get("payload", body) if isinstance(body, dict) else body
                if not isinstance(payload, dict):
                    self._send_json({"ok": False, "error": "payload must be object"}, 400)
                    return
                sn = str(payload.get("sn") or body.get("sn") or "").strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                track_raw = payload.get("track")
                track = _sanitize_track(track_raw if isinstance(track_raw, list) else [])
                with state_lock:
                    h = history_table.get(sn) or {"sn": sn, "pkt_count_total": 0}
                    h["sn"] = sn
                    h["track"] = track
                    h["track_updated_wall_ts"] = (float(track[-1]["ts"]) if track else time.time())
                    history_table[sn] = h
                    e = state_table.get(sn)
                    if isinstance(e, dict):
                        e["track"] = list(track)
                        e["track_updated_wall_ts"] = h["track_updated_wall_ts"]
                    _history_mark_dirty()
                self._send_json({
                    "ok": True,
                    "sn": sn,
                    "count": len(track),
                }, 200)
            elif path == "/api/admin/restart":
                body = self._read_json_body()
                if not bool(WEB_CFG.get("allow_restart", True)):
                    self._send_json({"ok": False, "error": "restart disabled"}, 403)
                    return
                args_text = str(body.get("args") or "")
                save_cfg = bool(body.get("save"))
                iface_override_raw = body.get("iface")
                iface_override = None if iface_override_raw in (None, "") else str(iface_override_raw).strip()
                scan_wifi_fast_override = body.get("scan_wifi_fast")
                try:
                    tokens, raw = _parse_restart_args_text(args_text)
                    if iface_override_raw is not None:
                        tokens = _merge_token_option(tokens, "--iface", iface_override)
                    if scan_wifi_fast_override is not None:
                        tokens = _merge_token_flag(tokens, "--scan-wifi-fast", _to_bool(scan_wifi_fast_override, False))
                    if save_cfg:
                        overrides: dict = {}
                        if iface_override_raw is not None:
                            overrides["iface"] = iface_override
                        if scan_wifi_fast_override is not None:
                            overrides["scan_wifi_fast"] = _to_bool(scan_wifi_fast_override, False)
                        ok, msg = _save_basic_config_from_tokens(
                            tokens,
                            raw_text=raw or args_text,
                            overrides=overrides,
                        )
                        if not ok:
                            self._send_json({"ok": False, "error": f"save config failed: {msg}"}, 400)
                            return
                    ok, msg = _schedule_self_restart(tokens)
                    if not ok:
                        self._send_json({"ok": False, "error": msg}, 409)
                        return
                    self._send_json({
                        "ok": True,
                        "restarting": True,
                        "save": save_cfg,
                        "args": tokens,
                    }, 200)
                except ValueError as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/config/save":
                body = self._read_json_body()
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                raw_text = str(body.get("text") or "")
                if not raw_text.strip():
                    self._send_json({"ok": False, "error": "empty config text"}, 400)
                    return
                try:
                    parsed = json.loads(raw_text)
                    if not isinstance(parsed, dict):
                        self._send_json({"ok": False, "error": "config root must be object"}, 400)
                        return
                except Exception as e:
                    self._send_json({"ok": False, "error": f"invalid json: {e}"}, 400)
                    return
                ok, msg = save_app_config(APP_CONFIG_PATH, parsed)
                if not ok:
                    self._send_json({"ok": False, "error": f"save failed: {msg}"}, 500)
                    return
                cfg_loaded = load_app_config(APP_CONFIG_PATH)
                r_ok, r_msg = reload_runtime_config(cfg_loaded)
                self._send_json({
                    "ok": True,
                    "saved_to": APP_CONFIG_PATH,
                    "reloaded": bool(r_ok),
                    "reload_msg": r_msg,
                }, 200)
            elif path == "/api/web/base/save":
                body = self._read_json_body()
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                base_name = str(body.get("base_name") or "基站").strip() or "基站"
                lat_raw = body.get("base_lat")
                lon_raw = body.get("base_lon")
                zoom_raw = body.get("base_zoom")
                try:
                    base_lat = None if lat_raw in (None, "") else float(lat_raw)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid base_lat"}, 400)
                    return
                try:
                    base_lon = None if lon_raw in (None, "") else float(lon_raw)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid base_lon"}, 400)
                    return
                if (base_lat is None) != (base_lon is None):
                    self._send_json({"ok": False, "error": "base_lat/base_lon must be both set or both empty"}, 400)
                    return
                if base_lat is not None and not (-90.0 <= base_lat <= 90.0):
                    self._send_json({"ok": False, "error": "base_lat out of range [-90,90]"}, 400)
                    return
                if base_lon is not None and not (-180.0 <= base_lon <= 180.0):
                    self._send_json({"ok": False, "error": "base_lon out of range [-180,180]"}, 400)
                    return
                try:
                    base_zoom = int(zoom_raw if zoom_raw not in (None, "") else 13)
                except Exception:
                    base_zoom = 13
                base_zoom = max(3, min(19, base_zoom))
                try:
                    cfg = load_app_config(APP_CONFIG_PATH)
                    web_cfg = cfg.get("web")
                    if not isinstance(web_cfg, dict):
                        web_cfg = {}
                    web_cfg["base_name"] = base_name
                    web_cfg["base_lat"] = base_lat
                    web_cfg["base_lon"] = base_lon
                    web_cfg["base_zoom"] = base_zoom
                    cfg["web"] = web_cfg
                    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
                    if not ok:
                        self._send_json({"ok": False, "error": f"save failed: {msg}"}, 500)
                        return
                    cfg_loaded = load_app_config(APP_CONFIG_PATH)
                    r_ok, r_msg = reload_runtime_config(cfg_loaded)
                    self._send_json({
                        "ok": True,
                        "saved_to": APP_CONFIG_PATH,
                        "reloaded": bool(r_ok),
                        "reload_msg": r_msg,
                        "base_name": str(WEB_CFG.get("base_name") or base_name),
                        "base_lat": WEB_CFG.get("base_lat"),
                        "base_lon": WEB_CFG.get("base_lon"),
                        "base_zoom": WEB_CFG.get("base_zoom"),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            else:
                self._send_json({"ok": False, "error": "not found"}, 404)

        def log_message(self, *_): pass

    try:
        srv = ThreadingHTTPServer(("0.0.0.0", HTTP_PORT), Handler)
    except OSError as e:
        _log(f"[WARN] HTTP+WS start failed (port {HTTP_PORT} in use): {e}; continue sniff only")
        return

    _threading.Thread(target=_ws_push_loop, daemon=True).start()
    _log(f"[INFO] HTTP+WS service started: http://0.0.0.0:{HTTP_PORT}/")
    try:
        srv.serve_forever()
    except Exception as e:
        _log(f"[WARN] HTTP+WS service exception: {e}")

# -----------------------------------------------------------------------------
# parse_frame
# -----------------------------------------------------------------------------
def parse_frame(pkt) -> None:
    global ap_seq
    try:
        if not pkt.haslayer(Dot11): return
        d11 = pkt[Dot11]
        if d11.type != 0: return
        _sniff_note_packet()
        if d11.subtype not in (8, 5, 13): return
        subtype_name = {8:"Beacon",5:"ProbeResp",13:"Action"}.get(d11.subtype,"Mgmt")

        src_mac = d11.addr2 or "unknown"
        rssi    = None
        if pkt.haslayer(RadioTap):
            try: rssi = pkt[RadioTap].dBm_AntSignal
            except Exception: pass

        rt_ch     = _rt_channel(pkt)
        ch        = rt_ch or current_channel
        ch_assumed = (rt_ch is None)
        now       = time.monotonic()

        # SSID 提取
        ssid = None
        if pkt.haslayer(Dot11Beacon):
            try:
                elt = pkt[Dot11Beacon].payload
                while elt and elt.name != "NoPayload":
                    if hasattr(elt,"ID") and elt.ID==0:
                        ssid = bytes(elt.info).decode("utf-8", errors="replace")
                        sn_s = _ssid_to_sn(ssid)
                        if sn_s: mac_to_ssid_sn[src_mac]={"sn":sn_s,"ts":now}
                        break
                    elt = elt.payload
            except Exception: pass
            # AP scan logs (for HTTP log panel)
            ts    = time.strftime("%H:%M:%S")
            rssi_s = f"{rssi}dBm" if rssi is not None else "N/A"
            ch_s2  = f"ch{ch}" if ch else "ch?"
            ssid_s = ssid or "(hidden)"
            with log_lock:
                ap_buf.append(f"[{ts}] {src_mac}  {rssi_s:>8}  {ch_s2:<5}  {ssid_s}")
                ap_seq += 1
            try:
                _ap_touch(src_mac, ssid, rssi, ch, "Beacon")
            except Exception:
                pass

        # ODID 载荷提取
        payloads = extract_from_ies(pkt)
        if d11.subtype in (13, 5, 8):   # Extra: also scan raw payload for all mgmt subtypes
            raw_p = extract_from_raw(pkt)
            # 去重
            sigs = {zlib.crc32(p)&0xFFFFFFFF for p in payloads}
            for p in raw_p:
                if (zlib.crc32(p)&0xFFFFFFFF) not in sigs:
                    payloads.append(p)

        # Debug scan logs
        if DEBUG_MODE:
            rssi_s  = f"{rssi}dBm" if rssi is not None else "N/A"
            ch_s    = f"{'~' if ch_assumed else ''}ch{ch}" if ch else "ch?"
            ssid_s  = f" SSID={ssid!r}" if ssid else ""
            odid_s  = ""
            if payloads:
                types = [f"{((p[0]>>4)&0xF):X}" for p in payloads if p]
                odid_s = f" ODID={len(payloads)}[{','.join(types)}]"
            _scan(f"[FRAME] {subtype_name} src={src_mac} {rssi_s} {ch_s}{ssid_s}{odid_s}")

        is_wifi_fast = bool(SCAN_WIFI_FAST) and _is_wifi_fast_mac(src_mac)
        frame_hex = ""
        try:
            frame_hex = _hex_preview(bytes(pkt), max_bytes=220)
        except Exception:
            frame_hex = ""

        if not payloads:
            # Even without ODID payload, if SSID contains RID SN, still refresh last_seen_ts.
            if is_wifi_fast:
                state_update(src_mac, {"basic_id": {"uas_id": _wifi_fast_sn(src_mac), "id_type": "SSID"}, "location": None, "system": None},
                             rssi=rssi, ch=ch, ch_assumed=ch_assumed, pl_sig=0,
                             scan_type="phone", ssid=(ssid or ""), capture_type=subtype_name, raw_pkt_hex=frame_hex)
            elif ssid and src_mac in mac_to_ssid_sn:
                state_update(src_mac, {"basic_id": None, "location": None, "system": None},
                             rssi=rssi, ch=ch, ch_assumed=ch_assumed, pl_sig=0,
                             scan_type="rid", ssid=ssid, capture_type=subtype_name, raw_pkt_hex=frame_hex)
            return

        _notify_hit(ch if not ch_assumed or ch==current_channel else 0)

        def explode(p: bytes) -> list[bytes]:
            if not p: return []
            mt = (p[0]>>4)&0xF
            if mt != MSG_TYPE_PACK:
                return [p[:ODID_MSG_SIZE]] if len(p)>=ODID_MSG_SIZE else [p]
            layout = _decode_odid_pack_layout(p)
            if not layout:
                return [p]
            base, msg_size, qty = layout
            out = []
            for i in range(qty):
                s, e2 = base + i * msg_size, base + (i + 1) * msg_size
                if e2 <= len(p): out.append(p[s:e2])
            return out or [p]

        for payload in payloads:
            if not payload: continue
            for piece in explode(payload):
                sig     = zlib.crc32(piece if len(piece)>=ODID_MSG_SIZE else payload)&0xFFFFFFFF
                decoded = decode_odid(piece)
                if is_wifi_fast and not (decoded.get("basic_id") and decoded.get("basic_id", {}).get("uas_id")):
                    decoded = {
                        "basic_id": {"uas_id": _wifi_fast_sn(src_mac), "id_type": "SSID"},
                        "location": decoded.get("location"),
                        "system": decoded.get("system"),
                    }
                state_update(src_mac, decoded, rssi=rssi, ch=ch,
                             ch_assumed=ch_assumed, pl_sig=sig,
                             scan_type=("phone" if is_wifi_fast else "rid"),
                             ssid=ssid, capture_type=subtype_name,
                             raw_pkt_hex=_hex_preview(piece if piece else payload, max_bytes=160))
                if DEBUG_MODE:
                    b = decoded.get("basic_id")
                    l = decoded.get("location")
                    s = decoded.get("system")
                    if b: _scan(f"  -> BasicID: {b}")
                    if l: _scan(f"  -> Location: lat={l.get('lat'):.5f} lon={l.get('lon'):.5f} "
                                f"alt={l.get('alt_geodetic'):.1f}m spd={l.get('speed_ms')}")
                    if s: _scan(f"  -> System(pilot): lat={s.get('pilot_lat')} lon={s.get('pilot_lon')} type={s.get('pilot_loc_type_text')}")
    except Exception as ex:
        if DEBUG_MODE:
            _scan(f"[ERR] parse_frame: {ex}")

# -----------------------------------------------------------------------------
# TUI -curses
# -----------------------------------------------------------------------------

# Column definition: (header text, display width, field key)
COLUMNS = [
    ("●",    2, "dot"),
    ("SN",  22, "sn_s"),
    ("机型", 12, "model"),
    ("ch",   5, "ch_s"),
    ("纬度", 11, "lat_s"),
    ("经度", 11, "lon_s"),
    ("高程",  8, "alt_s"),
    ("速度",  8, "spd_s"),
    ("垂速",  7, "vsp_s"),
    ("信号",  8, "rssi_s"),
    ("包",    6, "pkts"),
    ("方向",  4, "dir_s"),
    ("时效",  7, "age_s"),
]

def _entry_row(e: dict, now: float) -> dict:
    age  = now - e.get("last_seen_ts", now)
    lost = age > LOST_TIMEOUT
    ch   = e.get("last_ch") or 0
    sn   = str(e.get("sn",""))
    return {
        "dot":     "○" if lost else "●",
        "lost":    lost,
        "mac_only": sn.startswith("MAC:"),
        "sn_s":    (sn[:20]+"...") if len(sn)>21 else sn,
        "model":   str(e.get("model","N/A")),
        "ch_s":    f"{'~' if e.get('ch_assumed') else ''}{ch}" if ch else "?",
        "lat_s":   _fmt(e.get("lat"),".5f"),
        "lon_s":   _fmt(e.get("lon"),".5f"),
        "alt_s":   _fmt(e.get("alt"),".1f","m"),
        "spd_s":   _fmt(e.get("speed"),".1f","m/s"),
        "vsp_s":   _fmt(e.get("vspeed"),".1f"),
        "rssi_s":  _fmt(e.get("rssi"),"d","dBm"),
        "pkts":    str(e.get("pkt_count",0)),
        "dir_s":   e.get("move_dir") or "-",
        "age_s":   f"{age:.0f}s",
    }

def tui_main(stdscr, args) -> None:
    curses.curs_set(0)
    stdscr.nodelay(True)
    curses.start_color()
    curses.use_default_colors()

    curses.init_pair(1, curses.COLOR_GREEN,  -1)   # 在线 SN
    curses.init_pair(2, curses.COLOR_YELLOW, -1)   # MAC-only
    curses.init_pair(3, curses.COLOR_WHITE,  -1)   # 离线
    curses.init_pair(4, curses.COLOR_CYAN,   -1)   # 表头
    curses.init_pair(5, curses.COLOR_BLACK,  curses.COLOR_CYAN)  # title bar
    curses.init_pair(6, curses.COLOR_YELLOW, -1)                 # 变化高亮

    C_ONLINE  = curses.color_pair(1) | curses.A_BOLD
    C_MACONLY = curses.color_pair(2)
    C_LOST    = curses.color_pair(3) | curses.A_DIM
    C_HEADER  = curses.color_pair(4) | curses.A_BOLD
    C_TITLE   = curses.color_pair(5) | curses.A_BOLD
    C_HL      = curses.color_pair(6) | curses.A_BOLD

    # mode: "table" | "log"（事件日志） | "scan"（完整扫描日志）
    mode       = "table"
    log_offset = 0
    last_draw  = 0.0

    while True:
        now = time.monotonic()
        h, w = stdscr.getmaxyx()

        try:   key = stdscr.getch()
        except: key = -1

        if key in (ord('q'), ord('Q')):
            break
        elif key in (ord('d'), ord('D')):
            if mode == "table":
                mode = "scan"       # First press `d`: scan log
            elif mode == "scan":
                mode = "log"        # Second press `d`: event log
            else:
                mode = "table"      # Third press `d`: back to table
            log_offset = 0
        elif key == curses.KEY_UP:
            if mode != "table": log_offset = min(log_offset+3, LOG_BUF_SIZE-1)
        elif key == curses.KEY_DOWN:
            if mode != "table": log_offset = max(log_offset-3, 0)
        elif key in (ord('g'), curses.KEY_HOME, ord('G'), curses.KEY_END):
            log_offset = 0

        if (now - last_draw) < TUI_REFRESH and key == -1:
            time.sleep(0.03)
            continue
        last_draw = now

        stdscr.erase()

        # -- title bar ------------------------------------------------------
        with state_lock:
            n_total = len(state_table)
            n_live  = sum(1 for e in state_table.values()
                         if (now-e["last_seen_ts"]) <= LOST_TIMEOUT)
        ch_s    = f"ch{current_channel}" if current_channel else "ch?"
        dbg_s   = " [DEBUG]" if DEBUG_MODE else ""
        mode_lbl = {"table":"table","scan":"scan-log","log":"events"}.get(mode,"?")
        left  = f"  RID Monitor  LIVE={n_live}  LOST={n_total-n_live}  {ch_s}{dbg_s} "
        right = f" [d]{mode_lbl}  [↑↓]scroll  [q]quit "
        bar   = left.ljust(w - _sw(right)) + right
        try: stdscr.addstr(0, 0, _pad(bar, w), C_TITLE)
        except curses.error: pass

        if mode == "table":
            _draw_table(stdscr, h, w, now, C_HEADER, C_ONLINE, C_MACONLY, C_LOST, C_HL)
        elif mode == "scan":
            _draw_buf(stdscr, h, w, scan_buf, log_offset, "scan log (all frames)", "d->events d->table")
        else:
            _draw_buf(stdscr, h, w, log_buf,  log_offset, "事件日志", "d->表格")

        try: stdscr.refresh()
        except curses.error: pass

def _draw_table(stdscr, h, w, now, C_HEADER, C_ONLINE, C_MACONLY, C_LOST, C_HL):
    # 表头
    hdr = ""
    for label, width, _ in COLUMNS:
        hdr += _pad(label, width) + " "
    sep = "-" * min(w, _sw(hdr))
    try:
        stdscr.addstr(1, 0, hdr[:w], C_HEADER)
        stdscr.addstr(2, 0, sep[:w], C_HEADER)
    except curses.error: pass

    with state_lock:
        entries = sorted(
            state_table.values(),
            key=lambda e: (
                (now-e["last_seen_ts"]) > LOST_TIMEOUT,
                -(e.get("rssi") or -999),
            )
        )

    row_y = 3
    for e in entries:
        if row_y >= h-1: break
        r  = _entry_row(e, now)
        hl = e.get("_hl", {})   # {col_key: expire_monotonic}
        if r["lost"]:       base_attr = C_LOST
        elif r["mac_only"]: base_attr = C_MACONLY
        else:               base_attr = C_ONLINE

        col_x = 0
        for _, width, key in COLUMNS:
            cell  = _pad(str(r.get(key,"")), width) + " "
            # Highlight this column if it has unexpired change mark.
            attr  = C_HL if (not r["lost"] and hl.get(key, 0) > now) else base_attr
            try: stdscr.addstr(row_y, col_x, cell, attr)
            except curses.error: pass
            col_x += width + 1
            if col_x >= w: break

        row_y += 1

    hint = f" total={len(entries)} refresh~{TUI_REFRESH:.1f}s "
    try: stdscr.addstr(h-1, 0, hint[:w].ljust(w), curses.A_DIM)
    except curses.error: pass

def _draw_buf(stdscr, h, w, buf: deque, offset: int, title: str, hint_extra: str):
    with log_lock:
        lines = list(buf)
    vis     = h - 2
    total   = len(lines)
    end_i   = max(0, total - offset)
    start_i = max(0, end_i - vis)
    for i, line in enumerate(lines[start_i:end_i]):
        if 1+i >= h-1: break
        try: stdscr.addstr(1+i, 0, line[:w].ljust(min(w, len(line)+4)))
        except curses.error: pass
    hint = f" {title} [{start_i+1}-{end_i}/{total}]  scroll ↑↓  {hint_extra} "
    try: stdscr.addstr(h-1, 0, hint[:w].ljust(w), curses.A_DIM)
    except curses.error: pass

# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------
def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="OpenDroneID RID WLAN listener")
    parser.add_argument("--config", default=os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT),
                        help="config file path (default: rid_config.json)")
    parser.add_argument("--iface",        default=None)
    parser.add_argument("--channel",      default=None, type=int)
    parser.add_argument("--hop",          action="store_true")
    parser.add_argument("--hop-5g",       action="store_true")
    parser.add_argument("--scan-wifi-fast", action="store_true")
    parser.add_argument("--dwell-2g",     default=DWELL_2G_DEFAULT, type=int)
    parser.add_argument("--dwell-5g",     default=DWELL_5G_DEFAULT, type=int)
    parser.add_argument("--settle",       default=SETTLE_DEFAULT,   type=int)
    parser.add_argument("--dwell-on-hit", default=2500, type=int)
    parser.add_argument("--hit-cap",      default=6000, type=int)
    parser.add_argument("--time",         default=DEFAULT_PRINT_INTERVAL, type=float,
                        help="heartbeat interval seconds (default 2.0)")
    parser.add_argument("--min-gap",      default=DEFAULT_MIN_GAP, type=float,
                        help="minimum output gap for same SN (default 1.0)")
    parser.add_argument("--rssi-delta",   default=3, type=int)
    parser.add_argument("--change-on-rssi",    action="store_true")
    parser.add_argument("--change-on-payload", action="store_true")
    parser.add_argument("--model-map", default=os.path.join(os.getcwd(),"rid_models.json"))
    parser.add_argument("--history-file", default=os.path.join(os.getcwd(), HISTORY_STORE_DEFAULT),
                        help="history cache file (default rid_history_cache.json)")
    parser.add_argument("--no-tui",   action="store_true", help="禁用 TUI，纯文本输出")
    parser.add_argument("--debug",    action="store_true", help="write all raw frames into scan log")
    parser.add_argument("--notify-test", action="store_true", help="send one WeCom test notification then exit")
    return parser

_BASIC_CFG_ARG_DESTS = {
    "iface", "channel", "hop", "hop_5g", "scan_wifi_fast",
    "dwell_2g", "dwell_5g", "settle", "dwell_on_hit", "hit_cap",
    "time", "min_gap", "rssi_delta",
    "change_on_rssi", "change_on_payload",
    "model_map", "history_file",
    "no_tui", "debug",
}

def _parse_restart_args_text(args_text: str | None) -> tuple[list[str], str]:
    raw = str(args_text or "").strip()
    if not raw:
        return list(sys.argv[1:]), ""
    try:
        tokens = shlex.split(raw, posix=True)
    except ValueError as e:
        raise ValueError(f"参数解析失败: {e}")
    for t in tokens:
        opt = t.split("=", 1)[0]
        if opt in ("--notify-test", "--config"):
            raise ValueError(f"not allowed from web page: {opt}")
    return tokens, raw

def _merge_token_option(tokens: list[str], opt: str, value: str | None) -> list[str]:
    out: list[str] = []
    i = 0
    while i < len(tokens):
        t = str(tokens[i])
        if t == opt:
            i += 1
            if i < len(tokens):
                i += 1
            continue
        if t.startswith(opt + "="):
            i += 1
            continue
        out.append(t)
        i += 1
    if value is not None and str(value).strip():
        out.extend([opt, str(value).strip()])
    return out

def _merge_token_flag(tokens: list[str], flag: str, enabled: bool) -> list[str]:
    out = [str(t) for t in tokens if str(t) != flag]
    if enabled:
        out.append(flag)
    return out

def _save_basic_config_from_tokens(tokens: list[str], raw_text: str = "", overrides: dict | None = None) -> tuple[bool, str]:
    global APP_CONFIG
    if not APP_CONFIG_PATH:
        return False, "config file path is empty"
    parser = build_arg_parser()
    try:
        ns = parser.parse_args(tokens)
    except SystemExit:
        return False, "invalid args"
    explicit = _parser_explicit_dests(parser, tokens)
    cfg = load_app_config(APP_CONFIG_PATH)
    basic = cfg.setdefault("basic", {})
    if not isinstance(basic, dict):
        basic = {}
        cfg["basic"] = basic
    for dest in _BASIC_CFG_ARG_DESTS:
        if dest in explicit:
            basic[dest] = getattr(ns, dest)
    if isinstance(overrides, dict):
        if "iface" in overrides:
            ov_iface = overrides.get("iface")
            basic["iface"] = (None if ov_iface in (None, "") else str(ov_iface).strip())
        if "scan_wifi_fast" in overrides:
            basic["scan_wifi_fast"] = _to_bool(overrides.get("scan_wifi_fast"), False)
    web = cfg.setdefault("web", {})
    if not isinstance(web, dict):
        web = {}
        cfg["web"] = web
    web["last_restart_args"] = raw_text if raw_text else " ".join(tokens)
    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
    if ok:
        APP_CONFIG = cfg
        init_web_from_config(APP_CONFIG)
        init_ap_from_config(APP_CONFIG)
        init_notify_from_config(APP_CONFIG)
        return True, msg
    return False, msg

def _schedule_self_restart(tokens: list[str]) -> tuple[bool, str]:
    global restart_pending
    if not bool(WEB_CFG.get("allow_restart", True)):
        return False, "restart disabled"
    py = sys.executable or "python3"
    script = os.path.abspath(sys.argv[0])
    if not os.path.exists(script):
        return False, f"script not found: {script}"
    with restart_lock:
        if restart_pending:
            return False, "已有重启任务"
        restart_pending = True

    def _do_restart(argv_tokens: list[str]) -> None:
        global restart_pending
        try:
            time.sleep(0.4)
            try:
                save_history_store(force=True)
            except Exception:
                pass
            try:
                os.chdir(APP_START_CWD)
            except Exception:
                pass
            argv_tokens = list(argv_tokens)
            has_cfg_arg = any(str(t).split("=", 1)[0] == "--config" for t in argv_tokens)
            if APP_CONFIG_PATH and (not APP_CONFIG_PATH_IS_DEFAULT) and not has_cfg_arg:
                argv_tokens.extend(["--config", APP_CONFIG_PATH])
            argv = [py, script] + argv_tokens
            _log("[INFO] 正在重启程序...")
            os.execv(py, argv)
        except Exception as e:
            _log(f"[WARN] 程序重启失败: {e}")
            with restart_lock:
                restart_pending = False

    Thread(target=_do_restart, args=(list(tokens),), daemon=True).start()
    return True, "restarting"

def main() -> None:
    global PRINT_INTERVAL, MIN_GAP, CHANGE_ON_RSSI, CHANGE_ON_PL
    global RSSI_DELTA, NO_TUI, DEBUG_MODE, current_channel, HISTORY_STORE_PATH, APP_CONFIG
    global APP_CONFIG_PATH, APP_CONFIG_PATH_IS_DEFAULT, APP_START_CWD
    global sniff_iface_name
    global SCAN_WIFI_FAST, WIFI_FAST_SUPPORTED, WIFI_FAST_SUPPORT_MSG

    try:
        if hasattr(sys.stdout,"reconfigure"):
            sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass

    parser = argparse.ArgumentParser(description="OpenDroneID RID WLAN listener")
    parser.add_argument("--config", default=os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT),
                        help="config file path (default: rid_config.json)")
    parser.add_argument("--iface",        default=None)
    parser.add_argument("--channel",      default=None, type=int)
    parser.add_argument("--hop",          action="store_true")
    parser.add_argument("--hop-5g",       action="store_true")
    parser.add_argument("--scan-wifi-fast", action="store_true")
    parser.add_argument("--dwell-2g",     default=DWELL_2G_DEFAULT, type=int)
    parser.add_argument("--dwell-5g",     default=DWELL_5G_DEFAULT, type=int)
    parser.add_argument("--settle",       default=SETTLE_DEFAULT,   type=int)
    parser.add_argument("--dwell-on-hit", default=2500, type=int)
    parser.add_argument("--hit-cap",      default=6000, type=int)
    parser.add_argument("--time",         default=DEFAULT_PRINT_INTERVAL, type=float,
                        help="heartbeat interval seconds (default 2.0)")
    parser.add_argument("--min-gap",      default=DEFAULT_MIN_GAP, type=float,
                        help="minimum output gap for same SN (default 1.0)")
    parser.add_argument("--rssi-delta",   default=3, type=int)
    parser.add_argument("--change-on-rssi",    action="store_true")
    parser.add_argument("--change-on-payload", action="store_true")
    parser.add_argument("--model-map", default=os.path.join(os.getcwd(),"rid_models.json"))
    parser.add_argument("--history-file", default=os.path.join(os.getcwd(), HISTORY_STORE_DEFAULT),
                        help="history cache file (default: rid_history_cache.json)")
    parser.add_argument("--no-tui",   action="store_true", help="禁用 TUI，纯文本输出")
    parser.add_argument("--debug",    action="store_true", help="write all raw frames into scan log")
    parser.add_argument("--notify-test", action="store_true", help="send one WeCom test notification then exit")
    APP_START_CWD = os.getcwd()
    args = parser.parse_args()

    cfg_path = os.path.abspath(str(args.config)) if args.config else None
    APP_CONFIG_PATH = cfg_path
    APP_CONFIG_PATH_IS_DEFAULT = (cfg_path == os.path.abspath(os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT))) if cfg_path else True
    APP_CONFIG = load_app_config(cfg_path)
    apply_config_to_args(parser, args, APP_CONFIG)

    PRINT_INTERVAL  = max(0.2, float(args.time))
    MIN_GAP         = max(0.0, float(args.min_gap))
    CHANGE_ON_RSSI  = bool(args.change_on_rssi)
    CHANGE_ON_PL    = bool(args.change_on_payload)
    RSSI_DELTA      = max(1, int(args.rssi_delta))
    NO_TUI          = bool(args.no_tui)
    DEBUG_MODE      = bool(args.debug)
    SCAN_WIFI_FAST  = bool(args.scan_wifi_fast)
    HISTORY_STORE_PATH = os.path.abspath(str(args.history_file)) if args.history_file else None

    # Redirect Python logging to `scan_buf` instead of `stderr` (avoids TUI swallow).
    class BufHandler(logging.Handler):
        def emit(self, record):
            _scan(f"[{record.levelname}] {self.format(record)}")
    root_logger = logging.getLogger()
    root_logger.setLevel(logging.DEBUG if DEBUG_MODE else logging.WARNING)
    root_logger.handlers.clear()
    root_logger.addHandler(BufHandler())

    init_web_from_config(APP_CONFIG)
    init_ap_from_config(APP_CONFIG)
    init_notify_from_config(APP_CONFIG)
    start_oui_loader()
    load_model_map(args.model_map)
    load_history_store(HISTORY_STORE_PATH)

    if args.notify_test:
        ok, resp = send_test_notification_from_config()
        if ok:
            _log("[INFO] WeCom notify test sent")
            if resp:
                _log(f"[INFO] WeCom response: {resp}")
        else:
            _log(f"[WARN] WeCom test notification failed: {resp}")
        return

    if os.geteuid() != 0:
        _log("[WARN] recommend running as root (sudo)")

    if SCAN_WIFI_FAST and (not args.hop) and (not args.channel):
        args.hop = True
        args.hop_5g = True
        _log("[INFO] WiFi fast-transfer scan enabled: auto use 2.4G+5G hopping")
    elif SCAN_WIFI_FAST and args.hop and (not args.hop_5g):
        args.hop_5g = True
        _log("[INFO] WiFi fast-transfer scan enabled: append 5G hopping")

    iface = interface_detect(prefer=args.iface)
    with sniff_health_lock:
        sniff_iface_name = str(iface or "")
    try:
        WIFI_FAST_SUPPORTED = bool(detect_5g(iface))
    except Exception:
        WIFI_FAST_SUPPORTED = False
    WIFI_FAST_SUPPORT_MSG = ""
    if SCAN_WIFI_FAST and WIFI_FAST_SUPPORTED:
        WIFI_FAST_SUPPORT_MSG = f"iface {iface} supports 5GHz; WiFi fast-transfer scan enabled"
    if SCAN_WIFI_FAST and not WIFI_FAST_SUPPORTED:
        WIFI_FAST_SUPPORT_MSG = f"iface {iface} does not support 5GHz; WiFi fast-transfer scan unavailable"
        _log(f"[WARN] {WIFI_FAST_SUPPORT_MSG}")

    if args.hop and args.channel:
        _log("[WARN] --hop and --channel both set; using hopping mode")

    if args.hop:
        dw2    = max(100, args.dwell_2g)
        dw5    = max(200, args.dwell_5g)
        hop_2g = CHANNELS_2G[:]
        hop_5g: list[int] = []
        if args.hop_5g:
            if WIFI_FAST_SUPPORTED:
                if SCAN_WIFI_FAST:
                    hop_5g = sorted(set(CHANNELS_5G + CHANNELS_5G_COMMON))
                else:
                    hop_5g = CHANNELS_5G[:]
                _log(f"[INFO] 5G channels={hop_5g}")
            else:
                _log("[INFO] 5G unsupported, using 2.4G only")
        _log(f"[INFO] hopping 2.4G={hop_2g}@{dw2}ms" + (f" 5G={hop_5g}@{dw5}ms" if hop_5g else ""))
        Thread(target=channel_hopper,
               args=(iface, hop_2g, hop_5g, dw2, dw5,
                     max(0,args.settle), args.dwell_on_hit, args.hit_cap),
               daemon=True).start()
    elif args.channel:
        _log(f"[INFO] lock channel {args.channel}")
        run_cmd(f"iw dev {iface} set channel {args.channel}")
        current_channel = args.channel
    else:
        # Default lock to ch6 (DJI RID commonly used channel).
        _log("[INFO] default lock channel 6 (DJI RID common). Use --hop or --channel N to change")
        run_cmd(f"iw dev {iface} set channel 6")
        current_channel = 6

    _log(f"[INFO] output: first/changed(min-gap={MIN_GAP:.1f}s)/heartbeat(time={PRINT_INTERVAL:.1f}s)")
    _log(f"[INFO] LOST timeout={LOST_TIMEOUT:.0f}s  PURGE={PURGE_TIMEOUT:.0f}s")
    if DEBUG_MODE:
        _log("[INFO] DEBUG mode: all raw frames are written into scan log (press d)")

    Thread(target=lost_checker, daemon=True).start()
    Thread(target=http_server_thread, daemon=True).start()
    Thread(target=history_persist_loop, daemon=True).start()
    start_notify_worker()

    def sniff_thread():
        global sniff_iface_name
        retry_delay = 2.0
        fail_count = 0
        recover_fail_count = 0
        iface_cur = str(iface or "")

        def note_recover_failure(reason: str) -> None:
            nonlocal recover_fail_count
            recover_fail_count += 1
            _log(f"[WARN] sniff recover failed {recover_fail_count}/{SNIFF_RESTART_AFTER_FAILS}: {reason}")
            if recover_fail_count >= SNIFF_RESTART_AFTER_FAILS:
                _log("[WARN] sniff recover failed too many times, schedule self-restart")
                ok, msg = _schedule_self_restart(list(sys.argv[1:]))
                if not ok:
                    _log(f"[WARN] self-restart scheduling failed: {msg}")
                recover_fail_count = 0

        def note_recover_success() -> None:
            nonlocal recover_fail_count
            recover_fail_count = 0
        while True:
            if not iface_cur:
                iface_cur = _sniff_pick_iface()
                if iface_cur:
                    with sniff_health_lock:
                        sniff_iface_name = iface_cur
                    _log(f"[INFO] sniff iface recovered: {iface_cur}")
                else:
                    _sniff_note_error("no iface available")
                    note_recover_failure("no iface available")
                    _log(f"[WARN] sniff no available iface, retry in {retry_delay:.0f}s")
                    time.sleep(retry_delay)
                    continue

            try:
                with sniff_health_lock:
                    sniff_iface_name = iface_cur
                sniff(iface=iface_cur, prn=parse_frame, store=False, monitor=True, timeout=SNIFF_POLL_TIMEOUT)
                fail_count = 0
                note_recover_success()
                idle = _sniff_idle_sec()
                if idle is not None and idle >= SNIFF_STALL_RECOVER_SEC:
                    ok = _sniff_recover_iface(iface_cur, f"idle {idle:.0f}s without management frame")
                    if not ok:
                        new_iface = _sniff_pick_iface(prefer=iface_cur)
                        if new_iface and new_iface != iface_cur:
                            _log(f"[WARN] sniff iface switch: {iface_cur} -> {new_iface}")
                            iface_cur = new_iface
                            with sniff_health_lock:
                                sniff_iface_name = iface_cur
                            _sniff_recover_iface(iface_cur, "switch iface recovery", force=True)
                time.sleep(0.05)
            except Exception as ex:
                fail_count += 1
                ex_msg = str(ex or "")
                _sniff_note_error(f"sniff exception#{fail_count}: {ex_msg}")
                note_recover_failure(ex_msg)
                if fail_count >= SNIFF_RESTART_AFTER_FAILS:
                    _log(f"[WARN] sniff exception count reached {SNIFF_RESTART_AFTER_FAILS}, scheduling self-restart")
                    ok, msg = _schedule_self_restart(list(sys.argv[1:]))
                    if not ok:
                        _log(f"[WARN] self-restart scheduling failed: {msg}")
                    fail_count = 0

                if _sniff_is_no_device_error(ex):
                    new_iface = _sniff_pick_iface(prefer=iface_cur)
                    if new_iface and new_iface != iface_cur:
                        _log(f"[WARN] sniff iface unavailable, switch {iface_cur} -> {new_iface}")
                        iface_cur = new_iface
                        with sniff_health_lock:
                            sniff_iface_name = iface_cur
                        _sniff_recover_iface(iface_cur, f"after iface switch: {ex_msg}", force=True)
                    elif new_iface:
                        _log(f"[WARN] sniff iface exception#{fail_count}: {ex_msg}, try reset {iface_cur}")
                        _sniff_recover_iface(iface_cur, f"exception#{fail_count}: {ex_msg}", force=True)
                    else:
                        _log(f"[WARN] sniff iface lost: {ex_msg}, waiting for NIC recovery")
                        iface_cur = ""
                else:
                    _log(f"[WARN] sniff exception#{fail_count}: {ex_msg}, retry in {retry_delay:.0f}s")
                    _sniff_recover_iface(iface_cur, f"exception#{fail_count}: {ex_msg}", force=(fail_count >= 3))

                time.sleep(retry_delay)

    Thread(target=sniff_thread, daemon=True).start()

    if NO_TUI:
        _log("[INFO] --no-tui mode (Ctrl+C to exit)")
        try:
            while True: time.sleep(1)
        except KeyboardInterrupt:
            _log("[INFO] stopped")
        finally:
            save_history_store(force=True)
    else:
        try:
            curses.wrapper(tui_main, args)
        except KeyboardInterrupt:
            pass
        finally:
            save_history_store(force=True)
            print("\n[INFO] TUI exited, last 30 event logs:")
            with log_lock:
                for line in list(log_buf)[-30:]:
                    print(line)
            if DEBUG_MODE:
                print("\n[INFO] Last 30 scan logs:")
                with log_lock:
                    for line in list(scan_buf)[-30:]:
                        print(line)

if __name__ == "__main__":
    main()
