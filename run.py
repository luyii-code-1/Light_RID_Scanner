from __future__ import annotations
import argparse
import base64
import curses
import difflib
import hashlib
import hmac
import io
import ipaddress
import json
import logging
import math
import os
import platform
import queue
import random
import re
import secrets
import shlex
import shutil
import socket
import struct
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.request
import zipfile
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
DJI_RID_VENDOR_TYPE  = 0x0D
DJI_RID_VENDOR_PREFIX = ODID_OUI + bytes([DJI_RID_VENDOR_TYPE])
RID_NEW_FW_BODY_MIN  = 28
RID_NEW_FW_SN_LEN    = 20
RID_NEW_FW_UAS_LEN   = 8
RID_NEW_FW_COORD_SEARCH_MAX = 80
RID_NEW_FW_SIG_BYTES = 160

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
SYSTEMD_SERVICE_NAME = "light-rid-scanner.service"
SYSTEMD_SERVICE_PATH = "/etc/systemd/system/" + SYSTEMD_SERVICE_NAME
IW_PACKAGE_NAME = "iw"
RUNTIME_SERVICE_USER = "rid"
RUNTIME_SERVICE_HOME = "/var/lib/light-rid"
RUNTIME_SERVICE_CAPABILITIES = ("CAP_NET_ADMIN", "CAP_NET_RAW")
HISTORY_SAVE_INTERVAL = 5.0
HTTP_JSON_MAX_BYTES = 1024 * 1024
API_NAME = "Light RID Scanner API"
API_VERSION = "v1"
APP_RELEASE_VERSION = "2.0"
APP_HTTP_USER_AGENT = f"LightRIDScanner/{APP_RELEASE_VERSION}"
APP_SERVER_HEADER = f"LightRID/{APP_RELEASE_VERSION}"
BUILD_INFO_FILE = "rid_build_info.json"
EULA_SET_FILE = "EULA.set"
EULA_MARKDOWN_FILE = "EULA.md"
EULA_URL = "https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/EULA.md"
OUI_DB_DEFAULT = "oui.txt"
OUI_DB_URL = "https://standards-oui.ieee.org/oui/oui.txt"
RID_MODELS_UPDATE_URL_DEFAULT = "https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/rid_models.json"
APP_UPDATE_COMMIT_URL_DEFAULT = "https://api.github.com/repos/luyii-code-1/Light_RID_Scanner/commits/main"
MODEL_UPDATE_CHECK_INTERVAL_SEC = 24 * 3600
HOST_METRICS_DIR_DEFAULT = os.path.join(tempfile.gettempdir(), "light_rid_scanner")
HOST_METRICS_FILE_DEFAULT = "host_metrics.jsonl"
HOST_METRICS_SAMPLE_SEC = 60.0
HOST_METRICS_RETENTION_DAYS_DEFAULT = 7
AP_LIST_MAX_DEFAULT = 80
AP_STALE_TIMEOUT = 900.0
NOTIFY_REONLINE_COOLDOWN_DEFAULT = 300.0
NOTIFICATION_CENTER_MAX = 200
DJI_LOOKUP_URL_DEFAULT = "https://repair.dji.com/device/search?re=cn&lang=zh-CN"
SNIFF_POLL_TIMEOUT = 20.0
SNIFF_STALL_RECOVER_SEC = 60.0
SNIFF_RECOVER_COOLDOWN_SEC = 20.0
SNIFF_WORKER_HARD_GRACE_SEC = 8.0
SNIFF_WORKER_JOIN_GRACE_SEC = 2.0
SNIFF_RESTART_AFTER_FAILS = 5
WIFI_FAST_OUI_PREFIX = "0c:9a:e6"
TRACK_MAX_POINTS = 12000
TRACK_MIN_INTERVAL_SEC = 0.8
NO_IFACE_DEGRADE_HINT = "未检测到已绑定的无线网卡，已进入降级运行。请打开设置或 OOBE 完成网卡配置。"
CONFIG_ROLLBACK_SUFFIX = ".rollback"

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
op_buf:   deque[str] = deque(maxlen=LOG_BUF_SIZE)   # Web/admin/security operation audit log
ap_seq:   int = 0
ap_table: dict[str, dict] = {}
ap_list_seq: int = 0
ap_lock = Lock()
log_lock = Lock()
security_rate_lock = Lock()
security_rate_state: dict[str, dict] = {}

HISTORY_STORE_PATH: str | None = None
history_persist_dirty: bool = False
history_persist_last_save_wall: float = 0.0
history_io_lock = Lock()

APP_CONFIG: dict = {}
APP_CONFIG_PATH: str | None = None
APP_CONFIG_PATH_IS_DEFAULT: bool = True
OOBE_REQUIRED: bool = False
OOBE_REASON: str = ""
OOBE_LOCK = Lock()
APP_START_CWD: str = os.getcwd()
APP_START_WALL: float = time.time()
RAW_CONFIG_UNLOCK_TTL_SEC = 15 * 60
raw_config_unlock_lock = Lock()
raw_config_unlocks: dict[str, float] = {}
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
    "heading_ref_deg": 0.0,
    "map_auto_center_idle_sec": 20,
    "alarm_zones": [],
    "access_list_enabled": False,
    "access_list_mode": "allow",
    "access_list": [],
    "alarm_zone": {
        "enabled": False,
        "lat1": None,
        "lon1": None,
        "lat2": None,
        "lon2": None,
        "name": "报警区域",
    },
}
AP_CFG: dict = {
    "list_max": AP_LIST_MAX_DEFAULT,
    "vendor_db_file": os.path.join(os.getcwd(), OUI_DB_DEFAULT),
    "vendor_auto_download": True,
}
AUTH_CFG: dict = {
    "enabled": False,
    "username_sha256": "",
    "password_sha256": "",
    "realm": "Light RID Scanner",
    "session_ttl_min": 30,
    "login_methods": ["password", "passkey", "sso"],
    "sso_links": [],
    "passkeys": [],
}
AUTH_SESSION_COOKIE = "rid_auth"
AUTH_SESSION_TTL_SEC = 30 * 60
auth_session_lock = Lock()
auth_sso_lock = Lock()
auth_passkey_lock = Lock()
api_token_lock = Lock()
auth_sessions: dict[str, float] = {}
auth_session_secret = secrets.token_hex(16)
PASSKEY_CHALLENGE_TTL_SEC = 5 * 60
passkey_challenge_lock = Lock()
passkey_challenges: dict[str, dict] = {}
API_CFG: dict = {
    "enabled": False,
    "token": "",
    "token_sha256": "",
    "tokens": [],
    "whitelist_enabled": False,
    "whitelist_mode": "allow",
    "whitelist": [],
}
PAGE_API_HEADER = "X-LightRID-Page"
PAGE_API_HEADER_VALUE = "1"
NOTIFY_CFG: dict = {
    "enabled": False,
    "only_online": True,
    "notify_reonline": True,
    "reonline_cooldown_sec": NOTIFY_REONLINE_COOLDOWN_DEFAULT,
    "skip_mac_only": True,
    "wecom_webhooks": [],
    "wecom_webhook_key": "",
    "send_timeout_sec": 8,
}
MODEL_UPDATE_CFG: dict = {
    "enabled": True,
    "url": RID_MODELS_UPDATE_URL_DEFAULT,
}
CONFIG_UPDATE_CFG: dict = {
    "enabled": False,
    "url": "",
}
APP_UPDATE_CFG: dict = {
    "enabled": True,
    "commit_url": APP_UPDATE_COMMIT_URL_DEFAULT,
}
APP_UPDATE_STATE: dict = {
    "running": False,
    "last_check_ts": 0.0,
    "latest_commit": "",
    "current_commit": "",
    "update_available": False,
    "last_error": "",
}
MODEL_UPDATE_STATE: dict = {
    "running": False,
    "last_check_ts": 0.0,
    "last_success_ts": 0.0,
    "last_error": "",
    "last_message": "",
    "last_count": 0,
}
model_update_lock = Lock()
model_map_file_lock = Lock()
model_update_worker_started = False
CONFIG_UPDATE_STATE: dict = {
    "running": False,
    "last_check_ts": 0.0,
    "last_success_ts": 0.0,
    "last_error": "",
    "last_message": "",
    "last_count": 0,
}
config_update_lock = Lock()
config_update_worker_started = False
app_update_lock = Lock()

METRICS_CFG: dict = {
    "retention_days": HOST_METRICS_RETENTION_DAYS_DEFAULT,
    "temperature_source": "auto",
}
HOST_METRICS_PATH = os.path.join(HOST_METRICS_DIR_DEFAULT, HOST_METRICS_FILE_DEFAULT)
host_metrics_lock = Lock()
host_metrics_last_sample_wall: float = 0.0
iw_check_lock = Lock()
IW_CHECK_STATE: dict = {
    "checked": False,
    "available": False,
    "path": "",
    "install_attempted": False,
    "install_ok": False,
    "message": "",
    "manual_hint": "",
}

notify_queue: "queue.Queue[dict]" = queue.Queue(maxsize=256)
notify_worker_started = False
notify_worker_lock = Lock()
notification_lock = Lock()
notification_items: deque[dict] = deque(maxlen=NOTIFICATION_CENTER_MAX)
notification_seq: int = 0

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

hw_worker_lock = Lock()
hw_worker_started = False
hw_task_queue: "queue.Queue[dict]" = queue.Queue(maxsize=128)

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

def _op_log(action: str, detail: str = "", *, actor: str = "-", ip: str = "-", ok: bool = True) -> None:
    ts = time.strftime("%Y-%m-%d %H:%M:%S")
    status = "OK" if ok else "FAIL"
    safe_action = re.sub(r"[\r\n\t]+", " ", str(action or "-")).strip()[:80]
    safe_actor = re.sub(r"[\r\n\t]+", " ", str(actor or "-")).strip()[:80]
    safe_ip = re.sub(r"[\r\n\t]+", " ", str(ip or "-")).strip()[:80]
    safe_detail = re.sub(r"[\r\n]+", " ", str(detail or "")).strip()
    safe_detail = re.sub(r"(?i)(token|password|webhook|key|secret)=([^,\s\]}]+)", r"\1=***", safe_detail)
    safe_detail = safe_detail[:1200]
    line = f"[{ts}] [{status}] action={safe_action} actor={safe_actor} ip={safe_ip} {safe_detail}".rstrip()
    with log_lock:
        op_buf.append(line)

def _client_ip_from_handler(handler) -> str:
    try:
        return str((handler.client_address or ("",))[0] or "")
    except Exception:
        return ""

def _set_oobe_required(reason: str, required: bool = True) -> None:
    global OOBE_REQUIRED, OOBE_REASON
    text = str(reason or "").strip()
    with OOBE_LOCK:
        OOBE_REQUIRED = bool(required)
        OOBE_REASON = text if required else ""
    if required and text:
        _op_log("oobe-required", text, ok=False)

def _oobe_state() -> dict:
    with OOBE_LOCK:
        return {"required": bool(OOBE_REQUIRED), "reason": str(OOBE_REASON or "")}

def _app_file_path(name: str) -> str:
    return os.path.join(os.path.dirname(os.path.abspath(__file__)), str(name or ""))

def _eula_set_path() -> str:
    return _app_file_path(EULA_SET_FILE)

def _eula_accepted() -> bool:
    try:
        with open(_eula_set_path(), "r", encoding="utf-8") as f:
            return f.read().strip() == "1"
    except Exception:
        return False

def _write_eula_acceptance() -> tuple[bool, str]:
    try:
        path = _eula_set_path()
        parent = os.path.dirname(path)
        if parent:
            os.makedirs(parent, exist_ok=True)
        with open(path, "w", encoding="utf-8") as f:
            f.write("1\n")
        _op_log("eula-accept", f"path={path}", ok=True)
        return True, path
    except Exception as e:
        _op_log("eula-accept", str(e), ok=False)
        return False, str(e)

def _revoke_eula_acceptance() -> tuple[bool, str]:
    try:
        path = _eula_set_path()
        if os.path.exists(path):
            os.remove(path)
        _op_log("eula-revoke", f"path={path}", ok=True)
        return True, path
    except Exception as e:
        _op_log("eula-revoke", str(e), ok=False)
        return False, str(e)

def _eula_status_payload() -> dict:
    return {
        "ok": True,
        "accepted": _eula_accepted(),
        "set_path": _eula_set_path(),
        "source_url": EULA_URL,
    }

def _eula_redirect_required(req_path: str | None) -> bool:
    path = str(req_path or "/")
    if _eula_accepted():
        return False
    allowed = {
        "/eula",
        "/eula.html",
        "/api/eula/status",
        "/api/eula/accept",
        "/api/eula/revoke",
        "/favicon.ico",
    }
    return path not in allowed

def _html_escape(text: str, *, quote: bool = True) -> str:
    out = str(text or "").replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")
    if quote:
        out = out.replace('"', "&quot;").replace("'", "&#39;")
    return out

def _markdown_inline_html(text: str) -> str:
    escaped = _html_escape(text)

    def _link_repl(match) -> str:
        label = _html_escape(match.group(1))
        url = str(match.group(2) or "").strip()
        if not (url.startswith("https://") or url.startswith("http://")):
            return label
        return '<a href="' + _html_escape(url) + '" target="_blank" rel="noopener noreferrer">' + label + "</a>"

    escaped = re.sub(r"\[([^\]]+)\]\((https?://[^)\s]+)\)", _link_repl, escaped)
    escaped = re.sub(r"\*\*([^*]+)\*\*", r"<strong>\1</strong>", escaped)
    return escaped

def _markdown_to_html(md: str) -> str:
    lines = str(md or "").replace("\r\n", "\n").replace("\r", "\n").split("\n")
    out: list[str] = []
    paragraph: list[str] = []
    in_list = False
    in_code = False
    code_lines: list[str] = []

    def flush_paragraph() -> None:
        nonlocal paragraph
        if paragraph:
            out.append("<p>" + _markdown_inline_html(" ".join(paragraph).strip()) + "</p>")
            paragraph = []

    def close_list() -> None:
        nonlocal in_list
        if in_list:
            out.append("</ul>")
            in_list = False

    for line in lines:
        raw = line.rstrip("\n")
        stripped = raw.strip()
        if stripped.startswith("```"):
            if in_code:
                out.append('<pre class="eula-code"><code>' + _html_escape("\n".join(code_lines), quote=False) + "</code></pre>")
                code_lines = []
                in_code = False
            else:
                flush_paragraph()
                close_list()
                in_code = True
            continue
        if in_code:
            code_lines.append(raw)
            continue
        if not stripped:
            flush_paragraph()
            close_list()
            continue
        m = re.match(r"^(#{1,4})\s+(.+)$", stripped)
        if m:
            flush_paragraph()
            close_list()
            level = min(4, len(m.group(1)))
            out.append(f"<h{level}>{_markdown_inline_html(m.group(2))}</h{level}>")
            continue
        m = re.match(r"^[-*]\s+(.+)$", stripped)
        if m:
            flush_paragraph()
            if not in_list:
                out.append("<ul>")
                in_list = True
            out.append("<li>" + _markdown_inline_html(m.group(1)) + "</li>")
            continue
        paragraph.append(stripped)
    if in_code:
        out.append('<pre class="eula-code"><code>' + _html_escape("\n".join(code_lines), quote=False) + "</code></pre>")
    flush_paragraph()
    close_list()
    return "\n".join(out)

def _load_eula_markdown() -> str:
    md_path = _app_file_path(EULA_MARKDOWN_FILE)
    if os.path.exists(md_path):
        try:
            with open(md_path, "r", encoding="utf-8") as f:
                text = f.read().strip()
            if text:
                return text
        except Exception as e:
            return f"# 最终用户许可协议\n\n本地 EULA.md 读取失败：{e}\n\n请查看：[EULA.md]({EULA_URL})。"
    return "# 最终用户许可协议\n\n当前未能读取许可协议正文，请稍后刷新或查看：[EULA.md](" + EULA_URL + ")。"

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

# -----------------------------------------------------------------------------
# Track query helpers
# -----------------------------------------------------------------------------
# Page endpoints can request shorter windows/limits for rendering without
# mutating the persisted full track kept in memory/history.
def _track_query_value(query: dict | None, key: str) -> str:
    if not isinstance(query, dict):
        return ""
    try:
        v = query.get(key)
        if isinstance(v, list):
            return str(v[0] if v else "")
        return str(v or "")
    except Exception:
        return ""

def _track_for_query(raw, query: dict | None = None) -> list[dict]:
    # Always normalize stored points before applying request-level trimming.
    track = _sanitize_track(raw or [])
    if not isinstance(query, dict):
        return track
    try:
        window_sec = float(_track_query_value(query, "window") or 0.0)
    except Exception:
        window_sec = 0.0
    if window_sec > 0:
        window_sec = min(max(window_sec, 1.0), 30.0 * 86400.0)
        cutoff = time.time() - window_sec
        track = [p for p in track if float(p.get("ts") or 0.0) >= cutoff]
    try:
        limit = int(float(_track_query_value(query, "limit") or 0))
    except Exception:
        limit = 0
    if limit > 0:
        limit = max(10, min(limit, TRACK_MAX_POINTS))
        track = track[-limit:]
    return track

def _history_disk_items_locked() -> list[dict]:
    items: list[dict] = []
    for sn, e in history_table.items():
        if not sn:
            continue
        items.append({
            "sn": sn,
            "src_mac": e.get("src_mac"),
            "id_type": e.get("id_type"),
            "uas_id": _uas_id_clean(e.get("uas_id")),
            "model": _resolve_model_name(sn, e.get("scan_type"), e.get("model")),
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
            "firmware_type": _firmware_type_key(e.get("firmware_type")),
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
        repaired_model = 0
        compat_dirty = False
        with state_lock:
            for raw in items:
                if not isinstance(raw, dict):
                    continue
                sn = str(raw.get("sn","") or "").strip()
                if not sn:
                    continue
                if "firmware_type" not in raw or "uas_id" not in raw:
                    compat_dirty = True
                h = history_table.get(sn) or {"sn": sn}
                h["sn"] = sn
                for k in HISTORY_DETAIL_KEYS:
                    if k in raw:
                        h[k] = raw.get(k)
                h["scan_type"] = _scan_type_key(h.get("scan_type"))
                h["firmware_type"] = _firmware_type_key(h.get("firmware_type"))
                h["uas_id"] = _uas_id_clean(h.get("uas_id"))
                old_model = str(h.get("model") or "").strip()
                new_model = _resolve_model_name(sn, h.get("scan_type"), h.get("model"))
                if new_model != (old_model if old_model else "N/A"):
                    h["model"] = new_model
                    repaired_model += 1
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
        if repaired_model or compat_dirty:
            _history_mark_dirty()
        if compat_dirty:
            _log("[INFO] history cache upgraded for firmware/UAS fields")
        if repaired_model:
            _log(f"[INFO] history model repaired from SN map: {repaired_model}")
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
                "version": 3,
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
    "src_mac","id_type","uas_id","model","last_ch","ch_assumed","lat","lon",
    "alt","speed","vspeed","pilot_lat","pilot_lon","pilot_loc_type","pilot_loc_type_text",
    "rssi","move_dir","ssid",
    "capture_type","firmware_type","last_capture_wall_ts","raw_packets",
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
    h["firmware_type"] = _firmware_type_key(h.get("firmware_type"))
    h["uas_id"] = _uas_id_clean(h.get("uas_id"))
    h["model"] = _resolve_model_name(sn, h.get("scan_type"), h.get("model"))
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
        "version": 1,
        "basic": {
            "iface": None,
            "channel": None,
            "hop": False,
            "hop_5g": False,
            "scan_wifi_fast": False,
            "auto_self_heal": True,
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
            "no_tui": True,
            "debug": False,
        },
        "notify": {
            "enabled": True,
            "only_online": True,
            "notify_reonline": True,
            "reonline_cooldown_sec": int(NOTIFY_REONLINE_COOLDOWN_DEFAULT),
            "skip_mac_only": True,
            "send_timeout_sec": 8,
            "wecom_webhooks": [],
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
            "heading_ref_deg": 0.0,
            "map_auto_center_idle_sec": 20,
            "alarm_zones": [],
            "access_list_enabled": False,
            "access_list_mode": "allow",
            "access_list": [],
            "alarm_zone": {
                "enabled": False,
                "lat1": None,
                "lon1": None,
                "lat2": None,
                "lon2": None,
                "name": "报警区域",
            },
        },
        "ap": {
            "list_max": AP_LIST_MAX_DEFAULT,
            "vendor_db_file": os.path.join(os.getcwd(), OUI_DB_DEFAULT),
            "vendor_auto_download": True,
        },
        "model_update": {
            "enabled": True,
            "url": RID_MODELS_UPDATE_URL_DEFAULT,
        },
        "config_update": {
            "enabled": False,
            "url": "",
        },
        "app_update": {
            "enabled": True,
            "commit_url": APP_UPDATE_COMMIT_URL_DEFAULT,
        },
        "metrics": {
            "retention_days": HOST_METRICS_RETENTION_DAYS_DEFAULT,
            "temperature_source": "auto",
        },
        "auth": {
            "enabled": False,
            "username_sha256": "",
            "password_sha256": "",
            "realm": "Light RID Scanner",
            "session_ttl_min": 30,
            "login_methods": ["password", "passkey", "sso"],
            "passkeys": [],
        },
        "api": {
            "enabled": False,
            "token": "",
            "token_sha256": "",
            "tokens": [],
            "whitelist_enabled": False,
            "whitelist_mode": "allow",
            "whitelist": [],
        },
    }

def ensure_config_file(path: str) -> None:
    if not path:
        return
    if os.path.exists(path):
        return
    _set_oobe_required(f"配置文件不存在，已创建默认配置: {path}", True)
    cfg = default_app_config()
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(cfg, f, ensure_ascii=False, indent=2)
        f.write("\n")
    rb_path = path + CONFIG_ROLLBACK_SUFFIX
    try:
        shutil.copy2(path, rb_path)
    except Exception as e:
        _log(f"[WARN] 配置回滚副本创建失败: {e}")
    _log(f"[INFO] config file created: {path}")

def _config_isolate_file(path: str | None, tag: str = "broken") -> str | None:
    if not path or (not os.path.exists(path)):
        return None
    ts = time.strftime("%Y%m%d%H%M%S")
    dst = f"{path}.{tag}.{ts}"
    try:
        os.replace(path, dst)
        return dst
    except Exception:
        return None

def _config_load_raw(path: str) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        raw = json.load(f)
    if not isinstance(raw, dict):
        raise ValueError("root must be object")
    return raw

def _cfg_preferred_iface_from_cfg(cfg: dict | None) -> str | None:
    try:
        basic = cfg.get("basic") if isinstance(cfg, dict) else {}
        if not isinstance(basic, dict):
            return None
        v = basic.get("iface")
        if v in (None, ""):
            return None
        s = str(v).strip()
        return s or None
    except Exception:
        return None

def load_app_config(path: str | None) -> dict:
    if not path:
        _set_oobe_required("配置路径为空，使用默认配置", True)
        return default_app_config()
    rb_path = path + CONFIG_ROLLBACK_SUFFIX
    try:
        ensure_config_file(path)
        raw = _config_load_raw(path)
        cfg = _deep_merge_dict(default_app_config(), raw)
        try:
            shutil.copy2(path, rb_path)
        except Exception as e:
            _log(f"[WARN] 配置回滚副本刷新失败: {e}")
        if not _cfg_preferred_iface_from_cfg(cfg):
            _set_oobe_required("尚未绑定默认网卡，请进入 OOBE 或设置页完成配置", True)
        else:
            _set_oobe_required("", False)
        _log(f"[INFO] config loaded: {path}")
        return cfg
    except Exception as e:
        _log(f"[WARN] config load failed: {e}")
        _set_oobe_required(f"配置文件异常: {e}", True)
        # Try rollback snapshot first.
        if os.path.exists(rb_path):
            try:
                rb_raw = _config_load_raw(rb_path)
                cfg = _deep_merge_dict(default_app_config(), rb_raw)
                broken = _config_isolate_file(path, "broken")
                if broken:
                    _log(f"[WARN] 主配置文件已隔离为: {broken}")
                ok, msg = save_app_config(path, cfg)
                if ok:
                    _log(f"[INFO] 已从回滚配置恢复: {msg}")
                else:
                    _log(f"[WARN] 回滚恢复写回失败: {msg}")
                return cfg
            except Exception as e_rb:
                _log(f"[WARN] rollback config load failed: {e_rb}")
                rb_broken = _config_isolate_file(rb_path, "broken")
                if rb_broken:
                    _log(f"[WARN] 回滚配置文件已隔离为: {rb_broken}")

        _log("[WARN] 配置回滚不可用，使用默认配置重建")
        cfg = default_app_config()
        try:
            broken = _config_isolate_file(path, "broken")
            if broken:
                _log(f"[WARN] 配置文件已隔离为: {broken}")
            rb_broken = _config_isolate_file(rb_path, "broken")
            if rb_broken:
                _log(f"[WARN] 回滚配置文件已隔离为: {rb_broken}")
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
        # Keep a rollback snapshot in sync for self-protection.
        rb_path = path + CONFIG_ROLLBACK_SUFFIX
        rb_tmp = rb_path + ".tmp"
        try:
            with open(rb_tmp, "w", encoding="utf-8") as f:
                json.dump(cfg, f, ensure_ascii=False, indent=2)
                f.write("\n")
            os.replace(rb_tmp, rb_path)
        except Exception as e:
            try:
                if os.path.exists(rb_tmp):
                    os.remove(rb_tmp)
            except Exception:
                pass
            _log(f"[WARN] 配置回滚副本写入失败: {e}")
        return True, path
    except Exception as e:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass
        return False, str(e)

def create_config_backup(path: str | None, tag: str = "save") -> tuple[bool, str]:
    if not path:
        return False, "missing config path"
    if not os.path.exists(path):
        return True, ""
    try:
        parent = os.path.dirname(path) or os.getcwd()
        backup_dir = os.path.join(parent, "backups")
        os.makedirs(backup_dir, exist_ok=True)
        ts = time.strftime("%Y%m%d_%H%M%S")
        base = os.path.basename(path)
        dst = os.path.join(backup_dir, f"{base}.{tag}.{ts}.bak")
        shutil.copy2(path, dst)
        return True, dst
    except Exception as e:
        return False, str(e)

def restore_config_backup(path: str | None, backup_path: str | None) -> tuple[bool, str]:
    if not path or not backup_path:
        return False, "backup path missing"
    if not os.path.exists(backup_path):
        return False, "backup not found"
    try:
        shutil.copy2(backup_path, path)
        return True, path
    except Exception as e:
        return False, str(e)

# -----------------------------------------------------------------------------
# Raw config editor helpers
# -----------------------------------------------------------------------------
def _config_root_dir() -> str:
    path = APP_CONFIG_PATH or os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT)
    try:
        return os.path.abspath(os.path.dirname(path) or os.getcwd())
    except Exception:
        return os.path.abspath(os.getcwd())

def _config_path_within_root(path: str | None, root_dir: str | None = None) -> bool:
    # The raw-config UI is intentionally jailed to the active config root.
    if not path:
        return False
    try:
        root = os.path.abspath(root_dir or _config_root_dir())
        candidate = os.path.abspath(str(path))
        return os.path.commonpath([root, candidate]) == root
    except Exception:
        return False

def _config_rel_path(path: str | None, root_dir: str | None = None) -> str:
    if not path:
        return ""
    try:
        root = os.path.abspath(root_dir or _config_root_dir())
        candidate = os.path.abspath(str(path))
        if not _config_path_within_root(candidate, root):
            return ""
        rel = os.path.relpath(candidate, root)
        return "." if rel == "." else rel.replace("\\", "/")
    except Exception:
        return ""

def _config_resolve_path(path: str | None, root_dir: str | None = None) -> str | None:
    raw = str(path or "").strip()
    if not raw:
        return None
    root = os.path.abspath(root_dir or _config_root_dir())
    candidate = os.path.abspath(raw if os.path.isabs(raw) else os.path.join(root, raw))
    if not _config_path_within_root(candidate, root):
        return None
    return candidate

def _config_file_stat(path: str) -> dict:
    st = os.stat(path)
    return {
        "path": path,
        "name": os.path.basename(path),
        "rel_path": _config_rel_path(path),
        "type": "file",
        "size": int(st.st_size),
        "mtime": float(st.st_mtime),
    }

def _config_tree_entries(root_dir: str | None = None, *, max_depth: int = 3, max_entries: int = 600) -> dict:
    root = os.path.abspath(root_dir or _config_root_dir())
    root_name = os.path.basename(root.rstrip("\\/")) or root
    visited = 0

    def walk(dir_path: str, depth: int) -> list[dict]:
        nonlocal visited
        nodes: list[dict] = []
        if depth < 0 or visited >= max_entries:
            return nodes
        try:
            entries = list(os.scandir(dir_path))
        except Exception:
            return nodes
        dirs: list[os.DirEntry] = []
        files: list[os.DirEntry] = []
        for entry in entries:
            try:
                if entry.is_dir(follow_symlinks=False):
                    dirs.append(entry)
                elif entry.is_file(follow_symlinks=False):
                    files.append(entry)
            except Exception:
                continue
        for entry in sorted(dirs, key=lambda e: e.name.lower()):
            visited += 1
            if visited > max_entries:
                break
            child_path = entry.path
            node = {
                "name": entry.name,
                "path": child_path,
                "rel_path": _config_rel_path(child_path, root),
                "type": "dir",
                "children": [],
            }
            if depth > 0:
                node["children"] = walk(child_path, depth - 1)
            nodes.append(node)
        for entry in sorted(files, key=lambda e: e.name.lower()):
            visited += 1
            if visited > max_entries:
                break
            try:
                nodes.append(_config_file_stat(entry.path))
            except Exception:
                continue
        return nodes
    return {
        "root": root,
        "root_name": root_name,
        "tree": walk(root, max(0, int(max_depth or 0))),
    }

# Raw config editing uses a short-lived secondary unlock tied to the current
# page session so the password check does not permanently open write access.
def _raw_config_unlock_key(cookie_header: str | None) -> str:
    return _auth_cookie_parse(cookie_header, AUTH_SESSION_COOKIE)

def _raw_config_unlock_cleanup(now_wall: float | None = None) -> None:
    now_wall = float(now_wall or time.time())
    with raw_config_unlock_lock:
        stale = [k for k, exp in raw_config_unlocks.items() if float(exp or 0.0) <= now_wall]
        for key in stale:
            raw_config_unlocks.pop(key, None)

def _raw_config_unlock_set(cookie_header: str | None, ttl_sec: int = RAW_CONFIG_UNLOCK_TTL_SEC) -> bool:
    key = _raw_config_unlock_key(cookie_header)
    if not key:
        return False
    now_wall = time.time()
    with raw_config_unlock_lock:
        raw_config_unlocks[key] = now_wall + float(max(60, int(ttl_sec or RAW_CONFIG_UNLOCK_TTL_SEC)))
        if len(raw_config_unlocks) > 4096:
            stale = [k for k, exp in raw_config_unlocks.items() if float(exp or 0.0) <= now_wall]
            for item in stale[:2048]:
                raw_config_unlocks.pop(item, None)
    return True

def _raw_config_unlocked(cookie_header: str | None) -> bool:
    key = _raw_config_unlock_key(cookie_header)
    if not key:
        return False
    now_wall = time.time()
    with raw_config_unlock_lock:
        exp = raw_config_unlocks.get(key)
        if not exp or float(exp) <= now_wall:
            raw_config_unlocks.pop(key, None)
            return False
        return True

def _raw_config_access_payload(headers=None) -> dict:
    unlocked = _raw_config_unlocked(headers.get("Cookie") if headers is not None else None)
    return {
        "required": bool(_auth_enabled() and _auth_hashes_present(AUTH_CFG)),
        "unlocked": bool(unlocked),
        "ttl_sec": int(RAW_CONFIG_UNLOCK_TTL_SEC),
        "root": _config_root_dir(),
    }

def _config_file_payload(path: str | None = None, *, root_dir: str | None = None) -> dict:
    root = os.path.abspath(root_dir or _config_root_dir())
    abs_path = _config_resolve_path(path or APP_CONFIG_PATH or os.path.join(root, CONFIG_FILE_DEFAULT), root)
    if not abs_path:
        raise ValueError("invalid config path")
    with open(abs_path, "r", encoding="utf-8") as f:
        text = f.read()
    stat = os.stat(abs_path)
    return {
        "ok": True,
        "path": abs_path,
        "rel_path": _config_rel_path(abs_path, root),
        "root": root,
        "name": os.path.basename(abs_path),
        "text": text,
        "size": int(stat.st_size),
        "mtime": float(stat.st_mtime),
        "tree": _config_tree_entries(root),
        "raw_access": _raw_config_access_payload(),
    }

def _config_file_save_payload(path: str | None, text: str, *, tag: str = "raw") -> dict:
    root = _config_root_dir()
    abs_path = _config_resolve_path(path or APP_CONFIG_PATH or os.path.join(root, CONFIG_FILE_DEFAULT), root)
    if not abs_path:
        raise ValueError("invalid config path")
    raw_text = str(text or "")
    if not raw_text.strip():
        raise ValueError("empty config text")
    try:
        parsed = json.loads(raw_text)
        if not isinstance(parsed, dict):
            raise ValueError("config root must be object")
    except Exception as e:
        raise ValueError(f"invalid json: {e}") from e
    parsed = _deep_merge_dict(default_app_config(), parsed)
    parsed, guard_err = _prepare_security_cfg_for_save(parsed)
    if guard_err:
        raise ValueError(guard_err)
    b_ok, backup_path = create_config_backup(abs_path, tag=tag)
    if not b_ok:
        raise ValueError(f"backup failed: {backup_path}")
    ok, msg = save_app_config(abs_path, parsed)
    if not ok:
        raise ValueError(f"save failed: {msg}")
    reload_msg = "skipped"
    if APP_CONFIG_PATH and os.path.abspath(abs_path) == os.path.abspath(APP_CONFIG_PATH):
        cfg_loaded = load_app_config(abs_path)
        r_ok, r_msg = reload_runtime_config(cfg_loaded)
        if not r_ok:
            restore_config_backup(abs_path, backup_path)
            raise ValueError(f"reload failed: {r_msg}")
        reload_msg = r_msg
    return {
        "ok": True,
        "saved_to": abs_path,
        "backup_path": backup_path,
        "reloaded": bool(APP_CONFIG_PATH and os.path.abspath(abs_path) == os.path.abspath(APP_CONFIG_PATH)),
        "reload_msg": reload_msg,
        "root": root,
        "raw_access": _raw_config_access_payload(),
    }

def _config_file_delete_payload(path: str | None) -> dict:
    root = _config_root_dir()
    abs_path = _config_resolve_path(path or "", root)
    if not abs_path:
        raise ValueError("invalid config path")
    if APP_CONFIG_PATH and os.path.abspath(abs_path) == os.path.abspath(APP_CONFIG_PATH):
        raise ValueError("active config file cannot be deleted")
    if not os.path.exists(abs_path):
        raise ValueError("file not found")
    backup_path = ""
    try:
        b_ok, backup_path = create_config_backup(abs_path, tag="delete")
        if not b_ok:
            raise ValueError(f"backup failed: {backup_path}")
        os.remove(abs_path)
        return {
            "ok": True,
            "deleted": True,
            "deleted_path": abs_path,
            "backup_path": backup_path,
            "root": root,
            "raw_access": _raw_config_access_payload(),
        }
    except Exception:
        raise

def _settings_view_payload() -> dict:
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else default_app_config()
    basic = cfg.get("basic") if isinstance(cfg, dict) else {}
    if not isinstance(basic, dict):
        basic = {}
    notify = cfg.get("notify") if isinstance(cfg, dict) else {}
    if not isinstance(notify, dict):
        notify = {}
    web = cfg.get("web") if isinstance(cfg, dict) else {}
    if not isinstance(web, dict):
        web = {}
    api = cfg.get("api") if isinstance(cfg, dict) else {}
    if not isinstance(api, dict):
        api = {}
    auth = cfg.get("auth") if isinstance(cfg, dict) else {}
    if not isinstance(auth, dict):
        auth = {}
    model_update = _normalize_model_update_cfg(cfg)
    config_update = _normalize_config_update_cfg(cfg)
    app_update = _normalize_app_update_cfg(cfg)
    metrics_cfg = _normalize_metrics_cfg(cfg)
    api_prepared = _prepare_api_cfg_for_save(api)
    auth_prepared = _prepare_auth_cfg_for_save(auth)
    notify_norm = _normalize_notify_cfg({"notify": notify})
    web_norm = _normalize_web_cfg({"web": web})
    zones = list(web_norm.get("alarm_zones") or [])
    hooks = list(notify_norm.get("wecom_webhooks") or [])
    channel_raw = basic.get("channel")
    try:
        channel_effective = int(channel_raw) if channel_raw not in (None, "") else 6
    except Exception:
        channel_effective = 6
    interfaces = _iface_options_snapshot()
    host = _host_resource_snapshot()
    host["active_iface"] = str(sniff_iface_name or basic.get("iface") or "")
    host["current_channel"] = int(current_channel or channel_effective or 6)
    host["sniff_state"] = _sniff_health_meta(time.monotonic(), time.time())
    host["ifaces"] = interfaces
    api_tokens_public = _api_tokens_public(api_prepared)
    return {
        "ok": True,
        "path": APP_CONFIG_PATH or "",
        "visual": {
            "basic": {
                "iface": None if basic.get("iface") in (None, "") else str(basic.get("iface")),
                "channel": channel_raw,
                "channel_effective": channel_effective,
                "channel_custom": channel_raw not in (None, ""),
                "hop": bool(basic.get("hop")),
                "hop_5g": bool(basic.get("hop_5g")),
                "scan_wifi_fast": bool(basic.get("scan_wifi_fast")),
                "auto_self_heal": bool(basic.get("auto_self_heal", True)),
                "dwell_2g": basic.get("dwell_2g", DWELL_2G_DEFAULT),
                "dwell_5g": basic.get("dwell_5g", DWELL_5G_DEFAULT),
                "settle": basic.get("settle", SETTLE_DEFAULT),
                "dwell_on_hit": basic.get("dwell_on_hit", 2500),
                "hit_cap": basic.get("hit_cap", 6000),
                "time": basic.get("time", DEFAULT_PRINT_INTERVAL),
                "min_gap": basic.get("min_gap", DEFAULT_MIN_GAP),
                "rssi_delta": basic.get("rssi_delta", 3),
                "change_on_rssi": bool(basic.get("change_on_rssi")),
                "change_on_payload": bool(basic.get("change_on_payload")),
                "debug": bool(basic.get("debug")),
                "model_map": str(basic.get("model_map") or os.path.join(os.getcwd(), "rid_models.json")),
                "history_file": str(basic.get("history_file") or os.path.join(os.getcwd(), HISTORY_STORE_DEFAULT)),
            },
            "notify": {
                "enabled": bool(notify_norm.get("enabled")),
                "notify_reonline": bool(notify_norm.get("notify_reonline", True)),
                "reonline_cooldown_sec": int(notify_norm.get("reonline_cooldown_sec") or NOTIFY_REONLINE_COOLDOWN_DEFAULT),
                "send_timeout_sec": int(notify_norm.get("send_timeout_sec") or 8),
                "wecom_webhook_key_masked": (_mask_secret(str(hooks[0].get("key") or "")) if hooks else ""),
                "wecom_webhooks": [
                    {
                        "index": idx,
                        "name": str(item.get("name") or f"通道 {idx + 1}"),
                        "enabled": bool(item.get("enabled", True)),
                        "key_masked": _mask_secret(str(item.get("key") or "")),
                    }
                    for idx, item in enumerate(hooks)
                ],
            },
            "web": {
                "dji_lookup_url": str(web_norm.get("dji_lookup_url") or DJI_LOOKUP_URL_DEFAULT),
                "base_name": str(web_norm.get("base_name") or "基站"),
                "base_lat": web_norm.get("base_lat"),
                "base_lon": web_norm.get("base_lon"),
                "base_zoom": web_norm.get("base_zoom", 13),
                "heading_ref_deg": web_norm.get("heading_ref_deg", 0.0),
                "map_auto_center_idle_sec": web_norm.get("map_auto_center_idle_sec", 20),
                "access_list_enabled": bool(web_norm.get("access_list_enabled")),
                "access_list_mode": str(web_norm.get("access_list_mode") or "allow"),
                "access_list": list(web_norm.get("access_list") or []),
                "alarm_zones": zones,
            },
            "api": {
                "enabled": bool(api_prepared.get("enabled")),
                "configured": _api_tokens_have_secret(api_prepared),
                "tokens": api_tokens_public,
                "whitelist_effective": _api_tokens_have_secret(api_prepared),
                "whitelist_enabled": bool(api_prepared.get("whitelist_enabled")),
                "whitelist_mode": str(api_prepared.get("whitelist_mode") or "allow"),
                "whitelist": list(api_prepared.get("whitelist") or []),
            },
            "auth": {
                "enabled": bool(auth_prepared.get("enabled")),
                "configured": _auth_hashes_present(auth_prepared),
                "username_masked": ("已设置" if str(auth_prepared.get("username_sha256") or "").strip() else ""),
                "password_masked": ("********" if str(auth_prepared.get("password_sha256") or "").strip() else ""),
                "realm": str(auth_prepared.get("realm") or "Light RID Scanner"),
                "session_ttl_min": int(auth_prepared.get("session_ttl_min") or 30),
                "login_methods": list(auth_prepared.get("login_methods") or []),
                "sso_links": _auth_sso_public_links(auth_prepared),
                "passkeys": _auth_passkeys_public(auth_prepared),
            },
            "model_update": {
                "enabled": bool(model_update.get("enabled")),
                "url": "" if str(model_update.get("url") or "").strip() in ("", RID_MODELS_UPDATE_URL_DEFAULT) else str(model_update.get("url") or ""),
                "state": _model_update_status_payload(),
            },
            "config_update": {
                "enabled": bool(config_update.get("enabled")),
                "url": str(config_update.get("url") or ""),
                "state": _config_update_status_payload(),
            },
            "app_update": {
                "enabled": bool(app_update.get("enabled", True)),
                "commit_url": str(app_update.get("commit_url") or APP_UPDATE_COMMIT_URL_DEFAULT),
                "state": _app_update_status_payload(),
            },
            "metrics": {
                "retention_days": int(metrics_cfg.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT),
                "temperature_source": str(metrics_cfg.get("temperature_source") or "auto"),
                "store_path": HOST_METRICS_PATH,
                "sample_interval_sec": int(HOST_METRICS_SAMPLE_SEC),
            },
        },
        "host": host,
        "interfaces": interfaces,
        "oobe": _oobe_state(),
        "eula": _eula_status_payload(),
        "raw_access": _raw_config_access_payload(),
        "hardware_link": "/hardware-assistant",
    }

def _build_visual_settings_candidate(body: dict | None) -> tuple[dict | None, str | None]:
    if not APP_CONFIG_PATH:
        return None, "config path missing"
    payload = body if isinstance(body, dict) else {}
    cfg = load_app_config(APP_CONFIG_PATH)
    basic = cfg.setdefault("basic", {})
    notify = cfg.setdefault("notify", {})
    web = cfg.setdefault("web", {})
    api = cfg.setdefault("api", {})
    auth = cfg.setdefault("auth", {})
    model_update = cfg.setdefault("model_update", {})
    app_update = cfg.setdefault("app_update", {})
    metrics = cfg.setdefault("metrics", {})
    if not isinstance(basic, dict): basic = {}; cfg["basic"] = basic
    if not isinstance(notify, dict): notify = {}; cfg["notify"] = notify
    if not isinstance(web, dict): web = {}; cfg["web"] = web
    if not isinstance(api, dict): api = {}; cfg["api"] = api
    if not isinstance(auth, dict): auth = {}; cfg["auth"] = auth
    if not isinstance(model_update, dict): model_update = {}; cfg["model_update"] = model_update
    if not isinstance(app_update, dict): app_update = {}; cfg["app_update"] = app_update
    if not isinstance(metrics, dict): metrics = {}; cfg["metrics"] = metrics

    p_basic = payload.get("basic") if isinstance(payload.get("basic"), dict) else {}
    p_notify = payload.get("notify") if isinstance(payload.get("notify"), dict) else {}
    p_web = payload.get("web") if isinstance(payload.get("web"), dict) else {}
    p_api = payload.get("api") if isinstance(payload.get("api"), dict) else {}
    p_auth = payload.get("auth") if isinstance(payload.get("auth"), dict) else {}
    p_model_update = payload.get("model_update") if isinstance(payload.get("model_update"), dict) else {}
    p_app_update = payload.get("app_update") if isinstance(payload.get("app_update"), dict) else {}
    p_metrics = payload.get("metrics") if isinstance(payload.get("metrics"), dict) else {}

    iface_raw = p_basic.get("iface")
    iface = None if iface_raw in (None, "") else str(iface_raw).strip()
    if not iface:
        return None, "必须选择并绑定默认网卡"
    safe_iface = _hw_safe_iface(iface)
    if not safe_iface:
        return None, "invalid iface"
    iface = safe_iface
    basic["iface"] = iface
    if bool(p_basic.get("channel_use_default")):
        basic["channel"] = None
    else:
        try:
            basic["channel"] = None if p_basic.get("channel") in (None, "") else int(p_basic.get("channel"))
        except Exception:
            return {"ok": False, "error": "invalid channel"}
    for k in ("hop", "hop_5g", "scan_wifi_fast", "auto_self_heal", "change_on_rssi", "change_on_payload", "debug", "no_tui"):
        if k in p_basic:
            basic[k] = bool(p_basic.get(k))
    for k, default_v in (
        ("time", DEFAULT_PRINT_INTERVAL),
        ("min_gap", DEFAULT_MIN_GAP),
        ("dwell_2g", DWELL_2G_DEFAULT),
        ("dwell_5g", DWELL_5G_DEFAULT),
        ("settle", SETTLE_DEFAULT),
        ("dwell_on_hit", 2500),
        ("hit_cap", 6000),
    ):
        if k in p_basic:
            try:
                basic[k] = max(0.0, float(p_basic.get(k)))
            except Exception:
                return {"ok": False, "error": f"invalid {k}"}
            if k not in ("time", "min_gap"):
                basic[k] = int(round(float(basic[k])))
    if "rssi_delta" in p_basic:
        try:
            basic["rssi_delta"] = max(1, int(p_basic.get("rssi_delta")))
        except Exception:
            return {"ok": False, "error": "invalid rssi_delta"}
    for k in ("model_map", "history_file"):
        if k in p_basic:
            basic[k] = str(p_basic.get(k) or "").strip()

    for k in ("enabled", "notify_reonline"):
        if k in p_notify:
            notify[k] = bool(p_notify.get(k))
    for k, min_v in (("reonline_cooldown_sec", 0), ("send_timeout_sec", 2)):
        if k in p_notify:
            try:
                notify[k] = max(min_v, int(p_notify.get(k)))
            except Exception:
                return {"ok": False, "error": f"invalid {k}"}
    hooks_payload = p_notify.get("wecom_webhooks")
    if isinstance(hooks_payload, list):
        existing_hooks = _normalize_notify_cfg({"notify": notify}).get("wecom_webhooks") or []
        hooks_next: list[dict] = []
        for idx, item in enumerate(hooks_payload):
            if not isinstance(item, dict):
                continue
            name = str(item.get("name") or f"通道 {idx + 1}").strip() or f"通道 {idx + 1}"
            enabled = bool(item.get("enabled", True))
            cur_key = ""
            try:
                src_idx = int(item.get("index"))
                if 0 <= src_idx < len(existing_hooks):
                    cur_key = str(existing_hooks[src_idx].get("key") or "").strip()
            except Exception:
                cur_key = ""
            raw = str(item.get("key") or "").strip()
            if raw in ("", "********", "__KEEP__"):
                raw = cur_key
            if not raw:
                continue
            hooks_next.append({"name": name, "enabled": enabled, "key": raw})
        notify["wecom_webhooks"] = _normalize_wecom_webhooks(hooks_next, "")
        notify["wecom_webhook_key"] = str((notify["wecom_webhooks"][0]["key"] if notify["wecom_webhooks"] else "") or "")
    else:
        new_wecom = p_notify.get("wecom_webhook_key")
        if new_wecom is not None:
            raw = str(new_wecom or "").strip()
            if raw not in ("", "********", "__KEEP__"):
                notify["wecom_webhook_key"] = raw
        notify["wecom_webhooks"] = _normalize_wecom_webhooks(notify.get("wecom_webhooks"), notify.get("wecom_webhook_key") or "")
        notify["wecom_webhook_key"] = str((notify["wecom_webhooks"][0]["key"] if notify["wecom_webhooks"] else notify.get("wecom_webhook_key") or "") or "")

    for k in ("dji_lookup_url", "base_name"):
        if k in p_web:
            web[k] = str(p_web.get(k) or "").strip()
    for k, lo, hi in (("base_lat", -90.0, 90.0), ("base_lon", -180.0, 180.0)):
        if k in p_web:
            try:
                raw_v = p_web.get(k)
                web[k] = None if raw_v in (None, "") else float(raw_v)
            except Exception:
                return {"ok": False, "error": f"invalid {k}"}
            if web[k] is not None and not (lo <= float(web[k]) <= hi):
                return {"ok": False, "error": f"{k} out of range"}
    for k, mn, mx in (("base_zoom", 3, 30), ("map_auto_center_idle_sec", 5, 600)):
        if k in p_web:
            try:
                web[k] = max(mn, min(mx, int(p_web.get(k))))
            except Exception:
                return {"ok": False, "error": f"invalid {k}"}
    if "heading_ref_deg" in p_web:
        try:
            hd = float(p_web.get("heading_ref_deg") if p_web.get("heading_ref_deg") not in (None, "") else 0.0)
            hd = hd % 360.0
            if hd < 0:
                hd += 360.0
            web["heading_ref_deg"] = round(hd, 2)
        except Exception:
            return {"ok": False, "error": "invalid heading_ref_deg"}
    zones_payload = p_web.get("alarm_zones")
    if isinstance(zones_payload, list):
        zones_next: list[dict] = []
        for idx, zone in enumerate(zones_payload):
            if not isinstance(zone, dict):
                continue
            zone_cfg = {
                "enabled": bool(zone.get("enabled", False)),
                "name": str(zone.get("name") or f"报警区域 {idx + 1}").strip() or f"报警区域 {idx + 1}",
            }
            provided = 0
            for k, lo, hi in (("lat1", -90.0, 90.0), ("lat2", -90.0, 90.0), ("lon1", -180.0, 180.0), ("lon2", -180.0, 180.0)):
                try:
                    raw_v = zone.get(k)
                    zone_cfg[k] = None if raw_v in (None, "") else float(raw_v)
                except Exception:
                    return {"ok": False, "error": f"invalid alarm_zones[{idx}].{k}"}
                if zone_cfg[k] is not None:
                    provided += 1
                    if not (lo <= float(zone_cfg[k]) <= hi):
                        return {"ok": False, "error": f"alarm_zones[{idx}].{k} out of range"}
            if provided == 0:
                zone_cfg["enabled"] = False
            elif provided != 4:
                return {"ok": False, "error": f"alarm_zones[{idx}] incomplete"}
            zones_next.append(zone_cfg)
        web["alarm_zones"] = zones_next
        web["alarm_zone"] = zones_next[0] if zones_next else _normalize_alarm_zone_item({}, idx=1)
    else:
        zone = p_web.get("alarm_zone") if isinstance(p_web.get("alarm_zone"), dict) else {}
        zone_cfg = dict(web.get("alarm_zone") or {})
        zone_cfg["enabled"] = bool(zone.get("enabled", zone_cfg.get("enabled", False)))
        zone_cfg["name"] = str(zone.get("name") or zone_cfg.get("name") or "报警区域").strip() or "报警区域"
        for k, lo, hi in (("lat1", -90.0, 90.0), ("lat2", -90.0, 90.0), ("lon1", -180.0, 180.0), ("lon2", -180.0, 180.0)):
            if k in zone:
                try:
                    raw_v = zone.get(k)
                    zone_cfg[k] = None if raw_v in (None, "") else float(raw_v)
                except Exception:
                    return {"ok": False, "error": f"invalid alarm_zone.{k}"}
                if zone_cfg[k] is not None and not (lo <= float(zone_cfg[k]) <= hi):
                    return {"ok": False, "error": f"alarm_zone.{k} out of range"}
        web["alarm_zone"] = zone_cfg
        web["alarm_zones"] = _normalize_alarm_zones([], zone_cfg)

    if "enabled" in p_api:
        api["enabled"] = bool(p_api.get("enabled"))
    if "whitelist_enabled" in p_api:
        api["whitelist_enabled"] = bool(p_api.get("whitelist_enabled"))
    if "whitelist_mode" in p_api:
        mode = str(p_api.get("whitelist_mode") or "allow").strip().lower()
        api["whitelist_mode"] = "deny" if mode in ("deny", "block", "black", "blacklist") else "allow"
    if "whitelist" in p_api:
        api["whitelist"] = _parse_whitelist_entries(p_api.get("whitelist"))

    if "enabled" in p_auth:
        auth["enabled"] = bool(p_auth.get("enabled"))
    if "realm" in p_auth:
        auth["realm"] = str(p_auth.get("realm") or "Light RID Scanner").strip() or "Light RID Scanner"
    if "session_ttl_min" in p_auth:
        try:
            auth["session_ttl_min"] = max(1, min(10080, int(p_auth.get("session_ttl_min") or 30)))
        except Exception:
            return None, "invalid session_ttl_min"
    if "login_methods" in p_auth:
        auth["login_methods"] = _normalize_auth_login_methods(
            p_auth.get("login_methods"),
            default_missing=[],
            default_empty=[],
        )
    if "username" in p_auth:
        raw_user = str(p_auth.get("username") or "").strip()
        if raw_user not in ("", "__KEEP__", "已设置"):
            auth["username_sha256"] = _sha256_hex(raw_user)
        elif raw_user.lower() == "__clear__":
            auth["username_sha256"] = ""
    if "password" in p_auth:
        raw_pass = str(p_auth.get("password") or "")
        raw_pass_trim = raw_pass.strip()
        if raw_pass_trim not in ("", "__KEEP__", "********"):
            auth["password_sha256"] = _sha256_hex(raw_pass)
        elif raw_pass_trim.lower() == "__clear__":
            auth["password_sha256"] = ""

    if "access_list_enabled" in p_web:
        web["access_list_enabled"] = bool(p_web.get("access_list_enabled"))
    if "access_list_mode" in p_web:
        mode = str(p_web.get("access_list_mode") or "allow").strip().lower()
        web["access_list_mode"] = "deny" if mode in ("deny", "block", "black", "blacklist") else "allow"
    if "access_list" in p_web:
        web["access_list"] = _parse_whitelist_entries(p_web.get("access_list"))

    if p_model_update:
        if "enabled" in p_model_update:
            model_update["enabled"] = bool(p_model_update.get("enabled"))
        if "url" in p_model_update:
            url = str(p_model_update.get("url") or "").strip()
            if url and not (url.startswith("https://") or url.startswith("http://")):
                return None, "invalid model_update.url"
            model_update["url"] = url
        cfg["model_update"] = _normalize_model_update_cfg({"model_update": model_update})
    if p_app_update:
        if "enabled" in p_app_update:
            app_update["enabled"] = bool(p_app_update.get("enabled"))
        if "commit_url" in p_app_update:
            url = str(p_app_update.get("commit_url") or "").strip()
            if url and not (url.startswith("https://") or url.startswith("http://")):
                return None, "invalid app_update.commit_url"
            app_update["commit_url"] = url or APP_UPDATE_COMMIT_URL_DEFAULT
        cfg["app_update"] = _normalize_app_update_cfg({"app_update": app_update})

    if p_metrics:
        if "retention_days" in p_metrics:
            try:
                metrics["retention_days"] = max(1, min(90, int(p_metrics.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT)))
            except Exception:
                return None, "invalid metrics.retention_days"
        if "temperature_source" in p_metrics:
            metrics["temperature_source"] = str(p_metrics.get("temperature_source") or "auto")
        cfg["metrics"] = _normalize_metrics_cfg({"metrics": metrics})

    cfg, guard_err = _prepare_security_cfg_for_save(cfg)
    if guard_err:
        return None, guard_err

    return cfg, None

def _run_visual_settings_test(candidate_cfg: dict, previous_cfg: dict | None = None, notify_test: bool = False, keep_runtime: bool = False) -> tuple[bool, str, str]:
    prev_cfg = _deep_merge_dict(default_app_config(), previous_cfg if isinstance(previous_cfg, dict) else APP_CONFIG)
    notify_msg = ""
    r_ok, r_msg = reload_runtime_config(candidate_cfg)
    if not r_ok:
        try:
            reload_runtime_config(prev_cfg)
        except Exception:
            pass
        return False, str(r_msg or "runtime config reload failed"), notify_msg
    try:
        if notify_test:
            notify_norm = _normalize_notify_cfg(candidate_cfg)
            if bool(notify_norm.get("enabled")) and _notify_wecom_targets(notify_norm):
                n_ok, notify_msg = send_test_notification_from_config(candidate_cfg)
                if not n_ok:
                    raise RuntimeError(str(notify_msg or "notify test failed"))
            else:
                notify_msg = "skip"
        if not keep_runtime:
            rb_ok, rb_msg = reload_runtime_config(prev_cfg)
            if not rb_ok:
                return False, f"测试结束但运行时回滚失败: {rb_msg}", notify_msg
        return True, "test ok", notify_msg
    except Exception as e:
        try:
            reload_runtime_config(prev_cfg)
        except Exception as rb_e:
            return False, f"{e}; rollback failed: {rb_e}", notify_msg
        return False, str(e), notify_msg

def _save_visual_settings(body: dict | None, test_only: bool = False) -> dict:
    if not APP_CONFIG_PATH:
        return {"ok": False, "error": "config path missing"}
    prev_cfg = load_app_config(APP_CONFIG_PATH)
    candidate_cfg, build_err = _build_visual_settings_candidate(body)
    if build_err or not isinstance(candidate_cfg, dict):
        return {"ok": False, "error": str(build_err or "invalid candidate config")}

    test_ok, test_msg, notify_msg = _run_visual_settings_test(
        candidate_cfg,
        previous_cfg=prev_cfg,
        notify_test=False,
        keep_runtime=not test_only,
    )
    if not test_ok:
        return {"ok": False, "error": test_msg, "notify_test": notify_msg}

    if test_only:
        return {
            "ok": True,
            "tested": True,
            "saved": False,
            "reload_msg": "draft tested and rolled back",
            "notify_test": notify_msg,
            "settings": _settings_view_payload().get("visual"),
        }

    backup_path = ""
    b_ok, b_msg = create_config_backup(APP_CONFIG_PATH, tag="settings")
    if not b_ok:
        try:
            reload_runtime_config(prev_cfg)
        except Exception:
            pass
        return {"ok": False, "error": f"backup failed: {b_msg}"}
    backup_path = b_msg

    ok, msg = save_app_config(APP_CONFIG_PATH, candidate_cfg)
    if not ok:
        try:
            restore_config_backup(APP_CONFIG_PATH, backup_path)
            reload_runtime_config(prev_cfg)
        except Exception:
            pass
        return {"ok": False, "error": f"save failed: {msg}"}

    cfg_loaded = load_app_config(APP_CONFIG_PATH)
    r_ok, r_msg = reload_runtime_config(cfg_loaded)
    if not r_ok:
        restore_ok, restore_msg = restore_config_backup(APP_CONFIG_PATH, backup_path)
        try:
            reload_runtime_config(prev_cfg)
        except Exception:
            pass
        if restore_ok:
            return {"ok": False, "error": f"reload failed: {r_msg}; rolled back from backup", "backup_path": backup_path}
        return {"ok": False, "error": f"reload failed: {r_msg}; restore failed: {restore_msg}", "backup_path": backup_path}

    return {
        "ok": True,
        "saved_to": APP_CONFIG_PATH,
        "backup_path": backup_path,
        "tested": True,
        "saved": True,
        "reloaded": bool(r_ok),
        "reload_msg": r_msg,
        "notify_test": notify_msg,
        "settings": _settings_view_payload().get("visual"),
    }

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
    legacy_key = str(base.get("wecom_webhook_key") or "").strip()
    hooks = _normalize_wecom_webhooks(base.get("wecom_webhooks"), legacy_key)
    base["wecom_webhooks"] = hooks
    base["wecom_webhook_key"] = str((hooks[0]["key"] if hooks else legacy_key) or "").strip()
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
    base["base_zoom"] = max(3, min(30, base_zoom))
    try:
        heading_ref = float(base.get("heading_ref_deg") if base.get("heading_ref_deg") is not None else 0.0)
    except Exception:
        heading_ref = 0.0
    heading_ref = heading_ref % 360.0
    if heading_ref < 0:
        heading_ref += 360.0
    base["heading_ref_deg"] = round(heading_ref, 2)
    try:
        idle_sec = int(base.get("map_auto_center_idle_sec") if base.get("map_auto_center_idle_sec") is not None else 20)
    except Exception:
        idle_sec = 20
    base["map_auto_center_idle_sec"] = max(5, min(600, idle_sec))
    base["access_list_enabled"] = bool(base.get("access_list_enabled"))
    mode = str(base.get("access_list_mode") or "allow").strip().lower()
    base["access_list_mode"] = "deny" if mode in ("deny", "block", "black", "blacklist") else "allow"
    base["access_list"] = _parse_whitelist_entries(base.get("access_list"))
    zones = _normalize_alarm_zones(base.get("alarm_zones"), base.get("alarm_zone"))
    base["alarm_zones"] = zones
    base["alarm_zone"] = zones[0] if zones else _normalize_alarm_zone_item({}, idx=1)
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

def _normalize_model_update_cfg(cfg: dict | None) -> dict:
    base = dict(MODEL_UPDATE_CFG)
    if isinstance(cfg, dict):
        raw = cfg.get("model_update")
        if isinstance(raw, dict):
            for k in base.keys():
                if k in raw:
                    base[k] = raw.get(k)
    base["enabled"] = bool(base.get("enabled", True))
    url = str(base.get("url") or "").strip()
    if not url:
        url = RID_MODELS_UPDATE_URL_DEFAULT
    elif not (url.startswith("https://") or url.startswith("http://")):
        url = RID_MODELS_UPDATE_URL_DEFAULT
    base["url"] = url
    return base

def _normalize_config_update_cfg(cfg: dict | None) -> dict:
    base = dict(CONFIG_UPDATE_CFG)
    if isinstance(cfg, dict):
        raw = cfg.get("config_update")
        if isinstance(raw, dict):
            for k in base.keys():
                if k in raw:
                    base[k] = raw.get(k)
    base["enabled"] = bool(base.get("enabled", False))
    url = str(base.get("url") or "").strip()
    if url and not (url.startswith("https://") or url.startswith("http://")):
        url = ""
    base["url"] = url
    return base

def _normalize_app_update_cfg(cfg: dict | None) -> dict:
    base = dict(APP_UPDATE_CFG)
    if isinstance(cfg, dict):
        raw = cfg.get("app_update")
        if isinstance(raw, dict):
            for k in base.keys():
                if k in raw:
                    base[k] = raw.get(k)
    base["enabled"] = bool(base.get("enabled", True))
    url = str(base.get("commit_url") or APP_UPDATE_COMMIT_URL_DEFAULT).strip()
    if not (url.startswith("https://") or url.startswith("http://")):
        url = APP_UPDATE_COMMIT_URL_DEFAULT
    base["commit_url"] = url
    return base

def _normalize_metrics_cfg(cfg: dict | None) -> dict:
    base = dict(METRICS_CFG)
    if isinstance(cfg, dict):
        raw = cfg.get("metrics")
        if isinstance(raw, dict):
            for k in base.keys():
                if k in raw:
                    base[k] = raw.get(k)
    try:
        base["retention_days"] = max(1, min(90, int(base.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT)))
    except Exception:
        base["retention_days"] = HOST_METRICS_RETENTION_DAYS_DEFAULT
    raw_temp_source = str(base.get("temperature_source") or "auto").strip().lower().replace("-", "_")
    temp_alias = {
        "": "auto",
        "auto": "auto",
        "vcgencmd": "vcgencmd",
        "vcgen": "vcgencmd",
        "thermal": "thermal_zone",
        "thermal_zone": "thermal_zone",
        "thermalzone": "thermal_zone",
        "sysfs": "thermal_zone",
        "hwmon": "hwmon",
        "off": "off",
        "none": "off",
        "disabled": "off",
    }
    base["temperature_source"] = temp_alias.get(raw_temp_source, "auto")
    return base

def _sha256_hex(text: str) -> str:
    return hashlib.sha256(str(text or "").encode("utf-8", errors="ignore")).hexdigest().lower()

def _auth_hashes_present(auth_cfg: dict | None = None) -> bool:
    source = auth_cfg if isinstance(auth_cfg, dict) else AUTH_CFG
    return bool(str(source.get("username_sha256") or "").strip()) and bool(str(source.get("password_sha256") or "").strip())

def _parse_whitelist_entries(values) -> list[str]:
    items: list[str] = []
    if isinstance(values, list):
        src = values
    elif values in (None, ""):
        src = []
    else:
        src = str(values).replace("\r", "\n").split("\n")
    seen: set[str] = set()
    for raw in src:
        text = str(raw or "").strip()
        if not text:
            continue
        if text in seen:
            continue
        try:
            ipaddress.ip_network(text, strict=False)
        except Exception:
            continue
        seen.add(text)
        items.append(text)
    return items

def _api_ip_allowed(ip_text: str | None, entries: list[str] | None = None) -> bool:
    return _ip_in_list(ip_text, entries if entries is not None else (API_CFG.get("whitelist") or []))

def _ip_in_list(ip_text: str | None, entries: list[str] | None = None) -> bool:
    try:
        ip_obj = ipaddress.ip_address(str(ip_text or "").strip())
    except Exception:
        return False
    rules = list(entries or [])
    if not rules:
        return False
    for item in rules:
        try:
            if ip_obj in ipaddress.ip_network(str(item), strict=False):
                return True
        except Exception:
            continue
    return False

def _ip_policy_allowed(ip_text: str | None, *, enabled: bool, mode: str, entries: list[str]) -> bool:
    if not enabled:
        return True
    hit = _ip_in_list(ip_text, entries)
    policy = str(mode or "allow").strip().lower()
    if policy in ("deny", "block", "black", "blacklist"):
        return not hit
    return hit

def _api_access_allowed(ip_text: str | None) -> bool:
    if not _api_tokens_have_secret(API_CFG):
        return True
    return _ip_policy_allowed(
        ip_text,
        enabled=bool(API_CFG.get("whitelist_enabled")),
        mode=str(API_CFG.get("whitelist_mode") or "allow"),
        entries=list(API_CFG.get("whitelist") or []),
    )

def _web_access_allowed(ip_text: str | None) -> bool:
    return _ip_policy_allowed(
        ip_text,
        enabled=bool(WEB_CFG.get("access_list_enabled")),
        mode=str(WEB_CFG.get("access_list_mode") or "allow"),
        entries=list(WEB_CFG.get("access_list") or []),
    )

def _normalize_sso_links(raw) -> list[dict]:
    src = raw if isinstance(raw, list) else []
    out: list[dict] = []
    seen: set[str] = set()
    for idx, item in enumerate(src):
        if not isinstance(item, dict):
            continue
        check = str(item.get("check") or "").strip()
        if not re.fullmatch(r"[A-Za-z0-9_-]{8,80}", check or ""):
            continue
        if check in seen:
            continue
        seen.add(check)
        name = str(item.get("name") or f"SSO {idx + 1}").strip() or f"SSO {idx + 1}"
        try:
            created_ts = float(item.get("created_ts") or 0.0)
        except Exception:
            created_ts = 0.0
        try:
            expires_at = float(item.get("expires_at") or 0.0)
        except Exception:
            expires_at = 0.0
        try:
            used_ts = float(item.get("used_ts") or item.get("last_used_ts") or 0.0)
        except Exception:
            used_ts = 0.0
        try:
            used_count = max(0, int(item.get("used_count") or (1 if used_ts > 0 else 0)))
        except Exception:
            used_count = 0
        next_path = str(item.get("next") or "/").strip() or "/"
        if not next_path.startswith("/") or next_path.startswith("//"):
            next_path = "/"
        out.append({
            "name": name[:80],
            "check": check,
            "enabled": bool(item.get("enabled", True)),
            "created_ts": created_ts,
            "expires_at": max(0.0, expires_at),
            "single_use": _to_bool(item.get("single_use"), False),
            "used_ts": max(0.0, used_ts),
            "used_count": used_count,
            "next": next_path,
        })
    return out[:64]

def _sso_link_state(item: dict | None, now_wall: float | None = None) -> dict:
    now_wall = float(now_wall or time.time())
    raw = item if isinstance(item, dict) else {}
    expires_at = float(raw.get("expires_at") or 0.0)
    used_count = int(raw.get("used_count") or 0)
    single_use = bool(raw.get("single_use"))
    enabled = bool(raw.get("enabled", True))
    expired = bool(expires_at > 0 and expires_at <= now_wall)
    used = bool(single_use and used_count > 0)
    if not enabled:
        status = "disabled"
        label = "已停用"
    elif used:
        status = "used"
        label = "已使用"
    elif expired:
        status = "expired"
        label = "已过期"
    else:
        status = "active"
        label = "可用"
    expires_in = None if expires_at <= 0 else int(max(0.0, expires_at - now_wall))
    return {
        "active": status == "active",
        "status": status,
        "status_label": label,
        "expired": expired,
        "used": used,
        "expires_in_sec": expires_in,
    }

def _sso_expiry_from_payload(body: dict | None, now_wall: float | None = None) -> tuple[float, str | None]:
    now_wall = float(now_wall or time.time())
    src = body if isinstance(body, dict) else {}
    mode = str(src.get("expires") or src.get("expiry") or src.get("ttl_mode") or "").strip().lower()
    if mode in ("never", "forever", "infinite", "unlimited", "none", "0"):
        return 0.0, None
    if src.get("expires_at") not in (None, ""):
        try:
            expires_at = float(src.get("expires_at") or 0.0)
        except Exception:
            return 0.0, "invalid expires_at"
        if expires_at <= now_wall:
            return 0.0, "expires_at must be in the future"
        return expires_at, None
    raw_ttl = src.get("ttl_sec")
    if raw_ttl in (None, ""):
        raw_ttl = src.get("ttl_seconds")
    if raw_ttl in (None, ""):
        raw_ttl = src.get("ttl_min")
        if raw_ttl not in (None, ""):
            try:
                raw_ttl = float(raw_ttl) * 60.0
            except Exception:
                return 0.0, "invalid ttl_min"
    if raw_ttl in (None, ""):
        raw_ttl = 24 * 3600
    try:
        ttl_sec = int(float(raw_ttl))
    except Exception:
        return 0.0, "invalid ttl_sec"
    if ttl_sec <= 0:
        return 0.0, None
    ttl_sec = max(60, min(3650 * 86400, ttl_sec))
    return now_wall + ttl_sec, None

def _api_token_id_from_hash(token_hash: str | None, idx: int = 1) -> str:
    raw = str(token_hash or "").strip().lower()
    if re.fullmatch(r"[0-9a-f]{64}", raw or ""):
        return "tok_" + raw[:12]
    return "tok_" + secrets.token_urlsafe(8).replace("-", "_")[:12]

def _api_token_expiry_from_row(row: dict | None, now_wall: float | None = None, fallback: float = 0.0) -> tuple[float, str | None]:
    src = row if isinstance(row, dict) else {}
    now_wall = float(now_wall or time.time())
    mode = str(src.get("expires") or src.get("expiry") or src.get("ttl_mode") or "").strip().lower()
    if mode in ("never", "forever", "infinite", "unlimited", "none", "0"):
        return 0.0, None
    if mode == "keep":
        return max(0.0, float(fallback or 0.0)), None
    if mode or src.get("ttl_sec") not in (None, "") or src.get("ttl_seconds") not in (None, "") or src.get("ttl_min") not in (None, ""):
        return _sso_expiry_from_payload(src, now_wall=now_wall)
    if src.get("expires_at") not in (None, ""):
        try:
            return max(0.0, float(src.get("expires_at") or 0.0)), None
        except Exception:
            return 0.0, "invalid expires_at"
    return max(0.0, float(fallback or 0.0)), None

def _normalize_api_tokens(raw, legacy_token: str = "", legacy_hash: str = "") -> list[dict]:
    src = raw if isinstance(raw, list) else []
    if not src:
        legacy_plain = str(legacy_token or "").strip()
        legacy_digest = str(legacy_hash or "").strip().lower()
        if legacy_plain or re.fullmatch(r"[0-9a-f]{64}", legacy_digest or ""):
            src = [{
                "id": "legacy",
                "name": "默认 Token",
                "token": legacy_plain,
                "token_sha256": legacy_digest,
                "enabled": True,
                "created_ts": 0.0,
                "expires_at": 0.0,
                "single_use": False,
            }]
    out: list[dict] = []
    seen: set[str] = set()
    now_wall = time.time()
    for idx, item in enumerate(src, 1):
        if not isinstance(item, dict):
            continue
        token_plain = str(item.get("token") or item.get("token_plain") or "").strip()
        if token_plain in ("********", "__KEEP__"):
            token_plain = ""
        token_hash = str(item.get("token_sha256") or "").strip().lower()
        if token_plain:
            token_hash = _sha256_hex(token_plain)
        if not re.fullmatch(r"[0-9a-f]{64}", token_hash or ""):
            continue
        raw_id = str(item.get("id") or "").strip()
        token_id = raw_id if re.fullmatch(r"[A-Za-z0-9_-]{3,64}", raw_id or "") else _api_token_id_from_hash(token_hash, idx)
        base_id = token_id
        suffix = 2
        while token_id in seen:
            token_id = f"{base_id}_{suffix}"
            suffix += 1
        seen.add(token_id)
        name = str(item.get("name") or f"API Token {idx}").strip() or f"API Token {idx}"
        try:
            created_ts = float(item.get("created_ts") or 0.0)
        except Exception:
            created_ts = 0.0
        if created_ts <= 0.0:
            created_ts = now_wall
        try:
            expires_at = max(0.0, float(item.get("expires_at") or 0.0))
        except Exception:
            expires_at = 0.0
        try:
            used_ts = max(0.0, float(item.get("used_ts") or item.get("last_used_ts") or 0.0))
        except Exception:
            used_ts = 0.0
        try:
            used_count = max(0, int(item.get("used_count") or (1 if used_ts > 0 else 0)))
        except Exception:
            used_count = 0
        out.append({
            "id": token_id,
            "name": name[:80],
            "token": "",
            "token_sha256": token_hash,
            "enabled": _to_bool(item.get("enabled"), True),
            "created_ts": created_ts,
            "expires_at": expires_at,
            "single_use": _to_bool(item.get("single_use"), False),
            "used_ts": used_ts,
            "used_count": used_count,
        })
    return out[:64]

def _api_tokens_have_secret(api_cfg: dict | None = None) -> bool:
    source = api_cfg if isinstance(api_cfg, dict) else API_CFG
    return any(str(item.get("token_sha256") or "").strip() for item in _normalize_api_tokens(source.get("tokens"), source.get("token") or "", source.get("token_sha256") or ""))

def _api_tokens_public(api_cfg: dict | None = None) -> list[dict]:
    source = api_cfg if isinstance(api_cfg, dict) else API_CFG
    out: list[dict] = []
    for item in _normalize_api_tokens(source.get("tokens"), source.get("token") or "", source.get("token_sha256") or ""):
        state = _sso_link_state(item)
        out.append({
            "id": str(item.get("id") or ""),
            "name": str(item.get("name") or ""),
            "enabled": bool(item.get("enabled", True)),
            "created_ts": float(item.get("created_ts") or 0.0),
            "expires_at": float(item.get("expires_at") or 0.0),
            "expires_in_sec": state.get("expires_in_sec"),
            "single_use": bool(item.get("single_use")),
            "used_ts": float(item.get("used_ts") or 0.0),
            "used_count": int(item.get("used_count") or 0),
            "active": bool(state.get("active")),
            "status": str(state.get("status") or ""),
            "status_label": str(state.get("status_label") or ""),
        })
    return out

def _normalize_passkeys(raw) -> list[dict]:
    src = raw if isinstance(raw, list) else []
    out: list[dict] = []
    seen: set[str] = set()
    now_wall = time.time()
    for idx, item in enumerate(src, 1):
        if not isinstance(item, dict):
            continue
        pk_id = str(item.get("id") or item.get("credential_id") or "").strip()
        if not pk_id:
            continue
        if pk_id in seen:
            continue
        seen.add(pk_id)
        pk_name = str(item.get("name") or f"通行密钥 {idx}").strip() or f"通行密钥 {idx}"
        public_key = item.get("public_key") if isinstance(item.get("public_key"), dict) else {}
        x = str(public_key.get("x") or item.get("x") or "").strip()
        y = str(public_key.get("y") or item.get("y") or "").strip()
        if not x or not y:
            continue
        try:
            sign_count = max(0, int(item.get("sign_count") or 0))
        except Exception:
            sign_count = 0
        try:
            created_ts = float(item.get("created_ts") or 0.0)
        except Exception:
            created_ts = 0.0
        if created_ts <= 0.0:
            created_ts = now_wall
        try:
            last_used_ts = max(0.0, float(item.get("last_used_ts") or 0.0))
        except Exception:
            last_used_ts = 0.0
        out.append({
            "id": pk_id[:128],
            "name": pk_name[:80],
            "user_handle": str(item.get("user_handle") or ""),
            "public_key": {"kty": "EC", "crv": "P-256", "x": x, "y": y},
            "sign_count": sign_count,
            "created_ts": created_ts,
            "last_used_ts": last_used_ts,
            "enabled": bool(item.get("enabled", True)),
        })
    return out[:32]

def _normalize_auth_login_methods(raw, *, default_missing=None, default_empty=None) -> list[str]:
    alias = {
        "password": "password",
        "userpass": "password",
        "user_pass": "password",
        "username_password": "password",
        "account_password": "password",
        "passkey": "passkey",
        "webauthn": "passkey",
        "sso": "sso",
        "sso_url": "sso",
        "login_link": "sso",
        "login_links": "sso",
    }
    if raw is None:
        src = []
        fallback = default_missing
    elif isinstance(raw, dict):
        src = [k for k, enabled in raw.items() if enabled]
        fallback = default_empty
    elif isinstance(raw, (list, tuple, set)):
        src = list(raw)
        fallback = default_empty
    else:
        src = re.split(r"[\s,;|]+", str(raw or ""))
        fallback = default_empty
    out: list[str] = []
    seen: set[str] = set()
    for item in src:
        key = alias.get(str(item or "").strip().lower().replace("-", "_"))
        if not key or key in seen:
            continue
        seen.add(key)
        out.append(key)
    if out:
        return out
    if fallback is None:
        return []
    return _normalize_auth_login_methods(fallback, default_missing=None, default_empty=None)

def _auth_login_methods(auth_cfg: dict | None = None) -> list[str]:
    source = auth_cfg if isinstance(auth_cfg, dict) else AUTH_CFG
    return _normalize_auth_login_methods(
        source.get("login_methods") if isinstance(source, dict) else None,
        default_missing=("password", "passkey", "sso"),
        default_empty=("password", "passkey", "sso"),
    )

def _auth_login_method_enabled(method: str, auth_cfg: dict | None = None) -> bool:
    return str(method or "").strip().lower() in _auth_login_methods(auth_cfg)

def _prepare_auth_cfg_for_save(auth_cfg: dict | None) -> dict:
    raw = dict(auth_cfg) if isinstance(auth_cfg, dict) else {}
    out = dict(raw)
    plain_user = str(out.pop("username", "") or "").strip()
    plain_pass = str(out.pop("password", "") or "")
    user_hash = str(out.get("username_sha256") or "").strip().lower()
    pass_hash = str(out.get("password_sha256") or "").strip().lower()
    if plain_user:
        user_hash = _sha256_hex(plain_user)
    if plain_pass:
        pass_hash = _sha256_hex(plain_pass)
    if not re.fullmatch(r"[0-9a-f]{64}", user_hash or ""):
        user_hash = ""
    if not re.fullmatch(r"[0-9a-f]{64}", pass_hash or ""):
        pass_hash = ""
    out["enabled"] = bool(out.get("enabled"))
    out["realm"] = str(out.get("realm") or "Light RID Scanner").strip() or "Light RID Scanner"
    try:
        out["session_ttl_min"] = max(1, min(10080, int(out.get("session_ttl_min") or 30)))
    except Exception:
        out["session_ttl_min"] = 30
    out["login_methods"] = _normalize_auth_login_methods(
        out.get("login_methods"),
        default_missing=("password", "passkey", "sso"),
        default_empty=[],
    )
    out["username_sha256"] = user_hash
    out["password_sha256"] = pass_hash
    out["sso_links"] = _normalize_sso_links(out.get("sso_links"))
    out["passkeys"] = _normalize_passkeys(out.get("passkeys"))
    return out

def _prepare_api_cfg_for_save(api_cfg: dict | None) -> dict:
    raw = dict(api_cfg) if isinstance(api_cfg, dict) else {}
    out = dict(raw)
    plain_token = str(out.get("token") or out.get("token_plain") or "").strip()
    token_hash = str(out.get("token_sha256") or "").strip().lower()
    if plain_token:
        token_hash = _sha256_hex(plain_token)
    if not re.fullmatch(r"[0-9a-f]{64}", token_hash or ""):
        token_hash = ""
    tokens = _normalize_api_tokens(out.get("tokens"), plain_token, token_hash)
    first = tokens[0] if tokens else {}
    out["enabled"] = bool(out.get("enabled"))
    out["tokens"] = tokens
    out["token"] = str(first.get("token") or "")
    out["token_sha256"] = str(first.get("token_sha256") or "")
    out["whitelist_enabled"] = bool(out.get("whitelist_enabled"))
    mode = str(out.get("whitelist_mode") or "allow").strip().lower()
    out["whitelist_mode"] = "deny" if mode in ("deny", "block", "black", "blacklist") else "allow"
    out["whitelist"] = _parse_whitelist_entries(out.get("whitelist"))
    out.pop("token_plain", None)
    return out

def _access_rule_empty_error(label: str, enabled: bool, mode: str, entries: list[str]) -> str | None:
    if not enabled:
        return None
    policy = str(mode or "allow").strip().lower()
    if policy in ("deny", "block", "black", "blacklist"):
        return None
    if not entries:
        return f"{label}白名单模式已开启，但地址列表为空或格式无效"
    return None

def _validate_security_sections(auth_cfg: dict | None, api_cfg: dict | None, web_cfg: dict | None = None) -> str | None:
    auth = _prepare_auth_cfg_for_save(auth_cfg)
    api = _prepare_api_cfg_for_save(api_cfg)
    web = web_cfg if isinstance(web_cfg, dict) else {}
    if not list(auth.get("login_methods") or []):
        return "至少保留一种网页登录方式"
    if bool(auth.get("enabled")) and ("password" not in list(auth.get("login_methods") or [])):
        passkey_ready = any(bool(item.get("enabled", True)) for item in _normalize_passkeys(auth.get("passkeys")))
        sso_ready = any(bool(_sso_link_state(item).get("active")) for item in _normalize_sso_links(auth.get("sso_links")))
        if (not passkey_ready) and (not sso_ready):
            return "关闭账号密码登录前，至少先准备一把可用 PassKey 或一条有效的 SSO URL 登录链接"
    if bool(auth.get("enabled")) and (not _auth_hashes_present(auth)):
        return "启用网页登录鉴权前，必须先设置网页登录账号和密码"
    api_rule_err = _access_rule_empty_error(
        "API ",
        bool(api.get("whitelist_enabled")) and _api_tokens_have_secret(api),
        str(api.get("whitelist_mode") or "allow"),
        list(api.get("whitelist") or []),
    )
    if api_rule_err:
        return api_rule_err
    web_rule_err = _access_rule_empty_error(
        "网页访问",
        bool(web.get("access_list_enabled")),
        str(web.get("access_list_mode") or "allow"),
        _parse_whitelist_entries(web.get("access_list")),
    )
    if web_rule_err:
        return web_rule_err
    if bool(api.get("enabled")):
        if not bool(auth.get("enabled")):
            return "启用外部 API 前，必须先启用网页登录鉴权"
        if not _auth_hashes_present(auth):
            return "启用外部 API 前，必须先设置网页登录账号和密码"
        if not _api_tokens_have_secret(api):
            return "启用外部 API 前，必须先设置 API Token"
    return None

def _prepare_security_cfg_for_save(cfg: dict | None) -> tuple[dict, str | None]:
    out = dict(cfg) if isinstance(cfg, dict) else {}
    auth_raw = out.get("auth") if isinstance(out.get("auth"), dict) else {}
    api_raw = out.get("api") if isinstance(out.get("api"), dict) else {}
    web_raw = out.get("web") if isinstance(out.get("web"), dict) else {}
    auth_next = _prepare_auth_cfg_for_save(auth_raw)
    api_next = _prepare_api_cfg_for_save(api_raw)
    err = _validate_security_sections(auth_next, api_next, web_raw)
    out["auth"] = auth_next
    out["api"] = api_next
    return out, err

def _normalize_auth_cfg(cfg: dict | None) -> dict:
    base = dict(AUTH_CFG)
    plain_user = ""
    plain_pass = ""
    if isinstance(cfg, dict):
        auth = cfg.get("auth")
        if isinstance(auth, dict):
            for k in base.keys():
                if k in auth:
                    base[k] = auth.get(k)
            plain_user = str(auth.get("username") or "").strip()
            plain_pass = str(auth.get("password") or "")
    base["enabled"] = bool(base.get("enabled"))
    base["realm"] = str(base.get("realm") or "Light RID Scanner").strip() or "Light RID Scanner"
    try:
        base["session_ttl_min"] = max(1, min(10080, int(base.get("session_ttl_min") or 30)))
    except Exception:
        base["session_ttl_min"] = 30
    base["login_methods"] = _normalize_auth_login_methods(
        base.get("login_methods"),
        default_missing=("password", "passkey", "sso"),
        default_empty=("password", "passkey", "sso"),
    )
    u = str(base.get("username_sha256") or "").strip().lower()
    p = str(base.get("password_sha256") or "").strip().lower()
    if (not u) and plain_user:
        u = _sha256_hex(plain_user)
        _log("[WARN] auth.username detected in plain text; converted to SHA-256 in memory")
    if (not p) and plain_pass:
        p = _sha256_hex(plain_pass)
        _log("[WARN] auth.password detected in plain text; converted to SHA-256 in memory")
    if not re.fullmatch(r"[0-9a-f]{64}", u or ""):
        u = ""
    if not re.fullmatch(r"[0-9a-f]{64}", p or ""):
        p = ""
    base["username_sha256"] = u
    base["password_sha256"] = p
    base["sso_links"] = _normalize_sso_links(base.get("sso_links"))
    base["passkeys"] = _normalize_passkeys(base.get("passkeys"))
    if base["enabled"] and (not u or not p):
        _log("[WARN] auth enabled but username/password hash missing, fallback disabled")
        base["enabled"] = False
    return base

def _mask_secret(value: str | None, keep: int = 4) -> str:
    raw = str(value or "")
    if not raw:
        return ""
    keep = max(1, int(keep or 1))
    if len(raw) <= keep * 2:
        return "*" * len(raw)
    return raw[:keep] + ("*" * max(4, len(raw) - keep * 2)) + raw[-keep:]

def _normalize_wecom_webhooks(raw_list, legacy_key: str = "") -> list[dict]:
    items: list[dict] = []
    seen: set[str] = set()
    src: list = []
    legacy_key = str(legacy_key or "").strip()
    if legacy_key:
        src.append({"name": "默认通道", "key": legacy_key, "enabled": True})
    if isinstance(raw_list, list):
        src.extend(raw_list)
    elif raw_list not in (None, "", []):
        src.append(raw_list)
    for idx, item in enumerate(src, 1):
        if isinstance(item, dict):
            name = str(item.get("name") or f"通道 {idx}").strip() or f"通道 {idx}"
            key = str(item.get("key") or "").strip()
            enabled = bool(item.get("enabled", True))
        else:
            name = f"通道 {idx}"
            key = str(item or "").strip()
            enabled = True
        if not key or key in seen:
            continue
        seen.add(key)
        items.append({
            "name": name,
            "key": key,
            "enabled": enabled,
        })
    return items

def _normalize_alarm_zone_item(zone, idx: int = 1) -> dict:
    base = dict(WEB_CFG.get("alarm_zone") or {})
    zone = zone if isinstance(zone, dict) else {}
    item = {
        "enabled": bool(zone.get("enabled", base.get("enabled", False))),
        "name": str(zone.get("name") or base.get("name") or f"报警区域 {idx}").strip() or f"报警区域 {idx}",
    }
    for k, lo, hi in (
        ("lat1", -90.0, 90.0),
        ("lat2", -90.0, 90.0),
        ("lon1", -180.0, 180.0),
        ("lon2", -180.0, 180.0),
    ):
        try:
            raw_v = zone.get(k)
            val = None if raw_v in (None, "") else float(raw_v)
            if val is not None and not (lo <= val <= hi):
                val = None
        except Exception:
            val = None
        item[k] = val
    if None in (item["lat1"], item["lon1"], item["lat2"], item["lon2"]):
        item["enabled"] = False
    return item

def _normalize_alarm_zones(raw_list, legacy_zone=None) -> list[dict]:
    src: list = []
    if isinstance(raw_list, list):
        src.extend(raw_list)
    elif raw_list not in (None, "", []):
        src.append(raw_list)
    if (not src) and isinstance(legacy_zone, dict):
        src.append(legacy_zone)
    items: list[dict] = []
    for idx, item in enumerate(src, 1):
        norm = _normalize_alarm_zone_item(item, idx=idx)
        has_coords = any(norm.get(k) is not None for k in ("lat1", "lon1", "lat2", "lon2"))
        if not has_coords and not bool(norm.get("enabled")) and str(norm.get("name") or "").strip() in ("", "报警区域", f"报警区域 {idx}"):
            continue
        items.append(norm)
    return items

def _notify_wecom_targets(cfg: dict | None = None) -> list[dict]:
    source = cfg if isinstance(cfg, dict) else NOTIFY_CFG
    hooks = _normalize_wecom_webhooks(source.get("wecom_webhooks"), source.get("wecom_webhook_key") or "")
    return [x for x in hooks if x.get("enabled") and str(x.get("key") or "").strip()]

def _alarm_zone_names_for_point(lat, lon) -> list[str]:
    try:
        lat_f = float(lat)
        lon_f = float(lon)
    except Exception:
        return []
    if not (-90.0 <= lat_f <= 90.0 and -180.0 <= lon_f <= 180.0):
        return []
    try:
        zones = _normalize_alarm_zones(WEB_CFG.get("alarm_zones"), WEB_CFG.get("alarm_zone"))
    except Exception:
        zones = []
    hits: list[str] = []
    for idx, z in enumerate(zones):
        if not isinstance(z, dict) or not bool(z.get("enabled")):
            continue
        try:
            lat1 = float(z.get("lat1"))
            lat2 = float(z.get("lat2"))
            lon1 = float(z.get("lon1"))
            lon2 = float(z.get("lon2"))
        except Exception:
            continue
        south, north = min(lat1, lat2), max(lat1, lat2)
        west, east = min(lon1, lon2), max(lon1, lon2)
        if south <= lat_f <= north and west <= lon_f <= east:
            name = str(z.get("name") or f"报警区域 {idx + 1}").strip() or f"报警区域 {idx + 1}"
            hits.append(name)
    return hits

def _normalize_api_cfg(cfg: dict | None) -> dict:
    base = dict(API_CFG)
    if isinstance(cfg, dict):
        api = cfg.get("api")
        if isinstance(api, dict):
            for k in base.keys():
                if k in api:
                    base[k] = api.get(k)
    base = _prepare_api_cfg_for_save(base)
    if base.get("token") and not str(base.get("token_sha256") or "").strip():
        base["token_sha256"] = _sha256_hex(str(base.get("token") or "").strip())
        _log("[WARN] api.token detected in plain text; converted to SHA-256 in memory")
    auth_cfg = _normalize_auth_cfg(cfg)
    if base["enabled"] and not _api_tokens_have_secret(base):
        _log("[WARN] api token enabled but token hash missing, fallback disabled")
        base["enabled"] = False
    if base["enabled"] and not bool(auth_cfg.get("enabled")):
        _log("[WARN] api enabled but auth disabled, fallback disabled")
        base["enabled"] = False
    if base["enabled"] and not _auth_hashes_present(auth_cfg):
        _log("[WARN] api enabled but auth credentials missing, fallback disabled")
        base["enabled"] = False
    api_rule_err = _access_rule_empty_error(
        "API ",
        bool(base.get("whitelist_enabled")) and _api_tokens_have_secret(base),
        str(base.get("whitelist_mode") or "allow"),
        list(base.get("whitelist") or []),
    )
    if api_rule_err:
        _log("[WARN] " + api_rule_err)
        base["enabled"] = False
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

def _firmware_type_key(v: str | None) -> str:
    s = str(v or "").strip().lower()
    if s in ("new", "new_fw", "new_firmware", "新固件", "新版固件"):
        return "new"
    if s in ("old", "legacy", "old_fw", "old_firmware", "老固件", "旧固件", "旧版固件"):
        return "old"
    return "old"

def _firmware_type_display(v: str | None) -> str:
    return "新版固件" if _firmware_type_key(v) == "new" else "旧版固件"

def _uas_id_clean(v) -> str:
    try:
        s = str(v or "")
    except Exception:
        return ""
    s = "".join(c for c in s.strip() if 32 <= ord(c) <= 126)
    return s[:64]

def init_ap_from_config(cfg: dict | None) -> None:
    global AP_CFG
    AP_CFG = _normalize_ap_cfg(cfg)

def init_model_update_from_config(cfg: dict | None) -> None:
    global MODEL_UPDATE_CFG
    MODEL_UPDATE_CFG = _normalize_model_update_cfg(cfg)

def init_config_update_from_config(cfg: dict | None) -> None:
    global CONFIG_UPDATE_CFG
    CONFIG_UPDATE_CFG = _normalize_config_update_cfg(cfg)

def init_app_update_from_config(cfg: dict | None) -> None:
    global APP_UPDATE_CFG
    APP_UPDATE_CFG = _normalize_app_update_cfg(cfg)

def init_metrics_from_config(cfg: dict | None) -> None:
    global METRICS_CFG
    METRICS_CFG = _normalize_metrics_cfg(cfg)

def init_auth_from_config(cfg: dict | None) -> None:
    global AUTH_CFG, AUTH_SESSION_TTL_SEC
    AUTH_CFG = _normalize_auth_cfg(cfg)
    AUTH_SESSION_TTL_SEC = int(max(60, float(AUTH_CFG.get("session_ttl_min") or 30) * 60.0))
    now_wall = time.time()
    max_exp = now_wall + float(AUTH_SESSION_TTL_SEC)
    with auth_session_lock:
        for tok, exp in list(auth_sessions.items()):
            if float(exp or 0.0) > max_exp:
                auth_sessions[tok] = max_exp

def init_api_from_config(cfg: dict | None) -> None:
    global API_CFG
    API_CFG = _normalize_api_cfg(cfg)

def init_notify_from_config(cfg: dict | None) -> None:
    global NOTIFY_CFG
    NOTIFY_CFG = _normalize_notify_cfg(cfg)
    hooks = _notify_wecom_targets(NOTIFY_CFG)
    if NOTIFY_CFG.get("enabled") and hooks:
        _log(f"[INFO] WeCom robot notification enabled ({len(hooks)} channel(s), online-only)")
    else:
        _log("[INFO] notify disabled (missing key or disabled)")

def reload_runtime_config(cfg: dict | None) -> tuple[bool, str]:
    global APP_CONFIG, PRINT_INTERVAL, MIN_GAP, CHANGE_ON_RSSI, CHANGE_ON_PL, RSSI_DELTA, DEBUG_MODE
    if not isinstance(cfg, dict):
        return False, "invalid config root"
    APP_CONFIG = _deep_merge_dict(default_app_config(), cfg)
    init_web_from_config(APP_CONFIG)
    init_ap_from_config(APP_CONFIG)
    init_model_update_from_config(APP_CONFIG)
    init_config_update_from_config(APP_CONFIG)
    init_app_update_from_config(APP_CONFIG)
    init_metrics_from_config(APP_CONFIG)
    init_auth_from_config(APP_CONFIG)
    init_api_from_config(APP_CONFIG)
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
    alarm_hits = e.get("alarm_zone_hits")
    if not isinstance(alarm_hits, list):
        alarm_hits = _alarm_zone_names_for_point(lat, lon)
    alarm_s = ""
    if alarm_hits:
        alarm_s = "\n报警区域: " + "、".join(str(x) for x in alarm_hits if str(x).strip())
    return (
        f"[RID{event_title}] {ts_s}\n"
        f"SN: {sn}\n"
        f"机型/ID: {model} / {it}\n"
        f"MAC/信道/信号: {mac} / {ch_s} / {rssi}\n"
        f"位置: {loc_s}  高程: {alt_s}\n"
        f"速度: {spd_s}  垂速: {vsp_s}  包数: {pkts}"
        f"{alarm_s}"
    )

def _notify_zone_alarm_text(e: dict, zone_names: list[str], now_wall: float) -> str:
    sn = str(e.get("sn", ""))
    model = str(e.get("model", "N/A"))
    lat = e.get("lat")
    lon = e.get("lon")
    try:
        loc_s = f"{float(lat):.6f}, {float(lon):.6f}" if lat is not None and lon is not None else "N/A"
    except Exception:
        loc_s = "N/A"
    alt = e.get("alt")
    spd = e.get("speed")
    try:
        alt_s = f"{float(alt):.1f}m" if alt is not None else "N/A"
    except Exception:
        alt_s = "N/A"
    try:
        spd_s = f"{float(spd):.1f}m/s" if spd is not None else "N/A"
    except Exception:
        spd_s = "N/A"
    ts_s = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now_wall))
    zones = "、".join(str(x) for x in (zone_names or []) if str(x).strip()) or "报警区域"
    return (
        f"[RID区域告警] {ts_s}\n"
        f"SN: {sn}\n"
        f"机型: {model}\n"
        f"进入区域: {zones}\n"
        f"位置: {loc_s}  高程: {alt_s}\n"
        f"速度: {spd_s}"
    )

def _notify_lost_text(e: dict, age_sec: float, now_wall: float) -> str:
    sn = str(e.get("sn", ""))
    model = str(e.get("model", "N/A"))
    mac = str(e.get("src_mac") or "-")
    ts_s = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(now_wall))
    try:
        age_s = f"{float(age_sec):.0f}s"
    except Exception:
        age_s = "N/A"
    return (
        f"[RID离线] {ts_s}\n"
        f"SN: {sn}\n"
        f"机型: {model}\n"
        f"MAC: {mac}\n"
        f"未收到数据: {age_s}"
    )

def _notification_kind(kind: str | None) -> str:
    k = str(kind or "info").strip().lower()
    return k if k in ("info", "ok", "warn") else "info"

def _notification_add(text: str, kind: str = "info", source: str = "server") -> dict | None:
    global notification_seq
    msg = str(text or "").strip()
    if not msg:
        return None
    if len(msg) > 2000:
        msg = msg[:1997] + "..."
    with notification_lock:
        notification_seq += 1
        item = {
            "id": notification_seq,
            "text": msg,
            "kind": _notification_kind(kind),
            "source": str(source or "server")[:40],
            "ts": int(time.time() * 1000),
        }
        notification_items.appendleft(item)
        return dict(item)

def _notification_payload(limit: int = NOTIFICATION_CENTER_MAX) -> dict:
    try:
        limit = int(limit)
    except Exception:
        limit = NOTIFICATION_CENTER_MAX
    limit = max(1, min(NOTIFICATION_CENTER_MAX, limit))
    with notification_lock:
        items = [dict(x) for x in list(notification_items)[:limit]]
        seq = int(notification_seq)
    return {"ok": True, "seq": seq, "count": len(items), "items": items}

def _notification_delete(item_id) -> bool:
    target = str(item_id or "").strip()
    if not target:
        return False
    with notification_lock:
        before = len(notification_items)
        kept = [x for x in notification_items if str((x or {}).get("id") or "") != target]
        notification_items.clear()
        notification_items.extend(kept[:NOTIFICATION_CENTER_MAX])
        return len(notification_items) != before

def _notification_clear() -> int:
    with notification_lock:
        n = len(notification_items)
        notification_items.clear()
        return n

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
    targets = _notify_wecom_targets(NOTIFY_CFG)
    if not targets:
        return False
    now_wall = float(now_wall or time.time())
    content = _notify_online_text(e, event_title, now_wall)
    for item in targets:
        _notify_queue_put({
            "type": "wecom_text",
            "key": str(item.get("key") or "").strip(),
            "content": content,
            "timeout_sec": int(NOTIFY_CFG.get("send_timeout_sec") or 8),
        })
    return True

def queue_zone_alarm_notification(e: dict, zone_names: list[str], now_wall: float | None = None) -> bool:
    if not NOTIFY_CFG.get("enabled"):
        return False
    targets = _notify_wecom_targets(NOTIFY_CFG)
    if not targets:
        return False
    now_wall = float(now_wall or time.time())
    content = _notify_zone_alarm_text(e, zone_names, now_wall)
    for item in targets:
        _notify_queue_put({
            "type": "wecom_text",
            "key": str(item.get("key") or "").strip(),
            "content": content,
            "timeout_sec": int(NOTIFY_CFG.get("send_timeout_sec") or 8),
        })
    return True

def send_test_notification_from_config(cfg: dict | None = None) -> tuple[bool, str]:
    notify_cfg = _normalize_notify_cfg(cfg) if isinstance(cfg, dict) else dict(NOTIFY_CFG)
    if not notify_cfg.get("enabled"):
        return False, "notify disabled"
    targets = _notify_wecom_targets(notify_cfg)
    if not targets:
        return False, "missing wecom webhook"
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
    content = _notify_online_text(test_e, "上线(测试)", now_wall)
    timeout_sec = int(notify_cfg.get("send_timeout_sec") or 8)
    results: list[str] = []
    ok_count = 0
    for item in targets:
        ok, resp = _wecom_send_text(str(item.get("key") or "").strip(), content, timeout_sec=timeout_sec)
        if ok:
            ok_count += 1
        results.append(f"{item.get('name') or '通道'}: {'OK' if ok else 'FAIL'} {resp}")
    return (ok_count > 0), " | ".join(results)

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
        return "手机/热点"
    if any(k in v for k in ("tp-link", "h3c", "ruijie", "ubiquiti", "mikrotik", "netgear", "asus", "cisco", "tenda", "meraki")):
        return "路由/AP"
    if s.startswith("DIRECT-"):
        return "直连/Wi-Fi"
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
        headers={"User-Agent": APP_HTTP_USER_AGENT + " (+OUI cache)"},
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
        return "加载中"
    with oui_db_lock:
        oui_vendor_cache[key] = "未知"
    return "未知"

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
            "vendor": vendor or str(e.get("vendor") or "未知"),
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
    sn_key = re.sub(r"[^0-9A-Za-z]+", "", str(sn or "")).upper()
    if not sn_key:
        return "N/A"
    items = sorted(MODEL_MAP.items(), key=lambda kv: len(str(kv[0] or "")), reverse=True)
    for pref, model in items:
        pref_key = re.sub(r"[^0-9A-Za-z]+", "", str(pref or "")).upper()
        if pref_key and sn_key.startswith(pref_key):
            return model
    return "N/A"

def _resolve_model_name(sn: str, scan_type: str | None = None, current_model: str | None = None) -> str:
    if _scan_type_key(scan_type) == "phone":
        return "WiFi快传"
    mapped = _model_from_sn(sn)
    if mapped != "N/A":
        return mapped
    cur = str(current_model or "").strip()
    return cur if (cur and cur.upper() != "N/A") else "N/A"

def _refresh_models_locked(*, only_na: bool = False) -> tuple[int, int]:
    """Refresh model names from SN mapping for both history/state tables.
    Must be called with `state_lock` held.
    Returns (history_changed, state_changed).
    """
    history_changed = 0
    state_changed = 0
    for sn, h in history_table.items():
        if not isinstance(h, dict):
            continue
        old = str(h.get("model") or "").strip()
        if only_na and old and old.upper() != "N/A":
            continue
        sn_key = str(h.get("sn") or sn or "")
        new = _resolve_model_name(sn_key, h.get("scan_type"), old)
        old_norm = old if old else "N/A"
        if new != old_norm:
            h["model"] = new
            history_changed += 1
    for sn, e in state_table.items():
        if not isinstance(e, dict):
            continue
        old = str(e.get("model") or "").strip()
        if only_na and old and old.upper() != "N/A":
            continue
        sn_key = str(e.get("sn") or sn or "")
        new = _resolve_model_name(sn_key, e.get("scan_type"), old)
        old_norm = old if old else "N/A"
        if new != old_norm:
            e["model"] = new
            state_changed += 1
    return history_changed, state_changed

def load_model_map(path: str) -> None:
    global MODEL_MAP
    try:
        with open(path, "r", encoding="utf-8") as f:
            obj = json.load(f)
        if isinstance(obj, dict):
            MODEL_MAP = {str(k): str(v) for k, v in obj.items()}
            _log(f"[INFO] model map loaded: {path} ({len(MODEL_MAP)} entries)")
            with state_lock:
                h_changed, s_changed = _refresh_models_locked(only_na=False)
                if h_changed:
                    _history_mark_dirty()
            if h_changed or s_changed:
                _log(f"[INFO] model remap applied: history={h_changed}, live={s_changed}")
        else:
            _log(f"[WARN] model map format invalid: {path}")
    except FileNotFoundError:
        _log(f"[WARN] model map not found: {path}")
    except Exception as e:
        _log(f"[WARN] model map load failed: {e}")

def _model_map_target_path() -> str:
    try:
        basic = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
        if isinstance(basic, dict):
            raw = str(basic.get("model_map") or "").strip()
            if raw:
                return os.path.abspath(raw)
    except Exception:
        pass
    return os.path.abspath(os.path.join(os.getcwd(), "rid_models.json"))

def _model_map_items_from_dict(obj: dict | None) -> list[dict]:
    src = obj if isinstance(obj, dict) else {}
    return [
        {"prefix": str(k), "model": str(v)}
        for k, v in sorted(src.items(), key=lambda kv: str(kv[0]).upper())
    ]

def _read_model_map_file(path: str) -> dict[str, str]:
    with open(path, "r", encoding="utf-8") as f:
        obj = json.load(f)
    return _validate_model_map_payload(obj)

def _model_map_editor_payload(warning: str = "") -> dict:
    target = _model_map_target_path()
    data: dict[str, str] = {}
    warn = warning
    try:
        data = _read_model_map_file(target)
    except FileNotFoundError:
        data = dict(MODEL_MAP)
        warn = warn or "识别库文件不存在，保存后会创建。"
    except Exception as e:
        data = dict(MODEL_MAP)
        warn = warn or f"识别库文件读取失败，当前显示内存中的识别库：{e}"
    return {
        "ok": True,
        "path": target,
        "count": len(data),
        "items": _model_map_items_from_dict(data),
        "state": _model_update_status_payload(),
        "warning": warn,
    }

def _model_update_status_payload() -> dict:
    with model_update_lock:
        state = dict(MODEL_UPDATE_STATE)
    state["enabled"] = bool(MODEL_UPDATE_CFG.get("enabled", True))
    state["url"] = str(MODEL_UPDATE_CFG.get("url") or RID_MODELS_UPDATE_URL_DEFAULT)
    state["target"] = _model_map_target_path()
    state["interval_sec"] = int(MODEL_UPDATE_CHECK_INTERVAL_SEC)
    state["loaded_count"] = int(len(MODEL_MAP))
    return state

def _validate_model_map_payload(obj) -> dict[str, str]:
    if not isinstance(obj, dict):
        raise ValueError("识别库格式错误：根节点必须是对象")
    out: dict[str, str] = {}
    for k, v in obj.items():
        key = re.sub(r"[^0-9A-Za-z]+", "", str(k or "")).upper()
        val = str(v or "").strip()
        if not key or not val:
            continue
        if not re.fullmatch(r"[0-9A-Z]{4,32}", key):
            continue
        out[key] = val
    if not out:
        raise ValueError("识别库为空或没有有效前缀")
    return out

def _model_map_from_editor_items(items) -> dict[str, str]:
    if isinstance(items, dict):
        return _validate_model_map_payload(items)
    if not isinstance(items, list):
        raise ValueError("items must be a list")
    raw: dict[str, str] = {}
    for row in items:
        if not isinstance(row, dict):
            continue
        pref = re.sub(r"[^0-9A-Za-z]+", "", str(row.get("prefix") or "")).upper()
        model = str(row.get("model") or "").strip()
        if not pref and not model:
            continue
        raw[pref] = model
    return _validate_model_map_payload(raw)

def _write_model_map_file(next_map: dict[str, str], tag: str = "models") -> dict:
    target = _model_map_target_path()
    with model_map_file_lock:
        running = False
        with model_update_lock:
            running = bool(MODEL_UPDATE_STATE.get("running"))
        if running:
            return {"ok": False, "error": "识别库在线更新正在运行，请稍后再保存。", "state": _model_update_status_payload()}
        parent = os.path.dirname(target)
        if parent:
            os.makedirs(parent, exist_ok=True)
        b_ok, backup_path = create_config_backup(target, tag=tag)
        if not b_ok:
            return {"ok": False, "error": "backup failed: " + backup_path, "state": _model_update_status_payload()}
        tmp_path = target + ".tmp"
        with open(tmp_path, "w", encoding="utf-8") as f:
            json.dump(next_map, f, ensure_ascii=False, indent=2)
            f.write("\n")
        os.replace(tmp_path, target)
        load_model_map(target)
    try:
        save_history_store(force=True)
    except Exception:
        pass
    msg = f"识别库已保存：{len(next_map)} 条"
    _op_log("model-map-save", f"count={len(next_map)} target={target}", ok=True)
    _notification_add(msg, "ok", "server")
    payload = _model_map_editor_payload()
    payload.update({"ok": True, "message": msg, "backup_path": backup_path})
    return payload

def save_model_map_entries(items) -> dict:
    next_map = _model_map_from_editor_items(items)
    return _write_model_map_file(next_map, tag="models")

def upsert_model_map_entry(prefix: str = "", model: str = "", sn: str = "") -> dict:
    clean_prefix = re.sub(r"[^0-9A-Za-z]+", "", str(prefix or "")).upper()
    clean_sn = re.sub(r"[^0-9A-Za-z]+", "", str(sn or "")).upper()
    if not clean_prefix and clean_sn and not str(sn or "").upper().startswith("MAC:"):
        clean_prefix = clean_sn[:8]
    clean_model = str(model or "").strip()
    single = _validate_model_map_payload({clean_prefix: clean_model})
    target = _model_map_target_path()
    try:
        current = _read_model_map_file(target)
    except FileNotFoundError:
        current = dict(MODEL_MAP)
    current.update(single)
    return _write_model_map_file(_validate_model_map_payload(current), tag="models_upsert")

def update_model_map_from_url(manual: bool = False, url_override: str | None = None) -> dict:
    url = str(url_override or MODEL_UPDATE_CFG.get("url") or RID_MODELS_UPDATE_URL_DEFAULT).strip()
    if not (url.startswith("https://") or url.startswith("http://")):
        return {"ok": False, "error": "识别库更新地址必须以 http:// 或 https:// 开头", "state": _model_update_status_payload()}
    target = _model_map_target_path()
    busy = False
    with model_update_lock:
        if MODEL_UPDATE_STATE.get("running"):
            busy = True
        else:
            MODEL_UPDATE_STATE["running"] = True
            MODEL_UPDATE_STATE["last_check_ts"] = time.time()
            MODEL_UPDATE_STATE["last_error"] = ""
            MODEL_UPDATE_STATE["last_message"] = "正在检查识别库"
    if busy:
        return {"ok": False, "error": "识别库更新正在运行", "state": _model_update_status_payload()}
    try:
        req = urllib.request.Request(
            url,
            headers={"User-Agent": APP_HTTP_USER_AGENT + " (+model-map update)"},
            method="GET",
        )
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = resp.read(2 * 1024 * 1024)
        if not data:
            raise ValueError("远端返回为空")
        obj = json.loads(data.decode("utf-8", errors="replace"))
        next_map = _validate_model_map_payload(obj)
        with model_map_file_lock:
            parent = os.path.dirname(target)
            if parent:
                os.makedirs(parent, exist_ok=True)
            if os.path.exists(target):
                try:
                    shutil.copy2(target, target + ".bak")
                except Exception:
                    pass
            tmp_path = target + ".tmp"
            with open(tmp_path, "w", encoding="utf-8") as f:
                json.dump(next_map, f, ensure_ascii=False, indent=2)
                f.write("\n")
            os.replace(tmp_path, target)
            load_model_map(target)
        try:
            save_history_store(force=True)
        except Exception:
            pass
        msg = f"识别库已更新：{len(next_map)} 条"
        with model_update_lock:
            MODEL_UPDATE_STATE["running"] = False
            MODEL_UPDATE_STATE["last_success_ts"] = time.time()
            MODEL_UPDATE_STATE["last_error"] = ""
            MODEL_UPDATE_STATE["last_message"] = msg
            MODEL_UPDATE_STATE["last_count"] = len(next_map)
        _op_log("model-update", f"manual={manual} count={len(next_map)} target={target}", ok=True)
        _notification_add(msg, "ok", "server")
        return {"ok": True, "message": msg, "count": len(next_map), "target": target, "state": _model_update_status_payload()}
    except Exception as e:
        msg = str(e)
        with model_update_lock:
            MODEL_UPDATE_STATE["running"] = False
            MODEL_UPDATE_STATE["last_error"] = msg
            MODEL_UPDATE_STATE["last_message"] = "识别库更新失败"
        _op_log("model-update", f"manual={manual} error={msg}", ok=False)
        if manual:
            _notification_add("识别库更新失败：" + msg, "warn", "server")
        return {"ok": False, "error": msg, "target": target, "state": _model_update_status_payload()}

def model_update_loop() -> None:
    time.sleep(10.0)
    while True:
        try:
            if bool(MODEL_UPDATE_CFG.get("enabled", True)):
                with model_update_lock:
                    last = float(MODEL_UPDATE_STATE.get("last_check_ts") or 0.0)
                    running = bool(MODEL_UPDATE_STATE.get("running"))
                if (not running) and (time.time() - last >= MODEL_UPDATE_CHECK_INTERVAL_SEC):
                    update_model_map_from_url(manual=False)
        except Exception as e:
            _log(f"[WARN] model update loop failed: {e}")
        time.sleep(300.0)

# -----------------------------------------------------------------------------
# Remote config update
# -----------------------------------------------------------------------------
def _config_update_status_payload() -> dict:
    with config_update_lock:
        state = dict(CONFIG_UPDATE_STATE)
    state["enabled"] = bool(CONFIG_UPDATE_CFG.get("enabled", False))
    state["url"] = str(CONFIG_UPDATE_CFG.get("url") or "")
    state["target"] = APP_CONFIG_PATH or ""
    return state

def update_config_from_url(manual: bool = False, url_override: str | None = None) -> dict:
    url = str(url_override or CONFIG_UPDATE_CFG.get("url") or "").strip()
    if not url:
        return {"ok": False, "error": "config update url missing", "state": _config_update_status_payload()}
    if not (url.startswith("https://") or url.startswith("http://")):
        return {"ok": False, "error": "config update url must start with http:// or https://", "state": _config_update_status_payload()}
    if not APP_CONFIG_PATH:
        return {"ok": False, "error": "config path missing", "state": _config_update_status_payload()}
    busy = False
    with config_update_lock:
        if CONFIG_UPDATE_STATE.get("running"):
            busy = True
        else:
            CONFIG_UPDATE_STATE["running"] = True
            CONFIG_UPDATE_STATE["last_check_ts"] = time.time()
            CONFIG_UPDATE_STATE["last_error"] = ""
            CONFIG_UPDATE_STATE["last_message"] = "downloading config"
    if busy:
        return {"ok": False, "error": "config update already running", "state": _config_update_status_payload()}
    try:
        req = urllib.request.Request(
            url,
            headers={"User-Agent": APP_HTTP_USER_AGENT + " (+config update)"},
            method="GET",
        )
        with urllib.request.urlopen(req, timeout=20) as resp:
            data = resp.read(2 * 1024 * 1024)
        if not data:
            raise ValueError("empty response")
        parsed = json.loads(data.decode("utf-8", errors="replace"))
        if not isinstance(parsed, dict):
            raise ValueError("remote config root must be object")
        # Remote config updates follow the same guard rails as manual saves:
        # merge defaults, validate security, backup, save, reload, rollback.
        candidate = _deep_merge_dict(default_app_config(), parsed)
        candidate, guard_err = _prepare_security_cfg_for_save(candidate)
        if guard_err:
            raise ValueError(guard_err)
        b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="config_update")
        if not b_ok:
            raise ValueError("backup failed: " + backup_path)
        ok, msg = save_app_config(APP_CONFIG_PATH, candidate)
        if not ok:
            raise ValueError("save failed: " + msg)
        cfg_loaded = load_app_config(APP_CONFIG_PATH)
        r_ok, r_msg = reload_runtime_config(cfg_loaded)
        if not r_ok:
            restore_config_backup(APP_CONFIG_PATH, backup_path)
            raise ValueError("reload failed: " + r_msg)
        msg = f"config updated from url; keys={len(candidate.keys())}"
        with config_update_lock:
            CONFIG_UPDATE_STATE["running"] = False
            CONFIG_UPDATE_STATE["last_success_ts"] = time.time()
            CONFIG_UPDATE_STATE["last_error"] = ""
            CONFIG_UPDATE_STATE["last_message"] = msg
            CONFIG_UPDATE_STATE["last_count"] = len(candidate.keys())
        _op_log("config-update", f"manual={manual} target={APP_CONFIG_PATH}", ok=True)
        return {"ok": True, "message": msg, "saved_to": APP_CONFIG_PATH, "state": _config_update_status_payload()}
    except Exception as e:
        msg = str(e)
        with config_update_lock:
            CONFIG_UPDATE_STATE["running"] = False
            CONFIG_UPDATE_STATE["last_error"] = msg
            CONFIG_UPDATE_STATE["last_message"] = "config update failed"
        _op_log("config-update", f"manual={manual} error={msg}", ok=False)
        return {"ok": False, "error": msg, "state": _config_update_status_payload()}

def config_update_loop() -> None:
    time.sleep(20.0)
    while True:
        try:
            if bool(CONFIG_UPDATE_CFG.get("enabled", False)):
                with config_update_lock:
                    last = float(CONFIG_UPDATE_STATE.get("last_check_ts") or 0.0)
                    running = bool(CONFIG_UPDATE_STATE.get("running"))
                if (not running) and (time.time() - last >= 24 * 3600):
                    update_config_from_url(manual=False)
        except Exception as e:
            _log(f"[WARN] config update loop failed: {e}")
        time.sleep(300.0)

def start_config_update_worker() -> None:
    global config_update_worker_started
    if config_update_worker_started:
        return
    config_update_worker_started = True
    Thread(target=config_update_loop, daemon=True).start()

def start_model_update_worker() -> None:
    global model_update_worker_started
    if model_update_worker_started:
        return
    model_update_worker_started = True
    Thread(target=model_update_loop, daemon=True).start()

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

def _is_linux_host() -> bool:
    return platform.system().lower() == "linux"

def _is_root_user() -> bool:
    try:
        return bool(hasattr(os, "geteuid") and os.geteuid() == 0)
    except Exception:
        return False

def _command_path(name: str) -> str:
    try:
        return str(shutil.which(str(name or "").strip()) or "")
    except Exception:
        return ""

def _current_uid() -> int | None:
    try:
        if hasattr(os, "geteuid"):
            return int(os.geteuid())
    except Exception:
        pass
    return None

def _capability_bit(name: str) -> int | None:
    caps = {
        "CAP_NET_ADMIN": 12,
        "CAP_NET_RAW": 13,
    }
    return caps.get(str(name or "").strip().upper())

def _process_has_capabilities(names: tuple[str, ...] | list[str]) -> bool:
    if not _is_linux_host():
        return False
    try:
        wanted = [_capability_bit(str(x)) for x in names]
        wanted = [int(x) for x in wanted if x is not None]
        if not wanted:
            return False
        with open("/proc/self/status", "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                if line.startswith("CapEff:"):
                    value = int(line.split(":", 1)[1].strip(), 16)
                    return all((value & (1 << bit)) for bit in wanted)
    except Exception:
        pass
    return False

def _username_for_uid(uid: int | None) -> str:
    try:
        if uid is not None and _is_linux_host():
            import pwd
            return str(pwd.getpwuid(int(uid)).pw_name or "")
    except Exception:
        pass
    try:
        return str(os.environ.get("USER") or os.environ.get("USERNAME") or "")
    except Exception:
        return ""

def _local_user_exists(name: str) -> bool:
    user = str(name or "").strip()
    if not user or not _is_linux_host():
        return False
    try:
        import pwd
        pwd.getpwnam(user)
        return True
    except KeyError:
        return False
    except Exception:
        ok, _out, _rc = _run_program(["id", "-u", user], timeout=4)
        return bool(ok)

def _local_group_exists(name: str) -> bool:
    group = str(name or "").strip()
    if not group or not _is_linux_host():
        return False
    try:
        import grp
        grp.getgrnam(group)
        return True
    except KeyError:
        return False
    except Exception:
        ok, _out, _rc = _run_program(["getent", "group", group], timeout=4)
        return bool(ok)

def _sudo_available() -> bool:
    return bool(_is_linux_host() and _command_path("sudo"))

def _sudo_password_from_body(body: dict | None) -> str:
    if not isinstance(body, dict):
        return ""
    try:
        return str(body.get("sudo_password") or body.get("password") or "")
    except Exception:
        return ""

def _truncate_text(text: str, limit: int = 3600) -> str:
    raw = str(text or "").strip()
    if len(raw) <= limit:
        return raw
    return raw[:limit] + "\n...输出已截断..."

def _run_program(args: list[str], timeout: int = 30, env: dict | None = None, input_text: str | None = None) -> tuple[bool, str, int]:
    try:
        r = subprocess.run(
            [str(x) for x in args],
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
            input=input_text,
        )
        out = ((r.stdout or "") + ("\n" if r.stdout and r.stderr else "") + (r.stderr or "")).strip()
        return r.returncode == 0, _truncate_text(out), int(r.returncode)
    except Exception as e:
        return False, str(e), -1

def _run_privileged(args: list[str], timeout: int = 30, env: dict | None = None, sudo_password: str | None = None) -> tuple[bool, str, int]:
    cmd = [str(x) for x in args]
    if not cmd:
        return False, "empty command", -1
    if _is_root_user():
        return _run_program(cmd, timeout=timeout, env=env)
    sudo = _command_path("sudo")
    if not sudo:
        return False, "当前进程不是 root，且未检测到 sudo。", -1
    password = "" if sudo_password is None else str(sudo_password)
    if password:
        return _run_program([sudo, "-S", "-p", "", "--"] + cmd, timeout=timeout, env=env, input_text=password + "\n")
    return _run_program([sudo, "-n", "--"] + cmd, timeout=timeout, env=env)

def _systemctl(args: list[str], timeout: int = 20, sudo_password: str | None = None, privileged: bool = False) -> tuple[bool, str, int]:
    cmd = [_command_path("systemctl") or "systemctl"] + [str(x) for x in args]
    if privileged:
        return _run_privileged(cmd, timeout=timeout, sudo_password=sudo_password)
    return _run_program(cmd, timeout=timeout)

def _systemctl_privileged(args: list[str], timeout: int = 20, sudo_password: str | None = None) -> tuple[bool, str, int]:
    return _systemctl(args, timeout=timeout, sudo_password=sudo_password, privileged=True)

def _iw_manual_install_hint() -> str:
    return "请手动安装: sudo apt-get update && sudo apt-get install -y iw"

def _iw_missing_message() -> str:
    return "未检测到 iw 命令，无法枚举或切换无线网卡。"

def _set_iw_check_state(**updates) -> dict:
    with iw_check_lock:
        IW_CHECK_STATE.update(updates)
        return dict(IW_CHECK_STATE)

def _refresh_iw_check_state(message: str | None = None) -> dict:
    path = _command_path(IW_PACKAGE_NAME)
    available = bool(path)
    msg = str(message or "").strip()
    if not msg:
        msg = f"iw 可用: {path}" if available else _iw_missing_message()
    return _set_iw_check_state(
        checked=True,
        available=available,
        path=path,
        message=msg,
        manual_hint=("" if available else _iw_manual_install_hint()),
    )

def _iw_status_payload(refresh: bool = True) -> dict:
    with iw_check_lock:
        checked = bool(IW_CHECK_STATE.get("checked"))
    if refresh or not checked:
        snap = _refresh_iw_check_state()
    else:
        with iw_check_lock:
            snap = dict(IW_CHECK_STATE)
    snap["sudo_available"] = _sudo_available()
    snap["can_install"] = bool(_is_linux_host() and (_is_root_user() or _sudo_available()) and _command_path("apt-get"))
    snap["package"] = IW_PACKAGE_NAME
    return snap

def _install_iw_package(sudo_password: str | None = None) -> dict:
    existing = _iw_status_payload(refresh=True)
    if existing.get("available"):
        return {
            "ok": True,
            "installed": False,
            "message": "iw 已可用，无需安装。",
            "iw": existing,
        }
    _set_iw_check_state(install_attempted=True, install_ok=False)
    if not _is_linux_host():
        snap = _refresh_iw_check_state("当前主机不是 Linux，无法自动安装 iw。")
        return {"ok": False, "installed": False, "error": snap.get("message"), "iw": snap}
    if not _command_path("apt-get"):
        snap = _refresh_iw_check_state("未检测到 apt-get，无法自动安装 iw。")
        return {"ok": False, "installed": False, "error": snap.get("message"), "iw": snap}
    if not (_is_root_user() or _sudo_available()):
        snap = _refresh_iw_check_state("自动安装 iw 需要 root 或 sudo 提权。")
        return {"ok": False, "installed": False, "error": snap.get("message"), "iw": snap}

    env = dict(os.environ)
    env["DEBIAN_FRONTEND"] = "noninteractive"
    ok_update, out_update, rc_update = _run_privileged(["apt-get", "update"], timeout=300, env=env, sudo_password=sudo_password)
    if not ok_update:
        snap = _refresh_iw_check_state("apt-get update 失败，iw 未安装。")
        return {
            "ok": False,
            "installed": False,
            "error": snap.get("message"),
            "returncode": rc_update,
            "output": out_update,
            "iw": snap,
        }
    ok_install, out_install, rc_install = _run_privileged(["apt-get", "install", "-y", IW_PACKAGE_NAME], timeout=300, env=env, sudo_password=sudo_password)
    snap = _refresh_iw_check_state("iw 安装完成。" if ok_install else "apt-get install iw 失败。")
    installed = bool(ok_install and snap.get("available"))
    _set_iw_check_state(install_ok=installed)
    snap = _iw_status_payload(refresh=False)
    return {
        "ok": installed,
        "installed": installed,
        "error": "" if installed else str(snap.get("message") or "iw install failed"),
        "returncode": rc_install,
        "output": _truncate_text((out_update + "\n" + out_install).strip()),
        "iw": snap,
    }

def _prompt_install_iw_on_startup() -> bool:
    try:
        return bool(sys.stdin and sys.stdin.isatty() and sys.stdout and sys.stdout.isatty())
    except Exception:
        return False

def check_iw_available_on_startup() -> bool:
    snap = _iw_status_payload(refresh=True)
    if snap.get("available"):
        _log(f"[INFO] iw command available: {snap.get('path')}")
        return True

    msg = f"{snap.get('message') or _iw_missing_message()} {snap.get('manual_hint') or _iw_manual_install_hint()}"
    _log(f"[WARN] {msg}")
    _sniff_note_error(msg)
    if not (_is_linux_host() and _is_root_user() and _command_path("apt-get") and _prompt_install_iw_on_startup()):
        _log("[WARN] 启动环境无法交互确认自动安装 iw，请手动安装后重启服务。")
        return False

    try:
        answer = input("未检测到 iw，是否现在自动安装？这将执行 apt-get update && apt-get install -y iw [y/N]: ")
    except Exception:
        answer = ""
    if str(answer or "").strip().lower() not in ("y", "yes"):
        _log(f"[WARN] 已跳过 iw 自动安装。{_iw_manual_install_hint()}")
        return False

    rsp = _install_iw_package()
    if rsp.get("ok"):
        _log("[INFO] iw installed successfully")
        return True
    _log(f"[WARN] iw 自动安装失败: {rsp.get('error') or rsp.get('output') or 'unknown error'}")
    _log(f"[WARN] {_iw_manual_install_hint()}")
    return False

# -----------------------------------------------------------------------------
# Privileged runtime repair / systemd helpers
# -----------------------------------------------------------------------------
def _systemd_supported() -> tuple[bool, str]:
    if not _is_linux_host():
        return False, "当前主机不是 Linux。"
    if not _command_path("systemctl"):
        return False, "未检测到 systemctl。"
    return True, ""

def _systemd_quote_arg(value: str) -> str:
    s = str(value or "")
    if not s:
        return '""'
    if re.search(r"\s|[\"\\]", s):
        return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'
    return s

def _systemd_service_spec() -> dict:
    # Always point the generated unit at the current script/config pair and
    # force no-TUI mode for unattended service execution.
    script = os.path.abspath(str(sys.argv[0] or os.path.join(APP_START_CWD, "run.py")))
    workdir = os.path.abspath(APP_START_CWD or os.path.dirname(script) or ".")
    config_path = os.path.abspath(APP_CONFIG_PATH or os.path.join(workdir, CONFIG_FILE_DEFAULT))
    py = os.path.abspath(sys.executable or "python3")
    exec_start = " ".join([
        _systemd_quote_arg(py),
        _systemd_quote_arg(script),
        "--config",
        _systemd_quote_arg(config_path),
        "--no-tui",
    ])
    service_lines = [
        "[Unit]",
        "Description=Light RID Scanner",
        "Wants=network-online.target",
        "After=network-online.target",
        "",
        "[Service]",
        "Type=simple",
        "Environment=PYTHONUNBUFFERED=1",
        f"WorkingDirectory={_systemd_quote_arg(workdir)}",
        f"ExecStart={exec_start}",
        f"User={RUNTIME_SERVICE_USER}",
    ]
    if _local_group_exists(RUNTIME_SERVICE_USER):
        service_lines.append(f"Group={RUNTIME_SERVICE_USER}")
    if _local_group_exists("netdev"):
        service_lines.append("SupplementaryGroups=netdev")
    caps = " ".join(RUNTIME_SERVICE_CAPABILITIES)
    service_lines.extend([
        f"AmbientCapabilities={caps}",
        f"CapabilityBoundingSet={caps}",
        "Restart=on-failure",
        "RestartSec=3",
        "",
        "[Install]",
        "WantedBy=multi-user.target",
        "",
    ])
    unit = "\n".join(service_lines)
    return {
        "service_name": SYSTEMD_SERVICE_NAME,
        "service_path": SYSTEMD_SERVICE_PATH,
        "python": py,
        "script": script,
        "cwd": workdir,
        "config_path": config_path,
        "exec_start": exec_start,
        "service_user": RUNTIME_SERVICE_USER,
        "service_home": RUNTIME_SERVICE_HOME,
        "service_capabilities": list(RUNTIME_SERVICE_CAPABILITIES),
        "unit_text": unit,
    }

def _read_systemd_unit_text() -> tuple[str, str]:
    try:
        if os.path.exists(SYSTEMD_SERVICE_PATH):
            with open(SYSTEMD_SERVICE_PATH, "r", encoding="utf-8", errors="ignore") as f:
                return f.read(), ""
    except Exception as e:
        return "", str(e)
    return "", ""

def _unit_declared_user(unit_text: str) -> str:
    try:
        for line in str(unit_text or "").splitlines():
            s = line.strip()
            if s.startswith("User="):
                return s.split("=", 1)[1].strip()
    except Exception:
        pass
    return ""

def _runtime_security_payload(unit_text: str | None = None) -> dict:
    uid = _current_uid()
    current_user = _username_for_uid(uid)
    running_as_root = _is_root_user()
    if unit_text is None:
        unit_text, _err = _read_systemd_unit_text()
    actual_service_user = _unit_declared_user(unit_text or "")
    dedicated_exists = _local_user_exists(RUNTIME_SERVICE_USER)
    sudo_available = _sudo_available()
    caps_ok = bool(_process_has_capabilities(list(RUNTIME_SERVICE_CAPABILITIES)))
    risk = "当前程序以 root 权限运行，网页接口和采集进程拥有过高权限。"
    no_caps = f"当前程序以 {current_user or '非 root'} 权限运行，但未检测到采集所需网络能力。"
    ok_msg = f"当前程序以 {current_user or '非 root'} 权限运行。"
    level = "warn" if running_as_root or (not running_as_root and _is_linux_host() and not caps_ok) else "ok"
    return {
        "ok": True,
        "current_uid": uid,
        "current_user": current_user,
        "running_as_root": bool(running_as_root),
        "has_network_capabilities": bool(caps_ok),
        "risk": "root-runtime" if running_as_root else ("" if caps_ok or not _is_linux_host() else "missing-capabilities"),
        "level": level,
        "message": risk if running_as_root else (ok_msg if caps_ok or not _is_linux_host() else no_caps),
        "dedicated_user": RUNTIME_SERVICE_USER,
        "dedicated_user_exists": bool(dedicated_exists),
        "service_user": actual_service_user,
        "service_uses_dedicated_user": actual_service_user == RUNTIME_SERVICE_USER,
        "sudo_available": bool(sudo_available),
        "can_elevate": bool(_is_linux_host() and (running_as_root or sudo_available)),
        "password_saved": False,
    }

def _runtime_path_targets() -> tuple[list[str], list[str]]:
    dirs: set[str] = set()
    files: set[str] = set()

    def add_file(path: str | None) -> None:
        p = str(path or "").strip()
        if not p:
            return
        p = os.path.abspath(p)
        files.add(p)
        parent = os.path.dirname(p)
        if parent:
            dirs.add(parent)
            dirs.add(os.path.join(parent, "backups"))

    def add_dir(path: str | None) -> None:
        p = str(path or "").strip()
        if p:
            dirs.add(os.path.abspath(p))

    add_dir(APP_START_CWD)
    add_file(APP_CONFIG_PATH)
    if APP_CONFIG_PATH:
        add_file(str(APP_CONFIG_PATH) + CONFIG_ROLLBACK_SUFFIX)
    add_file(HISTORY_STORE_PATH)
    add_file(_model_map_target_path())
    add_file(_eula_set_path())
    try:
        add_file(str(AP_CFG.get("vendor_db_file") or ""))
    except Exception:
        pass
    add_dir(os.path.dirname(os.path.abspath(HOST_METRICS_PATH)))
    return sorted(dirs), sorted(files)

def _runtime_traverse_dirs(dirs: list[str]) -> list[str]:
    out: set[str] = set()
    for raw in dirs:
        try:
            path = os.path.abspath(str(raw or ""))
        except Exception:
            continue
        parent = os.path.dirname(path)
        while parent and parent != path:
            if parent == os.path.abspath(os.sep):
                break
            out.add(parent)
            path = parent
            parent = os.path.dirname(path)
    return sorted(out, key=lambda p: len(p))

def _run_repair_step(label: str, args: list[str], steps: list[dict], sudo_password: str | None = None, timeout: int = 30, optional: bool = False) -> bool:
    ok, out, rc = _run_privileged(args, timeout=timeout, sudo_password=sudo_password)
    steps.append({"label": label, "ok": bool(ok), "returncode": rc, "output": out})
    return bool(ok or optional)

def _run_as_runtime_user(args: list[str], sudo_password: str | None, timeout: int = 20) -> tuple[bool, str, int]:
    cmd = [str(x) for x in args]
    if not cmd:
        return False, "empty command", -1
    if _command_path("runuser"):
        return _run_privileged(["runuser", "-u", RUNTIME_SERVICE_USER, "--"] + cmd, timeout=timeout, sudo_password=sudo_password)
    sudo = _command_path("sudo")
    if sudo:
        return _run_privileged([sudo, "-u", RUNTIME_SERVICE_USER, "--"] + cmd, timeout=timeout, sudo_password=sudo_password)
    return False, "未检测到 runuser/sudo，无法以 rid 账号验收权限。", -1

def _verify_runtime_path_access(sudo_password: str | None, steps: list[dict]) -> bool:
    dirs, files = _runtime_path_targets()
    for d in dirs:
        if not d:
            continue
        ok, out, rc = _run_as_runtime_user(["test", "-d", d, "-a", "-r", d, "-a", "-w", d, "-a", "-x", d], sudo_password=sudo_password)
        steps.append({"label": f"rid 目录权限验收 {d}", "ok": bool(ok), "returncode": rc, "output": out})
        if not ok:
            return False
    for f in files:
        if not f or not os.path.exists(f):
            continue
        ok, out, rc = _run_as_runtime_user(["test", "-r", f, "-a", "-w", f], sudo_password=sudo_password)
        steps.append({"label": f"rid 文件权限验收 {f}", "ok": bool(ok), "returncode": rc, "output": out})
        if not ok:
            return False
    return True

def _grant_runtime_path_access(sudo_password: str | None, steps: list[dict]) -> bool:
    dirs, files = _runtime_path_targets()
    for d in _runtime_traverse_dirs(dirs):
        if not d or not os.path.isdir(d):
            continue
        acl_cmd = ["setfacl", "-m", f"u:{RUNTIME_SERVICE_USER}:x", d]
        if _command_path("setfacl"):
            if not _run_repair_step(f"上级目录进入权限 {d}", acl_cmd, steps, sudo_password=sudo_password, optional=False):
                return False
        else:
            if not _run_repair_step(f"上级目录进入权限 {d}", ["chmod", "o+x", d], steps, sudo_password=sudo_password, optional=False):
                return False
    for d in dirs:
        if not d:
            continue
        if not _run_repair_step(f"创建目录 {d}", ["mkdir", "-p", d], steps, sudo_password=sudo_password):
            return False
        if not _run_repair_step(f"目录授权 {d}", ["chgrp", RUNTIME_SERVICE_USER, d], steps, sudo_password=sudo_password, optional=False):
            return False
        if not _run_repair_step(f"目录写权限 {d}", ["chmod", "g+rwx,g+s", d], steps, sudo_password=sudo_password):
            return False
    for f in files:
        if not f or not os.path.exists(f):
            continue
        if not _run_repair_step(f"文件授权 {f}", ["chgrp", RUNTIME_SERVICE_USER, f], steps, sudo_password=sudo_password):
            return False
        if not _run_repair_step(f"文件写权限 {f}", ["chmod", "g+rw", f], steps, sudo_password=sudo_password):
            return False
    return True

def _write_systemd_unit_privileged(unit_text: str, sudo_password: str | None, steps: list[dict]) -> tuple[bool, str]:
    backup_path = ""
    tmp_path = ""
    try:
        with tempfile.NamedTemporaryFile("w", encoding="utf-8", delete=False, prefix="light-rid-service-", suffix=".service") as f:
            tmp_path = f.name
            f.write(unit_text)
    except Exception as e:
        steps.append({"label": "生成临时服务文件", "ok": False, "returncode": -1, "output": str(e)})
        return False, backup_path
    try:
        if os.path.exists(SYSTEMD_SERVICE_PATH):
            backup_path = SYSTEMD_SERVICE_PATH + "." + time.strftime("%Y%m%d_%H%M%S") + ".bak"
            if not _run_repair_step("备份 systemd 服务文件", ["cp", "-a", SYSTEMD_SERVICE_PATH, backup_path], steps, sudo_password=sudo_password):
                return False, backup_path
        if not _run_repair_step("写入 systemd 服务文件", ["install", "-m", "0644", tmp_path, SYSTEMD_SERVICE_PATH], steps, sudo_password=sudo_password):
            return False, backup_path
        return True, backup_path
    finally:
        try:
            if tmp_path:
                os.remove(tmp_path)
        except Exception:
            pass

def _schedule_systemd_restart(sudo_password: str | None, steps: list[dict], delay_sec: int = 3) -> bool:
    delay = max(1, int(delay_sec or 3))
    systemctl = _command_path("systemctl") or "systemctl"
    systemd_run = _command_path("systemd-run")
    if systemd_run:
        unit_name = f"light-rid-scanner-restart-{os.getpid()}-{int(time.time())}"
        args = [
            systemd_run,
            f"--unit={unit_name}",
            f"--on-active={delay}s",
            "--collect",
            systemctl,
            "restart",
            SYSTEMD_SERVICE_NAME,
        ]
        ok, out, rc = _run_privileged(args, timeout=20, sudo_password=sudo_password)
        steps.append({"label": f"安排 {delay} 秒后自动重启服务", "ok": bool(ok), "returncode": rc, "output": out})
        return bool(ok)

    shell = f"sleep {delay}; exec {shlex.quote(systemctl)} restart {shlex.quote(SYSTEMD_SERVICE_NAME)}"
    try:
        if _is_root_user():
            subprocess.Popen(
                ["sh", "-c", shell],
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                start_new_session=True,
                close_fds=True,
            )
        else:
            sudo = _command_path("sudo")
            if not sudo:
                steps.append({"label": "安排自动重启服务", "ok": False, "returncode": -1, "output": "当前进程不是 root，且未检测到 sudo。"})
                return False
            password = "" if sudo_password is None else str(sudo_password)
            if password:
                proc = subprocess.Popen(
                    [sudo, "-S", "-p", "", "--", "sh", "-c", shell],
                    stdin=subprocess.PIPE,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    text=True,
                    start_new_session=True,
                    close_fds=True,
                )
                try:
                    if proc.stdin:
                        proc.stdin.write(password + "\n")
                        proc.stdin.close()
                finally:
                    password = ""
            else:
                subprocess.Popen(
                    [sudo, "-n", "--", "sh", "-c", shell],
                    stdin=subprocess.DEVNULL,
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    start_new_session=True,
                    close_fds=True,
                )
        steps.append({"label": f"安排 {delay} 秒后自动重启服务", "ok": True, "returncode": 0, "output": "已安排后台重启。"})
        return True
    except Exception as e:
        steps.append({"label": "安排自动重启服务", "ok": False, "returncode": -1, "output": str(e)})
        return False

def repair_runtime_security(sudo_password: str | None = None) -> dict:
    supported, reason = _systemd_supported()
    steps: list[dict] = []
    if not supported:
        return {"ok": False, "error": reason, "status": _systemd_service_status_payload(), "steps": steps}
    if not (_is_root_user() or _sudo_available()):
        return {"ok": False, "error": "创建专用运行账号需要 root 或 sudo 提权。", "status": _systemd_service_status_payload(), "steps": steps}
    if not _local_user_exists(RUNTIME_SERVICE_USER):
        shell_path = "/usr/sbin/nologin" if os.path.exists("/usr/sbin/nologin") else "/bin/false"
        useradd_cmd = [
            _command_path("useradd") or "useradd",
            "--system",
            "--create-home",
            "--home-dir",
            RUNTIME_SERVICE_HOME,
            "--shell",
            shell_path,
            "--user-group",
            RUNTIME_SERVICE_USER,
        ]
        if not _run_repair_step(f"创建 {RUNTIME_SERVICE_USER} 账号", useradd_cmd, steps, sudo_password=sudo_password, timeout=30):
            return {"ok": False, "error": f"创建 {RUNTIME_SERVICE_USER} 账号失败。", "status": _systemd_service_status_payload(), "steps": steps}
    else:
        steps.append({"label": f"{RUNTIME_SERVICE_USER} 账号已存在", "ok": True, "returncode": 0, "output": ""})
    if not _run_repair_step("准备专用运行目录", ["install", "-d", "-o", RUNTIME_SERVICE_USER, "-g", RUNTIME_SERVICE_USER, "-m", "0750", RUNTIME_SERVICE_HOME], steps, sudo_password=sudo_password):
        return {"ok": False, "error": "准备专用运行目录失败。", "status": _systemd_service_status_payload(), "steps": steps}
    if _local_group_exists("netdev"):
        _run_repair_step("加入 netdev 组", ["usermod", "-a", "-G", "netdev", RUNTIME_SERVICE_USER], steps, sudo_password=sudo_password, optional=True)
    if not _grant_runtime_path_access(sudo_password, steps):
        return {"ok": False, "error": "授予运行文件写权限失败。", "status": _systemd_service_status_payload(), "steps": steps}
    if not _verify_runtime_path_access(sudo_password, steps):
        return {"ok": False, "error": "rid 账号权限验收失败。请检查上方失败步骤后重试。", "status": _systemd_service_status_payload(), "steps": steps}
    rsp = register_systemd_service(sudo_password=sudo_password, require_dedicated_user=True, _steps=steps)
    payload = dict(rsp)
    payload["steps"] = steps
    if rsp.get("ok"):
        restart_delay = 3
        restart_scheduled = _schedule_systemd_restart(sudo_password, steps, delay_sec=restart_delay)
        payload["steps"] = steps
        payload["restart_scheduled"] = bool(restart_scheduled)
        payload["restart_delay_sec"] = restart_delay
        if restart_scheduled:
            payload["message"] = "已创建/确认 rid 专用账号，并更新 systemd 服务为 rid 账号运行。服务将在几秒后自动重启，页面可能短暂断开。"
        else:
            payload["message"] = "已创建/确认 rid 专用账号，并更新 systemd 服务为 rid 账号运行；但自动重启安排失败，请手动重启 light-rid-scanner.service。"
    return payload

def _systemd_service_status_payload() -> dict:
    supported, reason = _systemd_supported()
    spec = _systemd_service_spec()
    registered = os.path.exists(SYSTEMD_SERVICE_PATH)
    enabled = "unknown"
    active = "unknown"
    unit_matches = False
    last_error = ""
    unit_text = ""
    if registered:
        unit_text, last_error = _read_systemd_unit_text()
        unit_matches = (unit_text.strip() == str(spec.get("unit_text") or "").strip())
    if supported and registered:
        ok_enabled, out_enabled, _rc_enabled = _systemctl(["is-enabled", SYSTEMD_SERVICE_NAME], timeout=8)
        enabled = (out_enabled.splitlines() or ["enabled" if ok_enabled else "disabled"])[0].strip() or ("enabled" if ok_enabled else "disabled")
        ok_active, out_active, _rc_active = _systemctl(["is-active", SYSTEMD_SERVICE_NAME], timeout=8)
        active = (out_active.splitlines() or ["active" if ok_active else "inactive"])[0].strip() or ("active" if ok_active else "inactive")
    security = _runtime_security_payload(unit_text=unit_text)
    return {
        "ok": True,
        "supported": bool(supported),
        "reason": reason,
        "running_as_root": _is_root_user(),
        "current_user": security.get("current_user"),
        "current_uid": security.get("current_uid"),
        "registered": bool(registered),
        "enabled": enabled,
        "active": active,
        "unit_matches": bool(unit_matches),
        "last_error": last_error,
        "dedicated_user": RUNTIME_SERVICE_USER,
        "dedicated_user_exists": bool(security.get("dedicated_user_exists")),
        "actual_service_user": security.get("service_user"),
        "service_uses_dedicated_user": bool(security.get("service_uses_dedicated_user")),
        "sudo_available": bool(security.get("sudo_available")),
        "can_elevate": bool(security.get("can_elevate")),
        "security": security,
        "manual_hint": "需要 root 或临时 sudo 提权写入 /etc/systemd/system 并执行 systemctl daemon-reload、systemctl enable。",
        "iw": _iw_status_payload(refresh=True),
        **spec,
    }

def register_systemd_service(sudo_password: str | None = None, require_dedicated_user: bool = True, _steps: list[dict] | None = None) -> dict:
    supported, reason = _systemd_supported()
    steps = _steps if isinstance(_steps, list) else []
    if not supported:
        return {"ok": False, "error": reason, "status": _systemd_service_status_payload(), "steps": steps}
    if require_dedicated_user and not _local_user_exists(RUNTIME_SERVICE_USER):
        return {
            "ok": False,
            "error": f"专用运行账号 {RUNTIME_SERVICE_USER} 不存在，请先执行一键修复。",
            "status": _systemd_service_status_payload(),
            "steps": steps,
        }
    if not (_is_root_user() or _sudo_available()):
        return {"ok": False, "error": "注册 systemd 服务需要 root 或临时 sudo 提权。", "status": _systemd_service_status_payload(), "steps": steps}
    spec = _systemd_service_spec()
    unit_text = str(spec.get("unit_text") or "")
    ok_write, backup_path = _write_systemd_unit_privileged(unit_text, sudo_password, steps)
    if not ok_write:
        return {"ok": False, "error": "写入服务文件失败。", "status": _systemd_service_status_payload(), "steps": steps}

    ok_reload, out_reload, rc_reload = _systemctl_privileged(["daemon-reload"], timeout=20, sudo_password=sudo_password)
    steps.append({"label": "systemctl daemon-reload", "ok": bool(ok_reload), "returncode": rc_reload, "output": out_reload})
    if not ok_reload:
        return {
            "ok": False,
            "error": "systemctl daemon-reload 失败",
            "returncode": rc_reload,
            "output": out_reload,
            "backup_path": backup_path,
            "status": _systemd_service_status_payload(),
            "steps": steps,
        }
    ok_enable, out_enable, rc_enable = _systemctl_privileged(["enable", SYSTEMD_SERVICE_NAME], timeout=20, sudo_password=sudo_password)
    steps.append({"label": "systemctl enable", "ok": bool(ok_enable), "returncode": rc_enable, "output": out_enable})
    status = _systemd_service_status_payload()
    if not ok_enable:
        return {
            "ok": False,
            "error": "systemctl enable 失败",
            "returncode": rc_enable,
            "output": out_enable,
            "backup_path": backup_path,
            "status": status,
            "steps": steps,
        }
    return {
        "ok": True,
        "message": f"systemd 服务已注册并设为开机自启；服务文件将以 {RUNTIME_SERVICE_USER} 账号运行，当前进程不会被自动重启。",
        "backup_path": backup_path,
        "output": out_enable,
        "status": status,
        "steps": steps,
    }

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
    steps = (
        (f"ip link set {iface} down", 0.15),
        (f"iw dev {iface} set type managed", 0.35),
        (f"ip link set {iface} up", 0.25),
        (f"ip link set {iface} down", 0.15),
        (f"iw dev {iface} set type monitor", 0.35),
        (f"ip link set {iface} up", 0.25),
        (f"iw dev {iface} set power_save off", 0.0),
    )
    for c, pause_sec in steps:
        run_cmd(c, timeout=6)
        if pause_sec > 0:
            time.sleep(pause_sec)
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

def _sniff_close_socket(sock) -> None:
    if not sock:
        return
    try:
        sock.close()
    except Exception:
        pass

def _sniff_open_socket(iface: str):
    try:
        return conf.L2listen(iface=iface, monitor=True)
    except TypeError:
        return conf.L2listen(iface=iface)

def _sniff_run_once(iface: str, timeout_sec: float = SNIFF_POLL_TIMEOUT) -> tuple[str, str]:
    iface = str(iface or "").strip()
    if not iface:
        return "error", "iface empty"
    timeout_sec = max(1.0, float(timeout_sec or SNIFF_POLL_TIMEOUT))
    hard_deadline = time.monotonic() + timeout_sec + SNIFF_WORKER_HARD_GRACE_SEC
    result = {"error": "", "done": False}
    sock_ref = {"sock": None}

    def _worker() -> None:
        sock = None
        try:
            sock = _sniff_open_socket(iface)
            sock_ref["sock"] = sock
            sniff(opened_socket=sock, prn=parse_frame, store=False, timeout=timeout_sec)
        except Exception as ex:
            result["error"] = str(ex or "")
        finally:
            result["done"] = True
            if sock_ref.get("sock") is sock:
                sock_ref["sock"] = None
            _sniff_close_socket(sock)

    th = Thread(target=_worker, daemon=True)
    th.start()
    while th.is_alive():
        if time.monotonic() >= hard_deadline:
            _sniff_close_socket(sock_ref.get("sock"))
            th.join(SNIFF_WORKER_JOIN_GRACE_SEC)
            if th.is_alive():
                return "hung", f"worker exceeded {timeout_sec + SNIFF_WORKER_HARD_GRACE_SEC:.0f}s"
            return "hung", f"worker forced close after {timeout_sec + SNIFF_WORKER_HARD_GRACE_SEC:.0f}s"
        time.sleep(0.25)
    if result["error"]:
        return "error", result["error"]
    return "ok", ""

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

def _cfg_preferred_iface() -> str | None:
    return _cfg_preferred_iface_from_cfg(APP_CONFIG)

def _cfg_auto_self_heal() -> bool:
    try:
        basic = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
        if not isinstance(basic, dict):
            return True
        return bool(basic.get("auto_self_heal", True))
    except Exception:
        return True

def _sniff_pick_iface(prefer: str | None = None) -> str | None:
    iftypes = _sniff_iface_candidates()
    if not iftypes:
        return None
    if prefer and prefer in iftypes:
        return prefer
    if prefer:
        _sniff_note_error(f"配置的默认网卡未检测到: {prefer}")
        return None
    _sniff_note_error("未绑定默认网卡，请打开 OOBE 或设置页选择网卡")
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

def interface_detect(prefer: str | None = None) -> str | None:
    iw      = run_cmd("iw dev")
    if not iw and not _command_path(IW_PACKAGE_NAME):
        snap = _iw_status_payload(refresh=True)
        msg = f"{snap.get('message') or _iw_missing_message()} {snap.get('manual_hint') or _iw_manual_install_hint()}"
        _log(f"[WARN] {msg}")
        _sniff_note_error(msg)
        _set_oobe_required(msg, True)
        return None
    iftypes: dict[str, str] = {}
    cur     = None
    for line in iw.splitlines():
        m = re.match(r"\s*Interface\s+(\S+)", line)
        if m: cur = m.group(1)
        m2 = re.match(r"\s*type\s+(\S+)", line)
        if m2 and cur: iftypes[cur] = m2.group(1)

    if not prefer:
        msg = "未绑定默认网卡，请进入 OOBE 或设置页选择固定网卡"
        _log(f"[WARN] {msg}")
        _sniff_note_error(msg)
        _set_oobe_required(msg, True)
        return None
    if prefer and prefer in iftypes:
        iface = prefer
    else:
        iface = None
    if not iface:
        msg = f"默认网卡未检测到: {prefer}" if iftypes else NO_IFACE_DEGRADE_HINT
        _log(f"[WARN] {msg}")
        _sniff_note_error(msg + "。请打开 OOBE 或设置页检查默认网卡。")
        _set_oobe_required(msg, True)
        return None

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

def _snap(e: dict) -> dict:
    s = {k: e.get(k) for k in
         ("sn","src_mac","id_type","uas_id","model","lat","lon","alt","speed","vspeed","last_ch","move_dir")}
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
            "uas_id": _uas_id_clean(e.get("uas_id")),
            "firmware_type": _firmware_type_key(e.get("firmware_type")),
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
    h["rssi"] = e.get("rssi")
    h["move_dir"] = e.get("move_dir")
    h["ssid"] = e.get("ssid")
    h["capture_type"] = e.get("capture_type")
    h["uas_id"] = _uas_id_clean(e.get("uas_id"))
    h["firmware_type"] = _firmware_type_key(e.get("firmware_type"))
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
    h.setdefault("uas_id", _uas_id_clean(e.get("uas_id")))
    h.setdefault("firmware_type", _firmware_type_key(e.get("firmware_type")))
    h.setdefault("track", _sanitize_track(e.get("track") or []))
    h.setdefault("track_updated_wall_ts", e.get("track_updated_wall_ts"))
    _history_mark_dirty()

def state_update(src_mac: str, decoded: dict, rssi: int | None,
                 ch: int, ch_assumed: bool, pl_sig: int,
                 *, scan_type: str = "rid", ssid: str | None = None,
                 capture_type: str | None = None, raw_pkt_hex: str | None = None,
                 firmware_type: str | None = "old") -> None:
    basic = decoded.get("basic_id")
    loc   = decoded.get("location")
    sys_loc = decoded.get("system")
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
            track_data = _sanitize_track(cur.get("track", hist.get("track", [])) or [])
            drones.append({
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
            "settings_path": "/settings",
        },
    }

def _api_iso_now(ts: float | None = None) -> str:
    try:
        return time.strftime("%Y-%m-%dT%H:%M:%S%z", time.localtime(ts if ts is not None else time.time()))
    except Exception:
        return ""

def _load_build_info() -> dict:
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), BUILD_INFO_FILE)
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}

def _local_git_commit() -> str:
    repo = os.path.dirname(os.path.abspath(__file__))
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

def _fallback_private_commit() -> str:
    try:
        path = os.path.abspath(__file__)
        st = os.stat(path)
        raw = f"{path}|{st.st_size}|{int(st.st_mtime)}".encode("utf-8", errors="replace")
        return hashlib.sha1(raw).hexdigest()[:7]
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
            build = int(os.stat(os.path.abspath(__file__)).st_mtime)
        except Exception:
            build = int(time.time())
    return f"commit:{commit}#{build}"

def _short_commit(commit: str) -> str:
    text = str(commit or "").strip()
    return text[:12] if text else ""

def _app_update_status_payload() -> dict:
    current = _local_app_commit() or _fallback_private_commit()
    with app_update_lock:
        cfg = dict(APP_UPDATE_CFG)
        state = dict(APP_UPDATE_STATE)
    state["current_commit"] = current
    state["current_short"] = _short_commit(current)
    state["latest_short"] = _short_commit(state.get("latest_commit") or "")
    state["commit_url"] = str(cfg.get("commit_url") or APP_UPDATE_COMMIT_URL_DEFAULT)
    state["checked"] = bool(state.get("last_check_ts"))
    return state

def _check_app_update_once(manual: bool = False) -> dict:
    if not manual and not bool(APP_UPDATE_CFG.get("enabled", True)):
        return {"ok": True, "skipped": True, "state": _app_update_status_payload()}
    with app_update_lock:
        if bool(APP_UPDATE_STATE.get("running")):
            busy = True
        else:
            busy = False
            APP_UPDATE_STATE["running"] = True
            APP_UPDATE_STATE["last_error"] = ""
            commit_url = str(APP_UPDATE_CFG.get("commit_url") or APP_UPDATE_COMMIT_URL_DEFAULT)
    if busy:
        return {"ok": False, "error": "程序更新检查正在运行", "state": _app_update_status_payload()}
    try:
        local_commit = _local_app_commit()
        if not local_commit:
            local_commit = _fallback_private_commit()
        req = urllib.request.Request(
            commit_url,
            headers={"User-Agent": APP_HTTP_USER_AGENT + " (+version check)"},
        )
        with urllib.request.urlopen(req, timeout=6) as resp:
            data = json.loads(resp.read(256 * 1024).decode("utf-8", errors="replace"))
        remote_commit = str((data if isinstance(data, dict) else {}).get("sha") or "").strip()
        update_available = bool(remote_commit and local_commit and not remote_commit.startswith(local_commit) and not local_commit.startswith(remote_commit[:7]))
        with app_update_lock:
            APP_UPDATE_STATE.update({
                "running": False,
                "last_check_ts": time.time(),
                "latest_commit": remote_commit,
                "current_commit": local_commit,
                "update_available": update_available,
                "last_error": "",
            })
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
                "current_commit": _local_app_commit() or _fallback_private_commit(),
                "last_error": str(e),
            })
        _log(f"[WARN] 程序更新检查失败: {e}")
        return {"ok": False, "error": str(e), "state": _app_update_status_payload()}

def start_app_update_check() -> None:
    Thread(target=_check_app_update_once, daemon=True).start()

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
        {"method": "GET", "path": "/api/v1/logs?type=event|scan|ap&limit=200", "desc": "Logs"},
        {"method": "GET", "path": "/api/logs/view?type=runtime|operation|scan|scan_diff|ap", "desc": "Built-in page log viewer"},
        {"method": "GET", "path": "/api/logs/export?type=all|runtime|operation|scan|scan_diff|ap", "desc": "Built-in page log export"},
        {"method": "POST", "path": "/api/v1/history/clear", "desc": "Clear history cache"},
        {"method": "POST", "path": "/api/v1/history/delete", "desc": "Delete one history item"},
        {"method": "POST", "path": "/api/v1/tracks/clear", "desc": "Clear tracks"},
        {"method": "POST", "path": "/api/v1/config/reload", "desc": "Reload config file"},
    ]

def _api_token_enabled() -> bool:
    return bool(API_CFG.get("enabled")) and bool(_auth_enabled()) and _auth_hashes_present(AUTH_CFG) and _api_tokens_have_secret(API_CFG)

def _api_token_check_value(token: str | None) -> dict | None:
    if not _api_token_enabled():
        return None
    raw = str(token or "").strip()
    if not raw:
        return None
    incoming_hash = _sha256_hex(raw)
    for item in _normalize_api_tokens(API_CFG.get("tokens"), API_CFG.get("token") or "", API_CFG.get("token_sha256") or ""):
        token_hash = str(item.get("token_sha256") or "").strip().lower()
        if token_hash and hmac.compare_digest(incoming_hash, token_hash) and bool(_sso_link_state(item).get("active")):
            return dict(item)
    return None

def _api_token_from_request(headers, query: dict | None = None) -> str:
    authz = str(headers.get("Authorization") or "").strip()
    if authz.lower().startswith("bearer "):
        return authz[7:].strip()
    token = str(headers.get("X-API-Token") or "").strip()
    if token:
        return token
    if isinstance(query, dict):
        try:
            arr = query.get("token") or [""]
            return str(arr[0] or "").strip()
        except Exception:
            return ""
    return ""

def _api_mark_token_used(token_id: str | None) -> bool:
    raw_id = str(token_id or "").strip()
    if not raw_id:
        return False
    changed = False
    now_wall = time.time()
    def _mark(tokens):
        nonlocal changed
        out = []
        for item in tokens:
            row = dict(item or {})
            if str(row.get("id") or "") == raw_id:
                row["used_count"] = int(row.get("used_count") or 0) + 1
                row["used_ts"] = now_wall
                changed = True
            out.append(row)
        return out
    ok, _msg, _tokens = _api_mutate_tokens(_mark, tag="api_token_use")
    return bool(ok and changed)

def _api_mutate_tokens(mutator, *, tag: str = "api_token") -> tuple[bool, str, list[dict]]:
    if not APP_CONFIG_PATH:
        return False, "config path missing", _api_tokens_public()
    try:
        with api_token_lock:
            cfg = load_app_config(APP_CONFIG_PATH)
            api = cfg.setdefault("api", {})
            if not isinstance(api, dict):
                api = {}
                cfg["api"] = api
            tokens = _normalize_api_tokens(api.get("tokens"), api.get("token") or "", api.get("token_sha256") or "")
            api["tokens"] = _normalize_api_tokens(mutator(list(tokens)))
            first = api["tokens"][0] if api["tokens"] else {}
            api["token"] = str(first.get("token") or "")
            api["token_sha256"] = str(first.get("token_sha256") or "")
            cfg, guard_err = _prepare_security_cfg_for_save(cfg)
            if guard_err:
                return False, guard_err, _api_tokens_public()
            b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag=tag)
            if not b_ok:
                return False, f"backup failed: {backup_path}", _api_tokens_public()
            ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
            if not ok:
                return False, msg, _api_tokens_public()
            cfg_loaded = load_app_config(APP_CONFIG_PATH)
            r_ok, r_msg = reload_runtime_config(cfg_loaded)
            if not r_ok:
                return False, f"reload failed: {r_msg}", _api_tokens_public()
            api_loaded = cfg_loaded.get("api") if isinstance(cfg_loaded, dict) else None
            return True, "ok", _api_tokens_public(api_loaded if isinstance(api_loaded, dict) else None)
    except Exception as e:
        return False, str(e), _api_tokens_public()

def _build_api_token_create_payload(body: dict | None, *, headers=None, client_ip: str | None = None) -> tuple[dict, int]:
    if not _auth_enabled() or (not _auth_hashes_present(AUTH_CFG)):
        return {"ok": False, "error": "网页登录鉴权未启用或未完成配置，不能生成 API Token"}, 400
    src = body if isinstance(body, dict) else {}
    subject = str(src.get("username") or "-")
    reauth_ok = _auth_check_userpass(str(src.get("username") or ""), str(src.get("password") or ""))
    if not reauth_ok and headers is not None and headers.get("Authorization"):
        reauth_ok = _auth_check_basic_header(headers.get("Authorization"))
    if not reauth_ok:
        _op_log("api-token-create", "", actor=subject, ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": "账号或密码错误"}, 401
    now_wall = time.time()
    expires_at, expiry_err = _api_token_expiry_from_row(src, now_wall=now_wall, fallback=0.0)
    if expiry_err:
        return {"ok": False, "error": expiry_err}, 400
    name = str(src.get("name") or "").strip()
    if not name:
        name = "API Token " + time.strftime("%Y-%m-%d %H:%M:%S")
    token_plain = secrets.token_urlsafe(32)
    token_hash = _sha256_hex(token_plain)
    token_id = _api_token_id_from_hash(token_hash)
    item = {
        "id": token_id,
        "name": name[:80],
        "token": "",
        "token_sha256": token_hash,
        "enabled": True,
        "created_ts": now_wall,
        "expires_at": expires_at,
        "single_use": _to_bool(src.get("single_use"), False),
        "used_ts": 0.0,
        "used_count": 0,
    }
    def _add_token(tokens):
        tokens.append(item)
        return tokens[-64:]
    ok, msg, tokens = _api_mutate_tokens(_add_token, tag="api_token_create")
    if not ok:
        return {"ok": False, "error": msg, "tokens": tokens}, 500
    _op_log("api-token-create", "name=" + name[:40], actor=subject, ip=str(client_ip or "-"), ok=True)
    return {
        "ok": True,
        "id": token_id,
        "name": name,
        "token": token_plain,
        "expires_at": expires_at,
        "expires_in_sec": None if expires_at <= 0 else int(max(0.0, expires_at - now_wall)),
        "single_use": bool(item.get("single_use")),
        "tokens": tokens,
    }, 200

def _api_token_docs_payload() -> dict:
    return {
        "ok": True,
        "api": _api_meta(),
        "auth": {
            "type": "token",
            "usage": [
                "Header: X-API-Token: <token>",
                "or Authorization: Bearer <token>",
                "Query fallback: ?token=<token> (not recommended for browser history/privacy)",
            ],
            "disabled_behavior": "When public API is disabled, /api/docs, /api/health and /api/v1/* only work from the built-in web pages via page session requests.",
            "token_policy": "API tokens support multiple entries, per-token expiry, single-use mode, and retained expired records.",
            "create_sso_link": {
                "method": "POST",
                "path": "/api/v1/auth/sso-links/create",
                "body": {
                    "name": "optional display name",
                    "next": "/",
                    "ttl_sec": 86400,
                    "expires": "never",
                    "single_use": False,
                },
                "expiry_fields": "Use one of ttl_sec, ttl_min, expires_at, or expires=never.",
            },
        },
        "endpoints": _api_endpoint_index(),
    }

def _api_v1_home_payload() -> dict:
    meta = _api_meta()
    return {
        "ok": True,
        "api": meta,
        "auth": {
            "token_api": {
                "enabled": bool(_api_token_enabled()),
                "headers": ["X-API-Token", "Authorization: Bearer <token>"],
                "query_fallback": "token",
                "supports_multiple_tokens": True,
                "supports_single_use": True,
                "supports_never_expires": True,
                "expired_tokens_auto_delete": False,
                "token_count": len(_api_tokens_public(API_CFG)),
                "whitelist_enabled": bool(API_CFG.get("whitelist_enabled")),
                "whitelist_count": len(API_CFG.get("whitelist") or []),
            },
            "web_login": meta.get("web_auth") or {},
            "sso_links": {
                "create_endpoint": "/api/v1/auth/sso-links/create",
                "supports_single_use": True,
                "supports_never_expires": True,
                "expired_links_auto_delete": False,
            },
        },
        "endpoints": _api_endpoint_index(),
    }

def _settings_runtime_payload(limit: int = 180) -> dict:
    try:
        n = max(20, min(1000, int(limit)))
    except Exception:
        n = 180
    aps, aps_seq, aps_total = _ap_snapshot()
    with log_lock:
        event_logs = list(log_buf)[-n:]
        scan_logs = list(scan_buf)[-n:]
        ap_logs = list(ap_buf)[-n:]
    return {
        "ok": True,
        "aps": aps,
        "aps_seq": aps_seq,
        "aps_total": aps_total,
        "metrics": _host_metrics_payload(24 * 3600),
        "event_logs": event_logs,
        "scan_logs": scan_logs,
        "ap_logs": ap_logs,
    }

def _logs_snapshot(log_type: str = "runtime", limit: int = 500) -> dict:
    try:
        n = max(1, min(5000, int(limit)))
    except Exception:
        n = 500
    kind = str(log_type or "runtime").strip().lower()
    with log_lock:
        runtime_rows = list(log_buf)[-n:]
        operation_rows = list(op_buf)[-n:]
        scan_rows = list(scan_buf)[-n:]
        ap_rows = list(ap_buf)[-n:]
    if kind in ("op", "ops", "operation", "audit"):
        kind = "operation"
        rows = operation_rows
    elif kind in ("scan", "scanner"):
        kind = "scan"
        rows = scan_rows
    elif kind in ("ap", "ap_scan"):
        kind = "ap"
        rows = ap_rows
    elif kind in ("diff", "scan_diff"):
        kind = "scan_diff"
        rows = list(difflib.unified_diff(
            runtime_rows,
            scan_rows,
            fromfile="runtime.log",
            tofile="scan.log",
            lineterm="",
        ))[-n:]
    else:
        kind = "runtime"
        rows = runtime_rows
    return {
        "ok": True,
        "type": kind,
        "limit": n,
        "count": len(rows),
        "items": rows,
        "available": ["runtime", "operation", "scan", "scan_diff", "ap"],
    }

def _logs_export_bytes(log_type: str = "all", limit: int = 5000) -> tuple[bytes, str, str]:
    stamp = time.strftime("%Y%m%d_%H%M%S")
    kind = str(log_type or "all").strip().lower()
    if kind == "all":
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
            for name in ("runtime", "operation", "scan", "scan_diff", "ap"):
                snap = _logs_snapshot(name, limit=limit)
                zf.writestr(f"{name}.log", "\n".join(str(x) for x in snap.get("items") or []) + "\n")
        return buf.getvalue(), f"light-rid-logs-{stamp}.zip", "application/zip"
    snap = _logs_snapshot(kind, limit=limit)
    body = ("\n".join(str(x) for x in snap.get("items") or []) + "\n").encode("utf-8")
    return body, f"light-rid-{snap.get('type')}-{stamp}.log", "text/plain; charset=utf-8"

def _oobe_status_payload() -> dict:
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else default_app_config()
    basic = cfg.get("basic") if isinstance(cfg, dict) else {}
    web = cfg.get("web") if isinstance(cfg, dict) else {}
    auth = cfg.get("auth") if isinstance(cfg, dict) else {}
    if not isinstance(basic, dict): basic = {}
    if not isinstance(web, dict): web = {}
    if not isinstance(auth, dict): auth = {}
    return {
        "ok": True,
        "oobe": _oobe_state(),
        "config_path": APP_CONFIG_PATH or "",
        "interfaces": _iface_options_snapshot(),
        "selected_iface": _cfg_preferred_iface_from_cfg(cfg),
        "channel": basic.get("channel"),
        "base_name": str(web.get("base_name") or "基站"),
        "base_lat": web.get("base_lat"),
        "base_lon": web.get("base_lon"),
        "auth_enabled": bool(auth.get("enabled")),
        "auth_configured": _auth_hashes_present(auth),
        "host": _host_resource_snapshot(),
    }

def _oobe_save_config(body: dict | None) -> dict:
    if not APP_CONFIG_PATH:
        return {"ok": False, "error": "config path missing"}
    payload = body if isinstance(body, dict) else {}
    iface = str(payload.get("iface") or "").strip()
    if not iface:
        return {"ok": False, "error": "必须选择默认网卡"}
    safe_iface = _hw_safe_iface(iface)
    if not safe_iface:
        return {"ok": False, "error": f"网卡不可用: {iface}"}
    iface = safe_iface
    try:
        channel = int(payload.get("channel") or 6)
    except Exception:
        channel = 6
    if channel < 1 or channel > 196:
        return {"ok": False, "error": "信道超出范围"}
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else default_app_config()
    basic = cfg.setdefault("basic", {})
    web = cfg.setdefault("web", {})
    auth = cfg.setdefault("auth", {})
    if not isinstance(basic, dict): basic = {}; cfg["basic"] = basic
    if not isinstance(web, dict): web = {}; cfg["web"] = web
    if not isinstance(auth, dict): auth = {}; cfg["auth"] = auth
    basic["iface"] = iface
    basic["channel"] = channel
    basic["no_tui"] = True
    basic["auto_self_heal"] = True
    web["base_name"] = str(payload.get("base_name") or web.get("base_name") or "基站").strip() or "基站"
    for k, lo, hi in (("base_lat", -90.0, 90.0), ("base_lon", -180.0, 180.0)):
        raw_v = payload.get(k)
        if raw_v in (None, ""):
            continue
        try:
            val = float(raw_v)
        except Exception:
            return {"ok": False, "error": f"{k} 格式错误"}
        if not (lo <= val <= hi):
            return {"ok": False, "error": f"{k} 超出范围"}
        web[k] = val
    username = str(payload.get("username") or "").strip()
    password = str(payload.get("password") or "")
    if username or password:
        if not username or not password:
            return {"ok": False, "error": "账号和密码必须同时填写"}
        auth["enabled"] = True
        auth["username_sha256"] = _sha256_hex(username)
        auth["password_sha256"] = _sha256_hex(password)
        auth["realm"] = str(auth.get("realm") or "Light RID Scanner")
    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="oobe")
    if not b_ok:
        return {"ok": False, "error": f"backup failed: {backup_path}"}
    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
    if not ok:
        return {"ok": False, "error": f"save failed: {msg}"}
    cfg_loaded = load_app_config(APP_CONFIG_PATH)
    r_ok, r_msg = reload_runtime_config(cfg_loaded)
    if not r_ok:
        restore_config_backup(APP_CONFIG_PATH, backup_path)
        return {"ok": False, "error": f"reload failed: {r_msg}", "backup_path": backup_path}
    _set_oobe_required("", False)
    _op_log("oobe-save", f"iface={iface} channel={channel} backup={backup_path}", ok=True)
    return {
        "ok": True,
        "saved_to": APP_CONFIG_PATH,
        "backup_path": backup_path,
        "iface": iface,
        "channel": channel,
        "reload_msg": r_msg,
        "login_required": bool(_normalize_auth_cfg(cfg_loaded).get("enabled")),
        "next": ("/login" if bool(_normalize_auth_cfg(cfg_loaded).get("enabled")) else "/"),
    }

def _diagnostic_run(cmd: str, timeout: int = 8) -> str:
    try:
        r = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        out = (r.stdout or "")
        err = (r.stderr or "")
        text = out
        if err:
            text += ("\n--- STDERR ---\n" + err)
        if not text.strip():
            text = f"(empty, rc={getattr(r, 'returncode', '')})\n"
        return text
    except Exception as e:
        return f"command failed: {e}\n"

def _diagnostic_redact(obj):
    sensitive = ("token", "password", "secret", "webhook", "key", "sha256", "authorization", "cookie")
    if isinstance(obj, dict):
        out = {}
        for k, v in obj.items():
            ks = str(k).lower()
            if any(s in ks for s in sensitive):
                out[k] = "***REDACTED***" if v not in (None, "", []) else v
            else:
                out[k] = _diagnostic_redact(v)
        return out
    if isinstance(obj, list):
        return [_diagnostic_redact(x) for x in obj]
    return obj

def _diagnostic_zip_bytes() -> tuple[bytes, str]:
    now_wall = time.time()
    stamp = time.strftime("%Y%m%d_%H%M%S", time.localtime(now_wall))
    buf = io.BytesIO()
    now_mono = time.monotonic()
    meta = {
        "generated_at": _fmt_wall_ts(now_wall),
        "uptime_sec": int(max(0.0, now_wall - APP_START_WALL)),
        "cwd": APP_START_CWD,
        "config_path": APP_CONFIG_PATH or "",
        "history_store": HISTORY_STORE_PATH or "",
        "app_version": _app_version_label(),
        "python": sys.version,
        "platform": platform.platform(),
        "argv": list(sys.argv),
        "current_channel": current_channel,
        "sniff": _sniff_health_meta(now_mono, now_wall),
        "api": _api_meta(),
    }
    with log_lock:
        event_logs = list(log_buf)
        scan_logs = list(scan_buf)
        ap_logs = list(ap_buf)
        operation_logs = list(op_buf)
    with state_lock:
        state_summary = {
            "live_count": len(state_table),
            "history_count": len(history_table),
            "live_keys": sorted([str(k) for k in state_table.keys()])[:500],
            "history_keys": sorted([str(k) for k in history_table.keys()])[:500],
        }
    commands = {
        "system_uname.txt": "uname -a",
        "system_uptime.txt": "uptime",
        "system_free.txt": "free -h",
        "system_df.txt": "df -h",
        "system_ip_addr.txt": "ip addr",
        "system_ip_link.txt": "ip link",
        "wifi_iw_dev.txt": "iw dev",
        "wifi_iw_info.txt": "iw dev 2>/dev/null",
        "wifi_iw_phy.txt": "iw phy",
        "wifi_rfkill.txt": "rfkill list",
        "usb_lsusb.txt": "lsusb",
        "service_status.txt": "systemctl status light-rid-scanner.service --no-pager -l",
        "service_journal.txt": "journalctl -u light-rid-scanner.service -n 500 --no-pager",
        "process_ps.txt": "ps -eo pid,ppid,stat,pcpu,pmem,comm,args --sort=-pcpu | head -80",
    }
    if sniff_iface_name:
        safe_iface = shlex.quote(str(sniff_iface_name))
        commands[f"wifi_{sniff_iface_name}_info.txt"] = f"iw dev {safe_iface} info"
        commands[f"wifi_{sniff_iface_name}_link.txt"] = f"iw dev {safe_iface} link"
    with zipfile.ZipFile(buf, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=6) as zf:
        zf.writestr("README.txt", (
            "Light RID Scanner quality report\n"
            "Sensitive config values are redacted. Logs may still contain observed SN/MAC/location data.\n"
        ))
        zf.writestr("meta.json", json.dumps(meta, ensure_ascii=False, indent=2))
        zf.writestr("state_summary.json", json.dumps(state_summary, ensure_ascii=False, indent=2))
        zf.writestr("snapshot.json", json.dumps(_state_snapshot(), ensure_ascii=False, indent=2))
        zf.writestr("config_redacted.json", json.dumps(_diagnostic_redact(APP_CONFIG), ensure_ascii=False, indent=2))
        zf.writestr("logs/event.log", "\n".join(event_logs) + ("\n" if event_logs else ""))
        zf.writestr("logs/scan.log", "\n".join(scan_logs) + ("\n" if scan_logs else ""))
        zf.writestr("logs/ap.log", "\n".join(ap_logs) + ("\n" if ap_logs else ""))
        zf.writestr("logs/operation.log", "\n".join(operation_logs) + ("\n" if operation_logs else ""))
        for name, cmd in commands.items():
            zf.writestr("commands/" + name, "$ " + cmd + "\n\n" + _diagnostic_run(cmd, timeout=10))
    data = buf.getvalue()
    if len(data) < 128:
        fallback = io.BytesIO()
        with zipfile.ZipFile(fallback, "w", compression=zipfile.ZIP_STORED) as zf:
            zf.writestr("README.txt", "Light RID Scanner quality report fallback\n")
            zf.writestr("meta.json", json.dumps(meta, ensure_ascii=False, indent=2))
        data = fallback.getvalue()
    filename = f"light-rid-quality-{stamp}.zip"
    return data, filename

def _path_uses_api_token(req_path: str | None) -> bool:
    path = str(req_path or "").split("?", 1)[0]
    if path == "/api/docs":
        return True
    if path == "/api/health":
        return True
    if path in ("/api/v1", "/api/v1/"):
        return True
    return path.startswith("/api/v1/")

def _path_is_page_api(req_path: str | None) -> bool:
    path = str(req_path or "").split("?", 1)[0]
    return path.startswith("/api/") and (not _path_uses_api_token(path))

def _path_is_oobe_public(req_path: str | None) -> bool:
    path = str(req_path or "").split("?", 1)[0]
    return path in ("/oobe", "/oobe.html", "/api/oobe/status", "/api/oobe/save", "/api/health")

def _oobe_redirect_required(req_path: str | None) -> bool:
    if not _oobe_state().get("required"):
        return False
    path = str(req_path or "").split("?", 1)[0]
    if _path_is_oobe_public(path):
        return False
    return True

def _oobe_auth_required() -> bool:
    return bool(_oobe_state().get("required")) and _auth_enabled() and _auth_hashes_present(AUTH_CFG)

def _auth_enabled() -> bool:
    return bool(AUTH_CFG.get("enabled"))

def _auth_check_userpass(username: str, password: str) -> bool:
    if not _auth_enabled():
        return True
    u_hash = str(AUTH_CFG.get("username_sha256") or "").strip().lower()
    p_hash = str(AUTH_CFG.get("password_sha256") or "").strip().lower()
    if not u_hash or not p_hash:
        return False
    u_ok = hmac.compare_digest(_sha256_hex(username), u_hash)
    p_ok = hmac.compare_digest(_sha256_hex(password), p_hash)
    return bool(u_ok and p_ok)

def _auth_check_userpass_hash(username_sha256: str, password_sha256: str) -> bool:
    if not _auth_enabled():
        return True
    u_hash = str(AUTH_CFG.get("username_sha256") or "").strip().lower()
    p_hash = str(AUTH_CFG.get("password_sha256") or "").strip().lower()
    u_in = str(username_sha256 or "").strip().strip("'\"").lower()
    p_in = str(password_sha256 or "").strip().strip("'\"").lower()
    if not re.fullmatch(r"[0-9a-f]{64}", u_in or ""):
        return False
    if not re.fullmatch(r"[0-9a-f]{64}", p_in or ""):
        return False
    if not u_hash or not p_hash:
        return False
    return bool(hmac.compare_digest(u_in, u_hash) and hmac.compare_digest(p_in, p_hash))

def _webauthn_b64u_encode(data: bytes | None) -> str:
    raw = bytes(data or b"")
    return base64.urlsafe_b64encode(raw).rstrip(b"=").decode("ascii")

def _webauthn_b64u_decode(text: str | None) -> bytes:
    raw = str(text or "").strip()
    if not raw:
        return b""
    raw += "=" * (-len(raw) % 4)
    return base64.urlsafe_b64decode(raw.encode("ascii"))

def _webauthn_host_from_header(host_header: str | None) -> str:
    host = str(host_header or "").strip().lower()
    if not host:
        return "localhost"
    if host.startswith("[") and "]" in host:
        host = host[1:host.index("]")]
    elif ":" in host:
        host = host.rsplit(":", 1)[0]
    return host or "localhost"

def _webauthn_origin_from_headers(headers) -> str:
    host = _webauthn_host_from_header(headers.get("Host") if headers is not None else None)
    if headers is not None:
        proto = str(headers.get("X-Forwarded-Proto") or "").strip().lower()
        if proto not in ("http", "https"):
            origin = str(headers.get("Origin") or "").strip()
            m = re.match(r"^(https?)://([^/]+)", origin)
            if m:
                proto = m.group(1).lower()
        if proto not in ("http", "https"):
            proto = "https" if str(headers.get("Upgrade-Insecure-Requests") or "") == "1" else "http"
    else:
        proto = "http"
    return f"{proto}://{host}"

def _webauthn_rp_id_from_headers(headers) -> str:
    return _webauthn_host_from_header(headers.get("Host") if headers is not None else None)

def _webauthn_user_handle() -> bytes:
    seed = str(AUTH_CFG.get("username_sha256") or AUTH_CFG.get("realm") or "Light RID Scanner").strip()
    if not seed:
        seed = "Light RID Scanner"
    return hashlib.sha256((seed + "|passkey").encode("utf-8", errors="ignore")).digest()

_CBOR_BREAK = object()

def _cbor_read_length(data: bytes, offset: int, ai: int) -> tuple[int | None, int]:
    if ai < 24:
        return ai, offset
    if ai == 24:
        return data[offset], offset + 1
    if ai == 25:
        return int.from_bytes(data[offset:offset + 2], "big"), offset + 2
    if ai == 26:
        return int.from_bytes(data[offset:offset + 4], "big"), offset + 4
    if ai == 27:
        return int.from_bytes(data[offset:offset + 8], "big"), offset + 8
    if ai == 31:
        return None, offset
    raise ValueError("unsupported cbor length")

def _cbor_decode_one(data: bytes, offset: int = 0):
    if offset >= len(data):
        raise ValueError("cbor truncated")
    initial = data[offset]
    offset += 1
    major = initial >> 5
    ai = initial & 31
    if major in (0, 1):
        n, offset = _cbor_read_length(data, offset, ai)
        if n is None:
            raise ValueError("indefinite integer")
        return (n if major == 0 else -1 - n), offset
    if major in (2, 3):
        length, offset = _cbor_read_length(data, offset, ai)
        if length is None:
            chunks: list[bytes] = []
            while True:
                if offset >= len(data):
                    raise ValueError("cbor truncated")
                if data[offset] == 0xFF:
                    offset += 1
                    break
                part, offset = _cbor_decode_one(data, offset)
                if major == 2:
                    if not isinstance(part, (bytes, bytearray)):
                        raise ValueError("invalid cbor chunk")
                    chunks.append(bytes(part))
                else:
                    if not isinstance(part, str):
                        raise ValueError("invalid cbor chunk")
                    chunks.append(part.encode("utf-8"))
            raw = b"".join(chunks)
            return (raw if major == 2 else raw.decode("utf-8", errors="replace")), offset
        raw = data[offset:offset + length]
        offset += length
        return (bytes(raw) if major == 2 else raw.decode("utf-8", errors="replace")), offset
    if major == 4:
        length, offset = _cbor_read_length(data, offset, ai)
        items = []
        if length is None:
            while True:
                if offset >= len(data):
                    raise ValueError("cbor truncated")
                if data[offset] == 0xFF:
                    offset += 1
                    break
                item, offset = _cbor_decode_one(data, offset)
                items.append(item)
        else:
            for _ in range(length):
                item, offset = _cbor_decode_one(data, offset)
                items.append(item)
        return items, offset
    if major == 5:
        length, offset = _cbor_read_length(data, offset, ai)
        items = {}
        if length is None:
            while True:
                if offset >= len(data):
                    raise ValueError("cbor truncated")
                if data[offset] == 0xFF:
                    offset += 1
                    break
                key, offset = _cbor_decode_one(data, offset)
                val, offset = _cbor_decode_one(data, offset)
                items[key] = val
        else:
            for _ in range(length):
                key, offset = _cbor_decode_one(data, offset)
                val, offset = _cbor_decode_one(data, offset)
                items[key] = val
        return items, offset
    if major == 6:
        _tag, offset = _cbor_read_length(data, offset, ai)
        return _cbor_decode_one(data, offset)
    if major == 7:
        if ai == 20:
            return False, offset
        if ai == 21:
            return True, offset
        if ai in (22, 23):
            return None, offset
        if ai == 24:
            return data[offset], offset + 1
        if ai == 25:
            raw = int.from_bytes(data[offset:offset + 2], "big")
            offset += 2
            sign = (raw >> 15) & 1
            exp = (raw >> 10) & 0x1F
            frac = raw & 0x3FF
            val = (1 if sign == 0 else -1) * (2 ** (exp - 15)) * (1 + frac / 1024.0)
            return val, offset
        if ai == 26:
            return struct.unpack(">f", data[offset:offset + 4])[0], offset + 4
        if ai == 27:
            return struct.unpack(">d", data[offset:offset + 8])[0], offset + 8
        if ai == 31:
            return _CBOR_BREAK, offset
    raise ValueError("unsupported cbor type")

def _cbor_loads(data: bytes):
    value, offset = _cbor_decode_one(bytes(data or b""))
    if offset != len(data):
        raise ValueError("cbor trailing data")
    return value

def _webauthn_decode_json(data: bytes | str | None) -> dict:
    raw = data.decode("utf-8", errors="replace") if isinstance(data, (bytes, bytearray)) else str(data or "")
    parsed = json.loads(raw)
    if not isinstance(parsed, dict):
        raise ValueError("client data must be object")
    return parsed

def _webauthn_public_key_coords(public_key) -> tuple[int, int]:
    if not isinstance(public_key, dict):
        raise ValueError("public key missing")
    x_raw = public_key.get("x")
    y_raw = public_key.get("y")
    if not x_raw or not y_raw:
        raise ValueError("public key missing coordinates")
    def _decode_coord(raw):
        text = str(raw or "").strip()
        if not text:
            raise ValueError("empty coordinate")
        if re.fullmatch(r"[0-9a-fA-F]{64}", text):
            return int.from_bytes(bytes.fromhex(text), "big")
        buf = _webauthn_b64u_decode(text)
        if len(buf) != 32:
            raise ValueError("invalid coordinate length")
        return int.from_bytes(buf, "big")
    return _decode_coord(x_raw), _decode_coord(y_raw)

_P256_P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
_P256_A = (_P256_P - 3) % _P256_P
_P256_B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
_P256_GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
_P256_GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
_P256_N = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
_P256_G = (_P256_GX, _P256_GY)

def _p256_on_curve(point: tuple[int, int] | None) -> bool:
    if point is None:
        return True
    x, y = point
    if not (0 <= x < _P256_P and 0 <= y < _P256_P):
        return False
    return (y * y - (x * x * x + _P256_A * x + _P256_B)) % _P256_P == 0

def _p256_point_add(p: tuple[int, int] | None, q: tuple[int, int] | None) -> tuple[int, int] | None:
    if p is None:
        return q
    if q is None:
        return p
    x1, y1 = p
    x2, y2 = q
    if x1 == x2:
        if (y1 + y2) % _P256_P == 0:
            return None
        slope = ((3 * x1 * x1 + _P256_A) * pow(2 * y1, -1, _P256_P)) % _P256_P
    else:
        slope = ((y2 - y1) * pow((x2 - x1) % _P256_P, -1, _P256_P)) % _P256_P
    x3 = (slope * slope - x1 - x2) % _P256_P
    y3 = (slope * (x1 - x3) - y1) % _P256_P
    return x3, y3

def _p256_point_mul(k: int, point: tuple[int, int] | None) -> tuple[int, int] | None:
    if point is None:
        return None
    if k % _P256_N == 0:
        return None
    result = None
    addend = point
    n = k % _P256_N
    while n:
        if n & 1:
            result = _p256_point_add(result, addend)
        addend = _p256_point_add(addend, addend)
        n >>= 1
    return result

def _ecdsa_parse_der_signature(sig: bytes) -> tuple[int, int]:
    raw = bytes(sig or b"")
    if len(raw) < 8 or raw[0] != 0x30:
        raise ValueError("invalid signature")
    total_len = raw[1]
    idx = 2
    if total_len & 0x80:
        n_len = total_len & 0x7F
        total_len = int.from_bytes(raw[idx:idx + n_len], "big")
        idx += n_len
    if idx + total_len > len(raw):
        raise ValueError("invalid signature length")
    def read_int() -> int:
        nonlocal idx
        if idx >= len(raw) or raw[idx] != 0x02:
            raise ValueError("invalid signature integer")
        idx += 1
        if idx >= len(raw):
            raise ValueError("invalid signature integer length")
        ln = raw[idx]
        idx += 1
        if ln & 0x80:
            n_len = ln & 0x7F
            ln = int.from_bytes(raw[idx:idx + n_len], "big")
            idx += n_len
        val = int.from_bytes(raw[idx:idx + ln], "big")
        idx += ln
        return val
    r = read_int()
    s = read_int()
    return r, s

def _ecdsa_verify_p256(public_key: dict, message_hash: bytes, signature: bytes) -> bool:
    try:
        x, y = _webauthn_public_key_coords(public_key)
    except Exception:
        return False
    if not _p256_on_curve((x, y)):
        return False
    try:
        r, s = _ecdsa_parse_der_signature(signature)
    except Exception:
        return False
    if not (1 <= r < _P256_N and 1 <= s < _P256_N):
        return False
    e = int.from_bytes(bytes(message_hash or b""), "big")
    w = pow(s, -1, _P256_N)
    u1 = (e * w) % _P256_N
    u2 = (r * w) % _P256_N
    p = _p256_point_add(_p256_point_mul(u1, _P256_G), _p256_point_mul(u2, (x, y)))
    if p is None:
        return False
    return (p[0] % _P256_N) == r

def _webauthn_parse_attestation_object(raw: bytes) -> dict:
    obj = _cbor_loads(bytes(raw or b""))
    if not isinstance(obj, dict):
        raise ValueError("attestation object must be map")
    fmt = str(obj.get("fmt") or "").strip().lower()
    auth_data = obj.get("authData")
    if fmt != "none":
        raise ValueError("only none attestation is supported")
    if not isinstance(auth_data, (bytes, bytearray)) or len(auth_data) < 37:
        raise ValueError("authData missing")
    auth = bytes(auth_data)
    rp_id_hash = auth[:32]
    flags = auth[32]
    sign_count = int.from_bytes(auth[33:37], "big")
    offset = 37
    if not (flags & 0x40):
        raise ValueError("credential data missing")
    if offset + 16 + 2 > len(auth):
        raise ValueError("credential data truncated")
    aaguid = auth[offset:offset + 16]
    offset += 16
    cred_len = int.from_bytes(auth[offset:offset + 2], "big")
    offset += 2
    if offset + cred_len > len(auth):
        raise ValueError("credential id truncated")
    cred_id = auth[offset:offset + cred_len]
    offset += cred_len
    public_key, offset = _cbor_decode_one(auth, offset)
    if offset > len(auth):
        raise ValueError("public key truncated")
    if not isinstance(public_key, dict):
        raise ValueError("public key missing")
    cose_kty = public_key.get(1)
    cose_alg = public_key.get(3)
    cose_crv = public_key.get(-1)
    x = public_key.get(-2)
    y = public_key.get(-3)
    if cose_kty != 2 or cose_alg != -7 or cose_crv != 1 or not x or not y:
        raise ValueError("unsupported credential public key")
    return {
        "auth_data": auth,
        "rp_id_hash": rp_id_hash,
        "flags": flags,
        "credential_id": bytes(cred_id),
        "sign_count": sign_count,
        "public_key": {
            "kty": "EC",
            "crv": "P-256",
            "x": _webauthn_b64u_encode(bytes(x) if isinstance(x, (bytes, bytearray)) else b""),
            "y": _webauthn_b64u_encode(bytes(y) if isinstance(y, (bytes, bytearray)) else b""),
        },
        "aaguid": _webauthn_b64u_encode(aaguid),
    }

# -----------------------------------------------------------------------------
# WebAuthn / passkey helpers
# -----------------------------------------------------------------------------
def _auth_passkeys_public(auth_cfg: dict | None = None) -> list[dict]:
    source = auth_cfg if isinstance(auth_cfg, dict) else AUTH_CFG
    out: list[dict] = []
    for item in _normalize_passkeys(source.get("passkeys")):
        out.append({
            "id": str(item.get("id") or ""),
            "name": str(item.get("name") or ""),
            "enabled": bool(item.get("enabled", True)),
            "created_ts": float(item.get("created_ts") or 0.0),
            "last_used_ts": float(item.get("last_used_ts") or 0.0),
            "sign_count": int(item.get("sign_count") or 0),
        })
    return out

def _passkey_timeout_ms() -> int:
    return int(PASSKEY_CHALLENGE_TTL_SEC * 1000)

def _auth_mutate_passkeys(mutator, *, tag: str = "passkey") -> tuple[bool, str, list[dict]]:
    if not APP_CONFIG_PATH:
        return False, "config path missing", _auth_passkeys_public()
    try:
        with auth_passkey_lock:
            cfg = load_app_config(APP_CONFIG_PATH)
            auth = cfg.setdefault("auth", {})
            if not isinstance(auth, dict):
                auth = {}
                cfg["auth"] = auth
            items = _normalize_passkeys(auth.get("passkeys"))
            auth["passkeys"] = _normalize_passkeys(mutator(list(items)))
            # Passkey changes must stay aligned with the saved config and the
            # in-memory auth runtime, so save + reload are handled as one flow.
            cfg, guard_err = _prepare_security_cfg_for_save(cfg)
            if guard_err:
                return False, guard_err, _auth_passkeys_public()
            b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag=tag)
            if not b_ok:
                return False, f"backup failed: {backup_path}", _auth_passkeys_public()
            ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
            if not ok:
                return False, msg, _auth_passkeys_public()
            cfg_loaded = load_app_config(APP_CONFIG_PATH)
            r_ok, r_msg = reload_runtime_config(cfg_loaded)
            if not r_ok:
                return False, f"reload failed: {r_msg}", _auth_passkeys_public()
            auth_loaded = cfg_loaded.get("auth") if isinstance(cfg_loaded, dict) else None
            return True, "ok", _auth_passkeys_public(auth_loaded if isinstance(auth_loaded, dict) else None)
    except Exception as e:
        return False, str(e), _auth_passkeys_public()

def _passkey_cleanup(now_wall: float | None = None) -> None:
    now_wall = float(now_wall or time.time())
    with passkey_challenge_lock:
        stale = [k for k, v in passkey_challenges.items() if float((v or {}).get("expires_at") or 0.0) <= now_wall]
        for key in stale:
            passkey_challenges.pop(key, None)

def _passkey_challenge_new(kind: str, data: dict | None = None, *, ttl_sec: int = PASSKEY_CHALLENGE_TTL_SEC) -> dict:
    now_wall = time.time()
    token = secrets.token_urlsafe(24)
    row = dict(data or {})
    row.update({
        "kind": kind,
        "challenge": token,
        "created_ts": now_wall,
        "expires_at": now_wall + max(60, int(ttl_sec or PASSKEY_CHALLENGE_TTL_SEC)),
    })
    with passkey_challenge_lock:
        passkey_challenges[token] = row
        if len(passkey_challenges) > 1024:
            _passkey_cleanup(now_wall=now_wall)
    return row

def _passkey_challenge_take(token: str | None, kind: str | None = None) -> dict | None:
    raw = str(token or "").strip()
    if not raw:
        return None
    now_wall = time.time()
    with passkey_challenge_lock:
        row = passkey_challenges.pop(raw, None)
    if not isinstance(row, dict):
        return None
    if float(row.get("expires_at") or 0.0) <= now_wall:
        return None
    if kind and str(row.get("kind") or "") != kind:
        return None
    return row

def _passkey_options_public(passkeys: list[dict]) -> list[dict]:
    out: list[dict] = []
    for item in passkeys:
        cred_id = str(item.get("id") or "").strip()
        if not cred_id or not bool(item.get("enabled", True)):
            continue
        out.append({
            "type": "public-key",
            "id": cred_id,
            "transports": ["internal", "hybrid", "usb", "nfc", "ble"],
        })
    return out

def _passkey_record_payload(passkey_name: str | None = None) -> str:
    name = str(passkey_name or "").strip()
    if name:
        return name[:80]
    return "通行密钥 " + time.strftime("%Y-%m-%d %H:%M:%S")

def _passkey_login_begin(headers) -> dict:
    if not _auth_enabled() or not _auth_hashes_present(AUTH_CFG):
        return {"ok": False, "error": "网页登录账号密码未配置完整"}
    if not _auth_login_method_enabled("passkey"):
        return {"ok": False, "error": "PassKey 登录已关闭"}
    items = [item for item in _normalize_passkeys(AUTH_CFG.get("passkeys")) if bool(item.get("enabled", True))]
    if not items:
        return {"ok": False, "error": "暂无可用的通行密钥"}
    rp_id = _webauthn_rp_id_from_headers(headers)
    origin = _webauthn_origin_from_headers(headers)
    row = _passkey_challenge_new("login", {
        "rp_id": rp_id,
        "origin": origin,
        "allow_credentials": [str(item.get("id") or "") for item in items],
    })
    return {
        "ok": True,
        "challenge": row["challenge"],
        "challenge_token": row["challenge"],
        "rp_id": rp_id,
        "origin": origin,
        "timeout_ms": _passkey_timeout_ms(),
        "allow_credentials": _passkey_options_public(items),
        "passkeys": _auth_passkeys_public(),
        "realm": str(AUTH_CFG.get("realm") or "Light RID Scanner"),
    }

def _passkey_register_begin(body: dict | None, headers, *, client_ip: str | None = None) -> dict:
    if not _auth_enabled() or not _auth_hashes_present(AUTH_CFG):
        return {"ok": False, "error": "网页登录账号密码未配置完整"}, 400
    if not _auth_login_method_enabled("passkey"):
        return {"ok": False, "error": "PassKey 登录已关闭"}, 403
    src = body if isinstance(body, dict) else {}
    user = str(src.get("username") or "").strip()
    pwd = str(src.get("password") or "")
    if not user or not pwd:
        return {"ok": False, "error": "请同时提供账号和密码"}, 400
    if not _auth_check_userpass(user, pwd):
        _op_log("passkey-register", "start auth failed", actor=user or "-", ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": "账号或密码错误"}, 401
    rp_id = _webauthn_rp_id_from_headers(headers)
    origin = _webauthn_origin_from_headers(headers)
    realm = str(AUTH_CFG.get("realm") or "Light RID Scanner")
    passkey_name = _passkey_record_payload(src.get("name") or src.get("label"))
    row = _passkey_challenge_new("register", {
        "rp_id": rp_id,
        "origin": origin,
        "passkey_name": passkey_name,
        "user_handle": _webauthn_b64u_encode(_webauthn_user_handle()),
    })
    return {
        "ok": True,
        "challenge": row["challenge"],
        "challenge_token": row["challenge"],
        "rp_id": rp_id,
        "origin": origin,
        "timeout_ms": _passkey_timeout_ms(),
        "publicKey": {
            "challenge": row["challenge"],
            "rp": {"name": realm, "id": rp_id},
            "user": {
                "id": _webauthn_b64u_encode(_webauthn_user_handle()),
                "name": user,
                "displayName": passkey_name,
            },
            "pubKeyCredParams": [{"type": "public-key", "alg": -7}],
            "timeout": _passkey_timeout_ms(),
            "attestation": "none",
            "authenticatorSelection": {
                "userVerification": "preferred",
                "residentKey": "preferred",
            },
            "excludeCredentials": _passkey_options_public(_normalize_passkeys(AUTH_CFG.get("passkeys"))),
        },
        "passkey_name": passkey_name,
        "realm": realm,
    }

def _passkey_finish_register(body: dict | None, headers, *, client_ip: str | None = None) -> dict:
    if not _auth_login_method_enabled("sso"):
        return {"ok": False, "error": "SSO URL 登录已关闭"}, 403
    src = body if isinstance(body, dict) else {}
    token = str(src.get("challenge") or src.get("challenge_token") or "").strip()
    row = _passkey_challenge_take(token, "register")
    if not row:
        return {"ok": False, "error": "challenge expired"}, 400
    expected_origin = str(row.get("origin") or "")
    expected_rp_id = str(row.get("rp_id") or "")
    response = src.get("response") if isinstance(src.get("response"), dict) else {}
    try:
        # Registration accepts a new credential only after challenge, origin,
        # and rpId validation succeed against the stored single-use challenge.
        client_data_raw = _webauthn_b64u_decode(str(response.get("clientDataJSON") or ""))
        client_data = _webauthn_decode_json(client_data_raw)
        if str(client_data.get("type") or "") != "webauthn.create":
            raise ValueError("invalid client data type")
        if str(client_data.get("challenge") or "") != token:
            raise ValueError("challenge mismatch")
        if str(client_data.get("origin") or "") != expected_origin:
            raise ValueError("origin mismatch")
        att_obj = _webauthn_parse_attestation_object(_webauthn_b64u_decode(str(response.get("attestationObject") or "")))
        cred_id = bytes(att_obj.get("credential_id") or b"")
        if not cred_id:
            raise ValueError("credential id missing")
        if str(expected_rp_id) and hashlib.sha256(expected_rp_id.encode("utf-8", errors="ignore")).digest() != bytes(att_obj.get("rp_id_hash") or b""):
            raise ValueError("rpId mismatch")
        passkey_name = str(src.get("name") or row.get("passkey_name") or "通行密钥").strip() or "通行密钥"
        cred_id_text = _webauthn_b64u_encode(cred_id)
        public_key = att_obj.get("public_key") if isinstance(att_obj.get("public_key"), dict) else {}
        sign_count = int(att_obj.get("sign_count") or 0)
    except Exception as e:
        _op_log("passkey-register", f"finish error={e}", actor=str(src.get("username") or "-"), ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": str(e)}, 400
    def _add_passkey(items):
        items = [dict(item or {}) for item in items]
        items = [item for item in items if str(item.get("id") or "") != cred_id_text]
        items.append({
            "id": cred_id_text,
            "name": passkey_name,
            "user_handle": str(row.get("user_handle") or ""),
            "public_key": public_key,
            "sign_count": sign_count,
            "created_ts": time.time(),
            "last_used_ts": 0.0,
            "enabled": True,
        })
        return items[-32:]
    ok, msg, passkeys = _auth_mutate_passkeys(_add_passkey, tag="passkey_create")
    if not ok:
        return {"ok": False, "error": msg, "passkeys": passkeys}, 500
    _op_log("passkey-register", f"ok name={passkey_name}", actor=str(src.get("username") or "-"), ip=str(client_ip or "-"), ok=True)
    return {"ok": True, "passkeys": passkeys, "passkey_name": passkey_name}, 200

def _passkey_finish_login(body: dict | None, headers, *, client_ip: str | None = None) -> dict:
    if not _auth_enabled() or not _auth_hashes_present(AUTH_CFG):
        return {"ok": False, "error": "网页登录账号密码未配置完整"}, 400
    if not _auth_login_method_enabled("passkey"):
        return {"ok": False, "error": "PassKey 登录已关闭"}, 403
    src = body if isinstance(body, dict) else {}
    token = str(src.get("challenge") or src.get("challenge_token") or "").strip()
    row = _passkey_challenge_take(token, "login")
    if not row:
        return {"ok": False, "error": "challenge expired"}, 400
    expected_origin = str(row.get("origin") or "")
    expected_rp_id = str(row.get("rp_id") or "")
    response = src.get("response") if isinstance(src.get("response"), dict) else {}
    cred_id = str(src.get("id") or src.get("rawId") or "").strip()
    if not cred_id:
        return {"ok": False, "error": "credential id required"}, 400
    passkey_row = None
    for item in _normalize_passkeys(AUTH_CFG.get("passkeys")):
        if str(item.get("id") or "") == cred_id and bool(item.get("enabled", True)):
            passkey_row = dict(item)
            break
    if not passkey_row:
        return {"ok": False, "error": "unknown passkey"}, 401
    try:
        # Login verification stays fully local: validate challenge/origin/rpId,
        # then verify the signature against the stored credential public key.
        client_data_raw = _webauthn_b64u_decode(str(response.get("clientDataJSON") or ""))
        client_data = _webauthn_decode_json(client_data_raw)
        if str(client_data.get("type") or "") != "webauthn.get":
            raise ValueError("invalid client data type")
        if str(client_data.get("challenge") or "") != token:
            raise ValueError("challenge mismatch")
        if str(client_data.get("origin") or "") != expected_origin:
            raise ValueError("origin mismatch")
        auth_data = _webauthn_b64u_decode(str(response.get("authenticatorData") or ""))
        signature = _webauthn_b64u_decode(str(response.get("signature") or ""))
        if len(auth_data) < 37 or not signature:
            raise ValueError("invalid assertion response")
        if expected_rp_id and hashlib.sha256(expected_rp_id.encode("utf-8", errors="ignore")).digest() != auth_data[:32]:
            raise ValueError("rpId mismatch")
        flags = auth_data[32]
        if not (flags & 0x01):
            raise ValueError("user presence required")
        message_hash = hashlib.sha256(auth_data + hashlib.sha256(client_data_raw).digest()).digest()
        if not _ecdsa_verify_p256(passkey_row.get("public_key") or {}, message_hash, signature):
            raise ValueError("signature mismatch")
        sign_count = int.from_bytes(auth_data[33:37], "big")
    except Exception as e:
        _op_log("passkey-login", f"finish error={e}", actor=str(passkey_row.get("name") or "-"), ip=str(client_ip or "-"), ok=False)
        return {"ok": False, "error": str(e)}, 401
    def _touch_passkey(items):
        now_wall = time.time()
        out = []
        for item in items:
            row_item = dict(item or {})
            if str(row_item.get("id") or "") == cred_id:
                row_item["last_used_ts"] = now_wall
                if sign_count > int(row_item.get("sign_count") or 0):
                    row_item["sign_count"] = sign_count
            out.append(row_item)
        return out
    ok, _msg, _ = _auth_mutate_passkeys(_touch_passkey, tag="passkey_use")
    if not ok:
        _log("[WARN] passkey usage update failed: " + str(_msg))
    self_tok = _auth_issue_session()
    _op_log("passkey-login", "login ok", actor=str(passkey_row.get("name") or "-"), ip=str(client_ip or "-"), ok=True)
    return {"ok": True, "next": str(src.get("next") or "/") or "/", "session": self_tok}, 200

def _auth_sso_path(check: str, next_path: str = "/") -> str:
    from urllib.parse import quote
    target = str(next_path or "/").strip() or "/"
    if not target.startswith("/") or target.startswith("//"):
        target = "/"
    user_hash = str(AUTH_CFG.get("username_sha256") or "").strip().lower()
    pass_hash = str(AUTH_CFG.get("password_sha256") or "").strip().lower()
    return (
        "/login?user=" + quote(user_hash, safe="")
        + "&password=" + quote(pass_hash, safe="")
        + "&check=" + quote(str(check or "").strip(), safe="")
        + "&next=" + quote(target, safe="/")
    )

def _auth_sso_public_links(auth_cfg: dict | None = None, *, include_paths: bool = False) -> list[dict]:
    from urllib.parse import quote
    source = auth_cfg if isinstance(auth_cfg, dict) else AUTH_CFG
    user_hash = str(source.get("username_sha256") or "").strip().lower()
    pass_hash = str(source.get("password_sha256") or "").strip().lower()
    out: list[dict] = []
    for item in _normalize_sso_links(source.get("sso_links")):
        check = str(item.get("check") or "").strip()
        next_path = str(item.get("next") or "/")
        path = (
            "/login?user=" + quote(user_hash, safe="")
            + "&password=" + quote(pass_hash, safe="")
            + "&check=" + quote(check, safe="")
            + "&next=" + quote(next_path, safe="/")
        )
        state = _sso_link_state(item)
        row = {
            "name": str(item.get("name") or ""),
            "check": check,
            "enabled": bool(item.get("enabled", True)),
            "created_ts": float(item.get("created_ts") or 0.0),
            "expires_at": float(item.get("expires_at") or 0.0),
            "expires_in_sec": state.get("expires_in_sec"),
            "single_use": bool(item.get("single_use")),
            "used_ts": float(item.get("used_ts") or 0.0),
            "used_count": int(item.get("used_count") or 0),
            "next": next_path,
            "active": bool(state.get("active")),
            "status": str(state.get("status") or ""),
            "status_label": str(state.get("status_label") or ""),
        }
        if include_paths:
            row["path"] = path
        out.append(row)
    return out

def _auth_check_sso_link(username_sha256: str, password_sha256: str, check: str | None) -> dict | None:
    raw_check = str(check or "").strip()
    if not raw_check:
        return None
    if not _auth_login_method_enabled("sso"):
        return None
    if not _auth_check_userpass_hash(username_sha256, password_sha256):
        return None
    for item in _normalize_sso_links(AUTH_CFG.get("sso_links")):
        if hmac.compare_digest(str(item.get("check") or ""), raw_check) and bool(_sso_link_state(item).get("active")):
            return dict(item)
    return None

def _auth_mark_sso_used(check: str | None) -> bool:
    raw_check = str(check or "").strip()
    if not raw_check:
        return False
    changed = False
    now_wall = time.time()
    def _mark(links):
        nonlocal changed
        out = []
        for item in links:
            row = dict(item or {})
            if hmac.compare_digest(str(row.get("check") or ""), raw_check):
                row["used_count"] = int(row.get("used_count") or 0) + 1
                row["used_ts"] = now_wall
                changed = True
            out.append(row)
        return out
    ok, _msg, _links = _auth_mutate_sso_links(_mark, tag="sso_use")
    return bool(ok and changed)

def _build_sso_link_payload(body: dict | None, *, require_reauth: bool = True, headers=None, client_ip: str | None = None) -> tuple[dict, int]:
    if not _auth_enabled() or (not _auth_hashes_present(AUTH_CFG)):
        return {"ok": False, "error": "网页登录鉴权未启用或未完成配置"}, 400
    if not _auth_login_method_enabled("sso"):
        return {"ok": False, "error": "SSO URL 登录已关闭"}, 403
    src = body if isinstance(body, dict) else {}
    subject = str(src.get("username") or "-")
    if require_reauth:
        reauth_ok = _auth_check_userpass(str(src.get("username") or ""), str(src.get("password") or ""))
        if not reauth_ok and headers is not None and headers.get("Authorization"):
            reauth_ok = _auth_check_basic_header(headers.get("Authorization"))
        if not reauth_ok:
            _op_log("login-link-create", "", actor=subject, ip=str(client_ip or "-"), ok=False)
            return {"ok": False, "error": "账号或密码错误"}, 401
    next_path = str(src.get("next") or "/").strip() or "/"
    if not next_path.startswith("/") or next_path.startswith("//"):
        next_path = "/"
    name = str(src.get("name") or "").strip()
    if not name:
        name = "SSO " + time.strftime("%Y-%m-%d %H:%M:%S")
    now_wall = time.time()
    expires_at, expiry_err = _sso_expiry_from_payload(src, now_wall=now_wall)
    if expiry_err:
        return {"ok": False, "error": expiry_err}, 400
    single_use = _to_bool(src.get("single_use"), False)
    check = secrets.token_urlsafe(16)
    def _add_link(links):
        links.append({
            "name": name,
            "check": check,
            "enabled": True,
            "created_ts": now_wall,
            "expires_at": expires_at,
            "single_use": single_use,
            "used_ts": 0.0,
            "used_count": 0,
            "next": next_path,
        })
        return links[-64:]
    ok, msg, links = _auth_mutate_sso_links(_add_link, tag="sso_create")
    if not ok:
        return {"ok": False, "error": msg, "links": links}, 500
    path_url = _auth_sso_path(check, next_path=next_path)
    return {
        "ok": True,
        "check": check,
        "name": name,
        "path": path_url,
        "expires_at": expires_at,
        "expires_in_sec": None if expires_at <= 0 else int(max(0.0, expires_at - now_wall)),
        "single_use": single_use,
        "next": next_path,
        "links": links,
    }, 200

def _auth_mutate_sso_links(mutator, *, tag: str = "sso") -> tuple[bool, str, list[dict]]:
    if not APP_CONFIG_PATH:
        return False, "config path missing", _auth_sso_public_links()
    try:
        with auth_sso_lock:
            cfg = load_app_config(APP_CONFIG_PATH)
            auth = cfg.setdefault("auth", {})
            if not isinstance(auth, dict):
                auth = {}
                cfg["auth"] = auth
            links = _normalize_sso_links(auth.get("sso_links"))
            auth["sso_links"] = _normalize_sso_links(mutator(list(links)))
            cfg, guard_err = _prepare_security_cfg_for_save(cfg)
            if guard_err:
                return False, guard_err, _auth_sso_public_links()
            b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag=tag)
            if not b_ok:
                return False, f"backup failed: {backup_path}", _auth_sso_public_links()
            ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
            if not ok:
                return False, msg, _auth_sso_public_links()
            cfg_loaded = load_app_config(APP_CONFIG_PATH)
            r_ok, r_msg = reload_runtime_config(cfg_loaded)
            if not r_ok:
                return False, f"reload failed: {r_msg}", _auth_sso_public_links()
            auth_loaded = cfg_loaded.get("auth") if isinstance(cfg_loaded, dict) else None
            return True, "ok", _auth_sso_public_links(auth_loaded if isinstance(auth_loaded, dict) else None)
    except Exception as e:
        return False, str(e), _auth_sso_public_links()

def _auth_check_basic_header(header_value: str | None) -> bool:
    if not _auth_enabled():
        return True
    raw = str(header_value or "").strip()
    if not raw.startswith("Basic "):
        return False
    token = raw[6:].strip()
    if not token:
        return False
    try:
        text = base64.b64decode(token).decode("utf-8", errors="replace")
    except Exception:
        return False
    if ":" not in text:
        return False
    user, pwd = text.split(":", 1)
    return _auth_check_userpass(user, pwd)

def _rate_key(scope: str, ip: str | None, subject: str | None = "") -> str:
    return f"{str(scope or 'default')}:{str(ip or '-')}:{str(subject or '-')[:96]}"

def _rate_limited(scope: str, ip: str | None, subject: str | None = "", *, limit: int = 8, window_sec: int = 300, block_sec: int = 900) -> tuple[bool, int]:
    now_wall = time.time()
    key = _rate_key(scope, ip, subject)
    with security_rate_lock:
        st = security_rate_state.get(key) or {"fails": [], "blocked_until": 0.0}
        blocked_until = float(st.get("blocked_until") or 0.0)
        if blocked_until > now_wall:
            return True, int(max(1.0, blocked_until - now_wall))
        fails = [float(x) for x in (st.get("fails") or []) if now_wall - float(x) <= float(window_sec)]
        st["fails"] = fails
        security_rate_state[key] = st
        if len(security_rate_state) > 4096:
            stale = [k for k, v in security_rate_state.items()
                     if float((v or {}).get("blocked_until") or 0.0) <= now_wall and not (v or {}).get("fails")]
            for k in stale[:2048]:
                security_rate_state.pop(k, None)
        if len(fails) >= int(limit):
            st["blocked_until"] = now_wall + float(block_sec)
            return True, int(block_sec)
    return False, 0

def _rate_note(scope: str, ip: str | None, subject: str | None = "", *, success: bool, limit: int = 8, window_sec: int = 300, block_sec: int = 900) -> None:
    key = _rate_key(scope, ip, subject)
    now_wall = time.time()
    with security_rate_lock:
        if success:
            security_rate_state.pop(key, None)
            return
        st = security_rate_state.get(key) or {"fails": [], "blocked_until": 0.0}
        fails = [float(x) for x in (st.get("fails") or []) if now_wall - float(x) <= float(window_sec)]
        fails.append(now_wall)
        st["fails"] = fails
        if len(fails) >= int(limit):
            st["blocked_until"] = now_wall + float(block_sec)
            _op_log("rate-limit", f"scope={scope} subject={str(subject or '-')[:96]} blocked={block_sec}s fails={len(fails)}", ip=str(ip or "-"), ok=False)
        security_rate_state[key] = st
        if len(security_rate_state) > 4096:
            ordered = sorted(security_rate_state.items(), key=lambda kv: max([float(x) for x in ((kv[1] or {}).get("fails") or [0.0])] + [float((kv[1] or {}).get("blocked_until") or 0.0)]), reverse=True)
            security_rate_state.clear()
            security_rate_state.update(dict(ordered[:2048]))

def _auth_cookie_parse(cookie_header: str | None, key: str) -> str:
    raw = str(cookie_header or "")
    if not raw:
        return ""
    for part in raw.split(";"):
        p = str(part or "").strip()
        if not p or "=" not in p:
            continue
        k, v = p.split("=", 1)
        if k.strip() == key:
            return v.strip()
    return ""

def _auth_cleanup_sessions(now_wall: float | None = None) -> None:
    now_wall = float(now_wall or time.time())
    with auth_session_lock:
        stale = [tok for tok, exp in auth_sessions.items() if float(exp or 0.0) <= now_wall]
        for tok in stale:
            auth_sessions.pop(tok, None)

def _auth_issue_session() -> str:
    now_wall = time.time()
    tok_src = f"{now_wall}:{random.random()}:{auth_session_secret}:{os.getpid()}"
    token = hashlib.sha256(tok_src.encode("utf-8", errors="ignore")).hexdigest().lower()
    exp = now_wall + float(AUTH_SESSION_TTL_SEC)
    with auth_session_lock:
        auth_sessions[token] = exp
        if len(auth_sessions) > 4096:
            stale = [tok for tok, ts in auth_sessions.items() if float(ts or 0.0) <= now_wall]
            for tok in stale:
                auth_sessions.pop(tok, None)
            if len(auth_sessions) > 4096:
                # keep most recently expiring sessions
                keep = sorted(auth_sessions.items(), key=lambda kv: float(kv[1]), reverse=True)[:2048]
                auth_sessions.clear()
                auth_sessions.update({k: v for k, v in keep})
    return token

def _auth_check_session_cookie(cookie_header: str | None, *, refresh: bool = True) -> bool:
    if not _auth_enabled():
        return True
    token = _auth_cookie_parse(cookie_header, AUTH_SESSION_COOKIE)
    if not token:
        return False
    now_wall = time.time()
    with auth_session_lock:
        exp = auth_sessions.get(token)
        if not exp or float(exp) <= now_wall:
            auth_sessions.pop(token, None)
            return False
        if refresh:
            auth_sessions[token] = now_wall + float(AUTH_SESSION_TTL_SEC)
    return True

def _request_same_origin(headers) -> bool:
    host = str(headers.get("Host") or "").strip().lower()
    if not host:
        return True
    for header_name in ("Origin", "Referer"):
        raw = str(headers.get(header_name) or "").strip()
        if not raw:
            continue
        try:
            from urllib.parse import urlparse as _urlparse
            parsed = _urlparse(raw)
            if parsed.netloc and parsed.netloc.lower() != host:
                return False
        except Exception:
            return False
    return True

def _page_api_header_ok(headers) -> bool:
    value = str(headers.get(PAGE_API_HEADER) or "").strip()
    return value == PAGE_API_HEADER_VALUE

def _hw_safe_iface(iface: str) -> str | None:
    name = str(iface or "").strip()
    if not name:
        return None
    if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,32}", name):
        return None
    iftypes = _sniff_iface_candidates()
    if name not in iftypes:
        return None
    return name

def _hw_cmd_result(cmd: str, timeout: int = 8) -> dict:
    try:
        proc = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        out = (proc.stdout or "").strip()
        err = (proc.stderr or "").strip()
        ok = (proc.returncode == 0)
        return {
            "ok": ok,
            "cmd": cmd,
            "code": int(proc.returncode),
            "stdout": out,
            "stderr": err,
        }
    except Exception as e:
        return {
            "ok": False,
            "cmd": cmd,
            "code": -1,
            "stdout": "",
            "stderr": str(e),
        }

_HOST_CPU_LOCK = Lock()
_HOST_CPU_CACHE: tuple[float, float] | None = None


def _read_proc_cpu_totals() -> tuple[float, float] | None:
    try:
        with open("/proc/stat", "r", encoding="utf-8", errors="ignore") as f:
            first = f.readline().strip()
        if not first.startswith("cpu "):
            return None
        parts = [float(x) for x in first.split()[1:] if x.strip()]
        if len(parts) < 4:
            return None
        idle = parts[3] + (parts[4] if len(parts) > 4 else 0.0)
        total = float(sum(parts))
        return idle, total
    except Exception:
        return None


def _host_cpu_percent() -> float | None:
    global _HOST_CPU_CACHE
    snap = _read_proc_cpu_totals()
    if snap:
        idle, total = snap
        with _HOST_CPU_LOCK:
            prev = _HOST_CPU_CACHE
            _HOST_CPU_CACHE = (idle, total)
        if prev:
            idle_prev, total_prev = prev
            total_delta = total - total_prev
            idle_delta = idle - idle_prev
            if total_delta > 0:
                busy = max(0.0, min(1.0, 1.0 - (idle_delta / total_delta)))
                return round(busy * 100.0, 1)
    try:
        load1 = os.getloadavg()[0]
        cpu_count = max(1, int(os.cpu_count() or 1))
        return round(max(0.0, min(100.0, (float(load1) / float(cpu_count)) * 100.0)), 1)
    except Exception:
        return None


def _host_mem_stats() -> dict:
    try:
        data: dict[str, int] = {}
        with open("/proc/meminfo", "r", encoding="utf-8", errors="ignore") as f:
            for line in f:
                if ":" not in line:
                    continue
                k, v = line.split(":", 1)
                try:
                    data[k.strip()] = int(v.strip().split()[0])
                except Exception:
                    continue
        total_kb = int(data.get("MemTotal") or 0)
        avail_kb = int(data.get("MemAvailable") or data.get("MemFree") or 0)
        if total_kb <= 0:
            return {"percent": None, "used_mb": None, "total_mb": None}
        used_kb = max(0, total_kb - avail_kb)
        return {
            "percent": round((used_kb / total_kb) * 100.0, 1),
            "used_mb": int(round(used_kb / 1024.0)),
            "total_mb": int(round(total_kb / 1024.0)),
        }
    except Exception:
        return {"percent": None, "used_mb": None, "total_mb": None}


def _host_temperature_from_vcgencmd() -> float | None:
    try:
        out = subprocess.run(["vcgencmd", "measure_temp"], capture_output=True, text=True, timeout=3)
        m = re.search(r"(-?\d+(?:\.\d+)?)", (out.stdout or "") + (out.stderr or ""))
        if m:
            value = float(m.group(1))
            if -40.0 <= value <= 125.0:
                return round(value, 1)
    except Exception:
        pass
    return None


def _host_temperature_from_sysfs(*roots: str) -> float | None:
    candidates: list[tuple[int, float, str]] = []
    for root in roots:
        try:
            for dirpath, _dirs, files in os.walk(root):
                label = ""
                base = os.path.basename(dirpath).lower()
                try:
                    if base.startswith("thermal_zone") and "type" in files:
                        with open(os.path.join(dirpath, "type"), "r", encoding="utf-8", errors="ignore") as f:
                            label = f.read().strip().lower()
                except Exception:
                    label = ""
                for name in files:
                    if not (name == "temp" or (name.startswith("temp") and name.endswith("_input"))):
                        continue
                    path = os.path.join(dirpath, name)
                    sensor_label = label
                    if not sensor_label and base.startswith("hwmon") and "_input" in name:
                        label_name = name[:-6] + "_label"
                        try:
                            with open(os.path.join(dirpath, label_name), "r", encoding="utf-8", errors="ignore") as f:
                                sensor_label = f.read().strip().lower()
                        except Exception:
                            sensor_label = label
                    try:
                        with open(path, "r", encoding="utf-8", errors="ignore") as f:
                            raw = f.read().strip()
                        if not raw:
                            continue
                        value = float(raw)
                        if abs(value) > 250:
                            value = value / 1000.0
                        if not (-40.0 <= value <= 140.0):
                            continue
                    except Exception:
                        continue
                    score = 20
                    if base.startswith("thermal_zone"):
                        score -= 8
                    if any(k in sensor_label for k in ("cpu", "package", "soc", "board", "thermal", "system")):
                        score -= 10
                    if any(k in sensor_label for k in ("max", "crit", "limit", "trip", "hot")):
                        score += 12
                    if value >= 95.0 and not any(k in sensor_label for k in ("cpu", "package", "soc", "board")):
                        score += 8
                    candidates.append((score, float(value), path))
        except Exception:
            continue
    if candidates:
        candidates.sort(key=lambda item: (item[0], abs(item[1] - 55.0), item[1]))
        best = candidates[0]
        if best[1] >= 95.0:
            for item in candidates[1:]:
                if item[1] < 95.0 and item[0] <= best[0] + 8:
                    best = item
                    break
        return round(best[1], 1)
    return None


def _host_temperature_read() -> tuple[float | None, str]:
    source = str(METRICS_CFG.get("temperature_source") or "auto")
    if source == "off":
        return None, "off"
    probes = []
    if source == "vcgencmd":
        probes = [("vcgencmd", _host_temperature_from_vcgencmd)]
    elif source == "thermal_zone":
        probes = [("thermal_zone", lambda: _host_temperature_from_sysfs("/sys/class/thermal"))]
    elif source == "hwmon":
        probes = [("hwmon", lambda: _host_temperature_from_sysfs("/sys/class/hwmon"))]
    else:
        probes = [
            ("vcgencmd", _host_temperature_from_vcgencmd),
            ("thermal_zone", lambda: _host_temperature_from_sysfs("/sys/class/thermal")),
            ("hwmon", lambda: _host_temperature_from_sysfs("/sys/class/hwmon")),
        ]
    for key, probe in probes:
        value = probe()
        if value is not None:
            return value, key
    return None, source


def _host_temperature_c() -> float | None:
    value, _source = _host_temperature_read()
    return value


def _host_temperature_source_label(source: str | None) -> str:
    key = str(source or "").strip().lower().replace("-", "_")
    return {
        "auto": "自动",
        "vcgencmd": "vcgencmd",
        "thermal_zone": "/sys/class/thermal",
        "hwmon": "/sys/class/hwmon",
        "off": "关闭",
    }.get(key, "自动")


def _host_local_ips() -> list[str]:
    ips: list[str] = []
    try:
        text = subprocess.run("hostname -I", shell=True, capture_output=True, text=True, timeout=3).stdout or ""
        for part in text.split():
            s = part.strip()
            if s and s not in ips:
                ips.append(s)
    except Exception:
        pass
    if not ips:
        try:
            host = socket.gethostname()
            for item in socket.getaddrinfo(host, None):
                addr = str(item[4][0] or "").strip()
                if addr and not addr.startswith("127.") and addr != "::1" and addr not in ips:
                    ips.append(addr)
        except Exception:
            pass
    return ips[:12]


def _host_resource_snapshot() -> dict:
    temperature_c, temperature_source = _host_temperature_read()
    mem = _host_mem_stats()
    uptime_sec = None
    try:
        with open("/proc/uptime", "r", encoding="utf-8", errors="ignore") as f:
            uptime_sec = int(float((f.read().strip().split() or ["0"])[0]))
    except Exception:
        uptime_sec = None
    load1 = load5 = load15 = None
    try:
        load1, load5, load15 = os.getloadavg()
    except Exception:
        pass
    return {
        "hostname": str(platform.node() or os.environ.get("COMPUTERNAME") or "host"),
        "cpu_percent": _host_cpu_percent(),
        "cpu_count": int(os.cpu_count() or 1),
        "mem_percent": mem.get("percent"),
        "mem_used_mb": mem.get("used_mb"),
        "mem_total_mb": mem.get("total_mb"),
        "temperature_c": temperature_c,
        "temperature_source": temperature_source,
        "temperature_source_label": _host_temperature_source_label(temperature_source),
        "local_ips": _host_local_ips(),
        "load1": (None if load1 is None else round(float(load1), 2)),
        "load5": (None if load5 is None else round(float(load5), 2)),
        "load15": (None if load15 is None else round(float(load15), 2)),
        "uptime_sec": uptime_sec,
    }

def _host_metrics_ensure_store() -> None:
    parent = os.path.dirname(HOST_METRICS_PATH)
    if parent:
        os.makedirs(parent, exist_ok=True)
    if not os.path.exists(HOST_METRICS_PATH):
        with open(HOST_METRICS_PATH, "a", encoding="utf-8"):
            pass

def _host_metric_point() -> dict:
    host = _host_resource_snapshot()
    aps, _seq, aps_total = _ap_snapshot()
    cpu_count = max(1, int(host.get("cpu_count") or os.cpu_count() or 1))
    load1 = host.get("load1")
    load_percent = None
    try:
        if load1 is not None:
            load_percent = round(max(0.0, min(100.0, (float(load1) / float(cpu_count)) * 100.0)), 1)
    except Exception:
        load_percent = None
    return {
        "ts": time.time(),
        "cpu": host.get("cpu_percent"),
        "mem": host.get("mem_percent"),
        "temp": host.get("temperature_c"),
        "load": load_percent,
        "load1": load1,
        "ap": int(aps_total if aps_total is not None else len(aps)),
    }

def _host_metrics_read_all() -> list[dict]:
    _host_metrics_ensure_store()
    rows: list[dict] = []
    try:
        with open(HOST_METRICS_PATH, "r", encoding="utf-8", errors="replace") as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                try:
                    obj = json.loads(line)
                except Exception:
                    continue
                if isinstance(obj, dict) and obj.get("ts") is not None:
                    rows.append(obj)
    except Exception:
        return []
    rows.sort(key=lambda x: float(x.get("ts") or 0.0))
    return rows

def _host_metrics_prune_and_write(rows: list[dict]) -> None:
    retention = int(METRICS_CFG.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT)
    cutoff = time.time() - max(1, retention) * 86400.0
    kept = [x for x in rows if float(x.get("ts") or 0.0) >= cutoff]
    tmp_path = HOST_METRICS_PATH + ".tmp"
    _host_metrics_ensure_store()
    with open(tmp_path, "w", encoding="utf-8") as f:
        for item in kept:
            f.write(json.dumps(item, ensure_ascii=False, separators=(",", ":")) + "\n")
    os.replace(tmp_path, HOST_METRICS_PATH)

def _host_metrics_sample(force: bool = False) -> dict | None:
    global host_metrics_last_sample_wall
    now = time.time()
    with host_metrics_lock:
        if (not force) and host_metrics_last_sample_wall and (now - host_metrics_last_sample_wall) < HOST_METRICS_SAMPLE_SEC:
            return None
        host_metrics_last_sample_wall = now
    point = _host_metric_point()
    with host_metrics_lock:
        rows = _host_metrics_read_all()
        rows.append(point)
        _host_metrics_prune_and_write(rows)
    return point

def _decimate_points(rows: list[dict], max_points: int = 720) -> list[dict]:
    if len(rows) <= max_points:
        return rows
    step = max(1, int(math.ceil(len(rows) / float(max_points))))
    out = rows[::step]
    if rows and out[-1] is not rows[-1]:
        out.append(rows[-1])
    return out

def _host_metrics_payload(window_sec: int = 24 * 3600) -> dict:
    try:
        window_sec = max(3600, min(7 * 86400, int(window_sec)))
    except Exception:
        window_sec = 24 * 3600
    try:
        _host_metrics_sample(force=False)
    except Exception:
        pass
    cutoff = time.time() - float(window_sec)
    with host_metrics_lock:
        rows = [x for x in _host_metrics_read_all() if float(x.get("ts") or 0.0) >= cutoff]
    return {
        "ok": True,
        "window_sec": int(window_sec),
        "retention_days": int(METRICS_CFG.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT),
        "temperature_source": str(METRICS_CFG.get("temperature_source") or "auto"),
        "temperature_source_label": _host_temperature_source_label(METRICS_CFG.get("temperature_source")),
        "sample_interval_sec": int(HOST_METRICS_SAMPLE_SEC),
        "store_path": HOST_METRICS_PATH,
        "count": len(rows),
        "items": _decimate_points(rows, max_points=900),
    }

def host_metrics_loop() -> None:
    try:
        _host_metrics_sample(force=True)
    except Exception as e:
        _log(f"[WARN] host metrics initial sample failed: {e}")
    while True:
        try:
            _host_metrics_sample(force=False)
        except Exception as e:
            _log(f"[WARN] host metrics sample failed: {e}")
        time.sleep(HOST_METRICS_SAMPLE_SEC)


def _hw_status_snapshot() -> dict:
    items = _iface_options_snapshot()
    host = _host_resource_snapshot()
    host["ifaces"] = items
    return {
        "items": items,
        "active_iface": str(sniff_iface_name or ""),
        "sniff_state": _sniff_health_meta(time.monotonic(), time.time()),
        "current_channel": int(current_channel or 0),
        "scan_wifi_fast": bool(SCAN_WIFI_FAST),
        "wifi_fast_supported": WIFI_FAST_SUPPORTED,
        "wifi_fast_msg": str(WIFI_FAST_SUPPORT_MSG or ""),
        "host": host,
    }

def _hw_execute_task(task: dict) -> dict:
    global current_channel
    op = str(task.get("op") or "").strip().lower()
    iface = _hw_safe_iface(task.get("iface"))
    if op == "status":
        return {"ok": True, "data": _hw_status_snapshot()}
    if op == "list_ifaces":
        return {"ok": True, "items": _iface_options_snapshot(), "active_iface": str(sniff_iface_name or "")}
    if op == "iw_dev":
        return _hw_cmd_result("iw dev", timeout=8)
    if op == "iw_info":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        return _hw_cmd_result(f"iw dev {iface} info", timeout=8)
    if op == "iw_link":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        return _hw_cmd_result(f"iw dev {iface} link", timeout=8)
    if op == "set_monitor":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        steps = [
            _hw_cmd_result(f"ip link set {iface} down", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set type monitor", timeout=8),
            _hw_cmd_result(f"ip link set {iface} up", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set power_save off", timeout=8),
        ]
        return {"ok": all(s.get("ok") for s in steps), "steps": steps}
    if op == "set_managed":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        steps = [
            _hw_cmd_result(f"ip link set {iface} down", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set type managed", timeout=8),
            _hw_cmd_result(f"ip link set {iface} up", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set power_save off", timeout=8),
        ]
        return {"ok": all(s.get("ok") for s in steps), "steps": steps}
    if op == "restart_iface":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        steps = [
            _hw_cmd_result(f"ip link set {iface} down", timeout=8),
            _hw_cmd_result(f"ip link set {iface} up", timeout=8),
            _hw_cmd_result(f"iw dev {iface} set power_save off", timeout=8),
        ]
        return {"ok": all(s.get("ok") for s in steps), "steps": steps}
    if op == "set_channel":
        if not iface:
            return {"ok": False, "error": "invalid iface"}
        try:
            ch = int(task.get("channel"))
        except Exception:
            return {"ok": False, "error": "invalid channel"}
        if ch < 1 or ch > 196:
            return {"ok": False, "error": "channel out of range"}
        r = _hw_cmd_result(f"iw dev {iface} set channel {ch}", timeout=8)
        if r.get("ok"):
            current_channel = ch
        return r
    if op == "restart_program":
        ok, msg = _schedule_self_restart(list(sys.argv[1:]))
        return {"ok": bool(ok), "msg": msg}
    return {"ok": False, "error": f"unsupported op: {op}"}

def _hw_worker_loop() -> None:
    while True:
        task = hw_task_queue.get()
        if not isinstance(task, dict):
            continue
        rsp_q = task.get("_rsp_q")
        try:
            out = _hw_execute_task(task)
        except Exception as e:
            out = {"ok": False, "error": str(e)}
        if isinstance(rsp_q, queue.Queue):
            try:
                rsp_q.put_nowait(out)
            except Exception:
                pass

def start_hw_worker() -> None:
    global hw_worker_started
    with hw_worker_lock:
        if hw_worker_started:
            return
        hw_worker_started = True
    Thread(target=_hw_worker_loop, daemon=True).start()

def _hw_submit_task(task: dict, timeout_sec: float = 12.0) -> dict:
    start_hw_worker()
    rsp_q: "queue.Queue[dict]" = queue.Queue(maxsize=1)
    item = dict(task or {})
    item["_rsp_q"] = rsp_q
    try:
        hw_task_queue.put_nowait(item)
    except queue.Full:
        return {"ok": False, "error": "hardware helper busy"}
    try:
        out = rsp_q.get(timeout=max(0.5, float(timeout_sec)))
    except Exception:
        return {"ok": False, "error": "hardware helper timeout"}
    return out if isinstance(out, dict) else {"ok": False, "error": "invalid helper response"}

_PAGE_HTML = """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Light RID Scanner</title>
<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"/>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Rajdhani:wght@500;600;700&family=Share+Tech+Mono&display=swap" rel="stylesheet">
<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"></script>
<style>
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
:root{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--panel:#2b2a29;--panel2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --green:#92c353;--yellow:#ffb900;--dim:#c8c6c4;--blue:#2899f5;
  --purple:#caa0ff;--cyan:#7dc6ff;--glow:rgba(40,153,245,.12);--soft:rgba(255,255,255,.03)
}
body{background:var(--bg);color:var(--txt);font-family:var(--font-ui);font-size:16px;
     height:100dvh;display:grid;grid-template-rows:auto minmax(0,1fr) minmax(240px,38vh) auto;
     row-gap:12px;overflow:hidden;position:relative;
     transition:background-color .16s ease,color .16s ease;
     background:linear-gradient(180deg,var(--bg),var(--bg2) 18%,var(--bg))}
body.theme-light{
  --bg:#f3f2f1;--bg2:#edebe9;--panel:#ffffff;--panel2:#faf9f8;--border:#e1dfdd;--txt:#323130;
  --green:#107c10;--yellow:#986f0b;--dim:#605e5c;--blue:#0078d4;
  --purple:#6b5bd2;--cyan:#005a9e;--glow:rgba(0,120,212,.10);--soft:rgba(0,0,0,.018)
}
body::before{
  content:""; position:fixed; inset:0; pointer-events:none; z-index:0;
  background:linear-gradient(180deg, rgba(255,255,255,.04), rgba(255,255,255,0) 140px);
}
body.theme-light::before{
  background:linear-gradient(180deg, rgba(255,255,255,.65), rgba(255,255,255,0) 140px);
}
header,.tbl-wrap,.panel,footer{position:relative;z-index:1}
.mono, code, .logbox, .aplist, .adv-input, .stat b{font-family:var(--font-mono)}

/* -- Header -- */
header{background:var(--panel);border-bottom:1px solid var(--border);
       padding:10px 14px;display:grid;grid-template-columns:auto auto minmax(0,1fr);
       align-items:center;gap:8px 16px;position:sticky;top:0;z-index:10;
       box-shadow:0 1px 3px rgba(0,0,0,.12)}
header .head-stats{display:flex;align-items:center;justify-content:flex-end;
       gap:8px 16px;flex-wrap:wrap;min-width:0;grid-column:3}
header h1{font-size:20px;font-weight:600;color:var(--txt);letter-spacing:.01em;text-transform:none}
.app-version-label{font-family:var(--font-mono);font-size:12px;font-weight:600;line-height:1;color:var(--dim);white-space:nowrap}
.adv-modal{
  position:fixed;inset:0;z-index:10006;background:rgba(3,8,14,.62);
  display:none;align-items:center;justify-content:center;padding:12px;
}
.adv-modal.show{display:flex}
.adv-window{
  width:min(1120px, calc(100vw - 24px));max-height:calc(100vh - 24px);overflow:auto;
  border:1px solid var(--border);border-radius:4px;background:var(--panel);
  box-shadow:0 18px 36px rgba(0,0,0,.20);
}
.adv-window-hd{
  display:flex;align-items:center;justify-content:space-between;gap:8px;
  padding:10px 12px;border-bottom:1px solid var(--border);color:var(--txt);font-size:14px;font-weight:600;
}
.adv-window-hd .btn-mini{padding:4px 8px}
.adv-body{
  padding:10px;
  display:grid;
  grid-template-columns:repeat(2,minmax(0,1fr));
  gap:10px;
}
.adv-col{display:grid;gap:8px;min-width:0;align-content:start}
.adv-row{display:flex;gap:8px;align-items:center;flex-wrap:wrap;min-width:0}
.adv-row label{font-size:13px;color:var(--dim)}
.adv-row.focus-pulse{
  border:1px solid color-mix(in srgb, var(--blue) 48%, var(--border));
  border-radius:4px;
  padding:6px;
  box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 24%, transparent);
  animation:hwPulse .9s ease-out 2;
}
@keyframes hwPulse{
  0%{box-shadow:0 0 0 0 rgba(88,166,255,.30)}
  100%{box-shadow:0 0 0 10px rgba(88,166,255,0)}
}
@keyframes alarmRowPulse{from{box-shadow:inset 3px 0 0 rgba(255,79,79,.55)}to{box-shadow:inset 3px 0 0 rgba(255,79,79,1)}}
.adv-input{min-width:260px;flex:1 1 420px;background:var(--panel2);color:var(--txt);border:1px solid var(--border);border-radius:4px;padding:7px 9px;font:inherit}
.adv-note{font-size:13px;color:var(--dim);word-break:break-all}
.adv-note code{color:var(--txt)}
.adv-actions{display:flex;gap:8px;flex-wrap:wrap}
.cfg-editor{
  width:100%;min-height:220px;resize:vertical;
  background:var(--panel2);color:var(--txt);border:1px solid var(--border);border-radius:4px;
  padding:8px 10px;font:13px/1.5 var(--font-mono);
}
.stat{font-size:15px;color:var(--dim);white-space:nowrap}
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
  border:1px solid color-mix(in srgb, var(--warn) 44%, var(--border));
  border-radius:4px;
  background:color-mix(in srgb, var(--warn) 10%, var(--panel));
  color:#ffd7cc;
  font-size:13px;
  line-height:1.35;
  z-index:12;
}
.sniff-banner.warn{
  border-color:color-mix(in srgb, var(--yellow) 38%, var(--border));
  background:color-mix(in srgb, var(--yellow) 11%, var(--panel));
  color:#f5e2a8;
}
.security-banner{
  align-items:center;
  justify-content:space-between;
  gap:10px;
}
.security-banner .btn-mini{flex:0 0 auto}
.banner-stack{
  position:fixed;top:10px;left:50%;transform:translateX(-50%);
  display:flex;flex-direction:column;gap:8px;z-index:9998;
  width:min(92vw, 860px);pointer-events:none;
}
.banner{
  opacity:0;transform:translateY(-6px);
  transition:opacity .18s ease,transform .18s ease;
  border:1px solid var(--border);border-radius:4px;
  background:var(--panel);color:var(--txt);
  padding:9px 12px;font-size:13px;line-height:1.35;
  box-shadow:0 8px 18px rgba(0,0,0,.16);
}
.banner.show{opacity:1;transform:translateY(0)}
.banner.ok{border-color:color-mix(in srgb, var(--green) 40%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel));color:color-mix(in srgb, var(--green) 72%, white)}
.banner.warn{border-color:color-mix(in srgb, var(--yellow) 34%, var(--border));background:color-mix(in srgb, var(--yellow) 10%, var(--panel));color:#ffd9a9}
.notify-center-button{
  position:fixed;right:18px;bottom:18px;z-index:9999;width:54px;height:54px;border-radius:50%;
  border:1px solid color-mix(in srgb, var(--blue) 40%, var(--border));
  background:color-mix(in srgb, var(--panel) 92%, transparent);color:var(--txt);
  box-shadow:0 12px 28px rgba(0,0,0,.28);backdrop-filter:blur(10px);
  display:flex;align-items:center;justify-content:center;cursor:pointer;font:700 18px/1 var(--font-ui);
  transition:transform .14s ease,border-color .14s ease,background-color .14s ease,box-shadow .14s ease;
}
.notify-center-button:hover,.notify-center-button.active{transform:translateY(-2px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 12%, var(--panel));box-shadow:0 16px 34px rgba(0,0,0,.34)}
.notify-center-glyph{position:relative;width:22px;height:22px;border:2px solid currentColor;border-radius:50%;display:block}
.notify-center-glyph::before{content:"";position:absolute;left:50%;top:4px;width:2px;height:9px;background:currentColor;transform:translateX(-50%)}
.notify-center-glyph::after{content:"";position:absolute;left:50%;bottom:4px;width:4px;height:4px;border-radius:50%;background:currentColor;transform:translateX(-50%)}
.notify-center-count{
  position:absolute;right:-3px;top:-3px;min-width:20px;height:20px;padding:0 5px;border-radius:999px;
  display:none;align-items:center;justify-content:center;background:#d83b01;color:#fff;
  border:2px solid var(--panel);font:700 11px/1 var(--font-ui);
}
.notify-center-button.has-items .notify-center-count{display:flex}
.notify-center-panel{
  position:fixed;right:18px;bottom:84px;z-index:9999;width:min(380px,calc(100vw - 28px));
  max-height:min(560px,calc(100vh - 110px));display:none;flex-direction:column;overflow:hidden;
  border:1px solid var(--border);border-radius:6px;background:color-mix(in srgb, var(--panel) 96%, transparent);
  box-shadow:0 18px 42px rgba(0,0,0,.34);backdrop-filter:blur(14px);
}
.notify-center-panel.show{display:flex}
.notify-center-head{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:12px 14px;border-bottom:1px solid var(--border);background:color-mix(in srgb, var(--panel2) 84%, transparent)}
.notify-center-title{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.notify-center-sub{margin-top:4px;color:var(--dim);font-size:12px}
.notify-center-list{padding:8px;display:grid;gap:8px;overflow:auto}
.notify-center-empty{padding:28px 12px;text-align:center;color:var(--dim);font-size:13px}
.notify-item{display:grid;grid-template-columns:4px minmax(0,1fr) auto;gap:10px;align-items:start;padding:10px;border:1px solid color-mix(in srgb, var(--border) 86%, transparent);border-radius:5px;background:color-mix(in srgb, var(--panel2) 82%, transparent)}
.notify-item-bar{width:4px;height:100%;min-height:42px;border-radius:999px;background:var(--blue)}
.notify-item.ok .notify-item-bar{background:var(--green)}
.notify-item.warn .notify-item-bar{background:var(--yellow)}
.notify-item-text{color:var(--txt);font-size:13px;line-height:1.4;white-space:pre-wrap;word-break:break-word}
.notify-item-time{margin-top:6px;color:var(--dim);font-size:11px}
.notify-item-del{width:24px;height:24px;border:1px solid var(--border);border-radius:4px;background:var(--panel);color:var(--dim);cursor:pointer;line-height:1}
.notify-item-del:hover{border-color:var(--blue);color:var(--txt);background:color-mix(in srgb, var(--blue) 10%, var(--panel))}
#dot-ws{width:9px;height:9px;border-radius:50%;background:var(--dim);
        display:inline-block;margin-right:4px;transition:background .3s}
#dot-ws.on{background:var(--green)}

/* -- Table -- */
.tbl-wrap{margin:0 12px;min-height:0;overflow:auto;
          border:1px solid var(--border);border-radius:4px;background:var(--panel);
          box-shadow:0 1px 3px rgba(0,0,0,.08)}
table{width:100%;border-collapse:collapse;table-layout:fixed;min-width:980px}
thead tr{background:var(--panel2);position:sticky;top:0;z-index:9}
thead th{padding:9px 10px;text-align:left;font-size:14px;color:var(--dim);
          border-bottom:1px solid var(--border);white-space:nowrap}
tbody tr{border-bottom:1px solid color-mix(in srgb, var(--border) 70%, transparent);transition:background-color .14s ease}
tbody tr:hover{background:color-mix(in srgb, var(--blue) 7%, var(--panel))}
tbody tr.lost{opacity:.4}
tbody tr.selected{background:color-mix(in srgb, var(--blue) 12%, var(--panel))}
tbody tr.alarm-zone{background:color-mix(in srgb, #ff3b30 12%, var(--panel));animation:alarmRowPulse .9s ease-in-out infinite alternate}
td{padding:8px 10px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:16px}
.empty{text-align:center;padding:40px;color:var(--dim);font-size:15px}
th:nth-child(1),td:nth-child(1){width:46px}
th:nth-child(2),td:nth-child(2){width:46px}
th:nth-child(3),td:nth-child(3){width:330px}
th:nth-child(4),td:nth-child(4){width:132px}
th:nth-child(5),td:nth-child(5){width:96px}
th:nth-child(6),td:nth-child(6){width:62px}
th:nth-child(7),td:nth-child(7){width:68px}
th:nth-child(8),td:nth-child(8){width:92px}
th:nth-child(9),td:nth-child(9){width:176px}
th:nth-child(10),td:nth-child(10){width:112px}
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
    grid-template-columns:auto auto;
    padding:8px 10px;
    gap:8px 10px;
  }
  header h1{font-size:18px}
  header .head-stats{
    grid-column:1/-1;
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
  .adv-window{width:calc(100vw - 12px);max-height:calc(100vh - 12px)}
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
  .app-version-label{font-size:11px}
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
       box-shadow:0 12px 26px rgba(0,0,0,.22), 0 0 0 1px rgba(97,183,255,.04) inset}
.panel-hdr{background:var(--panel2);padding:8px 14px;font-size:14px;
           color:var(--txt);font-weight:600;border-bottom:1px solid var(--border);
           display:flex;justify-content:space-between;align-items:center}
.panel-hdr span.sub{color:var(--dim);font-size:13px;font-weight:400}
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
.rid-drone-icon{background:transparent;border:0}
.drone-pin{position:relative;width:74px;height:58px;pointer-events:none;opacity:var(--drone-op,1)}
.drone-symbol{
  position:absolute;left:2px;top:7px;width:46px;height:46px;transform:rotate(var(--drone-rot,0deg));
  transform-origin:50% 50%;filter:drop-shadow(0 2px 4px rgba(0,0,0,.32));
}
.drone-pin.selected .drone-symbol{filter:drop-shadow(0 0 8px rgba(255,255,255,.62)) drop-shadow(0 2px 4px rgba(0,0,0,.32))}
.drone-index{
  position:absolute;left:46px;top:5px;min-width:24px;height:22px;padding:0 5px;border-radius:999px;
  display:flex;align-items:center;justify-content:center;
  border:1px solid rgba(255,255,255,.92);background:rgba(20,24,28,.86);color:#fff;
  font:800 11px/1 var(--font-mono);box-shadow:0 2px 5px rgba(0,0,0,.24);
}
.drone-pin.alarm .drone-symbol,.drone-pin.alarm .drone-index{animation:droneAlarmBlink .72s ease-in-out infinite alternate}
@keyframes droneAlarmBlink{from{opacity:.38;filter:drop-shadow(0 0 0 rgba(255,59,48,0)) drop-shadow(0 2px 4px rgba(0,0,0,.32))}to{opacity:1;filter:drop-shadow(0 0 10px rgba(255,59,48,.88)) drop-shadow(0 2px 4px rgba(0,0,0,.32))}}
.replay-sync-banner{
  display:none;position:absolute;left:50%;top:60px;z-index:1210;transform:translateX(-50%);
  align-items:center;gap:8px;padding:8px 12px;border:1px solid rgba(255,185,0,.52);border-radius:5px;
  background:color-mix(in srgb, var(--panel) 90%, transparent);color:#ffe4a3;
  box-shadow:0 8px 20px rgba(0,0,0,.22);backdrop-filter:blur(8px);font:700 13px/1 var(--font-ui);
}
#map-panel.replay-sync-paused .replay-sync-banner{display:flex}
.replay-sync-dot{width:8px;height:8px;border-radius:50%;background:#ffb900;box-shadow:0 0 0 0 rgba(255,185,0,.42);animation:replaySyncPulse 1s ease-out infinite}
@keyframes replaySyncPulse{to{box-shadow:0 0 0 9px rgba(255,185,0,0)}}
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
  border:1px solid var(--border);border-radius:4px;
  background:color-mix(in srgb, var(--panel) 94%, transparent);backdrop-filter:blur(6px);
  padding:8px;
  box-shadow:0 8px 18px rgba(0,0,0,.14);
}
.map-mini-list .mini-title{font-size:12px;color:var(--dim);margin-bottom:6px}
.map-mini-list .mini-item{
  display:flex;align-items:center;gap:8px;padding:4px 2px;font-size:13px;white-space:nowrap;
}
.map-mini-list .mini-item .sn{overflow:hidden;text-overflow:ellipsis}
.map-mini-list .mini-item .mini-model{margin-left:auto;max-width:42%;overflow:hidden;text-overflow:ellipsis;color:var(--dim)}
.panel.map-panel.fullscreen .map-mini-list{display:block}

/* -- Log Box -- */
.logbox{flex:1;overflow-y:auto;padding:7px 12px;
        font-size:14px;line-height:1.65;
        background:var(--bg);min-height:0}
.logbox .ap{color:var(--txt)}
.logbox .rid{color:var(--green);font-weight:700}
.panel-hdr label{display:flex;align-items:center;gap:6px;cursor:pointer;
                 color:var(--dim);font-weight:400;font-size:13px}
.btn-mini{
  border:1px solid var(--border);background:var(--panel2);color:var(--txt);
  padding:5px 9px;border-radius:4px;font:600 13px/1 var(--font-ui);cursor:pointer;
  letter-spacing:0;
  transition:background-color .14s ease,border-color .14s ease,box-shadow .14s ease,color .14s ease,transform .14s ease;
  box-shadow:0 1px 2px rgba(0,0,0,.06);
}
.btn-mini:hover{background:color-mix(in srgb, var(--blue) 10%, var(--panel2));border-color:var(--blue);box-shadow:0 2px 8px var(--glow);transform:translateY(-1px)}
.btn-mini:disabled{opacity:.55;cursor:wait}
.btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:color-mix(in srgb, var(--warn) 74%, white)}
.btn-mini.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--panel2))}
#bottom-restore{
  position:fixed;right:12px;bottom:12px;z-index:9996;display:none;
  box-shadow:0 8px 24px rgba(0,0,0,.26);
}
body.bottom-all-collapsed #bottom-restore{display:inline-flex}
.sn-cell{display:flex;align-items:center;gap:6px;min-width:0}
.sn-text-stack{display:flex;flex-direction:column;gap:2px;min-width:0}
.sn-cell .mono{min-width:0;overflow:hidden;text-overflow:ellipsis}
.uas-line{font:700 11px/1.2 var(--font-mono);color:var(--dim);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.uas-line.empty{opacity:.6}
.sn-badge{
  display:inline-block;padding:1px 6px;border-radius:999px;font-size:11px;
  border:1px solid color-mix(in srgb, var(--yellow) 38%, var(--border));background:color-mix(in srgb, var(--yellow) 12%, var(--panel2));color:#ffd85f;line-height:1.3;flex:0 0 auto;
}
.sn-badge.firmware-new{border-color:rgba(46,204,113,.55);background:rgba(46,204,113,.14);color:#98f5be}
.sn-badge.firmware-old{border-color:color-mix(in srgb, var(--blue) 34%, var(--border));background:color-mix(in srgb, var(--blue) 9%, var(--panel2));color:#9fd0ff}
.sn-badge.alarm{border-color:rgba(255,79,79,.72);background:rgba(255,79,79,.16);color:#ffb3ae}
.icon-btn{
  border:1px solid var(--border);background:var(--panel2);color:var(--dim);
  width:24px;height:24px;display:inline-flex;align-items:center;justify-content:center;
  border-radius:4px;cursor:pointer;font-size:12px;line-height:1;flex:0 0 auto;
  transition:background-color .14s ease,border-color .14s ease,color .14s ease,transform .14s ease,box-shadow .14s ease;
  box-shadow:0 1px 2px rgba(0,0,0,.05);
}
.icon-btn:hover{background:color-mix(in srgb, var(--blue) 10%, var(--panel2));color:var(--txt);border-color:var(--blue);transform:translateY(-1px)}
.icon-btn.done{border-color:color-mix(in srgb, var(--green) 42%, var(--border));color:color-mix(in srgb, var(--green) 72%, white)}
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
  border:1px solid var(--border);border-radius:4px;overflow:hidden;
  background:var(--panel);
  box-shadow:0 16px 32px rgba(0,0,0,.18);
  display:flex;flex-direction:column;
}
.info-card-hd{
  display:flex;align-items:center;justify-content:space-between;gap:8px;
  padding:10px 12px;border-bottom:1px solid var(--border);color:var(--txt);font-weight:600;
}
.info-card-close{
  border:1px solid var(--border);background:var(--panel2);color:var(--dim);
  width:26px;height:26px;border-radius:4px;cursor:pointer;line-height:1;
}
.info-card-close:hover{background:color-mix(in srgb, var(--blue) 10%, var(--panel2));color:var(--txt);border-color:var(--blue)}
.info-card-body{
  padding:12px 14px;overflow:auto;
  white-space:normal;line-height:1.6;color:var(--txt);font-size:14px;
}
.info-grid{display:grid;grid-template-columns:1fr;gap:4px}
.info-row{display:grid;grid-template-columns:110px 1fr;gap:8px;align-items:start}
.info-row .k{color:var(--dim)}
.info-row .v{word-break:break-all}
.raw-title{margin:10px 0 6px 0;font-weight:600;color:var(--txt)}
.raw-meta{font-size:12px;color:var(--dim);margin:6px 0 4px 0}
.raw-code{
  margin:0 0 8px 0;padding:8px 10px;border-radius:4px;
  border:1px solid var(--border);background:var(--panel2);color:var(--txt);
  font:12px/1.45 var(--font-mono);white-space:pre-wrap;word-break:break-all;
}
.raw-empty{color:var(--dim);font-size:13px}
.info-card-body .mono{font-family:var(--font-mono)}
.aplist{flex:1;min-height:0;max-height:min(34vh,360px);overflow:auto;background:var(--panel);font-size:13px;line-height:1.45;padding:6px 8px}
.aplist .ap-empty{color:var(--dim);padding:14px 8px}
.aprow{display:grid;grid-template-columns:42px minmax(116px, 15ch) 62px 86px minmax(0,1.15fr) minmax(0,1fr);gap:8px;padding:6px 6px;border-bottom:1px solid color-mix(in srgb, var(--border) 70%, transparent);align-items:start}
.aprow:hover{background:color-mix(in srgb, var(--blue) 6%, var(--panel))}
.aprow.hd{position:sticky;top:0;background:var(--panel2);color:var(--dim);font-weight:600;z-index:1}
.aprow .idx{text-align:right;color:var(--dim)}
.aprow .mono{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.aprow .ap-mac{font-feature-settings:"tnum" 1}
.aplist.wide .aprow{grid-template-columns:42px minmax(170px, 20ch) 64px 92px minmax(0,1.15fr) minmax(0,1fr)}
.aplist.narrow .aprow{grid-template-columns:30px minmax(96px, 12ch) 54px minmax(0,1fr)}
.aplist.narrow .aprow > :nth-child(4),
.aplist.narrow .aprow > :nth-child(6){display:none}
.aprow .ssid{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all}
.aprow .vendor{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all;color:var(--txt)}
.aprow .ssid-col,.aprow .vendor-col{min-width:0}
.subline{font-size:11px;color:var(--dim)}

body.theme-light header{
  background:var(--panel);
  box-shadow:0 1px 3px rgba(0,0,0,.06);
}
body.theme-light .adv-window{
  background:var(--panel);
  border-color:var(--border);
  box-shadow:0 16px 30px rgba(15,23,42,.12);
}
body.theme-light .adv-window-hd{
  color:var(--txt);border-bottom-color:var(--border);
}
body.theme-light .tbl-wrap{
  background:var(--panel);
  box-shadow:0 1px 3px rgba(15,23,42,.06);
}
body.theme-light thead tr{background:var(--panel2)}
body.theme-light thead th{color:var(--dim)}
body.theme-light tbody tr{border-bottom-color:#e6e3e1}
body.theme-light tbody tr:hover{background:color-mix(in srgb, var(--blue) 6%, var(--panel))}
body.theme-light .panel{
  box-shadow:0 1px 3px rgba(15,23,42,.06);
}
body.theme-light .panel-hdr{
  background:var(--panel2);
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
body.theme-light .aplist{background:var(--panel)}
body.theme-light .aprow{border-bottom-color:#ece8e6}
body.theme-light .aprow:hover{background:color-mix(in srgb, var(--blue) 5%, var(--panel))}
body.theme-light .aprow.hd{background:var(--panel2);color:var(--dim)}
body.theme-light .aprow .vendor{color:var(--txt)}
body.theme-light .adv-input{
  background:var(--panel2);color:var(--txt);border-color:var(--border);
}
body.theme-light .adv-row.focus-pulse{
  border-color:color-mix(in srgb, var(--blue) 45%, var(--border));
  box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 18%, transparent);
}
body.theme-light .adv-note code{color:var(--txt)}
body.theme-light .cfg-editor{
  background:var(--panel2);color:var(--txt);border-color:var(--border);
}
body.theme-light .btn-mini{
  border-color:var(--border);
  background:var(--panel2);
  color:var(--txt);
}
body.theme-light .btn-mini:hover{
  background:color-mix(in srgb, var(--blue) 8%, var(--panel2));
  border-color:var(--blue);
  box-shadow:0 2px 8px var(--glow);
}
body.theme-light .btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 40%, var(--border));color:var(--warn)}
body.theme-light .btn-mini.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--panel2))}
body.theme-light .icon-btn{
  border-color:var(--border);background:var(--panel2);color:var(--dim);
}
body.theme-light .icon-btn:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));color:var(--txt)}
body.theme-light .icon-btn.done{border-color:color-mix(in srgb, var(--green) 38%, var(--border));color:#0f7a3b}
body.theme-light .sn-badge{border-color:color-mix(in srgb, var(--yellow) 35%, var(--border));background:color-mix(in srgb, var(--yellow) 12%, var(--panel2));color:#7b5b00}
body.theme-light .sn-badge.firmware-new{border-color:rgba(21,128,61,.38);background:rgba(21,128,61,.09);color:#166534}
body.theme-light .sn-badge.firmware-old{border-color:color-mix(in srgb, var(--blue) 30%, var(--border));background:color-mix(in srgb, var(--blue) 8%, var(--panel2));color:#1f4e79}
body.theme-light .sn-badge.alarm{border-color:rgba(209,52,56,.55);background:rgba(209,52,56,.10);color:#a4262c}
body.theme-light tbody td.hl{
  background-color:rgba(250,213,97,calc(var(--hl-alpha,.0) * .52));
}
body.theme-light tbody tr.selected{background:color-mix(in srgb, var(--blue) 10%, var(--panel))}
body.theme-light .map-mini-list{
  border-color:var(--border);background:rgba(255,255,255,.96);
}
body.theme-light .map-mini-list .mini-title{color:var(--dim)}
body.theme-light .info-modal{background:rgba(15,23,42,.24)}
body.theme-light .info-card{
  border-color:var(--border);
  background:var(--panel);
  box-shadow:0 16px 28px rgba(15,23,42,.12);
}
body.theme-light .info-card-hd{
  color:var(--txt);border-bottom-color:var(--border);
}
body.theme-light .info-card-close{
  border-color:var(--border);background:var(--panel2);color:var(--dim);
}
body.theme-light .info-card-close:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));color:var(--txt)}
body.theme-light .info-card-body{color:var(--txt)}
body.theme-light .info-row .k{color:var(--dim)}
body.theme-light .raw-title{color:var(--txt)}
body.theme-light .raw-meta{color:var(--dim)}
body.theme-light .raw-code{
  border-color:var(--border);background:var(--panel2);color:var(--txt);
}
body.theme-light .raw-empty{color:var(--dim)}
body.theme-light .sniff-banner{
  border-color:color-mix(in srgb, var(--warn) 40%, var(--border));
  background:color-mix(in srgb, var(--warn) 10%, var(--panel));
  color:#9f2a2a;
}
body.theme-light .sniff-banner.warn{
  border-color:color-mix(in srgb, var(--yellow) 35%, var(--border));
  background:color-mix(in srgb, var(--yellow) 12%, var(--panel));
  color:#8a6800;
}
body.theme-light .banner{border-color:var(--border);background:rgba(255,255,255,.97);color:var(--txt)}
body.theme-light .banner.ok{border-color:color-mix(in srgb, var(--green) 38%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel));color:#14532d}
body.theme-light .banner.warn{border-color:color-mix(in srgb, var(--yellow) 34%, var(--border));background:color-mix(in srgb, var(--yellow) 12%, var(--panel));color:#7c2d12}
 
footer{text-align:center;padding:8px 10px;font-size:12px;color:#5b6470}
</style>
</head><body>
<header>
  <h1>✈ Light RID Scanner</h1><code class="app-version-label">__APP_VERSION_LABEL__</code>
  <div class="head-stats">
  <span class="stat">在线 <b id="n-live">-</b></span>
  <span class="stat ls">离线 <b id="n-lost">-</b></span>
  <span class="stat cs">信道 <b id="cur-ch">-</b></span>
  <span class="stat ts">更新 <b id="cur-ts">-</b></span>
  <span class="stat"><span id="dot-ws"></span><span id="ws-status">连接中</span></span>
  <button class="btn-mini" id="btn-clear-history" type="button">清空历史</button>
  </div>
</header>

<div class="tbl-wrap">
<table id="dtable">
<thead><tr>
  <th><div class="sel-wrap"><input id="sel-all" class="sel-sn" type="checkbox" title="全选"></div></th><th>#</th><th>SN</th><th>机型</th><th>信号</th><th>包</th><th>方向</th><th>数据更新</th><th>末次发现</th><th>UAS ID</th>
</tr></thead>
<tbody id="tbody"></tbody>
</table>
</div>

<div class="bottom">
  <div class="panel">
    <div class="panel-hdr">
      🗺 地图
      <span class="sub" id="map-hint">等待坐标...</span>
    </div>
    <div id="map"></div>
  </div>
  <div class="panel">
    <div class="panel-hdr">
      📡 AP 扫描日志
      <label><input type="checkbox" id="autoscroll" checked>自动滚动</label>
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
var deleteHistorySnBusy = {};
var restartBusy = false;
var metaState = {};
var uiFrozen = false;
var frozenPendingData = null;
var homeFreezeAfterFirstRender = false;
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
var selectedMacSet = {};
var historyHiddenSnSet = {};
var zoneAlarmSnSet = {};
var autoTrackSnSet = {};
var rowClickTimer = null;
var trackCache = {};
var trackLoading = {};
var trackFetchMeta = {};
var prefRealtimeTrack = true;
var prefTrack2hOnly = false;
var COOKIE_TRACK_REALTIME = 'rid_realtime_track';
var COOKIE_TRACK_2H_ONLY = 'rid_track_2h_only';
var FREEZE_ON_HOME_KEY = 'rid_freeze_on_home_once';
var NEW_FIRMWARE_PARSE_KEY = 'rid_new_firmware_parse_enabled';
var LIVE_TRACK_WINDOW_SEC = 300;
var LIVE_LOST_WINDOW_SEC = 120;
var AUTO_TRACK_OFFLINE_HIDE_SEC = LIVE_TRACK_WINDOW_SEC;
var TRACK_FILTER_WINDOW_SEC = 7200;
var TRACK_LIVE_FETCH_LIMIT = 600;
var TRACK_HISTORY_FETCH_LIMIT = 4000;
var TRACK_FORCE_RELOAD_MS = 8000;
var notificationItems = [];
var notificationSeq = 0;
var notificationSyncBusy = false;
var notificationPollTimer = null;
var authRedirecting = false;
var replaySyncPaused = false;
var replayState = {sn:null,min:null,max:null,start:null,end:null,cursor:null,playing:false,speed:1,timer:null,userRange:false};
var replayMarkers = {};
var replayUiSig = '';
var REPLAY_GAP_SKIP_SEC = 10;
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
var mapLastUserInputTs = 0;
var mapHeadingRefDeg = 0;
var mapAutoCenterIdleSec = 20;

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
function normDeg(v){
  var d = Number(v);
  if(!isFinite(d)) return 0;
  d = d % 360;
  if(d < 0) d += 360;
  return d;
}
function headingDeltaDeg(nowDeg, refDeg){
  var a = normDeg(nowDeg);
  var b = normDeg(refDeg);
  var d = a - b;
  if(d > 180) d -= 360;
  if(d < -180) d += 360;
  return d;
}
function mapAutoState(){
  var cd = Number(mapAutoCenterIdleSec);
  if(!isFinite(cd) || cd < 5) cd = 20;
  if(!mapLastUserInputTs) return {allow:true, remain:0};
  var now = Date.now() / 1000;
  var elapsed = now - Number(mapLastUserInputTs);
  if(elapsed >= cd) return {allow:true, remain:0};
  return {allow:false, remain:Math.max(0, cd - elapsed)};
}
function markMapUserInteracted(){
  mapLastUserInputTs = Date.now() / 1000;
  if(map) map._rid_user_moved = true;
}
function cookieGet(name){
  var key = String(name || '').trim();
  if(!key) return null;
  var parts = String(document.cookie || '').split(';');
  for(var i=0;i<parts.length;i++){
    var p = String(parts[i] || '').trim();
    if(!p) continue;
    var pos = p.indexOf('=');
    var k = (pos < 0) ? p : p.slice(0, pos).trim();
    if(k !== key) continue;
    var raw = (pos < 0) ? '' : p.slice(pos + 1);
    try{ return decodeURIComponent(raw); }catch(_e){ return raw; }
  }
  return null;
}
function cookieSet(name, value, days){
  var key = String(name || '').trim();
  if(!key) return;
  var val = encodeURIComponent(String(value == null ? '' : value));
  var nDays = Number(days);
  if(!isFinite(nDays) || nDays <= 0) nDays = 365;
  var secure = (location.protocol === 'https:') ? '; Secure' : '';
  document.cookie = key + '=' + val + '; Max-Age=' + Math.round(nDays * 86400) + '; Path=/; SameSite=Lax' + secure;
}
function cookieBool(name, defVal){
  var v = cookieGet(name);
  if(v == null || v === '') return !!defVal;
  v = String(v).toLowerCase();
  return (v === '1' || v === 'true' || v === 'on' || v === 'yes');
}
function loadTrackPrefs(){
  prefRealtimeTrack = cookieBool(COOKIE_TRACK_REALTIME, true);
  prefTrack2hOnly = cookieBool(COOKIE_TRACK_2H_ONLY, false);
  saveTrackPrefs();
}
function saveTrackPrefs(){
  cookieSet(COOKIE_TRACK_REALTIME, prefRealtimeTrack ? '1' : '0', 365);
  cookieSet(COOKIE_TRACK_2H_ONLY, prefTrack2hOnly ? '1' : '0', 365);
}
function syncTrackPrefsUi(){
  var rt = qs('opt-realtime-track');
  if(rt) rt.checked = !!prefRealtimeTrack;
  var f2h = qs('opt-track-2h');
  if(f2h) f2h.checked = !!prefTrack2hOnly;
}
function consumeFreezeOnHomeRequest(){
  try{
    homeFreezeAfterFirstRender = (localStorage.getItem(FREEZE_ON_HOME_KEY) === '1');
  }catch(_e){
    homeFreezeAfterFirstRender = false;
  }
}
function refreshAutoTrackSelection(rows){
  autoTrackSnSet = {};
  if(!prefRealtimeTrack) return;
  var arr = Array.isArray(rows) ? rows : [];
  for(var i=0;i<arr.length;i++){
    var e = arr[i] || {};
    var sn = String(e.sn || '');
    if(!sn || e.archived) continue;
    var age = Number(e.age || 0);
    if(!isFinite(age) || age < 0) age = 0;
    if(age >= AUTO_TRACK_OFFLINE_HIDE_SEC) continue;
    autoTrackSnSet[sn] = true;
  }
}
function effectiveTrackSnList(){
  var out = {};
  var sel = selectedSnList();
  for(var i=0;i<sel.length;i++){
    out[String(sel[i] || '')] = true;
  }
  if(prefRealtimeTrack){
    Object.keys(autoTrackSnSet).forEach(function(sn){
      if(sn) out[sn] = true;
    });
  }
  return Object.keys(out).filter(function(sn){ return !!sn; });
}
function historyVisibleSnList(rows){
  var out = [];
  (Array.isArray(rows) ? rows : []).forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn || historyHiddenSnSet[sn]) return;
    out.push(sn);
  });
  return out;
}
function displayTrackSnList(page, rows){
  if(page === 'history'){
    var focus = replayFocusSn();
    if(focus) return [focus];
    return historyVisibleSnList(rows);
  }
  return effectiveTrackSnList();
}
function replayFocusSn(){
  var sn = String((replayState && replayState.sn) || '');
  if(currentAppPage() !== 'history' || !sn || replayState.start == null) return '';
  return sn;
}
function isHistoryTrackVisible(sn){
  sn = String(sn || '');
  return !!sn && !historyHiddenSnSet[sn];
}
function isSnCheckedForCurrentPage(sn){
  return currentAppPage() === 'history' ? isHistoryTrackVisible(sn) : isSnSelected(sn);
}
function _trackTsSec(p){
  var ts = Number((p && p.ts) || 0);
  return (isFinite(ts) && ts > 0) ? ts : null;
}
function filterTrackForDisplay(track, page){
  var arr = Array.isArray(track) ? track.slice() : [];
  if(page === 'live'){
    var liveThreshold = (Date.now() / 1000) - LIVE_TRACK_WINDOW_SEC;
    arr = arr.filter(function(p){
      var ts = _trackTsSec(p);
      return ts == null ? true : (ts >= liveThreshold);
    });
  }else if(prefTrack2hOnly){
    var threshold = (Date.now() / 1000) - TRACK_FILTER_WINDOW_SEC;
    arr = arr.filter(function(p){
      var ts = _trackTsSec(p);
      return ts == null ? true : (ts >= threshold);
    });
  }
  if(page === 'history'){
    arr = filterTrackByReplay(arr);
  }
  return arr;
}
function trackLatLngSignature(latlngs){
  if(!Array.isArray(latlngs) || !latlngs.length) return '0';
  var first = latlngs[0] || {};
  var last = latlngs[latlngs.length - 1] || {};
  function key(p){
    var lat = Array.isArray(p) ? p[0] : p.lat;
    var lng = Array.isArray(p) ? p[1] : p.lng;
    return Number(lat || 0).toFixed(6) + ',' + Number(lng || 0).toFixed(6);
  }
  return String(latlngs.length) + '|' + key(first) + '|' + key(last);
}
function baseFromMeta(meta){
  meta = (meta && typeof meta === 'object') ? meta : {};
  var lat = numOrNull(meta.base_lat);
  var lon = numOrNull(meta.base_lon);
  var zoom = intOrDefault(meta.base_zoom, 13);
  zoom = Math.max(3, Math.min(30, zoom));
  var name = String(meta.base_name || '基站').trim() || '基站';
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
  return (idType === 'SSID') ? 'SSID' : 'RID包';
}
function scanTypeText(e){
  var k = String((e && e.scan_type_key) || '').toLowerCase();
  if(k === 'phone') return '手机快传';
  return 'RID报送';
}
function newFirmwareParseEnabled(){
  try{ return localStorage.getItem(NEW_FIRMWARE_PARSE_KEY) !== '0'; }catch(_e){ return true; }
}
function firmwareTypeKey(e){
  var k = String((e && e.firmware_type_key) || '').toLowerCase();
  if(k === 'new') return 'new';
  if(String((e && e.firmware_type) || '').indexOf('新') >= 0) return 'new';
  return 'old';
}
function firmwareTypeText(e){
  return firmwareTypeKey(e) === 'new' ? '新版固件' : '旧版固件';
}
function uasIdText(e){
  var s = String((e && e.uas_id) || '').trim();
  return s ? s : '-';
}
function includeDroneByFirmware(e){
  if(newFirmwareParseEnabled()) return true;
  return String((e && e.scan_type_key) || '').toLowerCase() === 'phone';
}
function buildInfoHtml(e){
  e = e || {};
  var detailSn = String(e.sn || '');
  var html = '<div class="info-actions">'+
    '<button class="btn-mini export-track-btn" type="button" data-sn="'+escAttr(detailSn)+'">导出轨迹</button>'+
    '<button class="btn-mini warn delete-history-btn" type="button" data-sn="'+escAttr(detailSn)+'">删除历史</button>'+
    '</div><div class="info-grid">';
  html += infoRowHtml('SN', String(e.sn || '-'));
  html += infoRowHtml('UAS ID', uasIdText(e));
  html += infoRowHtml('机型', String(e.model || 'N/A'));
  html += infoRowHtml('在线状态', e.lost ? '离线' : '在线');
  html += infoRowHtml('归档', e.archived ? '是' : '否');
  html += infoRowHtml('MAC', String(e.mac || '-'));
  html += infoRowHtml('SSID', String(e.ssid || '(hidden)'));
  html += infoRowHtml('来源', snSourceText(e));
  html += infoRowHtml('扫描类型', scanTypeText(e));
  html += infoRowHtml('固件', firmwareTypeText(e));
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
function trackFetchUrl(sn){
  var page = currentAppPage();
  var url = '/api/tracks/get?sn=' + encodeURIComponent(sn);
  if(page === 'live'){
    url += '&window=' + encodeURIComponent(String(LIVE_TRACK_WINDOW_SEC));
    url += '&limit=' + encodeURIComponent(String(TRACK_LIVE_FETCH_LIMIT));
  }else{
    if(prefTrack2hOnly){
      url += '&window=' + encodeURIComponent(String(TRACK_FILTER_WINDOW_SEC));
    }
    url += '&limit=' + encodeURIComponent(String(TRACK_HISTORY_FETCH_LIMIT));
  }
  return url;
}
async function ensureTrackLoaded(sn, force){
  sn = String(sn || '');
  if(!sn) return;
  if(trackLoading[sn]) return;
  if(trackCache[sn] && !force) return;
  var nowMs = Date.now();
  var meta = trackFetchMeta[sn] || {};
  if(force && trackCache[sn] && currentAppPage() === 'live' && (nowMs - Number(meta.ts || 0)) < TRACK_FORCE_RELOAD_MS) return;
  trackLoading[sn] = true;
  try{
    var data = await getJson(trackFetchUrl(sn));
    var tr = Array.isArray(data.track) ? data.track : [];
    trackCache[sn] = tr;
    trackFetchMeta[sn] = {ts: Date.now(), count:Number(data.count || tr.length || 0), shown:Number(tr.length || 0)};
    if(isSnSelected(sn) || (prefRealtimeTrack && autoTrackSnSet[sn])){
      updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    }
  }catch(_e){
    if(!trackCache[sn]) trackCache[sn] = [];
  }finally{
    delete trackLoading[sn];
  }
}
function syncSelectedFromRows(rows){
  var arr = Array.isArray(rows) ? rows : [];
  var nextMac = {};
  for(var i=0;i<arr.length;i++){
    var e = arr[i] || {};
    var sn = String(e.sn || '');
    var mac = String(e.mac || e.src_mac || '').toLowerCase();
    if(!sn) continue;
    if(selectedSnSet[sn]){
      if(mac) nextMac[mac] = true;
      continue;
    }
    if(mac && selectedMacSet[mac]){
      selectedSnSet[sn] = true;
      nextMac[mac] = true;
    }
  }
  selectedMacSet = nextMac;
}
function setSnSelected(sn, on){
  sn = String(sn || '');
  if(!sn) return;
  var e = latestDroneMap[sn] || null;
  var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
  if(on){
    selectedSnSet[sn] = true;
    if(mac) selectedMacSet[mac] = true;
  }else{
    delete selectedSnSet[sn];
    if(mac) delete selectedMacSet[mac];
  }
  if(on) ensureTrackLoaded(sn, false);
  syncTableSelectionUi();
  renderLiveCards(latestDroneRows);
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function setHistorySnVisible(sn, on){
  sn = String(sn || '');
  if(!sn) return;
  if(on){
    delete historyHiddenSnSet[sn];
    ensureTrackLoaded(sn, false);
  }else{
    historyHiddenSnSet[sn] = true;
  }
  syncTableSelectionUi();
  renderMapMiniList(latestDroneRows);
  refreshReplayBounds(false);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function setAllVisibleSelected(on){
  if(currentAppPage() === 'history'){
    var hRows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
    hRows.forEach(function(e){
      var sn = String((e && e.sn) || '');
      if(!sn) return;
      if(on){
        delete historyHiddenSnSet[sn];
        ensureTrackLoaded(sn, false);
      }else{
        historyHiddenSnSet[sn] = true;
      }
    });
    syncTableSelectionUi();
    renderMapMiniList(latestDroneRows);
    refreshReplayBounds(false);
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    return;
  }
  var rows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
  rows.forEach(function(e){
    var sn = String((e && e.sn) || '');
    var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
    if(!sn) return;
    if(on){
      selectedSnSet[sn] = true;
      if(mac) selectedMacSet[mac] = true;
      ensureTrackLoaded(sn, false);
    }else{
      delete selectedSnSet[sn];
      if(mac) delete selectedMacSet[mac];
    }
  });
  syncTableSelectionUi();
  renderLiveCards(latestDroneRows);
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
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
function isTypingTarget(el){
  var t = el || document.activeElement;
  if(!t || !t.tagName) return false;
  var tag = String(t.tagName || '').toLowerCase();
  if(tag === 'input' || tag === 'textarea' || tag === 'select') return true;
  return !!t.isContentEditable;
}
function openAdvModal(){
  var m = qs('adv-modal');
  if(m) m.classList.add('show');
}
function closeAdvModal(){
  var m = qs('adv-modal');
  if(m) m.classList.remove('show');
}
function hideInfoCard(){
  var modal = qs('info-modal');
  if(!modal) return;
  modal.classList.remove('show');
}
function stripUnsafeHtml(html){
  var t = document.createElement('template');
  t.innerHTML = String(html || '');
  t.content.querySelectorAll('script,iframe,object,embed,link[rel="import"]').forEach(function(n){ n.remove(); });
  t.content.querySelectorAll('*').forEach(function(n){
    Array.prototype.slice.call(n.attributes || []).forEach(function(a){
      var name = String(a.name || '').toLowerCase();
      var val = String(a.value || '').trim().toLowerCase();
      if(name.indexOf('on') === 0 || name === 'srcdoc' || ((name === 'href' || name === 'src') && val.indexOf('javascript:') === 0)){
        n.removeAttribute(a.name);
      }
    });
  });
  return t.innerHTML;
}
function showInfoCard(msg, asHtml){
  var modal = qs('info-modal');
  var body = qs('info-card-body');
  if(!modal || !body) return;
  if(asHtml){
    body.innerHTML = stripUnsafeHtml(msg);
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
      uas_id: String(e.uas_id || ''),
      rssi: String(e.rssi == null ? '' : e.rssi),
      pkts: String(e.pkts == null ? '' : e.pkts),
      dir: String(e.dir || ''),
      last_seen: String(e.last_seen || ''),
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
function redirectToLogin(){
  if(authRedirecting) return;
  authRedirecting = true;
  try{ if(ws) ws.close(); }catch(_e){}
  location.href = '/login?next=/';
}
function isAuthExpiredResponse(resp, data){
  var status = resp && Number(resp.status || 0);
  var err = String((data && data.error) || '');
  return status === 401 && (!!(data && data.auth_expired) || err === 'login required' || err === 'auth required');
}
function handleAuthExpired(resp, data){
  if(isAuthExpiredResponse(resp, data)){
    redirectToLogin();
    return true;
  }
  return false;
}
function authAwareError(resp, data){
  if(handleAuthExpired(resp, data)){
    var e = new Error('login required');
    e.authRedirect = true;
    return e;
  }
  return null;
}
function showBanner(text, kind, timeoutMs, opts){
  if(!opts || opts.persist !== false){
    addNotificationEntry(text, kind || 'info');
  }
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
function notificationKindLabel(kind){
  kind = String(kind || 'info');
  if(kind === 'ok') return '完成';
  if(kind === 'warn') return '警告';
  return '通知';
}
function normalizeNotificationItems(items){
  return (Array.isArray(items) ? items : []).filter(function(x){ return x && x.text; }).slice(0, 200);
}
async function refreshNotificationCenter(){
  if(notificationSyncBusy) return;
  notificationSyncBusy = true;
  try{
    var data = await getJson('/api/notifications?limit=200');
    notificationItems = normalizeNotificationItems(data.items);
    notificationSeq = Number(data.seq || notificationSeq || 0);
    renderNotificationCenter();
  }catch(e){
    if(!(e && e.authRedirect) && qs('notify-center-sub')){
      qs('notify-center-sub').textContent = '通知同步失败';
    }
  }finally{
    notificationSyncBusy = false;
  }
}
function applyNotificationPayload(data){
  if(data && Array.isArray(data.items)){
    notificationItems = normalizeNotificationItems(data.items);
    notificationSeq = Number(data.seq || notificationSeq || 0);
    renderNotificationCenter();
  }
}
function addNotificationEntry(text, kind){
  var msg = String(text || '').trim();
  if(!msg) return;
  fetch(apiUrl('/api/notifications'), {
    method:'POST',
    cache:'no-store',
    headers:{'Content-Type':'application/json','X-LightRID-Page':'1'},
    body: JSON.stringify({text: msg, kind: String(kind || 'info')})
  }).then(function(resp){
    return resp.json().catch(function(){ return {}; }).then(function(data){
      var authErr = authAwareError(resp, data);
      if(authErr) throw authErr;
      if(resp.ok && data.ok !== false) applyNotificationPayload(data);
    });
  }).catch(function(e){
    if(!(e && e.authRedirect)) refreshNotificationCenter();
  });
}
function fmtNotificationTime(ts){
  var n = Number(ts || 0);
  if(!isFinite(n) || n <= 0) return '-';
  try{ return new Date(n).toLocaleString(); }catch(_e){ return '-'; }
}
function ensureNotificationCenter(){
  if(!qs('notify-center-button')){
    var btn = document.createElement('button');
    btn.id = 'notify-center-button';
    btn.className = 'notify-center-button';
    btn.type = 'button';
    btn.title = '通知中心';
    btn.setAttribute('aria-label', '通知中心');
    btn.innerHTML = '<span class="notify-center-glyph" aria-hidden="true"></span><span id="notify-center-count" class="notify-center-count">0</span>';
    btn.addEventListener('click', function(ev){
      ev.preventDefault();
      toggleNotificationCenter();
    });
    document.body.appendChild(btn);
  }
  if(!qs('notify-center-panel')){
    var panel = document.createElement('aside');
    panel.id = 'notify-center-panel';
    panel.className = 'notify-center-panel';
    panel.setAttribute('aria-label', '通知中心');
    panel.innerHTML =
      '<div class="notify-center-head">'+
      '  <div><div class="notify-center-title">通知中心</div><div id="notify-center-sub" class="notify-center-sub">暂无通知</div></div>'+
      '  <button class="btn-mini" id="notify-center-clear" type="button">清空</button>'+
      '</div>'+
      '<div id="notify-center-list" class="notify-center-list"></div>';
    document.body.appendChild(panel);
    panel.addEventListener('click', function(ev){
      var del = ev.target && ev.target.closest ? ev.target.closest('.notify-item-del[data-id]') : null;
      if(!del) return;
      ev.preventDefault();
      deleteNotificationItem(del.getAttribute('data-id'));
    });
  }
  if(qs('notify-center-clear') && qs('notify-center-clear').getAttribute('data-bound') !== '1'){
    qs('notify-center-clear').setAttribute('data-bound', '1');
    qs('notify-center-clear').addEventListener('click', function(ev){
      ev.preventDefault();
      postJson('/api/notifications/clear', {}).then(applyNotificationPayload).catch(function(e){
        if(!(e && e.authRedirect)) showBanner('清空通知失败: ' + ((e && e.message) ? e.message : e), 'warn', 3200, {persist:false});
      });
    });
  }
  renderNotificationCenter();
  refreshNotificationCenter();
  if(!notificationPollTimer){
    notificationPollTimer = setInterval(refreshNotificationCenter, 5000);
  }
}
function toggleNotificationCenter(force){
  ensureNotificationCenter();
  var panel = qs('notify-center-panel');
  var btn = qs('notify-center-button');
  var show = (typeof force === 'boolean') ? force : !(panel && panel.classList.contains('show'));
  if(panel) panel.classList.toggle('show', show);
  if(btn) btn.classList.toggle('active', show);
}
function deleteNotificationItem(id){
  postJson('/api/notifications/delete', {id: id}).then(applyNotificationPayload).catch(function(e){
    if(!(e && e.authRedirect)) showBanner('删除通知失败: ' + ((e && e.message) ? e.message : e), 'warn', 3200, {persist:false});
  });
}
function renderNotificationCenter(){
  var btn = qs('notify-center-button');
  var count = qs('notify-center-count');
  var sub = qs('notify-center-sub');
  var list = qs('notify-center-list');
  var n = Array.isArray(notificationItems) ? notificationItems.length : 0;
  if(btn) btn.classList.toggle('has-items', n > 0);
  if(count) count.textContent = n > 99 ? '99+' : String(n);
  if(sub) sub.textContent = n ? ('保留 ' + n + ' 条历史通知') : '暂无通知';
  if(!list) return;
  if(!n){
    list.innerHTML = '<div class="notify-center-empty">暂无通知</div>';
    return;
  }
  list.innerHTML = notificationItems.map(function(item){
    item = item || {};
    var id = String(item.id || '');
    var kind = String(item.kind || 'info');
    return '<article class="notify-item '+escAttr(kind)+'">'+
      '<span class="notify-item-bar"></span>'+
      '<div><div class="notify-item-text">'+esc(item.text || '')+'</div>'+
      '<div class="notify-item-time">'+esc(notificationKindLabel(kind))+' · '+esc(fmtNotificationTime(item.ts))+'</div></div>'+
      '<button class="notify-item-del" type="button" data-id="'+escAttr(id)+'" title="删除">×</button>'+
      '</article>';
  }).join('');
}
function notifyBtnText(){
  if(!('Notification' in window)) return '网页通知(不支持)';
  if(webNotifyEnabled && Notification.permission === 'granted') return '网页通知(已开)';
  if(Notification.permission === 'denied') return '网页通知(已拒绝)';
  return '网页通知';
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
        new Notification('Light RID Scanner 通知已启用', {body:'将推送飞机上下线事件'});
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
      var title = isLost ? '飞机下线' : '飞机上线';
      var body = nowLabel + '  ' + sn + '\\n' + String(e.model || 'N/A') + '  ' +
        (e.rssi == null ? 'N/A' : (e.rssi + 'dBm'));
      pushWebNotification(title, body, 'rid-'+sn+'-'+(isLost?'off':'on'));
      showBanner(title + '  ' + sn, isLost ? 'warn' : 'ok', 2600, {persist:false});
    }
    droneStatePrev[sn] = isLost;
  });
  Object.keys(droneStatePrev).forEach(function(sn){
    if(!seen[sn]) delete droneStatePrev[sn];
  });
}
async function getJson(url){
  var resp = await fetch(apiUrl(url), {cache:'no-store', headers:{'X-LightRID-Page':'1'}});
  var data = {};
  try{ data = await resp.json(); }catch(_e){}
  if(!resp.ok || data.ok===false){
    var authErr = authAwareError(resp, data);
    if(authErr) throw authErr;
    throw new Error((data && data.error) ? data.error : ('HTTP '+resp.status));
  }
  return data;
}
function apiUrl(url){
  var u = String(url || '');
  try{
    return new URL(u, window.location.origin).toString();
  }catch(_e){
    return u;
  }
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
    btn.textContent = light ? '深色' : '浅色';
    btn.title = light ? '切换为深色' : '切换为浅色';
  }
}
function toggleTheme(){
  applyTheme(uiTheme === 'light' ? 'dark' : 'light');
}
async function postJson(url, body){
  var resp = await fetch(apiUrl(url), {
    method:'POST',
    headers:{'Content-Type':'application/json','X-LightRID-Page':'1'},
    body: JSON.stringify(body||{})
  });
  var data = {};
  try{ data = await resp.json(); }catch(_e){}
  if(!resp.ok || data.ok===false){
    var authErr = authAwareError(resp, data);
    if(authErr) throw authErr;
    throw new Error((data && data.error) ? data.error : ('HTTP '+resp.status));
  }
  return data;
}

function setToolsStatus(text){
  var st = qs('tools-status');
  if(st) st.textContent = String(text || '-');
}

function _toolStamp(){
  var d = new Date();
  function p2(n){ return String(n).padStart(2, '0'); }
  return d.getFullYear() + p2(d.getMonth()+1) + p2(d.getDate()) + '_' + p2(d.getHours()) + p2(d.getMinutes()) + p2(d.getSeconds());
}

function _downloadJsonFile(name, data){
  var text = JSON.stringify(data, null, 2);
  var blob = new Blob([text], {type:'application/json;charset=utf-8'});
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = String(name || ('rid_export_' + _toolStamp() + '.json'));
  document.body.appendChild(a);
  a.click();
  setTimeout(function(){
    try{ URL.revokeObjectURL(url); }catch(_e){}
    if(a.parentNode) a.parentNode.removeChild(a);
  }, 200);
}

function _readFileText(file){
  return new Promise(function(resolve, reject){
    if(!file){
      reject(new Error('未选择文件'));
      return;
    }
    var fr = new FileReader();
    fr.onload = function(){ resolve(String(fr.result || '')); };
    fr.onerror = function(){ reject(new Error('文件读取失败')); };
    fr.readAsText(file, 'utf-8');
  });
}

function _pickImportFile(id){
  var input = qs(id);
  if(!input) return;
  input.value = '';
  input.click();
}

function _pickToolSn(){
  var sel = qs('track-sn-select');
  var sn = sel ? String(sel.value || '').trim() : '';
  if(sn) return sn;
  var selected = selectedSnList();
  if(selected.length) return String(selected[0] || '');
  return '';
}

async function toolsExportAllDetails(){
  setToolsStatus('导出全部详情中...');
  try{
    var data = await getJson('/api/tools/export/all');
    _downloadJsonFile('rid_details_all_' + _toolStamp() + '.json', data);
    setToolsStatus('导出完成：全部详情 ' + Number(data.count || 0) + ' 架');
    showBanner('已导出全部详情', 'ok', 2200);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导出失败: ' + msg);
    showBanner('导出全部详情失败', 'warn', 3600);
  }
}

async function toolsExportSingleTrack(){
  var sn = _pickToolSn();
  if(!sn){
    setToolsStatus('请先在“历史/轨迹”中选择飞机，或勾选目标飞机');
    showBanner('请先选择飞机再导出轨迹', 'warn', 3200);
    return;
  }
  setToolsStatus('导出轨迹中: ' + sn);
  try{
    var data = await getJson('/api/tools/export/track?sn=' + encodeURIComponent(sn));
    _downloadJsonFile('rid_track_' + sn + '_' + _toolStamp() + '.json', data);
    setToolsStatus('导出完成: ' + sn + ' (' + Number(data.count || 0) + ' 点)');
    showBanner('已导出轨迹: ' + sn, 'ok', 2200);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导出轨迹失败: ' + msg);
    showBanner('导出轨迹失败', 'warn', 3600);
  }
}

async function toolsImportAllDetailsFromFile(file){
  try{
    setToolsStatus('导入全部详情中...');
    var txt = await _readFileText(file);
    var payload = JSON.parse(txt);
    var data = await postJson('/api/tools/import/all', {payload: payload});
    setToolsStatus('导入完成: 新增 ' + Number(data.added || 0) + '，更新 ' + Number(data.updated || 0) + '，跳过 ' + Number(data.skipped || 0));
    showBanner('全部详情导入完成', 'ok', 2400);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导入失败: ' + msg);
    showBanner('导入全部详情失败', 'warn', 4200);
  }
}

async function toolsImportSingleTrackFromFile(file){
  try{
    setToolsStatus('导入单机轨迹中...');
    var txt = await _readFileText(file);
    var obj = JSON.parse(txt);
    var sn = _pickToolSn();
    var payload = null;
    if(Array.isArray(obj)){
      payload = {sn: sn, track: obj};
    }else if(obj && typeof obj === 'object'){
      if(obj.payload && typeof obj.payload === 'object'){
        payload = obj.payload;
      }else{
        payload = obj;
      }
    }else{
      throw new Error('文件格式无效');
    }
    if(!payload || typeof payload !== 'object'){
      throw new Error('文件格式无效');
    }
    if(!payload.sn){
      payload.sn = sn;
    }
    payload.sn = String(payload.sn || '').trim();
    if(!payload.sn){
      throw new Error('文件内无 SN，且当前未选择飞机');
    }
    if(!Array.isArray(payload.track)){
      throw new Error('文件内缺少 track 数组');
    }
    var data = await postJson('/api/tools/import/track', {payload: payload});
    trackCache[payload.sn] = payload.track.slice();
    delete trackFetchMeta[payload.sn];
    delete trackLineSig[payload.sn];
    ensureTrackLoaded(payload.sn, true);
    setToolsStatus('导入完成: ' + payload.sn + ' (' + Number(data.count || 0) + ' 点)');
    showBanner('轨迹导入完成: ' + payload.sn, 'ok', 2400);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导入轨迹失败: ' + msg);
    showBanner('导入单机轨迹失败', 'warn', 4200);
  }
}

async function loadIfaceOptions(force){
  if(ifaceOptionsLoaded && !force) return;
  var sel = qs('iface-select');
  var st = qs('iface-status');
  if(!sel) return;
  try{
    var data = await getJson('/api/interfaces');
    var items = Array.isArray(data.items) ? data.items : [];
    var html = '<option value="">请选择默认网卡</option>';
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
    btn.textContent = uiFrozen ? '恢复同步' : '冻结列表';
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
  if(frozenPendingData && !replaySyncPaused){
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
  if(btn) btn.textContent = collapsed ? '展开' : '收起';
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
  if(btn) btn.textContent = collapsed ? '展开' : '收起';
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
  if(btn) btn.textContent = collapsed ? '展开' : '收起';
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
  var allow = currentAppPage() === 'history';
  btn.style.display = allow ? '' : 'none';
  btn.disabled = !allow;
  if(!allow){
    btn.textContent = '全屏';
    return;
  }
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
  if(currentAppPage() !== 'history'){
    showBanner('实时页不提供地图全屏，请切到历史记录使用。', 'info', 2600);
    return;
  }
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
  var show = currentAppPage() === 'history'
    && (isMapFullscreen() || !!(panel && panel.classList && panel.classList.contains('fullscreen')));
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
  var html = '<div class="mini-title">历史记录 · 选择飞机查看轨迹</div>';
  rows.forEach(function(e, idx){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    var model = String(e.model || 'N/A');
    var checked = isHistoryTrackVisible(sn) ? ' checked' : '';
    var chip = '<span class="track-color-chip" style="--track-color:'+escAttr(trackColorForSn(sn))+';'+(checked ? '' : 'display:none')+'" title="轨迹颜色"></span>';
    html += '<label class="mini-item"><input class="mini-sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+checked+'>'+
      chip+'<span class="mono">#'+(idx+1)+'</span><span class="sn" title="'+esc(sn)+'">'+esc(sn)+'</span><span class="mini-model" title="'+esc(model)+'">'+esc(model)+'</span></label>';
  });
  box.innerHTML = html;
  var cbs = box.querySelectorAll('.mini-sel-sn');
  for(var i=0;i<cbs.length;i++){
    cbs[i].addEventListener('change', function(ev){
      var sn = ev.target.getAttribute('data-sn') || '';
      setHistorySnVisible(sn, !!ev.target.checked);
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
  var page = currentAppPage();
  for(var i=0;i<cbs.length;i++){
    var sn = String(cbs[i].getAttribute('data-sn') || '');
    cbs[i].checked = (page === 'history') ? isHistoryTrackVisible(sn) : isSnSelected(sn);
    var chip = cbs[i].parentNode ? cbs[i].parentNode.querySelector('.track-color-chip') : null;
    if(chip) chip.style.display = cbs[i].checked ? '' : 'none';
    var tr = cbs[i].closest ? cbs[i].closest('tr[data-sn]') : null;
    if(tr) tr.classList.toggle('selected', !!cbs[i].checked);
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

  ensureNotificationCenter();

  if(!qs('info-modal')){
    var modal = document.createElement('div');
    modal.id = 'info-modal';
    modal.className = 'info-modal';
    modal.innerHTML =
      '<div class="info-card" role="dialog" aria-modal="true" aria-label="详情信息">'+
      '  <div class="info-card-hd"><span>详情信息</span><button id="info-card-close" class="info-card-close" type="button" title="关闭">×</button></div>'+
      '  <div id="info-card-body" class="info-card-body"></div>'+
      '</div>';
    document.body.appendChild(modal);
    modal.addEventListener('click', function(ev){
      var btn = ev.target && ev.target.closest ? ev.target.closest('.export-track-btn[data-sn]') : null;
      if(btn){
        ev.preventDefault();
        exportTrackForSn(btn.getAttribute('data-sn') || '');
        return;
      }
      var delBtn = ev.target && ev.target.closest ? ev.target.closest('.delete-history-btn[data-sn]') : null;
      if(delBtn){
        ev.preventDefault();
        deleteHistoryForSn(delBtn.getAttribute('data-sn') || '', {button: delBtn, hideCard: true});
        return;
      }
      if(ev.target === modal) hideInfoCard();
    });
  }
  if(qs('info-card-close')) qs('info-card-close').addEventListener('click', hideInfoCard);
  if(!infoCardEscBound){
    document.addEventListener('keydown', function(ev){
      if(ev && ev.key === 'Escape'){
        hideInfoCard();
        closeAdvModal();
      }
    });
    infoCardEscBound = true;
  }

  var clearBtn = qs('btn-clear-history');
  if(clearBtn && !qs('sniff-state')){
    var sniffStat = document.createElement('span');
    sniffStat.className = 'stat snf';
    sniffStat.innerHTML = '采集 <b id="sniff-state" class="warn">-</b>';
    clearBtn.parentNode.insertBefore(sniffStat, clearBtn);
  }
  if(clearBtn && !qs('btn-theme')){
    var themeBtn = document.createElement('button');
    themeBtn.className = 'btn-mini';
    themeBtn.id = 'btn-theme';
    themeBtn.type = 'button';
    themeBtn.textContent = '浅色';
    clearBtn.parentNode.insertBefore(themeBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-dji-lookup')){
    var djiBtn = document.createElement('button');
    djiBtn.className = 'btn-mini';
    djiBtn.id = 'btn-dji-lookup';
    djiBtn.type = 'button';
    djiBtn.textContent = 'DJI查询';
    clearBtn.parentNode.insertBefore(djiBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-freeze')){
    var freezeBtn = document.createElement('button');
    freezeBtn.className = 'btn-mini';
    freezeBtn.id = 'btn-freeze';
    freezeBtn.type = 'button';
    freezeBtn.textContent = '冻结列表';
    clearBtn.parentNode.insertBefore(freezeBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-web-notify')){
    var notifyBtn = document.createElement('button');
    notifyBtn.className = 'btn-mini';
    notifyBtn.id = 'btn-web-notify';
    notifyBtn.type = 'button';
    notifyBtn.textContent = '网页通知';
    clearBtn.parentNode.insertBefore(notifyBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-hw-assistant')){
    var hwBtn = document.createElement('button');
    hwBtn.className = 'btn-mini';
    hwBtn.id = 'btn-hw-assistant';
    hwBtn.type = 'button';
    hwBtn.textContent = '硬件助手';
    clearBtn.parentNode.insertBefore(hwBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-adv-open')){
    var advBtn = document.createElement('button');
    advBtn.className = 'btn-mini';
    advBtn.id = 'btn-adv-open';
    advBtn.type = 'button';
    advBtn.textContent = '高级设置';
    clearBtn.parentNode.insertBefore(advBtn, clearBtn);
  }

  var header = document.querySelector('header');
  if(header && !qs('security-banner')){
    var secBanner = document.createElement('div');
    secBanner.id = 'security-banner';
    secBanner.className = 'sniff-banner warn security-banner';
    secBanner.style.display = 'none';
    secBanner.innerHTML = '<span id="security-banner-text">当前处于 root 权限，存在安全风险。</span><button class="btn-mini warn" id="btn-security-settings" type="button">去设置修复</button>';
    header.appendChild(secBanner);
  }
  if(qs('btn-security-settings') && qs('btn-security-settings').getAttribute('data-bound') !== '1'){
    qs('btn-security-settings').setAttribute('data-bound', '1');
    qs('btn-security-settings').addEventListener('click', function(ev){
      ev.preventDefault();
      location.href = '/settings';
    });
  }
  if(header && !qs('sniff-banner')){
    var banner = document.createElement('div');
    banner.id = 'sniff-banner';
    banner.className = 'sniff-banner';
    header.appendChild(banner);
  }
  if(!qs('adv-modal')){
    var modal = document.createElement('div');
    modal.className = 'adv-modal';
    modal.id = 'adv-modal';
    modal.innerHTML =
      '<div class="adv-window" role="dialog" aria-modal="true" aria-label="高级设置">'+
      '<div class="adv-window-hd"><span>高级设置</span><button class="btn-mini" id="btn-adv-close" type="button">关闭</button></div>'+
      '<div class="adv-body">'+
      '  <div class="adv-col">'+
      '    <div class="adv-row">'+
      '      <label for="restart-args">参数</label>'+
      '      <input id="restart-args" class="adv-input" type="text" placeholder="例如: --no-tui --channel 6">'+
      '    </div>'+
      '    <div class="adv-row" id="hw-assistant-row">'+
      '      <label for="iface-select">硬件配置助手</label>'+
      '      <select id="iface-select" class="adv-input"><option value="">请选择默认网卡</option></select>'+
      '      <button class="btn-mini" id="btn-iface-refresh" type="button">刷新网卡</button>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label><input id="scan-wifi-fast" type="checkbox"> 扫描WiFi快传(5GHz常见信道)</label>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label><input id="opt-realtime-track" type="checkbox"> 实时轨迹（最近5分钟轨迹）</label>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label><input id="opt-track-2h" type="checkbox"> 自动筛选 2 小时内轨迹</label>'+
      '    </div>'+
      '    <div class="adv-note">轨迹偏好已保存到 Cookie</div>'+
      '    <div class="adv-row">'+
      '      <label for="base-name">基站名称</label>'+
      '      <input id="base-name" class="adv-input" type="text" placeholder="例如: 基站A">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-lat">基站纬度</label>'+
      '      <input id="base-lat" class="adv-input" type="text" inputmode="decimal" placeholder="例如: 30.0678192">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-lon">基站经度</label>'+
      '      <input id="base-lon" class="adv-input" type="text" inputmode="decimal" placeholder="例如: 121.1854406">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-zoom">基站缩放</label>'+
      '      <input id="base-zoom" class="adv-input" type="number" min="3" max="30" step="1" placeholder="13">'+
      '      <button class="btn-mini" id="btn-base-save" type="button">保存基站</button>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="heading-ref">参考航向(°)</label>'+
      '      <input id="heading-ref" class="adv-input" type="number" min="0" max="359.99" step="0.1" placeholder="0">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="map-idle-sec">自动回中冷却(s)</label>'+
      '      <input id="map-idle-sec" class="adv-input" type="number" min="5" max="600" step="1" placeholder="20">'+
      '    </div>'+
      '    <div class="adv-note" id="base-status">-</div>'+
      '    <div class="adv-note" id="iface-status">-</div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-save-iface-default" type="button">保存默认网卡</button>'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-restart-once" type="button">仅本次重启</button>'+
      '      <button class="btn-mini warn" id="btn-restart-save" type="button">保存并重启</button>'+
      '    </div>'+
      '    <div class="adv-note">DJI地址: <code id="dji-url-text">-</code></div>'+
      '    <div class="adv-note">当前参数: <code id="restart-current-args">-</code></div>'+
      '    <div class="adv-note">已保存参数: <code id="restart-saved-args">-</code></div>'+
      '  </div>'+
      '  <div class="adv-col">'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-config-load" type="button">读取配置</button>'+
      '      <button class="btn-mini" id="btn-config-save" type="button">保存并热重载</button>'+
      '    </div>'+
      '    <div class="adv-note" id="config-editor-status">-</div>'+
      '    <textarea id="config-editor" class="cfg-editor" spellcheck="false" placeholder="在这里编辑 rid_config.json"></textarea>'+
      '    <div class="adv-row">'+
      '      <label for="track-sn-select">历史/轨迹</label>'+
      '      <select id="track-sn-select" class="adv-input"><option value="">请选择飞机</option></select>'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini warn" id="btn-history-delete" type="button">删除该飞机</button>'+
      '      <button class="btn-mini" id="btn-track-clear-one" type="button">清空该机轨迹</button>'+
      '      <button class="btn-mini warn" id="btn-track-clear-all" type="button">清空全部轨迹</button>'+
      '    </div>'+
      '    <div class="adv-note">TOOLS</div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-tools-export-all" type="button">导出全部详情</button>'+
      '      <button class="btn-mini" id="btn-tools-import-all" type="button">导入全部详情</button>'+
      '      <input id="tools-import-all-file" type="file" accept=".json,application/json" style="display:none">'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-tools-export-track" type="button">导出单机轨迹</button>'+
      '      <button class="btn-mini" id="btn-tools-import-track" type="button">导入单机轨迹</button>'+
      '      <input id="tools-import-track-file" type="file" accept=".json,application/json" style="display:none">'+
      '    </div>'+
      '    <div class="adv-note" id="tools-status">-</div>'+
      '    <div class="adv-note" id="track-mgr-status">-</div>'+
      '  </div>'+
      '</div></div>';
    document.body.appendChild(modal);
    modal.addEventListener('click', function(ev){
      if(ev.target === modal) closeAdvModal();
    });
  }

  var bottom = document.querySelector('.bottom');
  if(bottom && !qs('aplist')){
    var panel = document.createElement('div');
    panel.className = 'panel ap-panel';
    panel.innerHTML =
      '<div class="panel-hdr">📋 实时AP列表 <span class="sub" id="ap-list-count">0</span></div>'+
      '<div class="aplist" id="aplist"></div>';
    bottom.appendChild(panel);
  }
  if(!qs('bottom-restore')){
    var restoreBtn = document.createElement('button');
    restoreBtn.className = 'btn-mini';
    restoreBtn.id = 'bottom-restore';
    restoreBtn.type = 'button';
    restoreBtn.textContent = '展开底部面板';
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
  if(qs('btn-hw-assistant')) qs('btn-hw-assistant').addEventListener('click', openHardwareAssistant);
  if(qs('btn-adv-open')) qs('btn-adv-open').addEventListener('click', openAdvModal);
  if(qs('btn-adv-close')) qs('btn-adv-close').addEventListener('click', closeAdvModal);
  if(qs('btn-restart-once')) qs('btn-restart-once').addEventListener('click', function(){ restartProgram(false); });
  if(qs('btn-restart-save')) qs('btn-restart-save').addEventListener('click', function(){ restartProgram(true); });
  if(qs('btn-config-load')) qs('btn-config-load').addEventListener('click', loadConfigEditor);
  if(qs('btn-config-save')) qs('btn-config-save').addEventListener('click', saveConfigEditor);
  if(qs('btn-history-delete')) qs('btn-history-delete').addEventListener('click', deleteHistoryBySelect);
  if(qs('btn-track-clear-one')) qs('btn-track-clear-one').addEventListener('click', clearTrackBySelect);
  if(qs('btn-track-clear-all')) qs('btn-track-clear-all').addEventListener('click', clearTrackAll);
  if(qs('btn-tools-export-all')) qs('btn-tools-export-all').addEventListener('click', toolsExportAllDetails);
  if(qs('btn-tools-import-all')) qs('btn-tools-import-all').addEventListener('click', function(){ _pickImportFile('tools-import-all-file'); });
  if(qs('btn-tools-export-track')) qs('btn-tools-export-track').addEventListener('click', toolsExportSingleTrack);
  if(qs('btn-tools-import-track')) qs('btn-tools-import-track').addEventListener('click', function(){ _pickImportFile('tools-import-track-file'); });
  if(qs('tools-import-all-file')) qs('tools-import-all-file').addEventListener('change', function(ev){
    var f = (ev && ev.target && ev.target.files && ev.target.files[0]) ? ev.target.files[0] : null;
    if(f) toolsImportAllDetailsFromFile(f);
  });
  if(qs('tools-import-track-file')) qs('tools-import-track-file').addEventListener('change', function(ev){
    var f = (ev && ev.target && ev.target.files && ev.target.files[0]) ? ev.target.files[0] : null;
    if(f) toolsImportSingleTrackFromFile(f);
  });
  if(qs('btn-iface-refresh')) qs('btn-iface-refresh').addEventListener('click', function(){ loadIfaceOptions(true); });
  if(qs('btn-save-iface-default')) qs('btn-save-iface-default').addEventListener('click', saveDefaultIfaceConfig);
  if(qs('iface-select')) qs('iface-select').addEventListener('change', function(){ this.dataset.edited='1'; });
  if(qs('scan-wifi-fast')) qs('scan-wifi-fast').addEventListener('change', function(){ this.dataset.edited='1'; });
  if(qs('opt-realtime-track')) qs('opt-realtime-track').addEventListener('change', function(ev){
    prefRealtimeTrack = !!(ev && ev.target && ev.target.checked);
    saveTrackPrefs();
    refreshAutoTrackSelection(latestDroneRows);
    effectiveTrackSnList().forEach(function(sn){ ensureTrackLoaded(sn, false); });
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  });
  if(qs('opt-track-2h')) qs('opt-track-2h').addEventListener('change', function(ev){
    prefTrack2hOnly = !!(ev && ev.target && ev.target.checked);
    saveTrackPrefs();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  });
  if(qs('restart-args')) qs('restart-args').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-name')) qs('base-name').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-lat')) qs('base-lat').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-lon')) qs('base-lon').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-zoom')) qs('base-zoom').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('heading-ref')) qs('heading-ref').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('map-idle-sec')) qs('map-idle-sec').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('btn-base-save')) qs('btn-base-save').addEventListener('click', saveBaseConfig);
  if(qs('sel-all')) qs('sel-all').addEventListener('change', function(ev){ setAllVisibleSelected(!!(ev && ev.target && ev.target.checked)); });
  if(qs('tbody')) qs('tbody').addEventListener('click', function(ev){
    var cb = ev.target && ev.target.closest ? ev.target.closest('.sel-sn') : null;
    if(cb){
      ev.stopPropagation();
      var snCb = cb.getAttribute('data-sn') || '';
      if(currentAppPage() === 'history') setHistorySnVisible(snCb, !!cb.checked);
      else setSnSelected(snCb, !!cb.checked);
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
      if(rowClickTimer){
        clearTimeout(rowClickTimer);
        rowClickTimer = null;
      }
      rowClickTimer = setTimeout(function(){
        rowClickTimer = null;
        var e = latestDroneMap[sn];
        if(e) showInfoCard(buildInfoHtml(e), true);
      }, 220);
    }
  });
  if(qs('tbody')) qs('tbody').addEventListener('dblclick', function(ev){
    var cb = ev.target && ev.target.closest ? ev.target.closest('.sel-sn') : null;
    if(cb) return;
    var btn = ev.target && ev.target.closest ? ev.target.closest('.copy-sn') : null;
    if(btn) return;
    var tr = ev.target && ev.target.closest ? ev.target.closest('tr[data-sn]') : null;
    if(!tr) return;
    var sn = tr.getAttribute('data-sn') || '';
    if(!sn) return;
    ev.preventDefault();
    ev.stopPropagation();
    if(rowClickTimer){
      clearTimeout(rowClickTimer);
      rowClickTimer = null;
    }
    setSnSelected(sn, true);
    hideInfoCard();
    if(typeof window.__ridNavSet === 'function'){
      window.__ridNavSet('history');
    }else{
      document.body.setAttribute('data-page', 'history');
      setTimeout(function(){ if(map) map.invalidateSize(false); }, 80);
    }
  });
  applyTheme(uiTheme);
  if(('Notification' in window) && Notification.permission === 'granted'){
    webNotifyEnabled = true;
  }
  updateNotifyButton();
  loadConfigEditor();
  loadIfaceOptions(false);
  syncTrackPrefsUi();
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
    baseNameInput.value = String(metaState.base_name || '基站');
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
    baseZoomInput.value = String(Math.max(3, Math.min(30, bz)));
  }
  var headingRefInput = qs('heading-ref');
  if(headingRefInput && !headingRefInput.dataset.edited){
    var hr = Number(metaState.heading_ref_deg);
    if(!isFinite(hr)) hr = 0;
    headingRefInput.value = String(normDeg(hr).toFixed(1));
  }
  var mapIdleInput = qs('map-idle-sec');
  if(mapIdleInput && !mapIdleInput.dataset.edited){
    var mi = intOrDefault(metaState.map_auto_center_idle_sec, 20);
    mapIdleInput.value = String(Math.max(5, Math.min(600, mi)));
  }
  mapHeadingRefDeg = normDeg(metaState.heading_ref_deg);
  mapAutoCenterIdleSec = Math.max(5, Math.min(600, intOrDefault(metaState.map_auto_center_idle_sec, 20)));
  var baseCfg = baseFromMeta(metaState);
  var baseStatus = qs('base-status');
  if(baseStatus){
    if(baseCfg.ok){
      baseStatus.textContent = '基站: ' + baseCfg.name + ' (' + baseCfg.lat.toFixed(6) + ', ' + baseCfg.lon.toFixed(6) + ') z' + baseCfg.zoom + ' | 参考航向 ' + mapHeadingRefDeg.toFixed(1) + '° | 回中冷却 ' + mapAutoCenterIdleSec + 's';
    } else {
      baseStatus.textContent = '基站未配置 | 参考航向 ' + mapHeadingRefDeg.toFixed(1) + '° | 回中冷却 ' + mapAutoCenterIdleSec + 's';
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
    var statText = '当前采集网卡: ' + activeIface + extra;
    if((activeIface === '-' || activeIface === '') && String(metaState.sniff_state || '') !== 'ok'){
      statText += ' | 请打开“高级设置 - 硬件配置助手”检查网卡';
    }
    ifaceStatus.textContent = statText;
  }
  if(!!metaState.scan_wifi_fast && metaState.wifi_fast_supported === false){
    var warnMsg = String(metaState.wifi_fast_msg || '网卡不支持5GHz，WiFi快传扫描不可用');
    if(applyMeta.__fastWarn !== warnMsg){
      showBanner(warnMsg, 'warn', 4200);
      applyMeta.__fastWarn = warnMsg;
    }
  }
  applyRuntimeSecurity(metaState);
  updateNotifyButton();
  applySniffStatus(metaState);
}

function applyRuntimeSecurity(meta){
  var sec = (meta && meta.runtime_security) || {};
  var banner = qs('security-banner');
  if(!banner) return;
  if(sec.running_as_root){
    if(qs('security-banner-text')){
      qs('security-banner-text').textContent = '当前处于 root 权限，存在安全风险。请在设置中一键修复为 rid 专用账号运行。';
    }
    banner.className = 'sniff-banner warn security-banner';
    banner.style.display = 'flex';
    if(applyRuntimeSecurity.__last !== 'root'){
      showBanner('当前处于 root 权限，存在安全风险。', 'warn', 5200);
    }
    applyRuntimeSecurity.__last = 'root';
  }else{
    banner.style.display = 'none';
    applyRuntimeSecurity.__last = 'ok';
  }
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
      badge.textContent = '正常';
    } else if(state === 'error'){
      badge.classList.add('err');
      badge.textContent = '异常';
    } else {
      badge.classList.add('warn');
      badge.textContent = '警告';
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
  var tip = (state === 'error' ? '采集异常：' : '采集告警：') + (msg || '未知');
  if(iface) tip += ' [iface: '+iface+']';
  if(idle > 0) tip += ' (' + Math.round(idle) + 's)';
  if(lastPkt && lastPkt !== '-') tip += '  上次帧: ' + lastPkt;
  banner.textContent = tip;
  banner.className = 'sniff-banner ' + (state === 'error' ? 'error' : 'warn');
  banner.style.display = 'block';
  if(state !== sniffBannerPrevState){
    showBanner(tip, state === 'error' ? 'warn' : 'info', 4200);
    sniffBannerPrevState = state;
  }
}

function openHardwareAssistant(){
  var mobile = false;
  try { mobile = window.matchMedia('(max-width: 900px)').matches; } catch(_e) {}
  if(mobile){
    window.open('/hardware-assistant', '_blank', 'noopener,noreferrer');
  } else {
    window.open('/hardware-assistant', 'hardware_assistant_window', 'noopener,noreferrer,width=1120,height=860');
  }
}

function openDjiLookup(){
  var url = String(metaState.dji_lookup_url || '');
  if(!url){
    alert('未配置DJI查询地址');
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
    btn.textContent = ok ? '已' : '!';
    setTimeout(function(){ btn.classList.remove('done'); btn.textContent = old; }, 1200);
  }
}

async function clearHistory(){
  if(clearHistoryBusy) return;
  if(!confirm('清空历史无人机记录，并删除本地缓存文件？')) return;
  var btn = qs('btn-clear-history');
  clearHistoryBusy = true;
  if(btn){ btn.disabled = true; btn.textContent = '清空中...'; }
  try{
    var data = await postJson('/api/history/clear', {});
    selectedSnSet = {};
    selectedMacSet = {};
    trackCache = {};
    trackFetchMeta = {};
    trackLineSig = {};
    showBanner('历史已清空' + (typeof data.cleared==='number' ? ('（'+data.cleared+'架）') : ''), 'ok', 2600);
  }catch(e){
    showBanner('清空失败: ' + ((e && e.message) ? e.message : e), 'warn', 4200);
  }finally{
    if(btn){ btn.disabled = false; btn.textContent = '清空历史'; }
    clearHistoryBusy = false;
  }
}

function removeHistorySnClientState(sn){
  sn = String(sn || '').trim();
  if(!sn) return;
  var e = latestDroneMap[sn] || null;
  var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
  delete selectedSnSet[sn];
  if(mac) delete selectedMacSet[mac];
  delete historyHiddenSnSet[sn];
  delete trackCache[sn];
  delete trackLoading[sn];
  delete trackFetchMeta[sn];
  delete trackLineSig[sn];
  if(latestDroneMap) delete latestDroneMap[sn];
  function keepOther(row){
    return String((row && row.sn) || '') !== sn;
  }
  latestDroneRows = (Array.isArray(latestDroneRows) ? latestDroneRows : []).filter(keepOther);
  latestMapRows = (Array.isArray(latestMapRows) ? latestMapRows : []).filter(keepOther);
  syncTableSelectionUi();
  renderLiveCards(latestDroneRows);
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  refreshReplayBounds(false);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}

async function deleteHistoryForSn(sn, opts){
  opts = opts || {};
  sn = String(sn || '').trim();
  if(!sn){
    if(opts.statusEl) opts.statusEl.textContent = '请先选择飞机';
    return false;
  }
  if(deleteHistorySnBusy[sn]) return false;
  if(opts.confirm !== false && !confirm('删除该飞机历史记录？\\n' + sn)) return false;
  var btn = opts.button || null;
  var oldText = btn ? btn.textContent : '';
  deleteHistorySnBusy[sn] = true;
  if(btn){
    btn.disabled = true;
    btn.textContent = '删除中...';
  }
  if(opts.statusEl) opts.statusEl.textContent = '删除中...';
  try{
    var data = await postJson('/api/history/delete', {sn: sn});
    removeHistorySnClientState(sn);
    if(opts.hideCard !== false) hideInfoCard();
    if(opts.statusEl) opts.statusEl.textContent = data.removed ? ('已删除: ' + sn) : ('未找到: ' + sn);
    showBanner(data.removed ? ('已删除历史: ' + sn) : ('未找到历史: ' + sn), data.removed ? 'ok' : 'info', 2600);
    return !!data.removed;
  }catch(e){
    if(opts.statusEl) opts.statusEl.textContent = '删除失败: ' + ((e && e.message) ? e.message : e);
    showBanner('删除历史失败: ' + ((e && e.message) ? e.message : e), 'warn', 4200);
    return false;
  }finally{
    if(btn){
      btn.disabled = false;
      btn.textContent = oldText || '删除历史';
    }
    delete deleteHistorySnBusy[sn];
  }
}

async function deleteHistoryBySelect(){
  var sel = qs('track-sn-select');
  var st = qs('track-mgr-status');
  var sn = sel ? String(sel.value || '').trim() : '';
  await deleteHistoryForSn(sn, {statusEl: st, hideCard: false});
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
    delete trackFetchMeta[sn];
    delete trackLineSig[sn];
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
    trackFetchMeta = {};
    trackLineSig = {};
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
  var tip = saveCfg ? '保存配置并重启程序？' : '按当前输入参数重启程序（仅本次）？';
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
  var headingInput = qs('heading-ref');
  var idleInput = qs('map-idle-sec');
  var name = nameInput ? String(nameInput.value || '').trim() : '';
  var latRaw = latInput ? String(latInput.value || '').trim() : '';
  var lonRaw = lonInput ? String(lonInput.value || '').trim() : '';
  var zoomRaw = zoomInput ? String(zoomInput.value || '').trim() : '';
  var headingRaw = headingInput ? String(headingInput.value || '').trim() : '';
  var idleRaw = idleInput ? String(idleInput.value || '').trim() : '';
  if(!name) name = '基站';

  var lat = (latRaw === '') ? null : numOrNull(latRaw);
  var lon = (lonRaw === '') ? null : numOrNull(lonRaw);
  var zoom = intOrDefault(zoomRaw, 13);
  var headingRef = (headingRaw === '') ? 0 : numOrNull(headingRaw);
  var idleSec = intOrDefault(idleRaw, 20);
  zoom = Math.max(3, Math.min(30, zoom));
  idleSec = Math.max(5, Math.min(600, idleSec));
  if(headingRef == null || !isFinite(Number(headingRef))){
    if(st) st.textContent = '参考航向需为数字';
    return;
  }
  headingRef = normDeg(headingRef);

  if((lat === null) !== (lon === null)){
    if(st) st.textContent = '基站坐标需要同时填写经纬度';
    return;
  }
  if(lat !== null && (lat < -90 || lat > 90)){
    if(st) st.textContent = '纬度范围需在 -90 ~ 90';
    return;
  }
  if(lon !== null && (lon < -180 || lon > 180)){
    if(st) st.textContent = '经度范围需在 -180 ~ 180';
    return;
  }

  if(st) st.textContent = '保存中...';
  if(btn) btn.disabled = true;
  try{
    var data = await postJson('/api/web/base/save', {
      base_name: name,
      base_lat: lat,
      base_lon: lon,
      base_zoom: zoom,
      heading_ref_deg: headingRef,
      map_auto_center_idle_sec: idleSec
    });
    metaState = Object.assign({}, metaState, {
      base_name: data.base_name,
      base_lat: data.base_lat,
      base_lon: data.base_lon,
      base_zoom: data.base_zoom,
      heading_ref_deg: data.heading_ref_deg,
      map_auto_center_idle_sec: data.map_auto_center_idle_sec
    });
    if(nameInput){ delete nameInput.dataset.edited; }
    if(latInput){ delete latInput.dataset.edited; }
    if(lonInput){ delete lonInput.dataset.edited; }
    if(zoomInput){ delete zoomInput.dataset.edited; }
    if(headingInput){ delete headingInput.dataset.edited; }
    if(idleInput){ delete idleInput.dataset.edited; }
    applyMeta(metaState);
    applyBaseMarker(true);
    if(st){
      st.textContent = '基站已保存: ' + String(data.base_name || '基站');
    }
    showBanner('基站配置已保存', 'ok', 2200);
  }catch(e){
    if(st) st.textContent = '保存失败: ' + ((e && e.message) ? e.message : e);
    showBanner('基站保存失败', 'warn', 4200);
  }finally{
    if(btn) btn.disabled = false;
  }
}

async function saveDefaultIfaceConfig(){
  var st = qs('iface-status');
  var btn = qs('btn-save-iface-default');
  var ifaceSel = qs('iface-select');
  var iface = ifaceSel ? String(ifaceSel.value || '').trim() : '';
  var scanFast = !!(qs('scan-wifi-fast') && qs('scan-wifi-fast').checked);
  if(btn) btn.disabled = true;
  if(st) st.textContent = '保存默认网卡中...';
  try{
    var data = await postJson('/api/web/basic/save', {
      iface: iface,
      scan_wifi_fast: scanFast
    });
    metaState = Object.assign({}, metaState, {
      iface_selected: data.iface_selected,
      scan_wifi_fast: data.scan_wifi_fast
    });
    if(ifaceSel){ delete ifaceSel.dataset.edited; }
    var scanFastEl = qs('scan-wifi-fast');
    if(scanFastEl){ delete scanFastEl.dataset.edited; }
    applyMeta(metaState);
    if(st){
      st.textContent = '默认网卡已保存: ' + (data.iface_selected || '未设置') + '，WiFi快传=' + (data.scan_wifi_fast ? '开' : '关');
    }
    showBanner('默认网卡配置已保存', 'ok', 2200);
  }catch(e){
    if(st) st.textContent = '保存失败: ' + ((e && e.message) ? e.message : e);
    showBanner('默认网卡保存失败', 'warn', 3600);
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
    box.innerHTML = '<div class="ap-empty">暂无AP数据</div>';
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
  html += '<div class="aprow hd"><div class="idx">#</div><div>MAC</div><div>信号</div><div>类型</div><div>SSID</div><div>设备</div></div>';
  for(var i=0;i<rows.length;i++){
    var a = rows[i] || {};
    var rssi = (a.rssi==null) ? 'N/A' : (a.rssi+'dBm');
    var mac = String(a.mac || '');
    var ssid = String(a.ssid || '(hidden)');
    var vt = String(a.vendor_type || 'AP');
    var vn = String(a.vendor || '未知');
    if(vn === '加载中' && Number(a.age || 0) >= 10) vn = '未知';
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

function renderLiveCards(list){
  var box = qs('live-card-list');
  if(!box) return;
  var rows = liveRecentRows(list).slice();
  rows.sort(function(a,b){
    var al = !!(a && a.lost), bl = !!(b && b.lost);
    if(al !== bl) return al ? 1 : -1;
    var ar = (a && a.rssi != null) ? Number(a.rssi) : -9999;
    var br = (b && b.rssi != null) ? Number(b.rssi) : -9999;
    return br - ar;
  });
  if(qs('live-card-count')) qs('live-card-count').textContent = String(rows.length);
  if(!rows.length){
    box.innerHTML = '<div class="ap-empty">暂无实时目标</div>';
    return;
  }
  var html = '';
  rows.forEach(function(e, idx){
    e = e || {};
    var sn = String(e.sn || '');
    var selected = isSnSelected(sn);
    var inAlarmZone = !!zoneAlarmSnSet[sn];
    var cls = 'live-card' + (selected ? ' selected' : '') + (e.lost ? ' lost' : '') + (inAlarmZone ? ' alarm-zone' : '');
    var rssi = e.rssi == null ? 'N/A' : (String(e.rssi) + 'dBm');
    var model = String(e.model || 'N/A');
    var latlon = (e.lat == null || e.lon == null) ? 'N/A' : (fmt(e.lat,6,'') + ', ' + fmt(e.lon,6,''));
    var pilot = (e.pilot_lat == null || e.pilot_lon == null) ? 'N/A' : (fmt(e.pilot_lat,6,'') + ', ' + fmt(e.pilot_lon,6,''));
    var alt = fmt(e.alt,1,'m');
    var spd = fmt(e.spd,2,'m/s');
    var heading = String(e.dir || '-');
    var stateCls = e.lost ? 'lost' : 'live';
    var stateTxt = e.lost ? '2分钟内离线' : '在线';
    var firmwareTxt = firmwareTypeText(e);
    var uas = uasIdText(e);
    html += '<article class="'+cls+'" data-sn="'+escAttr(sn)+'">'
      + '<div class="live-card-top">'
      +   '<div class="live-card-title" title="'+esc(model)+'">'+esc(model)+'</div>'
      +   '<div class="live-card-actions">'
      +     '<label class="live-card-pick"><input class="sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+(selected?' checked':'')+'><span>选中</span></label>'
      +     (inAlarmZone ? '<span class="live-card-state alarm">区域告警</span>' : '')
      +     '<span class="live-card-state firmware">'+esc(firmwareTxt)+'</span>'
      +     '<span class="live-card-state '+stateCls+'">'+esc(stateTxt)+'</span>'
      +   '</div>'
      + '</div>'
      + '<div class="live-card-snrow"><span class="label">SN</span><span class="live-card-sntext" title="'+esc(sn)+'">'+esc(sn || '-')+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+escAttr(sn)+'" title="复制 SN">⧉</button></div>'
      + '<div class="live-card-snrow live-card-uasrow"><span class="label">UAS ID</span><span class="live-card-sntext" title="'+esc(uas)+'">'+esc(uas)+'</span><span></span></div>'
      + '<div class="live-card-grid">'
      +   '<div class="live-card-item"><div class="k">经纬度</div><div class="v">'+esc(latlon)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">高度</div><div class="v">'+esc(alt)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">速度</div><div class="v">'+esc(spd)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">航向</div><div class="v">'+esc(heading)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">飞手坐标</div><div class="v">'+esc(pilot)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">信号 / 更新</div><div class="v">'+esc(rssi + ' / ' + String(e.age_text || fmtAge(e.age)))+'</div></div>'
      + '</div>'
      + '<div class="live-card-foot"><span>最后数据包 '+esc(String(e.last_pkt_time || e.capture_time || '-'))+'</span><span>#'+(idx+1)+'</span></div>'
      + '</article>';
  });
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
    if(uiFrozen || replaySyncPaused){
      frozenPendingData = d;
      return;
    }
    onData(d);
  };
}
function setWsState(ok){
  qs('dot-ws').className = ok ? 'on' : '';
  qs('ws-status').textContent = replaySyncPaused ? '重演中' : (ok ? '实时' : '重连中');
}

function onData(d){
  buildExtraUi();
  applyMeta((d && d.meta) || {});
  qs('cur-ts').textContent = d.ts;
  qs('cur-ch').textContent = d.ch;
  var list = (Array.isArray(d.drones) ? d.drones : []).filter(includeDroneByFirmware);
  var live = list.filter(function(x){ return x && !x.lost; }).length;
  qs('n-live').textContent = live;
  qs('n-lost').textContent = list.length - live;
  syncFieldHighlights(list);
  handleDroneNotifications(list);
  latestDroneMap = {};
  latestDroneRows = list.slice();
  syncSelectedFromRows(latestDroneRows);
  refreshAutoTrackSelection(latestDroneRows);
  displayTrackSnList(currentAppPage(), latestDroneRows).forEach(function(sn){ ensureTrackLoaded(sn, false); });

  var rows='';
  var page = currentAppPage();
  if(!list.length){
    rows='<tr><td colspan="10" class="empty">暂无数据</td></tr>';
  } else {
    list.forEach(function(e, idx){
      e = e || {};
      var sn = String(e.sn || '');
      if(sn) latestDroneMap[sn] = e;
      var selected = (page === 'history') ? isHistoryTrackVisible(sn) : isSnSelected(sn);
      var snSrc = snSourceText(e);
      var scanType = scanTypeText(e);
      var firmwareType = firmwareTypeText(e);
      var firmwareKey = firmwareTypeKey(e);
      var uas = uasIdText(e);
      var cls = e.lost ? 'lost' : (sn.indexOf('MAC:')===0 ? 'mac' : 'live');
      if(selected) cls += ' selected';
      if(zoneAlarmSnSet[sn]) cls += ' alarm-zone';
      var snMeta = '<span class="sn-badge">'+esc(snSrc)+'</span><span class="sn-badge">'+esc(scanType)+'</span><span class="sn-badge firmware-'+escAttr(firmwareKey)+'">'+esc(firmwareType)+'</span>'+(zoneAlarmSnSet[sn] ? '<span class="sn-badge alarm">报警</span>' : '');
      var modelCls = fieldCellAttrs(sn, 'model', '');
      var rssiCls = fieldCellAttrs(sn, 'rssi', '');
      var pktCls = fieldCellAttrs(sn, 'pkts', '');
      var dirCls = fieldCellAttrs(sn, 'dir', '');
      var ageCls = fieldCellAttrs(sn, 'age_text', 'mono');
      var lastSeenCls = fieldCellAttrs(sn, 'last_seen', 'mono');
      var uasCls = fieldCellAttrs(sn, 'uas_id', 'mono');
      var checked = selected ? ' checked' : '';
      var chip = '<span class="track-color-chip" style="--track-color:'+escAttr(trackColorForSn(sn))+';'+(selected ? '' : 'display:none')+'" title="轨迹颜色"></span>';
      rows += '<tr class="'+cls+' data-row" data-sn="'+escAttr(sn)+'">'+
        '<td><div class="sel-wrap track-sel-wrap"><input class="sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+checked+'>'+chip+'</div></td>'+
        '<td class="idx-cell">'+(idx+1)+'</td>'+
        '<td><div class="sn-cell">'+snMeta+'<span class="mono">'+esc(sn)+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+escAttr(sn)+'" title="复制SN">⧉</button></div></td>'+
        '<td'+modelCls+'>'+esc(e.model || 'N/A')+'</td>'+
        '<td'+rssiCls+'>'+fmt(e.rssi,0,'dBm')+'</td>'+
        '<td'+pktCls+'>'+esc(e.pkts==null?'0':e.pkts)+'</td>'+
        '<td'+dirCls+'>'+esc(e.dir || '-')+'</td>'+
        '<td'+ageCls+'>'+esc(e.age_text || fmtAge(e.age))+'</td>'+
        '<td'+lastSeenCls+'>'+esc(e.last_seen || '-')+'</td>'+
        '<td'+uasCls+'>'+esc(uas)+'</td>'+
        '</tr>';
    });
  }
  qs('tbody').innerHTML = rows;
  syncTableSelectionUi();
  renderLiveCards(list);
  renderMapMiniList(list);
  refreshTrackMgrOptions(list);
  ensureHighlightAnimation();

  var box = qs('logbox');
  var autoEl = qs('autoscroll');
  var auto = !autoEl || autoEl.checked;
  var logs = Array.isArray(d.logs) ? d.logs : [];
  if(box && (lastLogsSeq !== d.logs_seq || box.childElementCount !== logs.length)){
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
  if(box && auto) box.scrollTop=box.scrollHeight;

  if(lastApsSeq !== d.aps_seq){
    renderAps(d.aps || [], d.aps_total || 0);
    lastApsSeq = d.aps_seq;
  }

  latestMapRows = Array.isArray(d.map_drones) ? d.map_drones : (Array.isArray(d.drones) ? d.drones : []);
  displayTrackSnList(currentAppPage(), latestDroneRows).forEach(function(sn){
    var e = latestDroneMap[sn];
    if(e && Number(e.track_count || 0) !== Number((trackCache[sn] || []).length)){
      var tm = trackFetchMeta[sn] || {};
      if(currentAppPage() === 'history' || (Date.now() - Number(tm.ts || 0)) >= TRACK_FORCE_RELOAD_MS){
        ensureTrackLoaded(sn, true);
      }
    }
  });
  initMap();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}

loadTrackPrefs();
consumeFreezeOnHomeRequest();
applyTheme(loadThemePref());
buildExtraUi();
connect();

var map = null, markers = {}, pilotMarkers = {}, trackLines = {}, trackLineSig = {}, twsLines = {}, baseMarker = null;
var motionState = {};
var COLORS = ['#58a6ff','#3fb950','#d29922','#d2a8ff','#79c0ff','#ff7b72'];
var TRACK_COLORS = ['#1f9dff','#12b886','#ff8f1f','#ff4d6d','#8b5cf6','#06b6d4','#84cc16','#eab308'];
var colorIdx = {};
var LIVE_RECENT_WINDOW_SEC = LIVE_TRACK_WINDOW_SEC;
window.addEventListener('resize', function(){
  if(map) map.invalidateSize(false);
  if(latestApsRows.length){
    renderAps(latestApsRows, latestApsTotal);
  }
});
function currentAppPage(){
  var p = String(document.body.getAttribute('data-page') || 'live');
  return p === 'history' ? 'history' : 'live';
}
function liveRecentRows(rows){
  return (Array.isArray(rows) ? rows : []).filter(function(e){
    if(!e || e.archived) return false;
    var age = Number(e.age || 0);
    if(!isFinite(age) || age < 0) age = 0;
    if(e.lost) return age <= LIVE_LOST_WINDOW_SEC;
    return age <= LIVE_RECENT_WINDOW_SEC;
  });
}

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

function _deg2rad(d){ return d * Math.PI / 180; }
function calcDistanceMeters(lat1, lon1, lat2, lon2){
  var p1 = _deg2rad(lat1), p2 = _deg2rad(lat2);
  var dLat = p2 - p1;
  var dLon = _deg2rad(lon2 - lon1);
  var sa = Math.sin(dLat / 2.0);
  var sb = Math.sin(dLon / 2.0);
  var a = sa * sa + Math.cos(p1) * Math.cos(p2) * sb * sb;
  var c = 2.0 * Math.atan2(Math.sqrt(a), Math.sqrt(Math.max(0, 1.0 - a)));
  return 6371000.0 * c;
}
function calcBearing(lat1, lon1, lat2, lon2){
  var p1 = _deg2rad(lat1), p2 = _deg2rad(lat2);
  var dLon = _deg2rad(lon2 - lon1);
  var y = Math.sin(dLon) * Math.cos(p2);
  var x = Math.cos(p1) * Math.sin(p2) - Math.sin(p1) * Math.cos(p2) * Math.cos(dLon);
  var b = Math.atan2(y, x) * 180 / Math.PI;
  if(!isFinite(b)) return null;
  if(b < 0) b += 360;
  return b;
}
function calcHeadingByLatLon(prevLat, prevLon, curLat, curLon, minMoveMeters){
  var dist = calcDistanceMeters(prevLat, prevLon, curLat, curLon);
  var mm = Number(minMoveMeters);
  if(!isFinite(mm) || mm < 0.1) mm = 2.0;
  if(!isFinite(dist) || dist < mm){
    return {ok:false, heading:null, dist:isFinite(dist)?dist:0};
  }
  var b = calcBearing(prevLat, prevLon, curLat, curLon);
  if(!isFinite(Number(b))){
    return {ok:false, heading:null, dist:dist};
  }
  return {ok:true, heading:normDeg(b), dist:dist};
}
function destinationPoint(lat, lon, bearingDeg, distMeter){
  var R = 6371000.0;
  var br = _deg2rad(bearingDeg);
  var lat1 = _deg2rad(lat), lon1 = _deg2rad(lon);
  var ad = distMeter / R;
  var sinLat1 = Math.sin(lat1), cosLat1 = Math.cos(lat1);
  var sinAd = Math.sin(ad), cosAd = Math.cos(ad);
  var lat2 = Math.asin(sinLat1 * cosAd + cosLat1 * sinAd * Math.cos(br));
  var lon2 = lon1 + Math.atan2(Math.sin(br) * sinAd * cosLat1, cosAd - sinLat1 * Math.sin(lat2));
  return {lat:lat2 * 180/Math.PI, lon:lon2 * 180/Math.PI};
}
function interpLatLng(a, b, t){
  return [
    Number(a[0]) + (Number(b[0]) - Number(a[0])) * t,
    Number(a[1]) + (Number(b[1]) - Number(a[1])) * t
  ];
}
function splitLatLngsByMeters(latlngs, meters){
  var pts = Array.isArray(latlngs) ? latlngs : [];
  var target = Math.max(10, Number(meters || 100));
  if(pts.length < 2) return [];
  var out = [];
  var cur = [pts[0]];
  var prev = pts[0];
  var inSeg = 0;
  for(var i=1;i<pts.length;i++){
    var next = pts[i];
    var remaining = calcDistanceMeters(Number(prev[0]), Number(prev[1]), Number(next[0]), Number(next[1]));
    if(!isFinite(remaining) || remaining <= 0){
      continue;
    }
    while(inSeg + remaining >= target){
      var need = target - inSeg;
      if(need <= 0.001){
        if(cur.length > 1) out.push(cur);
        cur = [prev];
        inSeg = 0;
        continue;
      }
      var frac = Math.max(0, Math.min(1, need / remaining));
      var cut = interpLatLng(prev, next, frac);
      cur.push(cut);
      if(cur.length > 1) out.push(cur);
      cur = [cut];
      prev = cut;
      remaining = calcDistanceMeters(Number(prev[0]), Number(prev[1]), Number(next[0]), Number(next[1]));
      inSeg = 0;
      if(!isFinite(remaining) || remaining <= 0) break;
    }
    cur.push(next);
    inSeg += remaining;
    prev = next;
  }
  if(cur.length > 1) out.push(cur);
  return out;
}
function makeTrackLayer(latlngs, color){
  var group = L.layerGroup();
  var segments = splitLatLngsByMeters(latlngs, 100);
  if(!segments.length) segments = [latlngs];
  segments.forEach(function(seg){
    L.polyline(seg, {
      color: color,
      weight: 4,
      opacity: 0.84,
      dashArray: '8 9',
      lineCap: 'butt',
      lineJoin: 'round'
    }).addTo(group);
  });
  return group;
}

function initMap(){
  if(map) return;
  map = L.map('map', {zoomControl:true, attributionControl:true, maxZoom:30});
  L.tileLayer('https://webrd0{s}.is.autonavi.com/appmaptile?lang=zh_cn&size=1&scale=1&style=8&x={x}&y={y}&z={z}',{
    subdomains:['1','2','3','4'],
    maxZoom:30,
    maxNativeZoom:18,
    attribution:'&copy; 高德地图'
  }).addTo(map);
  var b = baseFromMeta(metaState);
  if(b.ok) map.setView([b.lat, b.lon], b.zoom);
  else map.setView([30, 114], 5);
  map._rid_user_moved = false;
  var mapEl = map.getContainer ? map.getContainer() : null;
  if(mapEl){
    mapEl.addEventListener('wheel', markMapUserInteracted, {passive:true});
    mapEl.addEventListener('pointerdown', markMapUserInteracted, {passive:true});
    mapEl.addEventListener('touchstart', markMapUserInteracted, {passive:true});
  }
  applyBaseMarker(false);
  setTimeout(function(){ if(map) map.invalidateSize(false); }, 0);
}

function baseIcon(){
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="48" height="48" viewBox="0 0 24 24">'
    +'<circle cx="12" cy="12" r="10.6" fill="#2f81f7" fill-opacity="0.92" stroke="#fff" stroke-width="1.1"/>'
    +'<path d="M12 6.3v10.2M9.4 17.1h5.2M10.2 10.8L12 9l1.8 1.8M9.8 8.5c.9-.92 2.05-1.38 3.2-1.38 1.15 0 2.3.46 3.2 1.38M8.3 7c1.32-1.34 3.03-2.01 4.74-2.01 1.71 0 3.42.67 4.74 2.01" stroke="#fff" stroke-linecap="round" stroke-linejoin="round" stroke-width="1.35" fill="none"/>'
    +'<path d="M10.8 16.6l-1.15 2.3M13.2 16.6l1.15 2.3" stroke="#fff" stroke-linecap="round" stroke-width="1.2"/>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[48,48], iconAnchor:[24,24], popupAnchor:[0,-22]
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

function fmtReplayTime(ts){
  var n = Number(ts);
  if(!isFinite(n) || n <= 0) return '-';
  try{
    return new Date(n * 1000).toLocaleString();
  }catch(_e){
    return '-';
  }
}
function replaySliderToTs(val){
  if(replayState.min == null || replayState.max == null) return null;
  var span = Number(replayState.max) - Number(replayState.min);
  if(!isFinite(span) || span <= 0) return Number(replayState.min);
  var v = Math.max(0, Math.min(1000, Number(val || 0)));
  return Number(replayState.min) + span * (v / 1000);
}
function replayTsToSlider(ts){
  if(replayState.min == null || replayState.max == null) return 0;
  var span = Number(replayState.max) - Number(replayState.min);
  if(!isFinite(span) || span <= 0) return 0;
  var v = (Number(ts) - Number(replayState.min)) / span;
  return Math.max(0, Math.min(1000, Math.round(v * 1000)));
}
function ensureTrackReplayCard(){
  var panel = qs('map-panel');
  if(!panel) return null;
  if(!qs('replay-sync-banner')){
    var syncBanner = document.createElement('div');
    syncBanner.id = 'replay-sync-banner';
    syncBanner.className = 'replay-sync-banner';
    syncBanner.innerHTML = '<span class="replay-sync-dot"></span><span id="replay-sync-text">轨迹重演中，同步已暂停</span>';
    panel.appendChild(syncBanner);
  }
  var card = qs('track-replay-card');
  if(card) return card;
  card = document.createElement('aside');
  card.id = 'track-replay-card';
  card.className = 'track-replay-card';
  card.innerHTML =
    '<div class="track-replay-head"><div><div class="track-replay-title">轨迹重放</div><div id="track-replay-count" class="track-replay-sub">-</div></div><button class="btn-mini" id="btn-replay-play" type="button">播放</button></div>'+
    '<select id="replay-sn-select" class="input-mini" aria-label="选择重放目标"><option value="">选择飞机</option></select>'+
    '<div class="track-replay-time" id="track-replay-time">-</div>'+
    '<div class="track-replay-ranges">'+
    '  <input id="replay-progress" type="range" min="0" max="1000" step="1" value="0" aria-label="重放进度">'+
    '</div>'+
    '<div class="track-replay-controls">'+
    '  <button class="btn-mini" id="btn-replay-reset" type="button">起点</button>'+
    '  <label class="track-speed-label"><span>速度</span><input id="replay-speed" type="range" min="1" max="10" step="0.1" value="1" aria-label="重放速度"><span id="replay-speed-value" class="track-speed-value">1.0x</span></label>'+
    '  <button class="btn-mini" id="btn-replay-100x" type="button">100x</button>'+
    '</div>'+
    '<div class="track-replay-status" id="track-replay-status">请选择一架飞机后重放。</div>';
  panel.appendChild(card);
  var progress = qs('replay-progress');
  if(progress) progress.addEventListener('input', onReplayRangeInput);
  var play = qs('btn-replay-play');
  if(play) play.addEventListener('click', function(){ setReplayPlaying(!replayState.playing); });
  var sel = qs('replay-sn-select');
  if(sel) sel.addEventListener('change', function(){
    if(replayState.playing) setReplayPlaying(false);
    replayState.sn = String(sel.value || '') || null;
    refreshReplayBounds(true);
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  });
  var reset = qs('btn-replay-reset');
  if(reset) reset.addEventListener('click', resetReplayRange);
  var speed = qs('replay-speed');
  if(speed) speed.addEventListener('input', function(){
    replayState.speed = Math.max(1, Math.min(10, Number(speed.value || 1)));
    renderReplayCard();
  });
  var speed100 = qs('btn-replay-100x');
  if(speed100) speed100.addEventListener('click', function(){
    replayState.speed = (Number(replayState.speed || 1) === 100) ? Math.max(1, Math.min(10, Number((qs('replay-speed') || {}).value || 1))) : 100;
    renderReplayCard();
  });
  return card;
}
function replayCandidateList(){
  var rows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
  var seen = {};
  var out = [];
  rows.forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn || seen[sn]) return;
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    if(!tr.length) return;
    seen[sn] = true;
    out.push({sn:sn, count:tr.length, label:sn + ' · ' + tr.length + ' 点'});
  });
  out.sort(function(a,b){ return String(a.sn).localeCompare(String(b.sn)); });
  return out;
}
function replaySelectedSn(){
  var candidates = replayCandidateList();
  var set = {};
  candidates.forEach(function(x){ set[String(x.sn)] = true; });
  var cur = String(replayState.sn || '');
  if(cur && set[cur]) return cur;
  var visible = historyVisibleSnList(latestDroneRows).filter(function(sn){ return !!set[String(sn)]; });
  if(visible.length === 1) return String(visible[0]);
  return '';
}
function syncReplaySelect(candidates, selectedSn){
  var sel = qs('replay-sn-select');
  if(!sel) return;
  var prev = sel.value;
  var opts = ['<option value="">选择飞机</option>'];
  (candidates || []).forEach(function(x){
    opts.push('<option value="'+escAttr(x.sn)+'">'+esc(x.label || x.sn)+'</option>');
  });
  var html = opts.join('');
  if(sel.innerHTML !== html) sel.innerHTML = html;
  sel.value = selectedSn || (prev && (candidates || []).some(function(x){ return x.sn === prev; }) ? prev : '');
}
function collectReplayBounds(){
  var candidates = replayCandidateList();
  var sn = replaySelectedSn();
  syncReplaySelect(candidates, sn);
  if(!sn){
    return {sn:null, min:null, max:null, selectedCount:0, candidateCount:candidates.length, count:0};
  }
  replayState.sn = sn;
  var minTs = null;
  var maxTs = null;
  var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
  for(var i=0;i<tr.length;i++){
    var ts = _trackTsSec(tr[i]);
    if(ts == null) continue;
    if(minTs == null || ts < minTs) minTs = ts;
    if(maxTs == null || ts > maxTs) maxTs = ts;
  }
  return {sn:sn, min:minTs, max:maxTs, selectedCount:1, candidateCount:candidates.length, count:tr.length};
}
function refreshReplayBounds(keepRange){
  ensureTrackReplayCard();
  var b = collectReplayBounds();
  replayState.sn = b.sn || null;
  if(b.selectedCount !== 1){
    if(replayState.playing) setReplayPlaying(false);
    else {
      stopReplayTimer();
      setReplaySyncPaused(false);
    }
    replayState.min = replayState.max = replayState.start = replayState.end = replayState.cursor = null;
    replayState.userRange = false;
    renderReplayCard();
    clearReplayMarkers();
    return;
  }
  if(b.min == null || b.max == null || b.max <= b.min){
    if(replayState.playing) setReplayPlaying(false);
    else {
      stopReplayTimer();
      setReplaySyncPaused(false);
    }
    replayState.min = replayState.max = replayState.start = replayState.end = replayState.cursor = null;
    replayState.userRange = false;
    renderReplayCard();
    clearReplayMarkers();
    return;
  }
  replayState.min = b.min;
  replayState.max = b.max;
  replayState.start = b.min;
  replayState.end = b.max;
  if(!keepRange || replayState.cursor == null || replayState.cursor < b.min || replayState.cursor > b.max){
    replayState.cursor = b.min;
  }
  renderReplayCard();
}
function renderReplayCard(){
  var card = ensureTrackReplayCard();
  if(!card) return;
  var page = currentAppPage();
  card.style.display = (page === 'history') ? '' : 'none';
  var candidates = replayCandidateList();
  var selectedSn = replaySelectedSn();
  syncReplaySelect(candidates, selectedSn);
  var count = selectedSn ? 1 : 0;
  var countEl = qs('track-replay-count');
  if(countEl){
    if(selectedSn) countEl.textContent = '重放目标 ' + selectedSn;
    else countEl.textContent = candidates.length ? ('可选 ' + candidates.length + ' 架') : '暂无可重放轨迹';
  }
  var progressEl = qs('replay-progress');
  var hasRange = replayState.min != null && replayState.max != null && replayState.max > replayState.min;
  if(progressEl) progressEl.disabled = !hasRange;
  if(progressEl && hasRange) progressEl.value = String(replayTsToSlider(replayState.cursor == null ? replayState.start : replayState.cursor));
  var play = qs('btn-replay-play');
  if(play){
    play.disabled = !hasRange || !selectedSn;
    play.textContent = replayState.playing ? '暂停' : '播放';
  }
  var reset = qs('btn-replay-reset');
  if(reset) reset.disabled = !hasRange;
  var speed = qs('replay-speed');
  if(speed){
    speed.disabled = !hasRange;
    if(Number(replayState.speed || 1) !== 100){
      speed.value = String(Math.max(1, Math.min(10, Number(replayState.speed || 1))));
    }
  }
  var speedValue = qs('replay-speed-value');
  if(speedValue) speedValue.textContent = (Number(replayState.speed || 1) === 100) ? '100x' : (Number(replayState.speed || 1).toFixed(1) + 'x');
  var speed100 = qs('btn-replay-100x');
  if(speed100){
    speed100.disabled = !hasRange;
    speed100.classList.toggle('warn', Number(replayState.speed || 1) === 100);
  }
  var time = qs('track-replay-time');
  if(time){
    time.textContent = hasRange
      ? ('当前 ' + fmtReplayTime(replayState.cursor == null ? replayState.start : replayState.cursor) + '\\n首包 ' + fmtReplayTime(replayState.start) + '  末包 ' + fmtReplayTime(replayState.end))
      : '暂无可重放轨迹';
  }
  var status = qs('track-replay-status');
  if(status){
    var speedText = speedValue ? speedValue.textContent : ((Number(replayState.speed || 1) === 100) ? '100x' : (Number(replayState.speed || 1).toFixed(1) + 'x'));
    if(!selectedSn) status.textContent = candidates.length ? '选择一架飞机后开始重放，地图会聚焦该目标。' : '当前没有可重放轨迹。';
    else if(!hasRange) status.textContent = '轨迹正在加载或时间点不足。';
    else status.textContent = replayState.playing ? ('正在重演中，新的数据同步已暂停。倍速 ' + speedText + '，超过 ' + REPLAY_GAP_SKIP_SEC + 's 的空白段会自动跳过。') : '点击播放会从第一数据包开始重演。';
  }
  updateReplaySyncUi();
}
function onReplayRangeInput(){
  if(replayState.min == null || replayState.max == null) return;
  var progressEl = qs('replay-progress');
  var curTs = replaySliderToTs(progressEl ? progressEl.value : 0);
  if(curTs == null) return;
  replayState.cursor = Math.max(Number(replayState.start), Math.min(Number(replayState.end), Number(curTs)));
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function resetReplayRange(){
  if(replayState.min == null || replayState.max == null) return;
  replayState.start = replayState.min;
  replayState.end = replayState.max;
  replayState.cursor = replayState.start;
  replayState.userRange = false;
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function nextReplayTrackTsAfter(curTs){
  var sn = String(replayState.sn || '');
  if(!sn) return null;
  var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
  var cur = Number(curTs);
  if(!isFinite(cur)) return null;
  var next = null;
  for(var i=0;i<tr.length;i++){
    var ts = _trackTsSec(tr[i]);
    if(ts == null || ts <= cur + 0.001) continue;
    if(replayState.end != null && ts > Number(replayState.end)) continue;
    if(next == null || ts < next) next = ts;
  }
  return next;
}
function stopReplayTimer(){
  if(replayState.timer){
    clearInterval(replayState.timer);
    replayState.timer = null;
  }
  replayState.playing = false;
}
function updateReplaySyncUi(){
  var panel = qs('map-panel');
  if(panel) panel.classList.toggle('replay-sync-paused', !!replaySyncPaused);
  var txt = qs('replay-sync-text');
  if(txt) txt.textContent = replayState.sn ? ('轨迹重演中，同步已暂停：' + replayState.sn) : '轨迹重演中，同步已暂停';
  if(qs('ws-status')){
    if(replaySyncPaused) qs('ws-status').textContent = '重演中';
    else if(ws && ws.readyState === WebSocket.OPEN) qs('ws-status').textContent = '实时';
  }
}
function setReplaySyncPaused(paused){
  var next = !!paused;
  if(replaySyncPaused === next){
    updateReplaySyncUi();
    return;
  }
  replaySyncPaused = next;
  updateReplaySyncUi();
  if(!replaySyncPaused && !uiFrozen && frozenPendingData){
    var d = frozenPendingData;
    frozenPendingData = null;
    onData(d);
  }
}
function setReplayPlaying(on){
  if(!on){
    stopReplayTimer();
    setReplaySyncPaused(false);
    renderReplayCard();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    return;
  }
  var b = collectReplayBounds();
  if(!b.sn){
    showBanner('请先在轨迹重放卡片中选择一架飞机。', 'warn', 3200);
    renderReplayCard();
    return;
  }
  if(b.min == null || b.max == null || b.max <= b.min){
    showBanner('该飞机轨迹点不足，暂不能重演。', 'warn', 3200);
    renderReplayCard();
    return;
  }
  replayState.sn = b.sn;
  replayState.min = b.min;
  replayState.max = b.max;
  replayState.start = b.min;
  replayState.end = b.max;
  replayState.cursor = b.min;
  if(replayState.start == null || replayState.end == null || replayState.end <= replayState.start) return;
  replayState.playing = true;
  setReplaySyncPaused(true);
  if(replayState.timer) clearInterval(replayState.timer);
  replayState.timer = setInterval(function(){
    var step = 0.25 * Math.max(1, Number(replayState.speed || 1));
    var cur = Number(replayState.cursor || replayState.start);
    var nextCursor = cur + step;
    var nextPointTs = nextReplayTrackTsAfter(cur);
    if(nextPointTs != null && (nextPointTs - cur) > REPLAY_GAP_SKIP_SEC && nextCursor < nextPointTs){
      nextCursor = nextPointTs;
    }
    replayState.cursor = Math.min(Number(replayState.end), nextCursor);
    if(replayState.cursor >= replayState.end){
      stopReplayTimer();
      setReplaySyncPaused(false);
      showBanner('轨迹重演已结束，数据同步已恢复。', 'ok', 2600);
    }
    renderReplayCard();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  }, 250);
  showBanner('轨迹重演开始，新的数据同步已暂停。', 'warn', 3600);
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function replayWindowEnd(){
  if(replayState.playing && replayState.cursor != null) return replayState.cursor;
  return replayState.end;
}
function filterTrackByReplay(track){
  var arr = Array.isArray(track) ? track.slice() : [];
  if(currentAppPage() !== 'history') return arr;
  if(replayState.start == null || replayState.end == null) return arr;
  var start = Number(replayState.start);
  var end = Number(replayWindowEnd());
  if(!isFinite(start) || !isFinite(end) || end < start) return arr;
  return arr.filter(function(p){
    var ts = _trackTsSec(p);
    return ts == null ? true : (ts >= start && ts <= end);
  });
}
function clearReplayMarkers(){
  if(!map) return;
  Object.keys(replayMarkers).forEach(function(sn){
    try{ map.removeLayer(replayMarkers[sn]); }catch(_e){}
    delete replayMarkers[sn];
  });
}
function updateReplayMarkers(){
  if(!map) return;
  if(currentAppPage() !== 'history' || replayState.start == null || replayWindowEnd() == null){
    clearReplayMarkers();
    return;
  }
  var active = {};
  var end = Number(replayWindowEnd());
  var start = Number(replayState.start);
  displayTrackSnList('history', latestDroneRows).forEach(function(sn){
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    var point = null;
    var prevPoint = null;
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var ts = _trackTsSec(p);
      if(ts == null || ts < start || ts > end) continue;
      if(point) prevPoint = point;
      point = p;
    }
    if(!point) return;
    var lat = Number(point.lat), lon = Number(point.lon);
    if(!isFinite(lat) || !isFinite(lon)) return;
    active[sn] = true;
    var pos = toMapLatLng(lat, lon);
    var col = trackColorForSn(sn);
    var heading = null;
    if(prevPoint && isFinite(Number(prevPoint.lat)) && isFinite(Number(prevPoint.lon))){
      var hs = calcHeadingByLatLon(Number(prevPoint.lat), Number(prevPoint.lon), lat, lon, 0.5);
      if(hs.ok) heading = hs.heading;
    }
    var popup = '<b>'+esc(sn)+'</b><br>重放位置<br>'+fmtReplayTime(point.ts);
    var icon = droneIcon(col, false, heading, true, 1, false);
    if(replayMarkers[sn] && replayMarkers[sn].setIcon){
      replayMarkers[sn].setLatLng(pos).setIcon(icon).setPopupContent(popup);
    }else{
      if(replayMarkers[sn]){
        try{ map.removeLayer(replayMarkers[sn]); }catch(_e){}
      }
      replayMarkers[sn] = L.marker(pos, {icon: icon}).addTo(map).bindPopup(popup);
    }
  });
  Object.keys(replayMarkers).forEach(function(sn){
    if(!active[sn]){
      map.removeLayer(replayMarkers[sn]);
      delete replayMarkers[sn];
    }
  });
}

function droneIcon(color, lost, headingDeg, selected, indexNo, alarm){
  var op = lost ? 0.34 : 1.0;
  var rot = Number(headingDeg);
  if(!isFinite(rot)) rot = 0;
  var idx = Number(indexNo);
  if(!isFinite(idx) || idx <= 0) idx = 0;
  var idxTxt = idx > 99 ? '99+' : String(Math.round(idx));
  var cls = 'drone-pin' + (selected ? ' selected' : '') + (alarm ? ' alarm' : '');
  var svg = '<div class="'+cls+'" style="--drone-color:'+escAttr(color)+';--drone-rot:'+rot.toFixed(1)+'deg;--drone-op:'+op.toFixed(2)+'">'
    +'<div class="drone-symbol"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 48 48" width="46" height="46" aria-hidden="true">'
    +'<path d="M24 3.8 39.7 41.5 24 33.8 8.3 41.5 24 3.8Z" fill="'+escAttr(color)+'" stroke="#fff" stroke-width="2.5" stroke-linejoin="round"/>'
    +'<path d="M24 8.6v24.8M15.5 37.9 24 29.4l8.5 8.5" fill="none" stroke="rgba(255,255,255,.82)" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>'
    +'</svg></div><div class="drone-index">'+esc(idxTxt)+'</div></div>';
  return L.divIcon({
    html: svg, className:'rid-drone-icon', iconSize:[74,58], iconAnchor:[25,30], popupAnchor:[0,-30]
  });
}

function pilotIcon(color, lost){
  var op = lost ? 0.4 : 1.0;
  var fill = color || '#ffb84d';
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="48" height="48" viewBox="0 0 24 24">'
    +'<rect x="3.5" y="3.5" width="17" height="17" rx="4" ry="4" fill="'+fill+'" fill-opacity="'+op+'" stroke="#fff" stroke-width="1.4"/>'
    +'<text x="12" y="16" text-anchor="middle" font-size="12" fill="#fff" font-family="monospace" font-weight="bold">👤</text>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[48,48], iconAnchor:[24,24], popupAnchor:[0,-20]
  });
}

function updateMap(drones){
  if(!map) return;
  applyBaseMarker(false);
  var autoState = mapAutoState();
  var page = currentAppPage();
  var rows = Array.isArray(drones) ? drones : [];
  var selected = (page === 'history') ? historyVisibleSnList(rows) : selectedSnList();
  var replayFocus = replayFocusSn();
  if(page === 'history' && replayFocus) selected = [replayFocus];
  var selectedSet = {};
  selected.forEach(function(sn){ selectedSet[sn] = true; });
  var recentRows = liveRecentRows(rows);
  var trackSn = displayTrackSnList(page, rows);
  var liveAir = (page === 'live' ? recentRows : rows).filter(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return false;
    if(page === 'history' && !selectedSet[sn]) return false;
    if(e.lat==null || e.lon==null) return false;
    return true;
  });
  var livePilot = (page === 'live' ? recentRows : rows).filter(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return false;
    if(page === 'history' && !selectedSet[sn]) return false;
    if(e.pilot_lat==null || e.pilot_lon==null) return false;
    return true;
  });
  var mapHintTxt = '';
  if(page === 'live'){
    mapHintTxt = '实时目标:' + recentRows.length + '  飞机:' + liveAir.length + '  飞手:' + livePilot.length + '  离线:2分钟  轨迹:5分钟';
  }else{
    mapHintTxt = '显示飞机:' + liveAir.length + '  已选:' + selected.length + '  轨迹:' + trackSn.length + '  飞手:' + livePilot.length;
  }
  if(!autoState.allow){
    mapHintTxt += '  |  自动回中冷却 ' + Math.ceil(autoState.remain) + 's';
  }
  document.getElementById('map-hint').textContent = mapHintTxt;

  // color assignment by SN
  rows.forEach(function(e){
    if(!colorIdx[e.sn]){
      var n = Object.keys(colorIdx).length;
      colorIdx[e.sn] = COLORS[n % COLORS.length];
    }
  });

  var activeAir = {};
  var activeTws = {};
  var nowSec = Date.now() / 1000;
  var headingMinMove = 2.0;
  var headingMaxGapSec = 90.0;
  liveAir.forEach(function(e, idx){
    var sn = String(e.sn || '');
    if(!sn) return;
    activeAir[sn] = true;
    var col = colorIdx[sn];
    var isSel = !!selectedSet[sn];
    var inAlarmZone = !!zoneAlarmSnSet[sn];
    var latRaw = Number(e.lat), lonRaw = Number(e.lon);
    var prev = motionState[sn] || {};
    var heading = null;
    var headingDelta = null;
    if(isFinite(Number(prev.lat)) && isFinite(Number(prev.lon))){
      var dt = nowSec - Number(prev.ts || 0);
      if(isFinite(dt) && dt >= 0 && dt <= headingMaxGapSec){
        var hs = calcHeadingByLatLon(Number(prev.lat), Number(prev.lon), latRaw, lonRaw, headingMinMove);
        if(hs.ok) heading = hs.heading;
      }
    }
    if(heading == null && isFinite(Number(prev.heading))){
      heading = Number(prev.heading);
    }
    if(heading != null && isFinite(Number(heading))){
      heading = normDeg(heading);
      headingDelta = headingDeltaDeg(heading, mapHeadingRefDeg);
    }else{
      heading = null;
      headingDelta = null;
    }
    motionState[sn] = {lat:latRaw, lon:lonRaw, heading:heading, ts:nowSec};

    var popup = '<b>'+sn+'</b><br>'+e.model+'<br>'
      +(e.lat!=null?e.lat.toFixed(5):'-')+', '+(e.lon!=null?e.lon.toFixed(5):'-')
      +'<br>高度: '+(e.alt!=null?e.alt.toFixed(1)+'m':'N/A')
      +'<br>速度: '+(e.spd!=null?e.spd.toFixed(1)+'m/s':'N/A')
      +'<br>信号: '+(e.rssi!=null?e.rssi+'dBm':'N/A')
      +'<br>航向: '+(isFinite(Number(heading))?Number(heading).toFixed(1)+'°':'N/A')
      +'<br>航向差: '+(isFinite(Number(headingDelta))?((headingDelta>=0?'+':'')+Number(headingDelta).toFixed(1)+'°'):'N/A')
      +'<br>数据更新: '+esc(String(e.age_text || fmtAge(e.age)));

    var airPos = toMapLatLng(latRaw, lonRaw);
    var dispNo = idx + 1;
    if(markers[sn]){
      markers[sn].setLatLng(airPos)
                   .setIcon(droneIcon(col, e.lost, heading, isSel, dispNo, inAlarmZone))
                   .setPopupContent(popup);
    } else {
      markers[sn] = L.marker(airPos, {icon: droneIcon(col, e.lost, heading, isSel, dispNo, inAlarmZone)})
        .addTo(map).bindPopup(popup);
      (function(snLocal){
        markers[snLocal].on('click', function(){
          if(currentAppPage() === 'history') setHistorySnVisible(snLocal, true);
          else setSnSelected(snLocal, true);
        });
      })(sn);
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
    var popup = '<b>'+sn+'</b><br>飞手位置<br>'
      +(e.pilot_lat!=null?e.pilot_lat.toFixed(5):'-')+', '+(e.pilot_lon!=null?e.pilot_lon.toFixed(5):'-')
      +'<br>类型: '+esc(ptxt);
    if(pilotMarkers[sn]){
      pilotMarkers[sn].setLatLng(pilotPos)
        .setIcon(pilotIcon(col, e.lost))
        .setPopupContent(popup);
    }else{
      pilotMarkers[sn] = L.marker(pilotPos, {icon: pilotIcon(col, e.lost)})
        .addTo(map).bindPopup(popup);
      (function(snLocal){
        pilotMarkers[snLocal].on('click', function(){
          if(currentAppPage() === 'history') setHistorySnVisible(snLocal, true);
          else setSnSelected(snLocal, true);
        });
      })(sn);
    }
  });

  var activeTrack = {};
  var trackLatLngsAll = [];
  trackSn.forEach(function(sn){
    sn = String(sn || '');
    if(!sn) return;
    var tr = filterTrackForDisplay(Array.isArray(trackCache[sn]) ? trackCache[sn] : [], page);
    if(tr.length < 2){
      if(trackLines[sn]){
        map.removeLayer(trackLines[sn]);
        delete trackLines[sn];
        delete trackLineSig[sn];
      }
      return;
    }
    var latlngs = [];
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var lat = Number(p.lat), lon = Number(p.lon);
      if(isFinite(lat) && isFinite(lon)){
        var ll = toMapLatLng(lat, lon);
        latlngs.push(ll);
        trackLatLngsAll.push(ll);
      }
    }
    if(latlngs.length < 2){
      if(trackLines[sn]){
        map.removeLayer(trackLines[sn]);
        delete trackLines[sn];
        delete trackLineSig[sn];
      }
      return;
    }
    activeTrack[sn] = true;
    var tColor = trackColorForSn(sn);
    var sig = trackLatLngSignature(latlngs);
    if(trackLines[sn] && trackLineSig[sn] === sig){
      return;
    }
    if(trackLines[sn]){
      map.removeLayer(trackLines[sn]);
      delete trackLines[sn];
    }
    trackLines[sn] = makeTrackLayer(latlngs, tColor).addTo(map);
    trackLineSig[sn] = sig;
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
  Object.keys(twsLines).forEach(function(sn){
    if(!activeTws[sn]){
      map.removeLayer(twsLines[sn]); delete twsLines[sn];
    }
  });
  // remove stale or unselected tracks
  Object.keys(trackLines).forEach(function(sn){
    if(!activeTrack[sn]){
      map.removeLayer(trackLines[sn]); delete trackLines[sn]; delete trackLineSig[sn];
    }
  });
  Object.keys(motionState).forEach(function(sn){
    if(!activeAir[sn]) delete motionState[sn];
  });

  if(!liveAir.length){
    var b = baseFromMeta(metaState);
    if(page === 'history' && trackLatLngsAll.length && autoState.allow && (!map._rid_fitted || !!map._rid_user_moved)){
      if(trackLatLngsAll.length === 1) map.setView(trackLatLngsAll[0], 15);
      else map.fitBounds(L.latLngBounds(trackLatLngsAll).pad(0.14));
      map._rid_fitted = true;
      map._rid_user_moved = false;
      document.getElementById('map-hint').textContent = '历史轨迹 ' + trackSn.length + ' 架';
      return;
    }
    if(b.ok){
      if(autoState.allow && (!map._rid_base_fitted || !!map._rid_user_moved)){
        map.setView([b.lat, b.lon], b.zoom);
        map._rid_base_fitted = true;
        map._rid_user_moved = false;
      }
      if(autoState.allow){
        document.getElementById('map-hint').textContent = (page === 'live')
          ? '实时页暂无可显示目标'
          : '未勾选飞机或无可显示坐标';
      }else{
        document.getElementById('map-hint').textContent = ((page === 'live')
          ? '实时页暂无可显示目标'
          : '未勾选飞机或无可显示坐标')
          + ' | 自动回中冷却 ' + Math.ceil(autoState.remain) + 's';
      }
    } else {
      document.getElementById('map-hint').textContent='无坐标数据';
    }
    return;
  }

  // first-time fit bounds for visible aircraft only
  var latlngs = liveAir.map(function(e){ return toMapLatLng(e.lat, e.lon); }).concat(page === 'history' ? trackLatLngsAll : []);
  if(latlngs.length && autoState.allow && (!map._rid_fitted || !!map._rid_user_moved)){
    if(latlngs.length === 1) map.setView(latlngs[0], 14);
    else map.fitBounds(L.latLngBounds(latlngs).pad(0.3));
    map._rid_fitted = true;
    map._rid_user_moved = false;
  }
}
</script>
</body></html>"""

_HW_PAGE_HTML = """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>硬件配置助手 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}
:root{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --muted:#c8c6c4;--blue:#2899f5;--green:#92c353;--warn:#f7630c;--glow:rgba(40,153,245,.12);--soft:rgba(255,255,255,.03);--app-vh:100dvh
}
body.theme-light{
  --bg:#f3f2f1;--bg2:#edebe9;--card:#ffffff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;
  --muted:#605e5c;--blue:#0078d4;--green:#107c10;--warn:#d83b01;--glow:rgba(0,120,212,.10);--soft:rgba(0,0,0,.018)
}
html,body{margin:0;padding:0;background:var(--bg);color:var(--txt);font-family:var(--font-ui)}
body{min-height:100vh;background:linear-gradient(180deg,var(--bg),var(--bg2) 18%,var(--bg));}
.wrap{max-width:1360px;margin:0 auto;padding:22px 18px 32px}
.topbar{display:flex;justify-content:space-between;align-items:flex-start;gap:14px;flex-wrap:wrap;margin-bottom:16px}
.title{font:600 32px/1 var(--font-ui);letter-spacing:.01em}
.sub{color:var(--muted);margin-top:6px}
.actions{display:flex;gap:10px;flex-wrap:wrap}
.btn{border:1px solid var(--border);background:var(--card2);color:var(--txt);padding:10px 14px;border-radius:4px;cursor:pointer;font:600 14px/1 var(--font-ui);letter-spacing:0;transition:border-color .14s ease,background-color .14s ease,color .14s ease,transform .14s ease,box-shadow .14s ease;box-shadow:0 1px 2px rgba(0,0,0,.06)}
.btn:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--card2));box-shadow:0 2px 8px var(--glow)}
.btn.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:var(--warn)}
.btn.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--card2))}
.layout{display:grid;grid-template-columns:minmax(320px,.92fr) minmax(400px,1.08fr);gap:14px}
.stack{display:grid;gap:14px}
.card{border:1px solid var(--border);border-radius:4px;background:var(--card);padding:16px;box-shadow:0 1px 3px rgba(0,0,0,.08);animation:officeFade .16s ease-out both}
.card h2{margin:0 0 12px;font:600 18px/1 var(--font-ui);letter-spacing:.01em}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.field{display:grid;gap:6px}
.field label{font:600 12px/1 var(--font-ui);letter-spacing:.01em;color:var(--muted);text-transform:none}
select,input{width:100%;background:var(--card2);color:var(--txt);border:1px solid var(--border);border-radius:4px;padding:10px 12px;font:600 14px/1.35 var(--font-ui);transition:border-color .14s ease,box-shadow .14s ease,background-color .14s ease}
select:focus,input:focus{outline:none;border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 38%, transparent)}
.btn-row{display:flex;gap:10px;flex-wrap:wrap}
.btn-group{display:grid;gap:10px}
.status-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:10px}
.status-tile{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
.status-tile .k{font:600 11px/1 var(--font-ui);letter-spacing:.01em;color:var(--muted);text-transform:none}
.status-tile .v{margin-top:8px;font:600 20px/1.1 var(--font-ui)}
.status-tile .s{margin-top:6px;color:var(--muted);font-size:13px;word-break:break-word}
.iface-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:10px}
.iface-card{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
.iface-name{font:600 16px/1 var(--font-ui)}
.iface-meta{margin-top:6px;color:var(--muted);font-size:13px;line-height:1.55}
.tag{display:inline-flex;align-items:center;gap:6px;padding:3px 8px;border:1px solid var(--border);border-radius:999px;font:600 12px/1 var(--font-ui);letter-spacing:0}
.tag.ok{color:var(--green);border-color:color-mix(in srgb, var(--green) 34%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--card2))}
.tag.warn{color:var(--warn);border-color:color-mix(in srgb, var(--warn) 34%, var(--border));background:color-mix(in srgb, var(--warn) 8%, var(--card2))}
.status-line{white-space:pre-wrap;color:var(--muted);font-size:13px;line-height:1.6}
pre{margin:0;min-height:360px;max-height:60vh;overflow:auto;background:var(--card2);border:1px solid var(--border);border-radius:4px;padding:14px;color:var(--txt);font:13px/1.55 var(--font-mono)}
@keyframes officeFade{from{opacity:.0;transform:translateY(4px)}to{opacity:1;transform:none}}
@media (max-width:1080px){.layout{grid-template-columns:1fr}.grid,.status-grid{grid-template-columns:1fr}}
</style>
</head><body>
<div class="wrap">
  <div class="topbar">
    <div>
      <div class="title">硬件配置助手</div>
      <div class="sub">网卡、信道、采集恢复。</div>
    </div>
    <div class="actions">
      <button class="btn" id="btn-back" type="button">返回设置</button>
      <button class="btn" id="btn-theme" type="button">浅色</button>
      <button class="btn" id="btn-refresh" type="button">刷新状态</button>
    </div>
  </div>
  <div class="layout">
    <div class="stack">
      <div class="card">
        <h2>当前状态</h2>
        <div class="status-grid">
          <div class="status-tile"><div class="k">采集状态</div><div class="v" id="tile-state">-</div><div class="s" id="tile-msg">-</div></div>
          <div class="status-tile"><div class="k">当前网卡</div><div class="v" id="tile-active-iface">-</div><div class="s" id="tile-selected-iface">默认/未设置</div></div>
          <div class="status-tile"><div class="k">当前信道</div><div class="v" id="tile-channel">-</div><div class="s" id="tile-extra">-</div></div>
        </div>
        <div id="status" class="status-line" style="margin-top:12px">-</div>
      </div>
      <div class="card">
        <h2>控制面板</h2>
        <div class="grid">
          <div class="field"><label for="iface">目标网卡</label><select id="iface"><option value="">请选择默认网卡</option></select></div>
          <div class="field"><label for="channel">目标信道</label><input id="channel" type="number" min="1" max="196" value="6"></div>
        </div>
        <div class="btn-group" style="margin-top:14px">
          <div class="btn-row">
            <button class="btn" id="btn-iw-dev" type="button">查看 iw dev</button>
            <button class="btn" id="btn-iw-info" type="button">查看 iw info</button>
            <button class="btn" id="btn-iw-link" type="button">查看 iw link</button>
          </div>
          <div class="btn-row">
            <button class="btn" id="btn-set-monitor" type="button">切换为监控模式</button>
            <button class="btn" id="btn-set-managed" type="button">切换为托管模式</button>
            <button class="btn" id="btn-set-channel" type="button">应用目标信道</button>
          </div>
          <div class="btn-row">
            <button class="btn" id="btn-restart-iface" type="button">重启网卡</button>
            <button class="btn warn" id="btn-restart-program" type="button">重启主程序</button>
          </div>
        </div>
      </div>
      <div class="card">
        <h2>网卡总览</h2>
        <div id="iface-grid" class="iface-grid"></div>
      </div>
    </div>
    <div class="stack">
      <div class="card">
        <h2>命令输出</h2>
        <pre id="output">-</pre>
      </div>
    </div>
  </div>
</div>
<script>
function qs(id){ return document.getElementById(id); }
function showStatus(s){ qs('status').textContent = String(s||'-'); }
function showOut(t){ qs('output').textContent = String(t||'-'); }
function loadTheme(){
  try{
    var s = localStorage.getItem('rid_ui_theme');
    if(s === 'dark' || s === 'light') return s;
  }catch(_e){}
  if(window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches) return 'light';
  return 'dark';
}
function applyTheme(theme){
  var light = (theme === 'light');
  document.body.classList.toggle('theme-light', light);
  document.body.classList.toggle('theme-dark', !light);
  try{ localStorage.setItem('rid_ui_theme', light ? 'light' : 'dark'); }catch(_e){}
  qs('btn-theme').textContent = light ? '深色' : '浅色';
}
function apiUrl(url){
  const u = String(url || '');
  try{
    return new URL(u, window.location.origin).toString();
  }catch(_e){
    return u;
  }
}
let authRedirecting = false;
function authExpired(r, d){
  const err = String((d && d.error) || '');
  return r && r.status === 401 && (!!(d && d.auth_expired) || err === 'login required' || err === 'auth required');
}
function redirectLogin(){
  if(authRedirecting) return;
  authRedirecting = true;
  location.href = '/login?next=/';
}
async function getJson(url){
  const r = await fetch(apiUrl(url), {cache:'no-store', headers:{'X-LightRID-Page':'1'}});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
async function postJson(url, body){
  const r = await fetch(apiUrl(url), {method:'POST', headers:{'Content-Type':'application/json','X-LightRID-Page':'1'}, body:JSON.stringify(body||{})});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
function curIface(){ return String(qs('iface').value || '').trim(); }
function fmtOpResult(d){
  if(!d) return '-';
  if(Array.isArray(d.steps)){
    return d.steps.map((x, i)=>`[${i+1}] ${x.cmd}\\ncode=${x.code}\\n${x.stdout||''}\\n${x.stderr||''}`).join('\\n\\n');
  }
  if(typeof d.stdout === 'string' || typeof d.stderr === 'string'){
    return `cmd: ${d.cmd||'-'}\\ncode: ${d.code}\\n\\n${d.stdout||''}${(d.stderr?('\\n'+d.stderr):'')}`;
  }
  return JSON.stringify(d, null, 2);
}
function renderIfaceGrid(items){
  const root = qs('iface-grid');
  const arr = Array.isArray(items) ? items : [];
  if(!root) return;
  if(!arr.length){
    root.innerHTML = '<div class="iface-card"><div class="iface-name">未发现网卡</div><div class="iface-meta">请检查 USB 网卡、驱动与权限。</div></div>';
    return;
  }
  root.innerHTML = arr.map(it=>{
    const mode = String(it.mode || '-');
    const band = it.supports_5g ? '2.4G / 5G' : '2.4G';
    const monitor = mode.toLowerCase().indexOf('monitor') >= 0;
    return '<div class="iface-card">'
      +'<div class="iface-name">'+String(it.name || '-').replace(/</g,'&lt;')+'</div>'
      +'<div style="margin-top:10px"><span class="tag '+(monitor ? 'ok' : 'warn')+'">'+(monitor ? '监控模式' : '非监控模式')+'</span></div>'
      +'<div class="iface-meta">模式: '+mode+'<br>频段: '+band+'<br>5G 支持: '+(it.supports_5g ? '是' : '否')+'</div>'
      +'</div>';
  }).join('');
}
async function refreshStatus(){
  try{
    const d = await getJson('/api/hw/status');
    const items = Array.isArray(d.items) ? d.items : [];
    const sel = qs('iface');
    const old = sel.value;
    sel.innerHTML = '<option value="">请选择固定网卡</option>' + items.map(it=>{
      const n = String(it.name||'');
      const m = String(it.mode||'');
      const g = it.supports_5g ? '5G' : '2.4G';
      return `<option value="${n}">${n} [${m}] ${g}</option>`;
    }).join('');
    if(old) sel.value = old;
    const snf = d.sniff_state || {};
    qs('tile-state').textContent = String(snf.state || '-');
    qs('tile-msg').textContent = String(snf.msg || '-');
    qs('tile-active-iface').textContent = String(d.active_iface || '-');
    qs('tile-selected-iface').textContent = '选择: ' + String(curIface() || '未绑定');
    qs('tile-channel').textContent = String((snf.channel || d.current_channel || '-') || '-');
    qs('tile-extra').textContent = '网卡数: ' + String(items.length || 0);
    showStatus(`采集网卡: ${d.active_iface||'-'}\n状态: ${snf.state||'-'}\n说明: ${snf.msg||'-'}`);
    renderIfaceGrid(items);
    showOut(JSON.stringify(d, null, 2));
  }catch(e){
    showStatus('刷新失败: ' + (e.message || e));
  }
}
async function runOp(op, ext){
  try{
    showStatus('执行中: ' + op);
    const body = Object.assign({op: op, iface: curIface()}, ext||{});
    const d = await postJson('/api/hw/op', body);
    showStatus('完成: ' + op + (d.ok ? ' (OK)' : ' (FAILED)'));
    showOut(fmtOpResult(d));
    if(op === 'restart_program'){ setTimeout(refreshStatus, 1200); }
  }catch(e){
    showStatus('执行失败: ' + (e.message || e));
  }
}
qs('btn-back').addEventListener('click', ()=>{ location.href = '/settings'; });
qs('btn-theme').addEventListener('click', ()=>applyTheme(document.body.classList.contains('theme-light') ? 'dark' : 'light'));
qs('btn-refresh').addEventListener('click', refreshStatus);
qs('btn-iw-dev').addEventListener('click', ()=>runOp('iw_dev'));
qs('btn-iw-info').addEventListener('click', ()=>runOp('iw_info'));
qs('btn-iw-link').addEventListener('click', ()=>runOp('iw_link'));
qs('btn-set-monitor').addEventListener('click', ()=>runOp('set_monitor'));
qs('btn-set-managed').addEventListener('click', ()=>runOp('set_managed'));
qs('btn-restart-iface').addEventListener('click', ()=>runOp('restart_iface'));
qs('btn-set-channel').addEventListener('click', ()=>runOp('set_channel', {channel: Number(qs('channel').value||0)}));
qs('btn-restart-program').addEventListener('click', ()=>{
  if(confirm('确认重启主程序？')) runOp('restart_program');
});
applyTheme(loadTheme());
refreshStatus();
</script>
</body></html>"""

_MAIN_PAGE_PATCH_CSS = r"""
:root{
  --app-vh:100dvh;
  --rid-home-header-height:108px;
  --rid-home-content-height:calc(var(--app-vh) - var(--rid-home-header-height));
}
header.app-shell-header{
  margin:12px 12px 0;
  padding:10px 12px;
  display:flex;
  align-items:center;
  gap:10px;
  flex-wrap:nowrap;
  overflow-x:auto;
  overflow-y:visible;
  white-space:nowrap;
  background:var(--panel);
  border:1px solid var(--border);
  border-radius:4px;
  box-shadow:0 1px 3px rgba(0,0,0,.08);
}
header.app-shell-header::-webkit-scrollbar{height:6px}
.main-shell-top{
  display:flex;
  align-items:center;
  gap:10px;
  flex:1 0 auto;
  min-width:max-content;
}
.main-title-block{
  min-width:0;
  display:flex;
  align-items:center;
  gap:10px;
}
header.app-shell-header h1{
  margin:0;
  font:600 20px/1 var(--font-ui);
  letter-spacing:.01em;
  color:var(--txt);
  text-transform:none;
  white-space:nowrap;
}
.main-title-sub{
  display:none;
}
.main-head-side{
  display:flex;
  align-items:center;
  gap:8px;
  justify-content:flex-end;
  min-width:0;
  flex:1 0 auto;
}
.main-menu-actions{
  display:flex;
  gap:8px;
  flex-wrap:nowrap;
  justify-content:flex-end;
}
.main-live-stats{
  display:flex;
  gap:8px;
  flex-wrap:nowrap;
  justify-content:flex-end;
}
.main-live-stats .stat{
  border:1px solid var(--border);
  border-radius:4px;
  background:var(--panel2);
  padding:6px 10px;
  color:var(--txt);
  box-shadow:0 1px 2px rgba(0,0,0,.05);
  font-size:13px;
  white-space:nowrap;
}
.main-live-stats .stat b{font-weight:700}
.app-tab-nav{
  display:inline-grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:3px;padding:3px;
  width:auto;min-width:300px;margin:0;
  border:1px solid var(--border);background:var(--panel2);border-radius:4px;
  box-shadow:0 1px 2px rgba(0,0,0,.05)
}
.app-tab-btn,.header-link-btn,.btn-mini,.icon-btn,.info-card-close{
  border:1px solid var(--border);
  background:var(--panel2);
  color:var(--txt);
  border-radius:4px;
  font:600 14px/1 var(--font-ui);
  letter-spacing:0;
  cursor:pointer;
  transition:background-color .14s ease,border-color .14s ease,color .14s ease,transform .14s ease,box-shadow .14s ease;
  box-shadow:0 1px 2px rgba(0,0,0,.05);
}
.app-tab-btn,.header-link-btn,.btn-mini{
  padding:8px 11px;
  text-align:center;
  white-space:nowrap;
}
.icon-btn,.info-card-close{
  width:28px;
  height:28px;
  display:inline-flex;
  align-items:center;
  justify-content:center;
  padding:0;
}
.app-tab-btn:hover,.header-link-btn:hover,.btn-mini:hover,.icon-btn:hover,.info-card-close:hover{
  transform:translateY(-1px);
  border-color:var(--blue);
  background:color-mix(in srgb, var(--blue) 10%, var(--panel2));
  box-shadow:0 2px 8px var(--glow);
}
.app-tab-btn.active{
  border-color:var(--blue);
  background:color-mix(in srgb, var(--blue) 14%, var(--panel2));
  color:var(--txt);
  box-shadow:inset 0 0 0 1px color-mix(in srgb, var(--blue) 26%, transparent)
}
.btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:color-mix(in srgb, var(--warn) 74%, white)}
.btn-mini.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--panel2));border-color:var(--warn);box-shadow:0 2px 8px color-mix(in srgb, var(--warn) 16%, transparent)}
body.theme-light .app-tab-nav{background:var(--panel2);box-shadow:0 1px 2px rgba(15,23,42,.05)}
body.theme-light .app-tab-btn:hover,body.theme-light .header-link-btn:hover,body.theme-light .btn-mini:hover,body.theme-light .icon-btn:hover,body.theme-light .info-card-close:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));border-color:var(--blue);box-shadow:0 2px 8px var(--glow)}
body.theme-light .app-tab-btn.active{
  background:color-mix(in srgb, var(--blue) 12%, var(--panel2));
  color:var(--txt);border-color:var(--blue);box-shadow:inset 0 0 0 1px color-mix(in srgb, var(--blue) 20%, transparent)
}
body.theme-light header.app-shell-header{
  background:var(--panel);
}
body.theme-light .main-live-stats .stat{background:var(--panel2)}
body.theme-light .btn-mini,body.theme-light .header-link-btn,body.theme-light .app-tab-btn,body.theme-light .icon-btn,body.theme-light .info-card-close{
  background:var(--panel2);
  border-color:var(--border);
  color:var(--txt);
}
body.theme-light .btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 40%, var(--border));color:var(--warn)}
body.app-paged{grid-template-rows:auto minmax(0,1fr) auto}
.app-pages{min-height:0;padding:0 14px 10px;display:block;height:max(320px,var(--rid-home-content-height))}
.app-page{display:none;min-height:0;height:100%}
body[data-page="live"] .app-page[data-page="live"],
body[data-page="history"] .app-page[data-page="history"]{display:block}
.live-layout{display:grid;grid-template-columns:minmax(340px,30vw) minmax(0,1fr);gap:14px;height:100%;min-height:0}
.live-card-panel{border:1px solid var(--border);background:var(--panel);border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,.08);display:flex;flex-direction:column;min-height:0;overflow:hidden}
.live-card-head{padding:12px 14px;border-bottom:1px solid var(--border);font:600 14px/1 var(--font-ui);color:var(--txt);display:flex;justify-content:space-between;gap:10px}
.live-card-list{padding:10px;display:grid;gap:10px;overflow:auto;min-height:0;align-content:start}
.live-card{border:1px solid var(--border);background:var(--panel2);border-radius:4px;padding:12px;display:grid;gap:10px;cursor:pointer;transition:background-color .14s ease,border-color .14s ease,transform .14s ease,box-shadow .14s ease}
.live-card:hover{transform:translateY(-1px);border-color:var(--blue);box-shadow:0 2px 8px var(--glow)}
.live-card.selected{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--panel2))}
.live-card.lost{opacity:.72}
.live-card.alarm-zone{border-color:rgba(255,79,79,.78);background:color-mix(in srgb, #ff3b30 10%, var(--panel2));animation:alarmRowPulse .9s ease-in-out infinite alternate}
.live-card-top{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:10px;align-items:start}
.live-card-title{font:700 20px/1.12 var(--font-ui);letter-spacing:.01em;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.live-card-actions{display:flex;align-items:center;gap:8px;flex-wrap:wrap;justify-content:flex-end}
.live-card-pick{display:inline-flex;align-items:center;gap:6px;color:var(--dim);font-size:12px}
.live-card-state{display:inline-flex;align-items:center;padding:3px 8px;border:1px solid var(--border);border-radius:999px;font:600 11px/1 var(--font-ui);color:var(--dim)}
.live-card-state.live{color:var(--green);border-color:color-mix(in srgb, var(--green) 40%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel2))}
.live-card-state.lost{color:var(--warn);border-color:color-mix(in srgb, var(--warn) 38%, var(--border));background:color-mix(in srgb, var(--warn) 8%, var(--panel2))}
.live-card-state.firmware{color:#9fd0ff;border-color:color-mix(in srgb, var(--blue) 34%, var(--border));background:color-mix(in srgb, var(--blue) 9%, var(--panel2))}
.live-card-state.alarm{color:#ffb3ae;border-color:rgba(255,79,79,.68);background:rgba(255,79,79,.14)}
.live-card-snrow{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:8px;align-items:center}
.live-card-snrow .label{font-size:11px;color:var(--dim);letter-spacing:.04em;text-transform:uppercase}
.live-card-sntext{font:700 13px/1.25 var(--font-mono);min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.live-card-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px}
.live-card-item{border:1px solid color-mix(in srgb, var(--border) 84%, transparent);border-radius:4px;padding:8px 9px;background:color-mix(in srgb, var(--panel) 74%, var(--panel2))}
.live-card-item .k{font-size:11px;color:var(--dim);line-height:1;text-transform:uppercase;letter-spacing:.04em}
.live-card-item .v{margin-top:6px;font:600 13px/1.35 var(--font-ui);word-break:break-word}
.live-card-foot{display:flex;justify-content:space-between;gap:8px;flex-wrap:wrap;color:var(--dim);font-size:12px}
.live-map-slot{min-height:0;height:100%;display:flex;flex-direction:column}
.live-map-slot .panel{height:100%}
.live-map-slot #map{height:100%}
.history-layout{display:grid;grid-template-rows:minmax(240px,1fr) minmax(240px,1fr);gap:14px;height:100%;min-height:0}
.history-table-slot,.history-map-slot{min-height:0;display:flex;flex-direction:column}
.history-table-slot .tbl-wrap,.history-map-slot .panel{height:100%;min-height:0}
.history-table-slot .tbl-wrap{overflow:auto}
.history-table-slot .tbl-wrap table{min-width:100%}
.history-map-slot #map{height:100%}
.track-sel-wrap{gap:6px}
.track-color-chip{display:inline-block;width:10px;height:10px;border-radius:50%;background:var(--track-color,#1f9dff);box-shadow:0 0 0 2px color-mix(in srgb, var(--track-color,#1f9dff) 24%, transparent);flex:0 0 auto}
.track-replay-card{
  display:none;
  position:absolute;
  right:14px;
  top:62px;
  bottom:14px;
  z-index:1200;
  width:clamp(260px,25%,360px);
  border:1px solid var(--border);
  border-radius:4px;
  background:color-mix(in srgb, var(--panel) 94%, transparent);
  backdrop-filter:blur(8px);
  box-shadow:0 12px 24px rgba(0,0,0,.18);
  padding:12px;
  overflow:auto;
}
#map-panel.history-mounted .track-replay-card{display:block}
.track-replay-head{display:flex;justify-content:space-between;align-items:flex-start;gap:10px;margin-bottom:10px}
.track-replay-title{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.track-replay-sub,.track-replay-status{margin-top:5px;color:var(--dim);font-size:12px;line-height:1.45}
.track-replay-card .input-mini{width:100%;height:34px;border:1px solid var(--border);background:var(--panel2);color:var(--txt);border-radius:4px;padding:6px 8px;font:600 13px/1.2 var(--font-ui);margin-bottom:10px}
.track-replay-time{border:1px solid var(--border);border-radius:4px;background:var(--panel2);padding:8px 10px;font-size:12px;line-height:1.45;color:var(--txt);margin-bottom:10px;white-space:pre-line}
.track-replay-ranges{display:grid;gap:8px;margin:10px 0}
.track-replay-ranges input{width:100%;accent-color:var(--blue)}
.track-replay-controls{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.track-speed-label{display:grid;grid-template-columns:auto minmax(110px,1fr) 42px;align-items:center;gap:7px;color:var(--dim);font-size:12px;flex:1 1 190px;min-width:0}
.track-speed-label input{width:100%;accent-color:var(--blue)}
.track-speed-value{font:700 12px/1 var(--font-mono);color:var(--txt);text-align:right}
#map-panel.fullscreen .track-replay-card{right:350px;bottom:auto;max-height:calc(100vh - 82px)}
#map-panel.fullscreen .map-mini-list{max-height:calc(100vh - 82px)}
.app-page[data-page="ops"]{display:none!important}
.app-page[data-page="ops"] .bottom .panel .logbox,
.app-page[data-page="ops"] .bottom .panel .aplist{flex:1;min-height:0;max-height:none}
#map-panel-toggle,#log-panel-toggle,#ap-panel-toggle,#bottom-restore{display:none!important}
#map-panel .panel-hdr,#log-panel .panel-hdr,#ap-panel .panel-hdr{cursor:default!important}
.app-page .panel{border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,.08);animation:officeFade .16s ease-out both}
.app-page .panel-hdr{font-size:13px;letter-spacing:.01em}
.tbl-wrap,.app-page .panel,.map-mini-list,.banner{
  border-radius:4px;
}
.tbl-wrap{
  box-shadow:0 1px 3px rgba(0,0,0,.08);
}
.app-page .panel{
  border:1px solid var(--border);
  background:var(--panel);
}
.app-page .panel-hdr{
  padding:12px 14px;
  border-bottom:1px solid var(--border);
  color:var(--txt);
}
.app-page .panel-hdr .sub{color:var(--dim)}
.app-page .panel-hdr label{color:var(--dim)}
.app-page .panel.map-panel{position:relative}
.zone-alarm{
  position:fixed;inset:18px;display:none;z-index:9996;border:2px solid rgba(255,79,79,.92);
  border-radius:4px;box-shadow:0 0 0 999px rgba(255,0,0,.12), inset 0 0 0 1px rgba(255,80,80,.18);
  pointer-events:none;align-items:center;justify-content:center;padding:24px;text-align:center;
  background:rgba(255,90,90,.06);
}
.zone-alarm.show{display:flex;animation:zonePulse 1.15s ease-in-out infinite alternate}
.zone-alarm-card{backdrop-filter:blur(8px);background:color-mix(in srgb, var(--panel) 92%, transparent);border:1px solid rgba(255,96,96,.75);border-radius:4px;padding:26px 28px;max-width:min(640px,88vw);box-shadow:0 18px 28px rgba(0,0,0,.18)}
.zone-alarm-title{font:600 34px/1 var(--font-ui);color:#ff7b7b;letter-spacing:.06em;margin-bottom:10px}
.zone-alarm-text{font:500 18px/1.55 var(--font-ui);color:#ffe8e8}
body.zone-alert-active header.app-shell-header,body.zone-alert-active header{box-shadow:0 0 0 2px rgba(255,79,79,.42),0 8px 22px rgba(255,0,0,.16)}
@keyframes zonePulse{from{transform:scale(1);opacity:.92}to{transform:scale(1.01);opacity:1}}
.info-sections{display:grid;gap:14px}
.info-block{border:1px solid var(--border);border-radius:4px;padding:14px;background:var(--panel2);box-shadow:0 1px 2px rgba(0,0,0,.04)}
.info-block h3{font:600 15px/1 var(--font-ui);letter-spacing:.01em;margin-bottom:12px;color:var(--txt)}
.info-actions{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:12px}
.info-actions .btn-mini{padding:7px 12px}
.info-model-cell{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.info-model-na{font:700 13px/1 var(--font-mono);color:var(--dim)}
.model-row-actions{display:inline-flex;gap:6px;flex-wrap:wrap;vertical-align:middle}
.model-row-actions .btn-mini{padding:5px 8px;font-size:12px;line-height:1.1}
@keyframes officeFade{from{opacity:0;transform:translateY(4px)}to{opacity:1;transform:none}}
@media (max-width: 960px){
  header.app-shell-header{gap:8px}
  .app-tab-nav{min-width:286px}
  .live-layout{grid-template-columns:1fr;height:auto}
  .live-card-panel{max-height:40vh}
  .history-layout{grid-template-rows:minmax(220px,1fr) minmax(300px,1fr);height:auto}
  .history-table-slot .tbl-wrap{height:auto;max-height:max(260px,var(--rid-home-content-height))}
  .track-replay-card{left:10px;right:10px;top:auto;bottom:10px;width:auto;max-height:42%}
  #map-panel.fullscreen .track-replay-card{left:10px;right:10px;top:auto;bottom:10px;max-height:34vh}
  #map-panel.fullscreen .map-mini-list{right:10px;top:62px;max-height:calc(66vh - 82px)}
  body[data-page="live"] .live-map-slot .panel{height:max(360px,calc(var(--rid-home-content-height) - 40vh - 14px))}
  .main-shell-top,.main-head-side,.main-menu-actions,.main-live-stats{gap:6px}
  header.app-shell-header h1{font-size:18px}
}
@media (max-width: 720px){
  .live-card-grid{grid-template-columns:1fr}
  .live-card-title{font-size:17px}
}
"""

_MAIN_PAGE_PATCH_JS = r"""
(function(){
  var PAGE_COOKIE='rid_home_page';
  var pageReady=false;
  var alarmRects=[];
  var alarmOverlayHideTimer=null;
  var alarmLastSig='';
  function syncHomeViewport(){
    var vp = window.visualViewport;
    var vh = Math.max(320, Math.round((vp && vp.height) ? vp.height : window.innerHeight || 0));
    document.documentElement.style.setProperty('--app-vh', vh + 'px');
    var header = document.querySelector('header.app-shell-header') || document.querySelector('header');
    var headerBudget = 108;
    if(header && header.getBoundingClientRect){
      var rect = header.getBoundingClientRect();
      var cs = window.getComputedStyle(header);
      headerBudget = Math.ceil(rect.top + rect.height + (parseFloat(cs.marginBottom) || 0) + 14);
    }
    var contentH = Math.max(320, vh - headerBudget);
    document.documentElement.style.setProperty('--rid-home-header-height', headerBudget + 'px');
    document.documentElement.style.setProperty('--rid-home-content-height', contentH + 'px');
    if(map){
      setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 40);
    }
  }
  function ensureZoneOverlay(){
    var el = document.getElementById('zone-alarm');
    if(el) return el;
    el = document.createElement('div');
    el.id = 'zone-alarm';
    el.className = 'zone-alarm';
    el.innerHTML = '<div class="zone-alarm-card"><div class="zone-alarm-title">区域告警</div><div id="zone-alarm-text" class="zone-alarm-text">检测到目标进入报警区域</div></div>';
    document.body.appendChild(el);
    return el;
  }
  function navSet(page){
    var p = (page === 'history') ? 'history' : 'live';
    if(p === 'live' && isMapFullscreen()){
      try{
        if(document.exitFullscreen) document.exitFullscreen();
        else if(document.webkitExitFullscreen) document.webkitExitFullscreen();
      }catch(_e){}
    }
    document.body.setAttribute('data-page', p);
    cookieSet(PAGE_COOKIE, p, 365);
    var tabs = document.querySelectorAll('.app-tab-btn');
    for(var i=0;i<tabs.length;i++){
      tabs[i].classList.toggle('active', tabs[i].getAttribute('data-page') === p);
    }
    mountMainMapPanel(p);
    displayTrackSnList(p, latestDroneRows).forEach(function(sn){ ensureTrackLoaded(sn, false); });
    refreshReplayBounds(true);
    if(p === 'live'){
      setTimeout(function(){ if(map) map.invalidateSize(false); }, 80);
    }
    renderLiveCards(latestDroneRows);
    renderMapMiniList(latestDroneRows);
    syncTableSelectionUi();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    syncHomeViewport();
  }
  window.__ridNavSet = navSet;
  function mountMainMapPanel(page){
    var panel = qs('map-panel');
    var liveSlot = qs('live-map-slot');
    var historySlot = qs('history-map-slot');
    if(!panel || !liveSlot || !historySlot) return;
    var target = (page === 'history') ? historySlot : liveSlot;
    if(panel.parentNode !== target){
      target.appendChild(panel);
    }
    panel.classList.toggle('history-mounted', page === 'history');
    panel.classList.toggle('live-mounted', page !== 'history');
    ensureTrackReplayCard();
    renderReplayCard();
    updateMapFullscreenButton();
    if(map){
      setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 40);
    }
  }
  function neutralizeCollapseHeader(hdr){
    if(!hdr || hdr.getAttribute('data-no-collapse') === '1') return;
    hdr.setAttribute('data-no-collapse', '1');
    hdr.style.cursor = 'default';
    hdr.addEventListener('click', function(ev){
      var t = ev.target;
      if(t && t.closest && t.closest('button,input,label,a,select,textarea')) return;
      ev.stopImmediatePropagation();
    }, true);
  }
  function neutralizeLegacyCollapsers(){
    ['map-panel','log-panel','ap-panel'].forEach(function(id){
      var panel = qs(id);
      if(!panel || !panel.querySelector) return;
      neutralizeCollapseHeader(panel.querySelector('.panel-hdr'));
    });
  }
  function ensureHeaderChrome(){
    var header = document.querySelector('header');
    if(!header) return;
    header.classList.add('app-shell-header');
    var title = header.querySelector('h1');
    if(title && !qs('main-title-sub')){
      var titleBlock = document.createElement('div');
      titleBlock.className = 'main-title-block';
      title.parentNode.insertBefore(titleBlock, title);
      titleBlock.appendChild(title);
      var versionLabel = header.querySelector('.app-version-label');
      if(versionLabel) titleBlock.appendChild(versionLabel);
      var sub = document.createElement('div');
      sub.id = 'main-title-sub';
      sub.className = 'main-title-sub';
      sub.textContent = '地图、列表、日志。';
      titleBlock.appendChild(sub);
    }
    var statsWrap = header.querySelector('.head-stats');
    if(statsWrap && !qs('main-shell-top')){
      var titleBlockNode = header.querySelector('.main-title-block') || title;
      var top = document.createElement('div');
      top.id = 'main-shell-top';
      top.className = 'main-shell-top';
      var side = document.createElement('div');
      side.id = 'main-head-side';
      side.className = 'main-head-side';
      var actions = document.createElement('div');
      actions.id = 'main-menu-actions';
      actions.className = 'main-menu-actions';
      var stats = document.createElement('div');
      stats.id = 'main-live-stats';
      stats.className = 'main-live-stats';
      var children = Array.prototype.slice.call(statsWrap.children || []);
      children.forEach(function(node){
        if(!node) return;
        if(String(node.tagName || '').toUpperCase() === 'BUTTON'){
          node.classList.add('header-link-btn');
          actions.appendChild(node);
        }else{
          stats.appendChild(node);
        }
      });
      side.appendChild(actions);
      side.appendChild(stats);
      top.appendChild(titleBlockNode);
      top.appendChild(side);
      header.insertBefore(top, header.firstChild);
      if(statsWrap.parentNode) statsWrap.parentNode.removeChild(statsWrap);
    }else if(statsWrap){
      Array.prototype.slice.call(statsWrap.children || []).forEach(function(node){
        if(String(node.tagName || '').toUpperCase() === 'BUTTON'){
          node.classList.add('header-link-btn');
        }
      });
    }
  }
  function ensureMainPages(){
    var header = document.querySelector('header');
    if(header && !qs('app-tab-nav')){
      var nav = document.createElement('div');
      nav.id = 'app-tab-nav';
      nav.className = 'app-tab-nav';
      nav.innerHTML =
        '<button class="app-tab-btn" data-page="live" type="button">实时</button>'+
        '<button class="app-tab-btn" data-page="history" type="button">历史记录</button>';
      nav.addEventListener('click', function(ev){
        var btn = ev.target && ev.target.closest ? ev.target.closest('.app-tab-btn') : null;
        if(!btn) return;
        navSet(btn.getAttribute('data-page') || 'live');
      });
      header.appendChild(nav);
    }
    var clearBtn = qs('btn-clear-history');
    if(clearBtn && !qs('btn-settings')){
      var btn = document.createElement('button');
      btn.id = 'btn-settings';
      btn.className = 'btn-mini header-link-btn';
      btn.type = 'button';
      btn.textContent = '设置';
      btn.addEventListener('click', function(){ location.href = '/settings'; });
      clearBtn.parentNode.insertBefore(btn, clearBtn);
    }
    if(clearBtn && !qs('btn-logs')){
      var logBtn = document.createElement('button');
      logBtn.id = 'btn-logs';
      logBtn.className = 'btn-mini header-link-btn';
      logBtn.type = 'button';
      logBtn.textContent = '日志';
      logBtn.addEventListener('click', function(){ location.href = '/logs'; });
      clearBtn.parentNode.insertBefore(logBtn, clearBtn);
    }
    ['btn-freeze','btn-web-notify','btn-clear-history'].forEach(function(id){
      var node = qs(id);
      if(node && node.parentNode) node.parentNode.removeChild(node);
    });
    var advBtn = qs('btn-adv-open'); if(advBtn && advBtn.parentNode) advBtn.parentNode.removeChild(advBtn);
    var hwBtn = qs('btn-hw-assistant'); if(hwBtn && hwBtn.parentNode) hwBtn.parentNode.removeChild(hwBtn);
    var advModal = qs('adv-modal'); if(advModal && advModal.parentNode) advModal.parentNode.removeChild(advModal);
    try{
      if(typeof setMapPanelCollapsed === 'function') setMapPanelCollapsed(false);
      if(typeof setLogPanelCollapsed === 'function') setLogPanelCollapsed(false);
      if(typeof setApPanelCollapsed === 'function') setApPanelCollapsed(false);
      if(typeof syncBottomPanelLayout === 'function') syncBottomPanelLayout();
    }catch(_e){}
    ensureHeaderChrome();
    neutralizeLegacyCollapsers();
    if(pageReady) return;
    var listWrap = document.querySelector('.tbl-wrap');
    var bottom = document.querySelector('.bottom');
    var mapEl = qs('map');
    var mapPanel = mapEl && mapEl.closest ? mapEl.closest('.panel') : null;
    if(!header || !listWrap || !mapPanel) return;
    document.body.classList.add('app-paged');
    var pages = document.getElementById('app-pages');
    if(!pages){
      pages = document.createElement('div');
      pages.id = 'app-pages';
      pages.className = 'app-pages';
      header.insertAdjacentElement('afterend', pages);
    }
    function ensurePage(name){
      var el = document.querySelector('.app-page[data-page="'+name+'"]');
      if(el) return el;
      el = document.createElement('section');
      el.className = 'app-page';
      el.setAttribute('data-page', name);
      pages.appendChild(el);
      return el;
    }
    var livePage = ensurePage('live');
    var liveLayout = qs('live-layout');
    if(!liveLayout){
      liveLayout = document.createElement('div');
      liveLayout.id = 'live-layout';
      liveLayout.className = 'live-layout';
      liveLayout.innerHTML = '<aside class="live-card-panel"><div class="live-card-head"><span>实时目标</span><span id="live-card-count">0</span></div><div id="live-card-list" class="live-card-list"></div></aside><div id="live-map-slot" class="live-map-slot"></div>';
      livePage.appendChild(liveLayout);
    }
    var historyPage = ensurePage('history');
    var historyLayout = qs('history-layout');
    if(!historyLayout){
      historyLayout = document.createElement('div');
      historyLayout.id = 'history-layout';
      historyLayout.className = 'history-layout';
      historyLayout.innerHTML = '<div id="history-table-slot" class="history-table-slot"></div><div id="history-map-slot" class="history-map-slot"></div>';
      historyPage.appendChild(historyLayout);
    }
    var liveCards = qs('live-card-list');
    if(liveCards && liveCards.getAttribute('data-bound') !== '1'){
      liveCards.setAttribute('data-bound', '1');
      liveCards.addEventListener('click', function(ev){
        var copyBtn = ev.target && ev.target.closest ? ev.target.closest('.copy-sn') : null;
        if(copyBtn){
          ev.preventDefault();
          ev.stopPropagation();
          copySn(copyBtn.getAttribute('data-sn') || '');
          return;
        }
        var cb = ev.target && ev.target.closest ? ev.target.closest('.sel-sn') : null;
        var card = ev.target && ev.target.closest ? ev.target.closest('.live-card[data-sn]') : null;
        if(!card) return;
        var sn = card.getAttribute('data-sn') || '';
        if(cb){
          setSnSelected(sn, !!cb.checked);
          return;
        }
        setSnSelected(sn, true);
        var e = latestDroneMap[sn];
        if(e) showInfoCard(buildInfoHtml(e), true);
        updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
        renderLiveCards(latestDroneRows);
      });
    }
    var historyTableSlot = qs('history-table-slot');
    if(historyTableSlot && listWrap.parentNode !== historyTableSlot){
      historyTableSlot.appendChild(listWrap);
    }
    if(bottom){
      bottom.style.display = 'none';
      bottom.setAttribute('aria-hidden', 'true');
    }
    mountMainMapPanel(cookieGet(PAGE_COOKIE) || 'live');
    pageReady = true;
    syncHomeViewport();
    navSet(cookieGet(PAGE_COOKIE) || 'live');
  }
  function buildInfoSection(title, rows){
    var html = '<section class="info-block"><h3>'+esc(title)+'</h3><div class="info-grid">';
    for(var i=0;i<rows.length;i++){
      if(rows[i][2] === 'html'){
        html += '<div class="info-row"><span class="k">'+esc(rows[i][0])+'</span><span class="v">'+String(rows[i][1] == null ? '' : rows[i][1])+'</span></div>';
      }else{
        html += infoRowHtml(rows[i][0], rows[i][1]);
      }
    }
    html += '</div></section>';
    return html;
  }
  window.exportTrackForSn = async function(sn){
    sn = String(sn || '').trim();
    if(!sn) return;
    var data = await getJson('/api/tools/export/track?sn=' + encodeURIComponent(sn));
    _downloadJsonFile('rid_track_' + sn + '_' + _toolStamp() + '.json', data);
  };
  function cleanModelPrefixFromSn(sn){
    var raw = String(sn || '');
    if(raw.toUpperCase().indexOf('MAC:') === 0) return '';
    return raw.replace(/[^0-9A-Za-z]+/g, '').toUpperCase().slice(0, 8);
  }
  function isUnknownModel(model){
    var v = String(model || '').trim().toUpperCase();
    return !v || v === 'N/A' || v === 'NA' || v === '-';
  }
  function modelActionCell(e){
    e = e || {};
    var model = String(e.model || 'N/A');
    if(!isUnknownModel(model)) return esc(model);
    var sn = String(e.sn || '');
    var prefix = cleanModelPrefixFromSn(sn);
    var disabled = prefix ? '' : ' disabled';
    return '<span class="info-model-cell"><span class="info-model-na">N/A</span>'
      + '<span class="model-row-actions">'
      + '<button class="btn-mini model-map-add" type="button" data-sn="'+escAttr(sn)+'" data-prefix="'+escAttr(prefix)+'"'+disabled+'>添加到识别库</button>'
      + '<button class="btn-mini model-map-issue" type="button" data-sn="'+escAttr(sn)+'" data-prefix="'+escAttr(prefix)+'"'+disabled+'>Issue</button>'
      + '<button class="btn-mini model-map-pr" type="button" data-sn="'+escAttr(sn)+'" data-prefix="'+escAttr(prefix)+'"'+disabled+'>PR</button>'
      + '</span></span>';
  }
  function modelIssueUrl(sn, prefix){
    var title = 'RID model mapping: ' + (prefix || sn || 'unknown');
    var body = [
      'SN: ' + String(sn || ''),
      'Prefix: ' + String(prefix || ''),
      'Current model: N/A',
      '',
      'Please add this RID model mapping to rid_models.json.'
    ].join('\\n');
    return 'https://github.com/luyii-code-1/Light_RID_Scanner/issues/new?title='
      + encodeURIComponent(title) + '&body=' + encodeURIComponent(body);
  }
  function modelPrEditUrl(){
    return 'https://github.com/luyii-code-1/Light_RID_Scanner/edit/main/rid_models.json';
  }
  function patchLocalModel(sn, model){
    sn = String(sn || '');
    model = String(model || '').trim();
    if(!sn || !model) return;
    if(latestDroneMap && latestDroneMap[sn]) latestDroneMap[sn].model = model;
    [latestDroneRows, latestMapRows].forEach(function(list){
      if(!Array.isArray(list)) return;
      list.forEach(function(row){ if(row && String(row.sn || '') === sn) row.model = model; });
    });
    var tr = null;
    if(window.CSS && CSS.escape){
      tr = document.querySelector('tr[data-sn="'+CSS.escape(sn)+'"]');
    }else{
      var rows = document.querySelectorAll('tr[data-sn]');
      for(var i=0;i<rows.length;i++){
        if(String(rows[i].getAttribute('data-sn') || '') === sn){ tr = rows[i]; break; }
      }
    }
    if(tr && tr.children && tr.children[3]) tr.children[3].textContent = model;
    renderLiveCards(latestDroneRows);
  }
  async function addModelFromDetail(sn, prefix){
    sn = String(sn || '');
    prefix = String(prefix || cleanModelPrefixFromSn(sn));
    if(!prefix){
      showBanner('无法从 SN 提取识别库前缀。', 'warn', 3200);
      return;
    }
    var model = window.prompt('请输入 ' + prefix + ' 对应的机型名称', '');
    model = String(model || '').trim();
    if(!model) return;
    try{
      await postJson('/api/settings/models/upsert', {sn:sn, prefix:prefix, model:model});
      patchLocalModel(sn, model);
      showBanner('识别库已添加：' + prefix + ' → ' + model, 'ok', 3200);
      if(latestDroneMap && latestDroneMap[sn]) showInfoCard(buildInfoHtml(latestDroneMap[sn]), true);
    }catch(e){
      showBanner('识别库添加失败：' + (e.message || e), 'warn', 4800);
    }
  }
  function openModelIssue(sn, prefix){
    if(!prefix){
      showBanner('无法从 SN 提取识别库前缀。', 'warn', 3200);
      return;
    }
    window.open(modelIssueUrl(sn, prefix), '_blank', 'noopener');
  }
  async function openModelPr(sn, prefix){
    if(!prefix){
      showBanner('无法从 SN 提取识别库前缀。', 'warn', 3200);
      return;
    }
    var model = window.prompt('请输入机型名称；会复制 JSON 条目并打开 GitHub 编辑页', '');
    model = String(model || '').trim();
    if(model && navigator.clipboard && navigator.clipboard.writeText){
      try{ await navigator.clipboard.writeText('"' + prefix + '": "' + model.replace(/"/g, '\\\\"') + '"'); }catch(_e){}
    }
    window.open(modelPrEditUrl(), '_blank', 'noopener');
    showBanner(model ? 'JSON 条目已复制，已打开 GitHub 编辑页。' : '已打开 GitHub 编辑页。', 'ok', 3600);
  }
  function bindModelActionButtons(){
    var modal = qs('info-modal');
    if(!modal || modal.getAttribute('data-model-actions') === '1') return;
    modal.setAttribute('data-model-actions', '1');
    modal.addEventListener('click', function(ev){
      var addBtn = ev.target && ev.target.closest ? ev.target.closest('.model-map-add') : null;
      var issueBtn = ev.target && ev.target.closest ? ev.target.closest('.model-map-issue') : null;
      var prBtn = ev.target && ev.target.closest ? ev.target.closest('.model-map-pr') : null;
      var btn = addBtn || issueBtn || prBtn;
      if(!btn) return;
      ev.preventDefault();
      ev.stopPropagation();
      var sn = btn.getAttribute('data-sn') || '';
      var prefix = btn.getAttribute('data-prefix') || cleanModelPrefixFromSn(sn);
      if(addBtn) addModelFromDetail(sn, prefix);
      else if(issueBtn) openModelIssue(sn, prefix);
      else openModelPr(sn, prefix);
    });
  }
  function patchInfoCard(){
    buildInfoHtml = function(e){
      e = e || {};
      var base = [
        ['SN', String(e.sn || '-')],
        ['UAS ID', uasIdText(e)],
        ['机型', modelActionCell(e), 'html'],
        ['在线状态', e.lost ? '离线' : '在线'],
        ['来源', snSourceText(e)],
        ['扫描类型', scanTypeText(e)],
        ['固件', firmwareTypeText(e)],
        ['MAC', String(e.mac || '-')],
        ['SSID', String(e.ssid || '(hidden)')],
        ['捕获类型', String(e.capture_type || '-')],
        ['捕获时间', String(e.capture_time || '-')],
        ['最后数据包', String(e.last_pkt_time || e.capture_time || '-')],
        ['信号', e.rssi==null ? 'N/A' : (e.rssi + 'dBm')],
        ['信道', String(e.ch || '?') + (e.ch_assumed ? ' (assumed)' : '')],
        ['包数', String(e.pkts==null?0:e.pkts)],
        ['数据更新时间', String(e.age_text || fmtAge(e.age))],
        ['在线时长', fmtDurSec(e.online_dur)],
        ['首次上线', String(e.first_seen || '-')],
        ['最后上线', String(e.last_seen || '-')],
        ['轨迹点数', String(e.track_count==null?0:e.track_count)]
      ];
      var dronePos = [
        ['纬度', fmt(e.lat,6,'')],
        ['经度', fmt(e.lon,6,'')],
        ['高度', fmt(e.alt,1,'m')],
        ['速度', fmt(e.spd,2,'m/s')],
        ['垂直速度', fmt(e.vspd,2,'m/s')],
        ['方向', String(e.dir || '-')]
      ];
      var pilotPos = [
        ['飞手纬度', fmt(e.pilot_lat,6,'')],
        ['飞手经度', fmt(e.pilot_lon,6,'')],
        ['飞手位置类型', String(e.pilot_loc_type_text || e.pilot_loc_type || '-')]
      ];
      var actionSn = String(e.sn || '');
      var html = '<div class="info-actions">'+
        '<button class="btn-mini export-track-btn" type="button" data-sn="'+escAttr(actionSn)+'">导出轨迹</button>'+
        '<button class="btn-mini warn delete-history-btn" type="button" data-sn="'+escAttr(actionSn)+'">删除历史</button>'+
        '</div><div class="info-sections">';
      html += buildInfoSection('飞机位置信息', dronePos);
      html += buildInfoSection('飞手位置信息', pilotPos);
      html += buildInfoSection('其他信息', base);
      var raws = Array.isArray(e.raw_packets) ? e.raw_packets : [];
      html += '<section class="info-block"><h3>原始包</h3>';
      if(raws.length){
        for(var i=0;i<raws.length;i++){
          var p = raws[i] || {};
          html += '<div class="raw-meta">#'+(i+1)+' ['+esc(String(p.capture_type || e.capture_type || '-'))+'] '+esc(String(p.ts || e.capture_time || '-'))+'</div>';
          html += '<pre class="raw-code">'+esc(String(p.hex || ''))+'</pre>';
        }
      }else{
        html += '<div class="raw-empty">暂无</div>';
      }
      html += '</section></div>';
      return html;
    };
  }
  function zoneList(){
    var list = metaState && metaState.alert_zones;
    if(Array.isArray(list) && list.length){
      return list.filter(function(z){ return !!z && typeof z === 'object'; });
    }
    var z = metaState && metaState.alert_zone;
    return (z && typeof z === 'object') ? [z] : [];
  }
  function zoneBounds(z){
    var lat1 = numOrNull(z.lat1), lat2 = numOrNull(z.lat2), lon1 = numOrNull(z.lon1), lon2 = numOrNull(z.lon2);
    if(lat1==null || lat2==null || lon1==null || lon2==null) return null;
    return {
      south: Math.min(lat1, lat2),
      north: Math.max(lat1, lat2),
      west: Math.min(lon1, lon2),
      east: Math.max(lon1, lon2)
    };
  }
  function clearAlarmZones(){
    if(!map) return;
    while(alarmRects.length){
      try{ map.removeLayer(alarmRects.pop()); }catch(_e){}
    }
  }
  function drawAlarmZones(){
    if(!map) return;
    clearAlarmZones();
    zoneList().forEach(function(z){
      var b = zoneBounds(z || {});
      if(!z || !z.enabled || !b) return;
      var rect = L.rectangle([[b.south, b.west], [b.north, b.east]], {color:'#ff5b5b', weight:2, fillColor:'#ff3b3b', fillOpacity:0.08}).addTo(map);
      rect.bindPopup('<b>'+esc(String(z.name || '报警区域'))+'</b>');
      alarmRects.push(rect);
    });
  }
  function zoneHitGroups(rows){
    var groups = [];
    rows = Array.isArray(rows) ? rows : [];
    zoneList().forEach(function(z){
      var b = zoneBounds(z || {});
      if(!z || !z.enabled || !b) return;
      var hits = [];
      for(var i=0;i<rows.length;i++){
        var e = rows[i] || {};
        if(e.lost || e.archived) continue;
        var lat = numOrNull(e.lat), lon = numOrNull(e.lon);
        if(lat==null || lon==null) continue;
        if(lat >= b.south && lat <= b.north && lon >= b.west && lon <= b.east){
          hits.push(e);
        }
      }
      if(hits.length){
        groups.push({zone:z, hits:hits});
      }
    });
    return groups;
  }
  function zoneHitSnSetFromGroups(groups){
    var out = {};
    (Array.isArray(groups) ? groups : []).forEach(function(group){
      (Array.isArray(group.hits) ? group.hits : []).forEach(function(e){
        var sn = String((e && e.sn) || '');
        if(sn) out[sn] = true;
      });
    });
    return out;
  }
  function zoneHitSnSet(rows){
    return zoneHitSnSetFromGroups(zoneHitGroups(rows));
  }
  function setZoneAlarm(rows){
    var overlay = ensureZoneOverlay();
    var groups = zoneHitGroups(rows);
    zoneAlarmSnSet = zoneHitSnSetFromGroups(groups);
    if(!groups.length){
      overlay.classList.remove('show');
      document.body.classList.remove('zone-alert-active');
      alarmLastSig = '';
      return;
    }
    document.body.classList.add('zone-alert-active');
    var sigParts = [];
    var lines = [];
    groups.forEach(function(group){
      var zoneName = String((group.zone && group.zone.name) || '报警区域');
      var names = group.hits.map(function(x){ return String(x.sn||'-') + ' / ' + String(x.model || 'N/A'); }).join('；');
      lines.push(zoneName + '：' + names);
      sigParts.push(zoneName + '>' + group.hits.map(function(x){ return String(x.sn||''); }).sort().join('|'));
    });
    var sig = sigParts.sort().join(' || ');
    var lineText = lines.join(' / ');
    qs('zone-alarm-text').textContent = '检测到目标进入自定义报警区域：' + lineText;
    overlay.classList.add('show');
    if(sig !== alarmLastSig){
      showBanner('区域告警：' + lineText, 'warn', 5200, {persist:false});
      if(webNotifyEnabled && window.Notification && Notification.permission === 'granted'){
        try{ new Notification('Light RID Scanner 区域告警', {body:lineText}); }catch(_e){}
      }
      alarmLastSig = sig;
    }
    if(alarmOverlayHideTimer) clearTimeout(alarmOverlayHideTimer);
    alarmOverlayHideTimer = setTimeout(function(){
      if(!zoneHitGroups(latestDroneRows).length){
        overlay.classList.remove('show');
        document.body.classList.remove('zone-alert-active');
        zoneAlarmSnSet = {};
      }
    }, 6000);
  }
  var _origBuildExtraUi = buildExtraUi;
  buildExtraUi = function(){
    _origBuildExtraUi();
    neutralizeLegacyCollapsers();
    ensureMainPages();
  };
  var _origApplyMeta = applyMeta;
  applyMeta = function(meta){
    _origApplyMeta(meta);
    ensureMainPages();
    neutralizeLegacyCollapsers();
    drawAlarmZones();
  };
  var _origOnData = onData;
  onData = function(d){
    zoneAlarmSnSet = zoneHitSnSet((d && Array.isArray(d.drones)) ? d.drones : []);
    _origOnData(d);
    if(homeFreezeAfterFirstRender && !uiFrozen){
      homeFreezeAfterFirstRender = false;
      try{ localStorage.removeItem(FREEZE_ON_HOME_KEY); }catch(_e){}
      setFreezeState(true);
      showBanner('列表已冻结，刷新或恢复同步后继续更新。', 'ok', 2600);
    }
  };
  var _origUpdateMap = updateMap;
  updateMap = function(drones){
    zoneAlarmSnSet = zoneHitSnSet(drones);
    refreshReplayBounds(true);
    _origUpdateMap(drones);
    drawAlarmZones();
    setZoneAlarm(drones);
    renderReplayCard();
    updateReplayMarkers();
  };
  document.addEventListener('DOMContentLoaded', function(){
    patchInfoCard();
    bindModelActionButtons();
    ensureMainPages();
    neutralizeLegacyCollapsers();
    drawAlarmZones();
    syncHomeViewport();
  });
  window.addEventListener('resize', syncHomeViewport);
  if(window.visualViewport){
    try{
      window.visualViewport.addEventListener('resize', syncHomeViewport);
      window.visualViewport.addEventListener('scroll', syncHomeViewport);
    }catch(_e){}
  }
})();
"""

def _inject_html_once(html_src: str, marker: str, extra: str) -> str:
    if not extra:
        return html_src
    if extra in html_src:
        return html_src
    return html_src.replace(marker, extra + marker, 1)

def _build_html() -> str:
    html_src = _PAGE_HTML
    html_src = html_src.replace("__APP_VERSION_LABEL__", _app_version_label())
    html_src = _inject_html_once(html_src, "</style>", _MAIN_PAGE_PATCH_CSS + "\n")
    html_src = _inject_html_once(html_src, "</body>", "<script>\n" + _MAIN_PAGE_PATCH_JS + "\n</script>\n")
    return html_src

def _build_login_html(next_path: str = "/", status_message: str = "", status_error: bool = False) -> str:
    safe_next = str(next_path or "/")
    if not safe_next.startswith("/") or safe_next.startswith("//"):
        safe_next = "/"
    password_enabled = _auth_login_method_enabled("password")
    sso_enabled = _auth_login_method_enabled("sso")
    passkey_enabled = _auth_login_method_enabled("passkey")
    has_passkey = passkey_enabled and any(bool(item.get("enabled", True)) for item in _normalize_passkeys(AUTH_CFG.get("passkeys")))
    password_login_html = (
        '  <form id="login-form">\n'
        '    <div class="field"><label for="user">账号</label><input id="user" autocomplete="username" autofocus></div>\n'
        '    <div class="field"><label for="password">密码</label><input id="password" type="password" autocomplete="current-password"></div>\n'
        '    <div class="row"><button id="submit" type="submit">登录</button></div>\n'
        '  </form>\n'
        if password_enabled else ""
    )
    passkey_login_html = (
        '  <div class="row" style="margin-top:12px">\n'
        '    <button id="btn-passkey-login" type="button">使用通行密钥登录</button>\n'
        '  </div>'
        if has_passkey else ""
    )
    if not status_message:
        if passkey_enabled and (not has_passkey) and (not password_enabled) and (not sso_enabled):
            status_message = "当前已启用 PassKey 登录，但尚未登记可用密钥。"
        elif (not password_enabled) and (not has_passkey):
            if sso_enabled:
                status_message = "当前仅允许通过 SSO URL 登录，请使用已生成的登录链接进入。"
            else:
                status_message = "当前没有可用的网页登录方式，请返回设置检查登录方式配置。"
    status_class = "status err" if status_error else "status"
    status_html = '<div class="' + status_class + '" id="status">' + _html_escape(status_message, quote=False) + "</div>"
    method_labels: list[str] = []
    if password_enabled:
        method_labels.append("账号密码")
    if has_passkey:
        method_labels.append("PassKey")
    elif passkey_enabled:
        method_labels.append("PassKey(待登记)")
    if sso_enabled:
        method_labels.append("SSO URL")
    login_method_copy = ("可用方式: " + " / ".join(method_labels)) if method_labels else "当前没有可用的网页登录方式。"
    return f"""<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>登录 - Light RID Scanner</title>
<style>
*{{box-sizing:border-box}}
:root{{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --bg:#f3f2f1;--card:#fff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01
}}
@media (prefers-color-scheme:dark){{
  :root{{--bg:#201f1e;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;--muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c}}
}}
html,body{{margin:0;min-height:100dvh;background:linear-gradient(180deg,var(--bg),var(--card2));color:var(--txt);font-family:var(--font-ui)}}
body{{display:grid;place-items:center;padding:22px}}
.card{{width:min(420px,100%);border:1px solid var(--border);background:var(--card);box-shadow:0 16px 34px rgba(0,0,0,.16);border-radius:4px;padding:26px;animation:fade .18s ease-out both}}
.brand{{font:700 24px/1.1 var(--font-ui);letter-spacing:.01em;margin:0 0 6px}}
.desc{{color:var(--muted);font-size:14px;line-height:1.5;margin:0 0 22px}}
.field{{display:grid;gap:7px;margin-top:14px}}
label{{font:600 12px/1 var(--font-ui);color:var(--muted)}}
input{{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 12px;font:600 15px/1.2 var(--font-ui);outline:none;transition:border-color .14s ease,box-shadow .14s ease}}
input:focus{{border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 34%, transparent)}}
.row{{display:flex;justify-content:space-between;align-items:center;gap:10px;margin-top:20px}}
button{{height:42px;border:1px solid var(--blue);background:var(--blue);color:white;border-radius:4px;padding:0 18px;font:700 14px/1 var(--font-ui);cursor:pointer;transition:transform .14s ease,filter .14s ease}}
button:hover{{transform:translateY(-1px);filter:brightness(1.05)}}
.status{{min-height:20px;margin-top:14px;color:var(--muted);font-size:13px;white-space:pre-wrap}}
.status.err{{color:var(--warn)}}
@keyframes fade{{from{{opacity:0;transform:translateY(5px)}}to{{opacity:1;transform:none}}}}
</style></head><body>
<main class="card">
  <h1 class="brand">Light RID Scanner</h1>
  <p class="desc">登录到在线监控平台。{_html_escape(login_method_copy, quote=False)}</p>
{password_login_html}{passkey_login_html}
  {status_html}
</main>
<script>
const nextPath = {json.dumps(safe_next, ensure_ascii=False)};
const form = document.getElementById('login-form');
const statusEl = document.getElementById('status');
const passkeyBtn = document.getElementById('btn-passkey-login');
function pageHeaders(extra){{
  var h = {{'X-LightRID-Page':'1'}};
  if(extra) Object.keys(extra).forEach(function(k){{ h[k] = extra[k]; }});
  return h;
}}
function setStatus(text, err){{
  if(!statusEl) return;
  statusEl.textContent = text || '';
  statusEl.classList.toggle('err', !!err);
}}
function b64uToBytes(text){{
  var raw = String(text || '').replace(/-/g,'+').replace(/_/g,'/');
  while(raw.length % 4) raw += '=';
  if(!raw) return new Uint8Array(0);
  var bin = atob(raw);
  var out = new Uint8Array(bin.length);
  for(var i=0;i<bin.length;i++) out[i] = bin.charCodeAt(i);
  return out;
}}
function bytesToB64u(bytes){{
  var view = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes || []);
  var bin = '';
  for(var i=0;i<view.length;i++) bin += String.fromCharCode(view[i]);
  return btoa(bin).replace(/\\+/g,'-').replace(/\\//g,'_').replace(/=+$/,'');
}}
async function loginWithPasskey(){{
  if(!window.PublicKeyCredential || !navigator.credentials || !navigator.credentials.get){{
      throw new Error('当前浏览器不支持通行密钥登录');
  }}
  setStatus('正在准备通行密钥登录...', false);
  const startR = await fetch('/api/passkey/login/start', {{
    method:'POST',
    headers:pageHeaders({{'Content-Type':'application/json'}}),
    body:'{{}}'
  }});
  const start = await startR.json().catch(() => ({{}}));
  if(!startR.ok || start.ok === false) throw new Error(start.error || ('HTTP ' + startR.status));
  const pk = start.publicKey || {{}};
  const allowCredentials = Array.isArray(pk.allowCredentials) ? pk.allowCredentials : [];
  const cred = await navigator.credentials.get({{
    publicKey: {{
      challenge: b64uToBytes(pk.challenge || start.challenge || ''),
      rpId: pk.rpId || pk.rp_id || location.hostname,
      timeout: pk.timeout || start.timeout_ms || 300000,
      userVerification: pk.userVerification || 'preferred',
      allowCredentials: allowCredentials.map(function(item){{ return {{type:'public-key', id:b64uToBytes(item.id || '')}}; }})
    }}
  }});
  if(!cred) throw new Error('未获取到通行密钥凭据');
  const response = cred.response || {{}};
  const finishR = await fetch('/api/passkey/login/finish', {{
    method:'POST',
    headers:pageHeaders({{'Content-Type':'application/json'}}),
    body:JSON.stringify({{
      challenge: start.challenge || start.challenge_token || '',
      id: cred.id || '',
      rawId: bytesToB64u(cred.rawId || new Uint8Array(0)),
      type: cred.type || 'public-key',
      response: {{
        clientDataJSON: bytesToB64u(response.clientDataJSON || new Uint8Array(0)),
        authenticatorData: bytesToB64u(response.authenticatorData || new Uint8Array(0)),
        signature: bytesToB64u(response.signature || new Uint8Array(0)),
        userHandle: response.userHandle ? bytesToB64u(response.userHandle) : ''
      }},
      next: nextPath || '/'
    }})
  }});
  const finish = await finishR.json().catch(() => ({{}}));
  if(!finishR.ok || finish.ok === false) throw new Error(finish.error || ('HTTP ' + finishR.status));
  location.href = nextPath || finish.next || '/';
}}
if(form){{
  form.addEventListener('submit', async function(ev){{
    ev.preventDefault();
    const btn = document.getElementById('submit');
    btn.disabled = true;
    setStatus('正在验证...', false);
    try{{
      const r = await fetch('/login', {{
        method:'POST',
        headers:{{'Content-Type':'application/json'}},
        body:JSON.stringify({{username:document.getElementById('user').value || '', password:document.getElementById('password').value || ''}})
      }});
      const d = await r.json().catch(() => ({{}}));
      if(!r.ok || d.ok === false) throw new Error(d.error || '登录失败');
      location.href = nextPath || d.next || '/';
    }}catch(e){{
      setStatus(e.message || String(e), true);
    }}finally{{
      btn.disabled = false;
    }}
  }});
}}
if(passkeyBtn){{
  passkeyBtn.addEventListener('click', async function(){{
    passkeyBtn.disabled = true;
    try{{
      await loginWithPasskey();
    }}catch(e){{
      setStatus(e.message || String(e), true);
    }}finally{{
      passkeyBtn.disabled = false;
    }}
  }});
}}
</script>
</body></html>"""

def _build_eula_html(next_path: str = "/") -> str:
    safe_next = str(next_path or "/")
    if not safe_next.startswith("/") or safe_next.startswith("//"):
        safe_next = "/"
    eula_html = _markdown_to_html(_load_eula_markdown())
    return f"""<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>许可协议 - Light RID Scanner</title>
<style>
*{{box-sizing:border-box}}
:root{{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;--muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c
}}
@media (prefers-color-scheme:light){{
  :root{{--bg:#f3f2f1;--card:#fff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01}}
}}
html,body{{margin:0;min-height:100dvh;background:var(--bg);color:var(--txt);font-family:var(--font-ui)}}
body{{display:grid;place-items:center;padding:18px}}
.shell{{width:min(960px,100%);display:grid;gap:12px}}
.head{{display:flex;justify-content:space-between;align-items:flex-end;gap:12px;flex-wrap:wrap}}
h1{{margin:0;font:700 26px/1.1 var(--font-ui);letter-spacing:0}}
.source{{font:600 12px/1.5 var(--font-ui);color:var(--muted)}}
.source a,.license a{{color:var(--blue);text-decoration:none}}
.source a:hover,.license a:hover{{text-decoration:underline}}
.license{{border:1px solid var(--border);background:var(--card);border-radius:4px;padding:18px;max-height:min(68dvh,720px);overflow:auto;box-shadow:0 16px 34px rgba(0,0,0,.18)}}
.license h1,.license h2,.license h3,.license h4{{margin:18px 0 8px;letter-spacing:0}}
.license h1:first-child,.license h2:first-child{{margin-top:0}}
.license p{{margin:8px 0;line-height:1.65;color:var(--txt)}}
.license ul{{margin:8px 0 12px 20px;padding:0;line-height:1.6}}
.eula-code{{white-space:pre-wrap;word-break:break-word;border:1px solid var(--border);background:var(--card2);border-radius:4px;padding:12px;font:600 12px/1.45 var(--font-mono);color:var(--txt)}}
.accept{{border:1px solid var(--border);background:var(--card);border-radius:4px;padding:14px;display:grid;gap:12px}}
.check{{display:flex;gap:10px;align-items:flex-start;line-height:1.5;color:var(--txt)}}
input[type=checkbox]{{width:16px;height:16px;flex:0 0 auto;margin-top:2px;accent-color:var(--blue)}}
.read-state{{font:600 13px/1.5 var(--font-ui);color:var(--muted)}}
.actions{{display:flex;justify-content:flex-end;gap:10px;flex-wrap:wrap}}
button{{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:0 16px;font:700 14px/1 var(--font-ui);cursor:pointer}}
button.primary{{border-color:var(--blue);background:var(--blue);color:white}}
button.warn{{border-color:color-mix(in srgb,var(--warn) 50%,var(--border));color:var(--warn)}}
button:disabled{{opacity:.58;cursor:not-allowed}}
.status{{min-height:20px;color:var(--muted);font-size:13px;white-space:pre-wrap}}
.status.err{{color:var(--warn)}}
</style></head><body>
<main class="shell">
  <div class="head">
    <div>
      <h1>Light RID Scanner 许可协议</h1>
      <div class="source">EULA 来源：<a href="{_html_escape(EULA_URL)}" target="_blank" rel="noopener noreferrer">{_html_escape(EULA_URL)}</a></div>
    </div>
  </div>
  <article class="license" id="eula-scroll" tabindex="0" aria-label="许可协议正文">{eula_html}</article>
  <section class="accept">
    <div class="read-state" id="read-state">请阅读 EULA，5 秒后才能勾选同意。</div>
    <label class="check"><input id="agree" type="checkbox" disabled> <span>我已完整阅读并同意以上许可协议，确认继续使用本软件。</span></label>
    <div class="actions">
      <button class="warn" id="decline" type="button">不同意</button>
      <button class="primary" id="accept" type="button" disabled>同意并继续</button>
    </div>
    <div id="status" class="status">首次运行必须同意许可协议后才能进入系统。</div>
  </section>
</main>
<script>
const nextPath = {json.dumps(safe_next, ensure_ascii=False)};
const READ_WAIT_MS = 5000;
const readStartMs = Date.now();
function qs(id){{ return document.getElementById(id); }}
function pageHeaders(extra){{ var h={{'X-LightRID-Page':'1'}}; if(extra) Object.keys(extra).forEach(function(k){{ h[k]=extra[k]; }}); return h; }}
function setStatus(text, err){{ qs('status').textContent = text || '-'; qs('status').classList.toggle('err', !!err); }}
function readWaitLeft(){{
  return Math.max(0, READ_WAIT_MS - (Date.now() - readStartMs));
}}
function updateReadState(){{
  var left = readWaitLeft();
  var ready = left <= 0;
  qs('agree').disabled = !ready;
  if(!ready){{
    qs('agree').checked = false;
    qs('accept').disabled = true;
    qs('read-state').textContent = '请阅读 EULA，' + Math.ceil(left / 1000) + ' 秒后才能勾选同意。';
  }}else{{
    qs('read-state').textContent = '已达到阅读等待时间，可以勾选同意。';
    qs('accept').disabled = !qs('agree').checked;
  }}
}}
window.addEventListener('resize', updateReadState);
window.addEventListener('load', updateReadState);
var readTimer = setInterval(function(){{
  updateReadState();
  if(readWaitLeft() <= 0) clearInterval(readTimer);
}}, 250);
setTimeout(updateReadState, 60);
qs('agree').addEventListener('change', function(){{ updateReadState(); }});
qs('decline').addEventListener('click', function(){{ setStatus('未同意许可协议，当前不会进入系统。', true); }});
qs('accept').addEventListener('click', async function(){{
  if(readWaitLeft() > 0){{ setStatus('请先阅读 EULA，等待时间结束后再继续。', true); return; }}
  if(!qs('agree').checked){{ setStatus('请先勾选同意许可协议。', true); return; }}
  var btn = qs('accept');
  btn.disabled = true;
  setStatus('正在保存许可状态...', false);
  try{{
    const r = await fetch('/api/eula/accept', {{
      method:'POST',
      headers:pageHeaders({{'Content-Type':'application/json'}}),
      body:JSON.stringify({{accepted:true,next:nextPath}})
    }});
    const d = await r.json().catch(function(){{ return {{}}; }});
    if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
    location.href = d.next || nextPath || '/';
  }}catch(e){{
    setStatus(e.message || String(e), true);
    btn.disabled = false;
  }}
}});
</script></body></html>"""

def _build_logs_html() -> str:
    return """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>日志 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}
:root{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c;--green:#92c353;--glow:rgba(40,153,245,.12)
}
body.theme-light{--bg:#f3f2f1;--bg2:#edebe9;--card:#ffffff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01;--green:#107c10;--glow:rgba(0,120,212,.10)}
html,body{margin:0;min-height:100dvh;background:linear-gradient(180deg,var(--bg),var(--bg2));color:var(--txt);font-family:var(--font-ui)}
.wrap{width:min(1500px,calc(100vw - 24px));margin:0 auto;padding:16px 12px 26px}
.topbar{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin-bottom:12px}
.title{font:700 28px/1 var(--font-ui)}
.actions,.tabs{display:flex;gap:8px;flex-wrap:wrap}
.btn,.tab{border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 13px;font:700 14px/1 var(--font-ui);cursor:pointer;transition:background-color .14s ease,border-color .14s ease,transform .14s ease,box-shadow .14s ease}
.btn:hover,.tab:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb,var(--blue) 10%,var(--card2));box-shadow:0 2px 8px var(--glow)}
.tab.active{border-color:var(--blue);background:color-mix(in srgb,var(--blue) 14%,var(--card2))}
.panel{border:1px solid var(--border);background:var(--card);border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,.08);overflow:hidden}
.toolbar{display:flex;justify-content:space-between;gap:10px;flex-wrap:wrap;align-items:center;padding:12px;border-bottom:1px solid var(--border)}
.meta{color:var(--muted);font-size:13px}
select,input{height:40px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:8px 10px;font:600 14px/1 var(--font-ui)}
pre{margin:0;height:calc(100dvh - 176px);min-height:420px;overflow:auto;padding:14px;background:#0e1116;color:#d6deeb;font:13px/1.55 var(--font-mono);white-space:pre-wrap;word-break:break-word}
body.theme-light pre{background:#fbfbfb;color:#24292f}
.status{padding:8px 12px;color:var(--muted);font-size:13px;border-top:1px solid var(--border)}
@media(max-width:720px){.wrap{width:calc(100vw - 10px);padding:10px 5px}.title{font-size:22px}pre{height:calc(100dvh - 230px);font-size:12px}}
</style></head><body><div class="wrap">
  <div class="topbar">
    <div><div class="title">日志</div><div class="meta">运行、操作、扫描与扫描差异。</div></div>
    <div class="actions">
      <button class="btn" id="btn-back" type="button">返回主页</button>
      <button class="btn" id="btn-settings" type="button">设置</button>
      <button class="btn" id="btn-theme" type="button">浅色</button>
    </div>
  </div>
  <div class="panel">
    <div class="toolbar">
      <div class="tabs">
        <button class="tab active" data-type="runtime" type="button">运行日志</button>
        <button class="tab" data-type="operation" type="button">操作日志</button>
        <button class="tab" data-type="scan" type="button">扫描日志</button>
        <button class="tab" data-type="scan_diff" type="button">扫描 Diff</button>
      </div>
      <div class="actions">
        <input id="limit" type="number" min="20" max="5000" value="500" title="行数">
        <button class="btn" id="btn-refresh" type="button">刷新</button>
        <button class="btn" id="btn-export" type="button">导出当前</button>
        <button class="btn" id="btn-export-all" type="button">导出全部</button>
      </div>
    </div>
    <pre id="log-view">正在加载...</pre>
    <div id="status" class="status">-</div>
  </div>
</div>
<script>
function qs(id){return document.getElementById(id)}
function enc(v){return String(v==null?'':v)}
function pageHeaders(extra){var h={'X-LightRID-Page':'1'}; if(extra){Object.keys(extra).forEach(function(k){h[k]=extra[k]})} return h}
function apiUrl(path){return new URL(path, location.origin).toString()}
var authRedirecting=false;
function authExpired(r,d){var e=String((d&&d.error)||'');return r&&r.status===401&&((d&&d.auth_expired)||e==='login required'||e==='auth required')}
function redirectLogin(){if(authRedirecting)return;authRedirecting=true;location.href='/login?next=/'}
function loadTheme(){try{var s=localStorage.getItem('rid_ui_theme'); if(s==='light'||s==='dark') return s}catch(_e){} return (matchMedia && matchMedia('(prefers-color-scheme: light)').matches)?'light':'dark'}
function applyTheme(t){var light=t==='light'; document.body.classList.toggle('theme-light', light); try{localStorage.setItem('rid_ui_theme', light?'light':'dark')}catch(_e){} qs('btn-theme').textContent=light?'深色':'浅色'}
var currentType='runtime';
async function loadLogs(){
  var limit=Math.max(20, Math.min(5000, Number(qs('limit').value||500)));
  qs('status').textContent='读取中...';
  var r=await fetch(apiUrl('/api/logs/view?type='+encodeURIComponent(currentType)+'&limit='+limit), {cache:'no-store', headers:pageHeaders()});
  var d=await r.json().catch(function(){return {}});
  if(authExpired(r,d)){redirectLogin();throw new Error('login required')}
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  qs('log-view').textContent=(d.items||[]).join('\\n') || '(empty)';
  qs('status').textContent=String(d.type||currentType)+' · '+String(d.count||0)+' 行';
}
function setType(t){
  currentType=t||'runtime';
  document.querySelectorAll('.tab').forEach(function(x){x.classList.toggle('active', x.getAttribute('data-type')===currentType)});
  loadLogs().catch(function(e){qs('status').textContent=e.message||String(e)});
}
async function downloadLogs(type){
  var limit=Math.max(20, Math.min(5000, Number(qs('limit').value||500)));
  var r=await fetch(apiUrl('/api/logs/export?type='+encodeURIComponent(type||currentType)+'&limit='+limit), {cache:'no-store', headers:pageHeaders()});
  if(r.status===401){
    var d=await r.clone().json().catch(function(){return {}});
    if(authExpired(r,d)){redirectLogin();throw new Error('login required')}
  }
  if(!r.ok) throw new Error('导出失败 HTTP '+r.status);
  var blob=await r.blob();
  if(!blob || !blob.size) throw new Error('导出内容为空');
  var cd=r.headers.get('Content-Disposition')||'';
  var m=/filename="([^"]+)"/.exec(cd);
  var name=m?m[1]:'light-rid-logs.log';
  var url=URL.createObjectURL(blob);
  var a=document.createElement('a'); a.href=url; a.download=name; document.body.appendChild(a); a.click();
  setTimeout(function(){URL.revokeObjectURL(url); if(a.parentNode)a.parentNode.removeChild(a)}, 8000);
}
document.querySelectorAll('.tab').forEach(function(btn){btn.addEventListener('click', function(){setType(btn.getAttribute('data-type'))})});
qs('btn-refresh').addEventListener('click', function(){loadLogs().catch(function(e){qs('status').textContent=e.message||String(e)})});
qs('btn-export').addEventListener('click', function(){downloadLogs(currentType).catch(function(e){qs('status').textContent=e.message||String(e)})});
qs('btn-export-all').addEventListener('click', function(){downloadLogs('all').catch(function(e){qs('status').textContent=e.message||String(e)})});
qs('btn-back').addEventListener('click', function(){location.href='/'});
qs('btn-settings').addEventListener('click', function(){location.href='/settings'});
qs('btn-theme').addEventListener('click', function(){applyTheme(document.body.classList.contains('theme-light')?'dark':'light')});
applyTheme(loadTheme());
loadLogs().catch(function(e){qs('status').textContent=e.message||String(e)});
</script></body></html>"""

def _build_oobe_html() -> str:
    return """<!doctype html><html lang="zh"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>初始化 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}:root{--font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;--bg:#f3f2f1;--card:#fff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01}
@media(prefers-color-scheme:dark){:root{--bg:#201f1e;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;--muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c}}
html,body{margin:0;min-height:100dvh;background:linear-gradient(180deg,var(--bg),var(--card2));color:var(--txt);font-family:var(--font-ui)}body{display:grid;place-items:center;padding:22px}
.card{width:min(720px,100%);border:1px solid var(--border);background:var(--card);border-radius:4px;box-shadow:0 16px 34px rgba(0,0,0,.16);padding:24px}
h1{margin:0 0 8px;font:700 28px/1.1 var(--font-ui)}.desc{color:var(--muted);line-height:1.55;margin-bottom:18px}.reason{border:1px solid color-mix(in srgb,var(--warn) 45%,var(--border));background:color-mix(in srgb,var(--warn) 10%,var(--card2));border-radius:4px;padding:10px 12px;margin-bottom:16px}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}.field{display:grid;gap:7px}.field.full{grid-column:1/-1}label{font:700 12px/1 var(--font-ui);color:var(--muted)}
input,select{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 12px;font:600 14px/1.2 var(--font-ui)}input:focus,select:focus{outline:none;border-color:var(--blue)}
.actions{display:flex;gap:10px;flex-wrap:wrap;justify-content:flex-end;margin-top:18px}.btn{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:0 16px;font:700 14px/1 var(--font-ui);cursor:pointer}.btn.primary{border-color:var(--blue);background:var(--blue);color:#fff}.status{margin-top:12px;color:var(--muted);white-space:pre-wrap}.status.err{color:var(--warn)}.micro{font-size:12px;color:var(--muted);line-height:1.5}@media(max-width:720px){body{padding:10px}.grid{grid-template-columns:1fr}.card{padding:18px}}
</style></head><body><main class="card">
<h1>Light RID Scanner 初始化</h1>
<div class="desc">程序需要绑定一张固定无线网卡。不会再自动递增选择其他网卡，避免多网卡环境下抓错设备。</div>
<div class="reason" id="reason">正在读取状态...</div>
<div class="grid">
  <div class="field full"><label>默认网卡</label><select id="iface"><option value="">正在扫描...</option></select><div class="micro">如果没有网卡，请插入支持 monitor 的无线网卡后刷新。</div></div>
  <div class="field"><label>RID 信道</label><input id="channel" type="number" min="1" max="196" value="6"><div class="micro">默认 CH6，通常无需修改。</div></div>
  <div class="field"><label>基站名称</label><input id="base-name" value="基站"></div>
  <div class="field"><label>基站纬度</label><input id="base-lat" type="number" step="0.000001"></div>
  <div class="field"><label>基站经度</label><input id="base-lon" type="number" step="0.000001"></div>
  <div class="field"><label>网页登录账号</label><input id="username" autocomplete="username" placeholder="可选"></div>
  <div class="field"><label>网页登录密码</label><input id="password" type="password" autocomplete="new-password" placeholder="可选"></div>
</div>
<div class="actions"><button class="btn" id="btn-refresh" type="button">刷新网卡</button><button class="btn" id="btn-location" type="button">读取浏览器位置</button><button class="btn primary" id="btn-save" type="button">保存并进入系统</button></div>
<div id="status" class="status">-</div>
</main><script>
function qs(id){return document.getElementById(id)}function pageHeaders(extra){var h={'X-LightRID-Page':'1'};if(extra){Object.keys(extra).forEach(function(k){h[k]=extra[k]})}return h}function setStatus(t,e){qs('status').textContent=t||'-';qs('status').classList.toggle('err',!!e)}function enc(v){return String(v==null?'':v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;')}var authRedirecting=false;function authExpired(r,d){var e=String((d&&d.error)||'');return r&&r.status===401&&((d&&d.auth_expired)||e==='login required'||e==='auth required')}function redirectLogin(){if(authRedirecting)return;authRedirecting=true;location.href='/login?next=/'}
async function loadStatus(){const r=await fetch('/api/oobe/status',{cache:'no-store',headers:pageHeaders()});const d=await r.json().catch(()=>({}));if(authExpired(r,d)){redirectLogin();throw new Error('login required')}if(!r.ok||d.ok===false)throw new Error(d.error||('HTTP '+r.status));qs('reason').textContent=(d.oobe&&d.oobe.reason)||'需要完成基础配置。';var opts=['<option value="">请选择默认网卡</option>'];(d.interfaces||[]).forEach(function(it){var name=String(it.name||'');if(name)opts.push('<option value="'+enc(name)+'">'+enc(name+' ['+(it.mode||'')+'] '+(it.supports_5g?'5G':'2.4G'))+'</option>')});qs('iface').innerHTML=opts.join('');qs('iface').value=d.selected_iface||'';qs('channel').value=String(d.channel||6);qs('base-name').value=String(d.base_name||'基站');qs('base-lat').value=d.base_lat==null?'':String(d.base_lat);qs('base-lon').value=d.base_lon==null?'':String(d.base_lon);setStatus((d.interfaces||[]).length?'请选择网卡后保存。':'未检测到无线网卡。',!(d.interfaces||[]).length)}
async function save(){var body={iface:qs('iface').value,channel:Number(qs('channel').value||6),base_name:qs('base-name').value,base_lat:qs('base-lat').value,base_lon:qs('base-lon').value,username:qs('username').value,password:qs('password').value};setStatus('正在保存...',false);const r=await fetch('/api/oobe/save',{method:'POST',headers:pageHeaders({'Content-Type':'application/json'}),body:JSON.stringify(body)});const d=await r.json().catch(()=>({}));if(authExpired(r,d)){redirectLogin();throw new Error('login required')}if(!r.ok||d.ok===false)throw new Error(d.error||('HTTP '+r.status));setStatus(d.login_required?'已保存，请先登录。':'已保存，正在进入系统...',false);setTimeout(function(){location.href=String(d.next||'/')},600)}
qs('btn-refresh').addEventListener('click',function(){loadStatus().catch(e=>setStatus(e.message||String(e),true))});qs('btn-save').addEventListener('click',function(){save().catch(e=>setStatus(e.message||String(e),true))});qs('btn-location').addEventListener('click',function(){if(!navigator.geolocation){setStatus('浏览器不支持定位',true);return}navigator.geolocation.getCurrentPosition(function(pos){qs('base-lat').value=String(pos.coords.latitude||'');qs('base-lon').value=String(pos.coords.longitude||'');setStatus('已读取浏览器位置',false)},function(err){setStatus('定位失败: '+(err&&err.message?err.message:err),true)},{enableHighAccuracy:true,timeout:12000,maximumAge:0})});loadStatus().catch(e=>setStatus(e.message||String(e),true));
</script></body></html>"""

def _build_settings_html() -> str:
    return """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>设置 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}
:root{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --muted:#c8c6c4;--blue:#2899f5;--green:#92c353;--warn:#f7630c;--glow:rgba(40,153,245,.12);--soft:rgba(255,255,255,.03);--app-vh:100dvh
}
body.theme-light{
  --bg:#f3f2f1;--bg2:#edebe9;--card:#ffffff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;
  --muted:#605e5c;--blue:#0078d4;--green:#107c10;--warn:#d83b01;--glow:rgba(0,120,212,.10);--soft:rgba(0,0,0,.018)
}
html,body{margin:0;padding:0;background:var(--bg);color:var(--txt);font-family:var(--font-ui)}
body{min-height:var(--app-vh);background:linear-gradient(180deg,var(--bg),var(--bg2) 18%,var(--bg))}
.wrap{width:min(1420px,calc(100vw - 24px));margin:0 auto;padding:clamp(14px,1.8vw,22px) clamp(10px,1.5vw,18px) 30px}
.settings-sticky-head{position:relative;z-index:1;background:linear-gradient(180deg,var(--bg),color-mix(in srgb,var(--bg) 94%,transparent));padding-top:clamp(8px,1.2vw,14px)}
.topbar{display:flex;justify-content:space-between;align-items:center;gap:14px;flex-wrap:wrap;margin-bottom:12px}
.title{font:600 32px/1 var(--font-ui);letter-spacing:.01em}
.sub{color:var(--muted);margin-top:5px;max-width:780px;line-height:1.45}
.actions{display:flex;gap:10px;flex-wrap:wrap}
.btn[disabled]{opacity:.58;cursor:not-allowed;transform:none!important;box-shadow:none!important}
.btn{border:1px solid var(--border);background:var(--card2);color:var(--txt);padding:10px 14px;border-radius:4px;cursor:pointer;font:600 14px/1 var(--font-ui);letter-spacing:0;transition:border-color .14s ease,background-color .14s ease,transform .14s ease,box-shadow .14s ease,color .14s ease;box-shadow:0 1px 2px rgba(0,0,0,.06)}
.btn:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--card2));box-shadow:0 2px 8px var(--glow)}
.btn.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:color-mix(in srgb, var(--warn) 70%, white)}
.btn.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--card2))}
.btn.ghost{background:transparent}
.draft-bar{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;margin:0 auto 12px;padding:10px 12px;border:1px solid var(--border);border-radius:4px;background:var(--card);box-shadow:0 1px 3px rgba(0,0,0,.08)}
.draft-copy{display:grid;gap:4px}
.draft-title{font:600 15px/1.2 var(--font-ui)}
.draft-meta{font-size:12px;color:var(--muted);line-height:1.5}
.draft-actions{display:flex;gap:10px;flex-wrap:wrap}
.tabs{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:3px;padding:3px;border:1px solid var(--border);background:var(--card2);border-radius:4px;margin:0 auto 12px;width:min(680px,100%);box-shadow:0 1px 2px rgba(0,0,0,.05)}
.tab{border:1px solid transparent;background:transparent;color:var(--txt);padding:11px 16px;border-radius:4px;cursor:pointer;font:600 14px/1 var(--font-ui);letter-spacing:0;text-align:center;transition:border-color .14s ease,background-color .14s ease,transform .14s ease,box-shadow .14s ease}
.tab:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 8%, var(--card2));box-shadow:0 2px 8px var(--glow)}
.tab.active{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 12%, var(--card2));box-shadow:inset 0 0 0 1px color-mix(in srgb, var(--blue) 18%, transparent)}
body.theme-light .tabs{background:var(--card2)}
body.theme-light .tab.active{background:color-mix(in srgb, var(--blue) 12%, var(--card2));border-color:var(--blue)}
.panel{display:none}.panel.active{display:block}
.raw-layout{display:grid;grid-template-columns:minmax(260px,.82fr) minmax(0,1.18fr);gap:12px;min-width:0}
.raw-pane{min-width:0;display:grid;gap:10px;align-content:start}
.raw-tree{border:1px solid var(--border);background:var(--card2);border-radius:4px;min-height:460px;max-height:min(72dvh,840px);overflow:auto;padding:10px}
.raw-tree .empty-state{margin:0}
.raw-tree details{margin:0 0 4px 0;padding-left:0}
.raw-tree summary{cursor:pointer;list-style:none;display:flex;align-items:center;gap:6px;padding:6px 8px;border-radius:4px}
.raw-tree summary::-webkit-details-marker{display:none}
.raw-tree summary:hover{background:color-mix(in srgb, var(--blue) 10%, var(--card2))}
.raw-tree .raw-file-btn{display:flex;align-items:center;justify-content:space-between;width:100%;border:1px solid transparent;background:transparent;color:var(--txt);padding:6px 8px;border-radius:4px;cursor:pointer;font:600 13px/1.3 var(--font-ui);text-align:left}
.raw-tree .raw-file-btn:hover{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 8%, var(--card2))}
.raw-tree .raw-file-btn.active{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 14%, var(--card2))}
.raw-tree .raw-dir-child{padding-left:14px;border-left:1px solid var(--border);margin:2px 0 6px 10px}
.raw-main{display:grid;gap:10px;min-width:0}
.raw-meta{display:flex;justify-content:space-between;gap:10px;flex-wrap:wrap;align-items:flex-start;padding:10px 12px;border:1px solid var(--border);border-radius:4px;background:var(--card2)}
.raw-meta .meta-copy{display:grid;gap:4px;min-width:0}
.raw-meta .meta-title{font:600 15px/1.2 var(--font-ui)}
.raw-meta .meta-sub{font-size:12px;color:var(--muted);line-height:1.5;word-break:break-word}
.raw-editor{min-height:54dvh;height:calc(100dvh - 390px);max-height:min(78dvh,920px)}
.raw-lock{padding:14px;border:1px dashed var(--border);border-radius:4px;background:color-mix(in srgb, var(--warn) 6%, var(--card2));display:grid;gap:10px}
.raw-lock strong{font-size:15px}
.raw-toolbar{display:flex;gap:10px;flex-wrap:wrap;justify-content:space-between;align-items:center}
.raw-toolbar .row-actions{justify-content:flex-end}
.passkey-list{display:grid;gap:8px}
.passkey-row{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:10px 12px;border:1px solid var(--border);border-radius:4px;background:var(--card2)}
.passkey-meta{display:grid;gap:4px;min-width:0}
.passkey-title{font:600 14px/1.2 var(--font-ui)}
.passkey-sub{font-size:12px;color:var(--muted);line-height:1.4;word-break:break-word}
.passkey-badges{display:flex;gap:6px;flex-wrap:wrap}
.passkey-badge{font-size:11px;line-height:1;padding:4px 7px;border:1px solid var(--border);border-radius:999px;background:var(--card)}
.visual-grid{display:grid;grid-template-columns:minmax(0,1.12fr) minmax(360px,.88fr);gap:12px}
.stack{display:grid;gap:12px;min-width:0;align-content:start}
.stack-label{font:700 12px/1 var(--font-ui);letter-spacing:0;color:var(--muted);padding:2px 2px 0}
.card{border:1px solid var(--border);border-radius:4px;background:var(--card);padding:14px;box-shadow:0 1px 3px rgba(0,0,0,.08);min-width:0;overflow:hidden;animation:officeFade .16s ease-out both}
.card.dirty{border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 22%, transparent),0 8px 18px var(--glow)}
.card.dirty h2{color:var(--blue)}
.card h2{margin:0;font:600 18px/1 var(--font-ui);letter-spacing:.01em}
.hint{color:var(--muted);font-size:13px;line-height:1.6}
.section-head{display:flex;justify-content:space-between;align-items:flex-start;gap:12px;flex-wrap:wrap}
.section-copy{margin-top:4px;color:var(--muted);font-size:13px;line-height:1.45;max-width:58ch}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.field{display:grid;gap:6px}
.field.full{grid-column:1/-1}
.field label{font:600 12px/1.15 var(--font-ui);letter-spacing:.01em;color:var(--muted)}
.field input,.field select,.field textarea{width:100%;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 12px;font:600 14px/1.35 var(--font-ui);transition:border-color .14s ease,box-shadow .14s ease,background-color .14s ease}
.field input[type="checkbox"],input[type="checkbox"]{width:16px;height:16px;min-width:16px;flex:0 0 auto;padding:0;margin:0;accent-color:var(--blue)}
.field input:not([type="checkbox"]),.field select,.token-actions input{height:42px}
.field-inline .btn,.token-actions .btn{height:42px}
.field input:focus,.field select:focus,.field textarea:focus{outline:none;border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 38%, transparent)}
.field textarea{min-height:440px;resize:vertical;font-family:var(--font-mono);font-size:13px}
.field-inline{display:grid;grid-template-columns:minmax(0,1fr) auto auto;gap:8px;align-items:center}
.field-inline input[disabled]{opacity:.9;background:color-mix(in srgb, var(--card2) 92%, black)}
.checks{display:flex;flex-wrap:wrap;gap:12px}
.checks label{display:flex;align-items:center;gap:8px;font-size:15px;color:var(--txt)}
.checks.pref-checks{display:grid;grid-template-columns:1fr;gap:10px}
.row-actions{display:flex;gap:10px;flex-wrap:wrap}
.token-actions{display:flex;gap:10px;flex-wrap:wrap;align-items:center;min-width:0}
.token-actions input{flex:1 1 260px;min-width:0}
.sso-link-list{margin-top:10px}
.sso-link-options{display:grid;grid-template-columns:minmax(120px,.8fr) minmax(110px,.7fr) auto;gap:10px;align-items:end;margin-top:10px}
.sso-link-options .field{min-width:0}
.sso-single-use{height:42px;display:flex;align-items:center;gap:8px;font-size:13px;color:var(--txt)}
.sso-link-row{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:10px;align-items:center}
.sso-link-row .btn{white-space:nowrap}
.sso-link-meta{min-width:0;overflow:hidden}
.sso-link-title{font:700 13px/1.25 var(--font-ui);color:var(--txt);display:flex;gap:8px;align-items:center;min-width:0;flex-wrap:wrap}
.sso-link-badge{font:700 11px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:3px 5px;background:var(--card)}
.sso-link-badge.bad{color:var(--warn);border-color:color-mix(in srgb,var(--warn) 45%,var(--border))}
.field.hidden{display:none}
.policy-grid{display:grid;grid-template-columns:150px minmax(0,1fr);gap:10px;align-items:end}
.disabled-block{opacity:.52;filter:saturate(.65);pointer-events:none}
.status{margin-top:12px;color:#8fd0a8;white-space:pre-wrap;line-height:1.65}
.status.err{color:#ff9b9b}
.secret-note,.micro{font-size:12px;color:var(--muted);line-height:1.55}
.micro{margin-top:6px}
.list-head{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:10px}
.list-wrap{display:grid;gap:8px}
.list-row{border:1px solid var(--border);border-radius:4px;padding:10px;background:var(--card2)}
.access-group{display:grid;gap:12px}
.access-subgrid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.access-subcard{border:1px solid var(--border);border-radius:4px;background:var(--card2);padding:12px;display:grid;gap:12px;min-width:0}
.access-subcard.full{grid-column:1/-1}
.access-subhead{display:flex;justify-content:space-between;gap:10px;align-items:flex-start;flex-wrap:wrap}
.access-subtitle{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.access-subcopy{margin-top:4px;color:var(--muted);font-size:12px;line-height:1.5}
.access-subcard .list-row,.access-subcard .empty-state{background:var(--card)}
.api-token-list{display:grid;gap:8px;max-height:420px;overflow:auto;padding-right:4px}
.api-token-row{border:1px solid var(--border);border-radius:4px;background:var(--card);padding:10px;display:grid;gap:10px;min-width:0}
.api-token-head{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px;align-items:center}
.api-token-name{font:700 13px/1.25 var(--font-ui);min-width:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.api-token-badges{display:flex;gap:6px;flex-wrap:wrap;align-items:center}
.api-token-badge{font:700 11px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:4px 6px;background:var(--card2);white-space:nowrap}
.api-token-badge.bad{color:var(--warn);border-color:color-mix(in srgb,var(--warn) 45%,var(--border))}
.api-token-create-grid{display:grid;grid-template-columns:minmax(150px,1fr) minmax(130px,.65fr) minmax(120px,.6fr) auto auto;gap:8px;align-items:end}
.api-token-grid{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px;align-items:center}
.api-token-grid .field{min-width:0}
.api-token-grid input:not([type="checkbox"]),.api-token-grid select,.api-token-create-grid input:not([type="checkbox"]),.api-token-create-grid select{height:38px}
.model-update-row{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:10px;align-items:center}
.model-editor{display:grid;gap:10px;margin-top:10px}
.model-editor-toolbar{display:grid;grid-template-columns:minmax(0,1fr) auto auto;gap:8px;align-items:center}
.model-editor-toolbar input{height:42px}
.model-map-list{display:grid;gap:8px;max-height:360px;overflow:auto;padding-right:4px}
.model-map-row{display:grid;grid-template-columns:minmax(100px,.42fr) minmax(0,1fr) auto;gap:8px;align-items:center;border:1px solid var(--border);border-radius:4px;background:var(--card2);padding:8px}
.model-map-row input{height:38px;border:1px solid var(--border);background:var(--card);color:var(--txt);border-radius:4px;padding:8px 10px;font:600 13px/1.25 var(--font-ui);min-width:0}
.model-map-row input.model-prefix{font-family:var(--font-mono);text-transform:uppercase}
.model-map-empty{padding:16px;border:1px dashed var(--border);border-radius:4px;color:var(--muted);background:var(--card2)}
.metric-toolbar{display:flex;align-items:center;gap:8px;flex-wrap:wrap;margin-top:12px}
.metric-toolbar .btn.active{border-color:var(--blue);background:color-mix(in srgb,var(--blue) 12%,var(--card2))}
.metric-retention{display:grid;grid-template-columns:auto 82px auto;gap:8px;align-items:center;margin-left:auto;color:var(--muted);font-size:12px}
.metric-retention input{height:36px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:7px 9px;font:600 13px/1 var(--font-ui)}
.metric-list{display:grid;gap:12px;margin-top:12px}
.metric-item{display:grid;grid-template-columns:minmax(0,1fr) auto;grid-template-areas:"label value" "chart chart";gap:9px;align-items:center;border:1px solid var(--border);border-radius:4px;background:var(--card2);padding:10px 12px;min-width:0}
.metric-label{grid-area:label;display:flex;align-items:center;gap:7px;min-width:0;font:600 13px/1.2 var(--font-ui)}
.metric-label i{width:12px;height:12px;border-radius:50%;display:inline-block;flex:0 0 auto}
.metric-spark-wrap{grid-area:chart;position:relative;height:136px;min-width:0;cursor:crosshair;touch-action:none;user-select:none}
.metric-spark-wrap.dragging{cursor:grabbing}
.metric-spark{width:100%;height:100%;display:block}
.metric-chart-tip{position:absolute;z-index:3;display:none;max-width:240px;transform:translate(-50%,calc(-100% - 10px));padding:7px 9px;border:1px solid color-mix(in srgb,var(--blue) 46%,var(--border));border-radius:4px;background:color-mix(in srgb,var(--card) 94%,transparent);box-shadow:0 12px 28px rgba(0,0,0,.24);font:600 12px/1.45 var(--font-mono);color:var(--txt);white-space:pre-line;pointer-events:none}
.metric-chart-tip.below{transform:translate(-50%,10px)}
.metric-value{grid-area:value;font:700 13px/1.2 var(--font-mono);text-align:right;color:var(--txt)}
.metric-zoom{display:grid;grid-template-columns:auto minmax(120px,1fr) auto;gap:8px;align-items:center;margin-top:10px;color:var(--muted);font-size:12px}
.metric-zoom input{width:100%}
.hook-layout{display:grid;grid-template-columns:minmax(110px,.7fr) minmax(0,1.5fr) 88px auto;gap:10px;align-items:end;min-width:0}
.zone-layout{display:grid;grid-template-columns:minmax(120px,1.2fr) 86px repeat(4,minmax(0,1fr)) auto;gap:10px;align-items:end;min-width:0}
.hook-layout>.field,.zone-layout>.field{min-width:0}
.empty-state{padding:14px;border:1px dashed var(--border);border-radius:4px;color:var(--muted);background:var(--card2)}
.security-alert{display:none;gap:8px;margin-top:14px;padding:12px;border:1px solid color-mix(in srgb,var(--warn) 46%,var(--border));border-radius:4px;background:color-mix(in srgb,var(--warn) 10%,var(--card2));color:var(--txt)}
.security-alert.show{display:grid}
.security-alert.ok{border-color:color-mix(in srgb,var(--green) 38%,var(--border));background:color-mix(in srgb,var(--green) 9%,var(--card2))}
.security-alert-title{font:700 14px/1.2 var(--font-ui);color:var(--txt)}
.security-alert-copy{font-size:13px;line-height:1.55;color:var(--muted)}
.security-alert.warn .security-alert-copy{color:color-mix(in srgb,var(--warn) 58%,white)}
.security-alert-actions{display:flex;gap:10px;flex-wrap:wrap}
.stats-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.stat{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
.stat .k{font:600 12px/1 var(--font-ui);color:var(--muted);letter-spacing:.01em}
.stat .v{margin-top:8px;font:600 20px/1.1 var(--font-ui)}
.stat .v.ip-lines{font:600 13px/1.45 var(--font-mono);display:grid;gap:5px;max-width:100%}
.ip-line{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px;align-items:center;min-width:0}
.ip-text{display:block;min-width:0;max-width:100%;white-space:nowrap;overflow-x:auto;overflow-y:hidden;text-overflow:clip;scrollbar-width:thin}
.ip-len{font:600 11px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:3px 5px;background:var(--card)}
.settings-ap-scroll{max-height:min(42vh,420px);overflow:auto;padding-right:4px}
.settings-ap-row-grid{display:grid;grid-template-columns:46px minmax(120px,.9fr) minmax(0,1.2fr) 86px;gap:10px;align-items:center;min-width:0}
.settings-ap-row-grid>*{min-width:0}
.settings-ap-row-grid .clip{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
details.advanced{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
details.advanced summary{cursor:pointer;font:600 14px/1.2 var(--font-ui);letter-spacing:.01em}
.split-actions{display:flex;justify-content:space-between;gap:10px;flex-wrap:wrap;align-items:center}
.modal-mask{position:fixed;inset:0;background:rgba(4,8,14,.66);backdrop-filter:blur(8px);display:none;align-items:center;justify-content:center;padding:20px;z-index:60}
.modal-mask.show{display:flex}
.modal-card{width:min(480px,100%);border:1px solid var(--border);border-radius:4px;background:var(--card);padding:18px;box-shadow:0 18px 32px rgba(0,0,0,.18)}
.modal-card.wide{width:min(900px,100%)}
.modal-card h3{margin:0 0 10px;font:600 20px/1 var(--font-ui)}
.one-time-secret{font:600 12px/1.55 var(--font-mono);word-break:break-all;border:1px solid var(--border);background:var(--card2);border-radius:4px;padding:12px;margin-top:12px;max-height:160px;overflow:auto}
.toast-stack{position:fixed;right:18px;bottom:18px;display:grid;gap:10px;z-index:72;width:min(420px,calc(100vw - 28px));pointer-events:none}
.toast{border:1px solid var(--border);border-radius:4px;background:color-mix(in srgb, var(--card) 96%, transparent);padding:12px 14px;box-shadow:0 14px 28px rgba(0,0,0,.18);opacity:0;transform:translateY(6px);transition:opacity .18s ease,transform .18s ease,border-color .18s ease;background-clip:padding-box;pointer-events:auto}
.toast.show{opacity:1;transform:translateY(0)}
.toast.ok{border-color:color-mix(in srgb, var(--green) 38%, var(--border))}
.toast.warn{border-color:color-mix(in srgb, var(--warn) 42%, var(--border))}
.toast-title{font:600 14px/1.2 var(--font-ui);margin-bottom:5px}
.toast-text{font-size:13px;line-height:1.5;color:var(--muted);white-space:pre-wrap}
@keyframes officeFade{from{opacity:0;transform:translateY(4px)}to{opacity:1;transform:none}}
@media (max-width:1360px){
  .hook-layout{grid-template-columns:repeat(2,minmax(0,1fr))}
  .api-token-create-grid{grid-template-columns:repeat(3,minmax(0,1fr))}
  .zone-layout{grid-template-columns:repeat(3,minmax(0,1fr))}
  .hook-layout .field:last-child,.api-token-create-grid .field:last-child,.zone-layout .field:last-child{grid-column:1/-1}
}
@media (max-width:1200px){.visual-grid{grid-template-columns:1fr}.access-subgrid,.hook-layout,.api-token-head,.api-token-create-grid,.api-token-grid,.policy-grid,.zone-layout,.field-inline,.model-update-row,.model-editor-toolbar,.model-map-row,.sso-link-options{grid-template-columns:1fr}.stats-grid{grid-template-columns:1fr}.metric-retention{margin-left:0}}
@media (max-width:700px){
  .wrap{width:min(100vw - 12px,1420px);padding:10px 6px 18px}
  .topbar,.draft-bar{gap:10px}
  .actions,.draft-actions{width:100%}
  .actions .btn,.draft-actions .btn{flex:1 1 140px}
  .card{padding:14px}
  .metric-item{grid-template-columns:minmax(0,1fr) auto;gap:7px}
  .metric-spark-wrap{height:118px}
  .toast-stack{right:10px;left:10px;bottom:10px;width:auto}
}
</style></head><body><div class="wrap">
  <div class="settings-sticky-head">
  <div class="topbar">
    <div>
      <div class="title">设置</div>
      <div class="sub">扫描采集、地图、通知、访问控制和运行工具集中在本页。</div>
    </div>
    <div class="actions">
      <button class="btn" id="btn-back" type="button">返回主页</button>
      <button class="btn" id="btn-logs" type="button">日志</button>
      <button class="btn ghost" id="btn-logout" type="button">登出</button>
      <button class="btn" id="btn-theme" type="button">浅色</button>
      <button class="btn" id="btn-reload-view" type="button">刷新</button>
    </div>
  </div>
  <div class="draft-bar">
    <div class="draft-copy">
      <div class="draft-title" id="draft-title">当前没有未保存修改</div>
      <div class="draft-meta" id="draft-meta">未保存改动按配置分组标记；测试结果独立于配置文件。</div>
    </div>
    <div class="draft-actions">
      <button class="btn" id="btn-test-visual" type="button" disabled>测试</button>
      <button class="btn warn" id="btn-save-visual" type="button" disabled>测试并保存</button>
      <button class="btn ghost" id="btn-save-visual-direct" type="button">直接保存</button>
    </div>
  </div>
  <div class="tabs">
    <button class="tab active" data-tab="visual" type="button">配置面板</button>
    <button class="tab" data-tab="raw" type="button">原始配置</button>
  </div>
  </div>
  <div class="panel active" data-tab="visual">
    <div class="visual-grid">
      <div class="stack">
        <div class="stack-label">核心配置</div>
        <div class="card" data-card-key="capture">
          <div class="section-head">
            <div>
              <h2>采集</h2>
              <div class="section-copy">采集网卡、RID 信道、刷新节奏、历史缓存和识别库来源。</div>
            </div>
          </div>
          <div class="grid" style="margin-top:14px">
            <div class="field"><label>默认网卡</label><select id="cfg-iface"><option value="">未绑定</option></select></div>
            <div class="field">
              <label>固定信道</label>
              <div class="field-inline">
                <input id="cfg-channel" type="number" min="1" max="196" disabled>
                <button class="btn ghost" id="btn-channel-edit" type="button">编辑</button>
                <button class="btn ghost" id="btn-channel-reset" type="button">默认</button>
              </div>
              <div class="micro" id="channel-hint" style="display:none"></div>
            </div>
            <div class="field"><label>日志刷新间隔(s)</label><input id="cfg-time" type="number" step="0.1"></div>
            <div class="field"><label>最短重复间隔(s)</label><input id="cfg-min-gap" type="number" step="0.1"></div>
            <div class="field"><label>信号变化阈值</label><input id="cfg-rssi-delta" type="number"></div>
            <div class="field full"><label>模型映射文件</label><input id="cfg-model-map" type="text"></div>
            <div class="field full" data-card-key="capture">
              <label>识别库在线更新</label>
              <div class="model-update-row">
                <label><input id="cfg-model-update-enabled" type="checkbox"> 自动更新</label>
                <input id="cfg-model-update-url" type="text" placeholder="留空使用官方源">
                <button class="btn" id="btn-model-update-now" type="button">立即更新</button>
              </div>
              <div class="micro" id="model-update-state">本地识别库可从官方源或自定义地址同步。</div>
              <div class="model-update-row" style="margin-top:10px">
                <label><input id="cfg-app-update-enabled" type="checkbox"> 启动自动检查版本</label>
                <div class="micro" id="app-update-state">当前版本与最新版本尚未检查。</div>
                <button class="btn ghost" id="btn-app-update-check" type="button">手动检查版本</button>
              </div>
              <div class="row-actions" style="margin-top:10px"><button class="btn ghost" id="btn-model-map-open" type="button">编辑识别库</button></div>
            </div>
            <div class="field full"><label>历史缓存文件</label><input id="cfg-history-file" type="text"></div>
          </div>
          <div class="checks" style="margin-top:14px">
            <label><input id="cfg-heal" type="checkbox"> 自愈恢复</label>
            <label><input id="cfg-rssi-change" type="checkbox"> 信号变化时更新</label>
            <label><input id="cfg-payload-change" type="checkbox"> 数据变化时更新</label>
            <label><input id="cfg-debug" type="checkbox"> 调试日志</label>
          </div>
          <details class="advanced" style="margin-top:14px">
            <summary>高级采集参数</summary>
            <div class="grid" style="margin-top:14px">
              <div class="field"><label>2.4G 驻留(ms)</label><input id="cfg-dwell2g" type="number"></div>
              <div class="field"><label>5G 驻留(ms)</label><input id="cfg-dwell5g" type="number"></div>
              <div class="field"><label>切换稳定等待(ms)</label><input id="cfg-settle" type="number"></div>
              <div class="field"><label>命中驻留(ms)</label><input id="cfg-hit-dwell" type="number"></div>
              <div class="field"><label>命中上限(ms)</label><input id="cfg-hit-cap" type="number"></div>
            </div>
            <div class="checks" style="margin-top:14px">
              <label><input id="cfg-hop" type="checkbox"> 自动跳频</label>
              <label><input id="cfg-hop5g" type="checkbox"> 跳频含 5G</label>
              <label><input id="cfg-fast" type="checkbox"> 扫描 WiFi 快传</label>
            </div>
          </details>
        </div>
        <div class="card" data-card-key="map">
          <div class="section-head">
            <div>
              <h2>地图与基站</h2>
              <div class="section-copy">基站坐标、地图默认视角、航向参考和自动回中参数。</div>
            </div>
          </div>
          <div class="grid">
            <div class="field"><label>基站名称</label><input id="cfg-base-name" type="text"></div>
            <div class="field"><label>DJI 查询地址</label><input id="cfg-dji-url" type="text"></div>
            <div class="field"><label>基站纬度</label><input id="cfg-base-lat" type="number" step="0.000001"></div>
            <div class="field"><label>基站经度</label><input id="cfg-base-lon" type="number" step="0.000001"></div>
            <div class="field"><label>默认缩放</label><input id="cfg-base-zoom" type="number" min="3" max="30"></div>
            <div class="field"><label>参考航向(°)</label><input id="cfg-heading-ref" type="number" step="0.1"></div>
            <div class="field"><label>自动回中冷却(s)</label><input id="cfg-map-idle" type="number" min="5" max="600"></div>
            <div class="field full">
              <label>定位</label>
              <div class="row-actions">
                <button class="btn" id="btn-browser-loc" type="button">读取浏览器位置</button>
                <button class="btn ghost" id="btn-clear-base-loc" type="button">清空基站坐标</button>
              </div>
              <div class="micro" id="base-geo-hint">浏览器定位能力由当前访问协议和浏览器权限决定。</div>
            </div>
          </div>
        </div>
        <div class="card" data-card-key="zones">
          <div class="list-head">
            <div>
              <h2>报警区域</h2>
              <div class="section-copy">矩形报警区域由 A/B 两组经纬度边界组成。</div>
            </div>
            <button class="btn" id="btn-zone-add" type="button">添加区域</button>
          </div>
          <div id="zone-list" class="list-wrap"></div>
        </div>
        <div class="card access-group" data-card-key="access">
          <div class="section-head">
            <div>
              <h2>通知与访问控制</h2>
              <div class="section-copy">通知发送、网页会话、临时登录链接、外部 API Token 和访问白名单集中在这里。</div>
            </div>
          </div>
          <div class="access-subgrid">
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">通知通道</div>
                  <div class="access-subcopy">企业微信机器人通道、通知开关和发送节奏。</div>
                </div>
                <button class="btn" id="btn-hook-add" type="button">添加通道</button>
              </div>
              <div id="wecom-list" class="list-wrap"></div>
              <div class="grid">
                <div class="field"><label>重上线冷却(s)</label><input id="cfg-reonline" type="number"></div>
                <div class="field"><label>通知超时(s)</label><input id="cfg-send-timeout" type="number"></div>
              </div>
              <div class="checks">
                <label><input id="cfg-notify-enabled" type="checkbox"> 启用企业微信通知</label>
                <label><input id="cfg-notify-reonline" type="checkbox"> 允许重上线通知</label>
              </div>
            </div>
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">网页登录</div>
                  <div class="access-subcopy">控制设置页和内置页面的账号密码登录会话。</div>
                </div>
              </div>
              <div class="grid">
                <div class="field"><label>登录标题</label><input id="cfg-auth-realm" type="text"><div class="micro">显示在登录框和认证域。</div></div>
                <div class="field"><label>会话有效期(min)</label><input id="cfg-auth-ttl" type="number" min="1" max="10080" step="1"><div class="micro">范围 1 分钟到 7 天。</div></div>
                <div class="field"><label>网页登录账号</label><input id="cfg-auth-user" type="text" placeholder="留空即不修改"></div>
                <div class="field"><label>网页登录密码</label><input id="cfg-auth-pass" type="password" placeholder="留空即不修改"></div>
              </div>
              <div class="checks">
                <label><input id="cfg-auth-enabled" type="checkbox"> 启用网页登录鉴权</label>
              </div>
              <div class="checks">
                <label><input id="cfg-auth-method-password" type="checkbox"> 账号密码登录</label>
                <label><input id="cfg-auth-method-passkey" type="checkbox"> PassKey 登录</label>
                <label><input id="cfg-auth-method-sso" type="checkbox"> SSO URL 登录</label>
              </div>
              <div class="micro" id="auth-method-state">至少保留一种网页登录方式；关闭账号密码直接登录后，账号密码仍用于设置页二次确认。</div>
            </div>
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">通行密钥登录</div>
                  <div class="access-subcopy">为网页登录账号绑定浏览器通行密钥，支持一键登录。</div>
                </div>
              </div>
              <div class="grid">
                <div class="field full"><label>通行密钥名称</label><input id="cfg-passkey-name" type="text" placeholder="留空即自动命名"><div class="micro">用于区分不同设备或浏览器。</div></div>
              </div>
              <div class="row-actions">
                <button class="btn" id="btn-passkey-add" type="button">验证并添加</button>
              </div>
              <div class="micro" id="passkey-state">完成网页登录账号和密码配置后，可在这里添加通行密钥。</div>
              <div id="passkey-list" class="passkey-list"></div>
            </div>
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">SSO 登录链接</div>
                  <div class="access-subcopy">为内置页面生成带有效期和单次登录控制的登录链接；过期记录保留。</div>
                </div>
              </div>
              <div class="token-actions">
                <input id="login-link-name" type="text" placeholder="链接名称">
                <button class="btn" id="btn-login-link-create" type="button">生成</button>
              </div>
              <div class="sso-link-options">
                <div class="field"><label>有效期</label><select id="login-link-expire-mode">
                  <option value="86400">24 小时</option>
                  <option value="3600">1 小时</option>
                  <option value="604800">7 天</option>
                  <option value="never">无限时间</option>
                  <option value="custom">自定义分钟</option>
                </select></div>
                <div class="field hidden" id="login-link-custom-field"><label>自定义有效期(min)</label><input id="login-link-ttl-min" type="number" min="1" max="5256000" step="1" value="1440"></div>
                <label class="sso-single-use"><input id="login-link-single-use" type="checkbox"> 单次登录</label>
              </div>
              <div class="micro" id="login-link-state">SSO 链接由校验码、有效期和单次登录状态控制；过期记录保留在列表。</div>
              <div id="login-link-list" class="list-wrap sso-link-list"></div>
            </div>
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">API Token</div>
                  <div class="access-subcopy">外部 API Token 随机生成，只在创建成功时显示一次。</div>
                </div>
              </div>
              <div class="api-token-create-grid">
                <div class="field"><label>名称</label><input id="api-token-new-name" type="text" placeholder="Token 名称"></div>
                <div class="field"><label>有效期</label><select id="api-token-new-expire-mode">
                  <option value="86400">24 小时</option>
                  <option value="3600">1 小时</option>
                  <option value="604800">7 天</option>
                  <option value="never">无限时间</option>
                  <option value="custom">自定义分钟</option>
                </select></div>
                <div class="field hidden" id="api-token-custom-field"><label>自定义(min)</label><input id="api-token-new-ttl-min" type="number" min="1" max="5256000" step="1" value="1440"></div>
                <label class="sso-single-use"><input id="api-token-new-single-use" type="checkbox"> 单次使用</label>
                <div class="field"><label>&nbsp;</label><button class="btn" id="btn-api-token-add" type="button">验证并生成</button></div>
              </div>
              <div id="api-token-list" class="api-token-list"></div>
              <div class="checks">
                <label><input id="cfg-api-enabled" type="checkbox"> 启用外部 API</label>
              </div>
            </div>
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">API 白名单</div>
                  <div class="access-subcopy">限制外部 API 来源地址</div>
                </div>
              </div>
              <div id="api-whitelist-block">
                <div class="policy-grid">
                  <div class="field"><label>模式</label><select id="cfg-api-whitelist-mode"><option value="allow">白名单</option><option value="deny">黑名单</option></select></div>
                  <div class="checks"><label><input id="cfg-api-whitelist-enabled" type="checkbox"> 启用 API 访问规则</label></div>
                </div>
                <div class="field full"><label>地址列表</label><textarea id="cfg-api-whitelist" spellcheck="false" style="min-height:140px"></textarea><div class="micro">每行一个 IP 或 CIDR。</div></div>
              </div>
            </div>
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">网页访问规则</div>
                  <div class="access-subcopy">限制设置页、主页和内置页面的访问来源。</div>
                </div>
              </div>
              <div class="policy-grid">
                <div class="field"><label>模式</label><select id="cfg-web-access-mode"><option value="allow">白名单</option><option value="deny">黑名单</option></select></div>
                <div class="checks"><label><input id="cfg-web-access-enabled" type="checkbox"> 启用网页访问规则</label></div>
              </div>
              <div class="field full"><label>地址列表</label><textarea id="cfg-web-access-list" spellcheck="false" style="min-height:120px"></textarea><div class="micro">每行一个 IP 或 CIDR；拒绝时页面返回 403。</div></div>
            </div>
          </div>
          <div class="secret-note" id="secret-state">通知、登录、Token 和外部 API 状态摘要。</div>
          <div id="status-visual" class="status">-</div>
        </div>
      </div>
      <div class="stack">
        <div class="stack-label">运行与页面</div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>主机状态</h2>
              <div class="section-copy">当前资源占用、网络地址、默认网卡和采集状态。</div>
            </div>
            <button class="btn ghost" id="btn-refresh-host" type="button">刷新状态</button>
          </div>
          <div id="host-stats" class="stats-grid" style="margin-top:14px"></div>
          <div id="host-meta" class="micro">-</div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn" id="btn-open-hw" type="button">打开硬件助手</button>
            <button class="btn" id="btn-diagnostic-export" type="button">导出质量分析包</button>
          </div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>权限与 systemd 服务</h2>
              <div class="section-copy">检查当前运行身份，使用 rid 专用账号运行服务，并保留采集所需的网络能力。</div>
            </div>
          </div>
          <div id="runtime-security-alert" class="security-alert">
            <div class="security-alert-title" id="runtime-security-title">权限检测</div>
            <div class="security-alert-copy" id="runtime-security-copy">正在读取运行权限...</div>
            <div class="security-alert-actions">
              <button class="btn warn" id="btn-security-repair" type="button">一键修复</button>
            </div>
          </div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn ghost" id="btn-service-refresh" type="button">刷新服务状态</button>
            <button class="btn" id="btn-service-register" type="button">注册/更新服务</button>
            <button class="btn" id="btn-iw-install" type="button">安装 iw</button>
          </div>
          <div class="micro" style="margin-top:10px">修复会创建/确认 rid 账号、授予配置与缓存写权限，并把服务注册为 rid + CAP_NET_ADMIN/CAP_NET_RAW；网页输入的 sudo 密码只用于本次请求，不会保存。</div>
          <div id="status-system-service" class="status">正在读取服务状态...</div>
        </div>
        <div class="card" data-card-key="metrics">
          <div class="section-head">
            <div>
              <h2>节点负载</h2>
              <div class="section-copy">CPU、内存、温度、系统负载和 AP 数的历史曲线。</div>
            </div>
          </div>
          <div class="metric-toolbar">
            <button class="btn ghost metric-window active" data-window="12h" type="button">12小时</button>
            <button class="btn ghost metric-window" data-window="24h" type="button">24小时</button>
            <button class="btn ghost metric-window" data-window="7d" type="button">7天</button>
            <label class="metric-retention"><span>保留</span><input id="cfg-metrics-retention" type="number" min="1" max="90" step="1"><span>天</span></label>
          </div>
          <div class="grid" style="margin-top:12px">
            <div class="field">
              <label>温度数据来源</label>
              <select id="cfg-metrics-temp-source">
                <option value="auto">自动（优先 vcgencmd）</option>
                <option value="vcgencmd">仅 vcgencmd</option>
                <option value="thermal_zone">仅 /sys/class/thermal</option>
                <option value="hwmon">仅 /sys/class/hwmon</option>
                <option value="off">关闭温度采集</option>
              </select>
              <div class="micro">节点温度会写入主机状态和温度曲线；关闭后显示为空值。</div>
            </div>
          </div>
          <div class="metric-list" id="metrics-list">
            <div class="metric-item" data-metric="cpu"><div class="metric-label"><i style="background:#2899f5"></i>CPU</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="cpu"></canvas></div><div class="metric-value" id="metric-value-cpu">—</div></div>
            <div class="metric-item" data-metric="mem"><div class="metric-label"><i style="background:#92c353"></i>内存</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="mem"></canvas></div><div class="metric-value" id="metric-value-mem">—</div></div>
            <div class="metric-item" data-metric="temp"><div class="metric-label"><i style="background:#f7630c"></i>温度</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="temp"></canvas></div><div class="metric-value" id="metric-value-temp">—</div></div>
            <div class="metric-item" data-metric="load"><div class="metric-label"><i style="background:#c19c00"></i>负载</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="load"></canvas></div><div class="metric-value" id="metric-value-load">—</div></div>
            <div class="metric-item" data-metric="ap"><div class="metric-label"><i style="background:#8764b8"></i>AP数</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="ap"></canvas></div><div class="metric-value" id="metric-value-ap">—</div></div>
          </div>
          <label class="metric-zoom"><span>缩放</span><input id="metrics-zoom" type="range" min="1" max="100" step="1" value="1"><span id="metrics-zoom-value">1x</span></label>
          <div id="status-metrics" class="micro">-</div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>主页工具</h2>
              <div class="section-copy">主页列表冻结、浏览器通知、历史数据和初始化入口。</div>
            </div>
          </div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn" id="btn-home-freeze" type="button">返回主页并冻结列表</button>
            <button class="btn" id="btn-settings-web-notify" type="button">网页通知</button>
            <button class="btn warn" id="btn-settings-clear-history" type="button">清空历史</button>
            <button class="btn" id="btn-oobe-simple" type="button">简化 OOBE</button>
            <button class="btn" id="btn-oobe-full" type="button">完整 OOBE</button>
          </div>
          <div id="status-home-actions" class="status">-</div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>许可协议</h2>
              <div class="section-copy">查看当前 EULA 阅读确认状态；撤回后会重新进入首次运行许可确认。</div>
            </div>
          </div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn" id="btn-eula-view" type="button">查看 EULA</button>
            <button class="btn warn" id="btn-eula-revoke" type="button">撤回同意</button>
          </div>
          <div id="status-eula" class="status">-</div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>浏览器偏好</h2>
              <div class="section-copy">实时轨迹和 2 小时轨迹过滤保存在当前浏览器。</div>
            </div>
          </div>
          <div class="checks pref-checks" style="margin-top:14px">
            <label><input id="pref-realtime-track" type="checkbox"> 实时轨迹</label>
            <label><input id="pref-track-2h" type="checkbox"> 只显示近 2 小时轨迹</label>
            <label><input id="pref-new-firmware-parser" type="checkbox"> 显示 RID 包解析结果</label>
          </div>
          <div class="micro">只控制当前浏览器显示；后台仍按旧 ODID 和新版 DJI Beacon 两套规则分别解析。默认开启。</div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>实时 AP</h2>
              <div class="section-copy">附近 AP 列表和最近扫描日志，内容来自运行时缓存。</div>
            </div>
            <button class="btn ghost" id="btn-refresh-runtime" type="button">刷新</button>
          </div>
          <div id="settings-ap-list" class="list-wrap" style="margin-top:14px"></div>
          <div class="field full" style="margin-top:14px"><label>扫描日志</label><textarea id="settings-runtime-log" readonly spellcheck="false" style="min-height:220px"></textarea></div>
          <div id="status-runtime" class="status">-</div>
        </div>
      </div>
    </div>
  </div>
  <div class="panel" data-tab="raw">
    <div class="card">
      <div class="raw-toolbar">
        <div>
          <h2>原始配置</h2>
          <div class="section-copy">浏览配置目录树、切换文件、编辑保存和删除配置文件。进入前需要先验证网页登录密码。</div>
        </div>
        <div class="row-actions">
          <button class="btn" id="btn-load-raw" type="button">刷新目录</button>
          <button class="btn warn" id="btn-save-raw" type="button">保存当前文件</button>
          <button class="btn warn" id="btn-delete-raw" type="button">删除当前文件</button>
          <button class="btn ghost" id="btn-raw-unlock" type="button">验证密码</button>
        </div>
      </div>
      <div class="raw-lock" id="raw-lock-card">
        <strong id="raw-lock-title">原始配置已锁定</strong>
        <div class="micro" id="raw-lock-copy">需要先验证网页登录密码，才能查看和编辑配置文件。</div>
        <div class="row-actions">
          <button class="btn" id="btn-raw-unlock-inline" type="button">验证密码</button>
        </div>
      </div>
      <div class="raw-layout" id="raw-layout">
        <aside class="raw-pane">
          <div class="raw-meta">
            <div class="meta-copy">
              <div class="meta-title" id="raw-tree-title">配置目录</div>
              <div class="meta-sub" id="raw-tree-path">-</div>
            </div>
          </div>
          <div id="raw-tree" class="raw-tree"></div>
        </aside>
        <section class="raw-main">
          <div class="raw-meta">
            <div class="meta-copy">
              <div class="meta-title" id="raw-file-title">未选择文件</div>
              <div class="meta-sub" id="raw-file-path">-</div>
            </div>
            <div class="meta-copy" style="text-align:right">
              <div class="meta-title" id="raw-file-size">-</div>
              <div class="meta-sub" id="raw-file-mtime">-</div>
            </div>
          </div>
          <textarea id="raw-editor" class="raw-editor" spellcheck="false"></textarea>
          <div id="status-raw" class="status">-</div>
        </section>
      </div>
    </div>
  </div>
<div id="settings-toast-stack" class="toast-stack" aria-live="polite" aria-atomic="true"></div>
<div class="modal-mask" id="reauth-modal">
  <div class="modal-card">
    <h3>再次验证</h3>
    <div class="section-copy">二次验证保护 Token 显示、复制和 SSO 链接生成。</div>
    <div class="grid" style="margin-top:14px">
      <div class="field full"><label>账号</label><input id="reauth-user" type="text" autocomplete="username"></div>
      <div class="field full"><label>密码</label><input id="reauth-pass" type="password" autocomplete="current-password"></div>
    </div>
    <div class="row-actions" style="margin-top:14px">
      <button class="btn ghost" id="btn-reauth-cancel" type="button">取消</button>
      <button class="btn" id="btn-reauth-confirm" type="button">确认</button>
    </div>
    <div id="reauth-status" class="status">-</div>
  </div>
</div>
<div class="modal-mask" id="elevate-modal">
  <div class="modal-card">
    <h3>临时提权</h3>
    <div class="section-copy" id="elevate-copy">此操作需要 root 权限；sudo 密码只用于本次请求，不会保存。</div>
    <div class="grid" style="margin-top:14px">
      <div class="field full"><label>sudo 密码</label><input id="elevate-pass" type="password" autocomplete="off"></div>
    </div>
    <div class="row-actions" style="margin-top:14px">
      <button class="btn ghost" id="btn-elevate-cancel" type="button">取消</button>
      <button class="btn" id="btn-elevate-confirm" type="button">确认</button>
    </div>
    <div id="elevate-status" class="status">-</div>
  </div>
</div>
<div class="modal-mask" id="one-time-modal">
  <div class="modal-card">
    <h3 id="one-time-title">只显示一次</h3>
    <div class="section-copy" id="one-time-note">关闭后不能再次查看或复制。</div>
    <div class="one-time-secret" id="one-time-secret"></div>
    <div class="row-actions" style="margin-top:14px">
      <button class="btn" id="btn-one-time-copy" type="button">复制</button>
      <button class="btn ghost" id="btn-one-time-close" type="button">关闭</button>
    </div>
  </div>
</div>
<div class="modal-mask" id="model-map-modal">
  <div class="modal-card wide">
    <h3>识别库编辑</h3>
    <div class="section-copy">编辑本地 rid_models.json 条目，保存后立即刷新实时和历史机型。</div>
    <div class="model-editor">
      <div class="model-editor-toolbar">
        <input id="model-map-search" type="text" placeholder="前缀或机型">
        <button class="btn ghost" id="btn-model-map-add" type="button">新增</button>
        <button class="btn" id="btn-model-map-save" type="button">保存列表</button>
      </div>
      <div id="model-map-list" class="model-map-list"></div>
      <div class="micro" id="model-map-editor-state">当前模型映射文件保存识别库条目。</div>
    </div>
    <div class="row-actions" style="margin-top:14px"><button class="btn ghost" id="btn-model-map-close" type="button">关闭</button></div>
  </div>
</div>
<script>
function qs(id){ return document.getElementById(id); }
function qsa(sel){ return Array.prototype.slice.call(document.querySelectorAll(sel) || []); }
function enc(v){ return String(v == null ? '' : v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function splitLines(text){
  var raw = String(text || '');
  if(raw.indexOf('\\r') >= 0) raw = raw.split('\\r').join('');
  return raw.split('\\n');
}
function isLocalHostName(host){
  var h = String(host || '').toLowerCase();
  return h === 'localhost' || h === '127.0.0.1';
}
var apiTokenRows = [];
var oneTimeSecretValue = '';
var reauthAction = null;
var elevateResolve = null;
var lastSystemServiceStatus = null;
var loginLinks = [];
var modelMapRows = [];
var modelMapPath = '';
var settingsState = {visualLoaded:false, rawLoaded:false, rawUnlocked:false, rawRoot:'', rawTree:null, rawSelectedPath:'', rawSelectedRel:'', channelUseDefault:true, channelEditing:false, visualInitial:null, visualDirty:false, dirtyCards:{}, authConfigured:false};
var metricsState = {window:'12h', zoom:1, panSec:0, hover:null, drag:null, chartMeta:{}, items:[]};
var SETTINGS_DRAFT_SECTIONS = [
  {key:'capture', label:'采集'},
  {key:'map', label:'地图与基站'},
  {key:'zones', label:'报警区域'},
  {key:'access', label:'通知与访问控制'},
  {key:'metrics', label:'节点负载'}
];
var COOKIE_TRACK_REALTIME = 'rid_realtime_track';
var COOKIE_TRACK_2H_ONLY = 'rid_track_2h_only';
var FREEZE_ON_HOME_KEY = 'rid_freeze_on_home_once';
var NEW_FIRMWARE_PARSE_KEY = 'rid_new_firmware_parse_enabled';
function on(id, type, handler){
  var el = qs(id);
  if(el) el.addEventListener(type, handler);
  return el;
}
async function guarded(action, statusId, okText, okMs, warnMs){
  try{
    await action();
    if(okText) showNotice(okText, 'ok', okMs || 2200);
  }catch(e){
    if(statusId) setStatus(statusId, e.message || e, true);
    showNotice(e.message || e, 'warn', warnMs || 3800);
  }
}
function syncSettingsViewport(){
  var vp = window.visualViewport;
  var vh = Math.max(320, Math.round((vp && vp.height) ? vp.height : window.innerHeight || 0));
  document.documentElement.style.setProperty('--app-vh', vh + 'px');
}
function cookieGet(name){
  var key = String(name || '').trim();
  if(!key) return null;
  var parts = String(document.cookie || '').split(';');
  for(var i=0;i<parts.length;i++){
    var p = String(parts[i] || '').trim();
    if(!p) continue;
    var pos = p.indexOf('=');
    var k = (pos < 0) ? p : p.slice(0, pos).trim();
    if(k !== key) continue;
    var raw = (pos < 0) ? '' : p.slice(pos + 1);
    try{ return decodeURIComponent(raw); }catch(_e){ return raw; }
  }
  return null;
}
function cookieSet(name, value, days){
  var key = String(name || '').trim();
  if(!key) return;
  var nDays = Number(days);
  if(!isFinite(nDays) || nDays <= 0) nDays = 365;
  var secure = (location.protocol === 'https:') ? '; Secure' : '';
  document.cookie = key + '=' + encodeURIComponent(String(value == null ? '' : value))
    + '; Max-Age=' + Math.round(nDays * 86400) + '; Path=/; SameSite=Lax' + secure;
}
function cookieBool(name, defVal){
  var v = cookieGet(name);
  if(v == null || v === '') return !!defVal;
  v = String(v).toLowerCase();
  return (v === '1' || v === 'true' || v === 'on' || v === 'yes');
}
function setStatus(id, text, err){
  var el = qs(id); if(!el) return;
  el.textContent = String(text || '-');
  el.classList.toggle('err', !!err);
}
function showNotice(text, kind, timeoutMs){
  var host = qs('settings-toast-stack');
  if(!host) return;
  var node = document.createElement('div');
  var tone = (kind === 'warn' || kind === 'error') ? 'warn' : 'ok';
  node.className = 'toast ' + tone;
  node.innerHTML = '<div class="toast-title">' + (tone === 'warn' ? '操作结果' : '已完成') + '</div>'
    + '<div class="toast-text">' + enc(String(text || '')) + '</div>';
  host.appendChild(node);
  requestAnimationFrame(function(){ node.classList.add('show'); });
  var ttl = Math.max(1800, Number(timeoutMs || 3200));
  window.setTimeout(function(){
    node.classList.remove('show');
    window.setTimeout(function(){ if(node.parentNode) node.parentNode.removeChild(node); }, 220);
  }, ttl);
}
function apiUrl(url){
  try{ return new URL(String(url||''), window.location.origin).toString(); }catch(_e){ return String(url||''); }
}
function pageHeaders(extra){
  var headers = {'X-LightRID-Page':'1'};
  if(extra && typeof extra === 'object'){
    Object.keys(extra).forEach(function(k){ headers[k] = extra[k]; });
  }
  return headers;
}
var authRedirecting = false;
function authExpired(r, d){
  var err = String((d && d.error) || '');
  return r && r.status === 401 && (!!(d && d.auth_expired) || err === 'login required' || err === 'auth required');
}
function redirectLogin(){
  if(authRedirecting) return;
  authRedirecting = true;
  location.href = '/login?next=/';
}
async function copyTextPlain(text){
  var raw = String(text || '');
  if(!raw) throw new Error('没有可复制的内容');
  if(navigator.clipboard && navigator.clipboard.writeText){
    try{
      await navigator.clipboard.writeText(raw);
      return;
    }catch(_e){}
  }
  var ta = document.createElement('textarea');
  ta.value = raw;
  ta.style.position = 'fixed';
  ta.style.opacity = '0';
  ta.style.pointerEvents = 'none';
  document.body.appendChild(ta);
  ta.focus();
  ta.select();
  try{
    if(!document.execCommand('copy')) throw new Error('copy failed');
  }finally{
    if(ta.parentNode) ta.parentNode.removeChild(ta);
  }
}
function parseFilenameFromDisposition(headerValue){
  var cd = String(headerValue || '');
  var marker = 'filename=';
  var pos = cd.toLowerCase().indexOf(marker);
  if(pos < 0) return '';
  var raw = cd.slice(pos + marker.length).trim();
  if(raw.charAt(0) === '"'){
    var end = raw.indexOf('"', 1);
    raw = end > 0 ? raw.slice(1, end) : raw.slice(1);
  }else{
    var semi = raw.indexOf(';');
    if(semi >= 0) raw = raw.slice(0, semi);
  }
  return raw.trim();
}
async function downloadQualityReport(){
  showNotice('正在生成质量分析包...', 'ok', 2200);
  const r = await fetch(apiUrl('/api/tools/diagnostic.zip'), {cache:'no-store', headers:pageHeaders()});
  if(!r.ok){
    var errText = '';
    try{
      var errJson = await r.json();
      if(authExpired(r, errJson)){ redirectLogin(); throw new Error('login required'); }
      errText = errJson.error || '';
    }catch(_e){
      try{ errText = await r.text(); }catch(_e2){}
    }
    throw new Error(errText || ('HTTP ' + r.status));
  }
  const blob = await r.blob();
  if(!blob || Number(blob.size || 0) < 128){
    throw new Error('质量分析包为空，请稍后重试或查看服务日志');
  }
  var filename = parseFilenameFromDisposition(r.headers.get('Content-Disposition')) || 'light-rid-quality.zip';
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  window.setTimeout(function(){
    URL.revokeObjectURL(url);
    if(a.parentNode) a.parentNode.removeChild(a);
  }, 15000);
  showNotice('质量分析包已生成。', 'ok', 3200);
}
async function getJson(url){
  const r = await fetch(apiUrl(url), {cache:'no-store', headers:pageHeaders()});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
async function postJson(url, body){
  const r = await fetch(apiUrl(url), {method:'POST', headers:pageHeaders({'Content-Type':'application/json'}), body:JSON.stringify(body||{})});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
function closeElevate(value){
  var modal = qs('elevate-modal');
  var pass = qs('elevate-pass');
  var resolver = elevateResolve;
  elevateResolve = null;
  if(pass) pass.value = '';
  if(modal) modal.classList.remove('show');
  if(resolver) resolver(value);
}
function requestElevationPassword(message){
  if(lastSystemServiceStatus && lastSystemServiceStatus.running_as_root) return Promise.resolve('');
  return new Promise(function(resolve){
    elevateResolve = resolve;
    if(qs('elevate-copy')) qs('elevate-copy').textContent = String(message || '此操作需要 root 权限；sudo 密码只用于本次请求，不会保存。');
    if(qs('elevate-status')) setStatus('elevate-status', '密码不会写入配置文件或浏览器存储。', false);
    if(qs('elevate-modal')) qs('elevate-modal').classList.add('show');
    window.setTimeout(function(){ if(qs('elevate-pass')) qs('elevate-pass').focus(); }, 40);
  });
}
async function privilegedBody(base, message){
  var body = Object.assign({}, base || {});
  if(lastSystemServiceStatus && lastSystemServiceStatus.running_as_root) return body;
  var pwd = await requestElevationPassword(message);
  if(pwd == null) throw new Error('已取消提权');
  body.sudo_password = String(pwd || '');
  return body;
}
function v(id){ return String((qs(id) && qs(id).value) || '').trim(); }
function n(id){ var x = v(id); if(!x) return null; var f = Number(x); return isFinite(f) ? f : null; }
function check(id){ return !!(qs(id) && qs(id).checked); }
function cloneJson(obj){ return JSON.parse(JSON.stringify(obj == null ? null : obj)); }
function sameJson(a, b){ return JSON.stringify(a == null ? null : a) === JSON.stringify(b == null ? null : b); }
function loadTheme(){
  try{ var s = localStorage.getItem('rid_ui_theme'); if(s === 'dark' || s === 'light') return s; }catch(_e){}
  if(window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches) return 'light';
  return 'dark';
}
function applyTheme(theme){
  var light = (theme === 'light');
  document.body.classList.toggle('theme-light', light);
  document.body.classList.toggle('theme-dark', !light);
  try{ localStorage.setItem('rid_ui_theme', light ? 'light' : 'dark'); }catch(_e){}
  qs('btn-theme').textContent = light ? '深色' : '浅色';
}
function loadBrowserPrefs(){
  var rt = qs('pref-realtime-track');
  var f2h = qs('pref-track-2h');
  var newFw = qs('pref-new-firmware-parser');
  if(rt) rt.checked = cookieBool(COOKIE_TRACK_REALTIME, true);
  if(f2h) f2h.checked = cookieBool(COOKIE_TRACK_2H_ONLY, false);
  if(newFw){
    try{ newFw.checked = localStorage.getItem(NEW_FIRMWARE_PARSE_KEY) !== '0'; }
    catch(_e){ newFw.checked = true; }
  }
}
function saveBrowserPrefs(){
  var rt = qs('pref-realtime-track');
  var f2h = qs('pref-track-2h');
  var newFw = qs('pref-new-firmware-parser');
  cookieSet(COOKIE_TRACK_REALTIME, (rt && rt.checked) ? '1' : '0', 365);
  cookieSet(COOKIE_TRACK_2H_ONLY, (f2h && f2h.checked) ? '1' : '0', 365);
  if(newFw){
    try{ localStorage.setItem(NEW_FIRMWARE_PARSE_KEY, newFw.checked ? '1' : '0'); }catch(_e){}
  }
  showNotice('页面偏好已保存到当前浏览器。', 'ok', 2200);
}
function notifySettingsButtonText(){
  if(!('Notification' in window)) return '网页通知(不支持)';
  if(Notification.permission === 'granted') return '网页通知(已开)';
  if(Notification.permission === 'denied') return '网页通知(已拒绝)';
  return '网页通知';
}
function updateHomeActionButtons(){
  var notifyBtn = qs('btn-settings-web-notify');
  if(notifyBtn){
    notifyBtn.textContent = notifySettingsButtonText();
    notifyBtn.disabled = !('Notification' in window) || Notification.permission === 'denied';
  }
}
async function requestSettingsWebNotify(){
  if(!('Notification' in window)){
    setStatus('status-home-actions', '当前浏览器不支持网页通知。', true);
    return;
  }
  try{
    if(Notification.permission !== 'granted'){
      await Notification.requestPermission();
    }
    updateHomeActionButtons();
    if(Notification.permission === 'granted'){
      try{ new Notification('Light RID Scanner 通知已启用', {body:'将推送飞机上下线事件'}); }catch(_e){}
      setStatus('status-home-actions', '网页通知已启用。', false);
      showNotice('网页通知已启用。', 'ok', 2400);
    }else{
      setStatus('status-home-actions', '网页通知未授权。', true);
      showNotice('网页通知未授权。', 'warn', 3200);
    }
  }catch(e){
    setStatus('status-home-actions', '网页通知申请失败: ' + (e.message || e), true);
  }
}
function freezeHomeOnReturn(){
  try{ localStorage.setItem(FREEZE_ON_HOME_KEY, '1'); }catch(_e){}
  location.href = '/';
}
async function clearHistoryFromSettings(){
  if(!confirm('清空历史无人机记录，并删除本地缓存文件？')) return;
  var btn = qs('btn-settings-clear-history');
  if(btn) btn.disabled = true;
  setStatus('status-home-actions', '清空历史中...', false);
  try{
    const data = await postJson('/api/history/clear', {});
    var msg = '历史已清空' + (typeof data.cleared === 'number' ? ('（' + data.cleared + '架）') : '') + '。';
    setStatus('status-home-actions', msg, false);
    showNotice(msg, 'ok', 2600);
    await loadRuntimePanel().catch(function(){});
  }catch(e){
    setStatus('status-home-actions', '清空失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 3800);
  }finally{
    if(btn) btn.disabled = false;
  }
}
function renderEulaState(eula){
  eula = eula || {};
  var status = qs('status-eula');
  var revokeBtn = qs('btn-eula-revoke');
  if(status){
    status.textContent = (eula.accepted ? '当前已同意许可协议。' : '当前未同意许可协议。')
      + '\\n状态文件: ' + String(eula.set_path || 'EULA.set')
      + '\\n官方文本: ' + String(eula.source_url || '');
    status.classList.toggle('err', !eula.accepted);
  }
  if(revokeBtn) revokeBtn.disabled = !eula.accepted;
}
async function revokeEulaAcceptance(){
  if(!confirm('撤回同意后，系统会立即回到许可协议确认页。确定撤回？')) return;
  var btn = qs('btn-eula-revoke');
  if(btn) btn.disabled = true;
  setStatus('status-eula', '正在撤回许可协议同意状态...', false);
  try{
    const data = await postJson('/api/eula/revoke', {});
    setStatus('status-eula', '已撤回同意。即将跳转到 EULA 页面。\\n状态文件: ' + String(data.set_path || ''), true);
    showNotice('已撤回 EULA 同意状态。', 'warn', 2600);
    window.setTimeout(function(){ location.href = '/eula?next=/settings'; }, 700);
  }catch(e){
    setStatus('status-eula', '撤回失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 3600);
    if(btn) btn.disabled = false;
  }
}
async function ensureTabLoaded(tab){
  if(tab === 'raw' && !settingsState.rawLoaded){
    await loadRaw();
    settingsState.rawLoaded = true;
  }
}
function activateTab(tab){
  qsa('.tab').forEach(function(btn){ btn.classList.toggle('active', btn.getAttribute('data-tab')===tab); });
  qsa('.panel').forEach(function(p){ p.classList.toggle('active', p.getAttribute('data-tab')===tab); });
  ensureTabLoaded(tab).catch(function(e){
    if(tab === 'raw') setStatus('status-raw', e.message || e, true);
  });
}
function applyTabs(){
  qsa('.tab').forEach(function(btn){
    btn.addEventListener('click', function(){
      activateTab(btn.getAttribute('data-tab') || 'visual');
    });
  });
}
function fmtPct(v){
  return (v == null || !isFinite(v)) ? '—' : (Number(v).toFixed(1) + '%');
}
function fmtMb(used, total){
  if(used == null || total == null || !isFinite(used) || !isFinite(total)) return '—';
  return String(used) + ' / ' + String(total) + ' MB';
}
function fmtSecShort(sec){
  sec = Number(sec);
  if(!isFinite(sec) || sec < 0) return '—';
  if(sec < 60) return Math.round(sec) + 's';
  if(sec < 3600) return Math.round(sec / 60) + 'm';
  if(sec < 86400) return Math.round(sec / 3600) + 'h';
  return Math.round(sec / 86400) + 'd';
}
function checkedAuthLoginMethods(){
  var out = [];
  if(check('cfg-auth-method-password')) out.push('password');
  if(check('cfg-auth-method-passkey')) out.push('passkey');
  if(check('cfg-auth-method-sso')) out.push('sso');
  return out;
}
function ensureAuthLoginMethodSelection(preferredId, noisy){
  var methods = checkedAuthLoginMethods();
  if(methods.length) return methods;
  var fallbackId = preferredId || 'cfg-auth-method-password';
  if(qs(fallbackId)) qs(fallbackId).checked = true;
  methods = checkedAuthLoginMethods();
  if(noisy){
    if(qs('auth-method-state')) qs('auth-method-state').textContent = '至少保留一种网页登录方式；账号密码仍用于设置页二次确认。';
    showNotice('至少保留一种网页登录方式。', 'warn', 2400);
  }
  return methods;
}
function syncAuthMethodUi(){
  var methods = ensureAuthLoginMethodSelection('', false);
  var authEnabled = check('cfg-auth-enabled');
  var authConfigured = !!settingsState.authConfigured;
  var allowPassword = methods.indexOf('password') >= 0;
  var allowPasskey = methods.indexOf('passkey') >= 0;
  var allowSso = methods.indexOf('sso') >= 0;
  if(qs('auth-method-state')){
    var labels = [];
    if(allowPassword) labels.push('账号密码');
    if(allowPasskey) labels.push('PassKey');
    if(allowSso) labels.push('SSO URL');
    qs('auth-method-state').textContent = '当前允许: ' + (labels.join(' / ') || '未选择') + '。至少保留一种网页登录方式；账号密码仍用于设置页二次确认和 PassKey 注册。';
  }
  if(qs('login-link-state')){
    if(!authEnabled || !authConfigured){
      qs('login-link-state').textContent = '网页登录账号密码完整时，SSO URL 登录可用。';
    }else if(!allowSso){
      qs('login-link-state').textContent = '当前已关闭 SSO URL 登录；已生成的链接会保留，但不会生效。';
    }else{
      qs('login-link-state').textContent = '生成的链接可在下面管理；链接受有效期和单次登录状态控制。';
    }
  }
  if(qs('passkey-state')){
    if(!authEnabled || !authConfigured){
      qs('passkey-state').textContent = '完成网页登录账号和密码配置后，可在这里登记通行密钥。';
    }else if(!allowPasskey){
      qs('passkey-state').textContent = '当前已关闭 PassKey 登录；已登记密钥会保留，但不会生效。';
    }else{
      qs('passkey-state').textContent = '通行密钥可以直接用于网页登录。';
    }
  }
  if(qs('btn-login-link-create')) qs('btn-login-link-create').disabled = !(authEnabled && authConfigured && allowSso);
  if(qs('btn-passkey-add')) qs('btn-passkey-add').disabled = !(authEnabled && authConfigured && allowPasskey);
}
function renderHostStats(host, basic){
  var root = qs('host-stats');
  if(!root) return;
  host = host || {};
  basic = basic || {};
  var sniff = host.sniff_state || {};
  var sniffLabel = sniff.state === 'ok' ? '正常' : (sniff.state === 'warn' ? '等待数据' : (sniff.state === 'error' ? '异常' : '—'));
  var localIps = (Array.isArray(host.local_ips) && host.local_ips.length) ? host.local_ips.map(function(ip){
    ip = String(ip || '');
    return '<div class="ip-line"><span class="ip-text" title="'+enc(ip)+'">'+enc(ip)+'</span><span class="ip-len">'+ip.length+'</span></div>';
  }).join('') : '—';
  var items = [
    ['主机', host.hostname || '—'],
    ['本机 IP', localIps, 'ip-lines'],
    ['CPU', fmtPct(host.cpu_percent)],
    ['内存', fmtPct(host.mem_percent)],
    ['内存容量', fmtMb(host.mem_used_mb, host.mem_total_mb)],
    ['温度', host.temperature_c == null ? '—' : (Number(host.temperature_c).toFixed(1) + '°C')],
    ['当前网卡', host.active_iface || basic.iface || '未绑定'],
    ['当前信道', String(host.current_channel || basic.channel_effective || 6)]
  ];
  root.innerHTML = items.map(function(row){
    var cls = row[2] ? ('v ' + row[2]) : 'v';
    var val = row[2] ? String(row[1]) : enc(row[1]);
    return '<div class="stat"><div class="k">'+enc(row[0])+'</div><div class="'+cls+'">'+val+'</div></div>';
  }).join('');
  var meta = [];
  if(host.cpu_count) meta.push('核心 ' + String(host.cpu_count));
  if(Array.isArray(host.ifaces) && host.ifaces.length) meta.push('网卡 ' + host.ifaces.map(function(x){ return String(x.name || ''); }).filter(Boolean).join(', '));
  if(host.load1 != null) meta.push('负载 ' + String(host.load1) + '/' + String(host.load5) + '/' + String(host.load15));
  if(host.uptime_sec != null) meta.push('运行 ' + fmtSecShort(host.uptime_sec));
  if(host.temperature_source_label) meta.push('温度源 ' + String(host.temperature_source_label));
  if(sniff.state) meta.push('采集 ' + sniffLabel);
  if(sniff.msg) meta.push(String(sniff.msg));
  qs('host-meta').textContent = meta.length ? meta.join(' | ') : '-';
}
function renderSystemServiceStatus(data){
  data = data || {};
  lastSystemServiceStatus = data;
  var iw = data.iw || {};
  var sec = data.security || {};
  var lines = [];
  if(data.supported){
    lines.push('服务: ' + String(data.service_name || 'light-rid-scanner.service'));
    lines.push('注册: ' + (data.registered ? '已注册' : '未注册')
      + ' | 开机自启: ' + String(data.enabled || 'unknown')
      + ' | 运行状态: ' + String(data.active || 'unknown'));
    lines.push('当前进程: ' + String(data.current_user || '-') + ' / uid=' + String(data.current_uid == null ? '-' : data.current_uid)
      + (data.running_as_root ? ' | root 高权限运行' : ' | 非 root'));
    lines.push('专用账号: ' + String(data.dedicated_user || 'rid') + (data.dedicated_user_exists ? ' 已存在' : ' 未创建')
      + ' | 服务账号: ' + String(data.actual_service_user || '未声明'));
    if(Array.isArray(data.service_capabilities) && data.service_capabilities.length) lines.push('采集能力: ' + data.service_capabilities.join(', '));
    if(data.service_path) lines.push('服务文件: ' + String(data.service_path));
    if(data.exec_start) lines.push('启动命令: ' + String(data.exec_start));
    if(data.registered && data.unit_matches === false) lines.push('当前服务文件与本页生成的启动参数不一致，可点击注册/更新服务。');
    if(data.running_as_root) lines.push('安全告警: 当前网页服务处于 root 权限，建议一键修复为 rid 专用账号运行。');
    if(data.registered && !data.service_uses_dedicated_user) lines.push('安全告警: 当前服务文件未声明 rid 专用账号。');
  }else{
    lines.push('systemd: 不可用' + (data.reason ? ('，' + String(data.reason)) : ''));
    if(data.manual_hint) lines.push(String(data.manual_hint));
  }
  lines.push('iw: ' + (iw.available ? ('可用 ' + String(iw.path || '')) : '未安装'));
  if(iw.message && !iw.available) lines.push(String(iw.message));
  if(iw.manual_hint && !iw.available) lines.push(String(iw.manual_hint));
  if(data.last_error) lines.push('状态读取错误: ' + String(data.last_error));
  var securityWarn = !!(data.running_as_root || (data.registered && !data.service_uses_dedicated_user) || !data.dedicated_user_exists);
  setStatus('status-system-service', lines.join('\\n'), !iw.available || (!!data.supported && securityWarn));
  renderRuntimeSecurityAlert(data, sec);
  var regBtn = qs('btn-service-register');
  if(regBtn) regBtn.disabled = !data.supported || !data.can_elevate || !data.dedicated_user_exists;
  var iwBtn = qs('btn-iw-install');
  if(iwBtn) iwBtn.disabled = !!iw.available || !iw.can_install;
  var repairBtn = qs('btn-security-repair');
  if(repairBtn) repairBtn.disabled = !data.supported || !data.can_elevate;
}
function renderRuntimeSecurityAlert(data, sec){
  var box = qs('runtime-security-alert');
  if(!box) return;
  data = data || {};
  sec = sec || data.security || {};
  var runningRoot = !!(data.running_as_root || sec.running_as_root);
  var serviceOk = !!data.service_uses_dedicated_user && !!data.dedicated_user_exists;
  box.classList.add('show');
  box.classList.toggle('warn', runningRoot || !serviceOk);
  box.classList.toggle('ok', !runningRoot && serviceOk);
  if(qs('runtime-security-title')){
    qs('runtime-security-title').textContent = runningRoot ? '当前处于 root 权限' : (serviceOk ? '运行权限正常' : '专用账号未完成');
  }
    if(qs('runtime-security-copy')){
    if(runningRoot){
      qs('runtime-security-copy').textContent = '当前网页服务和采集进程以 root 运行，存在安全风险。点击一键修复会创建/确认 rid 账号，并把 systemd 服务改为 rid 账号加网络能力运行。';
    }else if(sec && sec.risk === 'missing-capabilities'){
      qs('runtime-security-copy').textContent = '当前进程不是 root，但没有检测到采集所需网络能力。请执行一键修复，让 systemd 以 rid 账号和网络能力启动服务。';
    }else if(!serviceOk){
      qs('runtime-security-copy').textContent = '当前进程不是 root，但 systemd 服务还没有确认使用 rid 专用账号。需要 root 或临时 sudo 提权完成修复。';
    }else{
      qs('runtime-security-copy').textContent = '当前服务目标为 rid 专用账号，采集所需网络能力通过 systemd capability 提供。';
    }
  }
}
async function loadSystemServiceStatus(){
  const data = await getJson('/api/settings/systemd/status');
  renderSystemServiceStatus(data);
  return data;
}
async function registerSystemdServiceFromSettings(){
  if(!confirm('将写入 /etc/systemd/system/light-rid-scanner.service 并启用开机自启。继续？')) return;
  var btn = qs('btn-service-register');
  try{
    if(btn) btn.disabled = true;
    setStatus('status-system-service', '正在注册 systemd 服务...', false);
    const body = await privilegedBody({confirm:true}, '注册/更新 systemd 服务需要 root 权限。请输入 sudo 密码；密码只用于本次请求，不会保存。');
    const data = await postJson('/api/settings/systemd/register', body);
    renderSystemServiceStatus((data && data.status) || {});
    showNotice(data.message || 'systemd 服务已注册。', 'ok', 3600);
  }catch(e){
    setStatus('status-system-service', '注册失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 4200);
  }finally{
    await loadSystemServiceStatus().catch(function(){});
  }
}
async function installIwFromSettings(){
  if(!confirm('将执行 apt-get update 和 apt-get install -y iw。继续？')) return;
  var btn = qs('btn-iw-install');
  try{
    if(btn) btn.disabled = true;
    setStatus('status-system-service', '正在安装 iw...', false);
    const body = await privilegedBody({confirm:true}, '安装 iw 需要 root 权限。请输入 sudo 密码；密码只用于本次请求，不会保存。');
    const data = await postJson('/api/settings/iw/install', body);
    if(data.status) renderSystemServiceStatus(data.status);
    showNotice(data.message || 'iw 安装完成。', 'ok', 3600);
  }catch(e){
    setStatus('status-system-service', 'iw 安装失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 4600);
  }finally{
    await loadSystemServiceStatus().catch(function(){});
  }
}
function refreshSystemServiceAfterRestart(delaySec){
  var delayMs = Math.max(5000, Number(delaySec || 3) * 1000 + 4000);
  var attempts = 0;
  function tick(){
    attempts += 1;
    loadSystemServiceStatus().then(function(){
      setStatus('status-system-service', '服务已自动重启，运行状态已刷新。', false);
      showNotice('服务已自动重启，当前状态已刷新。', 'ok', 3600);
    }).catch(function(){
      if(attempts < 8){
        setTimeout(tick, 2000);
      }else{
        setStatus('status-system-service', '服务正在重启。如果状态没有恢复，请稍后手动刷新页面。', true);
        showNotice('服务正在重启。如果页面未恢复，请稍后手动刷新。', 'warn', 5200);
      }
    });
  }
  setTimeout(tick, delayMs);
}
async function repairRuntimeSecurityFromSettings(){
  if(!confirm('将创建/确认 rid 专用账号、授予配置与缓存写权限，把 systemd 服务改为 rid 账号运行，并在完成后自动重启服务。继续？')) return;
  var btn = qs('btn-security-repair');
  var restartScheduled = false;
  var restartDelay = 3;
  try{
    if(btn) btn.disabled = true;
    setStatus('status-system-service', '正在修复运行权限...', false);
    const body = await privilegedBody({confirm:true}, '一键修复需要 root 权限。请输入 sudo 密码；密码只用于创建账号、授权文件和写入 systemd 服务，本系统不会保存。');
    const data = await postJson('/api/settings/security/repair', body);
    restartScheduled = !!(data && data.restart_scheduled);
    restartDelay = Number((data && data.restart_delay_sec) || restartDelay);
    renderSystemServiceStatus((data && data.status) || {});
    if(restartScheduled){
      setStatus('status-system-service', '修复完成，服务将在几秒后自动重启；页面可能短暂断开。', false);
      showNotice(data.message || '运行权限已修复，服务即将自动重启。', 'ok', 8200);
      refreshSystemServiceAfterRestart(restartDelay);
    }else{
      showNotice(data.message || '运行权限已修复。', 'ok', 5200);
    }
  }catch(e){
    setStatus('status-system-service', '修复失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 5200);
  }finally{
    if(!restartScheduled){
      await loadSystemServiceStatus().catch(function(){});
    }
  }
}
function renderSettingsRuntime(data){
  data = data || {};
  var apRoot = qs('settings-ap-list');
  if(apRoot){
    var aps = Array.isArray(data.aps) ? data.aps.slice(0, 40) : [];
    if(!aps.length){
      apRoot.innerHTML = '<div class="empty-state">暂无 AP 数据</div>';
    }else{
      apRoot.innerHTML = '<div class="settings-ap-scroll">' + aps.map(function(a, idx){
        var mac = String(a.mac || '-');
        var ssid = String(a.ssid || '(hidden)');
        var vendor = String(a.vendor || '未知');
        var rssi = (a.rssi == null) ? 'N/A' : (String(a.rssi) + 'dBm');
        return '<div class="list-row"><div class="settings-ap-row-grid">'
          + '<div class="micro">#'+(idx+1)+'</div>'
          + '<div class="clip" title="'+enc(ssid)+'"><b>'+enc(ssid)+'</b><div class="micro clip" title="'+enc(vendor)+'">'+enc(vendor)+'</div></div>'
          + '<div class="micro clip" title="'+enc(mac)+'">'+enc(mac)+'</div>'
          + '<div>'+enc(rssi)+'</div>'
          + '</div></div>';
      }).join('') + '</div>';
    }
  }
  var log = qs('settings-runtime-log');
  if(log){
    var lines = [];
    if(Array.isArray(data.ap_logs) && data.ap_logs.length) lines = lines.concat(['[AP]'], data.ap_logs);
    if(Array.isArray(data.event_logs) && data.event_logs.length) lines = lines.concat(['', '[EVENT]'], data.event_logs);
    if(Array.isArray(data.scan_logs) && data.scan_logs.length) lines = lines.concat(['', '[SCAN]'], data.scan_logs);
    log.value = lines.join('\\n');
  }
  setStatus('status-runtime', 'AP ' + String((data.aps || []).length || 0) + '/' + String(data.aps_total || 0), false);
  if(data.metrics && Array.isArray(data.metrics.items)){
    metricsState.items = data.metrics.items;
    drawMetricsChart();
  }
}
async function loadRuntimePanel(){
  const data = await getJson('/api/settings/runtime?limit=220');
  renderSettingsRuntime(data);
}
function metricWindowSec(){
  if(metricsState.window === '7d') return 7 * 86400;
  if(metricsState.window === '24h') return 24 * 3600;
  return 12 * 3600;
}
function fmtMetricTime(ts){
  var d = new Date(Number(ts || 0) * 1000);
  if(!isFinite(d.getTime())) return '-';
  return d.toLocaleString();
}
function metricNumber(v){
  var n = Number(v);
  return isFinite(n) ? n : null;
}
function metricRowsSorted(){
  var arr = Array.isArray(metricsState.items) ? metricsState.items.slice() : [];
  arr.sort(function(a,b){ return Number(a.ts||0) - Number(b.ts||0); });
  return arr;
}
function metricZoomFactor(){
  var z = Math.max(1, Math.min(100, Number(metricsState.zoom || 1)));
  return Math.pow(24, (z - 1) / 99);
}
function metricCurrentRange(rows){
  var arr = Array.isArray(rows) ? rows : metricRowsSorted();
  var base = metricWindowSec();
  var span = Math.max(1800, base / metricZoomFactor());
  var latest = arr.length ? Number(arr[arr.length - 1].ts || (Date.now()/1000)) : (Date.now()/1000);
  var first = arr.length ? Number(arr[0].ts || latest) : (latest - base);
  var maxPan = Math.max(0, latest - first - span);
  metricsState.panSec = Math.max(0, Math.min(maxPan, Number(metricsState.panSec || 0)));
  var end = latest - Number(metricsState.panSec || 0);
  var start = end - span;
  return {start:start, end:end, span:span, latest:latest, first:first, maxPan:maxPan};
}
function metricVisibleItems(){
  var arr = metricRowsSorted();
  if(!arr.length) return [];
  var range = metricCurrentRange(arr);
  return arr.filter(function(x){ return Number(x.ts || 0) >= range.start && Number(x.ts || 0) <= range.end; });
}
function metricDefs(rows){
  var apMax = (Array.isArray(rows) ? rows : []).reduce(function(m, x){ return Math.max(m, Number(x.ap || 0)); }, 1);
  return [
    {key:'cpu', label:'CPU', color:'#2899f5', fmt:function(v){ return fmtPct(v); }, axis:function(v){ return Math.round(v) + '%'; }, max:100},
    {key:'mem', label:'内存', color:'#92c353', fmt:function(v){ return fmtPct(v); }, axis:function(v){ return Math.round(v) + '%'; }, max:100},
    {key:'temp', label:'温度', color:'#f7630c', fmt:function(v){ return v == null ? '—' : Number(v).toFixed(1) + '°C'; }, axis:function(v){ return Math.round(v) + '°'; }, max:100},
    {key:'load', label:'负载', color:'#c19c00', fmt:function(v){ return fmtPct(v); }, axis:function(v){ return Math.round(v) + '%'; }, max:100},
    {key:'ap', label:'AP数', color:'#8764b8', fmt:function(v){ return v == null ? '—' : String(Math.round(Number(v))); }, axis:function(v){ return String(Math.round(v)); }, max:Math.max(1, apMax)}
  ];
}
function metricTooltipFor(canvas, key){
  var wrap = canvas ? canvas.parentElement : null;
  if(!wrap) return null;
  var tip = wrap.querySelector('.metric-chart-tip');
  if(!tip){
    tip = document.createElement('div');
    tip.className = 'metric-chart-tip';
    tip.setAttribute('data-metric', key || '');
    wrap.appendChild(tip);
  }
  return tip;
}
function metricNearestPoint(rows, key, ts){
  var best = null, bestDiff = Infinity;
  (Array.isArray(rows) ? rows : []).forEach(function(p){
    var value = metricNumber(p && p[key]);
    if(value == null) return;
    var pt = Number(p.ts || 0);
    var diff = Math.abs(pt - ts);
    if(diff < bestDiff){
      bestDiff = diff;
      best = {row:p, ts:pt, value:value};
    }
  });
  return best;
}
function metricSyncZoomControl(){
  var z = Math.max(1, Math.min(100, Number(metricsState.zoom || 1)));
  metricsState.zoom = z;
  var input = qs('metrics-zoom');
  var label = qs('metrics-zoom-value');
  if(input) input.value = String(z);
  if(label) label.textContent = (Math.round(metricZoomFactor() * 10) / 10) + 'x';
}
function metricSetZoom(nextZoom, focusRatio){
  var rows = metricRowsSorted();
  var before = metricCurrentRange(rows);
  var ratio = Math.max(0, Math.min(1, Number(focusRatio == null ? 0.5 : focusRatio)));
  var focusTs = before.start + before.span * ratio;
  metricsState.zoom = Math.max(1, Math.min(100, Number(nextZoom || 1)));
  var span = Math.max(1800, metricWindowSec() / metricZoomFactor());
  var end = focusTs + (1 - ratio) * span;
  metricsState.panSec = before.latest - end;
  metricCurrentRange(rows);
  metricSyncZoomControl();
  drawMetricsChart();
}
function metricPanByPixels(canvas, dx){
  var key = canvas && canvas.getAttribute('data-metric');
  var meta = key ? metricsState.chartMeta[key] : null;
  if(!meta || !meta.range) return;
  var plotW = Math.max(1, meta.width - meta.pad.l - meta.pad.r);
  metricsState.panSec = Number(metricsState.panSec || 0) + (Number(dx || 0) / plotW) * meta.range.span;
  metricCurrentRange(metricRowsSorted());
  drawMetricsChart();
}
function metricPointerRatio(canvas, ev){
  var rect = canvas.getBoundingClientRect();
  if(!rect.width) return 0.5;
  return Math.max(0, Math.min(1, (Number(ev.clientX || 0) - rect.left) / rect.width));
}
function metricUpdateHoverFromEvent(canvas, ev){
  if(!canvas) return;
  metricsState.hover = {key:canvas.getAttribute('data-metric') || '', ratio:metricPointerRatio(canvas, ev)};
  drawMetricsChart();
}
function metricClearHover(){
  metricsState.hover = null;
  drawMetricsChart();
}
function metricBindCanvasEvents(canvas){
  if(!canvas || canvas.__metricBound) return;
  canvas.__metricBound = true;
  canvas.addEventListener('wheel', function(ev){
    ev.preventDefault();
    var step = ev.deltaY < 0 ? 6 : -6;
    metricSetZoom(Number(metricsState.zoom || 1) + step, metricPointerRatio(canvas, ev));
  }, {passive:false});
  canvas.addEventListener('pointerdown', function(ev){
    if(ev.button != null && ev.button !== 0) return;
    metricsState.drag = {key:canvas.getAttribute('data-metric') || '', lastX:Number(ev.clientX || 0), moved:false};
    var wrap = canvas.parentElement;
    if(wrap) wrap.classList.add('dragging');
    try{ canvas.setPointerCapture(ev.pointerId); }catch(_e){}
    ev.preventDefault();
  });
  canvas.addEventListener('pointermove', function(ev){
    if(metricsState.drag && metricsState.drag.key === (canvas.getAttribute('data-metric') || '')){
      var x = Number(ev.clientX || 0);
      var dx = x - Number(metricsState.drag.lastX || x);
      if(Math.abs(dx) >= 1){
        metricsState.drag.lastX = x;
        metricsState.drag.moved = true;
        metricPanByPixels(canvas, dx);
      }
      ev.preventDefault();
      return;
    }
    metricUpdateHoverFromEvent(canvas, ev);
  });
  function endDrag(ev){
    var wasDrag = metricsState.drag && metricsState.drag.key === (canvas.getAttribute('data-metric') || '');
    metricsState.drag = null;
    var wrap = canvas.parentElement;
    if(wrap) wrap.classList.remove('dragging');
    try{ canvas.releasePointerCapture(ev.pointerId); }catch(_e){}
    if(wasDrag) metricUpdateHoverFromEvent(canvas, ev);
  }
  canvas.addEventListener('pointerup', endDrag);
  canvas.addEventListener('pointercancel', endDrag);
  canvas.addEventListener('pointerleave', function(){
    if(metricsState.drag) return;
    metricClearHover();
  });
  canvas.addEventListener('dblclick', function(){
    metricsState.zoom = 1;
    metricsState.panSec = 0;
    metricSyncZoomControl();
    metricClearHover();
  });
}
function drawMetricsChart(){
  var allRows = metricRowsSorted();
  var range = metricCurrentRange(allRows);
  var rows = allRows.filter(function(x){ return Number(x.ts || 0) >= range.start && Number(x.ts || 0) <= range.end; });
  var defs = metricDefs(rows);
  metricsState.chartMeta = {};
  defs.forEach(function(def){ drawMetricSpark(def, rows, range); });
  var last = rows[rows.length - 1] || {};
  var status = qs('status-metrics');
  if(status){
    var panText = Number(metricsState.panSec || 0) > 1 ? (' | 视图偏移 ' + Math.round(Number(metricsState.panSec || 0) / 60) + ' 分钟') : '';
    status.textContent = rows.length ? ('样本 ' + rows.length
      + ' | 最新 CPU ' + fmtPct(last.cpu)
      + ' / 内存 ' + fmtPct(last.mem)
      + ' / 温度 ' + (last.temp == null ? '—' : Number(last.temp).toFixed(1) + '°C')
      + ' / AP ' + String(last.ap == null ? '—' : last.ap)
      + ' | 视图 ' + (Math.round(metricZoomFactor() * 10) / 10) + 'x' + panText) : '暂无负载数据';
  }
}
function drawMetricSpark(def, rows, range){
  var canvas = document.querySelector('.metric-spark[data-metric="'+def.key+'"]');
  var valueEl = qs('metric-value-' + def.key);
  var tip = canvas ? metricTooltipFor(canvas, def.key) : null;
  if(!canvas) return;
  var box = canvas.getBoundingClientRect();
  var dpr = window.devicePixelRatio || 1;
  var cssW = Math.max(260, box.width || (canvas.parentElement ? canvas.parentElement.clientWidth : 0) || 300);
  var cssH = Math.max(110, box.height || (canvas.parentElement ? canvas.parentElement.clientHeight : 0) || 136);
  var w = Math.round(cssW * dpr);
  var h = Math.round(cssH * dpr);
  if(canvas.width !== w) canvas.width = w;
  if(canvas.height !== h) canvas.height = h;
  var ctx = canvas.getContext('2d');
  ctx.clearRect(0,0,w,h);
  var styles = getComputedStyle(document.body);
  var border = (styles.getPropertyValue('--border') || '#444').trim();
  var muted = (styles.getPropertyValue('--muted') || '#888').trim();
  var txt = (styles.getPropertyValue('--txt') || '#fff').trim();
  var pad = {l:42, r:12, t:10, b:24};
  var padPx = {l:pad.l*dpr, r:pad.r*dpr, t:pad.t*dpr, b:pad.b*dpr};
  var plotW = Math.max(1, w - padPx.l - padPx.r);
  var plotH = Math.max(1, h - padPx.t - padPx.b);
  var start = range ? Number(range.start || 0) : 0;
  var end = range ? Number(range.end || (start + 1)) : 1;
  if(end <= start) end = start + 1;
  metricsState.chartMeta[def.key] = {width:cssW, height:cssH, pad:pad, range:{start:start,end:end,span:end-start}, rows:rows, def:def};
  if(tip) tip.style.display = 'none';
  ctx.strokeStyle = border;
  ctx.lineWidth = 1 * dpr;
  ctx.font = String(10 * dpr) + 'px sans-serif';
  ctx.fillStyle = muted;
  ctx.textBaseline = 'middle';
  ctx.beginPath();
  for(var gi=0;gi<=4;gi++){
    var gy = padPx.t + plotH * gi / 4;
    ctx.moveTo(padPx.l, gy); ctx.lineTo(w - padPx.r, gy);
    var gv = Math.max(0, Number(def.max || 100)) * (1 - gi / 4);
    ctx.fillText(def.axis ? def.axis(gv) : String(Math.round(gv)), 4 * dpr, gy);
  }
  for(var vi=0;vi<=4;vi++){
    var gx = padPx.l + plotW * vi / 4;
    ctx.moveTo(gx, padPx.t); ctx.lineTo(gx, h - padPx.b);
  }
  ctx.stroke();
  if(!rows.length){
    if(valueEl) valueEl.textContent = '—';
    ctx.fillStyle = muted;
    ctx.font = String(12 * dpr) + 'px sans-serif';
    ctx.fillText('暂无数据', padPx.l + 4 * dpr, h / 2);
    return;
  }
  function rawValue(p){ return metricNumber(p[def.key]); }
  var lastVal = null;
  for(var li=rows.length-1;li>=0;li--){
    lastVal = rawValue(rows[li]);
    if(lastVal != null) break;
  }
  if(valueEl) valueEl.textContent = def.fmt(lastVal);
  function xFor(ts){ return padPx.l + ((Number(ts || start) - start) / (end - start)) * plotW; }
  function yFor(v){
    var maxV = Math.max(1, Number(def.max || 100));
    var n = Math.max(0, Math.min(maxV, Number(v || 0)));
    return padPx.t + (1 - (n / maxV)) * plotH;
  }
  var drawn = false;
  var firstPt = null, lastPt = null;
  ctx.beginPath();
  rows.forEach(function(p){
    var raw = rawValue(p);
    if(raw == null) return;
    var x = xFor(p.ts), y = yFor(raw);
    if(!drawn){ ctx.moveTo(x,y); firstPt = {x:x,y:y}; drawn = true; }
    else ctx.lineTo(x,y);
    lastPt = {x:x,y:y};
  });
  if(drawn){
    ctx.save();
    ctx.lineTo(lastPt.x, h - padPx.b);
    ctx.lineTo(firstPt.x, h - padPx.b);
    ctx.closePath();
    ctx.globalAlpha = 0.14;
    ctx.fillStyle = def.color;
    ctx.fill();
    ctx.restore();
    ctx.beginPath();
    drawn = false;
    rows.forEach(function(p){
      var raw = rawValue(p);
      if(raw == null) return;
      var x = xFor(p.ts), y = yFor(raw);
      if(!drawn){ ctx.moveTo(x,y); drawn = true; }
      else ctx.lineTo(x,y);
    });
    ctx.strokeStyle = def.color;
    ctx.lineWidth = 2 * dpr;
    ctx.stroke();
  }
  ctx.fillStyle = muted;
  ctx.textBaseline = 'alphabetic';
  ctx.font = String(10 * dpr) + 'px sans-serif';
  ctx.fillText(fmtMetricTime(start).replace(/^\\d{4}\\//,''), padPx.l, h - 6 * dpr);
  var endLabel = fmtMetricTime(end).replace(/^\\d{4}\\//,'');
  var endW = ctx.measureText(endLabel).width;
  ctx.fillText(endLabel, Math.max(padPx.l, w - padPx.r - endW), h - 6 * dpr);
  if(metricsState.hover && metricsState.hover.key === def.key){
    var ratio = Math.max(0, Math.min(1, Number(metricsState.hover.ratio || 0)));
    var targetTs = start + (end - start) * ratio;
    var hit = metricNearestPoint(rows, def.key, targetTs);
    if(hit){
      var hx = xFor(hit.ts), hy = yFor(hit.value);
      ctx.save();
      ctx.setLineDash([4 * dpr, 4 * dpr]);
      ctx.strokeStyle = txt;
      ctx.globalAlpha = 0.48;
      ctx.lineWidth = 1 * dpr;
      ctx.beginPath();
      ctx.moveTo(hx, padPx.t);
      ctx.lineTo(hx, h - padPx.b);
      ctx.moveTo(padPx.l, hy);
      ctx.lineTo(w - padPx.r, hy);
      ctx.stroke();
      ctx.restore();
      ctx.beginPath();
      ctx.arc(hx, hy, 4 * dpr, 0, Math.PI * 2);
      ctx.fillStyle = def.color;
      ctx.fill();
      ctx.lineWidth = 2 * dpr;
      ctx.strokeStyle = txt;
      ctx.stroke();
      if(tip){
        var cssX = hx / dpr, cssY = hy / dpr;
        tip.classList.toggle('below', cssY < 52);
        tip.style.left = Math.max(74, Math.min(cssW - 74, cssX)) + 'px';
        tip.style.top = Math.max(18, Math.min(cssH - 18, cssY)) + 'px';
        tip.textContent = def.label + '  ' + def.fmt(hit.value) + '\\n' + fmtMetricTime(hit.ts);
        tip.style.display = 'block';
      }
    }
  }
}
async function loadMetrics(){
  const data = await getJson('/api/settings/metrics?window=' + encodeURIComponent(metricsState.window || '12h'));
  metricsState.items = Array.isArray(data.items) ? data.items : [];
  if(qs('status-metrics') && data.store_path){
    qs('status-metrics').textContent = '数据文件: ' + String(data.store_path);
  }
  drawMetricsChart();
}
function setMetricWindow(win){
  metricsState.window = (win === '7d' || win === '24h') ? win : '12h';
  metricsState.panSec = 0;
  metricsState.hover = null;
  qsa('.metric-window').forEach(function(btn){ btn.classList.toggle('active', btn.getAttribute('data-window') === metricsState.window); });
  loadMetrics().catch(function(e){ if(qs('status-metrics')) qs('status-metrics').textContent = e.message || String(e); });
}
async function updateModelsNow(){
  var btn = qs('btn-model-update-now');
  try{
    if(btn) btn.disabled = true;
    if(qs('model-update-state')) qs('model-update-state').textContent = '正在更新识别库...';
    const data = await postJson('/api/settings/models/update', {url: v('cfg-model-update-url')});
    if(qs('model-update-state')) qs('model-update-state').textContent = data.message || '识别库已更新。';
    showNotice(data.message || '识别库已更新。', 'ok', 3000);
    await loadVisual();
  }catch(e){
    if(qs('model-update-state')) qs('model-update-state').textContent = '更新失败: ' + (e.message || e);
    showNotice(e.message || e, 'warn', 4200);
  }finally{
    if(btn) btn.disabled = false;
  }
}
function renderAppUpdateState(state){
  var el = qs('app-update-state');
  if(!el) return;
  state = state || {};
  var current = state.current_short || (state.current_commit ? String(state.current_commit).slice(0, 12) : '');
  var latest = state.latest_short || (state.latest_commit ? String(state.latest_commit).slice(0, 12) : '');
  var lines = ['当前 commit: ' + (current || '未知')];
  lines.push('最新 commit: ' + (latest || '尚未检查'));
  if(state.running) lines.push('正在检查版本...');
  else if(state.last_error) lines.push('检查失败: ' + String(state.last_error));
  else if(state.checked) lines.push(state.update_available ? '发现新版本，更新需手动处理。' : '当前已是检查到的最新版本。');
  else lines.push('自动/手动检查只比较版本，不会自动更新程序。');
  el.textContent = lines.join(' | ');
}
async function checkAppVersionNow(){
  var btn = qs('btn-app-update-check');
  try{
    if(btn) btn.disabled = true;
    renderAppUpdateState({running:true});
    const data = await postJson('/api/settings/app-update/check', {});
    renderAppUpdateState((data && data.state) || {});
    showNotice(data && data.state && data.state.update_available ? '发现新版本，请手动更新。' : '版本检查完成。', 'ok', 3000);
  }catch(e){
    showNotice(e.message || e, 'warn', 4200);
  }finally{
    if(btn) btn.disabled = false;
  }
}
function cleanModelPrefix(prefix){
  return String(prefix == null ? '' : prefix).toUpperCase().replace(/[^0-9A-Z]/g, '').slice(0, 32);
}
function syncModelRowsFromInputs(){
  qsa('#model-map-list .model-map-row').forEach(function(row){
    var idx = Number(row.getAttribute('data-index'));
    if(!isFinite(idx) || !modelMapRows[idx]) return;
    var p = row.querySelector('.model-prefix');
    var m = row.querySelector('.model-name');
    modelMapRows[idx].prefix = cleanModelPrefix(p ? p.value : '');
    modelMapRows[idx].model = String((m && m.value) || '').trim();
    if(p) p.value = modelMapRows[idx].prefix;
  });
}
function filteredModelRows(){
  var q = String((qs('model-map-search') && qs('model-map-search').value) || '').trim().toLowerCase();
  return modelMapRows.map(function(row, idx){
    return {idx:idx, prefix:String(row.prefix || ''), model:String(row.model || '')};
  }).filter(function(row){
    if(!q) return true;
    return row.prefix.toLowerCase().indexOf(q) >= 0 || row.model.toLowerCase().indexOf(q) >= 0;
  });
}
function renderModelMapRows(){
  var root = qs('model-map-list');
  if(!root) return;
  var rows = filteredModelRows();
  if(!rows.length){
    root.innerHTML = '<div class="model-map-empty">暂无匹配条目。</div>';
  }else{
    root.innerHTML = rows.map(function(row){
      return '<div class="model-map-row" data-index="'+row.idx+'">'
        + '<input class="model-prefix" value="'+enc(row.prefix)+'" maxlength="32" spellcheck="false" placeholder="前缀">'
        + '<input class="model-name" value="'+enc(row.model)+'" spellcheck="false" placeholder="机型名称">'
        + '<button class="btn warn model-row-delete" type="button">删除</button>'
        + '</div>';
    }).join('');
  }
  var state = qs('model-map-editor-state');
  if(state){
    var suffix = modelMapPath ? (' | ' + modelMapPath) : '';
    state.textContent = '当前 ' + String(modelMapRows.length) + ' 条，保存后会立即刷新实时与历史机型。' + suffix;
  }
}
function collectModelMapRows(){
  syncModelRowsFromInputs();
  var seen = {};
  var out = [];
  modelMapRows.forEach(function(row){
    var prefix = cleanModelPrefix(row && row.prefix);
    var model = String((row && row.model) || '').trim();
    if(!prefix && !model) return;
    if(!prefix || !model) return;
    seen[prefix] = model;
  });
  Object.keys(seen).sort().forEach(function(prefix){
    out.push({prefix:prefix, model:seen[prefix]});
  });
  return out;
}
function addModelMapRow(prefix, model){
  syncModelRowsFromInputs();
  modelMapRows.unshift({prefix:cleanModelPrefix(prefix), model:String(model || '').trim()});
  if(qs('model-map-search')) qs('model-map-search').value = '';
  renderModelMapRows();
  var first = document.querySelector('#model-map-list .model-map-row input');
  if(first) first.focus();
}
async function loadModelEditor(){
  const data = await getJson('/api/settings/models/list');
  modelMapRows = (Array.isArray(data.items) ? data.items : []).map(function(row){
    return {prefix:cleanModelPrefix(row && row.prefix), model:String((row && row.model) || '').trim()};
  });
  modelMapPath = String(data.path || '');
  renderModelMapRows();
  if(data.warning && qs('model-map-editor-state')){
    qs('model-map-editor-state').textContent = String(data.warning);
  }
}
async function saveModelEditor(){
  var btn = qs('btn-model-map-save');
  try{
    if(btn) btn.disabled = true;
    var items = collectModelMapRows();
    const data = await postJson('/api/settings/models/save', {items:items});
    modelMapRows = (Array.isArray(data.items) ? data.items : items).map(function(row){
      return {prefix:cleanModelPrefix(row && row.prefix), model:String((row && row.model) || '').trim()};
    });
    modelMapPath = String(data.path || modelMapPath || '');
    renderModelMapRows();
    if(qs('model-update-state') && data.state){
      qs('model-update-state').textContent = '已加载 ' + String((data.state && data.state.loaded_count) || modelMapRows.length) + ' 条';
    }
    showNotice(data.message || '识别库已保存。', 'ok', 2600);
  }catch(e){
    showNotice(e.message || e, 'warn', 4200);
    if(qs('model-map-editor-state')) qs('model-map-editor-state').textContent = '保存失败: ' + (e.message || e);
  }finally{
    if(btn) btn.disabled = false;
  }
}
function collectVisualPayload(){
  return {
    basic: {
      iface: v('cfg-iface') || null,
      channel: settingsState.channelUseDefault ? null : n('cfg-channel'),
      channel_use_default: !!settingsState.channelUseDefault,
      time: n('cfg-time'),
      min_gap: n('cfg-min-gap'),
      rssi_delta: n('cfg-rssi-delta'),
      model_map: v('cfg-model-map'),
      history_file: v('cfg-history-file'),
      auto_self_heal: check('cfg-heal'),
      change_on_rssi: check('cfg-rssi-change'),
      change_on_payload: check('cfg-payload-change'),
      debug: check('cfg-debug'),
      dwell_2g: n('cfg-dwell2g'),
      dwell_5g: n('cfg-dwell5g'),
      settle: n('cfg-settle'),
      dwell_on_hit: n('cfg-hit-dwell'),
      hit_cap: n('cfg-hit-cap'),
      hop: check('cfg-hop'),
      hop_5g: check('cfg-hop5g'),
      scan_wifi_fast: check('cfg-fast'),
      no_tui: true
    },
    web: {
      dji_lookup_url: v('cfg-dji-url'),
      base_name: v('cfg-base-name'),
      base_lat: n('cfg-base-lat'),
      base_lon: n('cfg-base-lon'),
      base_zoom: n('cfg-base-zoom'),
      heading_ref_deg: n('cfg-heading-ref'),
      map_auto_center_idle_sec: n('cfg-map-idle'),
      access_list_enabled: check('cfg-web-access-enabled'),
      access_list_mode: v('cfg-web-access-mode') || 'allow',
      access_list: splitLines(qs('cfg-web-access-list').value || ''),
      alarm_zones: collectZoneRows()
    },
    notify: {
      enabled: check('cfg-notify-enabled'),
      notify_reonline: check('cfg-notify-reonline'),
      reonline_cooldown_sec: n('cfg-reonline'),
      send_timeout_sec: n('cfg-send-timeout'),
      wecom_webhooks: collectHookRows()
    },
    api: {
      enabled: check('cfg-api-enabled'),
      whitelist_enabled: check('cfg-api-whitelist-enabled'),
      whitelist_mode: v('cfg-api-whitelist-mode') || 'allow',
      whitelist: splitLines(qs('cfg-api-whitelist').value || '')
    },
    auth: {
      enabled: check('cfg-auth-enabled'),
      realm: v('cfg-auth-realm'),
      session_ttl_min: n('cfg-auth-ttl'),
      login_methods: ensureAuthLoginMethodSelection('', false),
      username: v('cfg-auth-user') || '__KEEP__',
      password: String((qs('cfg-auth-pass') && qs('cfg-auth-pass').value) || '').trim() || '__KEEP__'
    },
    model_update: {
      enabled: check('cfg-model-update-enabled'),
      url: v('cfg-model-update-url')
    },
    app_update: {
      enabled: check('cfg-app-update-enabled')
    },
    metrics: {
      retention_days: n('cfg-metrics-retention'),
      temperature_source: v('cfg-metrics-temp-source') || 'auto'
    }
  };
}
function visualPayloadSections(payload){
  payload = payload || {};
  return {
    capture: Object.assign({}, payload.basic || {}, {model_update: payload.model_update || {}, app_update: payload.app_update || {}}),
    map: {
      dji_lookup_url: ((payload.web || {}).dji_lookup_url),
      base_name: ((payload.web || {}).base_name),
      base_lat: ((payload.web || {}).base_lat),
      base_lon: ((payload.web || {}).base_lon),
      base_zoom: ((payload.web || {}).base_zoom),
      heading_ref_deg: ((payload.web || {}).heading_ref_deg),
      map_auto_center_idle_sec: ((payload.web || {}).map_auto_center_idle_sec)
    },
    zones: {alarm_zones: ((payload.web || {}).alarm_zones || [])},
    access: {
      web_access: {
        access_list_enabled: ((payload.web || {}).access_list_enabled),
        access_list_mode: ((payload.web || {}).access_list_mode),
        access_list: ((payload.web || {}).access_list || [])
      },
      notify: payload.notify || {},
      api: payload.api || {},
      auth: payload.auth || {}
    },
    metrics: payload.metrics || {}
  };
}
function setDraftUi(dirtyMap){
  dirtyMap = dirtyMap || {};
  settingsState.dirtyCards = dirtyMap;
  settingsState.visualDirty = Object.keys(dirtyMap).some(function(k){ return !!dirtyMap[k]; });
  qsa('.card[data-card-key]').forEach(function(card){
    var key = card.getAttribute('data-card-key') || '';
    card.classList.toggle('dirty', !!dirtyMap[key]);
  });
  if(qs('btn-test-visual')) qs('btn-test-visual').disabled = !settingsState.visualDirty;
  if(qs('btn-save-visual')) qs('btn-save-visual').disabled = !settingsState.visualDirty;
  if(qs('btn-save-visual-direct')) qs('btn-save-visual-direct').disabled = false;
  if(qs('draft-title')) qs('draft-title').textContent = settingsState.visualDirty ? '有未保存修改' : '当前没有未保存修改';
  if(qs('draft-meta')){
    var names = SETTINGS_DRAFT_SECTIONS
      .filter(function(item){ return !!dirtyMap[item.key]; })
      .map(function(item){ return item.label; });
    qs('draft-meta').textContent = settingsState.visualDirty
      ? ('已改动: ' + names.join('、') + '。测试结果独立于保存动作。')
      : '未保存改动按配置分组标记；测试结果独立于配置文件。';
  }
}
function updateVisualDraftState(){
  if(!settingsState.visualLoaded || !settingsState.visualInitial) return;
  var current = collectVisualPayload();
  var initialSections = visualPayloadSections(settingsState.visualInitial);
  var currentSections = visualPayloadSections(current);
  setDraftUi({
    capture: !sameJson(initialSections.capture, currentSections.capture),
    map: !sameJson(initialSections.map, currentSections.map),
    zones: !sameJson(initialSections.zones, currentSections.zones),
    access: !sameJson(initialSections.access, currentSections.access),
    metrics: !sameJson(initialSections.metrics, currentSections.metrics)
  });
}
function resetVisualDraftState(){
  settingsState.visualInitial = cloneJson(collectVisualPayload());
  setDraftUi({});
}
function bindVisualDraftTracking(){
  var root = document.querySelector('.panel[data-tab="visual"]');
  if(!root || root.getAttribute('data-dirty-bind') === '1') return;
  root.setAttribute('data-dirty-bind', '1');
  root.addEventListener('input', function(ev){
    updateVisualDraftState();
  });
  root.addEventListener('change', function(){
    updateVisualDraftState();
  });
}
function setVisualActionBusy(busy){
  ['btn-test-visual','btn-save-visual','btn-save-visual-direct','btn-reload-view'].forEach(function(id){
    var el = qs(id);
    if(!el) return;
    if(id === 'btn-test-visual' || id === 'btn-save-visual'){
      el.disabled = !!busy || (!settingsState.visualDirty);
    }else if(id === 'btn-save-visual-direct'){
      el.disabled = !!busy;
    }else{
      el.disabled = !!busy;
    }
  });
}
function setChannelUi(editing){
  settingsState.channelEditing = !!editing;
  var input = qs('cfg-channel');
  var editBtn = qs('btn-channel-edit');
  var resetBtn = qs('btn-channel-reset');
  var hint = qs('channel-hint');
  if(input) input.disabled = !editing;
  if(editBtn) editBtn.textContent = editing ? '锁定' : '编辑';
  if(resetBtn) resetBtn.style.display = settingsState.channelUseDefault ? 'none' : '';
  if(hint){
    hint.textContent = '';
    hint.style.display = 'none';
  }
}
function openReauth(action){
  reauthAction = action;
  qs('reauth-user').value = '';
  qs('reauth-pass').value = '';
  setStatus('reauth-status', '二次验证使用网页登录账号和密码。', false);
  qs('reauth-modal').classList.add('show');
  window.setTimeout(function(){ try{ qs('reauth-user').focus(); }catch(_e){} }, 30);
}
function closeReauth(){
  reauthAction = null;
  qs('reauth-modal').classList.remove('show');
}
function showOneTimeSecret(title, secret, note){
  oneTimeSecretValue = String(secret || '');
  qs('one-time-title').textContent = String(title || '只显示一次');
  qs('one-time-note').textContent = String(note || '关闭后不能再次查看或复制。');
  qs('one-time-secret').textContent = oneTimeSecretValue;
  qs('one-time-modal').classList.add('show');
}
function closeOneTimeSecret(){
  oneTimeSecretValue = '';
  qs('one-time-secret').textContent = '';
  qs('one-time-modal').classList.remove('show');
}
function b64uToBytes(text){
  var raw = String(text || '').replace(/-/g,'+').replace(/_/g,'/');
  while(raw.length % 4) raw += '=';
  if(!raw) return new Uint8Array(0);
  var bin = atob(raw);
  var out = new Uint8Array(bin.length);
  for(var i=0;i<bin.length;i++) out[i] = bin.charCodeAt(i);
  return out;
}
function bytesToB64u(bytes){
  var view = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes || []);
  var bin = '';
  for(var i=0;i<view.length;i++) bin += String.fromCharCode(view[i]);
  return btoa(bin).replace(/\\+/g,'-').replace(/\\//g,'_').replace(/=+$/,'');
}
function formatBytes(size){
  var n = Number(size);
  if(!isFinite(n) || n < 0) return '-';
  if(n < 1024) return String(n) + ' B';
  if(n < 1024 * 1024) return (n / 1024).toFixed(1).replace(/\\.0$/, '') + ' KB';
  if(n < 1024 * 1024 * 1024) return (n / (1024 * 1024)).toFixed(1).replace(/\\.0$/, '') + ' MB';
  return (n / (1024 * 1024 * 1024)).toFixed(1).replace(/\\.0$/, '') + ' GB';
}
function formatMtime(ts){
  var d = new Date(Number(ts || 0) * 1000);
  return isFinite(d.getTime()) ? d.toLocaleString() : '-';
}
function rawPathLabel(path){
  var raw = String(path || '');
  if(!raw) return '-';
  return raw;
}
function rawActivePath(){
  return String(settingsState.rawSelectedPath || '');
}
function rawSetMeta(data){
  data = data || {};
  if(qs('raw-tree-path')) qs('raw-tree-path').textContent = String(data.root || settingsState.rawRoot || '-');
  if(qs('raw-file-title')) qs('raw-file-title').textContent = String(data.name || ((data.rel_path && String(data.rel_path) !== '-') ? data.rel_path : '') || ((data.path && String(data.path) !== '-') ? data.path : '') || '未选择文件');
  if(qs('raw-file-path')) qs('raw-file-path').textContent = String(data.rel_path || data.path || '-');
  if(qs('raw-file-size')) qs('raw-file-size').textContent = data.size == null ? '-' : formatBytes(data.size);
  if(qs('raw-file-mtime')) qs('raw-file-mtime').textContent = data.mtime ? formatMtime(data.mtime) : '-';
}
function rawSetLocked(isLocked, message){
  var card = qs('raw-lock-card');
  var layout = qs('raw-layout');
  if(card) card.style.display = isLocked ? 'grid' : 'none';
  if(layout) layout.style.opacity = isLocked ? '0.55' : '1';
  var editor = qs('raw-editor');
  if(editor) editor.disabled = !!isLocked;
  ['btn-save-raw','btn-delete-raw','btn-load-raw'].forEach(function(id){
    var el = qs(id);
    if(el) el.disabled = !!isLocked && id !== 'btn-load-raw';
  });
  if(qs('raw-lock-copy') && message) qs('raw-lock-copy').textContent = String(message);
}
function rawRenderTreeNodes(nodes, selectedPath){
  var list = Array.isArray(nodes) ? nodes : [];
  if(!list.length) return '<div class="empty-state">暂无配置文件</div>';
  return list.map(function(node){
    node = node || {};
    var type = String(node.type || 'file');
    var name = enc(node.name || (type === 'dir' ? '目录' : '文件'));
    var rel = enc(node.rel_path || '');
    var path = enc(node.path || '');
    if(type === 'dir'){
      return '<details class="raw-dir" open><summary title="'+rel+'">'+name+'</summary><div class="raw-dir-child">'+rawRenderTreeNodes(node.children || [], selectedPath)+'</div></details>';
    }
    var active = String(node.path || '') === String(selectedPath || '');
    return '<button class="raw-file-btn'+(active ? ' active' : '')+'" type="button" data-path="'+path+'" data-rel="'+rel+'"><span class="clip" title="'+path+'">'+name+'</span><span class="micro">'+enc(formatBytes(node.size))+'</span></button>';
  }).join('');
}
function rawRenderTree(data){
  data = data || {};
  settingsState.rawTree = data;
  settingsState.rawRoot = String(data.root || settingsState.rawRoot || '');
  if(qs('raw-tree')) qs('raw-tree').innerHTML = rawRenderTreeNodes(data.tree || [], rawActivePath());
  rawSetMeta({root:data.root || settingsState.rawRoot || '-', name:'未选择文件', rel_path:'', path:'', size:null, mtime:null});
}
function rawFirstFile(nodes){
  var list = Array.isArray(nodes) ? nodes : [];
  for(var i=0;i<list.length;i++){
    var item = list[i] || {};
    if(item.type === 'file' && item.path) return String(item.path);
    var child = rawFirstFile(item.children || []);
    if(child) return child;
  }
  return '';
}
function rawRefreshButtons(){
  var unlocked = !!settingsState.rawUnlocked;
  var hasPath = !!settingsState.rawSelectedPath;
  var treeReady = !!settingsState.rawTree;
  ['btn-save-raw','btn-delete-raw','btn-load-raw'].forEach(function(id){
    var el = qs(id);
    if(!el) return;
    if(id === 'btn-load-raw'){
      el.disabled = !unlocked;
    }else{
      el.disabled = !unlocked || !hasPath || !treeReady;
    }
  });
}
async function rawLoadFile(path){
  var filePath = String(path || settingsState.rawSelectedPath || '').trim();
  if(!filePath) throw new Error('请选择一个配置文件');
  const data = await getJson('/api/config/file?path=' + encodeURIComponent(filePath));
  settingsState.rawUnlocked = true;
  settingsState.rawLoaded = true;
  settingsState.rawSelectedPath = String(data.path || filePath);
  settingsState.rawSelectedRel = String(data.rel_path || '');
  rawRenderTree(settingsState.rawTree || data.tree || {});
  rawSetMeta(data);
  if(qs('raw-editor')) qs('raw-editor').value = String(data.text || '');
  rawSetLocked(false, '');
  rawRefreshButtons();
  setStatus('status-raw', '已读取: ' + String(data.rel_path || data.path || '-'), false);
  return data;
}
async function rawLoadTree(){
  const data = await getJson('/api/config/tree');
  settingsState.rawUnlocked = true;
  settingsState.rawRoot = String(data.root || '');
  settingsState.rawTree = data;
  rawRenderTree(data);
  rawSetLocked(false, '');
  rawRefreshButtons();
  return data;
}
async function loadRaw(){
  try{
    const treeData = await rawLoadTree();
    var target = String(settingsState.rawSelectedPath || '');
    if(!target){
      target = rawFirstFile(treeData.tree || []);
      settingsState.rawSelectedPath = target;
    }
    if(target){
      await rawLoadFile(target);
    }else{
      settingsState.rawLoaded = true;
      rawSetMeta({root: treeData.root || settingsState.rawRoot || '-', name:'未选择文件', rel_path:'-', path:'-', size:null, mtime:null});
      if(qs('raw-editor')) qs('raw-editor').value = '';
      rawRefreshButtons();
    }
  }catch(e){
    var msg = e && e.message ? e.message : String(e);
    if(msg.indexOf('unlock required') >= 0 || msg.indexOf('raw config unlock required') >= 0){
      settingsState.rawUnlocked = false;
      settingsState.rawLoaded = false;
      rawSetLocked(true, '需要先验证网页登录密码，才能查看和编辑配置文件。');
      rawRefreshButtons();
      openReauth('raw-unlock');
      setStatus('status-raw', msg, true);
      return;
    }
    throw e;
  }
}
async function saveRaw(){
  var selected = String(settingsState.rawSelectedPath || '').trim();
  if(!selected) throw new Error('请选择一个配置文件');
  const data = await postJson('/api/settings/raw/save', {path:selected, text:String(qs('raw-editor').value || '')});
  settingsState.rawTree = null;
  settingsState.rawLoaded = false;
  setStatus('status-raw', '保存成功: ' + String(data.saved_to || '-') + '\\n' + String(data.reload_msg || ''), false);
  showNotice('原始配置已保存', 'ok', 3200);
  await loadRaw().catch(function(){});
}
async function deleteRawFile(){
  var selected = String(settingsState.rawSelectedPath || '').trim();
  if(!selected) throw new Error('请选择一个配置文件');
  if(!confirm('确认删除以下文件？\\n' + selected)) return;
  const data = await postJson('/api/config/file/delete', {path:selected});
  settingsState.rawSelectedPath = '';
  settingsState.rawSelectedRel = '';
  settingsState.rawTree = null;
  setStatus('status-raw', '已删除: ' + String(data.deleted_path || '-') + '\\n' + String(data.backup_path || ''), false);
  showNotice('原始配置文件已删除', 'ok', 2600);
  await loadRaw().catch(function(){});
}
function renderPasskeyRows(items){
  var root = qs('passkey-list');
  if(!root) return;
  var arr = Array.isArray(items) ? items.slice() : [];
  if(!arr.length){
    root.innerHTML = '<div class="empty-state">暂无通行密钥</div>';
    return;
  }
  root.innerHTML = arr.map(function(item, idx){
    item = item || {};
    var id = String(item.id || '');
    var name = enc(item.name || ('通行密钥 ' + (idx + 1)));
    var created = item.created_ts ? formatMtime(item.created_ts) : '-';
    var used = item.last_used_ts ? formatMtime(item.last_used_ts) : '未使用';
    return '<div class="passkey-row" data-id="'+enc(id)+'">'
      + '<div class="passkey-meta"><div class="passkey-title">'+name+'</div>'
      + '<div class="passkey-sub">创建时间: '+enc(created)+' | 上次使用: '+enc(used)+'</div>'
      + '<div class="passkey-badges"><span class="passkey-badge">签名计数 '+enc(String(item.sign_count || 0))+'</span><span class="passkey-badge">'+(item.enabled === false ? '已停用' : '已启用')+'</span></div>'
      + '</div><button class="btn ghost warn passkey-delete" type="button">删除</button></div>';
  }).join('');
}
async function createPasskeyWithCreds(){
  if(!window.PublicKeyCredential || !navigator.credentials || !navigator.credentials.create){
    throw new Error('当前浏览器不支持通行密钥创建');
  }
  var user = String(qs('reauth-user').value || '').trim();
  var pass = String(qs('reauth-pass').value || '');
  if(!user || !pass) throw new Error('请输入网页登录账号和密码');
  var name = String((qs('cfg-passkey-name') && qs('cfg-passkey-name').value) || '').trim();
  const start = await postJson('/api/settings/passkey/start', {username:user, password:pass, name:name});
  if(!start.ok) throw new Error(start.error || '通行密钥创建失败');
  var pk = start.publicKey || {};
  var challenge = b64uToBytes(pk.challenge || start.challenge || start.challenge_token || '');
  var userId = b64uToBytes((pk.user && pk.user.id) || '');
  var createOptions = {
    publicKey: {
      challenge: challenge,
      rp: pk.rp || {name:start.realm || 'Light RID Scanner', id:start.rp_id || location.hostname},
      user: {
        id: userId,
        name: (pk.user && pk.user.name) || user,
        displayName: (pk.user && pk.user.displayName) || (name || user),
      },
      pubKeyCredParams: pk.pubKeyCredParams || [{type:'public-key', alg:-7}],
      timeout: pk.timeout || start.timeout_ms || 300000,
      attestation: pk.attestation || 'none',
      authenticatorSelection: pk.authenticatorSelection || {userVerification:'preferred', residentKey:'preferred'},
      excludeCredentials: (pk.excludeCredentials || []).map(function(item){
        return {type:'public-key', id:b64uToBytes(item.id || '')};
      }),
    }
  };
  var cred = await navigator.credentials.create(createOptions);
  if(!cred) throw new Error('未获取到通行密钥凭据');
  var response = cred.response || {};
  const finish = await postJson('/api/settings/passkey/finish', {
    challenge: start.challenge || start.challenge_token,
    id: cred.id || '',
    rawId: bytesToB64u(cred.rawId || new Uint8Array(0)),
    type: cred.type || 'public-key',
    response: {
      clientDataJSON: bytesToB64u(response.clientDataJSON || new Uint8Array(0)),
      attestationObject: bytesToB64u(response.attestationObject || new Uint8Array(0)),
      authenticatorData: bytesToB64u(response.authenticatorData || new Uint8Array(0)),
      signature: bytesToB64u(response.signature || new Uint8Array(0)),
      userHandle: response.userHandle ? bytesToB64u(response.userHandle) : '',
    },
    name: name,
    username: user,
    next: '/',
  });
  renderPasskeyRows(finish.passkeys || []);
  showNotice('通行密钥已添加', 'ok', 3200);
  if(qs('cfg-passkey-name')) qs('cfg-passkey-name').value = '';
  return finish;
}
async function deletePasskey(id){
  const data = await postJson('/api/settings/passkey/delete', {id:String(id || '')});
  renderPasskeyRows(data.passkeys || []);
  showNotice('通行密钥已删除', 'ok', 2600);
  return data;
}
function fmtSsoExpiry(item){
  item = item || {};
  var expiresAt = Number(item.expires_at || 0);
  if(!isFinite(expiresAt) || expiresAt <= 0) return '无限时间';
  var left = Math.max(0, expiresAt - Date.now() / 1000);
  if(left <= 0) return '已过期';
  if(left < 3600) return Math.max(1, Math.round(left / 60)) + ' 分钟';
  if(left < 86400) return Math.round(left / 3600) + ' 小时';
  return Math.round(left / 86400) + ' 天';
}
function renderLoginLinks(items){
  loginLinks = Array.isArray(items) ? items.slice() : [];
  var root = qs('login-link-list');
  if(!root) return;
  if(!loginLinks.length){
    root.innerHTML = '<div class="empty-state">暂无 SSO 登录链接。</div>';
    return;
  }
  root.innerHTML = loginLinks.map(function(item, idx){
    var name = enc(item.name || ('SSO 链接 ' + (idx + 1)));
    var check = enc(item.check || '');
    var status = String(item.status || (item.active === false ? 'expired' : 'active'));
    var stateLabel = enc(item.status_label || (status === 'active' ? '可用' : '不可用'));
    var expireLabel = enc(fmtSsoExpiry(item));
    var modeLabel = item.single_use ? '<span class="sso-link-badge">单次</span>' : '<span class="sso-link-badge">多次</span>';
    var bad = (status === 'active') ? '' : ' bad';
    return '<div class="list-row sso-link-row" data-check="'+check+'">'
      + '<div class="sso-link-meta"><div class="sso-link-title"><span>'+name+'</span>'
      + '<span class="sso-link-badge'+bad+'">'+stateLabel+'</span><span class="sso-link-badge">'+expireLabel+'</span>'+modeLabel+'</div>'
      + '<div class="micro">使用此链接可一键登录系统</div></div>'
      + '<button class="btn ghost warn login-link-row-delete" type="button">删除</button>'
      + '</div>';
  }).join('');
}
async function deleteLoginLink(check){
  const r = await fetch(apiUrl('/api/settings/login-link/delete'), {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify({check:String(check || '')})
  });
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP ' + r.status));
  renderLoginLinks(d.links || []);
  qs('login-link-state').textContent = '已删除校验码，对应 SSO 链接立即失效。';
  return d;
}
function collectLoginLinkOptions(){
  var mode = String((qs('login-link-expire-mode') && qs('login-link-expire-mode').value) || '86400');
  var body = {
    name: String(qs('login-link-name').value || '').trim(),
    next: '/',
    single_use: !!(qs('login-link-single-use') && qs('login-link-single-use').checked)
  };
  if(mode === 'never'){
    body.expires = 'never';
  }else if(mode === 'custom'){
    body.ttl_min = Math.max(1, Number((qs('login-link-ttl-min') && qs('login-link-ttl-min').value) || 1440));
  }else{
    body.ttl_sec = Math.max(60, Number(mode || 86400));
  }
  return body;
}
function setLoginLinkExpiryUi(){
  var mode = String((qs('login-link-expire-mode') && qs('login-link-expire-mode').value) || '86400');
  var custom = qs('login-link-ttl-min');
  var field = qs('login-link-custom-field');
  if(custom) custom.disabled = (mode !== 'custom');
  if(field) field.classList.toggle('hidden', mode !== 'custom');
}
async function createLoginLinkWithCreds(){
  var user = String(qs('reauth-user').value || '').trim();
  var pass = String(qs('reauth-pass').value || '');
  if(!user || !pass){
    setStatus('reauth-status', '账号和密码不完整。', true);
    return null;
  }
  var reqBody = collectLoginLinkOptions();
  reqBody.username = user;
  reqBody.password = pass;
  const r = await fetch(apiUrl('/api/settings/login-link/create'), {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify(reqBody)
  });
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false){
    throw new Error(d.error || ('HTTP ' + r.status));
  }
  var url = String(d.url || d.path || '');
  var expireText = d.expires_at ? ('有效期至 ' + fmtMetricTime(d.expires_at)) : '无限时间';
  qs('login-link-state').textContent = '校验码 ' + String(d.check || '-').slice(0, 10) + '... 已加入列表；' + expireText + (d.single_use ? '；单次登录。' : '。');
  renderLoginLinks(d.links || []);
  showOneTimeSecret('SSO 登录链接', url, '这个链接只在本次弹窗显示，关闭后只能删除记录再重新生成。');
  return d;
}
function fillIfaceOptions(items, selected){
  const sel = qs('cfg-iface');
  if(!sel) return;
  const opts = ['<option value="">未绑定</option>'];
  (Array.isArray(items)?items:[]).forEach(function(it){
    const name = String(it.name || '');
    if(!name) return;
    opts.push('<option value="'+enc(name)+'">'+enc(name)+' ['+enc(String(it.mode||''))+'] '+(it.supports_5g ? '5G' : '2.4G')+'</option>');
  });
  sel.innerHTML = opts.join('');
  sel.value = selected || '';
}
function renderHookRows(items){
  var root = qs('wecom-list');
  var arr = Array.isArray(items) ? items.slice() : [];
  if(!arr.length) arr = [{index:'', name:'默认通道', enabled:true, key_masked:''}];
  root.innerHTML = arr.map(function(item, idx){
    var index = (item.index == null) ? '' : String(item.index);
    var name = enc(item.name || ('通道 ' + (idx + 1)));
    var mask = enc(item.key_masked || '');
    return '<div class="list-row hook-row" data-index="'+enc(index)+'">'
      +'<div class="hook-layout">'
      +'<div class="field"><label>通道名称</label><input class="hook-name" type="text" value="'+name+'"></div>'
      +'<div class="field"><label>Key</label><input class="hook-key" type="password" value="" placeholder="'+(mask ? '留空即不修改' : '新的 Key')+'"></div>'
      +'<div class="field"><label>启用</label><input class="hook-enabled" type="checkbox" '+(item.enabled ? 'checked' : '')+'></div>'
      +'<div class="field"><label>&nbsp;</label><button class="btn ghost row-remove" type="button">移除</button></div>'
      +'</div></div>';
  }).join('');
}
function renderZoneRows(items){
  var root = qs('zone-list');
  var arr = Array.isArray(items) ? items.slice() : [];
  if(!arr.length){
    root.innerHTML = '<div class="empty-state">暂无报警区域</div>';
    return;
  }
  root.innerHTML = arr.map(function(item, idx){
    return '<div class="list-row zone-row">'
      +'<div class="zone-layout">'
      +'<div class="field"><label>区域名称</label><input class="zone-name" type="text" value="'+enc(item.name || ('报警区域 ' + (idx + 1)))+'"></div>'
      +'<div class="field"><label>启用</label><input class="zone-enabled" type="checkbox" '+(item.enabled ? 'checked' : '')+'></div>'
      +'<div class="field"><label>A 点纬度</label><input class="zone-lat1" type="number" step="0.000001" value="'+(item.lat1 == null ? '' : enc(item.lat1))+'"></div>'
      +'<div class="field"><label>A 点经度</label><input class="zone-lon1" type="number" step="0.000001" value="'+(item.lon1 == null ? '' : enc(item.lon1))+'"></div>'
      +'<div class="field"><label>B 点纬度</label><input class="zone-lat2" type="number" step="0.000001" value="'+(item.lat2 == null ? '' : enc(item.lat2))+'"></div>'
      +'<div class="field"><label>B 点经度</label><input class="zone-lon2" type="number" step="0.000001" value="'+(item.lon2 == null ? '' : enc(item.lon2))+'"></div>'
      +'<div class="field"><label>&nbsp;</label><button class="btn ghost row-remove" type="button">移除</button></div>'
      +'</div></div>';
  }).join('');
}
function collectHookRows(){
  return qsa('.hook-row').map(function(row){
    var keyInput = row.querySelector('.hook-key');
    var idx = row.getAttribute('data-index') || '';
    var rawKey = String((keyInput && keyInput.value) || '').trim();
    if(!rawKey && idx !== '') rawKey = '__KEEP__';
    if(!rawKey && idx === '') return null;
    return {
      index: (idx === '' ? null : Number(idx)),
      name: String((row.querySelector('.hook-name') || {}).value || '').trim() || '默认通道',
      enabled: !!((row.querySelector('.hook-enabled') || {}).checked),
      key: rawKey
    };
  }).filter(function(x){ return !!x; });
}
function collectZoneRows(){
  return qsa('.zone-row').map(function(row, idx){
    function rowVal(sel){ return String(((row.querySelector(sel) || {}).value) || '').trim(); }
    function rowNum(sel){ var s = rowVal(sel); if(!s) return null; var f = Number(s); return isFinite(f) ? f : null; }
    var name = rowVal('.zone-name') || ('报警区域 ' + (idx + 1));
    var zone = {
      name: name,
      enabled: !!((row.querySelector('.zone-enabled') || {}).checked),
      lat1: rowNum('.zone-lat1'),
      lon1: rowNum('.zone-lon1'),
      lat2: rowNum('.zone-lat2'),
      lon2: rowNum('.zone-lon2')
    };
    if(zone.lat1 == null && zone.lon1 == null && zone.lat2 == null && zone.lon2 == null && !zone.enabled){
      return null;
    }
    return zone;
  }).filter(function(x){ return !!x; });
}
function fmtApiTokenExpiry(item){
  return fmtSsoExpiry(item || {});
}
function renderApiTokenRows(items){
  var root = qs('api-token-list');
  if(!root) return;
  apiTokenRows = Array.isArray(items) ? items.slice() : [];
  if(!apiTokenRows.length){
    root.innerHTML = '<div class="empty-state">暂无 API Token。添加后才能启用外部 API。</div>';
    return;
  }
  root.innerHTML = apiTokenRows.map(function(item, idx){
    item = item || {};
    var id = String(item.id || '');
    var name = enc(item.name || ('API Token ' + (idx + 1)));
    var status = String(item.status || (item.active === false ? 'expired' : 'active'));
    var stateLabel = enc(item.status_label || (status === 'active' ? '可用' : '不可用'));
    var bad = (status === 'active' || status === 'new') ? '' : ' bad';
    return '<div class="api-token-row" data-id="'+enc(id)+'" data-status="'+enc(status)+'" data-status-label="'+stateLabel+'">'
      + '<div class="api-token-head">'
      + '<div class="api-token-name" title="'+name+'">'+name+'</div>'
      + '<div class="api-token-badges"><span class="api-token-badge'+bad+'">'+stateLabel+'</span><span class="api-token-badge">'+enc(fmtApiTokenExpiry(item))+'</span><span class="api-token-badge">'+(item.single_use ? '单次' : '多次')+'</span></div>'
      + '</div>'
      + '<div class="api-token-grid">'
      + '<div class="micro">Token 只在创建成功时显示一次，之后不能查看、复制或修改。</div>'
      + '<button class="btn ghost warn api-token-row-remove" type="button">删除</button>'
      + '</div>'
      + '</div>';
  }).join('');
}
function collectApiTokenCreateOptions(){
  var mode = String((qs('api-token-new-expire-mode') && qs('api-token-new-expire-mode').value) || '86400');
  var body = {
    name: String((qs('api-token-new-name') && qs('api-token-new-name').value) || '').trim(),
    single_use: !!(qs('api-token-new-single-use') && qs('api-token-new-single-use').checked)
  };
  if(mode === 'never') body.expires = 'never';
  else if(mode === 'custom') body.ttl_min = Math.max(1, Number((qs('api-token-new-ttl-min') && qs('api-token-new-ttl-min').value) || 1440));
  else body.ttl_sec = Math.max(60, Number(mode || 86400));
  return body;
}
function setApiTokenCreateExpiryUi(){
  var mode = String((qs('api-token-new-expire-mode') && qs('api-token-new-expire-mode').value) || '86400');
  var custom = qs('api-token-new-ttl-min');
  var field = qs('api-token-custom-field');
  if(custom) custom.disabled = (mode !== 'custom');
  if(field) field.classList.toggle('hidden', mode !== 'custom');
}
function updateApiWhitelistUi(effective){
  var block = qs('api-whitelist-block');
  var enabled = !!effective;
  if(block) block.classList.toggle('disabled-block', !enabled);
  ['cfg-api-whitelist-enabled','cfg-api-whitelist-mode','cfg-api-whitelist'].forEach(function(id){
    var el = qs(id);
    if(el) el.disabled = !enabled;
  });
}
async function createApiTokenWithCreds(){
  var user = String(qs('reauth-user').value || '').trim();
  var pass = String(qs('reauth-pass').value || '');
  if(!user || !pass){
    setStatus('reauth-status', '账号和密码不完整。', true);
    return null;
  }
  var reqBody = collectApiTokenCreateOptions();
  reqBody.username = user;
  reqBody.password = pass;
  const r = await fetch(apiUrl('/api/settings/api-token/create'), {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify(reqBody)
  });
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP ' + r.status));
  renderApiTokenRows(d.tokens || []);
  updateApiWhitelistUi(true);
  showOneTimeSecret('API Token', String(d.token || ''), '这个 Token 只在本次弹窗显示，关闭后不能再次查看或复制。');
  if(qs('api-token-new-name')) qs('api-token-new-name').value = '';
  return d;
}
async function handleApiTokenListClick(ev){
  var row = ev.target && ev.target.closest ? ev.target.closest('.api-token-row') : null;
  if(!row) return;
  try{
    if(ev.target.closest('.api-token-row-remove')){
      var id = String(row.getAttribute('data-id') || '');
      if(!id) return;
      const d = await postJson('/api/settings/api-token/delete', {id:id});
      renderApiTokenRows(d.tokens || []);
      updateApiWhitelistUi(Array.isArray(d.tokens) && d.tokens.length > 0);
      showNotice('API Token 已删除。', 'ok', 2200);
      return;
    }
  }catch(e){
    showNotice(e.message || e, 'warn', 3600);
  }
}
function handleApiTokenListChange(_ev){}
function attachRowRemove(rootId, onEmptyFactory){
  var root = qs(rootId);
  if(!root) return;
  root.addEventListener('click', function(ev){
    var btn = ev.target && ev.target.closest ? ev.target.closest('.row-remove') : null;
    if(!btn) return;
    var row = btn.closest('.list-row');
    if(row && row.parentNode) row.parentNode.removeChild(row);
    if(!root.children.length && typeof onEmptyFactory === 'function') onEmptyFactory();
    updateVisualDraftState();
  });
}
async function useBrowserLocation(){
  if(!navigator.geolocation){ setStatus('status-visual', '当前浏览器不支持地理定位。', true); return; }
  if(!window.isSecureContext && !isLocalHostName(location.hostname || '')){
    setStatus('status-visual', '当前页面不是安全上下文，浏览器可能拒绝定位；HTTPS 或手动填写更稳定。', true);
  }
  navigator.geolocation.getCurrentPosition(function(pos){
    qs('cfg-base-lat').value = String(pos.coords.latitude || '');
    qs('cfg-base-lon').value = String(pos.coords.longitude || '');
    updateVisualDraftState();
    setStatus('status-visual', '已读取浏览器位置，等待测试或保存。', false);
  }, function(err){
    setStatus('status-visual', '定位失败: ' + (err && err.message ? err.message : err), true);
  }, {enableHighAccuracy:true, timeout:12000, maximumAge:0});
}
async function loadVisual(){
  const data = await getJson('/api/settings/view');
  const s = data.visual || {};
  const b = s.basic || {}, w = s.web || {}, nt = s.notify || {}, api = s.api || {}, auth = s.auth || {}, mu = s.model_update || {}, au = s.app_update || {}, mc = s.metrics || {};
  fillIfaceOptions(data.interfaces || [], b.iface || '');
  settingsState.visualLoaded = true;
  settingsState.channelUseDefault = !b.channel_custom;
  qs('cfg-channel').value = String(b.channel_effective == null ? 6 : b.channel_effective);
  setChannelUi(false);
  qs('cfg-time').value = String(b.time ?? '');
  qs('cfg-min-gap').value = String(b.min_gap ?? '');
  qs('cfg-rssi-delta').value = String(b.rssi_delta ?? '');
  qs('cfg-model-map').value = String(b.model_map || '');
  qs('cfg-model-update-enabled').checked = mu.enabled !== false;
  qs('cfg-app-update-enabled').checked = au.enabled !== false;
  qs('cfg-model-update-url').value = String(mu.url || '');
  renderAppUpdateState((au && au.state) || {});
  var must = (mu.state || {});
  qs('model-update-state').textContent = '已加载 ' + String(must.loaded_count || 0)
    + ' 条 | 上次成功 ' + (must.last_success_ts ? fmtMetricTime(must.last_success_ts) : '尚未成功')
    + (must.last_error ? (' | 最近错误: ' + String(must.last_error)) : '');
  qs('cfg-history-file').value = String(b.history_file || '');
  qs('cfg-heal').checked = !!b.auto_self_heal;
  qs('cfg-rssi-change').checked = !!b.change_on_rssi;
  qs('cfg-payload-change').checked = !!b.change_on_payload;
  qs('cfg-debug').checked = !!b.debug;
  qs('cfg-dwell2g').value = String(b.dwell_2g ?? '');
  qs('cfg-dwell5g').value = String(b.dwell_5g ?? '');
  qs('cfg-settle').value = String(b.settle ?? '');
  qs('cfg-hit-dwell').value = String(b.dwell_on_hit ?? '');
  qs('cfg-hit-cap').value = String(b.hit_cap ?? '');
  qs('cfg-hop').checked = !!b.hop;
  qs('cfg-hop5g').checked = !!b.hop_5g;
  qs('cfg-fast').checked = !!b.scan_wifi_fast;
  qs('cfg-base-name').value = String(w.base_name || '');
  qs('cfg-dji-url').value = String(w.dji_lookup_url || '');
  qs('cfg-base-lat').value = (w.base_lat == null) ? '' : String(w.base_lat);
  qs('cfg-base-lon').value = (w.base_lon == null) ? '' : String(w.base_lon);
  qs('cfg-base-zoom').value = String(w.base_zoom ?? '');
  qs('cfg-heading-ref').value = String(w.heading_ref_deg ?? '');
  qs('cfg-map-idle').value = String(w.map_auto_center_idle_sec ?? '');
  qs('cfg-web-access-enabled').checked = !!w.access_list_enabled;
  qs('cfg-web-access-mode').value = String(w.access_list_mode || 'allow');
  qs('cfg-web-access-list').value = Array.isArray(w.access_list) ? w.access_list.join('\\n') : '';
  renderZoneRows(Array.isArray(w.alarm_zones) ? w.alarm_zones : []);
  renderHostStats(data.host || {}, b);
  renderEulaState(data.eula || {});
  loadSystemServiceStatus().catch(function(e){ setStatus('status-system-service', e.message || e, true); });
  loadRuntimePanel().catch(function(){});
  loadMetrics().catch(function(){});
  qs('cfg-notify-enabled').checked = !!nt.enabled;
  qs('cfg-notify-reonline').checked = !!nt.notify_reonline;
  qs('cfg-reonline').value = String(nt.reonline_cooldown_sec ?? '');
  qs('cfg-send-timeout').value = String(nt.send_timeout_sec ?? '');
  renderHookRows(Array.isArray(nt.wecom_webhooks) ? nt.wecom_webhooks : []);
  qs('cfg-api-enabled').checked = !!api.enabled;
  renderApiTokenRows(Array.isArray(api.tokens) ? api.tokens : []);
  qs('cfg-api-whitelist-enabled').checked = !!api.whitelist_enabled;
  qs('cfg-api-whitelist-mode').value = String(api.whitelist_mode || 'allow');
  qs('cfg-api-whitelist').value = Array.isArray(api.whitelist) ? api.whitelist.join('\\n') : '';
  updateApiWhitelistUi(!!api.whitelist_effective);
  settingsState.authConfigured = !!auth.configured;
  qs('cfg-auth-enabled').checked = !!auth.enabled;
  qs('cfg-auth-method-password').checked = false;
  qs('cfg-auth-method-passkey').checked = false;
  qs('cfg-auth-method-sso').checked = false;
  (Array.isArray(auth.login_methods) && auth.login_methods.length ? auth.login_methods : ['password','passkey','sso']).forEach(function(method){
    var id = method === 'password' ? 'cfg-auth-method-password' : (method === 'passkey' ? 'cfg-auth-method-passkey' : (method === 'sso' ? 'cfg-auth-method-sso' : ''));
    if(id && qs(id)) qs(id).checked = true;
  });
  qs('cfg-auth-user').value = '';
  qs('cfg-auth-user').placeholder = '留空即不修改';
  qs('cfg-auth-pass').value = '';
  qs('cfg-auth-pass').placeholder = '留空即不修改';
  qs('cfg-auth-realm').value = String(auth.realm || 'Light RID Scanner');
  qs('cfg-auth-ttl').value = String(auth.session_ttl_min || 30);
  qs('login-link-name').value = '';
  if(qs('login-link-expire-mode')) qs('login-link-expire-mode').value = '86400';
  if(qs('login-link-ttl-min')) qs('login-link-ttl-min').value = '1440';
  if(qs('login-link-single-use')) qs('login-link-single-use').checked = false;
  if(qs('api-token-new-expire-mode')) qs('api-token-new-expire-mode').value = '86400';
  if(qs('api-token-new-ttl-min')) qs('api-token-new-ttl-min').value = '1440';
  if(qs('api-token-new-single-use')) qs('api-token-new-single-use').checked = false;
  setLoginLinkExpiryUi();
  setApiTokenCreateExpiryUi();
  qs('btn-api-token-add').disabled = !(auth.enabled && auth.configured);
  renderLoginLinks(auth.sso_links || []);
  renderPasskeyRows(Array.isArray(auth.passkeys) ? auth.passkeys : []);
  if(qs('cfg-passkey-name')) qs('cfg-passkey-name').value = '';
  syncAuthMethodUi();
  var rawAccess = data.raw_access || {};
  settingsState.rawUnlocked = !rawAccess.required || !!rawAccess.unlocked;
  settingsState.rawRoot = String(rawAccess.root || settingsState.rawRoot || '');
  settingsState.rawSelectedPath = String(data.path || settingsState.rawSelectedPath || '');
  rawSetLocked(!settingsState.rawUnlocked, settingsState.rawUnlocked ? '' : '需要先验证网页登录密码，才能查看和编辑配置文件。');
  rawRefreshButtons();
  qs('cfg-metrics-retention').value = String(mc.retention_days || 7);
  qs('cfg-metrics-temp-source').value = String(mc.temperature_source || 'auto');
  var apiTokenCount = Array.isArray(api.tokens) ? api.tokens.length : 0;
  qs('secret-state').textContent = '通知通道 ' + String((nt.wecom_webhooks || []).length || 0)
    + ' | API Token ' + String(apiTokenCount) + ' 个'
    + ' | 外部 API ' + (api.enabled ? '开启' : '关闭')
    + ' | 登录 ' + (auth.enabled ? (auth.configured ? '开启' : '未完成') : '关闭');
  resetVisualDraftState();
  if(data.path) setStatus('status-visual', '配置文件: ' + data.path, false);
}
async function loadRawLegacyUnused(){
  return loadRaw();
}
async function saveVisual(){
  const payload = collectVisualPayload();
  const data = await postJson('/api/settings/visual/save', payload);
  var msg = '测试并保存成功: ' + String(data.saved_to || '-');
  if(data.backup_path) msg += '\\n备份: ' + String(data.backup_path);
  if(data.reload_msg) msg += '\\n' + String(data.reload_msg);
  setStatus('status-visual', msg, false);
  showNotice('配置已保存并生效。', 'ok', 3600);
  await loadVisual();
}
async function testVisual(){
  const payload = collectVisualPayload();
  const data = await postJson('/api/settings/visual/test', payload);
  var msg = '测试通过，运行配置已回滚。';
  if(data.reload_msg) msg += '\\n' + String(data.reload_msg);
  setStatus('status-visual', msg, false);
  showNotice('测试通过，当前运行配置已回滚。', 'ok', 3000);
}
async function saveRawLegacyUnused(){
  return saveRaw();
}
function bindShellActions(){
  on('btn-back', 'click', function(){ location.href='/'; });
  on('btn-logs', 'click', function(){ location.href='/logs'; });
  on('btn-logout', 'click', function(){ location.href='/logout'; });
  on('btn-theme', 'click', function(){ applyTheme(document.body.classList.contains('theme-light') ? 'dark' : 'light'); });
  on('btn-open-hw', 'click', function(){ location.href='/hardware-assistant'; });
  on('btn-diagnostic-export', 'click', async function(){
    var btn = qs('btn-diagnostic-export');
    try{
      if(btn) btn.disabled = true;
      await downloadQualityReport();
    }catch(e){
      setStatus('status-visual', '质量分析包导出失败: ' + (e.message || e), true);
      showNotice(e.message || e, 'warn', 4200);
    }finally{
      if(btn) btn.disabled = false;
    }
  });
  on('btn-refresh-host', 'click', function(){
    guarded(loadVisual, 'status-visual');
  });
  on('btn-refresh-runtime', 'click', function(){
    guarded(loadRuntimePanel, 'status-runtime', '运行数据已刷新。', 1800, 3600);
  });
  on('btn-reload-view', 'click', function(){
    guarded(loadVisual, 'status-visual', '设置已重新读取。', 2200);
  });
}
function bindModelEditorActions(){
  on('btn-model-map-open', 'click', function(){
    qs('model-map-modal').classList.add('show');
    loadModelEditor().catch(function(e){ if(qs('model-map-editor-state')) qs('model-map-editor-state').textContent = '识别库读取失败: ' + (e.message || e); });
  });
  on('btn-model-map-close', 'click', function(){ qs('model-map-modal').classList.remove('show'); });
  on('model-map-modal', 'click', function(ev){ if(ev.target === qs('model-map-modal')) qs('model-map-modal').classList.remove('show'); });
  on('btn-model-update-now', 'click', updateModelsNow);
  on('btn-app-update-check', 'click', checkAppVersionNow);
  on('btn-model-map-add', 'click', function(){ addModelMapRow('', ''); });
  on('btn-model-map-save', 'click', saveModelEditor);
  on('model-map-search', 'input', function(){ syncModelRowsFromInputs(); renderModelMapRows(); });
  on('model-map-list', 'input', function(ev){
    var t = ev.target;
    if(t && t.classList && t.classList.contains('model-prefix')){
      t.value = cleanModelPrefix(t.value);
    }
    syncModelRowsFromInputs();
  });
  on('model-map-list', 'click', function(ev){
    var btn = ev.target && ev.target.closest ? ev.target.closest('.model-row-delete') : null;
    if(!btn) return;
    var row = btn.closest('.model-map-row');
    var idx = row ? Number(row.getAttribute('data-index')) : -1;
    if(isFinite(idx) && idx >= 0){
      syncModelRowsFromInputs();
      modelMapRows.splice(idx, 1);
      renderModelMapRows();
    }
  });
}
function bindMetricActions(){
  qsa('.metric-window').forEach(function(btn){
    btn.addEventListener('click', function(){ setMetricWindow(btn.getAttribute('data-window') || '12h'); });
  });
  on('metrics-zoom', 'input', function(){
    metricSetZoom(Number(qs('metrics-zoom').value || 1), 0.5);
  });
  qsa('.metric-spark').forEach(function(canvas){
    metricBindCanvasEvents(canvas);
  });
}
function bindHomeToolActions(){
  on('btn-home-freeze', 'click', freezeHomeOnReturn);
  on('btn-settings-web-notify', 'click', requestSettingsWebNotify);
  on('btn-settings-clear-history', 'click', clearHistoryFromSettings);
  on('btn-oobe-simple', 'click', function(){ location.href = '/oobe?manual=1&mode=simple'; });
  on('btn-oobe-full', 'click', function(){ location.href = '/settings?oobe=full'; showNotice('完整 OOBE 可直接在本页完成所有配置。', 'ok', 2600); });
  on('btn-eula-view', 'click', function(){ location.href = '/eula?next=/settings'; });
  on('btn-eula-revoke', 'click', revokeEulaAcceptance);
}
function bindCaptureActions(){
  on('btn-channel-edit', 'click', function(){
    setChannelUi(!settingsState.channelEditing);
  });
  on('btn-channel-reset', 'click', function(){
    settingsState.channelUseDefault = true;
    qs('cfg-channel').value = '6';
    setChannelUi(false);
  });
  on('cfg-channel', 'input', function(){
    var val = Number(qs('cfg-channel').value || '');
    settingsState.channelUseDefault = !(isFinite(val) && val !== 6);
    setChannelUi(settingsState.channelEditing);
  });
}
async function handleLoginLinkListClick(ev){
  var row = ev.target && ev.target.closest ? ev.target.closest('.sso-link-row') : null;
  if(!row) return;
  var check = row.getAttribute('data-check') || '';
  try{
    if(ev.target.closest('.login-link-row-delete')){
      await deleteLoginLink(check);
      showNotice('SSO 校验码已删除。', 'ok', 2400);
      return;
    }
  }catch(e){
    showNotice(e.message || e, 'warn', 3600);
  }
}
async function confirmReauthAction(){
  try{
    var action = reauthAction || 'copy';
    if(action === 'login-link'){
      await createLoginLinkWithCreds();
      setStatus('status-visual', 'SSO 登录链接已生成，只在弹窗中显示一次。', false);
      showNotice('SSO 登录链接已生成。', 'ok', 2600);
    }else if(action === 'api-token-create'){
      await createApiTokenWithCreds();
      setStatus('status-visual', 'API Token 已生成，只在弹窗中显示一次。', false);
      showNotice('API Token 已生成。', 'ok', 2600);
    }else if(action === 'raw-unlock'){
      var user = String(qs('reauth-user').value || '').trim();
      var pass = String(qs('reauth-pass').value || '');
      if(!user || !pass) throw new Error('请输入网页登录账号和密码');
      const data = await postJson('/api/settings/raw/unlock', {username:user, password:pass});
      if(!data.ok) throw new Error(data.error || '原始配置解锁失败');
      settingsState.rawUnlocked = true;
      rawSetLocked(false, '');
      rawRefreshButtons();
      showNotice('原始配置已解锁', 'ok', 2600);
      await loadRaw().catch(function(){});
    }else if(action === 'passkey-create'){
      await createPasskeyWithCreds();
      if(qs('passkey-state')) qs('passkey-state').textContent = '通行密钥已添加，可直接用于网页登录。';
    }else{
      throw new Error('不支持的二次验证操作');
    }
    closeReauth();
  }catch(e){
    setStatus('reauth-status', e.message || e, true);
    showNotice(e.message || e, 'warn', 3600);
  }
}
function bindAccessActions(){
  on('btn-api-token-add', 'click', function(){ openReauth('api-token-create'); });
  on('api-token-list', 'click', handleApiTokenListClick);
  on('api-token-list', 'change', handleApiTokenListChange);
  on('btn-login-link-create', 'click', function(){ openReauth('login-link'); });
  on('btn-passkey-add', 'click', function(){ openReauth('passkey-create'); });
  on('cfg-auth-enabled', 'change', syncAuthMethodUi);
  ['cfg-auth-method-password','cfg-auth-method-passkey','cfg-auth-method-sso'].forEach(function(id){
    on(id, 'change', function(){
      ensureAuthLoginMethodSelection(id, true);
      syncAuthMethodUi();
    });
  });
  on('login-link-expire-mode', 'change', setLoginLinkExpiryUi);
  on('api-token-new-expire-mode', 'change', setApiTokenCreateExpiryUi);
  on('login-link-list', 'click', handleLoginLinkListClick);
  on('passkey-list', 'click', function(ev){
    var row = ev.target && ev.target.closest ? ev.target.closest('.passkey-row') : null;
    if(!row) return;
    var id = row.getAttribute('data-id') || '';
    var del = ev.target && ev.target.closest ? ev.target.closest('.passkey-delete') : null;
    if(!del) return;
    deletePasskey(id).catch(function(e){ showNotice(e.message || e, 'warn', 3600); });
  });
  on('btn-one-time-copy', 'click', function(){ copyTextPlain(oneTimeSecretValue).then(function(){ showNotice('已复制。', 'ok', 1800); }).catch(function(e){ showNotice(e.message || e, 'warn', 2600); }); });
  on('btn-one-time-close', 'click', closeOneTimeSecret);
  on('one-time-modal', 'click', function(ev){ if(ev.target === qs('one-time-modal')) closeOneTimeSecret(); });
  on('btn-reauth-cancel', 'click', function(){ closeReauth(); });
  on('reauth-modal', 'click', function(ev){ if(ev.target === qs('reauth-modal')) closeReauth(); });
  document.addEventListener('keydown', function(ev){ if(ev.key === 'Escape' && qs('reauth-modal').classList.contains('show')) closeReauth(); });
  on('btn-reauth-confirm', 'click', confirmReauthAction);
  on('btn-hook-add', 'click', function(){
    var rows = collectHookRows();
    rows.push({index:null, name:'新通道', enabled:true, key:''});
    renderHookRows(rows);
    updateVisualDraftState();
  });
}
function bindSystemServiceActions(){
  on('btn-service-refresh', 'click', function(){
    guarded(loadSystemServiceStatus, 'status-system-service', '服务状态已刷新。', 1800, 3600);
  });
  on('btn-service-register', 'click', registerSystemdServiceFromSettings);
  on('btn-iw-install', 'click', installIwFromSettings);
  on('btn-security-repair', 'click', repairRuntimeSecurityFromSettings);
  on('btn-elevate-cancel', 'click', function(){ closeElevate(null); });
  on('btn-elevate-confirm', 'click', function(){ closeElevate(qs('elevate-pass') ? qs('elevate-pass').value : ''); });
  on('elevate-pass', 'keydown', function(ev){
    if(ev.key === 'Enter'){
      ev.preventDefault();
      closeElevate(qs('elevate-pass') ? qs('elevate-pass').value : '');
    }
  });
  on('elevate-modal', 'click', function(ev){ if(ev.target === qs('elevate-modal')) closeElevate(null); });
}
function bindRawActions(){
  on('btn-load-raw', 'click', function(){
    guarded(loadRaw, 'status-raw', '原始配置已读取。', 2200);
  });
  on('btn-save-raw', 'click', function(){
    guarded(saveRaw, 'status-raw', '原始配置已保存。', 2600);
  });
  on('btn-delete-raw', 'click', function(){
    guarded(deleteRawFile, 'status-raw', '原始配置文件已删除。', 2600);
  });
  on('btn-raw-unlock', 'click', function(){ openReauth('raw-unlock'); });
  on('btn-raw-unlock-inline', 'click', function(){ openReauth('raw-unlock'); });
  on('raw-tree', 'click', function(ev){
    var btn = ev.target && ev.target.closest ? ev.target.closest('.raw-file-btn') : null;
    if(!btn) return;
    var path = btn.getAttribute('data-path') || '';
    if(!path) return;
    settingsState.rawSelectedPath = path;
    settingsState.rawSelectedRel = btn.getAttribute('data-rel') || '';
    rawRefreshButtons();
    guarded(function(){ return rawLoadFile(path); }, 'status-raw', '已切换配置文件。', 1800);
  });
}
function bindSaveActions(){
  on('btn-test-visual', 'click', async function(){
    try{
      setVisualActionBusy(true);
      await testVisual();
    }catch(e){
      setStatus('status-visual', e.message || e, true);
      showNotice(e.message || e, 'warn', 3800);
    }finally{
      setVisualActionBusy(false);
    }
  });
  on('btn-save-visual', 'click', async function(){
    try{
      setVisualActionBusy(true);
      await saveVisual();
    }catch(e){
      setStatus('status-visual', e.message || e, true);
      showNotice(e.message || e, 'warn', 3800);
    }finally{
      setVisualActionBusy(false);
    }
  });
  on('btn-save-visual-direct', 'click', async function(){
    try{
      setVisualActionBusy(true);
      await saveVisual();
    }catch(e){
      setStatus('status-visual', e.message || e, true);
      showNotice(e.message || e, 'warn', 3800);
    }finally{
      setVisualActionBusy(false);
    }
  });
}
function bindMapAndZoneActions(){
  on('btn-zone-add', 'click', function(){
    var rows = collectZoneRows();
    rows.push({name:'报警区域 ' + (rows.length + 1), enabled:false, lat1:null, lon1:null, lat2:null, lon2:null});
    renderZoneRows(rows);
    updateVisualDraftState();
  });
  on('btn-browser-loc', 'click', useBrowserLocation);
  on('btn-clear-base-loc', 'click', function(){
    qs('cfg-base-lat').value='';
    qs('cfg-base-lon').value='';
    updateVisualDraftState();
    setStatus('status-visual', '已清空基站坐标，等待测试或保存。', false);
  });
  attachRowRemove('zone-list', function(){ renderZoneRows([]); });
}
function bindBrowserPreferenceActions(){
  ['pref-realtime-track','pref-track-2h','pref-new-firmware-parser'].forEach(function(id){
    on(id, 'change', saveBrowserPrefs);
  });
}
function bindViewportActions(){
  window.addEventListener('resize', function(){ syncSettingsViewport(); drawMetricsChart(); });
  if(window.visualViewport){
    try{
      window.visualViewport.addEventListener('resize', syncSettingsViewport);
      window.visualViewport.addEventListener('scroll', syncSettingsViewport);
    }catch(_e){}
  }
}
function initializeSettingsPage(){
  bindShellActions();
  bindCaptureActions();
  bindModelEditorActions();
  bindMetricActions();
  bindHomeToolActions();
  bindAccessActions();
  bindSystemServiceActions();
  bindRawActions();
  bindSaveActions();
  bindMapAndZoneActions();
  bindBrowserPreferenceActions();
  bindViewportActions();
  attachRowRemove('wecom-list', function(){ renderHookRows([]); });
  applyTheme(loadTheme());
  applyTabs();
  bindVisualDraftTracking();
  updateHomeActionButtons();
  syncSettingsViewport();
  loadBrowserPrefs();
  loadVisual().catch(function(e){ setStatus('status-visual', e.message || e, true); showNotice(e.message || e, 'warn', 3800); });
  window.setInterval(function(){ loadRuntimePanel().catch(function(){}); }, 2000);
  window.setInterval(function(){ loadMetrics().catch(function(){}); }, 2000);
}
initializeSettingsPage();
</script></body></html>"""

def http_server_thread() -> None:
    import socket as _socket, threading as _threading
    from http.server import BaseHTTPRequestHandler, HTTPServer
    from socketserver import ThreadingMixIn

    class ThreadingHTTPServer(ThreadingMixIn, HTTPServer):
        daemon_threads = True
        allow_reuse_address = True

    class Handler(BaseHTTPRequestHandler):
        server_version = APP_SERVER_HEADER
        sys_version = ""

        def end_headers(self):
            set_tok = getattr(self, "_auth_set_cookie_token", "")
            if set_tok:
                self.send_header(
                    "Set-Cookie",
                    f"{AUTH_SESSION_COOKIE}={set_tok}; Max-Age={int(AUTH_SESSION_TTL_SEC)}; Path=/; HttpOnly; SameSite=Lax",
                )
                self._auth_set_cookie_token = ""
            if getattr(self, "_auth_clear_cookie", False):
                self.send_header(
                    "Set-Cookie",
                    f"{AUTH_SESSION_COOKIE}=; Max-Age=0; Path=/; HttpOnly; SameSite=Lax",
                )
                self._auth_clear_cookie = False
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("X-Frame-Options", "DENY")
            self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
            self.send_header("Permissions-Policy", "geolocation=(self), microphone=(), camera=()")
            self.send_header(
                "Content-Security-Policy",
                "default-src 'self'; "
                "base-uri 'self'; object-src 'none'; frame-ancestors 'none'; form-action 'self'; "
                "script-src 'self' 'unsafe-inline' https://unpkg.com; "
                "style-src 'self' 'unsafe-inline' https://unpkg.com https://fonts.googleapis.com; "
                "font-src 'self' https://fonts.gstatic.com data:; "
                "img-src 'self' data: blob: https://*.is.autonavi.com; "
                "connect-src 'self' ws: wss: https://unpkg.com; "
                "media-src 'none'"
            )
            super().end_headers()

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

        def _send_bytes(self, body: bytes, content_type: str, filename: str | None = None, code: int = 200):
            body = bytes(body or b"")
            self.send_response(code)
            self.send_header("Content-Type", content_type or "application/octet-stream")
            self.send_header("Cache-Control", "no-store")
            if filename:
                safe = re.sub(r'[^A-Za-z0-9._-]+', '_', str(filename or "download.bin")).strip("._") or "download.bin"
                self.send_header("Content-Disposition", f'attachment; filename="{safe}"')
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except OSError as e:
                if getattr(e, "errno", None) not in (32, 54, 104, 10053, 10054):
                    raise

        def _redirect(self, location: str, code: int = 302):
            self.send_response(code)
            self.send_header("Location", str(location or "/"))
            self.send_header("Content-Length", "0")
            self.end_headers()

        def _read_json_body(self) -> dict:
            try:
                n = int(self.headers.get("Content-Length", "0") or "0")
            except Exception:
                n = 0
            if n > HTTP_JSON_MAX_BYTES:
                try:
                    self.rfile.read(min(n, 4096))
                except Exception:
                    pass
                return {}
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

        def _auth_fail(self):
            self.send_response(401)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            body = json.dumps({
                "ok": False,
                "error": "auth required",
                "auth_expired": True,
                "login_url": "/login?next=/",
            }, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _api_token_fail(self):
            self.send_response(401)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            body = json.dumps({
                "ok": False,
                "error": "api token required",
                "hint": "use X-API-Token or Authorization: Bearer <token>",
            }, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _rate_limit_fail(self, retry_after: int = 60):
            body = json.dumps({
                "ok": False,
                "error": "too many attempts",
                "retry_after_sec": int(max(1, retry_after)),
            }, ensure_ascii=False).encode("utf-8")
            self.send_response(429)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Retry-After", str(int(max(1, retry_after))))
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _page_api_fail(self, code: int = 403, message: str = "page session required"):
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            payload = {
                "ok": False,
                "error": message,
                "hint": "call this endpoint from the built-in web pages",
            }
            if int(code) == 401:
                payload["auth_expired"] = True
                payload["login_url"] = "/login?next=/"
            body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _api_whitelist_fail(self):
            self.send_response(403)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            body = json.dumps({
                "ok": False,
                "error": "当前无权访问该界面",
            }, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _access_denied_page(self):
            body = '<!doctype html><html lang="zh"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>403</title><style>body{margin:0;min-height:100dvh;display:grid;place-items:center;background:#201f1e;color:#f3f2f1;font-family:"Segoe UI","Microsoft YaHei",sans-serif}.box{border:1px solid #3b3a39;background:#2b2a29;padding:24px;border-radius:4px}h1{margin:0;font-size:26px}</style></head><body><div class="box"><h1>当前无权访问该界面</h1></div></body></html>'.encode("utf-8")
            self.send_response(403)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _require_auth(self) -> bool:
            if not _web_access_allowed(_client_ip_from_handler(self)):
                _op_log("web-access-deny", str(self.path or ""), ip=_client_ip_from_handler(self), ok=False)
                self._access_denied_page()
                return False
            if not _auth_enabled():
                return True
            if _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                return True
            req_path = str(self.path or "").split("?", 1)[0]
            if req_path == "/ws":
                # Avoid Safari repeatedly showing Basic-Auth dialog on websocket reconnect.
                self.send_response(403)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return False
            if req_path.startswith("/api/"):
                self._auth_fail()
                return False
            try:
                from urllib.parse import quote
                target = str(self.path or "/")
                if not target.startswith("/") or target.startswith("//"):
                    target = "/"
                self._redirect("/login?next=" + quote(target, safe="/?=&%"))
            except Exception:
                self._redirect("/login")
            return False

        def _require_page_api(self) -> bool:
            if not _web_access_allowed(_client_ip_from_handler(self)):
                _op_log("web-api-deny", str(self.path or ""), ip=_client_ip_from_handler(self), ok=False)
                self._page_api_fail(403, "当前无权访问该界面")
                return False
            if not _request_same_origin(self.headers):
                self._page_api_fail(403, "cross-origin page api denied")
                return False
            if not _page_api_header_ok(self.headers):
                self._page_api_fail(403, "page api header required")
                return False
            if _auth_enabled() and not _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                self._page_api_fail(401, "login required")
                return False
            return True

        def _require_raw_config_access(self) -> bool:
            if not self._require_page_api():
                return False
            if not (_auth_enabled() and _auth_hashes_present(AUTH_CFG)):
                return True
            if _raw_config_unlocked(self.headers.get("Cookie")):
                return True
            self._page_api_fail(403, "raw config unlock required")
            return False

        def _require_api_token(self, query: dict | None = None) -> bool:
            if not _api_token_enabled():
                return False
            ip = self.client_address[0] if self.client_address else ""
            if bool(API_CFG.get("whitelist_enabled")) and (not _api_access_allowed(ip)):
                _op_log("api-whitelist-deny", str(self.path or ""), ip=str(ip or "-"), ok=False)
                self._api_whitelist_fail()
                return False
            limited, retry_after = _rate_limited("api-token", ip, str(self.path or ""), limit=24, window_sec=120, block_sec=600)
            if limited:
                self._rate_limit_fail(retry_after)
                return False
            token = _api_token_from_request(self.headers, query)
            matched_token = _api_token_check_value(token)
            if matched_token:
                if bool(matched_token.get("single_use")):
                    _api_mark_token_used(str(matched_token.get("id") or ""))
                _rate_note("api-token", ip, str(self.path or ""), success=True, limit=24, window_sec=120, block_sec=600)
                return True
            _rate_note("api-token", ip, str(self.path or ""), success=False, limit=24, window_sec=120, block_sec=600)
            _op_log("api-token-deny", str(self.path or ""), ip=str(ip or "-"), ok=False)
            self._api_token_fail()
            return False

        def _require_public_api(self, query: dict | None = None) -> bool:
            if _api_token_enabled():
                return self._require_api_token(query)
            return self._require_page_api()

        def do_GET(self):
            from urllib.parse import urlparse, parse_qs, quote, unquote
            parsed = urlparse(self.path)
            path = parsed.path
            query = parse_qs(parsed.query or "")
            if path == "/favicon.ico":
                self.send_response(204)
                self.send_header("Cache-Control", "max-age=86400")
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
            if path == "/api/eula/status":
                self._send_json(_eula_status_payload(), 200)
                return
            if path == "/api/config/tree":
                if not self._require_raw_config_access():
                    return
                try:
                    root = _config_root_dir()
                    self._send_json({
                        "ok": True,
                        "root": root,
                        "root_name": os.path.basename(root.rstrip("\\/")) or root,
                        "tree": _config_tree_entries(root).get("tree") or [],
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path == "/api/config/file":
                if not self._require_raw_config_access():
                    return
                try:
                    file_path = _config_resolve_path((query.get("path") or [""])[0] if isinstance(query, dict) else None)
                    if not file_path:
                        self._send_json({"ok": False, "error": "invalid path"}, 400)
                        return
                    root = _config_root_dir()
                    with open(file_path, "r", encoding="utf-8") as f:
                        text = f.read()
                    st = os.stat(file_path)
                    self._send_json({
                        "ok": True,
                        "path": file_path,
                        "rel_path": _config_rel_path(file_path, root),
                        "root": root,
                        "name": os.path.basename(file_path),
                        "text": text,
                        "size": int(st.st_size),
                        "mtime": float(st.st_mtime),
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path in ("/eula", "/eula.html"):
                next_path = str((query.get("next") or ["/"])[0] or "/")
                if not next_path.startswith("/") or next_path.startswith("//"):
                    next_path = "/"
                body = _build_eula_html(next_path).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            if _eula_redirect_required(path):
                if path.startswith("/api/"):
                    self._send_json({
                        "ok": False,
                        "error": "eula required",
                        "eula_url": EULA_URL,
                    }, 428)
                else:
                    target = str(self.path or "/")
                    if not target.startswith("/") or target.startswith("//"):
                        target = "/"
                    self._redirect("/eula?next=" + quote(target, safe="/?=&%"))
                return
            if (not path.startswith("/api/")) and path != "/ws" and (not _web_access_allowed(_client_ip_from_handler(self))):
                _op_log("web-access-deny", str(self.path or ""), ip=_client_ip_from_handler(self), ok=False)
                self._access_denied_page()
                return
            if path == "/api/oobe/status":
                if not self._require_page_api():
                    return
                self._send_json(_oobe_status_payload(), 200)
                return
            if path in ("/oobe", "/oobe.html"):
                manual_oobe = _to_bool((query.get("manual") or ["0"])[0], False)
                if not _oobe_state().get("required") and not manual_oobe:
                    self._redirect("/")
                    return
                if (_auth_enabled() and _auth_hashes_present(AUTH_CFG)) and not _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                    self._redirect("/login?next=/oobe")
                    return
                body = _build_oobe_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            if _oobe_redirect_required(path) and not (path in ("/login", "/login.html") and _oobe_auth_required()):
                if path == "/ws":
                    self.send_response(503)
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                elif path.startswith("/api/"):
                    self._send_json({
                        "ok": False,
                        "error": "oobe required",
                        "oobe": _oobe_state(),
                    }, 409)
                else:
                    self._redirect("/oobe")
                return
            if path in ("/login", "/login.html"):
                next_path = str((query.get("next") or ["/"])[0] or "/")
                if not next_path.startswith("/") or next_path.startswith("//"):
                    next_path = "/"
                if not _auth_enabled():
                    self._redirect(next_path)
                    return
                user_hash = str((query.get("user") or [""])[0] or "")
                pass_hash = str((query.get("password") or [""])[0] or "")
                check_code = str((query.get("check") or [""])[0] or "")
                if user_hash and not pass_hash and ",password=" in user_hash:
                    user_hash, pass_hash = user_hash.split(",password=", 1)
                if user_hash and not pass_hash and "?password=" in user_hash:
                    user_hash, pass_hash = user_hash.split("?password=", 1)
                if pass_hash and not check_code and "?check=" in pass_hash:
                    pass_hash, check_code = pass_hash.split("?check=", 1)
                if user_hash and pass_hash:
                    ip = _client_ip_from_handler(self)
                    subject = (user_hash[:12] + ":" + check_code[:12])
                    limited, retry_after = _rate_limited("login-sso", ip, subject, limit=8, window_sec=300, block_sec=900)
                    if limited:
                        self._rate_limit_fail(retry_after)
                        return
                    sso_item = _auth_check_sso_link(user_hash, pass_hash, check_code)
                    ok_login = bool(sso_item)
                    _rate_note("login-sso", ip, subject, success=ok_login, limit=8, window_sec=300, block_sec=900)
                    _op_log("login-sso", "next=" + next_path, actor=subject, ip=ip, ok=ok_login)
                    if ok_login:
                        if bool((sso_item or {}).get("single_use")):
                            _auth_mark_sso_used(check_code)
                        self._auth_set_cookie_token = _auth_issue_session()
                        sso_next = str((sso_item or {}).get("next") or next_path or "/")
                        if not sso_next.startswith("/") or sso_next.startswith("//"):
                            sso_next = "/"
                        self._redirect(sso_next)
                    else:
                        body = _build_login_html(next_path, "SSO 登录失败或链接已失效", True).encode("utf-8")
                        self.send_response(401)
                        self.send_header("Content-Type", "text/html; charset=utf-8")
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body)
                    return
                if _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                    self._redirect(next_path)
                    return
                body = _build_login_html(next_path).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            if path == "/logout":
                _op_log("logout", "", ip=_client_ip_from_handler(self), ok=True)
                self._auth_clear_cookie = True
                self._redirect("/login")
                return
            if _path_uses_api_token(path):
                if not self._require_public_api(query):
                    return
            elif _path_is_page_api(path):
                if not self._require_page_api():
                    return
            elif not self._require_auth():
                return
            if path in ("/api", "/api/"):
                if not self._require_page_api():
                    return
                self._send_json(_api_token_docs_payload(), 200)
                return
            if path == "/api/docs":
                self._send_json(_api_token_docs_payload(), 200)
                return
            if path == "/api/health":
                now_mono = time.monotonic()
                now_wall = time.time()
                sniff = _sniff_health_meta(now_mono, now_wall)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "service": {
                        "uptime_sec": int(max(0.0, now_wall - APP_START_WALL)),
                        "sniff_state": sniff.get("state"),
                        "sniff_msg": sniff.get("msg"),
                        "sniff_iface": sniff.get("iface"),
                        "current_channel": int(current_channel or 0),
                    },
                }, 200)
                return
            if path in ("/api/v1", "/api/v1/"):
                self._send_json(_api_v1_home_payload(), 200)
                return
            if path == "/api/v1/snapshot":
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "data": _state_snapshot(),
                }, 200)
                return
            if path == "/api/v1/auth/status":
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "auth": (_api_v1_home_payload().get("auth") or {}),
                }, 200)
                return
            if path == "/api/v1/drones":
                online_only = _to_bool((query.get("online_only") or ["0"])[0], False)
                include_archived = _to_bool((query.get("include_archived") or ["1"])[0], True)
                snap = _state_snapshot()
                items = list(snap.get("drones") or [])
                if online_only:
                    items = [x for x in items if not bool(x.get("lost")) and not bool(x.get("archived"))]
                elif not include_archived:
                    items = [x for x in items if not bool(x.get("archived"))]
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "count": len(items),
                    "items": items,
                }, 200)
                return
            if path.startswith("/api/v1/drones/"):
                sn = unquote(path[len("/api/v1/drones/"):]).strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                snap = _state_snapshot()
                item = None
                for x in (snap.get("drones") or []):
                    if str(x.get("sn") or "") == sn:
                        item = x
                        break
                if not item:
                    self._send_json({"ok": False, "error": "sn not found"}, 404)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    track = _track_for_query(src.get("track") or [], query)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "item": item,
                    "track_count": len(track),
                    "track": track,
                }, 200)
                return
            if path == "/api/v1/aps":
                aps, aps_seq, aps_total = _ap_snapshot()
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "seq": aps_seq,
                    "total": aps_total,
                    "count": len(aps),
                    "items": aps,
                }, 200)
                return
            if path == "/api/v1/logs":
                log_type = str((query.get("type") or ["event"])[0] or "event").strip().lower()
                try:
                    limit = int((query.get("limit") or ["200"])[0] or "200")
                except Exception:
                    limit = 200
                limit = max(1, min(2000, limit))
                with log_lock:
                    if log_type == "scan":
                        rows = list(scan_buf)[-limit:]
                    elif log_type == "ap":
                        rows = list(ap_buf)[-limit:]
                    else:
                        log_type = "event"
                        rows = list(log_buf)[-limit:]
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "type": log_type,
                    "count": len(rows),
                    "items": rows,
                }, 200)
                return
            if path.startswith("/api/v1/tracks/"):
                sn = unquote(path[len("/api/v1/tracks/"):]).strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    track = _track_for_query(src.get("track") or [], query)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "sn": sn,
                    "count": len(track),
                    "track": track,
                }, 200)
                return
            if path in ("/", "/index.html"):
                body = _build_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path in ("/settings", "/settings.html"):
                body = _build_settings_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path in ("/logs", "/logs.html"):
                body = _build_logs_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path in ("/hardware-assistant", "/hardware-assistant.html"):
                body = _HW_PAGE_HTML.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path == "/api/config":
                if not self._require_raw_config_access():
                    return
                try:
                    self._send_json(_config_file_payload(APP_CONFIG_PATH), 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/config/tree":
                if not self._require_raw_config_access():
                    return
                try:
                    root = _config_root_dir()
                    self._send_json({
                        "ok": True,
                        "root": root,
                        "root_name": os.path.basename(root.rstrip("\\/")) or root,
                        "tree": _config_tree_entries(root).get("tree") or [],
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/config/file":
                if not self._require_raw_config_access():
                    return
                try:
                    file_path = _config_resolve_path((query.get("path") or [""])[0] if isinstance(query, dict) else None)
                    if not file_path:
                        self._send_json({"ok": False, "error": "invalid path"}, 400)
                        return
                    root = _config_root_dir()
                    with open(file_path, "r", encoding="utf-8") as f:
                        text = f.read()
                    st = os.stat(file_path)
                    self._send_json({
                        "ok": True,
                        "path": file_path,
                        "rel_path": _config_rel_path(file_path, root),
                        "root": root,
                        "name": os.path.basename(file_path),
                        "text": text,
                        "size": int(st.st_size),
                        "mtime": float(st.st_mtime),
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/settings/view":
                try:
                    self._send_json(_settings_view_payload(), 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/notifications":
                try:
                    limit = int((query.get("limit") or [str(NOTIFICATION_CENTER_MAX)])[0] or NOTIFICATION_CENTER_MAX)
                except Exception:
                    limit = NOTIFICATION_CENTER_MAX
                self._send_json(_notification_payload(limit), 200)
            elif path == "/api/settings/runtime":
                try:
                    limit = int((query.get("limit") or ["180"])[0] or "180")
                except Exception:
                    limit = 180
                self._send_json(_settings_runtime_payload(limit=limit), 200)
            elif path == "/api/settings/metrics":
                raw_window = str((query.get("window") or ["24h"])[0] or "24h").strip().lower()
                if raw_window in ("12h", "12"):
                    window_sec = 12 * 3600
                elif raw_window in ("7d", "7"):
                    window_sec = 7 * 86400
                else:
                    window_sec = 24 * 3600
                self._send_json(_host_metrics_payload(window_sec=window_sec), 200)
            elif path == "/api/settings/systemd/status":
                self._send_json(_systemd_service_status_payload(), 200)
            elif path == "/api/settings/models/list":
                self._send_json(_model_map_editor_payload(), 200)
            elif path == "/api/logs/view":
                try:
                    limit = int((query.get("limit") or ["500"])[0] or "500")
                except Exception:
                    limit = 500
                log_type = str((query.get("type") or ["runtime"])[0] or "runtime")
                self._send_json(_logs_snapshot(log_type, limit=limit), 200)
            elif path == "/api/logs/export":
                try:
                    limit = int((query.get("limit") or ["5000"])[0] or "5000")
                except Exception:
                    limit = 5000
                log_type = str((query.get("type") or ["all"])[0] or "all")
                try:
                    body, filename, ctype = _logs_export_bytes(log_type, limit=limit)
                    _op_log("logs-export", f"type={log_type} limit={limit}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_bytes(body, ctype, filename=filename, code=200)
                except Exception as e:
                    _op_log("logs-export", f"type={log_type} error={e}", ip=_client_ip_from_handler(self), ok=False)
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
            elif path == "/api/hw/status":
                try:
                    snap = _hw_submit_task({"op": "status"}, timeout_sec=10)
                    if snap.get("ok") and isinstance(snap.get("data"), dict):
                        data = snap.get("data")
                        data["ok"] = True
                        self._send_json(data, 200)
                    else:
                        self._send_json({"ok": False, "error": str(snap.get("error") or "status failed")}, 500)
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
                _op_log("tools-export-all", f"count={len(items)}", ip=_client_ip_from_handler(self), ok=True)
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
                _op_log("tools-export-track", f"sn={sn} count={len(track)}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "version": 1,
                    "exported_at": time.time(),
                    "sn": sn,
                    "count": len(track),
                    "track": track,
                }, 200)
            elif path == "/api/tools/diagnostic.zip":
                try:
                    body, filename = _diagnostic_zip_bytes()
                    _op_log("diagnostic-export", f"filename={filename} bytes={len(body)}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_bytes(body, "application/zip", filename=filename, code=200)
                except Exception as e:
                    _op_log("diagnostic-export", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/ws":
                # Headers are already parsed by BaseHTTPRequestHandler; read key directly.
                origin = str(self.headers.get("Origin") or "").strip()
                host = str(self.headers.get("Host") or "").strip()
                if origin and host:
                    try:
                        from urllib.parse import urlparse as _urlparse
                        o = _urlparse(origin)
                        if o.netloc and o.netloc.lower() != host.lower():
                            self.send_response(403)
                            self.end_headers()
                            return
                    except Exception:
                        pass
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
            if path == "/api/eula/accept":
                if not _request_same_origin(self.headers) or not _page_api_header_ok(self.headers):
                    self._page_api_fail(403, "page api header required")
                    return
                body = self._read_json_body()
                if not _to_bool(body.get("accepted"), False):
                    self._send_json({"ok": False, "error": "必须同意许可协议后才能继续"}, 400)
                    return
                ok, msg = _write_eula_acceptance()
                if not ok:
                    self._send_json({"ok": False, "error": msg}, 500)
                    return
                next_path = str(body.get("next") or "/")
                if not next_path.startswith("/") or next_path.startswith("//"):
                    next_path = "/"
                self._send_json({"ok": True, "accepted": True, "next": next_path, "set_path": msg}, 200)
                return
            if _eula_redirect_required(path):
                self._send_json({
                    "ok": False,
                    "error": "eula required",
                    "eula_url": EULA_URL,
                }, 428)
                return
            if path == "/api/oobe/save":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                rsp = _oobe_save_config(body)
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
                return
            if path == "/api/settings/raw/unlock":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                user = str(body.get("username") or "").strip()
                pwd = str(body.get("password") or "")
                if not user or not pwd:
                    self._send_json({"ok": False, "error": "账号和密码必须同时填写", "raw_access": _raw_config_access_payload(self.headers)}, 400)
                    return
                if not _auth_check_userpass(user, pwd):
                    self._send_json({"ok": False, "error": "账号或密码错误", "raw_access": _raw_config_access_payload(self.headers)}, 401)
                    return
                _raw_config_unlock_set(self.headers.get("Cookie"))
                self._send_json({
                    "ok": True,
                    "unlocked": True,
                    "raw_access": _raw_config_access_payload(self.headers),
                }, 200)
                return
            if path == "/api/passkey/login/start":
                if not _request_same_origin(self.headers) or not _page_api_header_ok(self.headers):
                    self._page_api_fail(403, "page api header required")
                    return
                self._read_json_body()
                rsp = _passkey_login_begin(self.headers)
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
                return
            if path == "/api/passkey/login/finish":
                if not _request_same_origin(self.headers) or not _page_api_header_ok(self.headers):
                    self._page_api_fail(403, "page api header required")
                    return
                body = self._read_json_body()
                rsp, code = _passkey_finish_login(body, self.headers, client_ip=_client_ip_from_handler(self))
                if rsp.get("ok"):
                    self._auth_set_cookie_token = str(rsp.pop("session") or "")
                self._send_json(rsp, code)
                return
            if _oobe_redirect_required(path) and not (path in ("/login", "/login.html") and _oobe_auth_required()):
                self._send_json({
                    "ok": False,
                    "error": "oobe required",
                    "oobe": _oobe_state(),
                }, 409)
                return
            if path in ("/login", "/login.html"):
                body = self._read_json_body()
                user = str(body.get("username") or "")
                pwd = str(body.get("password") or "")
                if not _auth_login_method_enabled("password"):
                    self._send_json({"ok": False, "error": "账号密码登录已关闭"}, 403)
                    return
                ip = _client_ip_from_handler(self)
                limited, retry_after = _rate_limited("login", ip, user, limit=8, window_sec=300, block_sec=900)
                if limited:
                    self._rate_limit_fail(retry_after)
                    return
                ok_login = _auth_check_userpass(user, pwd)
                _rate_note("login", ip, user, success=ok_login, limit=8, window_sec=300, block_sec=900)
                _op_log("login", "", actor=user or "-", ip=ip, ok=ok_login)
                if ok_login:
                    self._auth_set_cookie_token = _auth_issue_session()
                    self._send_json({"ok": True, "next": "/"}, 200)
                else:
                    self._send_json({"ok": False, "error": "账号或密码错误"}, 401)
                return
            if _path_uses_api_token(path):
                if not self._require_public_api(None):
                    return
            elif _path_is_page_api(path):
                if not self._require_page_api():
                    return
            elif not self._require_auth():
                return
            try:
                body_len = int(self.headers.get("Content-Length", "0") or "0")
            except Exception:
                body_len = 0
            if body_len > HTTP_JSON_MAX_BYTES:
                self._send_json({"ok": False, "error": f"request too large (>{HTTP_JSON_MAX_BYTES} bytes)"}, 413)
                return
            if path == "/api/notifications":
                body = self._read_json_body()
                item = _notification_add(
                    str(body.get("text") or ""),
                    str(body.get("kind") or "info"),
                    "page",
                )
                if not item:
                    self._send_json({"ok": False, "error": "text required"}, 400)
                    return
                payload = _notification_payload()
                payload["item"] = item
                self._send_json(payload, 200)
                return
            if path == "/api/notifications/delete":
                body = self._read_json_body()
                removed = _notification_delete(body.get("id"))
                payload = _notification_payload()
                payload["removed"] = bool(removed)
                self._send_json(payload, 200)
                return
            if path == "/api/notifications/clear":
                self._read_json_body()
                cleared = _notification_clear()
                self._send_json({"ok": True, "cleared": cleared, "seq": int(notification_seq), "count": 0, "items": []}, 200)
                return
            if path == "/api/eula/revoke":
                self._read_json_body()
                ok, msg = _revoke_eula_acceptance()
                if not ok:
                    self._send_json({"ok": False, "error": msg}, 500)
                    return
                self._send_json({"ok": True, "accepted": False, "set_path": msg, "next": "/eula?next=/settings"}, 200)
                return
            if path == "/api/v1/auth/logout":
                self._send_json({"ok": True, "api": _api_meta(), "logout": False, "token_api": True}, 200)
                return
            if path == "/api/v1/history/clear":
                try:
                    cleared, removed = clear_history_store(delete_file=True)
                    _op_log("api-v1-history-clear", f"cleared={cleared} file_removed={removed}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_json({
                        "ok": True,
                        "api": _api_meta(),
                        "cleared": cleared,
                        "file_removed": removed,
                        "history_file": HISTORY_STORE_PATH,
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path == "/api/v1/history/delete":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                removed = delete_history_item(sn)
                _op_log("api-v1-history-delete", f"sn={sn} removed={removed}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "sn": sn,
                    "removed": bool(removed),
                }, 200)
                return
            if path == "/api/v1/tracks/clear":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                affected = clear_track_store(sn if sn else None)
                _op_log("api-v1-track-clear", f"sn={sn or '*'} affected={affected}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "sn": (sn or None),
                    "affected": int(affected),
                }, 200)
                return
            if path == "/api/v1/config/reload":
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                try:
                    cfg_loaded = load_app_config(APP_CONFIG_PATH)
                    r_ok, r_msg = reload_runtime_config(cfg_loaded)
                    _op_log("api-v1-config-reload", f"ok={r_ok} msg={r_msg}", ip=_client_ip_from_handler(self), ok=bool(r_ok))
                    self._send_json({
                        "ok": True,
                        "api": _api_meta(),
                        "reloaded": bool(r_ok),
                        "reload_msg": str(r_msg or ""),
                        "config_path": APP_CONFIG_PATH,
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path == "/api/history/clear":
                self._read_json_body()
                try:
                    cleared, removed = clear_history_store(delete_file=True)
                    _op_log("history-clear", f"cleared={cleared} file_removed={removed}", ip=_client_ip_from_handler(self), ok=True)
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
                _op_log("history-delete", f"sn={sn} removed={removed}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "sn": sn, "removed": bool(removed)}, 200)
            elif path == "/api/tracks/clear":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                affected = clear_track_store(sn if sn else None)
                _op_log("track-clear", f"sn={sn or '*'} affected={affected}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "sn": (sn or None),
                    "affected": int(affected),
                }, 200)
            elif path == "/api/tools/import/all":
                body = self._read_json_body()
                payload = body.get("payload", body) if isinstance(body, dict) else body
                valid_payload = False
                if isinstance(payload, list):
                    valid_payload = True
                elif isinstance(payload, dict):
                    valid_payload = isinstance(payload.get("items"), list) or isinstance(payload.get("drones"), list)
                if not valid_payload:
                    self._send_json({"ok": False, "error": "invalid payload: expect items[]/drones[] or list"}, 400)
                    return
                added, updated, skipped = import_details_payload(payload)
                _op_log("tools-import-all", f"added={added} updated={updated} skipped={skipped}", ip=_client_ip_from_handler(self), ok=True)
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
                if not isinstance(track_raw, list):
                    self._send_json({"ok": False, "error": "track must be array"}, 400)
                    return
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
                _op_log("tools-import-track", f"sn={sn} count={len(track)}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "sn": sn,
                    "count": len(track),
                }, 200)
            elif path == "/api/hw/op":
                body = self._read_json_body()
                op = str(body.get("op") or "").strip().lower()
                if not op:
                    self._send_json({"ok": False, "error": "op required"}, 400)
                    return
                try:
                    rsp = _hw_submit_task(body, timeout_sec=15)
                    code = 200 if rsp.get("ok") else 500
                    _op_log("hw-op", f"op={op} ok={rsp.get('ok')} iface={body.get('iface') or ''}", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                    self._send_json(rsp, code)
                except Exception as e:
                    _op_log("hw-op", f"op={op} error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e)}, 500)
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
                        _op_log("admin-restart", f"schedule_failed={msg}", ip=_client_ip_from_handler(self), ok=False)
                        self._send_json({"ok": False, "error": msg}, 409)
                        return
                    _op_log("admin-restart", f"save={save_cfg} args={tokens}", ip=_client_ip_from_handler(self), ok=True)
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
                if not self._require_raw_config_access():
                    return
                body = self._read_json_body()
                try:
                    rsp = _config_file_save_payload(str(body.get("path") or APP_CONFIG_PATH or ""), str(body.get("text") or ""), tag="config")
                    self._send_json(rsp, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
            elif path == "/api/settings/visual/test":
                body = self._read_json_body()
                rsp = _save_visual_settings(body, test_only=True)
                _op_log("settings-test", str(rsp.get("error") or rsp.get("reload_msg") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
            elif path == "/api/settings/visual/save":
                body = self._read_json_body()
                rsp = _save_visual_settings(body, test_only=False)
                _op_log("settings-save", str(rsp.get("error") or rsp.get("backup_path") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
            elif path == "/api/settings/raw/save":
                if not self._require_raw_config_access():
                    return
                body = self._read_json_body()
                try:
                    rsp = _config_file_save_payload(str(body.get("path") or APP_CONFIG_PATH or ""), str(body.get("text") or ""), tag="raw")
                    self._send_json(rsp, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
            elif path == "/api/config/file/delete":
                if not self._require_raw_config_access():
                    return
                body = self._read_json_body()
                try:
                    rsp = _config_file_delete_payload(str(body.get("path") or ""))
                    self._send_json(rsp, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
            elif path == "/api/settings/passkey/start":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                rsp = _passkey_register_begin(body, self.headers, client_ip=_client_ip_from_handler(self))
                code = 200
                if isinstance(rsp, tuple):
                    payload, code = rsp
                    self._send_json(payload, code)
                else:
                    code = 200 if rsp.get("ok") else 400
                    self._send_json(rsp, code)
            elif path == "/api/settings/passkey/finish":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                rsp, code = _passkey_finish_register(body, self.headers, client_ip=_client_ip_from_handler(self))
                self._send_json(rsp, code)
            elif path == "/api/settings/passkey/delete":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                passkey_id = str(body.get("id") or "").strip()
                if not passkey_id:
                    self._send_json({"ok": False, "error": "id required"}, 400)
                    return
                def _remove_passkey(items):
                    return [x for x in items if str((x or {}).get("id") or "") != passkey_id]
                ok, msg, passkeys = _auth_mutate_passkeys(_remove_passkey, tag="passkey_delete")
                if not ok:
                    self._send_json({"ok": False, "error": msg, "passkeys": passkeys}, 500)
                    return
                _op_log("passkey-delete", "id=" + passkey_id[:16], actor="-", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "passkeys": passkeys, "id": passkey_id}, 200)
                return
            elif path == "/api/settings/notify/test":
                ok, resp = send_test_notification_from_config()
                _op_log("notify-test", str(resp or ""), ip=_client_ip_from_handler(self), ok=bool(ok))
                self._send_json({"ok": bool(ok), "resp": resp}, 200 if ok else 500)
            elif path == "/api/settings/models/update":
                body = self._read_json_body()
                rsp = update_model_map_from_url(manual=True, url_override=str(body.get("url") or "").strip() or None)
                self._send_json(rsp, 200 if rsp.get("ok") else 500)
            elif path == "/api/settings/app-update/check":
                self._read_json_body()
                rsp = _check_app_update_once(manual=True)
                self._send_json(rsp, 200 if rsp.get("ok") else 500)
            elif path == "/api/settings/systemd/register":
                body = self._read_json_body()
                if not bool(body.get("confirm")):
                    self._send_json({"ok": False, "error": "confirm required", "status": _systemd_service_status_payload()}, 400)
                    return
                rsp = register_systemd_service(sudo_password=_sudo_password_from_body(body))
                _op_log("systemd-register", str(rsp.get("error") or rsp.get("message") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                if rsp.get("ok"):
                    self._send_json(rsp, 200)
                else:
                    err = str(rsp.get("error") or "")
                    code = 403 if ("root" in err or "权限" in err) else 500
                    self._send_json(rsp, code)
            elif path == "/api/settings/iw/install":
                body = self._read_json_body()
                if not bool(body.get("confirm")):
                    self._send_json({"ok": False, "error": "confirm required", "status": _systemd_service_status_payload()}, 400)
                    return
                rsp = _install_iw_package(sudo_password=_sudo_password_from_body(body))
                status = _systemd_service_status_payload()
                payload = dict(rsp)
                payload["status"] = status
                payload["message"] = "iw 已安装并可用。" if rsp.get("ok") else str(rsp.get("error") or "iw 安装失败")
                _op_log("iw-install", payload.get("message") or "", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                if rsp.get("ok"):
                    self._send_json(payload, 200)
                else:
                    err = str(rsp.get("error") or "")
                    code = 403 if ("root" in err or "权限" in err) else 500
                    self._send_json(payload, code)
            elif path == "/api/settings/security/repair":
                body = self._read_json_body()
                if not bool(body.get("confirm")):
                    self._send_json({"ok": False, "error": "confirm required", "status": _systemd_service_status_payload()}, 400)
                    return
                rsp = repair_runtime_security(sudo_password=_sudo_password_from_body(body))
                _op_log("security-repair", str(rsp.get("error") or rsp.get("message") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                if rsp.get("ok"):
                    self._send_json(rsp, 200)
                else:
                    err = str(rsp.get("error") or "")
                    code = 403 if ("root" in err or "权限" in err or "sudo" in err) else 500
                    self._send_json(rsp, code)
            elif path == "/api/settings/models/save":
                body = self._read_json_body()
                try:
                    rsp = save_model_map_entries(body.get("items") if isinstance(body, dict) else None)
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("model-map-save", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e), "state": _model_update_status_payload()}, 400)
            elif path == "/api/settings/models/upsert":
                body = self._read_json_body()
                try:
                    rsp = upsert_model_map_entry(
                        prefix=str(body.get("prefix") or ""),
                        model=str(body.get("model") or ""),
                        sn=str(body.get("sn") or ""),
                    )
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("model-map-upsert", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e), "state": _model_update_status_payload()}, 400)
            elif path == "/api/settings/api-token/create":
                body = self._read_json_body()
                ip = _client_ip_from_handler(self)
                subject = str(body.get("username") or "-") if body else "-"
                limited, retry_after = _rate_limited("api-token-create", ip, subject, limit=5, window_sec=300, block_sec=900)
                if limited:
                    self._rate_limit_fail(retry_after)
                    return
                payload, code = _build_api_token_create_payload(body, headers=self.headers, client_ip=ip)
                _rate_note("api-token-create", ip, subject, success=bool(payload.get("ok")), limit=5, window_sec=300, block_sec=900)
                self._send_json(payload, code)
            elif path == "/api/settings/api-token/delete":
                body = self._read_json_body()
                token_id = str(body.get("id") or "").strip()
                if not token_id:
                    self._send_json({"ok": False, "error": "id required"}, 400)
                    return
                def _remove_token(tokens):
                    return [x for x in tokens if str((x or {}).get("id") or "") != token_id]
                ok, msg, tokens = _api_mutate_tokens(_remove_token, tag="api_token_delete")
                if not ok:
                    self._send_json({"ok": False, "error": msg, "tokens": tokens}, 500)
                    return
                _op_log("api-token-delete", "id=" + token_id[:16], actor="-", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "deleted": True, "tokens": tokens}, 200)
            elif path == "/api/v1/auth/sso-links/create":
                body = self._read_json_body()
                ip = _client_ip_from_handler(self)
                payload, code = _build_sso_link_payload(body, require_reauth=False, headers=self.headers, client_ip=ip)
                if payload.get("ok"):
                    host = str(self.headers.get("Host") or "").strip()
                    scheme = "https" if str(self.headers.get("X-Forwarded-Proto") or "").lower() == "https" else "http"
                    path_url = str(payload.get("path") or "")
                    payload["url"] = (f"{scheme}://{host}{path_url}" if host and path_url else path_url)
                    _op_log("api-sso-create", "next=" + str(payload.get("next") or "/"), ip=ip, ok=True)
                self._send_json(payload, code)
            elif path == "/api/settings/login-link/create":
                body = self._read_json_body()
                ip = _client_ip_from_handler(self)
                subject = str(body.get("username") or "-") if body else "-"
                limited, retry_after = _rate_limited("login-link-create", ip, subject, limit=5, window_sec=300, block_sec=900)
                if limited:
                    self._rate_limit_fail(retry_after)
                    return
                payload, code = _build_sso_link_payload(body, require_reauth=True, headers=self.headers, client_ip=ip)
                if payload.get("ok"):
                    _rate_note("login-link-create", ip, subject, success=True, limit=5, window_sec=300, block_sec=900)
                    host = str(self.headers.get("Host") or "").strip()
                    scheme = "https" if str(self.headers.get("X-Forwarded-Proto") or "").lower() == "https" else "http"
                    path_url = str(payload.get("path") or "")
                    payload["url"] = (f"{scheme}://{host}{path_url}" if host and path_url else path_url)
                    _op_log("login-link-create", "sso next=" + str(payload.get("next") or "/"), actor=subject, ip=ip, ok=True)
                elif code == 401:
                    _rate_note("login-link-create", ip, subject, success=False, limit=5, window_sec=300, block_sec=900)
                self._send_json(payload, code)
            elif path == "/api/settings/login-link/delete":
                body = self._read_json_body()
                check = str(body.get("check") or "").strip()
                if not check:
                    self._send_json({"ok": False, "error": "check required"}, 400)
                    return
                def _remove_link(links):
                    return [x for x in links if str((x or {}).get("check") or "") != check]
                ok, msg, links = _auth_mutate_sso_links(_remove_link, tag="sso_delete")
                if not ok:
                    self._send_json({"ok": False, "error": msg, "links": links}, 500)
                    return
                _op_log("login-link-delete", "check=" + check[:12], actor="-", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "deleted": True, "links": links}, 200)
            elif path == "/api/web/base/save":
                body = self._read_json_body()
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                base_name = str(body.get("base_name") or "基站").strip() or "基站"
                lat_raw = body.get("base_lat")
                lon_raw = body.get("base_lon")
                zoom_raw = body.get("base_zoom")
                heading_ref_raw = body.get("heading_ref_deg")
                map_idle_raw = body.get("map_auto_center_idle_sec")
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
                base_zoom = max(3, min(30, base_zoom))
                try:
                    heading_ref_deg = float(heading_ref_raw if heading_ref_raw not in (None, "") else 0.0)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid heading_ref_deg"}, 400)
                    return
                heading_ref_deg = heading_ref_deg % 360.0
                if heading_ref_deg < 0:
                    heading_ref_deg += 360.0
                try:
                    map_auto_center_idle_sec = int(map_idle_raw if map_idle_raw not in (None, "") else 20)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid map_auto_center_idle_sec"}, 400)
                    return
                map_auto_center_idle_sec = max(5, min(600, map_auto_center_idle_sec))
                try:
                    cfg = load_app_config(APP_CONFIG_PATH)
                    web_cfg = cfg.get("web")
                    if not isinstance(web_cfg, dict):
                        web_cfg = {}
                    web_cfg["base_name"] = base_name
                    web_cfg["base_lat"] = base_lat
                    web_cfg["base_lon"] = base_lon
                    web_cfg["base_zoom"] = base_zoom
                    web_cfg["heading_ref_deg"] = round(float(heading_ref_deg), 2)
                    web_cfg["map_auto_center_idle_sec"] = int(map_auto_center_idle_sec)
                    cfg["web"] = web_cfg
                    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="web-base")
                    if not b_ok:
                        self._send_json({"ok": False, "error": f"backup failed: {backup_path}"}, 500)
                        return
                    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
                    if not ok:
                        self._send_json({"ok": False, "error": f"save failed: {msg}"}, 500)
                        return
                    cfg_loaded = load_app_config(APP_CONFIG_PATH)
                    r_ok, r_msg = reload_runtime_config(cfg_loaded)
                    if not r_ok:
                        restore_config_backup(APP_CONFIG_PATH, backup_path)
                        self._send_json({"ok": False, "error": f"reload failed: {r_msg}", "backup_path": backup_path}, 500)
                        return
                    self._send_json({
                        "ok": True,
                        "saved_to": APP_CONFIG_PATH,
                        "backup_path": backup_path,
                        "reloaded": bool(r_ok),
                        "reload_msg": r_msg,
                        "base_name": str(WEB_CFG.get("base_name") or base_name),
                        "base_lat": WEB_CFG.get("base_lat"),
                        "base_lon": WEB_CFG.get("base_lon"),
                        "base_zoom": WEB_CFG.get("base_zoom"),
                        "heading_ref_deg": WEB_CFG.get("heading_ref_deg"),
                        "map_auto_center_idle_sec": WEB_CFG.get("map_auto_center_idle_sec"),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/web/basic/save":
                body = self._read_json_body()
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                iface_raw = body.get("iface")
                iface = None if iface_raw in (None, "") else str(iface_raw).strip()
                if not iface:
                    self._send_json({"ok": False, "error": "必须选择默认网卡"}, 400)
                    return
                safe_iface = _hw_safe_iface(iface)
                if not safe_iface:
                    self._send_json({"ok": False, "error": "invalid iface"}, 400)
                    return
                iface = safe_iface
                scan_wifi_fast = _to_bool(body.get("scan_wifi_fast"), False)
                try:
                    cfg = load_app_config(APP_CONFIG_PATH)
                    basic_cfg = cfg.get("basic")
                    if not isinstance(basic_cfg, dict):
                        basic_cfg = {}
                    basic_cfg["iface"] = iface
                    basic_cfg["scan_wifi_fast"] = bool(scan_wifi_fast)
                    cfg["basic"] = basic_cfg
                    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="web-basic")
                    if not b_ok:
                        self._send_json({"ok": False, "error": f"backup failed: {backup_path}"}, 500)
                        return
                    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
                    if not ok:
                        self._send_json({"ok": False, "error": f"save failed: {msg}"}, 500)
                        return
                    cfg_loaded = load_app_config(APP_CONFIG_PATH)
                    r_ok, r_msg = reload_runtime_config(cfg_loaded)
                    if not r_ok:
                        restore_config_backup(APP_CONFIG_PATH, backup_path)
                        self._send_json({"ok": False, "error": f"reload failed: {r_msg}", "backup_path": backup_path}, 500)
                        return
                    basic_now = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
                    if not isinstance(basic_now, dict):
                        basic_now = {}
                    self._send_json({
                        "ok": True,
                        "saved_to": APP_CONFIG_PATH,
                        "backup_path": backup_path,
                        "reloaded": bool(r_ok),
                        "reload_msg": r_msg,
                        "iface_selected": (None if basic_now.get("iface") in (None, "") else str(basic_now.get("iface"))),
                        "scan_wifi_fast": bool(basic_now.get("scan_wifi_fast")),
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
    if not _auth_enabled():
        _log("[WARN] Web auth disabled: Web UI is exposed to LAN; enable auth in config for safety")
    if not _api_token_enabled():
        _log("[INFO] API public mode disabled: /api/docs, /api/health and /api/v1/* stay page-session-only")
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

        # ODID 载荷提取。旧 ODID 和新版 DJI Beacon payload 保持两套解析路径。
        payloads = extract_from_ies(pkt)
        ssid_rid = _ssid_to_sn(ssid or "")
        new_fw_payloads = extract_new_firmware_from_ies(pkt, ssid_rid) if d11.subtype == 8 else []
        if d11.subtype in (13, 5, 8):   # Extra: also scan raw payload for all mgmt subtypes
            raw_p = extract_from_raw(pkt)
            # 去重
            sigs = {zlib.crc32(p)&0xFFFFFFFF for p in payloads}
            for p in raw_p:
                if (zlib.crc32(p)&0xFFFFFFFF) not in sigs:
                    payloads.append(p)
            if d11.subtype == 8:
                new_raw = extract_new_firmware_from_raw(pkt, ssid_rid)
                new_sigs = {_new_fw_payload_sig(p[0]) for p in new_fw_payloads}
                for p in new_raw:
                    sig = _new_fw_payload_sig(p[0])
                    if sig not in new_sigs:
                        new_sigs.add(sig)
                        new_fw_payloads.append(p)
        if new_fw_payloads and payloads:
            # New-firmware bodies can contain legacy-looking ODID fragments;
            # drop the overlapping legacy payloads so one beacon is not counted
            # twice by the old/new parser paths.
            new_bodies = [bytes(body or b"") for body, _decoded in new_fw_payloads]
            payloads = [
                p for p in payloads
                if not any(p and (bytes(p) == body or body.startswith(bytes(p)) or bytes(p) in body) for body in new_bodies)
            ]

        # Debug scan logs
        if DEBUG_MODE:
            rssi_s  = f"{rssi}dBm" if rssi is not None else "N/A"
            ch_s    = f"{'~' if ch_assumed else ''}ch{ch}" if ch else "ch?"
            ssid_s  = f" SSID={ssid!r}" if ssid else ""
            odid_s  = ""
            if payloads:
                types = [f"{((p[0]>>4)&0xF):X}" for p in payloads if p]
                odid_s = f" ODID={len(payloads)}[{','.join(types)}]"
            if new_fw_payloads:
                odid_s += f" NEWFW={len(new_fw_payloads)}"
            _scan(f"[FRAME] {subtype_name} src={src_mac} {rssi_s} {ch_s}{ssid_s}{odid_s}")

        is_wifi_fast = bool(SCAN_WIFI_FAST) and _is_wifi_fast_mac(src_mac)
        frame_hex = ""
        try:
            frame_hex = _hex_preview(bytes(pkt), max_bytes=220)
        except Exception:
            frame_hex = ""

        if not payloads and not new_fw_payloads:
            # Even without ODID payload, if SSID contains RID SN, still refresh last_seen_ts.
            if is_wifi_fast:
                state_update(src_mac, {"basic_id": {"uas_id": _wifi_fast_sn(src_mac), "id_type": "SSID"}, "location": None, "system": None},
                             rssi=rssi, ch=ch, ch_assumed=ch_assumed, pl_sig=0,
                             scan_type="phone", ssid=(ssid or ""), capture_type=subtype_name,
                             raw_pkt_hex=frame_hex, firmware_type="old")
            elif ssid and src_mac in mac_to_ssid_sn:
                state_update(src_mac, {"basic_id": None, "location": None, "system": None},
                             rssi=rssi, ch=ch, ch_assumed=ch_assumed, pl_sig=0,
                             scan_type="rid", ssid=ssid, capture_type=subtype_name,
                             raw_pkt_hex=frame_hex, firmware_type="old")
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
                             raw_pkt_hex=_hex_preview(piece if piece else payload, max_bytes=160),
                             firmware_type="old")
                if DEBUG_MODE:
                    b = decoded.get("basic_id")
                    l = decoded.get("location")
                    s = decoded.get("system")
                    if b: _scan(f"  -> BasicID: {b}")
                    if l: _scan(f"  -> Location: lat={l.get('lat'):.5f} lon={l.get('lon'):.5f} "
                                f"alt={l.get('alt_geodetic'):.1f}m spd={l.get('speed_ms')}")
                    if s: _scan(f"  -> System(pilot): lat={s.get('pilot_lat')} lon={s.get('pilot_lon')} type={s.get('pilot_loc_type_text')}")
        for body, decoded in new_fw_payloads:
            if not body or not decoded:
                continue
            sig = _new_fw_payload_sig(body)
            state_update(src_mac, decoded, rssi=rssi, ch=ch,
                         ch_assumed=ch_assumed, pl_sig=sig,
                         scan_type="rid", ssid=ssid, capture_type=subtype_name,
                         raw_pkt_hex=_hex_preview(body, max_bytes=160),
                         firmware_type="new")
            if DEBUG_MODE:
                b = decoded.get("basic_id")
                l = decoded.get("location")
                if b: _scan(f"  -> NewFW BasicID: {b}")
                if l: _scan(f"  -> NewFW Location: lat={l.get('lat'):.5f} lon={l.get('lon'):.5f} "
                            f"alt={l.get('alt_geodetic')}m dir={l.get('direction_deg')}")
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
    parser.add_argument("--no-tui",   action="store_true", default=True, help="禁用 TUI，纯文本输出")
    parser.add_argument("--tui",      action="store_false", dest="no_tui", help="启用 TUI")
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
    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="restart")
    if not b_ok:
        return False, f"backup failed: {backup_path}"
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
    parser.add_argument("--no-tui",   action="store_true", default=True, help="禁用 TUI，纯文本输出")
    parser.add_argument("--tui",      action="store_false", dest="no_tui", help="启用 TUI")
    parser.add_argument("--debug",    action="store_true", help="write all raw frames into scan log")
    parser.add_argument("--notify-test", action="store_true", help="send one WeCom test notification then exit")
    APP_START_CWD = os.getcwd()
    args = parser.parse_args()

    cfg_path = os.path.abspath(str(args.config)) if args.config else None
    APP_CONFIG_PATH = cfg_path
    APP_CONFIG_PATH_IS_DEFAULT = (cfg_path == os.path.abspath(os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT))) if cfg_path else True
    APP_CONFIG = load_app_config(cfg_path)
    if not _eula_accepted():
        _log(f"[INFO] EULA pending: open /eula to accept ({_eula_set_path()})")
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
    init_model_update_from_config(APP_CONFIG)
    init_config_update_from_config(APP_CONFIG)
    init_app_update_from_config(APP_CONFIG)
    init_metrics_from_config(APP_CONFIG)
    init_auth_from_config(APP_CONFIG)
    init_api_from_config(APP_CONFIG)
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

    if hasattr(os, "geteuid") and os.geteuid() != 0:
        if _process_has_capabilities(list(RUNTIME_SERVICE_CAPABILITIES)):
            _log("[INFO] running without root; required network capabilities are present")
        else:
            _log("[WARN] 当前不是 root，且未检测到采集所需网络能力；请在设置页执行一键修复")

    check_iw_available_on_startup()

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
    WIFI_FAST_SUPPORTED = False
    WIFI_FAST_SUPPORT_MSG = ""
    if iface:
        try:
            WIFI_FAST_SUPPORTED = bool(detect_5g(iface))
        except Exception:
            WIFI_FAST_SUPPORTED = False
        if SCAN_WIFI_FAST and WIFI_FAST_SUPPORTED:
            WIFI_FAST_SUPPORT_MSG = f"iface {iface} supports 5GHz; WiFi fast-transfer scan enabled"
        if SCAN_WIFI_FAST and not WIFI_FAST_SUPPORTED:
            WIFI_FAST_SUPPORT_MSG = f"iface {iface} does not support 5GHz; WiFi fast-transfer scan unavailable"
            _log(f"[WARN] {WIFI_FAST_SUPPORT_MSG}")
    else:
        WIFI_FAST_SUPPORT_MSG = NO_IFACE_DEGRADE_HINT
        _log(f"[WARN] {NO_IFACE_DEGRADE_HINT}")

    if args.hop and args.channel:
        _log("[WARN] --hop and --channel both set; using hopping mode")

    hop_cfg: tuple[list[int], list[int], int, int] | None = None
    if args.hop:
        dw2 = max(100, args.dwell_2g)
        dw5 = max(200, args.dwell_5g)
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
        hop_cfg = (hop_2g, hop_5g, dw2, dw5)
        _log(f"[INFO] hopping 2.4G={hop_2g}@{dw2}ms" + (f" 5G={hop_5g}@{dw5}ms" if hop_5g else ""))
        if iface:
            Thread(target=channel_hopper,
                   args=(iface, hop_2g, hop_5g, dw2, dw5,
                         max(0, args.settle), args.dwell_on_hit, args.hit_cap),
                   daemon=True).start()
        else:
            _log("[WARN] 当前无网卡，已进入降级运行；跳频将在网卡恢复后自动启用")
    elif args.channel:
        _log(f"[INFO] lock channel {args.channel}")
        if iface:
            run_cmd(f"iw dev {iface} set channel {args.channel}")
        else:
            _log("[WARN] 当前无网卡，先记录信道配置，网卡恢复后自动应用")
        current_channel = args.channel
    else:
        # Default lock to ch6 (DJI RID commonly used channel).
        _log("[INFO] default lock channel 6 (DJI RID common). Use --hop or --channel N to change")
        if iface:
            run_cmd(f"iw dev {iface} set channel 6")
        else:
            _log("[WARN] 当前无网卡，先使用默认信道配置，网卡恢复后自动应用")
        current_channel = 6

    _log(f"[INFO] output: first/changed(min-gap={MIN_GAP:.1f}s)/heartbeat(time={PRINT_INTERVAL:.1f}s)")
    _log(f"[INFO] LOST timeout={LOST_TIMEOUT:.0f}s  PURGE={PURGE_TIMEOUT:.0f}s")
    if DEBUG_MODE:
        _log("[INFO] DEBUG mode: all raw frames are written into scan log (press d)")

    Thread(target=lost_checker, daemon=True).start()
    Thread(target=http_server_thread, daemon=True).start()
    Thread(target=history_persist_loop, daemon=True).start()
    Thread(target=host_metrics_loop, daemon=True).start()
    start_hw_worker()
    start_notify_worker()
    start_model_update_worker()
    start_config_update_worker()
    start_app_update_check()

    def sniff_thread():
        global sniff_iface_name
        retry_delay = 2.0
        fail_count = 0
        recover_fail_count = 0
        iface_cur = str(iface or "")
        iface_watch_since = time.monotonic() if iface_cur else 0.0
        hop_started = bool(args.hop and bool(iface))

        def note_recover_failure(reason: str, allow_restart: bool = True) -> None:
            nonlocal recover_fail_count
            if (not allow_restart) or (not _cfg_auto_self_heal()):
                recover_fail_count = 0
                return
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

        def set_iface_watch(iface_name: str) -> None:
            nonlocal iface_watch_since
            iface_watch_since = time.monotonic() if iface_name else 0.0

        while True:
            prefer_iface = _cfg_preferred_iface()
            if not iface_cur:
                iface_cur = _sniff_pick_iface(prefer=prefer_iface)
                if iface_cur:
                    set_iface_watch(iface_cur)
                    with sniff_health_lock:
                        sniff_iface_name = iface_cur
                    _log(f"[INFO] sniff iface recovered: {iface_cur}")
                    ok = _sniff_recover_iface(iface_cur, "iface connected", force=True)
                    if not ok:
                        _log(f"[WARN] sniff iface init failed: {iface_cur}, waiting retry")
                        iface_cur = ""
                        time.sleep(retry_delay)
                        continue
                    if args.hop and (not hop_started) and hop_cfg:
                        hop_2g, hop_5g, dw2, dw5 = hop_cfg
                        Thread(target=channel_hopper,
                               args=(iface_cur, hop_2g, hop_5g, dw2, dw5,
                                     max(0, args.settle), args.dwell_on_hit, args.hit_cap),
                               daemon=True).start()
                        hop_started = True
                    elif (not args.hop):
                        if current_channel:
                            run_cmd(f"iw dev {iface_cur} set channel {current_channel}")
                else:
                    _sniff_note_error(NO_IFACE_DEGRADE_HINT)
                    # Missing/unconfigured NIC should surface as a stable degraded state,
                    # not a self-restart loop.
                    note_recover_failure("no iface available", allow_restart=False)
                    _log(f"[WARN] sniff no available iface, retry in {retry_delay:.0f}s")
                    time.sleep(retry_delay)
                    continue

            try:
                with sniff_health_lock:
                    sniff_iface_name = iface_cur
                state, detail = _sniff_run_once(iface_cur, timeout_sec=SNIFF_POLL_TIMEOUT)
                if state == "hung":
                    _sniff_note_error(f"sniff worker hung: {detail}")
                    _log(f"[WARN] sniff worker hung on {iface_cur}: {detail}")
                    recovered = _sniff_recover_iface(iface_cur, f"worker hung: {detail}", force=True)
                    if not recovered:
                        new_iface = _sniff_pick_iface(prefer=(prefer_iface or iface_cur))
                        if new_iface and new_iface != iface_cur:
                            _log(f"[WARN] sniff iface switch after hang: {iface_cur} -> {new_iface}")
                            iface_cur = new_iface
                            set_iface_watch(iface_cur)
                            with sniff_health_lock:
                                sniff_iface_name = iface_cur
                            recovered = _sniff_recover_iface(iface_cur, "switch iface after hang", force=True)
                    if recovered:
                        set_iface_watch(iface_cur)
                        note_recover_success()
                    else:
                        note_recover_failure(f"worker hung on {iface_cur}", allow_restart=True)
                    time.sleep(retry_delay)
                    continue
                if state != "ok":
                    raise RuntimeError(detail or "sniff worker failed")
                fail_count = 0
                now_mono = time.monotonic()
                idle = _sniff_idle_sec(now_mono)
                no_pkt_elapsed = None
                if idle is None and iface_watch_since > 0.0:
                    no_pkt_elapsed = max(0.0, now_mono - iface_watch_since)
                stall_reason = None
                if idle is not None and idle >= SNIFF_STALL_RECOVER_SEC:
                    stall_reason = f"idle {idle:.0f}s without management frame"
                elif no_pkt_elapsed is not None and no_pkt_elapsed >= SNIFF_STALL_RECOVER_SEC:
                    stall_reason = f"no management frame for {no_pkt_elapsed:.0f}s after sniff start"
                if stall_reason:
                    recovered = _sniff_recover_iface(iface_cur, stall_reason, force=True)
                    if not recovered:
                        new_iface = _sniff_pick_iface(prefer=(prefer_iface or iface_cur))
                        if new_iface and new_iface != iface_cur:
                            _log(f"[WARN] sniff iface switch: {iface_cur} -> {new_iface}")
                            iface_cur = new_iface
                            set_iface_watch(iface_cur)
                            with sniff_health_lock:
                                sniff_iface_name = iface_cur
                            recovered = _sniff_recover_iface(iface_cur, "switch iface recovery", force=True)
                    if recovered:
                        set_iface_watch(iface_cur)
                        note_recover_success()
                    else:
                        note_recover_failure(stall_reason, allow_restart=True)
                else:
                    note_recover_success()
                time.sleep(0.05)
            except Exception as ex:
                fail_count += 1
                ex_msg = str(ex or "")
                _sniff_note_error(f"sniff exception#{fail_count}: {ex_msg}")
                no_dev_err = _sniff_is_no_device_error(ex)
                note_recover_failure(ex_msg, allow_restart=True)
                if _cfg_auto_self_heal() and (not no_dev_err) and fail_count >= SNIFF_RESTART_AFTER_FAILS:
                    _log(f"[WARN] sniff exception count reached {SNIFF_RESTART_AFTER_FAILS}, scheduling self-restart")
                    ok, msg = _schedule_self_restart(list(sys.argv[1:]))
                    if not ok:
                        _log(f"[WARN] self-restart scheduling failed: {msg}")
                    fail_count = 0

                if no_dev_err:
                    fail_count = 0
                    new_iface = _sniff_pick_iface(prefer=(prefer_iface or iface_cur))
                    if new_iface and new_iface != iface_cur:
                        _log(f"[WARN] sniff iface unavailable, switch {iface_cur} -> {new_iface}")
                        iface_cur = new_iface
                        set_iface_watch(iface_cur)
                        with sniff_health_lock:
                            sniff_iface_name = iface_cur
                        _sniff_recover_iface(iface_cur, f"after iface switch: {ex_msg}", force=True)
                    elif new_iface:
                        _log(f"[WARN] sniff iface exception#{fail_count}: {ex_msg}, try reset {iface_cur}")
                        if _sniff_recover_iface(iface_cur, f"exception#{fail_count}: {ex_msg}", force=True):
                            set_iface_watch(iface_cur)
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
