from __future__ import annotations
# pylint: disable=unused-import
# This file is the first legacy runtime chunk. Several imports below seed the
# shared exec() namespace for later chunks until they become normal modules.
import argparse
import base64
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
    import curses
except ImportError:
    curses = None

try:
    from scapy.config import conf
    from scapy.layers.dot11 import Dot11, Dot11Beacon, Dot11Elt, RadioTap
    from scapy.sendrecv import sniff
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
RID_NEW_FW_BODY_MIN  = 83
RID_DJI_VENDOR_MIN   = 10
RID_DJI_GB46750_MIN  = 83
RID_DJI_ENTERPRISE_PRIVATE_MIN = 68
RID_NEW_FW_SN_LEN    = 20
RID_NEW_FW_UAS_LEN   = 8
RID_NEW_FW_GB_OFF    = 5
RID_NEW_FW_GB_MIN    = 78
RID_NEW_FW_ALL_IDENTIFIERS = b"\xff\xff\xfe"
RID_DJI_GB46750_HEADER = b"\xff\x20\x48\xff\xff\xfe"
RID_DJI_ENTERPRISE_PRIVATE_HEADER = b"\xf1\x19\x03\x01\x12"
RID_NEW_FW_SN_OFF    = 11
RID_NEW_FW_UAS_OFF   = 31
RID_NEW_FW_PILOT_LON_OFF = 42
RID_NEW_FW_PILOT_LAT_OFF = 46
RID_NEW_FW_PILOT_ALT_OFF = 50
RID_NEW_FW_DRONE_LON_OFF = 52
RID_NEW_FW_DRONE_LAT_OFF = 56
RID_NEW_FW_TRACK_OFF = 60
RID_NEW_FW_GROUND_SPEED_OFF = 62
RID_NEW_FW_REL_ALT_OFF = 64
RID_NEW_FW_VSPEED_OFF = 66
RID_NEW_FW_GEOID_ALT_OFF = 67
RID_NEW_FW_BARO_ALT_OFF = 69
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
DEFAULT_LOST_TIMEOUT   = 15.0
LOST_TIMEOUT           = DEFAULT_LOST_TIMEOUT
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
CONFIG_FILE_DEFAULT = "config.json"
HISTORY_STORE_DEFAULT = "history-cache.json"
HISTORY_RAW_PACKET_LIMIT = 100
HISTORY_RAW_PACKET_SNAPSHOT_LIMIT = 3
MODEL_MAP_FILE_DEFAULT = "rid-models.json"
MODEL_MAP_LEGACY_FILE = "rid_models.json"
SYSTEMD_SERVICE_NAME = "light-rid-scanner.service"
SYSTEMD_SERVICE_PATH = "/etc/systemd/system/" + SYSTEMD_SERVICE_NAME
IW_PACKAGE_NAME = "iw"
RUNTIME_SERVICE_USER = "rid"
RUNTIME_SERVICE_HOME = "/var/lib/light-rid"
RUNTIME_SERVICE_CAPABILITIES = ("CAP_NET_ADMIN", "CAP_NET_RAW", "CAP_NET_BIND_SERVICE")
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
RID_MODELS_UPDATE_URL_DEFAULT = "https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/rid-models.json"
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
TRACK_ANOMALY_MAX_METERS = 50_000.0
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
APP_CONFIG_PATH_LOCKED: bool = False
APP_EDITION: str = os.environ.get("LIGHT_RID_EDITION", "station").strip().lower() or "station"
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
    "username_hash": "",
    "password_hash": "",
    "realm": "Light RID Scanner",
    "session_ttl_min": 30,
    "login_methods": ["password", "passkey"],
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
    "token_hash": "",
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
    "enabled": False,
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

def _runtime_entrypoint_path() -> str:
    ctx = globals().get("RUNTIME_CONTEXT")
    entrypoint = getattr(ctx, "entrypoint", None)
    if entrypoint:
        return str(entrypoint)
    return str(__file__)

def _app_root_dir() -> str:
    cfg_path = globals().get("APP_CONFIG_PATH")
    if cfg_path:
        try:
            return os.path.abspath(os.path.dirname(str(cfg_path)) or os.getcwd())
        except Exception:
            pass
    return os.path.dirname(os.path.abspath(_runtime_entrypoint_path()))

def _app_file_path(name: str) -> str:
    return os.path.join(_app_root_dir(), str(name or ""))

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

def _track_for_query(raw, query: dict | None = None, firmware_type: str | None = None) -> list[dict]:
    # Always normalize stored points before applying request-level trimming.
    track = _track_points_for_display(_sanitize_track(raw or []), firmware_type=firmware_type)
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
            "kind": e.get("kind"),
            "rid_format": e.get("rid_format"),
            "dji_rid_kind": e.get("dji_rid_kind"),
            "parse_note": e.get("parse_note"),
            "raw_vendor": e.get("raw_vendor"),
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
            "gb_data_type": e.get("gb_data_type"),
            "gb_version_raw": e.get("gb_version_raw"),
            "gb_data_len": e.get("gb_data_len"),
            "dji_dynamic": e.get("dji_dynamic"),
            "reg_mark": e.get("reg_mark"),
            "status": e.get("status"),
            "coord_type": e.get("coord_type"),
            "coord_sys": e.get("coord_sys"),
            "coord_sys_text": e.get("coord_sys_text"),
            "home_lat": e.get("home_lat"),
            "home_lon": e.get("home_lon"),
            "aux_lat": e.get("aux_lat"),
            "aux_lon": e.get("aux_lon"),
            "pos_a_lat": e.get("pos_a_lat"),
            "pos_a_lon": e.get("pos_a_lon"),
            "pos_b_lat": e.get("pos_b_lat"),
            "pos_b_lon": e.get("pos_b_lon"),
            "alt_candidates": e.get("alt_candidates"),
            "enterprise_model": e.get("enterprise_model"),
            "enterprise_dynamic": e.get("enterprise_dynamic"),
            "enterprise_signature": e.get("enterprise_signature"),
            "capture_type": e.get("capture_type"),
            "firmware_type": _firmware_type_key(e.get("firmware_type")),
            "last_capture_wall_ts": e.get("last_capture_wall_ts"),
            "raw_packets": list(e.get("raw_packets") or [])[-HISTORY_RAW_PACKET_LIMIT:],
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
        repaired_enterprise = 0
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
                enterprise_refresh = globals().get("_refresh_enterprise_private_record")
                if callable(enterprise_refresh):
                    try:
                        if enterprise_refresh(h, h.get("model")):
                            repaired_enterprise += 1
                    except Exception:
                        pass
                h["raw_packets"] = list(h.get("raw_packets") or [])[-HISTORY_RAW_PACKET_LIMIT:]
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
        if repaired_model or repaired_enterprise or compat_dirty:
            _history_mark_dirty()
        if compat_dirty:
            _log("[INFO] history cache upgraded for firmware/UAS fields")
        if repaired_model:
            _log(f"[INFO] history model repaired from SN map: {repaired_model}")
        if repaired_enterprise:
            _log(f"[INFO] history enterprise RID coordinates repaired: {repaired_enterprise}")
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
    "kind","rid_format","dji_rid_kind","parse_note","raw_vendor",
    "gb_version","gb_identifiers",
    "gb_data_type","gb_version_raw","gb_data_len","dji_dynamic",
    "reg_mark","status","coord_type",
    "operation_category","operation_category_text",
    "aircraft_category","aircraft_category_text",
    "pilot_alt","track_deg","ground_speed","vertical_speed",
    "alt_relative","alt_geoid","alt_baro",
    "operation_state","operation_state_text",
    "coord_sys","coord_sys_text",
    "horizontal_accuracy","vertical_accuracy","speed_accuracy",
    "timestamp_ms","timestamp_accuracy","timestamp_accuracy_text",
    "home_lat","home_lon","aux_lat","aux_lon",
    "pos_a_lat","pos_a_lon","pos_b_lat","pos_b_lon",
    "alt_candidates","enterprise_model","enterprise_dynamic","enterprise_signature",
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
            h[k] = list(raw.get(k) or [])[-HISTORY_RAW_PACKET_LIMIT:]
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

def _settings_export_payload() -> dict:
    cfg = load_app_config(APP_CONFIG_PATH) if APP_CONFIG_PATH else default_app_config()
    return {
        "ok": True,
        "kind": "settings",
        "version": 1,
        "exported_at": time.time(),
        "config_path": APP_CONFIG_PATH or "",
        "settings": cfg,
    }

def _settings_import_candidate(payload) -> tuple[dict | None, str | None]:
    src = payload
    if isinstance(src, dict):
        if isinstance(src.get("settings"), dict):
            src = src.get("settings")
        elif isinstance(src.get("config"), dict):
            src = src.get("config")
        elif isinstance(src.get("payload"), dict):
            src = src.get("payload")
    if not isinstance(src, dict):
        return None, "payload must be object"
    if not any(k in src for k in ("basic", "notify", "web", "ap", "auth", "api", "model_update", "config_update", "app_update", "metrics")):
        return None, "invalid settings payload"
    candidate = _deep_merge_dict(default_app_config(), src)
    candidate, guard_err = _prepare_security_cfg_for_save(candidate)
    if guard_err:
        return None, guard_err
    return candidate, None

def _import_settings_payload(payload) -> dict:
    if not APP_CONFIG_PATH:
        return {"ok": False, "error": "config path missing"}
    prev_cfg = load_app_config(APP_CONFIG_PATH)
    candidate_cfg, err = _settings_import_candidate(payload)
    if err or not isinstance(candidate_cfg, dict):
        return {"ok": False, "error": str(err or "invalid settings payload")}
    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="settings_import")
    if not b_ok:
        return {"ok": False, "error": f"backup failed: {backup_path}"}
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
        "reload_msg": r_msg,
        "settings": _settings_view_payload().get("visual"),
    }

def _scan_data_payload_unwrap(payload):
    src = payload
    if isinstance(src, dict):
        if isinstance(src.get("scan_data"), dict):
            src = src.get("scan_data")
        elif isinstance(src.get("payload"), (dict, list)):
            src = src.get("payload")
    return src

def _scan_data_payload_valid(payload) -> bool:
    src = _scan_data_payload_unwrap(payload)
    if isinstance(src, list):
        return True
    if isinstance(src, dict):
        return isinstance(src.get("items"), list) or isinstance(src.get("drones"), list)
    return False

def _scan_data_file_info(path: str | None = None) -> dict:
    raw_path = str(path or HISTORY_STORE_PATH or "").strip()
    info = {"path": raw_path, "exists": False, "size": 0, "mtime": None}
    if not raw_path:
        return info
    try:
        abs_path = os.path.abspath(raw_path)
        info["path"] = abs_path
        st = os.stat(abs_path)
        info.update({"exists": True, "size": int(st.st_size), "mtime": float(st.st_mtime)})
    except FileNotFoundError:
        info["path"] = os.path.abspath(raw_path)
    except Exception as exc:
        info["error"] = str(exc)
    return info

def _scan_data_export_payload() -> dict:
    with state_lock:
        items = _history_disk_items_locked()
    file_info = _scan_data_file_info()
    return {
        "ok": True,
        "kind": "scan_data",
        "version": 1,
        "store_version": 3,
        "exported_at": time.time(),
        "data_file": file_info.get("path") or HISTORY_STORE_PATH or "",
        "data_file_info": file_info,
        "count": len(items),
        "items": items,
    }

def _import_scan_data_payload(payload, *, mode: str = "merge") -> dict:
    src = _scan_data_payload_unwrap(payload)
    if not _scan_data_payload_valid(src):
        return {"ok": False, "error": "invalid payload: expect items[]/drones[] or list"}
    import_mode = "replace" if str(mode or "").strip().lower() in ("replace", "overwrite", "reset") else "merge"
    replaced = 0
    if import_mode == "replace":
        replaced, _removed = clear_history_store(delete_file=False)
    added, updated, skipped = import_details_payload(src)
    save_history_store(force=True)
    with state_lock:
        total_count = len(history_table)
    return {
        "ok": True,
        "mode": import_mode,
        "replaced": int(replaced),
        "added": int(added),
        "updated": int(updated),
        "skipped": int(skipped),
        "count": int(total_count),
        "data_file": HISTORY_STORE_PATH or "",
        "data_file_info": _scan_data_file_info(),
    }

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
            "lost_timeout": DEFAULT_LOST_TIMEOUT,
            "rssi_delta": 3,
            "change_on_rssi": False,
            "change_on_payload": False,
            "model_map": os.path.join(os.getcwd(), MODEL_MAP_FILE_DEFAULT),
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
            "enabled": False,
            "retention_days": HOST_METRICS_RETENTION_DAYS_DEFAULT,
            "temperature_source": "auto",
        },
        "auth": {
            "enabled": False,
            "username_hash": "",
            "password_hash": "",
            "realm": "Light RID Scanner",
            "session_ttl_min": 30,
            "login_methods": ["password", "passkey"],
            "sso_links": [],
            "passkeys": [],
        },
        "api": {
            "enabled": False,
            "token": "",
            "token_hash": "",
            "tokens": [],
            "whitelist_enabled": False,
            "whitelist_mode": "allow",
            "whitelist": [],
        },
        "network_bindings": {
            "items": [],
            "ap": {
                "ssid": "LightRID-HotSpot",
                "password": "",
                "channel": 6,
                "address": "172.16.0.1",
                "cidr": "172.16.0.1/24",
                "dhcp_start": "172.16.0.20",
                "dhcp_end": "172.16.0.240",
                "http_port": 80,
                "internet_enabled": False,
                "uplink_iface": "",
            },
        },
    }

def _portable_edition_enabled() -> bool:
    return APP_EDITION in ("portable", "pe", "mobile")

def _runtime_resource_path(*parts: str) -> str:
    ctx = globals().get("RUNTIME_CONTEXT")
    base = getattr(ctx, "package_dir", None)
    if base:
        return os.path.abspath(os.path.join(str(base), "resources", *parts))
    return os.path.abspath(os.path.join(os.getcwd(), "resources", *parts))

def _write_json_file(path: str, payload: dict) -> None:
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    tmp_path = path + ".tmp"
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(payload, f, ensure_ascii=False, indent=2)
        f.write("\n")
    os.replace(tmp_path, path)

def _ensure_runtime_json_files(config_path: str | None, history_path: str | None, *, config_locked: bool) -> None:
    if config_path and (not os.path.exists(config_path)) and (not config_locked):
        _write_json_file(config_path, {})
        _log(f"[INFO] config file created: {config_path}")
    if history_path and not os.path.exists(history_path):
        _write_json_file(history_path, {"version": 3, "items": []})
        _log(f"[INFO] history cache created: {history_path}")

def _apply_portable_defaults(cfg: dict) -> dict:
    if not _portable_edition_enabled():
        return cfg
    out = _deep_merge_dict(default_app_config(), cfg if isinstance(cfg, dict) else {})
    notify = out.setdefault("notify", {})
    notify.update({"enabled": False, "wecom_webhooks": [], "wecom_webhook_key": ""})
    auth = out.setdefault("auth", {})
    auth.update({"enabled": False, "username_hash": "", "password_hash": "", "sso_links": [], "passkeys": []})
    auth["login_methods"] = []
    api = out.setdefault("api", {})
    api.update({"enabled": False, "token": "", "token_hash": "", "tokens": []})
    metrics = out.setdefault("metrics", {})
    metrics["enabled"] = False
    return out

def ensure_config_file(path: str) -> None:
    if not path:
        return
    if os.path.exists(path):
        return
    _set_oobe_required(f"配置文件不存在，已创建默认配置: {path}", True)
    if APP_CONFIG_PATH_LOCKED:
        raise FileNotFoundError(path)
    cfg = {}
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
            basic = {}
        v = basic.get("iface")
        if v not in (None, ""):
            s = str(v).strip()
            if s:
                return s
        nb = cfg.get("network_bindings") if isinstance(cfg, dict) else {}
        items = nb.get("items") if isinstance(nb, dict) else []
        if isinstance(items, list):
            for item in items:
                role = str((item or {}).get("role") or "").strip().lower().replace("-", "_") if isinstance(item, dict) else ""
                if role in ("scan", "scanner", "capture"):
                    s = str(item.get("iface") or "").strip()
                    if s:
                        return s
        return None
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
        cfg = _apply_portable_defaults(_deep_merge_dict(default_app_config(), raw))
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
                cfg = _apply_portable_defaults(_deep_merge_dict(default_app_config(), rb_raw))
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
        if APP_CONFIG_PATH_LOCKED and (not os.path.exists(path)):
            _log(f"[WARN] locked config missing, using in-memory defaults: {path}")
            return _apply_portable_defaults(default_app_config())
        cfg = _apply_portable_defaults(default_app_config())
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
        try:
            backups = []
            prefix = base + "."
            for name in os.listdir(backup_dir):
                p = os.path.join(backup_dir, name)
                if not (os.path.isfile(p) and name.startswith(prefix) and name.endswith(".bak")):
                    continue
                backups.append((os.path.getmtime(p), p))
            backups.sort(reverse=True)
            for _mtime, old_path in backups[5:]:
                try:
                    os.remove(old_path)
                except Exception:
                    pass
        except Exception:
            pass
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
    scan_data_file = _scan_data_file_info(HISTORY_STORE_PATH or str(basic.get("history_file") or ""))
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
                "lost_timeout": basic.get("lost_timeout", basic.get("offline_timeout", DEFAULT_LOST_TIMEOUT)),
                "rssi_delta": basic.get("rssi_delta", 3),
                "change_on_rssi": bool(basic.get("change_on_rssi")),
                "change_on_payload": bool(basic.get("change_on_payload")),
                "debug": bool(basic.get("debug")),
                "model_map": str(basic.get("model_map") or os.path.join(os.getcwd(), MODEL_MAP_FILE_DEFAULT)),
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
                "username_masked": ("已设置" if str(auth_prepared.get("username_hash") or "").strip() else ""),
                "password_masked": ("********" if str(auth_prepared.get("password_hash") or "").strip() else ""),
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
                "enabled": bool(metrics_cfg.get("enabled")),
                "retention_days": int(metrics_cfg.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT),
                "temperature_source": str(metrics_cfg.get("temperature_source") or "auto"),
                "store_path": HOST_METRICS_PATH,
                "sample_interval_sec": int(HOST_METRICS_SAMPLE_SEC),
            },
            "network_bindings": _network_bindings_visual_payload(cfg),
        },
        "host": host,
        "interfaces": interfaces,
        "oobe": _oobe_state(),
        "eula": _eula_status_payload(),
        "raw_access": _raw_config_access_payload(),
        "scan_data_file": scan_data_file,
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
    p_network_bindings = payload.get("network_bindings") if isinstance(payload.get("network_bindings"), dict) else {}

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
        ("lost_timeout", DEFAULT_LOST_TIMEOUT),
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
            auth["username_hash"] = _auth_secret_hash(raw_user)
        elif raw_user.lower() == "__clear__":
            auth["username_hash"] = ""
    if "password" in p_auth:
        raw_pass = str(p_auth.get("password") or "")
        raw_pass_trim = raw_pass.strip()
        if raw_pass_trim not in ("", "__KEEP__", "********"):
            auth["password_hash"] = _auth_secret_hash(raw_pass)
        elif raw_pass_trim.lower() == "__clear__":
            auth["password_hash"] = ""

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
        if "enabled" in p_metrics:
            metrics["enabled"] = bool(p_metrics.get("enabled"))
        if "retention_days" in p_metrics:
            try:
                metrics["retention_days"] = max(1, min(90, int(p_metrics.get("retention_days") or HOST_METRICS_RETENTION_DAYS_DEFAULT)))
            except Exception:
                return None, "invalid metrics.retention_days"
        if "temperature_source" in p_metrics:
            metrics["temperature_source"] = str(p_metrics.get("temperature_source") or "auto")
        cfg["metrics"] = _normalize_metrics_cfg({"metrics": metrics})

    if p_network_bindings:
        cfg, bind_err = _network_bindings_apply_visual(cfg, p_network_bindings)
        if bind_err:
            return None, bind_err

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

    if test_only:
        test_ok, test_msg, notify_msg = _run_visual_settings_test(
            candidate_cfg,
            previous_cfg=prev_cfg,
            notify_test=False,
            keep_runtime=False,
        )
        if not test_ok:
            return {"ok": False, "error": test_msg, "notify_test": notify_msg}
        return {
            "ok": True,
            "tested": True,
            "saved": False,
            "reload_msg": "draft tested and rolled back",
            "notify_test": notify_msg,
            "settings": _settings_view_payload().get("visual"),
        }
    notify_msg = "skip"

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
        "tested": False,
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
        "lost_timeout",
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
    base["enabled"] = bool(base.get("enabled", False))
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
        "vcgencmd_pmic": "vcgencmd_pmic",
        "pmic": "vcgencmd_pmic",
        "thermal": "thermal_zone",
        "thermal_zone": "thermal_zone",
        "thermalzone": "thermal_zone",
        "sysfs": "thermal_zone",
        "hwmon": "hwmon",
        "w1": "w1",
        "ds18b20": "w1",
        "onewire": "w1",
        "one_wire": "w1",
        "off": "off",
        "none": "off",
        "disabled": "off",
    }
    base["temperature_source"] = temp_alias.get(raw_temp_source, "auto")
    return base

def _sha256_hex(text: str) -> str:
    # Only for non-security identifiers/cache keys. Do not use for passwords or auth secrets.
    return hashlib.sha256(str(text or "").encode("utf-8", errors="ignore")).hexdigest().lower()

def _auth_secret_hash(value: str, salt: str | None = None) -> str:
    if not salt:
        salt_bytes = secrets.token_bytes(16)
        salt = base64.urlsafe_b64encode(salt_bytes).decode("ascii").rstrip("=")
    else:
        salt_bytes = base64.urlsafe_b64decode(salt + "=" * (-len(salt) % 4))
    n, r, p = 2 ** 14, 8, 1
    digest = hashlib.scrypt(
        str(value or "").encode("utf-8", errors="ignore"),
        salt=salt_bytes,
        n=n,
        r=r,
        p=p,
        dklen=32,
    )
    hash_text = base64.urlsafe_b64encode(digest).decode("ascii").rstrip("=")
    return f"scrypt${n}${r}${p}${salt}${hash_text}"

def _verify_auth_secret_hash(value: str, stored: str) -> bool:
    try:
        alg, n_text, r_text, p_text, salt, expected = str(stored or "").split("$", 5)
        if alg != "scrypt":
            return False
        n = int(n_text)
        r = int(r_text)
        p = int(p_text)
        if n < 2 ** 14 or r < 8 or p < 1:
            return False
        salt_bytes = base64.urlsafe_b64decode(salt + "=" * (-len(salt) % 4))
        digest = hashlib.scrypt(
            str(value or "").encode("utf-8", errors="ignore"),
            salt=salt_bytes,
            n=n,
            r=r,
            p=p,
            dklen=32,
        )
        actual = base64.urlsafe_b64encode(digest).decode("ascii").rstrip("=")
        return secrets.compare_digest(actual, expected)
    except Exception:
        return False

def _normalize_auth_secret_hash(stored: str | None) -> str:
    raw = str(stored or "").strip()
    try:
        alg, n_text, r_text, p_text, salt, expected = raw.split("$", 5)
        if alg == "scrypt" and int(n_text) >= 2 ** 14 and int(r_text) >= 8 and int(p_text) >= 1 and salt and expected:
            return raw
    except Exception:
        pass
    return ""

def _verify_auth_secret(value: str, stored: str) -> bool:
    normalized = _normalize_auth_secret_hash(stored)
    if not normalized:
        return False
    return _verify_auth_secret_hash(value, normalized)

def _auth_hashes_present(auth_cfg: dict | None = None) -> bool:
    source = auth_cfg if isinstance(auth_cfg, dict) else AUTH_CFG
    return bool(_normalize_auth_secret_hash(source.get("username_hash"))) and bool(_normalize_auth_secret_hash(source.get("password_hash")))

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

def _prune_expired_sso_links(raw, now_wall: float | None = None, grace_sec: float = 5 * 3600) -> list[dict]:
    now_wall = float(now_wall or time.time())
    keep: list[dict] = []
    for item in _normalize_sso_links(raw):
        expires_at = float(item.get("expires_at") or 0.0)
        if expires_at > 0 and now_wall - expires_at > float(grace_sec):
            continue
        keep.append(item)
    return keep

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
    raw = str(token_hash or "").strip()
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
        legacy_digest = _normalize_auth_secret_hash(legacy_hash)
        if legacy_plain or legacy_digest:
            src = [{
                "id": "legacy",
                "name": "默认 Token",
                "token": legacy_plain,
                "token_hash": legacy_digest,
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
        token_hash = _normalize_auth_secret_hash(item.get("token_hash"))
        if token_plain:
            token_hash = _auth_secret_hash(token_plain)
        if not _normalize_auth_secret_hash(token_hash):
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
            "token_hash": token_hash,
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
    return any(str(item.get("token_hash") or "").strip() for item in _normalize_api_tokens(source.get("tokens"), source.get("token") or "", source.get("token_hash") or ""))

def _api_tokens_public(api_cfg: dict | None = None) -> list[dict]:
    source = api_cfg if isinstance(api_cfg, dict) else API_CFG
    out: list[dict] = []
    for item in _normalize_api_tokens(source.get("tokens"), source.get("token") or "", source.get("token_hash") or ""):
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
        default_missing=("password", "passkey"),
        default_empty=("password", "passkey"),
    )

def _auth_login_method_enabled(method: str, auth_cfg: dict | None = None) -> bool:
    return str(method or "").strip().lower() in _auth_login_methods(auth_cfg)

def _prepare_auth_cfg_for_save(auth_cfg: dict | None) -> dict:
    raw = dict(auth_cfg) if isinstance(auth_cfg, dict) else {}
    out = dict(raw)
    plain_user = str(out.pop("username", "") or "").strip()
    plain_pass = str(out.pop("password", "") or "")
    user_hash = _normalize_auth_secret_hash(out.get("username_hash"))
    pass_hash = _normalize_auth_secret_hash(out.get("password_hash"))
    if plain_user:
        user_hash = _auth_secret_hash(plain_user)
    if plain_pass:
        pass_hash = _auth_secret_hash(plain_pass)
    out["enabled"] = bool(out.get("enabled"))
    out["realm"] = str(out.get("realm") or "Light RID Scanner").strip() or "Light RID Scanner"
    try:
        out["session_ttl_min"] = max(1, min(10080, int(out.get("session_ttl_min") or 30)))
    except Exception:
        out["session_ttl_min"] = 30
    out["login_methods"] = _normalize_auth_login_methods(
        out.get("login_methods"),
        default_missing=("password", "passkey"),
        default_empty=[],
    )
    out["username_hash"] = user_hash
    out["password_hash"] = pass_hash
    out["sso_links"] = _normalize_sso_links(out.get("sso_links"))
    out["passkeys"] = _normalize_passkeys(out.get("passkeys"))
    return out

def _prepare_api_cfg_for_save(api_cfg: dict | None) -> dict:
    raw = dict(api_cfg) if isinstance(api_cfg, dict) else {}
    out = dict(raw)
    plain_token = str(out.get("token") or out.get("token_plain") or "").strip()
    token_hash = _normalize_auth_secret_hash(out.get("token_hash"))
    if plain_token:
        token_hash = _auth_secret_hash(plain_token)
    tokens = _normalize_api_tokens(out.get("tokens"), plain_token, token_hash)
    first = tokens[0] if tokens else {}
    out["enabled"] = bool(out.get("enabled"))
    out["tokens"] = tokens
    out["token"] = str(first.get("token") or "")
    out["token_hash"] = str(first.get("token_hash") or "")
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
        if not passkey_ready:
            return "关闭账号密码登录前，至少先准备一把可用 PassKey"
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
        default_missing=("password", "passkey"),
        default_empty=("password", "passkey"),
    )
    u = _normalize_auth_secret_hash(base.get("username_hash"))
    p = _normalize_auth_secret_hash(base.get("password_hash"))
    if (not u) and plain_user:
        u = _auth_secret_hash(plain_user)
        _log("[WARN] auth.username detected in plain text; converted to scrypt in memory")
    if (not p) and plain_pass:
        p = _auth_secret_hash(plain_pass)
        _log("[WARN] auth.password detected in plain text; converted to scrypt in memory")
    base["username_hash"] = u
    base["password_hash"] = p
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
    if base.get("token") and not str(base.get("token_hash") or "").strip():
        base["token_hash"] = _auth_secret_hash(str(base.get("token") or "").strip())
        _log("[WARN] api.token detected in plain text; converted to scrypt in memory")
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
    if _portable_edition_enabled():
        METRICS_CFG["enabled"] = False

def init_auth_from_config(cfg: dict | None) -> None:
    global AUTH_CFG, AUTH_SESSION_TTL_SEC
    AUTH_CFG = _normalize_auth_cfg(cfg)
    if _portable_edition_enabled():
        AUTH_CFG.update({"enabled": False, "username_hash": "", "password_hash": "", "sso_links": [], "passkeys": []})
        AUTH_CFG["login_methods"] = []
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
    if _portable_edition_enabled():
        API_CFG.update({"enabled": False, "token": "", "token_hash": "", "tokens": []})

def init_notify_from_config(cfg: dict | None) -> None:
    global NOTIFY_CFG
    NOTIFY_CFG = _normalize_notify_cfg(cfg)
    if _portable_edition_enabled():
        NOTIFY_CFG.update({"enabled": False, "wecom_webhooks": [], "wecom_webhook_key": ""})
    hooks = _notify_wecom_targets(NOTIFY_CFG)
    if NOTIFY_CFG.get("enabled") and hooks:
        _log(f"[INFO] WeCom robot notification enabled ({len(hooks)} channel(s), online-only)")
    else:
        _log("[INFO] notify disabled (missing key or disabled)")

def reload_runtime_config(cfg: dict | None) -> tuple[bool, str]:
    global APP_CONFIG, PRINT_INTERVAL, MIN_GAP, LOST_TIMEOUT, CHANGE_ON_RSSI, CHANGE_ON_PL, RSSI_DELTA, DEBUG_MODE
    if not isinstance(cfg, dict):
        return False, "invalid config root"
    APP_CONFIG = _apply_portable_defaults(_deep_merge_dict(default_app_config(), cfg))
    init_web_from_config(APP_CONFIG)
    init_ap_from_config(APP_CONFIG)
    init_model_update_from_config(APP_CONFIG)
    init_config_update_from_config(APP_CONFIG)
    init_app_update_from_config(APP_CONFIG)
    init_metrics_from_config(APP_CONFIG)
    init_network_bindings_from_config(APP_CONFIG)
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
        LOST_TIMEOUT = max(3.0, min(3600.0, float(basic.get("lost_timeout", basic.get("offline_timeout", LOST_TIMEOUT)))))
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

