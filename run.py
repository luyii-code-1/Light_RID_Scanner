#!/usr/bin/env python3
"""run.py — OpenDroneID (Remote ID) WiFi 监听解析器（WLAN-only）

修复：
1) 检测稳定性：更宽松的 BasicID 验证、更完整的 IE/NAN 搜索
2) 列对齐：支持中文双宽字符（无需第三方库）
3) --debug 日志写入 TUI 缓冲区而非 stderr（不被吞掉）
4) 按 d 查看完整扫描日志（含原始帧 debug 信息）
5) 表格每 0.5s 强制刷新

用法：
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
    sys.exit("[FATAL] scapy 未安装: pip3 install scapy")

# ─────────────────────────────────────────────────────────────────────────────
# 常量
# ─────────────────────────────────────────────────────────────────────────────
ODID_OUI             = bytes([0xFA, 0x0B, 0xBC])
MSG_TYPE_BASIC_ID    = 0x0
MSG_TYPE_LOCATION    = 0x1
MSG_TYPE_PACK        = 0xF
ODID_MSG_SIZE        = 25

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
DWELL_2G_DEFAULT    = 250
DWELL_5G_DEFAULT    = 800
SETTLE_DEFAULT      = 30
MAC_BASIC_CACHE_MAX = 1000
ODID_MSG_TYPES_OK   = {0x0, 0x1, 0x2, 0x3, 0x4, 0x5, 0xF}
HEADING_MIN_MOVE_M  = 2.0
SSID_SN_RE          = re.compile(r"\bRID-([A-Za-z0-9]{4,64})\b")

LOG_BUF_SIZE = 4000   # 日志环形缓冲
TUI_REFRESH  = 0.5    # 表格强制刷新间隔（秒）
CONFIG_FILE_DEFAULT = "rid_config.json"
HISTORY_STORE_DEFAULT = "rid_history_cache.json"
HISTORY_SAVE_INTERVAL = 5.0
OUI_DB_DEFAULT = "oui.txt"
OUI_DB_URL = "https://standards-oui.ieee.org/oui/oui.txt"
AP_LIST_MAX_DEFAULT = 80
AP_STALE_TIMEOUT = 900.0
NOTIFY_REONLINE_COOLDOWN_DEFAULT = 300.0
DJI_LOOKUP_URL_DEFAULT = "https://repair.dji.com/device/search?re=cn&lang=zh-CN"

# ─────────────────────────────────────────────────────────────────────────────
# 全局状态（main() 赋值后使用）
# ─────────────────────────────────────────────────────────────────────────────
state_table: dict[str, dict] = {}
# Web side history cache: keep all seen drones after live-state purge.
history_table: dict[str, dict] = {}
state_lock = Lock()

log_buf:  deque[str] = deque(maxlen=LOG_BUF_SIZE)   # 普通日志（★/↻/LOST/INFO）
scan_buf: deque[str] = deque(maxlen=LOG_BUF_SIZE)   # 完整扫描日志（含 debug 帧信息）
ap_buf:   deque[str] = deque(maxlen=500)             # AP 扫描日志（HTTP 用）
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

# 运行时参数（main 赋值）
PRINT_INTERVAL: float = DEFAULT_PRINT_INTERVAL
MIN_GAP:        float = DEFAULT_MIN_GAP
CHANGE_ON_RSSI: bool  = False
CHANGE_ON_PL:   bool  = False
RSSI_DELTA:     int   = 3
MODEL_MAP:      dict[str, str] = {}
NO_TUI:         bool  = False
DEBUG_MODE:     bool  = False

# ─────────────────────────────────────────────────────────────────────────────
# 中文对齐辅助（无需 wcwidth 库）
# ─────────────────────────────────────────────────────────────────────────────
def _cw(c: str) -> int:
    """返回字符的显示宽度（CJK=2，其余=1）"""
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
    """字符串显示宽度"""
    return sum(_cw(c) for c in s)

def _pad(s: str, w: int) -> str:
    """将字符串填充/截断到显示宽度 w（中文安全）"""
    out, cur = "", 0
    for c in s:
        cw = _cw(c)
        if cur + cw > w:
            break
        out += c
        cur += cw
    return out + " " * (w - cur)

# ─────────────────────────────────────────────────────────────────────────────
# 日志
# ─────────────────────────────────────────────────────────────────────────────
def _log(msg: str) -> None:
    ts   = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    with log_lock:
        log_buf.append(line)
        scan_buf.append(line)   # 普通日志也进扫描流
    if NO_TUI:
        print(line, flush=True)

def _scan(msg: str) -> None:
    """仅写入扫描日志流（不写普通日志，不 print）"""
    ts   = time.strftime("%H:%M:%S")
    line = f"[{ts}] {msg}"
    with log_lock:
        scan_buf.append(line)

def _history_mark_dirty() -> None:
    global history_persist_dirty
    history_persist_dirty = True

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
            "rssi": e.get("rssi"),
            "move_dir": e.get("move_dir"),
            "first_seen_wall_ts": e.get("first_seen_wall_ts"),
            "last_seen_wall_ts": e.get("last_seen_wall_ts"),
            "pkt_count_total": int(e.get("pkt_count_total") or 0),
            "notify_first_online_sent": bool(e.get("notify_first_online_sent")),
            "notify_last_wall_ts": e.get("notify_last_wall_ts"),
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
            _log(f"[WARN] 历史缓存格式错误: {path}")
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
                for k in ("src_mac","id_type","model","last_ch","ch_assumed","lat","lon",
                          "alt","speed","vspeed","rssi","move_dir",
                          "first_seen_wall_ts","last_seen_wall_ts",
                          "notify_first_online_sent","notify_last_wall_ts"):
                    if k in raw:
                        h[k] = raw.get(k)
                h["pkt_count_total"] = max(0, int(raw.get("pkt_count_total") or 0))
                # Monotonic timestamps are process-local; keep them unset until new packets arrive.
                h.setdefault("first_seen_ts", None)
                h.setdefault("last_seen_ts", None)
                history_table[sn] = h
                loaded += 1
            history_persist_dirty = False
            history_persist_last_save_wall = time.time()
        _log(f"[INFO] 历史缓存已加载: {path} ({loaded} 架)")
    except Exception as e:
        _log(f"[WARN] 历史缓存加载失败: {e}")

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
                "version": 1,
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
                _log(f"[WARN] 历史缓存保存失败: {path}")
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
                _log(f"[WARN] 历史缓存文件删除失败: {e}")
            try:
                tmp_path = path + ".tmp"
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except Exception:
                pass
    _log(f"[INFO] 历史缓存已清空: {cleared} 架" + (f" (删除文件 {path})" if removed_file else ""))
    return cleared, removed_file

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
    _log(f"[INFO] 已创建配置文件: {path}")

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
        _log(f"[INFO] 配置已加载: {path}")
        return cfg
    except Exception as e:
        _log(f"[WARN] 配置加载失败，使用默认配置: {e}")
        return default_app_config()

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

def apply_config_to_args(parser: argparse.ArgumentParser, args, cfg: dict) -> None:
    basic = cfg.get("basic") if isinstance(cfg, dict) else {}
    if not isinstance(basic, dict):
        return
    explicit = _parser_explicit_dests(parser, sys.argv[1:])
    for dest in (
        "iface", "channel", "hop", "hop_5g",
        "dwell_2g", "dwell_5g", "settle", "dwell_on_hit", "hit_cap",
        "time", "min_gap", "rssi_delta",
        "change_on_rssi", "change_on_payload",
        "model_map", "history_file",
        "no_tui", "debug",
    ):
        if dest in explicit:
            continue
        if dest in basic:
            setattr(args, dest, basic.get(dest))

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

def init_ap_from_config(cfg: dict | None) -> None:
    global AP_CFG
    AP_CFG = _normalize_ap_cfg(cfg)

def init_notify_from_config(cfg: dict | None) -> None:
    global NOTIFY_CFG
    NOTIFY_CFG = _normalize_notify_cfg(cfg)
    key = NOTIFY_CFG.get("wecom_webhook_key") or ""
    if NOTIFY_CFG.get("enabled") and key:
        _log("[INFO] 企业微信机器人通知已启用（仅上线）")
    else:
        _log("[INFO] 企业微信机器人通知未启用（缺少 key 或 disabled）")

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
        _log("[WARN] 通知队列已满，丢弃一条通知")

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
                _log(f"[WARN] 企业微信通知发送失败: {resp}")
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
                _log(f"[WARN] OUI 数据库下载失败: {info}")
        if loaded_map:
            with oui_db_lock:
                oui_map = loaded_map
                oui_loaded = True
                oui_vendor_cache.clear()
            with ap_lock:
                ap_list_seq += 1
            _log(f"[INFO] OUI 数据库已加载: {len(loaded_map)} 条")
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
        _log(f"[WARN] OUI 数据库加载异常: {e}")
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
        if vendor and (e.get("vendor") in ("", "加载中", "未知") or vendor not in ("加载中", "未知")):
            e["vendor"] = vendor
        vname = str(e.get("vendor") or vendor or "")
        e["vendor_type"] = _ap_vendor_type(vname, e.get("ssid"))
        _ap_trim_locked(now_wall)
        ap_list_seq += 1

def _ap_snapshot() -> tuple[list[dict], int]:
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
            "vendor_type": _ap_vendor_type(vendor or str(e.get("vendor") or ""), e.get("ssid")),
            "age": age,
            "last_seen": _fmt_wall_ts(last_seen_wall),
        })
    rows.sort(key=lambda x: (x["age"], -(x.get("hits") or 0), x.get("mac") or ""))
    limit = int(AP_CFG.get("list_max") or AP_LIST_MAX_DEFAULT)
    return rows[:limit], seq

# ─────────────────────────────────────────────────────────────────────────────
# 机型映射
# ─────────────────────────────────────────────────────────────────────────────
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
            _log(f"[INFO] 机型映射: {path} ({len(MODEL_MAP)} 条)")
        else:
            _log(f"[WARN] 机型映射格式错误: {path}")
    except FileNotFoundError:
        _log(f"[WARN] 机型映射不存在: {path}")
    except Exception as e:
        _log(f"[WARN] 机型映射加载失败: {e}")

# ─────────────────────────────────────────────────────────────────────────────
# 格式化
# ─────────────────────────────────────────────────────────────────────────────
def _fmt(v, fmt=".6f", unit="", na="N/A") -> str:
    return f"{v:{fmt}}{unit}" if v is not None else na

# ─────────────────────────────────────────────────────────────────────────────
# 地理
# ─────────────────────────────────────────────────────────────────────────────
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

# ─────────────────────────────────────────────────────────────────────────────
# 系统命令 / 接口
# ─────────────────────────────────────────────────────────────────────────────
def run_cmd(cmd: str, timeout: int = 5) -> str:
    try:
        r = subprocess.run(cmd, shell=True, capture_output=True, text=True, timeout=timeout)
        return (r.stdout or "").strip()
    except Exception:
        return ""

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
    _log(f"[INFO] 接口={iface} 当前模式={mode}")
    if mode != "monitor":
        _log(f"[INFO] 切换到 monitor 模式...")
        for c in (f"ip link set {iface} down",
                  f"iw dev {iface} set type monitor",
                  f"ip link set {iface} up"):
            run_cmd(c)
        new = run_cmd(f"iw dev {iface} info | grep type").strip()
        _log(f"[INFO] 切换结果: {new}")
    ch_info = run_cmd(f"iw dev {iface} info | grep channel").strip()
    _log(f"[INFO] 当前信道: {ch_info or 'unknown'}")
    return iface

def detect_5g(iface: str) -> bool:
    out = run_cmd(f"iw dev {iface} info")
    m   = re.search(r"\bwiphy\s+(\d+)", out)
    if not m: return False
    phy = run_cmd(f"iw phy{m.group(1)} info")
    if "Band 2:" in phy: return True
    return any(5000<=int(x)<=5999 for x in re.findall(r"\b(5\d{3})\s+MHz\b", phy))

# ─────────────────────────────────────────────────────────────────────────────
# Channel hopper
# ─────────────────────────────────────────────────────────────────────────────
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

# ─────────────────────────────────────────────────────────────────────────────
# ODID 解码
# ─────────────────────────────────────────────────────────────────────────────
def decode_basic_id(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE: return None
    try:
        if ((msg25[0]>>4)&0xF) != MSG_TYPE_BASIC_ID: return None
        id_type = msg25[1] & 0x0F
        raw = msg25[2:22].rstrip(b"\x00")
        if not raw: return None
        # 宽松：允许 >= 4 字节，允许部分非 ascii 字节被替换
        try:
            s = raw.decode("ascii", errors="replace").strip()
        except Exception:
            return None
        # 过滤全替换字符
        if not s or s.count("?") > len(s)//2: return None
        # 去掉不可打印字符
        s = "".join(c if 32<=ord(c)<=126 else "" for c in s)
        if len(s) < 4: return None
        return {"uas_id": s, "id_type": UA_ID_TYPE.get(id_type, f"Unk{id_type}")}
    except Exception:
        return None

def decode_location(msg25: bytes) -> dict | None:
    if len(msg25) < ODID_MSG_SIZE: return None
    try:
        if ((msg25[0]>>4)&0xF) != MSG_TYPE_LOCATION: return None
        sm = msg25[1] & 0x1

        def _try_layout(endian: str, lat_off: int, lon_off: int, alt_off: int,
                        spd_off: int = 3, vsp_off: int = 4) -> dict | None:
            try:
                sr = msg25[spd_off]
                vr = struct.unpack_from("b", msg25, vsp_off)[0]
                lat_raw = struct.unpack_from(f"{endian}i", msg25, lat_off)[0]
                lon_raw = struct.unpack_from(f"{endian}i", msg25, lon_off)[0]
                alt_raw = struct.unpack_from(f"{endian}H", msg25, alt_off)[0]
            except Exception:
                return None
            lat = lat_raw * LOC_LAT_LON_MULT
            lon = lon_raw * LOC_LAT_LON_MULT
            if not (-90.0 <= lat <= 90.0 and -180.0 <= lon <= 180.0):
                return None
            alt = None if alt_raw == 0xFFFF else (alt_raw * LOC_ALT_MULT + LOC_ALT_OFFSET)
            spd = None if sr == 255 else sr * (0.75 if sm else 0.25)
            vsp = None if vr in (-128, 127) else vr * 0.5
            return {"lat": lat, "lon": lon, "alt_geodetic": alt,
                    "speed_ms": spd, "vspeed_ms": vsp}

        # Prefer current layout (byte5/9/15), but fall back for vendor/implementation
        # differences (endianness or legacy off-by-one layout) to avoid all-N/A positions.
        opp = "<" if LOC_ENDIAN == ">" else ">"
        for endian, lat_off, lon_off, alt_off in (
            (LOC_ENDIAN, 5, 9, 15),
            (opp,       5, 9, 15),
            (LOC_ENDIAN, 4, 8, 14),
            (opp,       4, 8, 14),
        ):
            out = _try_layout(endian, lat_off, lon_off, alt_off)
            if out is not None:
                return out
        return None
    except Exception:
        return None

def _valid_payload(p: bytes) -> bool:
    if not p or len(p) < 1: return False
    mt = (p[0]>>4)&0xF
    if mt not in ODID_MSG_TYPES_OK: return False
    if mt == MSG_TYPE_PACK:
        if len(p) < 2: return False
        qty = p[1]
        if not (1 <= qty <= 9): return False
        if 2+qty*ODID_MSG_SIZE > len(p): return False
        for i in range(qty):
            if (p[2+i*ODID_MSG_SIZE]>>4)&0xF not in ODID_MSG_TYPES_OK: return False
        return True
    return len(p) >= ODID_MSG_SIZE

def decode_odid(payload: bytes) -> dict:
    res: dict = {"basic_id": None, "location": None}
    if not payload: return res
    mt = (payload[0]>>4)&0xF
    if mt == MSG_TYPE_PACK:
        if len(payload) < 2: return res
        for i in range(payload[1]):
            s, e = 2+i*ODID_MSG_SIZE, 2+(i+1)*ODID_MSG_SIZE
            if e > len(payload): break
            sub = payload[s:e]
            st  = (sub[0]>>4)&0xF
            if st==MSG_TYPE_BASIC_ID  and not res["basic_id"]:  res["basic_id"]  = decode_basic_id(sub)
            elif st==MSG_TYPE_LOCATION and not res["location"]: res["location"]  = decode_location(sub)
        return res
    if len(payload) >= ODID_MSG_SIZE:
        m = payload[:ODID_MSG_SIZE]
        if mt==MSG_TYPE_BASIC_ID:   res["basic_id"]  = decode_basic_id(m)
        elif mt==MSG_TYPE_LOCATION: res["location"]  = decode_location(m)
    return res

# ─────────────────────────────────────────────────────────────────────────────
# IE / NAN 提取（更健壮）
# ─────────────────────────────────────────────────────────────────────────────
def extract_from_ies(pkt) -> list[bytes]:
    results: list[bytes] = []
    elt = pkt.getlayer(Dot11Elt)
    while elt and isinstance(elt, Dot11Elt):
        if elt.ID == 221:
            info = bytes(elt.info) if elt.info else b""
            # 标准 OUI 前缀（4字节：OUI + subtype）
            if len(info) >= 4 and info[:3] == ODID_OUI:
                p = info[4:]
                if _valid_payload(p): results.append(p)
            else:
                # 在 IE 内搜索 OUI（处理偏移/包装变体）
                idx = 0
                while True:
                    pos = info.find(ODID_OUI, idx)
                    if pos < 0: break
                    p = info[pos+4:]
                    if p and _valid_payload(p): results.append(p)
                    idx = pos + 1
        try:
            nxt = elt.payload
            if not isinstance(nxt, Dot11Elt): break
            elt = nxt
        except Exception:
            break
    return results

def extract_from_raw(pkt) -> list[bytes]:
    """在原始帧字节流中搜索 ODID OUI（用于 NAN / Action 帧）"""
    try: raw = bytes(pkt)
    except Exception: return []
    results: list[bytes] = []
    idx = 0
    while True:
        pos = raw.find(ODID_OUI, idx)
        if pos < 0: break
        p = raw[pos+4 : pos+4+2+9*ODID_MSG_SIZE]
        if p and _valid_payload(p): results.append(p)
        idx = pos + 1
    return results

# ─────────────────────────────────────────────────────────────────────────────
# 状态更新
# ─────────────────────────────────────────────────────────────────────────────
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
    h["rssi"] = e.get("rssi")
    h["move_dir"] = e.get("move_dir")
    h["last_seen_ts"] = now
    h["last_seen_wall_ts"] = now_wall
    h["pkt_count_total"] = h.get("pkt_count_total", 0) + 1
    h.setdefault("notify_first_online_sent", False)
    h.setdefault("notify_last_wall_ts", 0.0)
    _history_mark_dirty()

def state_update(src_mac: str, decoded: dict, rssi: int | None,
                 ch: int, ch_assumed: bool, pl_sig: int) -> None:
    basic = decoded.get("basic_id")
    loc   = decoded.get("location")

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

    model = _model_from_sn(sn)
    now   = time.monotonic()
    now_wall = time.time()

    with state_lock:
        # MAC → SN 迁移
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
                "last_print_ts":0.0,
                "pl_sig":None, "rssi":None, "last_ch":None, "ch_assumed":False,
                "lat":None, "lon":None, "alt":None, "speed":None, "vspeed":None,
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
        e["pkt_count"]    += 1
        if e["pkt_count"] > 1:
            iv = now - e["last_pkt_ts"]
            e["rx_avg"] = 0.3*iv + 0.7*(e["rx_avg"] or iv)
        e["last_pkt_ts"] = now
        e["id_type"] = it or e.get("id_type")
        e["model"]   = model

        if CHANGE_ON_PL:   e["pl_sig"] = pl_sig
        if rssi is not None:
            old = e.get("rssi")
            if old is None or not CHANGE_ON_RSSI or abs(rssi-old)>=RSSI_DELTA:
                e["rssi"] = rssi
        if ch:
            e["last_ch"]   = ch
            e["ch_assumed"] = bool(ch_assumed)

        if loc:
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
    mv_s  = f" 向={mv} Δ≈{md:.1f}m" if mv and md else ""
    pfx   = "★" if reason=="first" else "↻"
    _log(f"{pfx} SN={sn} 机型={model} 类型={it} MAC={mac} "
         f"经纬={lat},{lon} 高={alt} 速={spd} 垂={vsp} 信号={rssi} {ch_s} "
         f"包={pkts} ≈{avg_s}{mv_s}")

# ─────────────────────────────────────────────────────────────────────────────
# Lost checker
# ─────────────────────────────────────────────────────────────────────────────
def lost_checker() -> None:
    while True:
        time.sleep(1.0)
        now = time.monotonic()
        with state_lock:
            for sn, e in list(state_table.items()):
                age = now - e["last_seen_ts"]
                if age > LOST_TIMEOUT and not e["reported_lost"]:
                    _log(f"[LOST] SN={sn!r} {age:.0f}s未见 MAC={e.get('src_mac')}")
                    e["reported_lost"] = True
                if e["reported_lost"] and age > PURGE_TIMEOUT:
                    del state_table[sn]

# ─────────────────────────────────────────────────────────────────────────────
# HTTP + WebSocket 服务（端口 4600）
# ─────────────────────────────────────────────────────────────────────────────
HTTP_PORT = 4600

# 已连接的 WebSocket 客户端 socket 列表
_ws_clients: list = []
_ws_lock = Lock()

def _ws_push_loop() -> None:
    """每秒向所有 WS 客户端推送最新状态 JSON"""
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
    """封装一个 WebSocket text frame（RFC 6455，服务端无掩码）"""
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
    """返回可 JSON 序列化的当前状态快照"""
    now = time.monotonic()
    now_wall = time.time()
    with state_lock:
        live_by_sn = {str(e.get("sn","")): e for e in state_table.values() if e.get("sn")}
        drones = []
        for sn in (set(history_table.keys()) | set(live_by_sn.keys())):
            cur = live_by_sn.get(sn) or {}
            hist = history_table.get(sn) or cur
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
            ch = cur.get("last_ch", hist.get("last_ch")) or 0
            ch_assumed = bool(cur.get("ch_assumed", hist.get("ch_assumed")))
            drones.append({
                "sn": sn,
                "model": cur.get("model", hist.get("model","N/A")),
                "lost": lost,
                "archived": sn not in live_by_sn,
                "mac": cur.get("src_mac", hist.get("src_mac","")),
                "ch": f"{'~' if ch_assumed else ''}{ch}" if ch else "?",
                "lat": cur.get("lat", hist.get("lat")),
                "lon": cur.get("lon", hist.get("lon")),
                "alt": cur.get("alt", hist.get("alt")),
                "spd": cur.get("speed", hist.get("speed")),
                "vspd": cur.get("vspeed", hist.get("vspeed")),
                "rssi": cur.get("rssi", hist.get("rssi")),
                "pkts": hist.get("pkt_count_total", cur.get("pkt_count",0)),
                "dir": cur.get("move_dir", hist.get("move_dir")) or "-",
                "age": round(age),
                "first_seen": _fmt_wall_ts(hist.get("first_seen_wall_ts", cur.get("first_seen_wall_ts"))),
                "last_seen": _fmt_wall_ts(hist.get("last_seen_wall_ts", cur.get("last_seen_wall_ts"))),
            })
        drones.sort(key=lambda d: (d["lost"], d.get("archived", False), d["age"], d["sn"]))
        map_drones = [d for d in drones if not d.get("archived")]
    with log_lock:
        logs = list(ap_buf)[-80:]
        logs_seq = ap_seq
    aps, aps_seq = _ap_snapshot()
    return {
        "ts": time.strftime("%H:%M:%S"),
        "ch": f"ch{current_channel}" if current_channel else "ch?",
        "drones": drones,
        "map_drones": map_drones,
        "logs": logs,
        "logs_seq": logs_seq,
        "aps": aps,
        "aps_seq": aps_seq,
        "meta": {
            "dji_lookup_url": str(WEB_CFG.get("dji_lookup_url") or ""),
            "allow_restart": bool(WEB_CFG.get("allow_restart", True)),
            "restart_args_current": " ".join(sys.argv[1:]),
            "restart_args_saved": str(WEB_CFG.get("last_restart_args") or ""),
            "config_path": APP_CONFIG_PATH or "",
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
:root{--bg:#0a0e14;--bg2:#0d1117;--border:#1e2a38;--txt:#c5cdd9;
      --green:#3fb950;--yellow:#d29922;--dim:#6e7681;--blue:#58a6ff;
      --purple:#d2a8ff;--cyan:#79c0ff}
body{background:var(--bg);color:var(--txt);font-family:'Courier New',monospace;font-size:15px;
     height:100dvh;display:grid;grid-template-rows:auto minmax(0,1fr) minmax(240px,38vh) auto;
     row-gap:12px;overflow:hidden}

/* ── 顶栏 ── */
header{background:var(--bg2);border-bottom:1px solid var(--border);
       padding:10px 14px;display:grid;grid-template-columns:auto 1fr;
       align-items:center;gap:8px 16px;position:sticky;top:0;z-index:10}
header .head-stats{display:flex;align-items:center;justify-content:flex-end;
       gap:8px 16px;flex-wrap:wrap;min-width:0}
header h1{font-size:18px;font-weight:700;color:var(--blue);letter-spacing:.04em}
header details.adv{grid-column:1/-1;border:1px solid var(--border);border-radius:6px;background:#0b1320}
header details.adv > summary{cursor:pointer;list-style:none;padding:8px 10px;color:#8b949e;font-size:13px}
header details.adv > summary::-webkit-details-marker{display:none}
header details.adv[open] > summary{border-bottom:1px solid var(--border);color:var(--blue)}
.adv-body{padding:10px;display:grid;gap:8px}
.adv-row{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
.adv-row label{font-size:12px;color:#8b949e}
.adv-input{min-width:260px;flex:1 1 420px;background:#0a0e14;color:var(--txt);border:1px solid #2b3a4b;border-radius:6px;padding:7px 9px;font:inherit}
.adv-note{font-size:12px;color:#8b949e;word-break:break-all}
.adv-note code{color:#c5cdd9}
.adv-actions{display:flex;gap:8px;flex-wrap:wrap}
.stat{font-size:14px;color:#8b949e;white-space:nowrap}
.stat b{color:var(--green)}
.stat.ls b{color:var(--dim)}
.stat.cs b{color:var(--purple)}
.stat.ts b{color:var(--cyan);font-weight:400}
#dot-ws{width:9px;height:9px;border-radius:50%;background:var(--dim);
        display:inline-block;margin-right:4px;transition:background .3s}
#dot-ws.on{background:var(--green)}

/* ── 表格 ── */
.tbl-wrap{margin:0 12px;min-height:0;overflow:auto;
          border:1px solid var(--border);border-radius:6px;background:var(--bg2)}
table{width:100%;border-collapse:collapse;table-layout:fixed;min-width:1280px}
thead tr{background:var(--bg2);position:sticky;top:0;z-index:9}
thead th{padding:9px 10px;text-align:left;font-size:13px;color:#8b949e;
         border-bottom:1px solid var(--border);white-space:nowrap}
tbody tr{border-bottom:1px solid #161b22;transition:background .12s}
tbody tr:hover{background:#161b22}
tbody tr.live td:first-child{color:var(--green)}
tbody tr.mac  td:first-child{color:var(--yellow)}
tbody tr.lost{opacity:.4}
tbody tr.lost td:first-child{color:var(--dim)}
td{padding:8px 10px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:15px}
.mono{font-family:'Courier New',monospace}
.empty{text-align:center;padding:40px;color:var(--dim);font-size:15px}
th:nth-child(1),td:nth-child(1){width:28px}
th:nth-child(2),td:nth-child(2){width:248px}
th:nth-child(3),td:nth-child(3){width:120px}
th:nth-child(4),td:nth-child(4){width:50px}
th:nth-child(5),td:nth-child(5),th:nth-child(6),td:nth-child(6){width:108px}
th:nth-child(7),td:nth-child(7){width:80px}
th:nth-child(8),td:nth-child(8),th:nth-child(9),td:nth-child(9){width:84px}
th:nth-child(10),td:nth-child(10){width:78px}
th:nth-child(11),td:nth-child(11){width:50px}
th:nth-child(12),td:nth-child(12){width:44px}
th:nth-child(13),td:nth-child(13){width:54px}
th:nth-child(14),td:nth-child(14),th:nth-child(15),td:nth-child(15){width:172px}

/* ── 下方两栏：地图 + 日志 ── */
.bottom{display:grid;grid-template-columns:minmax(0,1.15fr) minmax(0,1fr) minmax(0,.95fr);gap:12px;
        margin:0 12px;min-height:0}
@media(max-width:960px){
  header{grid-template-columns:1fr}
  header .head-stats{justify-content:flex-start}
}
@media(max-width:1180px){
  .bottom{grid-template-columns:minmax(0,1fr) minmax(0,1fr)}
  .bottom .panel.ap-panel{grid-column:1/-1;min-height:220px}
}
@media(max-width:800px){
  body{grid-template-rows:auto minmax(0,1fr) minmax(220px,42vh) auto}
  .bottom{grid-template-columns:1fr;grid-template-rows:minmax(0,1fr) minmax(0,1fr)}
  .bottom .panel.ap-panel{grid-column:auto;min-height:220px}
  .adv-input{min-width:0;flex-basis:100%}
  th:nth-child(2),td:nth-child(2){width:220px}
  td{padding:7px 8px;font-size:14px}
}

.panel{border:1px solid var(--border);border-radius:6px;overflow:hidden;
       display:flex;flex-direction:column;min-height:0}
.panel-hdr{background:var(--bg2);padding:8px 14px;font-size:13px;
           color:var(--blue);font-weight:700;border-bottom:1px solid var(--border);
           display:flex;justify-content:space-between;align-items:center}
.panel-hdr span.sub{color:#8b949e;font-size:12px;font-weight:400}
.panel-hdr .hdr-actions{display:flex;align-items:center;gap:8px}
.panel.log-panel.collapsed .logbox{display:none}
.panel.log-panel.collapsed .panel-hdr{border-bottom:none}

/* ── Leaflet 地图 ── */
#map{flex:1;width:100%;min-height:0}

/* ── 日志框 ── */
.logbox{flex:1;overflow-y:auto;padding:7px 12px;
        font-family:'Courier New',monospace;font-size:13px;line-height:1.65;
        background:var(--bg);min-height:0}
.logbox .ap{color:var(--txt)}
.logbox .rid{color:var(--green);font-weight:700}
.panel-hdr label{display:flex;align-items:center;gap:6px;cursor:pointer;
                 color:#8b949e;font-weight:400;font-size:12px}
.btn-mini{
  border:1px solid #39485a;background:#121923;color:#c5cdd9;
  padding:4px 8px;border-radius:5px;font:inherit;font-size:12px;cursor:pointer;
}
.btn-mini:hover{background:#182232}
.btn-mini:disabled{opacity:.55;cursor:wait}
.btn-mini.warn{border-color:#7f3f3f;color:#ffb4b4}
.btn-mini.warn:hover{background:#2a1717}
.sn-cell{display:flex;align-items:center;gap:6px;min-width:0}
.sn-cell .mono{min-width:0;overflow:hidden;text-overflow:ellipsis}
.icon-btn{
  border:1px solid #314156;background:#0d1622;color:#b6c2d2;
  width:22px;height:22px;display:inline-flex;align-items:center;justify-content:center;
  border-radius:5px;cursor:pointer;font-size:12px;line-height:1;flex:0 0 auto;
}
.icon-btn:hover{background:#172334;color:#fff}
.icon-btn.done{border-color:#2a6a45;color:#9ef0bc}
.aplist{flex:1;overflow:auto;background:var(--bg);font-family:'Courier New',monospace;font-size:12px;line-height:1.45;padding:6px 8px}
.aplist .ap-empty{color:var(--dim);padding:14px 8px}
.aprow{display:grid;grid-template-columns:132px 52px 60px 54px 86px minmax(0,1fr);gap:8px;padding:5px 6px;border-bottom:1px solid #141b23;align-items:start}
.aprow:hover{background:#101722}
.aprow.hd{position:sticky;top:0;background:#0d1117;color:#8b949e;font-weight:700;z-index:1}
.aprow .mono{white-space:nowrap;overflow:visible;text-overflow:clip}
.aprow .ssid{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all}
.aprow .vendor{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all;color:#c9d5e6}
.subline{font-size:11px;color:#8b949e}
 
footer{text-align:center;padding:8px 10px;font-size:12px;color:#3d444d}
</style>
</head><body>
<header>
  <h1>&#x2708; RID Monitor</h1>
  <div class="head-stats">
  <span class="stat">在线 <b id="n-live">-</b></span>
  <span class="stat ls">离线 <b id="n-lost">-</b></span>
  <span class="stat cs">信道 <b id="cur-ch">-</b></span>
  <span class="stat ts">更新 <b id="cur-ts">-</b></span>
  <span class="stat"><span id="dot-ws"></span><span id="ws-status">连接中…</span></span>
  <button class="btn-mini" id="btn-clear-history" type="button">清空历史</button>
  </div>
</header>

<div class="tbl-wrap">
<table id="dtable">
<thead><tr>
  <th></th><th>SN</th><th>机型</th><th>ch</th>
  <th>纬度</th><th>经度</th><th>高程</th>
  <th>速度</th><th>垂速</th><th>信号</th>
  <th>包</th><th>方向</th><th>上次</th><th>首次上线</th><th>最后上线</th>
</tr></thead>
<tbody id="tbody"></tbody>
</table>
</div>

<div class="bottom">
  <div class="panel">
    <div class="panel-hdr">
      &#x1F5FA; 地图
      <span class="sub" id="map-hint">等待坐标…</span>
    </div>
    <div id="map"></div>
  </div>
  <div class="panel">
    <div class="panel-hdr">
      &#x1F4E1; AP 扫描日志
      <label><input type="checkbox" id="autoscroll" checked>自动滚动</label>
    </div>
    <div class="logbox" id="logbox"></div>
  </div>
</div>

<footer>WebSocket 实时推送 &nbsp;·&nbsp; OpenDroneID RID Monitor</footer>

<script>
// ── WebSocket ────────────────────────────────────────────────
var ws, reconnTimer;
var lastLogsSeq = -1;
var lastApsSeq = -1;
var clearHistoryBusy = false;
var restartBusy = false;
var metaState = {};

function qs(id){ return document.getElementById(id); }
function fmt(v,dec,unit){ return v==null?'N/A':Number(v).toFixed(dec)+unit; }
function esc(v){
  return String(v==null?'':v)
    .replace(/&/g,'&amp;')
    .replace(/</g,'&lt;')
    .replace(/>/g,'&gt;')
    .replace(/"/g,'&quot;')
    .replace(/'/g,'&#39;');
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

function setLogPanelCollapsed(collapsed){
  var panel = qs('log-panel');
  if(!panel) return;
  if(collapsed) panel.classList.add('collapsed');
  else panel.classList.remove('collapsed');
  var btn = qs('log-panel-toggle');
  if(btn) btn.textContent = collapsed ? '\u5c55\u5f00' : '\u6536\u8d77';
}

function toggleLogPanel(){
  var panel = qs('log-panel');
  if(!panel) return;
  setLogPanelCollapsed(!panel.classList.contains('collapsed'));
}

function buildExtraUi(){
  if(window.__ridExtraUiReady) return;
  window.__ridExtraUiReady = true;

  var clearBtn = qs('btn-clear-history');
  if(clearBtn && !qs('btn-dji-lookup')){
    var djiBtn = document.createElement('button');
    djiBtn.className = 'btn-mini';
    djiBtn.id = 'btn-dji-lookup';
    djiBtn.type = 'button';
    djiBtn.textContent = 'DJI\u67e5\u8be2';
    clearBtn.parentNode.insertBefore(djiBtn, clearBtn);
  }

  var header = document.querySelector('header');
  if(header && !qs('adv-panel')){
    var details = document.createElement('details');
    details.className = 'adv';
    details.id = 'adv-panel';
    details.innerHTML =
      '<summary>\u9ad8\u7ea7\u9009\u9879</summary>'+
      '<div class="adv-body">'+
      '  <div class="adv-row">'+
      '    <label for="restart-args">\u53c2\u6570</label>'+
      '    <input id="restart-args" class="adv-input" type="text" placeholder="\u4f8b\u5982: --no-tui --channel 6">'+
      '  </div>'+
      '  <div class="adv-actions">'+
      '    <button class="btn-mini" id="btn-restart-once" type="button">\u4ec5\u672c\u6b21\u91cd\u542f</button>'+
      '    <button class="btn-mini warn" id="btn-restart-save" type="button">\u4fdd\u5b58\u5e76\u91cd\u542f</button>'+
      '  </div>'+
      '  <div class="adv-note">DJI\u5730\u5740: <code id="dji-url-text">-</code></div>'+
      '  <div class="adv-note">\u5f53\u524d\u53c2\u6570: <code id="restart-current-args">-</code></div>'+
      '  <div class="adv-note">\u5df2\u4fdd\u5b58\u53c2\u6570: <code id="restart-saved-args">-</code></div>'+
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

  var logBox = qs('logbox');
  if(logBox){
    var logPanel = logBox.closest ? logBox.closest('.panel') : null;
    if(logPanel){
      logPanel.id = 'log-panel';
      logPanel.classList.add('log-panel');
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

  if(qs('btn-clear-history')) qs('btn-clear-history').addEventListener('click', clearHistory);
  if(qs('btn-dji-lookup')) qs('btn-dji-lookup').addEventListener('click', openDjiLookup);
  if(qs('btn-restart-once')) qs('btn-restart-once').addEventListener('click', function(){ restartProgram(false); });
  if(qs('btn-restart-save')) qs('btn-restart-save').addEventListener('click', function(){ restartProgram(true); });
  if(qs('restart-args')) qs('restart-args').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('tbody')) qs('tbody').addEventListener('click', function(ev){
    var btn = ev.target && ev.target.closest ? ev.target.closest('.copy-sn') : null;
    if(!btn) return;
    copySn(btn.getAttribute('data-sn') || '');
  });
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
    alert('\u5df2\u6e05\u7a7a\u5386\u53f2' + (typeof data.cleared==='number' ? ('\uff08'+data.cleared+'\u67b6\uff09') : ''));
  }catch(e){
    alert('\u6e05\u7a7a\u5931\u8d25: ' + ((e && e.message) ? e.message : e));
  }finally{
    if(btn){ btn.disabled = false; btn.textContent = '\u6e05\u7a7a\u5386\u53f2'; }
    clearHistoryBusy = false;
  }
}

async function restartProgram(saveCfg){
  if(restartBusy) return;
  var input = qs('restart-args');
  var argsText = input ? String(input.value || '').trim() : '';
  var tip = saveCfg ? '\u4fdd\u5b58\u914d\u7f6e\u5e76\u91cd\u542f\u7a0b\u5e8f\uff1f' : '\u6309\u5f53\u524d\u8f93\u5165\u53c2\u6570\u91cd\u542f\u7a0b\u5e8f\uff08\u4ec5\u672c\u6b21\uff09\uff1f';
  if(!confirm(tip)) return;
  restartBusy = true;
  applyMeta(metaState);
  try{
    await postJson('/api/admin/restart', {args: argsText, save: !!saveCfg});
    alert(saveCfg ? '\u5df2\u63d0\u4ea4\uff1a\u4fdd\u5b58\u5e76\u91cd\u542f' : '\u5df2\u63d0\u4ea4\uff1a\u4ec5\u672c\u6b21\u91cd\u542f');
  }catch(e){
    alert('\u91cd\u542f\u5931\u8d25: ' + ((e && e.message) ? e.message : e));
  }finally{
    restartBusy = false;
    applyMeta(metaState);
  }
}

function renderAps(aps){
  var box = qs('aplist');
  if(!box) return;
  var rows = Array.isArray(aps) ? aps : [];
  if(qs('ap-list-count')) qs('ap-list-count').textContent = String(rows.length);
  if(!rows.length){
    box.innerHTML = '<div class="ap-empty">\u6682\u65e0AP\u6570\u636e</div>';
    return;
  }
  var html = '';
  html += '<div class="aprow hd"><div>MAC</div><div>ch</div><div>\u4fe1\u53f7</div><div>\u5e74\u9f84</div><div>\u7c7b\u578b</div><div>SSID / \u5382\u5546</div></div>';
  for(var i=0;i<rows.length;i++){
    var a = rows[i] || {};
    var ch = (a.ch==null || a.ch===0) ? '?' : ('ch'+a.ch);
    var rssi = (a.rssi==null) ? 'N/A' : (a.rssi+'dBm');
    var age = (a.age==null) ? '-' : (a.age+'s');
    var mac = String(a.mac || '');
    var ssid = String(a.ssid || '(hidden)');
    var vt = String(a.vendor_type || 'AP');
    var vn = String(a.vendor || '\u672a\u77e5');
    if(vn === '\u52a0\u8f7d\u4e2d' && Number(a.age || 0) >= 10) vn = '\u672a\u77e5';
    html += '<div class="aprow">'+
      '<div class="mono" title="'+esc(mac)+'">'+esc(mac)+'</div>'+
      '<div>'+esc(ch)+'</div>'+
      '<div>'+esc(rssi)+'</div>'+
      '<div>'+esc(age)+'</div>'+
      '<div>'+esc(vt)+'</div>'+
      '<div><div class="ssid" title="'+esc(ssid)+'">'+esc(ssid)+'</div><div class="subline vendor" title="'+esc(vn)+'">'+esc(vn)+'</div></div>'+
      '</div>';
  }
  box.innerHTML = html;
}

function connect(){
  ws = new WebSocket('ws://'+location.host+'/ws');
  ws.onopen  = function(){ setWsState(true); };
  ws.onclose = function(){ setWsState(false); reconnTimer=setTimeout(connect,2000); };
  ws.onerror = function(){ ws.close(); };
  ws.onmessage = function(ev){ onData(JSON.parse(ev.data)); };
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

  var rows='';
  if(!list.length){
    rows='<tr><td colspan="15" class="empty">\u6682\u65e0\u6570\u636e</td></tr>';
  } else {
    list.forEach(function(e){
      e = e || {};
      var sn = String(e.sn || '');
      var cls = e.lost ? 'lost' : (sn.indexOf('MAC:')===0 ? 'mac' : 'live');
      var dot = e.lost ? '&#9675;' : '&#9679;';
      rows += '<tr class="'+cls+'">'+
        '<td>'+dot+'</td>'+
        '<td><div class="sn-cell"><span class="mono">'+esc(sn)+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+esc(sn)+'" title="\u590d\u5236SN">&#x29C9;</button></div></td>'+
        '<td>'+esc(e.model || 'N/A')+'</td>'+
        '<td>'+esc(e.ch || '?')+'</td>'+
        '<td class="mono">'+fmt(e.lat,5,'')+'</td>'+
        '<td class="mono">'+fmt(e.lon,5,'')+'</td>'+
        '<td>'+fmt(e.alt,1,'m')+'</td>'+
        '<td>'+fmt(e.spd,1,'m/s')+'</td>'+
        '<td>'+fmt(e.vspd,1,'')+'</td>'+
        '<td>'+fmt(e.rssi,0,'dBm')+'</td>'+
        '<td>'+esc(e.pkts==null?'0':e.pkts)+'</td>'+
        '<td>'+esc(e.dir || '-')+'</td>'+
        '<td>'+esc((e.age==null?'-':e.age)+'s')+'</td>'+
        '<td class="mono">'+esc(e.first_seen || '-')+'</td>'+
        '<td class="mono">'+esc(e.last_seen || '-')+'</td>'+
        '</tr>';
    });
  }
  qs('tbody').innerHTML = rows;

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
    renderAps(d.aps || []);
    lastApsSeq = d.aps_seq;
  }

  initMap();
  updateMap(d.map_drones || d.drones || []);
}

buildExtraUi();
connect();

var map = null, markers = {}, trails = {};
var COLORS = ['#58a6ff','#3fb950','#d29922','#d2a8ff','#79c0ff','#ff7b72'];
var colorIdx = {};
window.addEventListener('resize', function(){ if(map) map.invalidateSize(false); });

function initMap(){
  if(map) return;
  map = L.map('map', {zoomControl:true, attributionControl:true});
  L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png',{
    maxZoom:19,
    attribution:'© <a href="https://openstreetmap.org">OpenStreetMap</a>'
  }).addTo(map);
  map.setView([30, 114], 5);
  setTimeout(function(){ if(map) map.invalidateSize(false); }, 0);
}

function droneIcon(color, lost){
  var op = lost ? 0.4 : 1.0;
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="28" height="28" viewBox="0 0 28 28">'
    +'<circle cx="14" cy="14" r="10" fill="'+color+'" fill-opacity="'+op+'" stroke="#fff" stroke-width="1.5"/>'
    +'<text x="14" y="19" text-anchor="middle" font-size="13" fill="#fff" font-family="monospace" font-weight="bold">✈</text>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[28,28], iconAnchor:[14,14], popupAnchor:[0,-14]
  });
}

function updateMap(drones){
  if(!map) return;
  var live = drones.filter(function(e){ return e.lat!=null && e.lon!=null; });
  if(!live.length){
    document.getElementById('map-hint').textContent='无坐标数据';
    return;
  }
  document.getElementById('map-hint').textContent = live.length+'架有坐标';

  // 分配颜色
  live.forEach(function(e){
    if(!colorIdx[e.sn]){
      var n = Object.keys(colorIdx).length;
      colorIdx[e.sn] = COLORS[n % COLORS.length];
    }
  });

  var activeSns = {};
  live.forEach(function(e){
    activeSns[e.sn] = true;
    var col = colorIdx[e.sn];
    var popup = '<b>'+e.sn+'</b><br>'+e.model+'<br>'
      +(e.lat!=null?e.lat.toFixed(5):'-')+', '+(e.lon!=null?e.lon.toFixed(5):'-')
      +'<br>高程: '+(e.alt!=null?e.alt.toFixed(1)+'m':'N/A')
      +'<br>速度: '+(e.spd!=null?e.spd.toFixed(1)+'m/s':'N/A')
      +'<br>信号: '+(e.rssi!=null?e.rssi+'dBm':'N/A')
      +'<br>上次: '+e.age+'s';

    if(markers[e.sn]){
      markers[e.sn].setLatLng([e.lat, e.lon])
                   .setIcon(droneIcon(col, e.lost))
                   .setPopupContent(popup);
    } else {
      markers[e.sn] = L.marker([e.lat, e.lon], {icon: droneIcon(col, e.lost)})
        .addTo(map).bindPopup(popup);
    }

    // 轨迹
    if(!trails[e.sn]) trails[e.sn] = [];
    var tr = trails[e.sn];
    var last = tr[tr.length-1];
    if(!last || last[0]!==e.lat || last[1]!==e.lon){
      tr.push([e.lat, e.lon]);
      if(tr.length > 60) tr.shift();
    }
    if(trails[e.sn+'_line']){
      trails[e.sn+'_line'].setLatLngs(tr);
    } else {
      trails[e.sn+'_line'] = L.polyline(tr, {color:col, weight:2, opacity:0.6, dashArray:'5,4'}).addTo(map);
    }
  });

  // 移除消失的标记
  Object.keys(markers).forEach(function(sn){
    if(!activeSns[sn]){
      map.removeLayer(markers[sn]); delete markers[sn];
      if(trails[sn+'_line']){ map.removeLayer(trails[sn+'_line']); delete trails[sn+'_line']; }
    }
  });

  // 首次自动定位到所有点
  if(live.length && !map._rid_fitted){
    var latlngs = live.map(function(e){ return [e.lat, e.lon]; });
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
            if self.path in ("/", "/index.html"):
                body = _PAGE_HTML.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif self.path == "/ws":
                # headers 已由 BaseHTTPRequestHandler 解析好，直接取 key
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
                # 保持连接，排空客户端帧直到断开
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
            if self.path == "/api/history/clear":
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
            elif self.path == "/api/admin/restart":
                body = self._read_json_body()
                if not bool(WEB_CFG.get("allow_restart", True)):
                    self._send_json({"ok": False, "error": "restart disabled"}, 403)
                    return
                args_text = str(body.get("args") or "")
                save_cfg = bool(body.get("save"))
                try:
                    tokens, raw = _parse_restart_args_text(args_text)
                    if save_cfg:
                        ok, msg = _save_basic_config_from_tokens(tokens, raw_text=raw or args_text)
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
            else:
                self._send_json({"ok": False, "error": "not found"}, 404)

        def log_message(self, *_): pass

    try:
        srv = ThreadingHTTPServer(("0.0.0.0", HTTP_PORT), Handler)
    except OSError as e:
        _log(f"[WARN] HTTP+WS 服务启动失败(端口{HTTP_PORT}被占用?): {e}，继续运行抓包")
        return

    _threading.Thread(target=_ws_push_loop, daemon=True).start()
    _log(f"[INFO] HTTP+WS 服务已启动: http://0.0.0.0:{HTTP_PORT}/")
    try:
        srv.serve_forever()
    except Exception as e:
        _log(f"[WARN] HTTP+WS 服务异常退出: {e}")

# ─────────────────────────────────────────────────────────────────────────────
# parse_frame
# ─────────────────────────────────────────────────────────────────────────────
def parse_frame(pkt) -> None:
    global ap_seq
    try:
        if not pkt.haslayer(Dot11): return
        d11 = pkt[Dot11]
        if d11.type != 0 or d11.subtype not in (8, 5, 13): return

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
            # AP 扫描日志（供 HTTP 日志框使用）
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
        if d11.subtype in (13, 5, 8):   # 额外: 对所有管理帧类型也搜索原始
            raw_p = extract_from_raw(pkt)
            # 去重
            sigs = {zlib.crc32(p)&0xFFFFFFFF for p in payloads}
            for p in raw_p:
                if (zlib.crc32(p)&0xFFFFFFFF) not in sigs:
                    payloads.append(p)

        # Debug 扫描日志
        if DEBUG_MODE:
            rssi_s  = f"{rssi}dBm" if rssi is not None else "N/A"
            ch_s    = f"{'~' if ch_assumed else ''}ch{ch}" if ch else "ch?"
            subtype_name = {8:"Beacon",5:"ProbeResp",13:"Action"}.get(d11.subtype,"Mgmt")
            ssid_s  = f" SSID={ssid!r}" if ssid else ""
            odid_s  = ""
            if payloads:
                types = [f"{((p[0]>>4)&0xF):X}" for p in payloads if p]
                odid_s = f" ODID={len(payloads)}[{','.join(types)}]"
            _scan(f"[FRAME] {subtype_name} src={src_mac} {rssi_s} {ch_s}{ssid_s}{odid_s}")

        if not payloads:
            # 即使没有 ODID 载荷，只要 SSID 含 RID SN，也刷新 last_seen_ts
            if ssid and src_mac in mac_to_ssid_sn:
                state_update(src_mac, {"basic_id": None, "location": None},
                             rssi=rssi, ch=ch, ch_assumed=ch_assumed, pl_sig=0)
            return

        _notify_hit(ch if not ch_assumed or ch==current_channel else 0)

        def explode(p: bytes) -> list[bytes]:
            if not p: return []
            mt = (p[0]>>4)&0xF
            if mt != MSG_TYPE_PACK:
                return [p[:ODID_MSG_SIZE]] if len(p)>=ODID_MSG_SIZE else [p]
            qty = p[1] if len(p)>=2 else 0
            out = []
            for i in range(qty):
                s, e2 = 2+i*ODID_MSG_SIZE, 2+(i+1)*ODID_MSG_SIZE
                if e2 <= len(p): out.append(p[s:e2])
            return out or [p]

        for payload in payloads:
            if not payload: continue
            for piece in explode(payload):
                sig     = zlib.crc32(piece if len(piece)>=ODID_MSG_SIZE else payload)&0xFFFFFFFF
                decoded = decode_odid(piece)
                state_update(src_mac, decoded, rssi=rssi, ch=ch,
                             ch_assumed=ch_assumed, pl_sig=sig)
                if DEBUG_MODE:
                    b = decoded.get("basic_id")
                    l = decoded.get("location")
                    if b: _scan(f"  ↳ BasicID: {b}")
                    if l: _scan(f"  ↳ Location: lat={l.get('lat'):.5f} lon={l.get('lon'):.5f} "
                                f"alt={l.get('alt_geodetic'):.1f}m spd={l.get('speed_ms')}")
    except Exception as ex:
        if DEBUG_MODE:
            _scan(f"[ERR] parse_frame: {ex}")

# ─────────────────────────────────────────────────────────────────────────────
# TUI — curses
# ─────────────────────────────────────────────────────────────────────────────

# 列定义：(表头文字, 显示宽度, 字段key)
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
    ("上次",  7, "age_s"),
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
        "sn_s":    (sn[:20]+"…") if len(sn)>21 else sn,
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
    curses.init_pair(2, curses.COLOR_YELLOW, -1)   # 仅 MAC
    curses.init_pair(3, curses.COLOR_WHITE,  -1)   # 离线
    curses.init_pair(4, curses.COLOR_CYAN,   -1)   # 表头
    curses.init_pair(5, curses.COLOR_BLACK,  curses.COLOR_CYAN)  # 标题栏
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
                mode = "scan"       # 第一次按 d：扫描日志
            elif mode == "scan":
                mode = "log"        # 第二次按 d：事件日志
            else:
                mode = "table"      # 第三次按 d：回表格
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

        # ── 标题栏 ──────────────────────────────────────────────────────
        with state_lock:
            n_total = len(state_table)
            n_live  = sum(1 for e in state_table.values()
                         if (now-e["last_seen_ts"]) <= LOST_TIMEOUT)
        ch_s    = f"ch{current_channel}" if current_channel else "ch?"
        dbg_s   = " [DEBUG]" if DEBUG_MODE else ""
        mode_lbl = {"table":"表格","scan":"扫描日志","log":"事件日志"}.get(mode,"?")
        left  = f"  RID Monitor  ●{n_live}在线  ○{n_total-n_live}离线  {ch_s}{dbg_s} "
        right = f" [d]{mode_lbl}→  [↑↓]滚动  [q]退出 "
        bar   = left.ljust(w - _sw(right)) + right
        try: stdscr.addstr(0, 0, _pad(bar, w), C_TITLE)
        except curses.error: pass

        if mode == "table":
            _draw_table(stdscr, h, w, now, C_HEADER, C_ONLINE, C_MACONLY, C_LOST, C_HL)
        elif mode == "scan":
            _draw_buf(stdscr, h, w, scan_buf, log_offset, "扫描日志（所有帧）", "d→事件 d→表格")
        else:
            _draw_buf(stdscr, h, w, log_buf,  log_offset, "事件日志", "d→表格")

        try: stdscr.refresh()
        except curses.error: pass

def _draw_table(stdscr, h, w, now, C_HEADER, C_ONLINE, C_MACONLY, C_LOST, C_HL):
    # 表头
    hdr = ""
    for label, width, _ in COLUMNS:
        hdr += _pad(label, width) + " "
    sep = "─" * min(w, _sw(hdr))
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
            # 该列有未过期的高亮？
            attr  = C_HL if (not r["lost"] and hl.get(key, 0) > now) else base_attr
            try: stdscr.addstr(row_y, col_x, cell, attr)
            except curses.error: pass
            col_x += width + 1
            if col_x >= w: break

        row_y += 1

    hint = f" 共 {len(entries)} 架  刷新≈{TUI_REFRESH:.1f}s "
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
    hint = f" {title} [{start_i+1}–{end_i}/{total}]  ↑↓滚动  {hint_extra} "
    try: stdscr.addstr(h-1, 0, hint[:w].ljust(w), curses.A_DIM)
    except curses.error: pass

# ─────────────────────────────────────────────────────────────────────────────
# 主程序
# ─────────────────────────────────────────────────────────────────────────────
def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="OpenDroneID RID WLAN listener")
    parser.add_argument("--config", default=os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT),
                        help="配置文件路径（默认 rid_config.json）")
    parser.add_argument("--iface",        default=None)
    parser.add_argument("--channel",      default=None, type=int)
    parser.add_argument("--hop",          action="store_true")
    parser.add_argument("--hop-5g",       action="store_true")
    parser.add_argument("--dwell-2g",     default=DWELL_2G_DEFAULT, type=int)
    parser.add_argument("--dwell-5g",     default=DWELL_5G_DEFAULT, type=int)
    parser.add_argument("--settle",       default=SETTLE_DEFAULT,   type=int)
    parser.add_argument("--dwell-on-hit", default=2500, type=int)
    parser.add_argument("--hit-cap",      default=6000, type=int)
    parser.add_argument("--time",         default=DEFAULT_PRINT_INTERVAL, type=float,
                        help="心跳间隔秒（默认 2.0）")
    parser.add_argument("--min-gap",      default=DEFAULT_MIN_GAP, type=float,
                        help="同 SN 最小输出间隔（默认 1.0）")
    parser.add_argument("--rssi-delta",   default=3, type=int)
    parser.add_argument("--change-on-rssi",    action="store_true")
    parser.add_argument("--change-on-payload", action="store_true")
    parser.add_argument("--model-map", default=os.path.join(os.getcwd(),"rid_models.json"))
    parser.add_argument("--history-file", default=os.path.join(os.getcwd(), HISTORY_STORE_DEFAULT),
                        help="历史无人机缓存文件（默认 rid_history_cache.json）")
    parser.add_argument("--no-tui",   action="store_true", help="禁用 TUI，纯文本输出")
    parser.add_argument("--debug",    action="store_true", help="记录所有原始帧到扫描日志")
    parser.add_argument("--notify-test", action="store_true", help="发送一条企业微信测试通知后退出")
    return parser

_BASIC_CFG_ARG_DESTS = {
    "iface", "channel", "hop", "hop_5g",
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
            raise ValueError(f"不允许通过网页传入 {opt}")
    return tokens, raw

def _save_basic_config_from_tokens(tokens: list[str], raw_text: str = "") -> tuple[bool, str]:
    global APP_CONFIG
    if not APP_CONFIG_PATH:
        return False, "配置文件路径为空"
    parser = build_arg_parser()
    try:
        ns = parser.parse_args(tokens)
    except SystemExit:
        return False, "参数不合法"
    explicit = _parser_explicit_dests(parser, tokens)
    cfg = load_app_config(APP_CONFIG_PATH)
    basic = cfg.setdefault("basic", {})
    if not isinstance(basic, dict):
        basic = {}
        cfg["basic"] = basic
    for dest in _BASIC_CFG_ARG_DESTS:
        if dest in explicit:
            basic[dest] = getattr(ns, dest)
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
        return False, "高级重启已禁用"
    py = sys.executable or "python3"
    script = os.path.abspath(sys.argv[0])
    if not os.path.exists(script):
        return False, f"脚本不存在: {script}"
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

    try:
        if hasattr(sys.stdout,"reconfigure"):
            sys.stdout.reconfigure(line_buffering=True)
    except Exception:
        pass

    parser = argparse.ArgumentParser(description="OpenDroneID RID WLAN 监听器")
    parser.add_argument("--config", default=os.path.join(os.getcwd(), CONFIG_FILE_DEFAULT),
                        help="配置文件路径（默认: rid_config.json）")
    parser.add_argument("--iface",        default=None)
    parser.add_argument("--channel",      default=None, type=int)
    parser.add_argument("--hop",          action="store_true")
    parser.add_argument("--hop-5g",       action="store_true")
    parser.add_argument("--dwell-2g",     default=DWELL_2G_DEFAULT, type=int)
    parser.add_argument("--dwell-5g",     default=DWELL_5G_DEFAULT, type=int)
    parser.add_argument("--settle",       default=SETTLE_DEFAULT,   type=int)
    parser.add_argument("--dwell-on-hit", default=2500, type=int)
    parser.add_argument("--hit-cap",      default=6000, type=int)
    parser.add_argument("--time",         default=DEFAULT_PRINT_INTERVAL, type=float,
                        help="心跳间隔秒（默认 2.0）")
    parser.add_argument("--min-gap",      default=DEFAULT_MIN_GAP, type=float,
                        help="同 SN 最小输出间隔（默认 1.0）")
    parser.add_argument("--rssi-delta",   default=3, type=int)
    parser.add_argument("--change-on-rssi",    action="store_true")
    parser.add_argument("--change-on-payload", action="store_true")
    parser.add_argument("--model-map", default=os.path.join(os.getcwd(),"rid_models.json"))
    parser.add_argument("--history-file", default=os.path.join(os.getcwd(), HISTORY_STORE_DEFAULT),
                        help="历史无人机缓存文件（默认: rid_history_cache.json）")
    parser.add_argument("--no-tui",   action="store_true", help="禁用 TUI，纯文本输出")
    parser.add_argument("--debug",    action="store_true", help="记录所有原始帧到扫描日志")
    parser.add_argument("--notify-test", action="store_true", help="发送一条企业微信测试通知后退出")
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
    HISTORY_STORE_PATH = os.path.abspath(str(args.history_file)) if args.history_file else None

    # 把 Python logging 重定向到 scan_buf（而非 stderr，避免被 TUI 吞掉）
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
            _log("[INFO] 企业微信测试通知发送成功")
            if resp:
                _log(f"[INFO] 企业微信返回: {resp}")
        else:
            _log(f"[WARN] 企业微信测试通知发送失败: {resp}")
        return

    if os.geteuid() != 0:
        _log("[WARN] 建议以 root 权限运行 (sudo)")

    iface = interface_detect(prefer=args.iface)

    if args.hop and args.channel:
        _log("[WARN] --hop 与 --channel 同时指定，使用跳频")

    if args.hop:
        dw2    = max(100, args.dwell_2g)
        dw5    = max(200, args.dwell_5g)
        hop_2g = CHANNELS_2G[:]
        hop_5g: list[int] = []
        if args.hop_5g:
            if detect_5g(iface):
                hop_5g = CHANNELS_5G[:]
                _log(f"[INFO] 5G 信道={hop_5g}")
            else:
                _log("[INFO] 5G 不支持，仅 2.4G")
        _log(f"[INFO] 跳频 2.4G={hop_2g}@{dw2}ms" + (f" 5G={hop_5g}@{dw5}ms" if hop_5g else ""))
        Thread(target=channel_hopper,
               args=(iface, hop_2g, hop_5g, dw2, dw5,
                     max(0,args.settle), args.dwell_on_hit, args.hit_cap),
               daemon=True).start()
    elif args.channel:
        _log(f"[INFO] 锁定信道 {args.channel}")
        run_cmd(f"iw dev {iface} set channel {args.channel}")
        current_channel = args.channel
    else:
        # 默认锁定 ch6（DJI RID 常用频道）
        _log("[INFO] 默认锁定信道 6（DJI RID 常用）  --hop 可启用跳频  --channel N 可指定")
        run_cmd(f"iw dev {iface} set channel 6")
        current_channel = 6

    _log(f"[INFO] 输出: 首次立即 / 变化(min-gap={MIN_GAP:.1f}s) / 心跳(time={PRINT_INTERVAL:.1f}s)")
    _log(f"[INFO] LOST 灰色={LOST_TIMEOUT:.0f}s  PURGE={PURGE_TIMEOUT:.0f}s")
    if DEBUG_MODE:
        _log("[INFO] DEBUG 模式: 所有原始帧写入扫描日志（按 d 查看）")

    Thread(target=lost_checker, daemon=True).start()
    Thread(target=http_server_thread, daemon=True).start()
    Thread(target=history_persist_loop, daemon=True).start()
    start_notify_worker()

    def sniff_thread():
        retry_delay = 2.0
        while True:
            try:
                sniff(iface=iface, prn=parse_frame, store=False, monitor=True)
                _log(f"[WARN] sniff 已退出（接口可能短暂掉线），{retry_delay:.0f}s后重试")
            except Exception as ex:
                _log(f"[WARN] sniff异常: {ex}，{retry_delay:.0f}s后重试")
            time.sleep(retry_delay)

    Thread(target=sniff_thread, daemon=True).start()

    if NO_TUI:
        _log("[INFO] --no-tui 模式（Ctrl+C 退出）")
        try:
            while True: time.sleep(1)
        except KeyboardInterrupt:
            _log("[INFO] 已停止")
        finally:
            save_history_store(force=True)
    else:
        try:
            curses.wrapper(tui_main, args)
        except KeyboardInterrupt:
            pass
        finally:
            save_history_store(force=True)
            print("\n[INFO] TUI 已退出，最后 30 条事件日志：")
            with log_lock:
                for line in list(log_buf)[-30:]:
                    print(line)
            if DEBUG_MODE:
                print("\n[INFO] 最后 30 条扫描日志：")
                with log_lock:
                    for line in list(scan_buf)[-30:]:
                        print(line)

if __name__ == "__main__":
    main()
