"""Node-center viewer for aggregating station_edition sub-stations."""

from __future__ import annotations

import argparse
import base64
import hashlib
import hmac
import html
import json
import mimetypes
import os
import secrets
import sqlite3
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from http import HTTPStatus
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from socketserver import ThreadingMixIn
from typing import Any


APP_NAME = "Light RID Node Center"
APP_VERSION = "0.1.0"
DEFAULT_HOST = "0.0.0.0"
DEFAULT_PORT = 4700
if getattr(sys, "frozen", False):
    ROOT = Path(getattr(sys, "_MEIPASS", Path(sys.executable).resolve().parent))
    VIEWER_DIR = Path.cwd()
else:
    ROOT = Path(__file__).resolve().parent.parent
    VIEWER_DIR = Path(__file__).resolve().parent
DEFAULT_DB = Path(os.environ.get("LIGHT_RID_VIEWER_DB") or (VIEWER_DIR / "cfg.db"))
ASSETS_DIR = ROOT / "station_edition" / "light_rid" / "assets"
COOKIE_NAME = "rid_node_center_session"
SESSION_TTL_SEC = 12 * 3600
HTTP_TIMEOUT_SEC = 5.0
MAX_JSON_BYTES = 512 * 1024


def _now() -> float:
    return time.time()


def _utc_text(ts: float | None = None) -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(float(ts or _now())))


def _json_dumps(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def _clean_header(value: str) -> str:
    return str(value or "").replace("\r", "").replace("\n", "")


def _hash_secret(value: str) -> str:
    salt = secrets.token_bytes(16)
    digest = hashlib.scrypt(value.encode("utf-8"), salt=salt, n=2**14, r=8, p=1, dklen=32)
    return "scrypt$16384$8$1$" + base64.b64encode(salt).decode("ascii") + "$" + base64.b64encode(digest).decode("ascii")


def _verify_secret(value: str, encoded: str) -> bool:
    raw = str(encoded or "").strip()
    parts = raw.split("$")
    if len(parts) != 6 or parts[0] != "scrypt":
        return False
    try:
        n = int(parts[1])
        r = int(parts[2])
        p = int(parts[3])
        salt = base64.b64decode(parts[4].encode("ascii"), validate=True)
        expected = base64.b64decode(parts[5].encode("ascii"), validate=True)
        digest = hashlib.scrypt(value.encode("utf-8"), salt=salt, n=n, r=r, p=p, dklen=len(expected))
        return hmac.compare_digest(digest, expected)
    except Exception:
        return False


def _normalize_base_url(value: str) -> str:
    raw = str(value or "").strip()
    if not raw:
        raise ValueError("API 地址不能为空")
    if "://" not in raw:
        raw = "http://" + raw
    parsed = urllib.parse.urlparse(raw)
    if parsed.scheme not in ("http", "https") or not parsed.netloc:
        raise ValueError("API 地址必须是 http(s) URL")
    path = parsed.path.rstrip("/")
    return urllib.parse.urlunparse((parsed.scheme, parsed.netloc, path, "", "", ""))


def _safe_float(value: Any) -> float | None:
    try:
        if value in (None, ""):
            return None
        out = float(value)
        if out != out:
            return None
        return out
    except Exception:
        return None


def _station_position_from_snapshot(snapshot: dict[str, Any]) -> dict[str, Any]:
    data = snapshot.get("data") if isinstance(snapshot.get("data"), dict) else snapshot
    meta = data.get("meta") if isinstance(data.get("meta"), dict) else {}
    web = data.get("web") if isinstance(data.get("web"), dict) else {}
    settings = data.get("settings") if isinstance(data.get("settings"), dict) else {}
    settings_web = settings.get("web") if isinstance(settings.get("web"), dict) else {}
    source = {}
    for candidate in (meta, web, settings_web):
        if candidate and (candidate.get("base_lat") is not None or candidate.get("base_lon") is not None):
            source = candidate
            break
    name = str(source.get("base_name") or meta.get("base_name") or web.get("base_name") or "基站").strip() or "基站"
    lat = _safe_float(source.get("base_lat"))
    lon = _safe_float(source.get("base_lon"))
    return {
        "name": name,
        "lat": lat,
        "lon": lon,
        "zoom": _safe_float(source.get("base_zoom")) or 13,
    }


def _rows_from_snapshot(snapshot: dict[str, Any]) -> list[dict[str, Any]]:
    data = snapshot.get("data") if isinstance(snapshot.get("data"), dict) else snapshot
    rows = data.get("drones")
    if isinstance(rows, list):
        return [x for x in rows if isinstance(x, dict)]
    rows = snapshot.get("items")
    if isinstance(rows, list):
        return [x for x in rows if isinstance(x, dict)]
    return []


class ConfigStore:
    def __init__(self, path: Path):
        self.path = path
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._init_db()

    def connect(self) -> sqlite3.Connection:
        conn = sqlite3.connect(str(self.path), timeout=12)
        conn.row_factory = sqlite3.Row
        return conn

    def _init_db(self) -> None:
        with self.connect() as db:
            db.executescript(
                """
                PRAGMA journal_mode=WAL;
                CREATE TABLE IF NOT EXISTS nodes (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    name TEXT NOT NULL,
                    base_url TEXT NOT NULL UNIQUE,
                    token TEXT NOT NULL DEFAULT '',
                    enabled INTEGER NOT NULL DEFAULT 1,
                    created_at REAL NOT NULL,
                    updated_at REAL NOT NULL
                );
                CREATE TABLE IF NOT EXISTS settings (
                    key TEXT PRIMARY KEY,
                    value TEXT NOT NULL
                );
                CREATE TABLE IF NOT EXISTS sessions (
                    token TEXT PRIMARY KEY,
                    subject TEXT NOT NULL,
                    created_at REAL NOT NULL,
                    expires_at REAL NOT NULL
                );
                """
            )

    def get_setting(self, key: str, default: str = "") -> str:
        with self.connect() as db:
            row = db.execute("SELECT value FROM settings WHERE key=?", (key,)).fetchone()
        return str(row["value"]) if row else default

    def set_setting(self, key: str, value: str) -> None:
        with self.connect() as db:
            db.execute(
                "INSERT INTO settings(key,value) VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",
                (key, str(value)),
            )

    def auth_config(self) -> dict[str, Any]:
        return {
            "enabled": self.get_setting("auth.enabled", "0") == "1",
            "username": self.get_setting("auth.username", "admin") or "admin",
            "password_hash": self.get_setting("auth.password_hash", ""),
            "sso_enabled": self.get_setting("auth.sso_enabled", "0") == "1",
            "sso_check_hash": self.get_setting("auth.sso_check_hash", ""),
        }

    def public_auth_config(self) -> dict[str, Any]:
        cfg = self.auth_config()
        return {
            "enabled": bool(cfg["enabled"]),
            "username": cfg["username"],
            "password_configured": bool(cfg["password_hash"]),
            "sso_enabled": bool(cfg["sso_enabled"]),
            "sso_configured": bool(cfg["sso_check_hash"]),
        }

    def save_auth_config(self, body: dict[str, Any]) -> dict[str, Any]:
        current = self.auth_config()
        enabled = bool(body.get("enabled"))
        username = str(body.get("username") or current["username"] or "admin").strip() or "admin"
        password = str(body.get("password") or "")
        sso_enabled = bool(body.get("sso_enabled"))
        sso_check = str(body.get("sso_check") or "")
        password_hash = current["password_hash"]
        sso_hash = current["sso_check_hash"]
        if password:
            if len(password) < 4:
                raise ValueError("密码至少 4 位")
            password_hash = _hash_secret(password)
        if sso_check:
            if len(sso_check) < 12:
                raise ValueError("SSO check 至少 12 位")
            sso_hash = _hash_secret(sso_check)
        if enabled and not password_hash and not (sso_enabled and sso_hash):
            raise ValueError("启用登录前必须至少配置密码登录或 SSO 登录")
        if enabled and sso_enabled is False and not password_hash:
            raise ValueError("不能关闭最后一个可用登录方式")
        self.set_setting("auth.enabled", "1" if enabled else "0")
        self.set_setting("auth.username", username)
        self.set_setting("auth.password_hash", password_hash)
        self.set_setting("auth.sso_enabled", "1" if sso_enabled else "0")
        self.set_setting("auth.sso_check_hash", sso_hash)
        return self.public_auth_config()

    def create_session(self, subject: str) -> str:
        token = secrets.token_urlsafe(32)
        now = _now()
        with self.connect() as db:
            db.execute("DELETE FROM sessions WHERE expires_at < ?", (now,))
            db.execute(
                "INSERT INTO sessions(token,subject,created_at,expires_at) VALUES(?,?,?,?)",
                (token, subject, now, now + SESSION_TTL_SEC),
            )
        return token

    def session_subject(self, token: str) -> str | None:
        if not token:
            return None
        now = _now()
        with self.connect() as db:
            row = db.execute("SELECT subject,expires_at FROM sessions WHERE token=?", (token,)).fetchone()
            if not row or float(row["expires_at"]) < now:
                db.execute("DELETE FROM sessions WHERE token=?", (token,))
                return None
            db.execute("UPDATE sessions SET expires_at=? WHERE token=?", (now + SESSION_TTL_SEC, token))
        return str(row["subject"])

    def delete_session(self, token: str) -> None:
        if not token:
            return
        with self.connect() as db:
            db.execute("DELETE FROM sessions WHERE token=?", (token,))

    def list_nodes(self, reveal_token: bool = False) -> list[dict[str, Any]]:
        with self.connect() as db:
            rows = db.execute("SELECT * FROM nodes ORDER BY id ASC").fetchall()
        out = []
        for row in rows:
            token = str(row["token"] or "")
            out.append(
                {
                    "id": int(row["id"]),
                    "name": str(row["name"] or ""),
                    "base_url": str(row["base_url"] or ""),
                    "enabled": bool(row["enabled"]),
                    "token": token if reveal_token else "",
                    "token_configured": bool(token),
                    "created_at": float(row["created_at"]),
                    "updated_at": float(row["updated_at"]),
                }
            )
        return out

    def upsert_node(self, body: dict[str, Any]) -> dict[str, Any]:
        node_id = int(body.get("id") or 0)
        base_url = _normalize_base_url(str(body.get("base_url") or body.get("url") or ""))
        name = str(body.get("name") or "").strip() or urllib.parse.urlparse(base_url).netloc
        token = str(body.get("token") or "")
        enabled = 1 if body.get("enabled", True) else 0
        now = _now()
        with self.connect() as db:
            if node_id:
                old = db.execute("SELECT token FROM nodes WHERE id=?", (node_id,)).fetchone()
                if not old:
                    raise ValueError("节点不存在")
                if token == "" and not bool(body.get("clear_token")):
                    token = str(old["token"] or "")
                db.execute(
                    "UPDATE nodes SET name=?,base_url=?,token=?,enabled=?,updated_at=? WHERE id=?",
                    (name, base_url, token, enabled, now, node_id),
                )
            else:
                db.execute(
                    """
                    INSERT INTO nodes(name,base_url,token,enabled,created_at,updated_at)
                    VALUES(?,?,?,?,?,?)
                    ON CONFLICT(base_url) DO UPDATE SET
                        name=excluded.name,
                        token=excluded.token,
                        enabled=excluded.enabled,
                        updated_at=excluded.updated_at
                    """,
                    (name, base_url, token, enabled, now, now),
                )
        for item in self.list_nodes():
            if item["base_url"] == base_url:
                return item
        raise RuntimeError("节点保存后读取失败")

    def delete_node(self, node_id: int) -> bool:
        with self.connect() as db:
            cur = db.execute("DELETE FROM nodes WHERE id=?", (int(node_id),))
            return cur.rowcount > 0


def _fetch_json(base_url: str, token: str, path: str) -> tuple[dict[str, Any] | None, str | None, int | None]:
    url = base_url.rstrip("/") + path
    headers = {
        "Accept": "application/json",
        "User-Agent": f"{APP_NAME}/{APP_VERSION}",
    }
    if token:
        headers["X-API-Token"] = token
        headers["Authorization"] = "Bearer " + token
    req = urllib.request.Request(url, headers=headers, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=HTTP_TIMEOUT_SEC) as resp:
            raw = resp.read(MAX_JSON_BYTES + 1)
            if len(raw) > MAX_JSON_BYTES:
                return None, "response too large", int(resp.status)
            return json.loads(raw.decode("utf-8", "replace")), None, int(resp.status)
    except urllib.error.HTTPError as exc:
        msg = exc.read(8192).decode("utf-8", "replace")
        return None, msg or exc.reason, int(exc.code)
    except Exception as exc:
        return None, str(exc), None


def fetch_node_live(node: dict[str, Any]) -> dict[str, Any]:
    started = _now()
    base_url = str(node.get("base_url") or "")
    token = str(node.get("token") or "")
    health, health_err, health_code = _fetch_json(base_url, token, "/api/health")
    snapshot, snap_err, snap_code = _fetch_json(base_url, token, "/api/v1/snapshot")
    drones = _rows_from_snapshot(snapshot or {})
    if not drones:
        drones_payload, drones_err, drones_code = _fetch_json(base_url, token, "/api/v1/drones")
        if drones_payload and isinstance(drones_payload.get("items"), list):
            drones = [x for x in drones_payload["items"] if isinstance(x, dict)]
        elif not snap_err:
            snap_err = drones_err
            snap_code = drones_code
    station = _station_position_from_snapshot(snapshot or {})
    ok = bool((health or {}).get("ok", health is not None)) and snapshot is not None
    service = (health or {}).get("service") if isinstance((health or {}).get("service"), dict) else {}
    enriched = []
    for item in drones:
        row = dict(item)
        row["_node_id"] = node["id"]
        row["_node_name"] = node["name"]
        row["_node_url"] = base_url
        enriched.append(row)
    return {
        "id": node["id"],
        "name": node["name"],
        "base_url": base_url,
        "enabled": bool(node.get("enabled")),
        "ok": ok,
        "error": None if ok else (snap_err or health_err or "request failed"),
        "status_code": snap_code or health_code,
        "latency_ms": int((_now() - started) * 1000),
        "station": station,
        "service": service,
        "drones": enriched,
        "count": len(enriched),
        "online_count": len([x for x in enriched if not bool(x.get("lost")) and not bool(x.get("archived"))]),
        "fetched_at": _now(),
    }


def fetch_node_track(node: dict[str, Any], sn: str) -> dict[str, Any]:
    encoded_sn = urllib.parse.quote(str(sn or "").strip(), safe="")
    if not encoded_sn:
        raise ValueError("sn required")
    payload, err, code = _fetch_json(str(node.get("base_url") or ""), str(node.get("token") or ""), f"/api/v1/tracks/{encoded_sn}")
    if payload is None:
        return {
            "ok": False,
            "error": err or "request failed",
            "status_code": code,
            "track": [],
        }
    track = payload.get("track")
    if track is None:
        track = payload.get("items")
    if not isinstance(track, list):
        track = []
    return {
        "ok": True,
        "status_code": code,
        "track": [x for x in track if isinstance(x, dict)],
        "count": len(track),
    }


def aggregate_nodes(store: ConfigStore) -> dict[str, Any]:
    nodes = store.list_nodes(reveal_token=True)
    live_nodes = []
    drones = []
    for node in nodes:
        if not bool(node.get("enabled")):
            live_nodes.append(
                {
                    "id": node["id"],
                    "name": node["name"],
                    "base_url": node["base_url"],
                    "enabled": False,
                    "ok": False,
                    "error": "disabled",
                    "station": {"name": node["name"], "lat": None, "lon": None, "zoom": 13},
                    "service": {},
                    "drones": [],
                    "count": 0,
                    "online_count": 0,
                    "fetched_at": _now(),
                }
            )
            continue
        live = fetch_node_live(node)
        live_nodes.append(live)
        drones.extend(live.get("drones") or [])
    return {
        "ok": True,
        "version": APP_VERSION,
        "fetched_at": _now(),
        "nodes": [{k: v for k, v in n.items() if k != "drones"} for n in live_nodes],
        "drones": drones,
        "node_count": len(live_nodes),
        "online_node_count": len([n for n in live_nodes if n.get("ok")]),
        "drone_count": len(drones),
        "online_drone_count": len([x for x in drones if not bool(x.get("lost")) and not bool(x.get("archived"))]),
    }


def build_page() -> str:
    return """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Light RID Node Center</title>
<link rel="stylesheet" href="/assets/leaflet/leaflet.css">
<script src="/assets/leaflet/leaflet.js"></script>
<style>
*{box-sizing:border-box}html,body{height:100%;margin:0}
:root{--font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;--font-mono:"Cascadia Mono","Consolas",monospace;--bg:#201f1e;--bg2:#252423;--panel:#2b2a29;--panel2:#252423;--border:#3b3a39;--txt:#f3f2f1;--dim:#c8c6c4;--blue:#2899f5;--green:#92c353;--yellow:#ffb900;--red:#ff7b72;--soft:rgba(255,255,255,.035)}
body{height:100dvh;display:grid;grid-template-rows:auto minmax(0,1fr);background:linear-gradient(180deg,var(--bg),var(--bg2) 22%,var(--bg));color:var(--txt);font-family:var(--font-ui);overflow:hidden}
header{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:14px;align-items:center;padding:10px 14px;border-bottom:1px solid var(--border);background:var(--panel)}
h1{font-size:20px;line-height:1;margin:0;font-weight:650}.sub{color:var(--dim);font-size:13px}.stats{display:flex;gap:14px;justify-content:end;flex-wrap:wrap}.stat{color:var(--dim);font-size:13px}.stat b{color:var(--green);font-family:var(--font-mono)}
.shell{display:grid;grid-template-columns:minmax(330px,420px) minmax(0,1fr);gap:12px;min-height:0;padding:12px}
.side,.main{min-height:0;display:grid;gap:12px}.side{grid-template-rows:auto minmax(0,1fr)}.main{grid-template-rows:minmax(0,1fr) minmax(220px,34vh)}
.panel{min-height:0;border:1px solid var(--border);border-radius:4px;background:var(--panel);overflow:hidden;box-shadow:0 1px 3px rgba(0,0,0,.1)}
.panel-hd{display:flex;align-items:center;justify-content:space-between;gap:8px;padding:10px 12px;border-bottom:1px solid var(--border);background:var(--panel2)}
.panel-title{font-size:14px;font-weight:650}.actions{display:flex;gap:8px;align-items:center;flex-wrap:wrap}
button,.btn{border:1px solid var(--border);border-radius:4px;background:var(--panel2);color:var(--txt);height:34px;padding:0 10px;font:650 13px/1 var(--font-ui);cursor:pointer}button:hover{border-color:var(--blue);background:color-mix(in srgb,var(--blue) 10%,var(--panel2))}button.primary{border-color:color-mix(in srgb,var(--blue) 70%,var(--border));background:color-mix(in srgb,var(--blue) 18%,var(--panel2))}button.warn{border-color:color-mix(in srgb,var(--red) 50%,var(--border));color:#ffd8d8}
input{width:100%;height:36px;border:1px solid var(--border);border-radius:4px;background:var(--panel2);color:var(--txt);padding:8px 9px;font:13px/1 var(--font-ui)}
label{display:grid;gap:5px;color:var(--dim);font-size:12px}.form{display:grid;gap:9px;padding:12px}.twocol{display:grid;grid-template-columns:1fr 1fr;gap:8px}.note{color:var(--dim);font-size:12px;line-height:1.4}.status{color:var(--dim);font-size:12px;word-break:break-word}.status.err{color:var(--red)}
.node-list{overflow:auto}.node{display:grid;gap:7px;padding:10px 12px;border-bottom:1px solid color-mix(in srgb,var(--border) 70%,transparent)}.node.off{opacity:.62}.node-top{display:flex;align-items:center;justify-content:space-between;gap:8px}.node-name{font-weight:650;overflow:hidden;text-overflow:ellipsis}.pill{border:1px solid var(--border);border-radius:999px;padding:3px 8px;color:var(--dim);font:12px/1 var(--font-mono)}.pill.ok{color:var(--green);border-color:color-mix(in srgb,var(--green) 45%,var(--border))}.pill.err{color:var(--red);border-color:color-mix(in srgb,var(--red) 45%,var(--border))}
#map{width:100%;height:100%;min-height:0}.offline-map-tile{background:#232b35;border:1px solid rgba(255,255,255,.08);color:#6f7d8c;font:12px var(--font-mono);display:flex;align-items:center;justify-content:center}.station-pin{border:2px solid #fff;background:var(--blue);width:18px;height:18px;border-radius:50%;box-shadow:0 0 0 5px rgba(40,153,245,.18)}.drone-pin{width:22px;height:22px;border-radius:50%;background:var(--green);border:2px solid #fff;box-shadow:0 3px 10px rgba(0,0,0,.3)}.drone-pin.lost{background:var(--dim)}
.table-wrap{overflow:auto}table{width:100%;border-collapse:collapse;min-width:900px}th,td{padding:8px 10px;border-bottom:1px solid color-mix(in srgb,var(--border) 72%,transparent);text-align:left;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}th{position:sticky;top:0;background:var(--panel2);color:var(--dim);font-size:12px;z-index:1}td{font-size:13px}.mono{font-family:var(--font-mono)}
.login{max-width:430px;margin:12vh auto 0;border:1px solid var(--border);border-radius:4px;background:var(--panel);padding:18px;display:grid;gap:12px}.hidden{display:none!important}
@media(max-width:900px){body{overflow:auto}.shell{grid-template-columns:1fr;grid-auto-rows:auto;height:auto}.main{grid-template-rows:420px auto}.side{grid-template-rows:auto auto}.node-list{max-height:360px}}
</style></head><body>
<section id="login-box" class="login hidden">
  <h1>Light RID Node Center</h1>
  <div class="sub">节点中心登录</div>
  <label>账号<input id="login-user" autocomplete="username" value="admin"></label>
  <label>密码<input id="login-pass" type="password" autocomplete="current-password"></label>
  <button id="btn-login" class="primary" type="button">登录</button>
  <div id="login-status" class="status"></div>
</section>
<section id="app-box" class="hidden">
<header>
  <div><h1>Light RID Node Center</h1><div class="sub">4700 节点聚合视图</div></div>
  <div class="stats">
    <span class="stat">节点 <b id="stat-nodes">0/0</b></span>
    <span class="stat">飞机 <b id="stat-drones">0/0</b></span>
    <span class="stat">刷新 <b id="stat-time">-</b></span>
  </div>
  <div class="actions"><button id="btn-settings" type="button">设置</button><button id="btn-logout" type="button">退出</button></div>
</header>
<main class="shell">
  <section class="side">
    <div class="panel">
      <div class="panel-hd"><div class="panel-title">节点管理器</div><button id="btn-add" class="primary" type="button">保存节点</button></div>
      <div class="form">
        <input id="node-id" type="hidden">
        <label>名称<input id="node-name" placeholder="例如 东门基站"></label>
        <label>API 地址<input id="node-url" placeholder="http://192.168.1.10:4600"></label>
        <label>Token<input id="node-token" type="password" placeholder="留空表示编辑时保留原 Token"></label>
        <div class="twocol"><button id="btn-test" type="button">测试</button><button id="btn-clear-form" type="button">清空</button></div>
        <div class="note">只保存 API 地址和 Token。节点信息、飞机列表和基站坐标每次刷新都从远端 API 实时读取。</div>
        <div id="node-status" class="status"></div>
      </div>
    </div>
    <div class="panel">
      <div class="panel-hd"><div class="panel-title">已添加基站</div><button id="btn-refresh" type="button">刷新</button></div>
      <div id="node-list" class="node-list"></div>
    </div>
  </section>
  <section class="main">
    <div class="panel"><div id="map"></div></div>
    <div class="panel table-wrap">
      <table><thead><tr><th>节点</th><th>状态</th><th>SN / MAC</th><th>型号</th><th>纬度</th><th>经度</th><th>高度</th><th>距离</th><th>时间</th></tr></thead><tbody id="drone-body"></tbody></table>
    </div>
  </section>
</main>
</section>
<section id="settings-box" class="login hidden">
  <h1>设置</h1>
  <div class="sub">仅保留密码登录和 SSO 登录。此页面不包含 API / 负载 / AP / 基站信息 / Passkey 设置。</div>
  <label><span><input id="auth-enabled" type="checkbox"> 启用登录保护</span></label>
  <label>登录账号<input id="auth-user" value="admin"></label>
  <label>新密码<input id="auth-pass" type="password" placeholder="留空不修改"></label>
  <label><span><input id="sso-enabled" type="checkbox"> 启用 SSO check 登录</span></label>
  <label>SSO check 密钥<input id="sso-check" type="password" placeholder="留空不修改，至少 12 位"></label>
  <div class="twocol"><button id="btn-save-settings" class="primary" type="button">保存设置</button><button id="btn-back" type="button">返回</button></div>
  <div id="settings-status" class="status"></div>
</section>
<script>
const $ = (id) => document.getElementById(id);
let map, stationLayer, droneLayer, latestNodes = [], latestDrones = [];
function headers(extra){ const h={'X-LightRID-Page':'1'}; if(extra) Object.assign(h, extra); return h; }
async function api(path, opts){
  const r = await fetch(path, Object.assign({cache:'no-store', headers:headers()}, opts||{}));
  const d = await r.json().catch(()=>({}));
  if(r.status === 401){ showLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok === false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
function showLogin(){ $('login-box').classList.remove('hidden'); $('app-box').classList.add('hidden'); $('settings-box').classList.add('hidden'); }
function showApp(){ $('login-box').classList.add('hidden'); $('app-box').classList.remove('hidden'); $('settings-box').classList.add('hidden'); setTimeout(()=>{ if(map) map.invalidateSize(false); }, 0); }
function showSettings(){ $('login-box').classList.add('hidden'); $('app-box').classList.add('hidden'); $('settings-box').classList.remove('hidden'); loadSettings(); }
function esc(v){ return String(v==null?'':v).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c])); }
function num(v){ const n=Number(v); return Number.isFinite(n)?n:null; }
function fmt(v, digits){ const n=num(v); return n==null?'-':n.toFixed(digits); }
function initMap(){
  if(map) return;
  map = L.map('map', {zoomControl:true}).setView([35, 105], 4);
  const Grid = L.GridLayer.extend({createTile:function(coords){ const tile=L.DomUtil.create('div','offline-map-tile'); tile.innerHTML='RID<br>'+coords.z+'/'+coords.x+'/'+coords.y; return tile; }});
  new Grid({tileSize:256}).addTo(map);
  stationLayer = L.layerGroup().addTo(map);
  droneLayer = L.layerGroup().addTo(map);
}
function renderMap(nodes, drones){
  initMap(); stationLayer.clearLayers(); droneLayer.clearLayers();
  const bounds = [];
  nodes.forEach(n => {
    const st = n.station || {}; const lat=num(st.lat), lon=num(st.lon);
    if(lat==null || lon==null) return;
    const icon = L.divIcon({className:'', html:'<div class="station-pin"></div>', iconSize:[18,18], iconAnchor:[9,9]});
    L.marker([lat, lon], {icon}).bindPopup('<b>'+esc(n.name)+'</b><br>'+esc(n.base_url)+'<br>飞机 '+esc(n.count||0)).addTo(stationLayer);
    bounds.push([lat, lon]);
  });
  drones.forEach(d => {
    const lat=num(d.lat), lon=num(d.lon);
    if(lat==null || lon==null) return;
    const lost=!!d.lost || !!d.archived;
    const icon = L.divIcon({className:'', html:'<div class="drone-pin '+(lost?'lost':'')+'"></div>', iconSize:[22,22], iconAnchor:[11,11]});
    const sn = d.sn || d.mac || '-';
    L.marker([lat, lon], {icon}).bindPopup('<b>'+esc(sn)+'</b><br>'+esc(d._node_name||'-')+'<br>'+fmt(lat,6)+', '+fmt(lon,6)).addTo(droneLayer);
    bounds.push([lat, lon]);
  });
  if(bounds.length) map.fitBounds(bounds, {padding:[36,36], maxZoom:15});
}
function renderNodes(nodes){
  $('node-list').innerHTML = nodes.length ? nodes.map(n => '<div class="node '+(n.ok?'':'off')+'">'+
    '<div class="node-top"><div class="node-name">'+esc(n.name)+'</div><span class="pill '+(n.ok?'ok':'err')+'">'+(n.ok?'在线':'离线')+'</span></div>'+
    '<div class="sub">'+esc(n.base_url)+'</div>'+
    '<div class="sub">飞机 '+esc(n.online_count||0)+'/'+esc(n.count||0)+' · '+(n.station&&n.station.lat!=null?fmt(n.station.lat,5)+','+fmt(n.station.lon,5):'无基站坐标')+'</div>'+
    '<div class="actions"><button data-edit="'+n.id+'">编辑</button><button class="warn" data-del="'+n.id+'">删除</button></div>'+
    (n.error?'<div class="status err">'+esc(n.error).slice(0,160)+'</div>':'')+'</div>').join('') : '<div class="node"><div class="sub">尚未添加节点。</div></div>';
}
function renderDrones(rows){
  $('drone-body').innerHTML = rows.length ? rows.map(d => '<tr><td>'+esc(d._node_name)+'</td><td>'+(d.lost?'离线':'在线')+'</td><td class="mono">'+esc(d.sn||d.mac||'-')+'</td><td>'+esc(d.model||d.model_name||'-')+'</td><td>'+fmt(d.lat,6)+'</td><td>'+fmt(d.lon,6)+'</td><td>'+fmt(d.height_m||d.alt_m||d.altitude_m||d.alt,1)+'</td><td>'+fmt(d.distance_m,1)+'</td><td>'+esc(d.last_seen_text||d.last_seen||d.ts_text||d.updated_at||'-')+'</td></tr>').join('') : '<tr><td colspan="9" class="sub">暂无远端飞机数据。</td></tr>';
}
async function refreshAll(){
  const d = await api('/api/aggregate');
  latestNodes = d.nodes || []; latestDrones = d.drones || [];
  $('stat-nodes').textContent = String(d.online_node_count||0)+'/'+String(d.node_count||0);
  $('stat-drones').textContent = String(d.online_drone_count||0)+'/'+String(d.drone_count||0);
  $('stat-time').textContent = new Date().toLocaleTimeString();
  renderNodes(latestNodes); renderDrones(latestDrones); renderMap(latestNodes, latestDrones);
}
function clearForm(){ $('node-id').value=''; $('node-name').value=''; $('node-url').value=''; $('node-token').value=''; $('node-status').textContent=''; }
async function loadNodeRecords(){
  const d = await api('/api/nodes');
  return d.items || [];
}
async function saveNode(testOnly){
  const body = {id:Number($('node-id').value||0), name:$('node-name').value, base_url:$('node-url').value, token:$('node-token').value, enabled:true};
  $('node-status').classList.remove('err'); $('node-status').textContent = testOnly ? '正在测试...' : '正在保存...';
  const d = await api(testOnly?'/api/nodes/test':'/api/nodes', {method:'POST', headers:headers({'Content-Type':'application/json'}), body:JSON.stringify(body)});
  $('node-status').textContent = testOnly ? ('测试完成：'+((d.node&&d.node.ok)?'在线':'离线')+(d.node&&d.node.error?' · '+d.node.error:'')) : '已保存';
  if(!testOnly){ clearForm(); await refreshAll(); }
}
async function loadSettings(){
  const d = await api('/api/settings');
  const a = d.auth || {};
  $('auth-enabled').checked = !!a.enabled; $('auth-user').value = a.username || 'admin'; $('sso-enabled').checked = !!a.sso_enabled;
  $('settings-status').textContent = '密码 '+(a.password_configured?'已配置':'未配置')+' · SSO '+(a.sso_configured?'已配置':'未配置');
}
async function saveSettings(){
  const body = {enabled:$('auth-enabled').checked, username:$('auth-user').value, password:$('auth-pass').value, sso_enabled:$('sso-enabled').checked, sso_check:$('sso-check').value};
  const d = await api('/api/settings/auth', {method:'POST', headers:headers({'Content-Type':'application/json'}), body:JSON.stringify(body)});
  $('auth-pass').value=''; $('sso-check').value='';
  $('settings-status').textContent = '已保存。密码 '+(d.auth.password_configured?'已配置':'未配置')+' · SSO '+(d.auth.sso_configured?'已配置':'未配置');
}
$('btn-login').onclick = async () => {
  try{ await api('/api/login', {method:'POST', headers:headers({'Content-Type':'application/json'}), body:JSON.stringify({username:$('login-user').value,password:$('login-pass').value})}); showApp(); initMap(); await refreshAll(); }
  catch(e){ $('login-status').textContent=e.message||String(e); $('login-status').classList.add('err'); }
};
$('btn-logout').onclick = async () => { await api('/api/logout', {method:'POST'}).catch(()=>{}); showLogin(); };
$('btn-refresh').onclick = () => refreshAll().catch(e => alert(e.message||String(e)));
$('btn-add').onclick = () => saveNode(false).catch(e => { $('node-status').textContent=e.message||String(e); $('node-status').classList.add('err'); });
$('btn-test').onclick = () => saveNode(true).catch(e => { $('node-status').textContent=e.message||String(e); $('node-status').classList.add('err'); });
$('btn-clear-form').onclick = clearForm;
$('btn-settings').onclick = showSettings; $('btn-back').onclick = () => { showApp(); refreshAll().catch(()=>{}); };
$('btn-save-settings').onclick = () => saveSettings().catch(e => { $('settings-status').textContent=e.message||String(e); $('settings-status').classList.add('err'); });
$('node-list').onclick = async ev => {
  const del = ev.target.closest('[data-del]'); const edit = ev.target.closest('[data-edit]');
  if(del){ if(!confirm('删除该节点？')) return; await api('/api/nodes/delete',{method:'POST',headers:headers({'Content-Type':'application/json'}),body:JSON.stringify({id:Number(del.dataset.del)})}); await refreshAll(); return; }
  if(edit){ const rows = await loadNodeRecords(); const n = rows.find(x => Number(x.id)===Number(edit.dataset.edit)); if(!n) return; $('node-id').value=n.id; $('node-name').value=n.name; $('node-url').value=n.base_url; $('node-token').value=''; $('node-status').textContent='编辑模式：Token 留空会保留原值。'; }
};
(async function boot(){
  const d = await fetch('/api/session', {cache:'no-store', headers:headers()}).then(r=>r.json()).catch(()=>({ok:false}));
  if(d.auth_enabled && !d.authenticated){ showLogin(); return; }
  showApp(); initMap(); refreshAll().catch(e => { $('node-list').innerHTML='<div class="node"><div class="status err">'+esc(e.message||String(e))+'</div></div>'; });
  setInterval(()=>refreshAll().catch(()=>{}), 5000);
})();
</script></body></html>"""


def build_login_redirect_page(target: str) -> str:
    safe_target = html.escape(target or "/", quote=True)
    return f"""<!doctype html><html><head><meta charset="utf-8"><meta http-equiv="refresh" content="0;url={safe_target}"><title>{APP_NAME}</title></head><body><a href="{safe_target}">继续</a></body></html>"""


class ThreadingHTTPServer(ThreadingMixIn, HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


class ViewerHandler(BaseHTTPRequestHandler):
    server_version = "LightRIDNodeCenter/" + APP_VERSION
    sys_version = ""
    store: ConfigStore

    def log_message(self, fmt: str, *args: Any) -> None:
        print(f"[{_utc_text()}] {self.address_string()} {fmt % args}")

    def end_headers(self) -> None:
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
        super().end_headers()

    def _cookie_token(self) -> str:
        raw = self.headers.get("Cookie", "")
        try:
            cookie = SimpleCookie(raw)
            return str(cookie.get(COOKIE_NAME).value if cookie.get(COOKIE_NAME) else "")
        except Exception:
            return ""

    def _subject(self) -> str | None:
        cfg = self.store.auth_config()
        if not cfg["enabled"]:
            return "local"
        return self.store.session_subject(self._cookie_token())

    def _send_json(self, payload: dict[str, Any], status: int = 200) -> None:
        body = _json_dumps(payload)
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _send_html(self, text: str, status: int = 200) -> None:
        body = text.encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "text/html; charset=utf-8")
        self.send_header("Cache-Control", "no-store")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _read_json(self) -> dict[str, Any]:
        try:
            size = int(self.headers.get("Content-Length") or "0")
        except Exception:
            size = 0
        if size > MAX_JSON_BYTES:
            raise ValueError("request too large")
        if size <= 0:
            return {}
        raw = self.rfile.read(size)
        data = json.loads(raw.decode("utf-8"))
        if not isinstance(data, dict):
            raise ValueError("JSON body must be object")
        return data

    def _require_auth(self) -> bool:
        if self._subject():
            return True
        self._send_json({"ok": False, "error": "login required", "auth_expired": True}, 401)
        return False

    def _serve_asset(self, path: str) -> None:
        rel = urllib.parse.unquote(path[len("/assets/") :]).replace("\\", "/")
        parts = [x for x in rel.split("/") if x and x not in (".", "..")]
        if not parts or "/".join(parts) != rel:
            self._send_json({"ok": False, "error": "invalid asset path"}, 400)
            return
        full = (ASSETS_DIR / Path(*parts)).resolve()
        base = ASSETS_DIR.resolve()
        if not str(full).startswith(str(base)) or not full.is_file():
            self.send_response(404)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        ctype = mimetypes.guess_type(str(full))[0] or "application/octet-stream"
        body = full.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Cache-Control", "public, max-age=86400")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query or "")
        if path.startswith("/assets/"):
            self._serve_asset(path)
            return
        if path in ("/", "/index.html", "/settings"):
            if path == "/" and query.get("check"):
                cfg = self.store.auth_config()
                check = str((query.get("check") or [""])[0])
                if cfg["enabled"] and cfg["sso_enabled"] and cfg["sso_check_hash"] and _verify_secret(check, cfg["sso_check_hash"]):
                    token = self.store.create_session("sso")
                    self.send_response(302)
                    self.send_header("Location", "/")
                    self.send_header("Set-Cookie", _clean_header(f"{COOKIE_NAME}={token}; Max-Age={SESSION_TTL_SEC}; Path=/; HttpOnly; SameSite=Lax"))
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
            self._send_html(build_page())
            return
        if path == "/api/session":
            cfg = self.store.auth_config()
            subject = self._subject()
            self._send_json({"ok": True, "auth_enabled": bool(cfg["enabled"]), "authenticated": bool(subject), "subject": subject or ""})
            return
        if path == "/api/settings":
            if not self._require_auth():
                return
            self._send_json({"ok": True, "auth": self.store.public_auth_config()})
            return
        if path == "/api/nodes":
            if not self._require_auth():
                return
            self._send_json({"ok": True, "items": self.store.list_nodes(reveal_token=False)})
            return
        if path == "/api/aggregate":
            if not self._require_auth():
                return
            self._send_json(aggregate_nodes(self.store))
            return
        if path == "/api/tracks/get":
            if not self._require_auth():
                return
            try:
                node_id = int((query.get("node_id") or ["0"])[0] or "0")
                sn = str((query.get("sn") or [""])[0] or "").strip()
                node = None
                for item in self.store.list_nodes(reveal_token=True):
                    if int(item.get("id") or 0) == node_id:
                        node = item
                        break
                if not node:
                    self._send_json({"ok": False, "error": "node not found"}, 404)
                    return
                payload = fetch_node_track(node, sn)
                self._send_json(payload, 200 if payload.get("ok") else 502)
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc)}, 400)
            return
        self._send_json({"ok": False, "error": "not found"}, 404)

    def do_POST(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        try:
            body = self._read_json()
        except Exception as exc:
            self._send_json({"ok": False, "error": str(exc)}, 400)
            return
        if path == "/api/login":
            cfg = self.store.auth_config()
            if not cfg["enabled"]:
                token = self.store.create_session("local")
                self.send_response(200)
                self.send_header("Content-Type", "application/json; charset=utf-8")
                self.send_header("Set-Cookie", _clean_header(f"{COOKIE_NAME}={token}; Max-Age={SESSION_TTL_SEC}; Path=/; HttpOnly; SameSite=Lax"))
                payload = _json_dumps({"ok": True, "subject": "local"})
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
                return
            username = str(body.get("username") or "")
            password = str(body.get("password") or "")
            if username == cfg["username"] and cfg["password_hash"] and _verify_secret(password, cfg["password_hash"]):
                token = self.store.create_session(username)
                self.send_response(200)
                self.send_header("Content-Type", "application/json; charset=utf-8")
                self.send_header("Set-Cookie", _clean_header(f"{COOKIE_NAME}={token}; Max-Age={SESSION_TTL_SEC}; Path=/; HttpOnly; SameSite=Lax"))
                payload = _json_dumps({"ok": True, "subject": username})
                self.send_header("Content-Length", str(len(payload)))
                self.end_headers()
                self.wfile.write(payload)
                return
            self._send_json({"ok": False, "error": "账号或密码错误"}, 401)
            return
        if path == "/api/logout":
            self.store.delete_session(self._cookie_token())
            self.send_response(200)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Set-Cookie", _clean_header(f"{COOKIE_NAME}=; Max-Age=0; Path=/; HttpOnly; SameSite=Lax"))
            payload = _json_dumps({"ok": True})
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if not self._require_auth():
            return
        try:
            if path == "/api/settings/auth":
                self._send_json({"ok": True, "auth": self.store.save_auth_config(body)})
                return
            if path == "/api/nodes":
                self._send_json({"ok": True, "item": self.store.upsert_node(body)})
                return
            if path == "/api/nodes/test":
                node = {
                    "id": int(body.get("id") or 0),
                    "name": str(body.get("name") or "测试节点").strip() or "测试节点",
                    "base_url": _normalize_base_url(str(body.get("base_url") or body.get("url") or "")),
                    "token": str(body.get("token") or ""),
                    "enabled": True,
                }
                self._send_json({"ok": True, "node": fetch_node_live(node)})
                return
            if path == "/api/nodes/delete":
                self._send_json({"ok": True, "deleted": self.store.delete_node(int(body.get("id") or 0))})
                return
        except Exception as exc:
            self._send_json({"ok": False, "error": str(exc)}, 400)
            return
        self._send_json({"ok": False, "error": "not found"}, 404)


def run(host: str, port: int, db_path: Path) -> None:
    store = ConfigStore(db_path)
    ViewerHandler.store = store
    httpd = ThreadingHTTPServer((host, port), ViewerHandler)
    print(f"[INFO] {APP_NAME} listening on http://{host}:{port}/ using {db_path}")
    try:
        httpd.serve_forever()
    except KeyboardInterrupt:
        print("\n[INFO] stopped")
    finally:
        httpd.server_close()


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(description="Light RID node-center viewer")
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--port", type=int, default=DEFAULT_PORT)
    parser.add_argument("--db", default=str(DEFAULT_DB), help="SQLite config DB path")
    args = parser.parse_args(argv)
    run(str(args.host), int(args.port), Path(args.db).resolve())


if __name__ == "__main__":
    main()
