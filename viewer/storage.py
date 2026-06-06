"""SQLite-backed viewer configuration and auth state."""

from __future__ import annotations

import base64
import hashlib
import hmac
import secrets
import sqlite3
import time
import urllib.parse
from pathlib import Path
from typing import Any


SESSION_TTL_SEC = 12 * 3600


def hash_secret(value: str) -> str:
    salt = secrets.token_bytes(16)
    digest = hashlib.scrypt(value.encode("utf-8"), salt=salt, n=2**14, r=8, p=1, dklen=32)
    return "scrypt$16384$8$1$" + base64.b64encode(salt).decode("ascii") + "$" + base64.b64encode(digest).decode("ascii")


def verify_secret(value: str, encoded: str) -> bool:
    parts = str(encoded or "").strip().split("$")
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


def normalize_base_url(value: str) -> str:
    from urllib.parse import urlparse, urlunparse

    raw = str(value or "").strip()
    if any(ch.isspace() for ch in raw):
        raise ValueError("API address must not contain whitespace")
    if not raw:
        raise ValueError("API 地址必填")
    if "://" not in raw:
        raw = "http://" + raw
    parsed = urlparse(raw)
    try:
        parsed.port
    except ValueError as exc:
        raise ValueError("API address port is invalid") from exc
    if not parsed.hostname:
        raise ValueError("API address must be an http(s) URL")
    if parsed.username or parsed.password:
        raise ValueError("API address must not include user info")
    if parsed.path not in ("", "/") or parsed.params or parsed.query or parsed.fragment:
        raise ValueError("API address must be the URL root only, for example http://host:4600")
    if parsed.scheme not in ("http", "https") or not parsed.netloc:
        raise ValueError("API 地址必须是 http(s) URL")
    return urlunparse((parsed.scheme.lower(), parsed.netloc, "", "", "", ""))


def _float_or_none(value: Any) -> float | None:
    raw = str(value if value is not None else "").strip()
    if not raw or raw.lower() in {"na", "n/a", "none", "null", "-", "--"}:
        return None
    try:
        out = float(raw)
        return out if out == out and out not in (float("inf"), float("-inf")) else None
    except Exception:
        return None


def _int_clamped(value: Any, default: int, low: int, high: int) -> int:
    try:
        out = int(float(str(value).strip()))
    except Exception:
        out = default
    return max(low, min(high, out))


class ConfigStore:
    def __init__(self, path: Path):
        self.path = Path(path)
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
                CREATE TABLE IF NOT EXISTS aggregate_cache (
                    cache_key TEXT PRIMARY KEY,
                    payload TEXT NOT NULL,
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
                raise ValueError("密码长度不足")
            password_hash = hash_secret(password)
        if sso_check:
            if len(sso_check) < 12:
                raise ValueError("Check 码长度不足")
            sso_hash = hash_secret(sso_check)
        if enabled and not password_hash and not (sso_enabled and sso_hash):
            raise ValueError("至少启用一种登录方式")
        if enabled and not sso_enabled and not password_hash:
            raise ValueError("必须保留一种登录方式")
        self.set_setting("auth.enabled", "1" if enabled else "0")
        self.set_setting("auth.username", username)
        self.set_setting("auth.password_hash", password_hash)
        self.set_setting("auth.sso_enabled", "1" if sso_enabled else "0")
        self.set_setting("auth.sso_check_hash", sso_hash)
        return self.public_auth_config()

    def map_config(self) -> dict[str, Any]:
        return {
            "base_name": self.get_setting("map.base_name", "Node Center") or "Node Center",
            "base_lat": _float_or_none(self.get_setting("map.base_lat", "")),
            "base_lon": _float_or_none(self.get_setting("map.base_lon", "")),
            "base_zoom": _int_clamped(self.get_setting("map.base_zoom", "5"), 5, 3, 30),
            "map_auto_center_idle_sec": _int_clamped(self.get_setting("map.auto_center_idle_sec", "20"), 20, 5, 600),
            "heading_ref_deg": _float_or_none(self.get_setting("map.heading_ref_deg", "0")) or 0,
        }

    def aggregate_config(self) -> dict[str, Any]:
        return {
            "cache_ttl_hours": _int_clamped(self.get_setting("aggregate.cache_ttl_hours", "24"), 24, 1, 168),
        }

    def notify_config(self, *, reveal_secret: bool = False) -> dict[str, Any]:
        key = self.get_setting("notify.wecom_key", "")
        return {
            "enabled": self.get_setting("notify.enabled", "0") == "1",
            "wecom_configured": bool(key),
            "wecom_key": key if reveal_secret else "",
            "node_status_enabled": self.get_setting("notify.node_status_enabled", "1") == "1",
        }

    def save_notify_config(self, body: dict[str, Any]) -> dict[str, Any]:
        src = body if isinstance(body, dict) else {}
        current = self.notify_config(reveal_secret=True)
        enabled = bool(src.get("enabled"))
        node_status_enabled = bool(src.get("node_status_enabled", True))
        key = str(src.get("wecom_key") or "").strip() or str(current.get("wecom_key") or "")
        self.set_setting("notify.enabled", "1" if enabled else "0")
        self.set_setting("notify.node_status_enabled", "1" if node_status_enabled else "0")
        self.set_setting("notify.wecom_key", key)
        return self.notify_config(reveal_secret=False)

    def save_aggregate_config(self, body: dict[str, Any]) -> dict[str, Any]:
        src = body if isinstance(body, dict) else {}
        ttl = _int_clamped(src.get("cache_ttl_hours"), 24, 1, 168)
        self.set_setting("aggregate.cache_ttl_hours", str(ttl))
        return self.aggregate_config()

    def get_cache_payload(self, cache_key: str) -> dict[str, Any] | None:
        now = time.time()
        with self.connect() as db:
            row = db.execute(
                "SELECT payload,expires_at FROM aggregate_cache WHERE cache_key=?",
                (str(cache_key),),
            ).fetchone()
            if not row:
                return None
            if float(row["expires_at"] or 0) < now:
                db.execute("DELETE FROM aggregate_cache WHERE cache_key=?", (str(cache_key),))
                return None
            try:
                payload = __import__("json").loads(str(row["payload"] or "{}"))
            except Exception:
                db.execute("DELETE FROM aggregate_cache WHERE cache_key=?", (str(cache_key),))
                return None
        return payload if isinstance(payload, dict) else None

    def set_cache_payload(self, cache_key: str, payload: dict[str, Any], ttl_hours: int | float) -> None:
        import json

        now = time.time()
        ttl_sec = max(60.0, float(ttl_hours) * 3600.0)
        text = json.dumps(payload if isinstance(payload, dict) else {}, ensure_ascii=False, separators=(",", ":"))
        with self.connect() as db:
            db.execute(
                """
                INSERT INTO aggregate_cache(cache_key,payload,created_at,expires_at)
                VALUES(?,?,?,?)
                ON CONFLICT(cache_key) DO UPDATE SET
                    payload=excluded.payload,
                    created_at=excluded.created_at,
                    expires_at=excluded.expires_at
                """,
                (str(cache_key), text, now, now + ttl_sec),
            )

    def clear_cache_payload(self, cache_key: str | None = None) -> int:
        with self.connect() as db:
            if cache_key:
                cur = db.execute("DELETE FROM aggregate_cache WHERE cache_key=?", (str(cache_key),))
            else:
                cur = db.execute("DELETE FROM aggregate_cache")
            return int(cur.rowcount or 0)

    def save_map_config(self, body: dict[str, Any]) -> dict[str, Any]:
        src = body if isinstance(body, dict) else {}
        name = str(src.get("base_name") or "Node Center").strip() or "Node Center"
        lat = _float_or_none(src.get("base_lat"))
        lon = _float_or_none(src.get("base_lon"))
        if lat is not None and not (-90 <= lat <= 90):
            raise ValueError("纬度无效")
        if lon is not None and not (-180 <= lon <= 180):
            raise ValueError("经度无效")
        self.set_setting("map.base_name", name)
        self.set_setting("map.base_lat", "" if lat is None else str(lat))
        self.set_setting("map.base_lon", "" if lon is None else str(lon))
        self.set_setting("map.base_zoom", str(_int_clamped(src.get("base_zoom"), 5, 3, 30)))
        self.set_setting("map.auto_center_idle_sec", str(_int_clamped(src.get("map_auto_center_idle_sec"), 20, 5, 600)))
        heading = _float_or_none(src.get("heading_ref_deg"))
        self.set_setting("map.heading_ref_deg", str(heading if heading is not None else 0))
        return self.map_config()

    def eula_status(self) -> dict[str, Any]:
        return {"ok": True, "accepted": self.get_setting("eula.accepted", "0") == "1", "set_path": str(self.path)}

    def accept_eula(self) -> dict[str, Any]:
        self.set_setting("eula.accepted", "1")
        self.set_setting("eula.accepted_at", str(time.time()))
        return self.eula_status()

    def revoke_eula(self) -> dict[str, Any]:
        self.set_setting("eula.accepted", "0")
        return self.eula_status()

    def create_session(self, subject: str) -> str:
        token = secrets.token_urlsafe(32)
        now = time.time()
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
        now = time.time()
        with self.connect() as db:
            row = db.execute("SELECT subject,expires_at FROM sessions WHERE token=?", (token,)).fetchone()
            if not row or float(row["expires_at"]) < now:
                db.execute("DELETE FROM sessions WHERE token=?", (token,))
                return None
            db.execute("UPDATE sessions SET expires_at=? WHERE token=?", (now + SESSION_TTL_SEC, token))
        return str(row["subject"])

    def delete_session(self, token: str) -> None:
        if token:
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
        base_url = normalize_base_url(str(body.get("base_url") or body.get("url") or ""))
        name = str(body.get("name") or "").strip() or urllib.parse.urlparse(base_url).netloc
        token = str(body.get("token") or "")
        enabled = 1 if body.get("enabled", True) else 0
        now = time.time()
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
