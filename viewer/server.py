"""HTTP entrypoint for the standalone Light RID node-center viewer."""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import mimetypes
import os
import platform
import struct
import sys
import time
import urllib.parse
from http.cookies import SimpleCookie
from http.server import BaseHTTPRequestHandler, HTTPServer
from pathlib import Path
from socketserver import ThreadingMixIn
from typing import Any


if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from viewer.aggregation import (
    aggregate_nodes,
    create_node_sso_url,
    fetch_node_metrics,
    fetch_node_track,
    run_node_operation,
    test_node_communication,
    viewer_state_snapshot,
)
from viewer.nodes_ui import build_nodes_page
from viewer.paths import APP_NAME, APP_VERSION, ASSETS_DIR, DEFAULT_DB, DEFAULT_HOST, DEFAULT_PORT, EULA_PATH
from viewer.settings_ui import build_settings_page
from viewer.station_ui import build_station_viewer_page
from viewer.storage import ConfigStore, SESSION_TTL_SEC, normalize_base_url, verify_secret


COOKIE_NAME = "rid_node_center_session"
MAX_JSON_BYTES = 512 * 1024
WS_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"
APP_START_WALL = time.time()


def _utc_text(ts: float | None = None) -> str:
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(float(ts or time.time())))


def _json_bytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def _clean_header(value: str) -> str:
    return str(value or "").replace("\r", "").replace("\n", "")


def _html_escape(value: Any) -> str:
    return (
        str(value if value is not None else "")
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def _viewer_host_status(store: ConfigStore, listen: str = "") -> dict[str, Any]:
    aggregate = aggregate_nodes(store)
    host: dict[str, Any] = {
        "hostname": platform.node() or os.environ.get("COMPUTERNAME") or "viewer",
        "platform": platform.platform(),
        "cpu_count": int(os.cpu_count() or 1),
        "uptime_sec": int(max(0.0, time.time() - APP_START_WALL)),
        "db_path": str(store.path),
        "listen": listen,
        "node_count": aggregate.get("node_count", 0),
        "online_node_count": aggregate.get("online_node_count", 0),
        "drone_count": aggregate.get("drone_count", 0),
        "online_drone_count": aggregate.get("online_drone_count", 0),
    }
    try:
        import psutil  # type: ignore

        host["cpu_percent"] = psutil.cpu_percent(interval=0.0)
        mem = psutil.virtual_memory()
        host["mem_percent"] = round(float(mem.percent), 1)
        host["mem_used_mb"] = int((mem.total - mem.available) / (1024 * 1024))
        host["mem_total_mb"] = int(mem.total / (1024 * 1024))
    except Exception:
        host["cpu_percent"] = None
        host["mem_percent"] = None
        host["mem_used_mb"] = None
        host["mem_total_mb"] = None
    return host


def _viewer_notification_payload() -> dict[str, Any]:
    return {"ok": True, "seq": int(time.time()), "count": 0, "items": []}


def _viewer_interfaces_payload() -> dict[str, Any]:
    return {
        "ok": True,
        "selected": "viewer",
        "items": [
            {
                "name": "viewer",
                "label": "viewer (aggregated station APIs)",
                "is_wireless": False,
                "admin_up": True,
                "state": "virtual",
                "mode": "aggregate",
                "ipv4": [],
            }
        ],
    }


def _viewer_config_payload(store: ConfigStore) -> dict[str, Any]:
    cfg = {
        "viewer": {
            "db_path": str(store.path),
            "auth": store.public_auth_config(),
            "map": store.map_config(),
            "nodes": store.list_nodes(reveal_token=False),
        }
    }
    return {
        "ok": True,
        "path": str(store.path),
        "readonly": True,
        "text": json.dumps(cfg, ensure_ascii=False, indent=2),
    }


def _node_candidate_from_body(store: ConfigStore, body: dict[str, Any]) -> dict[str, Any]:
    node_id = int(body.get("id") or 0)
    base_url = normalize_base_url(str(body.get("base_url") or body.get("url") or ""))
    token = str(body.get("token") or "")
    if node_id and token == "" and not bool(body.get("clear_token")):
        existing = next((n for n in store.list_nodes(reveal_token=True) if int(n.get("id") or 0) == node_id), None)
        if existing:
            token = str(existing.get("token") or "")
    name = str(body.get("name") or "").strip() or urllib.parse.urlparse(base_url).netloc
    return {"id": node_id, "name": name, "base_url": base_url, "token": token, "enabled": True}


def _markdown_to_basic_html(text: str) -> str:
    blocks: list[str] = []
    for raw in str(text or "").splitlines():
        line = raw.rstrip()
        if not line:
            blocks.append("")
        elif line.startswith("#"):
            level = min(3, max(1, len(line) - len(line.lstrip("#"))))
            blocks.append(f"<h{level}>{_html_escape(line.lstrip('#').strip())}</h{level}>")
        else:
            blocks.append(f"<p>{_html_escape(line)}</p>")
    return "\n".join(blocks)


def _build_eula_page(next_path: str = "/") -> str:
    try:
        text = EULA_PATH.read_text(encoding="utf-8")
    except Exception:
        text = "Light RID Scanner EULA\n\nThe bundled EULA file is not available in this build."
    next_url = next_path if str(next_path or "").startswith("/") else "/"
    return f"""<!doctype html><html lang="zh"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>许可协议 - {APP_NAME}</title>
<style>
body{{margin:0;min-height:100dvh;background:#201f1e;color:#f3f2f1;font-family:"Segoe UI","Microsoft YaHei",sans-serif}}
.wrap{{width:min(980px,calc(100vw - 28px));margin:0 auto;padding:22px 12px 30px}}
.license{{border:1px solid #3b3a39;background:#2b2a29;border-radius:4px;padding:18px;max-height:min(68dvh,720px);overflow:auto;line-height:1.65}}
button{{height:36px;border:1px solid #3b3a39;background:#252423;color:#f3f2f1;border-radius:4px;padding:0 12px;font-weight:650;cursor:pointer}}
.warn{{color:#ffd8d8;border-color:#ff7b72}}.actions{{display:flex;gap:10px;flex-wrap:wrap;margin-top:14px}}.status{{color:#c8c6c4;margin-top:10px;white-space:pre-wrap}}
</style></head><body><div class="wrap">
<h1>Light RID Scanner 许可协议</h1>
<article class="license">{_markdown_to_basic_html(text)}</article>
<label style="display:flex;gap:8px;align-items:center;margin-top:14px"><input id="agree" type="checkbox"> <span>我已阅读并同意以上许可协议。</span></label>
<div class="actions"><button id="accept" type="button">同意并继续</button><button class="warn" id="back" type="button">返回</button></div>
<div id="status" class="status">首次使用前请确认许可协议。</div>
</div><script>
const nextPath = {next_url!r};
document.getElementById('back').onclick = function(){{ location.href = nextPath || '/'; }};
document.getElementById('accept').onclick = async function(){{
  if(!document.getElementById('agree').checked){{ document.getElementById('status').textContent='请先勾选同意许可协议。'; return; }}
  const r = await fetch('/api/eula/accept', {{method:'POST', headers:{{'Content-Type':'application/json','X-LightRID-Page':'1'}}, body:'{{}}'}});
  const d = await r.json().catch(()=>({{}}));
  if(!r.ok || d.ok === false){{ document.getElementById('status').textContent=d.error||('HTTP '+r.status); return; }}
  location.href = nextPath || '/';
}};
</script></body></html>"""


class ThreadingHTTPServer(ThreadingMixIn, HTTPServer):
    daemon_threads = True
    allow_reuse_address = True


class ViewerHandler(BaseHTTPRequestHandler):
    server_version = "LightRIDNodeCenter/" + APP_VERSION
    sys_version = ""
    store: ConfigStore
    listen_label: str = ""

    def log_message(self, fmt: str, *args: Any) -> None:
        print(f"[{_utc_text()}] {self.address_string()} {fmt % args}")

    def end_headers(self) -> None:
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("X-Frame-Options", "DENY")
        self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
        super().end_headers()

    def _cookie_token(self) -> str:
        try:
            cookie = SimpleCookie(self.headers.get("Cookie", ""))
            return str(cookie.get(COOKIE_NAME).value if cookie.get(COOKIE_NAME) else "")
        except Exception:
            return ""

    def _subject(self) -> str | None:
        cfg = self.store.auth_config()
        if not cfg["enabled"]:
            return "local"
        return self.store.session_subject(self._cookie_token())

    def _require_auth(self) -> bool:
        if self._subject():
            return True
        self._send_json({"ok": False, "error": "login required", "auth_expired": True}, 401)
        return False

    def _send_json(self, payload: dict[str, Any], status: int = 200) -> None:
        body = _json_bytes(payload)
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
        data = json.loads(self.rfile.read(size).decode("utf-8"))
        if not isinstance(data, dict):
            raise ValueError("JSON body must be object")
        return data

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
        body = full.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", mimetypes.guess_type(str(full))[0] or "application/octet-stream")
        self.send_header("Cache-Control", "public, max-age=86400")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def _set_session_response(self, subject: str) -> None:
        token = self.store.create_session(subject)
        payload = _json_bytes({"ok": True, "subject": subject})
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Set-Cookie", _clean_header(f"{COOKIE_NAME}={token}; Max-Age={SESSION_TTL_SEC}; Path=/; HttpOnly; SameSite=Lax"))
        self.send_header("Content-Length", str(len(payload)))
        self.end_headers()
        self.wfile.write(payload)

    def _send_ws_frame(self, payload: bytes) -> None:
        header = bytearray([0x81])
        length = len(payload)
        if length < 126:
            header.append(length)
        elif length < 65536:
            header.append(126)
            header.extend(struct.pack("!H", length))
        else:
            header.append(127)
            header.extend(struct.pack("!Q", length))
        self.wfile.write(bytes(header) + payload)
        self.wfile.flush()

    def _handle_ws(self) -> None:
        key = self.headers.get("Sec-WebSocket-Key", "").strip()
        if not key:
            self.send_response(400)
            self.end_headers()
            return
        accept = base64.b64encode(hashlib.sha1((key + WS_GUID).encode("ascii")).digest()).decode("ascii")
        try:
            self.request.sendall(
                (
                    "HTTP/1.1 101 Switching Protocols\r\n"
                    "Upgrade: websocket\r\n"
                    "Connection: Upgrade\r\n"
                    f"Sec-WebSocket-Accept: {accept}\r\n\r\n"
                ).encode("ascii")
            )
            last = 0.0
            while True:
                now = time.time()
                if now - last >= 1.5:
                    self._send_ws_frame(_json_bytes(viewer_state_snapshot(self.store)))
                    last = now
                time.sleep(0.25)
        except (BrokenPipeError, ConnectionAbortedError, ConnectionResetError, OSError):
            return

    def do_GET(self) -> None:
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query or "")
        if path.startswith("/assets/"):
            self._serve_asset(path)
            return
        if path == "/favicon.ico":
            self.send_response(204)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        if path in ("/", "/index.html"):
            if query.get("check"):
                cfg = self.store.auth_config()
                check = str((query.get("check") or [""])[0])
                if cfg["enabled"] and cfg["sso_enabled"] and cfg["sso_check_hash"] and verify_secret(check, cfg["sso_check_hash"]):
                    token = self.store.create_session("sso")
                    self.send_response(302)
                    self.send_header("Location", "/")
                    self.send_header("Set-Cookie", _clean_header(f"{COOKIE_NAME}={token}; Max-Age={SESSION_TTL_SEC}; Path=/; HttpOnly; SameSite=Lax"))
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return
            self._send_html(build_station_viewer_page())
            return
        if path == "/settings":
            if not self._require_auth():
                return
            self._send_html(build_settings_page())
            return
        if path == "/nodes":
            if not self._require_auth():
                return
            self._send_html(build_nodes_page())
            return
        if path in ("/eula", "/eula.html"):
            next_path = str((query.get("next") or ["/"])[0] or "/")
            self._send_html(_build_eula_page(next_path))
            return
        if path == "/ws":
            if not self._require_auth():
                return
            self._handle_ws()
            return
        if path == "/api/session":
            cfg = self.store.auth_config()
            subject = self._subject()
            self._send_json({"ok": True, "auth_enabled": bool(cfg["enabled"]), "authenticated": bool(subject), "subject": subject or ""})
            return
        if path == "/api/health":
            self._send_json(
                {
                    "ok": True,
                    "service": {
                        "sniff_state": "viewer",
                        "sniff_msg": "node-center",
                        "uptime_sec": int(max(0.0, time.time() - APP_START_WALL)),
                    },
                }
            )
            return
        if path in ("/api/v1", "/api/v1/"):
            self._send_json({"ok": True, "name": APP_NAME, "version": APP_VERSION})
            return
        if path == "/api/v1/snapshot":
            if not self._require_auth():
                return
            self._send_json({"ok": True, "data": viewer_state_snapshot(self.store)})
            return
        if path == "/api/v1/drones":
            if not self._require_auth():
                return
            snap = viewer_state_snapshot(self.store)
            self._send_json({"ok": True, "count": len(snap.get("drones") or []), "items": snap.get("drones") or []})
            return
        if path == "/api/v1/aps":
            self._send_json({"ok": True, "seq": int(time.time()), "total": 0, "count": 0, "items": []})
            return
        if path == "/api/notifications":
            if not self._require_auth():
                return
            self._send_json(_viewer_notification_payload())
            return
        if path == "/api/interfaces":
            if not self._require_auth():
                return
            self._send_json(_viewer_interfaces_payload())
            return
        if path == "/api/config":
            if not self._require_auth():
                return
            self._send_json(_viewer_config_payload(self.store))
            return
        if path == "/api/settings":
            if not self._require_auth():
                return
            self._send_json(
                {
                    "ok": True,
                    "auth": self.store.public_auth_config(),
                    "map": self.store.map_config(),
                    "host": _viewer_host_status(self.store, self.listen_label),
                    "eula": self.store.eula_status(),
                }
            )
            return
        if path == "/api/settings/view":
            if not self._require_auth():
                return
            self._send_json(
                {
                    "ok": True,
                    "auth": self.store.public_auth_config(),
                    "map": self.store.map_config(),
                    "host": _viewer_host_status(self.store, self.listen_label),
                    "eula": self.store.eula_status(),
                    "nodes": self.store.list_nodes(False),
                }
            )
            return
        if path == "/api/eula/status":
            self._send_json(self.store.eula_status())
            return
        if path == "/api/nodes":
            if not self._require_auth():
                return
            self._send_json({"ok": True, "items": self.store.list_nodes(reveal_token=False)})
            return
        if path == "/api/nodes/metrics":
            if not self._require_auth():
                return
            try:
                node_id = int((query.get("node_id") or ["0"])[0] or "0")
                window = str((query.get("window") or ["12h"])[0] or "12h")
                node = next((n for n in self.store.list_nodes(reveal_token=True) if int(n.get("id") or 0) == node_id), None)
                if not node:
                    self._send_json({"ok": False, "error": "node not found", "items": []}, 404)
                    return
                self._send_json(fetch_node_metrics(node, window))
            except Exception as exc:
                self._send_json({"ok": False, "error": str(exc), "items": []}, 400)
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
                nodes = self.store.list_nodes(reveal_token=True)
                if node_id:
                    nodes = [n for n in nodes if int(n.get("id") or 0) == node_id]
                for node in nodes:
                    payload = fetch_node_track(node, sn)
                    if payload.get("ok"):
                        self._send_json(payload)
                        return
                self._send_json({"ok": False, "error": "track not found", "track": []}, 404)
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
                self._set_session_response("local")
                return
            username = str(body.get("username") or "")
            password = str(body.get("password") or "")
            if username == cfg["username"] and cfg["password_hash"] and verify_secret(password, cfg["password_hash"]):
                self._set_session_response(username)
                return
            self._send_json({"ok": False, "error": "账号或密码错误"}, 401)
            return
        if path == "/api/logout":
            self.store.delete_session(self._cookie_token())
            payload = _json_bytes({"ok": True})
            self.send_response(200)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Set-Cookie", _clean_header(f"{COOKIE_NAME}=; Max-Age=0; Path=/; HttpOnly; SameSite=Lax"))
            self.send_header("Content-Length", str(len(payload)))
            self.end_headers()
            self.wfile.write(payload)
            return
        if not self._require_auth():
            return
        try:
            if path == "/api/eula/accept":
                self._send_json(self.store.accept_eula())
                return
            if path == "/api/eula/revoke":
                self._send_json(self.store.revoke_eula())
                return
            if path == "/api/notifications":
                self._send_json(_viewer_notification_payload())
                return
            if path == "/api/notifications/clear":
                self._send_json(_viewer_notification_payload() | {"cleared": 0})
                return
            if path == "/api/notifications/delete":
                self._send_json(_viewer_notification_payload() | {"deleted": False})
                return
            if path == "/api/config/save":
                self._send_json({"ok": False, "error": "viewer config is managed through /settings and /nodes"}, 400)
                return
            if path == "/api/settings/save":
                auth = self.store.save_auth_config(body.get("auth") if isinstance(body.get("auth"), dict) else {})
                map_cfg = self.store.save_map_config(body.get("map") if isinstance(body.get("map"), dict) else {})
                self._send_json(
                    {
                        "ok": True,
                        "auth": auth,
                        "map": map_cfg,
                        "host": _viewer_host_status(self.store, self.listen_label),
                        "eula": self.store.eula_status(),
                    }
                )
                return
            if path == "/api/settings/auth":
                self._send_json({"ok": True, "auth": self.store.save_auth_config(body)})
                return
            if path == "/api/nodes":
                probe = test_node_communication(_node_candidate_from_body(self.store, body))
                if not probe.get("ok"):
                    self._send_json({"ok": False, "error": probe.get("error") or "node API communication failed", "node": probe}, 400)
                    return
                self._send_json({"ok": True, "item": self.store.upsert_node(body)})
                return
            if path == "/api/nodes/test":
                node = _node_candidate_from_body(self.store, body)
                self._send_json({"ok": True, "node": test_node_communication(node)})
                return
            if path == "/api/nodes/delete":
                self._send_json({"ok": True, "deleted": self.store.delete_node(int(body.get("id") or 0))})
                return
            if path == "/api/nodes/sso":
                node_id = int(body.get("node_id") or body.get("id") or 0)
                node = next((n for n in self.store.list_nodes(reveal_token=True) if int(n.get("id") or 0) == node_id), None)
                if not node:
                    self._send_json({"ok": False, "error": "node not found"}, 404)
                    return
                payload = create_node_sso_url(node)
                self._send_json(payload, 200 if payload.get("ok", True) else 400)
                return
            if path == "/api/nodes/remote":
                ids = body.get("node_ids")
                if not isinstance(ids, list):
                    ids = [body.get("node_id") or body.get("id")]
                wanted = {int(x) for x in ids if str(x or "").strip()}
                operation = str(body.get("operation") or "")
                results = []
                for node in self.store.list_nodes(reveal_token=True):
                    if wanted and int(node.get("id") or 0) not in wanted:
                        continue
                    payload = run_node_operation(node, operation)
                    results.append(
                        {
                            "id": node.get("id"),
                            "name": node.get("name"),
                            "base_url": node.get("base_url"),
                            "ok": bool(payload.get("ok")),
                            "error": payload.get("error"),
                            "response": payload,
                        }
                    )
                if not results:
                    self._send_json({"ok": False, "error": "no nodes selected", "results": []}, 400)
                    return
                self._send_json({"ok": True, "operation": operation, "results": results})
                return
            if path in ("/api/history/clear", "/api/history/delete", "/api/tracks/clear"):
                self._send_json({"ok": False, "error": "viewer does not store remote history"}, 400)
                return
        except Exception as exc:
            self._send_json({"ok": False, "error": str(exc)}, 400)
            return
        self._send_json({"ok": False, "error": "not found"}, 404)


def run(host: str, port: int, db_path: Path) -> None:
    ViewerHandler.store = ConfigStore(db_path)
    ViewerHandler.listen_label = f"{host}:{port}"
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
