"""Live aggregation from station_edition token APIs."""

from __future__ import annotations

import json
import time
import urllib.error
import urllib.parse
import urllib.request
from typing import Any

from viewer.storage import ConfigStore


HTTP_TIMEOUT_SEC = 5.0
MAX_JSON_BYTES = 512 * 1024
APP_VERSION = "0.1.0"


def _safe_float(value: Any) -> float | None:
    try:
        if value in (None, ""):
            return None
        if str(value).strip().lower() in {"na", "n/a", "none", "null", "-", "--"}:
            return None
        out = float(value)
        return None if out != out or out in (float("inf"), float("-inf")) else out
    except Exception:
        return None


def _request_json(
    base_url: str,
    token: str,
    path: str,
    *,
    method: str = "GET",
    body: dict[str, Any] | None = None,
) -> tuple[dict[str, Any] | None, str | None, int | None]:
    url = base_url.rstrip("/") + path
    headers = {"Accept": "application/json", "User-Agent": f"LightRIDNodeCenter/{APP_VERSION}"}
    if token:
        headers["X-API-Token"] = token
        headers["Authorization"] = "Bearer " + token
    data = None
    if body is not None:
        data = json.dumps(body, ensure_ascii=False).encode("utf-8")
        headers["Content-Type"] = "application/json"
    req = urllib.request.Request(url, data=data, headers=headers, method=method.upper())
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


def _fetch_json(base_url: str, token: str, path: str) -> tuple[dict[str, Any] | None, str | None, int | None]:
    return _request_json(base_url, token, path)


def _payload_ok(payload: dict[str, Any] | None) -> bool:
    return isinstance(payload, dict) and payload.get("ok", True) is not False


def test_node_communication(node: dict[str, Any]) -> dict[str, Any]:
    started = time.time()
    base_url = str(node.get("base_url") or "")
    token = str(node.get("token") or "")
    api_root = base_url.rstrip("/") + "/api/v1"
    root, root_err, root_code = _fetch_json(base_url, token, "/api/v1")
    if not _payload_ok(root):
        return {
            "id": node.get("id", 0),
            "name": node.get("name") or base_url,
            "base_url": base_url,
            "api_root": api_root,
            "enabled": bool(node.get("enabled", True)),
            "ok": False,
            "error": "api root failed: " + (root_err or "invalid API response"),
            "status_code": root_code,
            "latency_ms": int((time.time() - started) * 1000),
            "station": {"name": node.get("name") or base_url, "lat": None, "lon": None, "zoom": 13},
            "drones": [],
            "count": 0,
            "online_count": 0,
            "fetched_at": time.time(),
        }
    snapshot, snap_err, snap_code = _fetch_json(base_url, token, "/api/v1/snapshot")
    if not _payload_ok(snapshot):
        return {
            "id": node.get("id", 0),
            "name": node.get("name") or base_url,
            "base_url": base_url,
            "api_root": api_root,
            "enabled": bool(node.get("enabled", True)),
            "ok": False,
            "error": "snapshot API failed: " + (snap_err or "invalid API response"),
            "status_code": snap_code,
            "latency_ms": int((time.time() - started) * 1000),
            "station": {"name": node.get("name") or base_url, "lat": None, "lon": None, "zoom": 13},
            "drones": [],
            "count": 0,
            "online_count": 0,
            "fetched_at": time.time(),
        }
    drones = _rows_from_snapshot(snapshot or {})
    return {
        "id": node.get("id", 0),
        "name": node.get("name") or base_url,
        "base_url": base_url,
        "api_root": api_root,
        "enabled": bool(node.get("enabled", True)),
        "ok": True,
        "error": None,
        "status_code": snap_code or root_code,
        "latency_ms": int((time.time() - started) * 1000),
        "station": _station_position_from_snapshot(snapshot or {}),
        "drones": drones,
        "count": len(drones),
        "online_count": len([x for x in drones if not bool(x.get("lost")) and not bool(x.get("archived"))]),
        "fetched_at": time.time(),
    }


def post_node_json(node: dict[str, Any], path: str, body: dict[str, Any] | None = None) -> dict[str, Any]:
    payload, err, code = _request_json(
        str(node.get("base_url") or ""),
        str(node.get("token") or ""),
        path,
        method="POST",
        body=body or {},
    )
    if payload is None:
        return {"ok": False, "error": err or "request failed", "status_code": code}
    if payload.get("ok") is False:
        payload.setdefault("status_code", code)
    return payload


def _station_position_from_snapshot(snapshot: dict[str, Any]) -> dict[str, Any]:
    data = snapshot.get("data") if isinstance(snapshot.get("data"), dict) else snapshot
    meta = data.get("meta") if isinstance(data.get("meta"), dict) else {}
    source = meta if isinstance(meta, dict) else {}
    name = str(source.get("base_name") or "基站").strip() or "基站"
    lat = _safe_float(source.get("base_lat"))
    lon = _safe_float(source.get("base_lon"))
    if lat is not None and not (-90 <= lat <= 90):
        lat = None
    if lon is not None and not (-180 <= lon <= 180):
        lon = None
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


def fetch_node_live(node: dict[str, Any]) -> dict[str, Any]:
    started = time.time()
    base_url = str(node.get("base_url") or "")
    token = str(node.get("token") or "")
    health, health_err, health_code = _fetch_json(base_url, token, "/api/health")
    snapshot, snap_err, snap_code = _fetch_json(base_url, token, "/api/v1/snapshot")
    hw_payload, _hw_err, _hw_code = _request_json(base_url, token, "/api/hw/op", method="POST", body={"op": "status"})
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
    hw_data = (hw_payload or {}).get("data") if isinstance((hw_payload or {}).get("data"), dict) else {}
    host = hw_data.get("host") if isinstance(hw_data.get("host"), dict) else {}
    if isinstance(hw_data.get("sniff_state"), dict) and not service.get("sniff_state"):
        service["sniff_state"] = hw_data["sniff_state"].get("state")
        service["sniff_msg"] = hw_data["sniff_state"].get("msg")
        service["sniff_iface"] = hw_data["sniff_state"].get("iface")
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
        "latency_ms": int((time.time() - started) * 1000),
        "station": station,
        "service": service,
        "host": host,
        "drones": enriched,
        "count": len(enriched),
        "online_count": len([x for x in enriched if not bool(x.get("lost")) and not bool(x.get("archived"))]),
        "fetched_at": time.time(),
    }


def fetch_node_track(node: dict[str, Any], sn: str) -> dict[str, Any]:
    encoded_sn = urllib.parse.quote(str(sn or "").strip(), safe="")
    if not encoded_sn:
        raise ValueError("sn required")
    payload, err, code = _fetch_json(str(node.get("base_url") or ""), str(node.get("token") or ""), f"/api/v1/tracks/{encoded_sn}")
    if payload is None:
        return {"ok": False, "error": err or "request failed", "status_code": code, "track": []}
    track = payload.get("track")
    if track is None:
        track = payload.get("items")
    if not isinstance(track, list):
        track = []
    return {"ok": True, "status_code": code, "track": [x for x in track if isinstance(x, dict)], "count": len(track)}


def fetch_node_metrics(node: dict[str, Any], window: str = "12h") -> dict[str, Any]:
    raw = str(window or "12h").strip().lower()
    if raw not in {"12h", "24h", "7d"}:
        raw = "12h"
    payload, err, code = _fetch_json(
        str(node.get("base_url") or ""),
        str(node.get("token") or ""),
        "/api/settings/metrics?window=" + urllib.parse.quote(raw, safe=""),
    )
    if payload is None:
        return {"ok": False, "error": err or "request failed", "status_code": code, "items": []}
    items = payload.get("items")
    if not isinstance(items, list):
        items = []
    payload["items"] = [x for x in items if isinstance(x, dict)]
    payload.setdefault("ok", True)
    payload["status_code"] = code
    return payload


def create_node_sso_url(node: dict[str, Any], name: str = "Viewer one-click login") -> dict[str, Any]:
    payload = post_node_json(
        node,
        "/api/v1/auth/sso-links/create",
        {"name": name, "next": "/", "ttl_sec": 3600, "single_use": False},
    )
    url = str(payload.get("url") or payload.get("path") or "")
    if url.startswith("/"):
        url = str(node.get("base_url") or "").rstrip("/") + url
        payload["url"] = url
    return payload


def run_node_operation(node: dict[str, Any], operation: str) -> dict[str, Any]:
    op = str(operation or "").strip().lower()
    if op == "restart":
        return post_node_json(node, "/api/admin/restart", {"save": False, "args": ""})
    if op == "update_models":
        return post_node_json(node, "/api/settings/models/update", {"url": ""})
    return {"ok": False, "error": f"unsupported operation: {operation}"}


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
                    "count": 0,
                    "online_count": 0,
                    "fetched_at": time.time(),
                }
            )
            continue
        live = fetch_node_live(node)
        live_nodes.append({k: v for k, v in live.items() if k != "drones"})
        drones.extend(live.get("drones") or [])
    return {
        "ok": True,
        "version": APP_VERSION,
        "fetched_at": time.time(),
        "nodes": live_nodes,
        "drones": drones,
        "node_count": len(live_nodes),
        "online_node_count": len([n for n in live_nodes if n.get("ok")]),
        "drone_count": len(drones),
        "online_drone_count": len([x for x in drones if not bool(x.get("lost")) and not bool(x.get("archived"))]),
    }


def viewer_state_snapshot(store: ConfigStore) -> dict[str, Any]:
    aggregate = aggregate_nodes(store)
    drones = list(aggregate.get("drones") or [])
    nodes = list(aggregate.get("nodes") or [])
    map_cfg = store.map_config()
    logs = []
    for node in nodes:
        status = "online" if node.get("ok") else "offline"
        detail = str(node.get("error") or node.get("base_url") or "")
        logs.append(f"[{status}] {node.get('name') or node.get('base_url')}: {detail}")
    return {
        "ts": time.strftime("%H:%M:%S"),
        "ch": "node-center",
        "drones": drones,
        "map_drones": [x for x in drones if not bool(x.get("archived"))],
        "logs": logs[-80:],
        "logs_seq": int(time.time()),
        "aps": [],
        "aps_seq": int(time.time()),
        "aps_total": 0,
        "meta": {
            "dji_lookup_url": "",
            "allow_restart": False,
            "restart_args_current": "",
            "restart_args_saved": "",
            "base_name": map_cfg.get("base_name") or "Node Center",
            "base_lat": map_cfg.get("base_lat"),
            "base_lon": map_cfg.get("base_lon"),
            "base_zoom": map_cfg.get("base_zoom") or 5,
            "heading_ref_deg": map_cfg.get("heading_ref_deg") or 0,
            "map_auto_center_idle_sec": map_cfg.get("map_auto_center_idle_sec") or 20,
            "config_path": str(store.path),
            "iface_selected": "viewer",
            "scan_wifi_fast": False,
            "wifi_fast_supported": False,
            "wifi_fast_msg": "viewer aggregates remote station APIs",
            "sniff_state": "ok" if aggregate.get("online_node_count") else "warn",
            "sniff_msg": f"nodes {aggregate.get('online_node_count', 0)}/{aggregate.get('node_count', 0)}",
            "sniff_iface": "node-center",
            "sniff_idle_sec": 0,
            "sniff_last_pkt": time.strftime("%H:%M:%S"),
            "settings_path": "/settings",
        },
    }
