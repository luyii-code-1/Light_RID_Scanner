"""Live aggregation from station_edition token APIs."""

from __future__ import annotations

import json
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import Any

from viewer.storage import ConfigStore


HTTP_TIMEOUT_SEC = 3.0
MAX_JSON_BYTES = 512 * 1024
APP_VERSION = "0.1.0"
LIVE_CACHE_SEC = 1.0
_LIVE_CACHE_LOCK = threading.Lock()
_LIVE_CACHE: dict[str, tuple[float, dict[str, Any]]] = {}


def _clear_live_cache(store: ConfigStore | None = None) -> None:
    prefix = str(getattr(store, "path", "") or "")
    with _LIVE_CACHE_LOCK:
        if not prefix:
            _LIVE_CACHE.clear()
            return
        for key in list(_LIVE_CACHE):
            if key.startswith(prefix + "|"):
                _LIVE_CACHE.pop(key, None)


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
    headers = {
        "Accept": "application/json",
        "User-Agent": f"LightRIDNodeCenter/{APP_VERSION}",
        "X-LightRID-Page": "1",
    }
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
        try:
            payload = json.loads(msg)
            if isinstance(payload, dict):
                msg = str(payload.get("error") or payload.get("message") or msg)
        except Exception:
            pass
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


def _node_label(node: dict[str, Any], station: dict[str, Any] | None = None) -> str:
    raw = ""
    if isinstance(station, dict):
        raw = str(station.get("name") or "").strip()
    return raw or str(node.get("name") or node.get("base_url") or "基站").strip() or "基站"


def _rssi_score(value: Any) -> float:
    val = _safe_float(value)
    return -9999.0 if val is None else float(val)


def _best_row(rows: list[dict[str, Any]]) -> dict[str, Any]:
    if not rows:
        return {}
    return max(rows, key=lambda row: (_rssi_score(row.get("rssi")), float(row.get("track_count") or 0), -float(row.get("age") or 0)))


def _merge_track_points(tracks: list[list[dict[str, Any]]]) -> list[dict[str, Any]]:
    by_slot: dict[str, dict[str, Any]] = {}
    for track in tracks:
        for point in track if isinstance(track, list) else []:
            if not isinstance(point, dict):
                continue
            ts = _safe_float(point.get("ts"))
            if ts is None:
                slot = f"idx:{len(by_slot)}"
            else:
                slot = f"{ts:.3f}"
            old = by_slot.get(slot)
            if old is None or _rssi_score(point.get("rssi")) > _rssi_score(old.get("rssi")):
                by_slot[slot] = dict(point)
    return sorted(
        by_slot.values(),
        key=lambda p: (_safe_float(p.get("ts")) is None, _safe_float(p.get("ts")) or 0.0),
    )


def _merge_rows_by_sn(rows: list[dict[str, Any]], *, aggregate_history: bool = False) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = {}
    passthrough: list[dict[str, Any]] = []
    for row in rows:
        if not isinstance(row, dict):
            continue
        sn = str(row.get("sn") or "").strip()
        if not sn:
            passthrough.append(row)
            continue
        grouped.setdefault(sn, []).append(row)
    out: list[dict[str, Any]] = list(passthrough)
    for sn, items in grouped.items():
        best = dict(_best_row(items))
        names: list[str] = []
        versions = []
        tracks = []
        for row in items:
            name = str(row.get("_node_name") or row.get("_station_name") or "").strip()
            if name and name not in names:
                names.append(name)
            versions.append(
                {
                    "node_id": row.get("_node_id"),
                    "node_name": row.get("_node_name"),
                    "node_url": row.get("_node_url"),
                    "rssi": row.get("rssi"),
                    "age": row.get("age"),
                    "last_pkt_time": row.get("last_pkt_time") or row.get("capture_time"),
                    "track_count": row.get("track_count"),
                }
            )
            if isinstance(row.get("track"), list):
                tracks.append(row["track"])
        best["sn"] = sn
        best["_node_names"] = names
        best["_node_observations"] = versions
        best["discovered_base_names"] = names
        best["discovered_base_text"] = "、".join(names) if names else ""
        best["viewer_aggregate_count"] = len(items)
        best["lost"] = all(bool(x.get("lost")) for x in items)
        best["archived"] = all(bool(x.get("archived")) for x in items)
        if len(items) > 1:
            best["viewer_aggregate_mode"] = True
        if aggregate_history and tracks:
            merged_track = _merge_track_points(tracks)
            best["track"] = merged_track
            best["track_count"] = len(merged_track)
        out.append(best)
    return out


def fetch_node_live(node: dict[str, Any], *, include_hw: bool = False) -> dict[str, Any]:
    started = time.time()
    base_url = str(node.get("base_url") or "")
    token = str(node.get("token") or "")
    snapshot, snap_err, snap_code = _fetch_json(base_url, token, "/api/v1/snapshot")
    health: dict[str, Any] | None = None
    health_err: str | None = None
    health_code: int | None = None
    if snapshot is None:
        health, health_err, health_code = _fetch_json(base_url, token, "/api/health")
    hw_payload: dict[str, Any] | None = None
    if include_hw:
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
    ok = snapshot is not None and _payload_ok(snapshot)
    service = (health or {}).get("service") if isinstance((health or {}).get("service"), dict) else {}
    hw_data = (hw_payload or {}).get("data") if isinstance((hw_payload or {}).get("data"), dict) else {}
    host = hw_data.get("host") if isinstance(hw_data.get("host"), dict) else {}
    if isinstance(hw_data.get("sniff_state"), dict) and not service.get("sniff_state"):
        service["sniff_state"] = hw_data["sniff_state"].get("state")
        service["sniff_msg"] = hw_data["sniff_state"].get("msg")
        service["sniff_iface"] = hw_data["sniff_state"].get("iface")
    enriched = []
    node_name = _node_label(node, station)
    for item in drones:
        row = dict(item)
        row["_node_id"] = node["id"]
        row["_node_name"] = node_name
        row["_node_url"] = base_url
        row["_station_name"] = station.get("name")
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
    clean = []
    for point in track:
        if not isinstance(point, dict):
            continue
        row = dict(point)
        row["_node_id"] = node.get("id")
        row["_node_name"] = node.get("name")
        row["_node_url"] = node.get("base_url")
        clean.append(row)
    return {"ok": True, "status_code": code, "track": clean, "count": len(clean)}


def aggregate_track_for_sn(store: ConfigStore, sn: str, *, force: bool = False) -> dict[str, Any]:
    sn = str(sn or "").strip()
    if not sn:
        return {"ok": False, "error": "sn required", "track": []}
    cache_key = "track." + sn
    ttl_hours = store.aggregate_config().get("cache_ttl_hours", 24)
    if not force:
        cached = store.get_cache_payload(cache_key)
        if cached:
            cached["cached"] = True
            return cached
    nodes = [node for node in store.list_nodes(reveal_token=True) if bool(node.get("enabled"))]
    tracks: list[list[dict[str, Any]]] = []
    results = []
    with ThreadPoolExecutor(max_workers=max(1, min(12, len(nodes) or 1))) as pool:
        futures = {pool.submit(fetch_node_track, node, sn): node for node in nodes}
        for future in as_completed(futures):
            node = futures[future]
            try:
                payload = future.result()
            except Exception as exc:
                payload = {"ok": False, "error": str(exc), "track": []}
            track = payload.get("track") if isinstance(payload.get("track"), list) else []
            if payload.get("ok") and track:
                tracks.append(track)
            results.append(
                {
                    "node_id": node.get("id"),
                    "node_name": node.get("name"),
                    "ok": bool(payload.get("ok")),
                    "count": len(track),
                    "error": payload.get("error"),
                }
            )
    merged = _merge_track_points(tracks)
    payload = {
        "ok": bool(merged) or bool(results),
        "sn": sn,
        "cached": False,
        "count": len(merged),
        "count_total": len(merged),
        "track": merged,
        "nodes": results,
    }
    if merged:
        store.set_cache_payload(cache_key, payload, ttl_hours)
    return payload


def aggregate_aircraft_detail(store: ConfigStore, sn: str, *, force: bool = False) -> dict[str, Any]:
    target_sn = str(sn or "").strip()
    if not target_sn:
        return {"ok": False, "error": "sn required", "item": None, "track": []}
    aggregate = aggregate_nodes(store, force=force)
    item = None
    for row in aggregate.get("drones") or []:
        if isinstance(row, dict) and str(row.get("sn") or "").strip() == target_sn:
            item = dict(row)
            break
    if not item:
        return {"ok": False, "error": "sn not found", "sn": target_sn, "item": None, "track": []}
    track_payload = aggregate_track_for_sn(store, target_sn, force=force)
    track = track_payload.get("track") if isinstance(track_payload.get("track"), list) else []
    return {
        "ok": True,
        "sn": target_sn,
        "sn_now": target_sn,
        "item": item,
        "track_count": len(track),
        "track": track,
        "nodes": track_payload.get("nodes") or [],
        "cached": bool(aggregate.get("cached") or track_payload.get("cached")),
    }


def fetch_node_metrics(node: dict[str, Any], window: str = "12h") -> dict[str, Any]:
    raw = str(window or "12h").strip().lower()
    if raw not in {"12h", "24h", "7d"}:
        raw = "12h"
    payload, err, code = _fetch_json(
        str(node.get("base_url") or ""),
        str(node.get("token") or ""),
        "/api/v1/metrics?window=" + urllib.parse.quote(raw, safe=""),
    )
    if payload is None and code in (404, 405):
        payload, err, code = _fetch_json(
            str(node.get("base_url") or ""),
            str(node.get("token") or ""),
            "/api/settings/metrics?window=" + urllib.parse.quote(raw, safe=""),
        )
    if payload is None:
        if str(err or "").strip().lower() == "login required":
            return {
                "ok": True,
                "enabled": False,
                "error": "子站负载接口需要网页登录会话；请更新子站以提供 /api/v1/metrics Token API。",
                "status_code": code,
                "items": [],
            }
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
    if op == "reidentify_recent":
        return post_node_json(node, "/api/v1/history/reidentify-recent", {"limit": 100})
    return {"ok": False, "error": f"unsupported operation: {operation}"}


def reparse_node_aircraft(store: ConfigStore, sn: str, mode: str = "auto") -> dict[str, Any]:
    target_sn = str(sn or "").strip()
    if not target_sn:
        return {"ok": False, "error": "sn required", "results": []}
    mode_key = str(mode or "auto").strip() or "auto"
    nodes = [node for node in store.list_nodes(reveal_token=True) if bool(node.get("enabled"))]
    results: list[dict[str, Any]] = []
    if nodes:
        with ThreadPoolExecutor(max_workers=max(1, min(12, len(nodes)))) as pool:
            futures = {
                pool.submit(post_node_json, node, "/api/v1/history/reparse", {"sn": target_sn, "mode": mode_key}): node
                for node in nodes
            }
            for future in as_completed(futures):
                node = futures[future]
                try:
                    payload = future.result()
                except Exception as exc:
                    payload = {"ok": False, "error": str(exc)}
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
    ok_count = sum(1 for item in results if item.get("ok"))
    if ok_count:
        store.clear_cache_payload(None)
        _clear_live_cache(store)
    sn_now = target_sn
    for item in results:
        response = item.get("response") if isinstance(item.get("response"), dict) else {}
        candidate = str(response.get("sn_now") or response.get("sn") or "").strip()
        if item.get("ok") and candidate:
            sn_now = candidate
            break
    detail = aggregate_aircraft_detail(store, sn_now, force=True) if ok_count else {}
    return {
        "ok": bool(ok_count),
        "sn": target_sn,
        "sn_now": sn_now,
        "mode": mode_key,
        "updated_nodes": ok_count,
        "node_count": len(results),
        "results": results,
        "refresh": bool(ok_count),
        "item": detail.get("item") if isinstance(detail, dict) else None,
        "track": detail.get("track") if isinstance(detail, dict) else [],
        "track_count": detail.get("track_count", 0) if isinstance(detail, dict) else 0,
        "message": f"远程重新解析完成: {ok_count}/{len(results)} 个节点",
    }


def _live_cache_key(store: ConfigStore, include_hw: bool) -> str:
    nodes = store.list_nodes(reveal_token=False)
    sig = "|".join(f"{n.get('id')}:{n.get('base_url')}:{int(bool(n.get('enabled')))}" for n in nodes)
    return f"{store.path}|{include_hw}|{sig}"


def aggregate_nodes(store: ConfigStore, *, include_hw: bool = False, force: bool = False) -> dict[str, Any]:
    cache_key = _live_cache_key(store, include_hw)
    now = time.time()
    if not force:
        with _LIVE_CACHE_LOCK:
            cached = _LIVE_CACHE.get(cache_key)
            if cached and now - cached[0] <= LIVE_CACHE_SEC:
                return dict(cached[1])
    nodes = store.list_nodes(reveal_token=True)
    live_nodes = []
    drones = []
    enabled_nodes = []
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
        enabled_nodes.append(node)
    max_workers = max(1, min(12, len(enabled_nodes)))
    if enabled_nodes:
        with ThreadPoolExecutor(max_workers=max_workers) as pool:
            futures = {pool.submit(fetch_node_live, node, include_hw=include_hw): node for node in enabled_nodes}
            for future in as_completed(futures):
                node = futures[future]
                try:
                    live = future.result()
                except Exception as exc:
                    live = {
                        "id": node["id"],
                        "name": node["name"],
                        "base_url": node["base_url"],
                        "enabled": bool(node.get("enabled")),
                        "ok": False,
                        "error": str(exc),
                        "station": {"name": node["name"], "lat": None, "lon": None, "zoom": 13},
                        "service": {},
                        "count": 0,
                        "online_count": 0,
                        "fetched_at": time.time(),
                    }
                live_nodes.append({k: v for k, v in live.items() if k != "drones"})
                drones.extend(live.get("drones") or [])
    merged = _merge_rows_by_sn(drones)
    payload = {
        "ok": True,
        "version": APP_VERSION,
        "fetched_at": time.time(),
        "nodes": sorted(live_nodes, key=lambda n: int(n.get("id") or 0)),
        "drones": merged,
        "raw_drones": drones,
        "node_count": len(live_nodes),
        "online_node_count": len([n for n in live_nodes if n.get("ok")]),
        "drone_count": len(merged),
        "raw_drone_count": len(drones),
        "online_drone_count": len([x for x in merged if not bool(x.get("lost")) and not bool(x.get("archived"))]),
    }
    with _LIVE_CACHE_LOCK:
        _LIVE_CACHE[cache_key] = (time.time(), dict(payload))
    return payload


def aggregate_history(store: ConfigStore, *, force: bool = False) -> dict[str, Any]:
    ttl_hours = store.aggregate_config().get("cache_ttl_hours", 24)
    if not force:
        cached = store.get_cache_payload("history.aggregate")
        if cached:
            cached["cached"] = True
            return cached
    live = aggregate_nodes(store, force=True)
    raw_rows = [x for x in live.get("raw_drones") or [] if isinstance(x, dict)]
    sn_list = sorted({str(x.get("sn") or "").strip() for x in raw_rows if str(x.get("sn") or "").strip()})
    nodes = store.list_nodes(reveal_token=True)
    node_by_id = {int(n.get("id") or 0): n for n in nodes}
    tracks_by_sn: dict[str, list[list[dict[str, Any]]]] = {sn: [] for sn in sn_list}
    tasks = []
    with ThreadPoolExecutor(max_workers=max(1, min(12, len(nodes) * 2 or 1))) as pool:
        for row in raw_rows:
            sn = str(row.get("sn") or "").strip()
            node = node_by_id.get(int(row.get("_node_id") or 0))
            if not sn or not node:
                continue
            tasks.append((sn, pool.submit(fetch_node_track, node, sn)))
        for sn, future in tasks:
            try:
                payload = future.result()
            except Exception:
                payload = {"ok": False, "track": []}
            if payload.get("ok") and isinstance(payload.get("track"), list):
                tracks_by_sn.setdefault(sn, []).append(payload["track"])
    expanded = []
    for row in raw_rows:
        item = dict(row)
        item["track"] = _merge_track_points(tracks_by_sn.get(str(row.get("sn") or "").strip(), []))
        item["track_count"] = len(item["track"])
        expanded.append(item)
    aggregated = _merge_rows_by_sn(expanded, aggregate_history=True)
    payload = {
        "ok": True,
        "version": APP_VERSION,
        "cached": False,
        "cache_ttl_hours": ttl_hours,
        "generated_at": time.time(),
        "nodes": live.get("nodes") or [],
        "items": aggregated,
        "drones": aggregated,
        "raw_count": len(raw_rows),
        "count": len(aggregated),
        "aggregate_count": len([x for x in aggregated if x.get("viewer_aggregate_mode")]),
    }
    store.set_cache_payload("history.aggregate", payload, ttl_hours)
    return payload


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
        "viewer_nodes": nodes,
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


def viewer_loading_snapshot(store: ConfigStore) -> dict[str, Any]:
    """Return an immediate shell snapshot without touching remote stations."""
    map_cfg = store.map_config()
    nodes = store.list_nodes(reveal_token=False)
    enabled = [node for node in nodes if bool(node.get("enabled"))]
    node_count = len(nodes)
    enabled_count = len(enabled)
    target_names = [
        str(node.get("name") or node.get("base_url") or "").strip()
        for node in enabled
        if str(node.get("name") or node.get("base_url") or "").strip()
    ]
    return {
        "ts": time.strftime("%H:%M:%S"),
        "ch": "node-center",
        "drones": [],
        "map_drones": [],
        "logs": [
            f"[loading] 正在向节点获取数据: 已配置 {node_count} 个节点，启用 {enabled_count} 个。",
            "[loading] 首页框架已加载，节点数据返回后会自动更新。",
        ],
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
            "sniff_state": "loading",
            "sniff_msg": "正在向节点获取数据",
            "sniff_iface": "node-center",
            "sniff_idle_sec": 0,
            "sniff_last_pkt": "",
            "settings_path": "/settings",
            "viewer_loading": True,
            "viewer_loading_targets": target_names[:8],
            "viewer_loading_timeout_sec": 15,
        },
    }
