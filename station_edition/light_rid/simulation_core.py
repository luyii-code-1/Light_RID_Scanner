"""Ephemeral target simulation for demos and end-to-end UI testing.

This file is loaded into the assembled runtime namespace after ``process_core``.
Simulated records intentionally live only in ``state_table`` so they never pollute
the persisted RID history store.
"""

SIMULATION_MAX_TARGETS = 100
SIMULATION_TICK_SEC = 1.0
_simulation_lock = Lock()
_simulation_targets: dict[str, dict] = {}
_simulation_thread = None
_simulation_generation = 0
_simulation_started_wall_ts = None
_simulation_options: dict = {}


def _simulation_number(value, default: float, low: float, high: float) -> float:
    try:
        number = float(value)
    except (TypeError, ValueError):
        number = float(default)
    if not math.isfinite(number):
        number = float(default)
    return max(low, min(high, number))


def _simulation_center(body: dict) -> tuple[float, float]:
    base_lat = WEB_CFG.get("base_lat") if isinstance(WEB_CFG, dict) else None
    base_lon = WEB_CFG.get("base_lon") if isinstance(WEB_CFG, dict) else None
    lat = _simulation_number(body.get("center_lat"), base_lat or 30.0678192, -90.0, 90.0)
    lon = _simulation_number(body.get("center_lon"), base_lon or 121.1854406, -180.0, 180.0)
    return lat, lon


def _simulation_offset(center_lat: float, center_lon: float, north_m: float, east_m: float) -> tuple[float, float]:
    lat = center_lat + north_m / 111320.0
    lon_scale = max(0.01, math.cos(math.radians(center_lat)))
    lon = center_lon + east_m / (111320.0 * lon_scale)
    return round(lat, 7), round(lon, 7)


def _simulation_sn(index: int, generation: int) -> str:
    # RID list validation requires exactly 20 alphanumeric characters.
    return f"SIM{generation % 10000:04d}{index:013d}"


def _simulation_entry(sn: str, index: int, options: dict, now: float, now_wall: float) -> dict:
    phase = (2.0 * math.pi * index) / max(1, int(options["count"]))
    target = {
        "sn": sn,
        "index": index,
        "phase": phase,
        "direction": -1.0 if index % 2 else 1.0,
    }
    entry = {
        "sn": sn,
        "src_mac": f"02:53:49:4d:{(index // 256) % 256:02x}:{index % 256:02x}",
        "id_type": "simulation",
        "model": "模拟目标",
        "first_seen_ts": now,
        "last_seen_ts": now,
        "first_seen_wall_ts": now_wall,
        "last_seen_wall_ts": now_wall,
        "session_start_ts": now,
        "session_start_wall_ts": now_wall,
        "last_online_duration_sec": None,
        "last_print_ts": 0.0,
        "pl_sig": None,
        "rssi": -38 - (index % 24),
        "last_ch": 6,
        "ch_assumed": False,
        "lat": None,
        "lon": None,
        "alt": float(options["altitude_m"]) + (index % 5) * 3.0,
        "speed": float(options["speed_mps"]),
        "vspeed": 0.0,
        "pilot_lat": options["center_lat"],
        "pilot_lon": options["center_lon"],
        "pilot_alt": 0.0,
        "pilot_loc_type": "simulated",
        "pilot_loc_type_text": "模拟飞手位置",
        "scan_type": "rid",
        "firmware_type": "old",
        "uas_id": sn,
        "ssid": f"RID-SIM-{index + 1:02d}",
        "capture_type": "simulation",
        "last_capture_wall_ts": now_wall,
        "raw_packets": [],
        "tracks": _empty_track_store(),
        "track": [],
        "track_updated_wall_ts": None,
        "pkt_count": 0,
        "rx_avg": SIMULATION_TICK_SEC,
        "last_pkt_ts": now,
        "reported_lost": False,
        "_last_shown": None,
        "_first_printed": False,
        "_prev_lat": None,
        "_prev_lon": None,
        "move_dir": None,
        "move_dist": None,
        "_dirty": True,
        "_dirty_keys": set(),
        "_hl": {},
        "_simulation": True,
    }
    target["entry"] = entry
    return target


def _simulation_update_target(target: dict, options: dict, elapsed: float, now: float, now_wall: float) -> None:
    entry = target["entry"]
    radius = float(options["radius_m"])
    speed = float(options["speed_mps"])
    pattern = str(options["pattern"])
    phase = float(target["phase"])
    if pattern == "stationary" or speed <= 0.0:
        angle = phase
    elif pattern == "line":
        travel = ((elapsed * speed + target["index"] * radius / max(1, options["count"])) % max(1.0, radius * 4.0)) - radius * 2.0
        angle = phase
        north_m = math.cos(angle) * travel
        east_m = math.sin(angle) * travel
        lat, lon = _simulation_offset(options["center_lat"], options["center_lon"], north_m, east_m)
        heading = (math.degrees(angle) + (0.0 if target["direction"] > 0 else 180.0)) % 360.0
    else:
        angular_speed = speed / max(10.0, radius)
        angle = phase + target["direction"] * elapsed * angular_speed
    if pattern != "line":
        north_m = math.cos(angle) * radius
        east_m = math.sin(angle) * radius
        lat, lon = _simulation_offset(options["center_lat"], options["center_lon"], north_m, east_m)
        heading = (math.degrees(angle) + (90.0 if target["direction"] > 0 else -90.0)) % 360.0

    previous_lat, previous_lon = entry.get("lat"), entry.get("lon")
    entry.update({
        "_prev_lat": previous_lat,
        "_prev_lon": previous_lon,
        "lat": lat,
        "lon": lon,
        "last_seen_ts": now,
        "last_seen_wall_ts": now_wall,
        "last_capture_wall_ts": now_wall,
        "last_pkt_ts": now,
        "move_dir": round(heading, 1),
        "track_deg": round(heading, 1),
        "pkt_count": int(entry.get("pkt_count") or 0) + 1,
        "rssi": -40 - ((int(elapsed) + target["index"] * 3) % 20),
    })
    sample = {
        "sample_type": "aircraft",
        "track_type": "aircraft",
        "sn": entry["sn"],
        "uas_id": entry["sn"],
        "lat": lat,
        "lon": lon,
        "alt": entry["alt"],
        "timestamp_ms": int(now_wall * 1000.0),
        "receive_time_ms": int(now_wall * 1000.0),
        "source": "simulation",
        "coordinate_system": "WGS84",
    }
    # Simulation owns this canonical store, so mutate it directly. Re-sanitizing
    # the full trajectory on every tick would make long demos progressively
    # more expensive.
    tracks = entry.get("tracks")
    if not isinstance(tracks, dict):
        tracks = _empty_track_store()
    _track_store_append_sample(tracks, sample)
    entry["tracks"] = tracks
    entry["track"] = _track_store_primary(tracks, "aircraft")
    entry["track_updated_wall_ts"] = now_wall


def _simulation_loop(generation: int) -> None:
    while True:
        with _simulation_lock:
            if generation != _simulation_generation or not _simulation_targets:
                return
            targets = list(_simulation_targets.values())
            options = dict(_simulation_options)
            started = float(_simulation_started_wall_ts or time.time())
        now = time.monotonic()
        now_wall = time.time()
        elapsed = max(0.0, now_wall - started)
        duration = float(options.get("duration_sec") or 0.0)
        if duration > 0.0 and elapsed >= duration:
            simulation_stop()
            return
        with _simulation_lock:
            if generation != _simulation_generation:
                return
            with state_lock:
                for target in targets:
                    _simulation_update_target(target, options, elapsed, now, now_wall)
                    state_table[target["entry"]["sn"]] = target["entry"]
        time.sleep(SIMULATION_TICK_SEC)


def simulation_start(body: dict | None = None) -> dict:
    """Start or replace the active simulation scenario."""
    global _simulation_generation, _simulation_started_wall_ts, _simulation_options, _simulation_thread
    body = body if isinstance(body, dict) else {}
    try:
        count = int(body.get("count") or 3)
    except (TypeError, ValueError):
        return {"ok": False, "error": "count must be an integer"}
    if count < 1 or count > SIMULATION_MAX_TARGETS:
        return {"ok": False, "error": f"count must be between 1 and {SIMULATION_MAX_TARGETS}"}
    pattern = str(body.get("pattern") or "circle").strip().lower()
    if pattern not in ("circle", "line", "stationary"):
        return {"ok": False, "error": "pattern must be circle, line or stationary"}
    center_lat, center_lon = _simulation_center(body)
    options = {
        "count": count,
        "pattern": pattern,
        "center_lat": center_lat,
        "center_lon": center_lon,
        "radius_m": _simulation_number(body.get("radius_m"), 500.0, 10.0, 100000.0),
        "speed_mps": _simulation_number(body.get("speed_mps"), 12.0, 0.0, 100.0),
        "altitude_m": _simulation_number(body.get("altitude_m"), 120.0, -500.0, 10000.0),
        "duration_sec": _simulation_number(body.get("duration_sec"), 0.0, 0.0, 86400.0),
    }
    simulation_stop()
    now, now_wall = time.monotonic(), time.time()
    with _simulation_lock:
        _simulation_generation += 1
        generation = _simulation_generation
        _simulation_started_wall_ts = now_wall
        _simulation_options = options
        for index in range(count):
            sn = _simulation_sn(index + 1, generation)
            _simulation_targets[sn] = _simulation_entry(sn, index, options, now, now_wall)
        targets = list(_simulation_targets.values())
    with state_lock:
        for target in targets:
            _simulation_update_target(target, options, 0.0, now, now_wall)
            state_table[target["entry"]["sn"]] = target["entry"]
    _simulation_thread = Thread(target=_simulation_loop, args=(generation,), daemon=True, name="rid-simulation")
    _simulation_thread.start()
    return simulation_status()


def simulation_stop() -> dict:
    """Stop simulation and remove all ephemeral targets from the live table."""
    global _simulation_generation, _simulation_started_wall_ts, _simulation_options
    with _simulation_lock:
        sn_list = list(_simulation_targets)
        _simulation_targets.clear()
        _simulation_generation += 1
        _simulation_started_wall_ts = None
        _simulation_options = {}
    with state_lock:
        for sn in sn_list:
            entry = state_table.get(sn)
            if isinstance(entry, dict) and entry.get("_simulation"):
                state_table.pop(sn, None)
            hist = history_table.get(sn)
            if isinstance(hist, dict) and hist.get("_simulation"):
                history_table.pop(sn, None)
    return {"ok": True, "running": False, "count": 0, "removed": len(sn_list), "targets": []}


def simulation_status() -> dict:
    with _simulation_lock:
        targets = list(_simulation_targets.values())
        started = _simulation_started_wall_ts
        options = dict(_simulation_options)
    now_wall = time.time()
    return {
        "ok": True,
        "running": bool(targets),
        "count": len(targets),
        "started_at": _fmt_wall_ts(started),
        "elapsed_sec": round(max(0.0, now_wall - started), 1) if started else 0.0,
        "options": options,
        "targets": [target["entry"]["sn"] for target in targets],
    }
