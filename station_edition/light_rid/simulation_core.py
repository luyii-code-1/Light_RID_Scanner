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
_simulation_tx_stats: dict = {}


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
    lat_value = body.get("center_lat")
    lon_value = body.get("center_lon")
    if lat_value in (None, ""):
        lat_value = base_lat
    if lon_value in (None, ""):
        lon_value = base_lon
    if lat_value in (None, "") or lon_value in (None, ""):
        raise ValueError("base station coordinates are not configured")
    lat = _simulation_number(lat_value, 0.0, -90.0, 90.0)
    lon = _simulation_number(lon_value, 0.0, -180.0, 180.0)
    return lat, lon


def _simulation_iface() -> str:
    basic = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
    iface = str((basic or {}).get("iface") or "").strip()
    return str(_hw_safe_iface(iface) or "") if iface else ""


def _simulation_odid_messages(entry: dict) -> list[bytes]:
    """Encode a target as standard 25-byte OpenDroneID messages."""
    sn = str(entry.get("sn") or "")[:20].encode("ascii", errors="ignore").ljust(20, b"\x00")
    basic = bytearray(ODID_MSG_SIZE)
    basic[0], basic[1], basic[2:22] = MSG_TYPE_BASIC_ID << 4, 1, sn
    location = bytearray(ODID_MSG_SIZE)
    location[0] = MSG_TYPE_LOCATION << 4
    location[3] = int(round(max(0.0, min(63.75, float(entry.get("speed") or 0.0))) / 0.25))
    struct.pack_into("<b", location, 4, int(round(max(-62.0, min(62.0, float(entry.get("vspeed") or 0.0))) / 0.5)))
    struct.pack_into("<i", location, 5, int(round(float(entry["lat"]) * 1e7)))
    struct.pack_into("<i", location, 9, int(round(float(entry["lon"]) * 1e7)))
    altitude = max(1, min(0xFFFF, int(round((float(entry.get("alt") or 0.0) + 1000.0) / 0.5))))
    struct.pack_into("<H", location, 13, altitude)
    struct.pack_into("<H", location, 15, altitude)
    system = bytearray(ODID_MSG_SIZE)
    system[0], system[1] = MSG_TYPE_SYSTEM << 4, 3
    struct.pack_into("<i", system, 2, int(round(float(entry["pilot_lat"]) * 1e7)))
    struct.pack_into("<i", system, 6, int(round(float(entry["pilot_lon"]) * 1e7)))
    return [bytes(basic), bytes(location), bytes(system)]


def _simulation_wifi_frame(entry: dict):
    src = str(entry.get("src_mac") or "02:53:49:4d:00:01")
    frame = RadioTap() / Dot11(type=0, subtype=8, addr1="ff:ff:ff:ff:ff:ff", addr2=src, addr3=src)
    frame = frame / Dot11Beacon(cap="ESS") / Dot11Elt(ID="SSID", info=str(entry.get("ssid") or "RID-SIM"))
    for message in _simulation_odid_messages(entry):
        frame = frame / Dot11Elt(ID=221, info=ODID_OUI + b"\x00" + message)
    return frame


def _simulation_transmit(targets: list[dict], iface: str) -> bool:
    try:
        sender = conf.L2socket(iface=iface)
        try:
            for target in targets:
                sender.send(_simulation_wifi_frame(target["entry"]))
                _simulation_tx_stats["sent"] = int(_simulation_tx_stats.get("sent") or 0) + 1
            _simulation_tx_stats["last_error"] = ""
        finally:
            sender.close()
        return True
    except Exception as exc:
        _simulation_tx_stats["failed"] = int(_simulation_tx_stats.get("failed") or 0) + len(targets)
        _simulation_tx_stats["last_error"] = str(exc)
        _log(f"[WARN] simulation transmit failed on {iface}: {exc}")
        return False


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
                    if options.get("transport") == "memory":
                        state_table[target["entry"]["sn"]] = target["entry"]
            if options.get("transport") == "network":
                _simulation_transmit(targets, str(options.get("iface") or ""))
        time.sleep(SIMULATION_TICK_SEC)


def simulation_start(body: dict | None = None) -> dict:
    """Start or replace the active simulation scenario."""
    global _simulation_generation, _simulation_started_wall_ts, _simulation_options, _simulation_thread, _simulation_tx_stats
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
    try:
        center_lat, center_lon = _simulation_center(body)
    except ValueError as exc:
        return {"ok": False, "error": str(exc)}
    transport = str(body.get("transport") or "network").strip().lower()
    if transport not in ("network", "memory"):
        return {"ok": False, "error": "transport must be network or memory"}
    iface = _simulation_iface() if transport == "network" else ""
    if transport == "network" and not iface:
        return {"ok": False, "error": "no configured scan interface"}
    if transport == "network" and not SCAPY_AVAILABLE:
        return {"ok": False, "error": "network simulation requires scapy"}
    options = {
        "count": count,
        "pattern": pattern,
        "center_lat": center_lat,
        "center_lon": center_lon,
        "radius_m": _simulation_number(body.get("radius_m"), 500.0, 10.0, 100000.0),
        "speed_mps": _simulation_number(body.get("speed_mps"), 12.0, 0.0, 100.0),
        "altitude_m": _simulation_number(body.get("altitude_m"), 120.0, -500.0, 10000.0),
        "duration_sec": _simulation_number(body.get("duration_sec"), 0.0, 0.0, 86400.0),
        "transport": transport,
        "iface": iface,
    }
    simulation_stop()
    now, now_wall = time.monotonic(), time.time()
    with _simulation_lock:
        _simulation_generation += 1
        generation = _simulation_generation
        _simulation_started_wall_ts = now_wall
        _simulation_options = options
        _simulation_tx_stats = {"iface": iface, "sent": 0, "failed": 0, "last_error": ""}
        for index in range(count):
            sn = _simulation_sn(index + 1, generation)
            _simulation_targets[sn] = _simulation_entry(sn, index, options, now, now_wall)
        targets = list(_simulation_targets.values())
    with state_lock:
        for target in targets:
            _simulation_update_target(target, options, 0.0, now, now_wall)
            if transport == "memory":
                state_table[target["entry"]["sn"]] = target["entry"]
    if transport == "network":
        if not _simulation_transmit(targets, iface):
            error = str(_simulation_tx_stats.get("last_error") or "network transmit failed")
            simulation_stop()
            return {"ok": False, "error": f"failed to transmit on {iface}: {error}"}
    _simulation_thread = Thread(target=_simulation_loop, args=(generation,), daemon=True, name="rid-simulation")
    _simulation_thread.start()
    return simulation_status()


def simulation_stop() -> dict:
    """Stop simulation and remove all ephemeral targets from the live table."""
    global _simulation_generation, _simulation_started_wall_ts, _simulation_options, _simulation_tx_stats
    with _simulation_lock:
        sn_list = list(_simulation_targets)
        _simulation_targets.clear()
        _simulation_generation += 1
        _simulation_started_wall_ts = None
        _simulation_options = {}
        _simulation_tx_stats = {}
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
        "transmit": dict(_simulation_tx_stats),
        "targets": [target["entry"]["sn"] for target in targets],
    }
