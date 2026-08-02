use crate::state::{AppState, DroneEntry, unix_now};
use serde_json::{Value, json};

pub fn start(state: &AppState, body: Value) -> Value {
    let count = body
        .get("count")
        .and_then(Value::as_u64)
        .unwrap_or(3)
        .clamp(1, 100) as usize;
    let pattern = body
        .get("pattern")
        .and_then(Value::as_str)
        .unwrap_or("circle");
    if !matches!(pattern, "circle" | "line" | "stationary") {
        return json!({"ok": false, "error": "pattern must be circle, line or stationary"});
    }
    let center_lat = body
        .get("center_lat")
        .and_then(Value::as_f64)
        .unwrap_or(30.0678192);
    let center_lon = body
        .get("center_lon")
        .and_then(Value::as_f64)
        .unwrap_or(121.1854406);
    let radius_m = body
        .get("radius_m")
        .and_then(Value::as_f64)
        .unwrap_or(500.0)
        .clamp(10.0, 100000.0);
    let speed = body
        .get("speed_mps")
        .and_then(Value::as_f64)
        .unwrap_or(12.0)
        .clamp(0.0, 100.0);
    let now = unix_now();
    let mut drones = state.drones.write();
    drones.retain(|_, entry| !entry.simulation);
    for idx in 0..count {
        let angle = std::f64::consts::TAU * idx as f64 / count.max(1) as f64;
        let (lat, lon) = offset(
            center_lat,
            center_lon,
            angle.cos() * radius_m,
            angle.sin() * radius_m,
        );
        let sn = format!("SIM{:04}{:013}", (now as u64) % 10000, idx + 1);
        drones.insert(sn.clone(), DroneEntry {
            sn: sn.clone(),
            src_mac: format!("02:53:49:4d:{:02x}:{:02x}", (idx / 256) % 256, idx % 256),
            model: "模拟目标".to_string(),
            lat: Some(lat),
            lon: Some(lon),
            alt: Some(120.0 + (idx % 5) as f64 * 3.0),
            speed: Some(speed),
            rssi: Some(-38 - (idx % 24) as i32),
            last_ch: Some(6),
            capture_type: "simulation".to_string(),
            firmware_type: "old".to_string(),
            scan_type: "rid".to_string(),
            pkt_count: 1,
            last_seen_wall_ts: now,
            tracks: json!({"aircraft":[{"track_type":"aircraft","sample_type":"aircraft","sn":sn,"lat":lat,"lon":lon,"timestamp_ms":(now*1000.0) as i64,"receive_time_ms":(now*1000.0) as i64,"source":"simulation","coordinate_system":"WGS84"}],"operator":[],"last_aircraft":null,"last_operator":null}),
            simulation: true,
        });
    }
    status(state)
}

pub fn stop(state: &AppState) -> Value {
    let mut drones = state.drones.write();
    let before = drones.len();
    drones.retain(|_, entry| !entry.simulation);
    json!({"ok": true, "running": false, "count": 0, "removed": before - drones.len(), "targets": []})
}

pub fn status(state: &AppState) -> Value {
    let drones = state.drones.read();
    let targets: Vec<String> = drones
        .values()
        .filter(|d| d.simulation)
        .map(|d| d.sn.clone())
        .collect();
    json!({"ok": true, "running": !targets.is_empty(), "count": targets.len(), "targets": targets})
}

fn offset(center_lat: f64, center_lon: f64, north_m: f64, east_m: f64) -> (f64, f64) {
    let lat = center_lat + north_m / 111_320.0;
    let lon_scale = center_lat.to_radians().cos().max(0.01);
    let lon = center_lon + east_m / (111_320.0 * lon_scale);
    (
        (lat * 10_000_000.0).round() / 10_000_000.0,
        (lon * 10_000_000.0).round() / 10_000_000.0,
    )
}
