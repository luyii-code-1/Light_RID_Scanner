use anyhow::Result;
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    fs,
    path::PathBuf,
    sync::Arc,
    time::{SystemTime, UNIX_EPOCH},
};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Config {
    #[serde(default)]
    pub basic: Value,
    #[serde(default)]
    pub notify: Value,
    #[serde(default)]
    pub web: Value,
    #[serde(default)]
    pub ap: Value,
    #[serde(default)]
    pub auth: Value,
    #[serde(default)]
    pub api: Value,
    #[serde(default)]
    pub metrics: Value,
    #[serde(default)]
    pub network_bindings: Value,
}

impl Default for Config {
    fn default() -> Self {
        serde_json::from_str(include_str!("../../station_edition/config.example.json"))
            .unwrap_or_else(|_| Config {
                basic: json!({}),
                notify: json!({}),
                web: json!({}),
                ap: json!({}),
                auth: json!({"enabled": false}),
                api: json!({"enabled": false}),
                metrics: json!({"enabled": false}),
                network_bindings: json!({}),
            })
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DroneEntry {
    pub sn: String,
    #[serde(default)]
    pub src_mac: String,
    #[serde(default)]
    pub model: String,
    #[serde(default)]
    pub lat: Option<f64>,
    #[serde(default)]
    pub lon: Option<f64>,
    #[serde(default)]
    pub alt: Option<f64>,
    #[serde(default)]
    pub speed: Option<f64>,
    #[serde(default)]
    pub rssi: Option<i32>,
    #[serde(default)]
    pub last_ch: Option<u16>,
    #[serde(default)]
    pub capture_type: String,
    #[serde(default)]
    pub firmware_type: String,
    #[serde(default)]
    pub scan_type: String,
    #[serde(default)]
    pub pkt_count: u64,
    #[serde(default)]
    pub last_seen_wall_ts: f64,
    #[serde(default)]
    pub tracks: Value,
    #[serde(default)]
    pub simulation: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Notification {
    pub id: String,
    pub ts: f64,
    pub text: String,
    pub kind: String,
    pub source: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct CaptureStatus {
    pub running: bool,
    pub iface: String,
    pub channel: Option<u16>,
    pub frames: u64,
    pub management_frames: u64,
    pub rid_packets: u64,
    pub parse_errors: u64,
    pub last_packet_ts: Option<f64>,
    pub last_rid_ts: Option<f64>,
    pub last_error: String,
}

#[derive(Debug)]
pub struct AppInner {
    pub config_path: PathBuf,
    pub history_path: PathBuf,
    pub config: RwLock<Config>,
    pub drones: RwLock<BTreeMap<String, DroneEntry>>,
    pub history: RwLock<BTreeMap<String, Value>>,
    pub runtime_logs: RwLock<Vec<String>>,
    pub scan_logs: RwLock<Vec<String>>,
    pub notifications: RwLock<Vec<Notification>>,
    pub capture: RwLock<CaptureStatus>,
}

pub type AppState = Arc<AppInner>;

pub fn load(config_path: &str, history_path: &str) -> Result<AppState> {
    let cfg_path = PathBuf::from(config_path);
    let config = if cfg_path.is_file() {
        serde_json::from_slice(&fs::read(&cfg_path)?)?
    } else {
        Config::default()
    };
    Ok(Arc::new(AppInner {
        config_path: cfg_path,
        history_path: PathBuf::from(history_path),
        config: RwLock::new(config),
        drones: RwLock::new(BTreeMap::new()),
        history: RwLock::new(BTreeMap::new()),
        runtime_logs: RwLock::new(Vec::new()),
        scan_logs: RwLock::new(Vec::new()),
        notifications: RwLock::new(Vec::new()),
        capture: RwLock::new(CaptureStatus::default()),
    }))
}

pub trait AppStateExt {
    fn log_info<S: Into<String>>(&self, text: S);
    fn notification_add<S: Into<String>>(&self, text: S, kind: &str);
    fn snapshot(&self, lightweight: bool) -> Value;
}

impl AppStateExt for AppState {
    fn log_info<S: Into<String>>(&self, text: S) {
        let line = text.into();
        tracing::info!("{line}");
        let mut logs = self.runtime_logs.write();
        logs.push(format!("[{}] {line}", wall_ts_string()));
        if logs.len() > 4000 {
            let drain = logs.len() - 4000;
            logs.drain(0..drain);
        }
    }

    fn notification_add<S: Into<String>>(&self, text: S, kind: &str) {
        let mut items = self.notifications.write();
        items.push(Notification {
            id: Uuid::new_v4().to_string(),
            ts: unix_now(),
            text: text.into(),
            kind: kind.to_string(),
            source: "server".to_string(),
        });
        if items.len() > 200 {
            let drain = items.len() - 200;
            items.drain(0..drain);
        }
    }

    fn snapshot(&self, lightweight: bool) -> Value {
        let drones: Vec<Value> = self.drones.read().values().map(|d| json!(d)).collect();
        json!({
            "ok": true,
            "ts": unix_now(),
            "version": crate::APP_RELEASE_VERSION,
            "drones": drones,
            "count": drones.len(),
            "history_count": self.history.read().len(),
            "capture": self.capture.read().clone(),
            "lightweight": lightweight,
        })
    }
}

pub fn unix_now() -> f64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs_f64())
        .unwrap_or_default()
}

pub fn wall_ts_string() -> String {
    chrono::Local::now().format("%Y-%m-%d %H:%M:%S").to_string()
}
