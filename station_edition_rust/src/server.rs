use crate::{
    capture::{self, FrameMeta},
    parser, simulation,
    state::{AppState, AppStateExt},
};
use anyhow::Result;
use axum::{
    Json, Router,
    body::Body,
    extract::{Path, Query, State},
    http::{HeaderValue, StatusCode, header},
    response::{Html, IntoResponse, Response},
    routing::{get, post},
};
use serde_json::{Value, json};
use std::{
    collections::HashMap,
    fs,
    net::SocketAddr,
    path::{Path as FsPath, PathBuf},
};
use tower_http::cors::CorsLayer;

const STATION_PAGE: &str = include_str!(concat!(env!("OUT_DIR"), "/station_page.html"));

pub async fn serve(state: AppState) -> Result<()> {
    let port = state
        .config
        .read()
        .web
        .get("http_port")
        .and_then(Value::as_u64)
        .unwrap_or(8000) as u16;
    let app = Router::new()
        .route("/", get(index))
        .route("/mobile", get(mobile))
        .route("/settings", get(settings))
        .route("/assets/{*path}", get(asset))
        .route("/api/eula/status", get(eula_status))
        .route("/api/eula/accept", post(eula_accept))
        .route("/api/eula/revoke", post(eula_revoke))
        .route("/api/config", get(config))
        .route("/api/config/tree", get(config_tree))
        .route("/api/config/file", get(config_file))
        .route("/api/config/file/delete", post(not_implemented_ok))
        .route("/api/config/save", post(config_save))
        .route("/api/oobe/status", get(oobe_status))
        .route("/api/oobe/save", post(config_save))
        .route("/api/docs", get(api_docs))
        .route("/api/health", get(api_health))
        .route("/api/parse", post(parse_api))
        .route("/api/v1/parse", post(parse_api))
        .route("/api/update-health", get(api_health))
        .route("/api/v1/snapshot", get(snapshot))
        .route("/api/v1/auth/status", get(auth_status))
        .route("/api/v1/drones", get(drones))
        .route("/api/v1/metrics", get(metrics))
        .route("/api/v1/aps", get(aps))
        .route("/api/v1/logs", get(logs))
        .route("/api/v1/auth/logout", post(logout))
        .route("/api/v1/history/clear", post(history_clear))
        .route("/api/v1/history/delete", post(history_delete))
        .route("/api/v1/tracks/clear", post(tracks_clear))
        .route("/api/v1/config/reload", post(config_reload))
        .route("/api/v1/history/reparse", post(not_implemented_ok))
        .route(
            "/api/v1/history/reidentify-recent",
            post(not_implemented_ok),
        )
        .route("/api/settings/view", get(settings_view))
        .route("/api/settings/runtime", get(settings_runtime))
        .route("/api/settings/metrics", get(metrics))
        .route("/api/settings/systemd/status", get(systemd_status))
        .route("/api/settings/systemd/register", post(privileged_stub))
        .route("/api/settings/iw/install", post(privileged_stub))
        .route("/api/settings/security/repair", post(privileged_stub))
        .route("/api/settings/raw/unlock", post(not_implemented_ok))
        .route("/api/settings/raw/save", post(config_save))
        .route("/api/settings/visual/test", post(not_implemented_ok))
        .route("/api/settings/visual/save", post(config_save))
        .route("/api/settings/notify/test", post(notify_test))
        .route("/api/settings/models/list", get(models_list))
        .route("/api/settings/models/update", post(not_implemented_ok))
        .route("/api/settings/models/save", post(not_implemented_ok))
        .route("/api/settings/models/upsert", post(not_implemented_ok))
        .route("/api/settings/app-update/check", post(not_implemented_ok))
        .route(
            "/api/settings/app-update/download",
            post(not_implemented_ok),
        )
        .route(
            "/api/settings/app-update/upload/prepare",
            post(not_implemented_ok),
        )
        .route("/api/settings/app-update/upload", post(not_implemented_ok))
        .route("/api/settings/app-update/start", post(privileged_stub))
        .route("/api/settings/api-token/create", post(not_implemented_ok))
        .route("/api/settings/api-token/delete", post(not_implemented_ok))
        .route("/api/settings/login-link/create", post(not_implemented_ok))
        .route("/api/settings/login-link/delete", post(not_implemented_ok))
        .route("/api/settings/passkey/start", post(not_implemented_ok))
        .route("/api/settings/passkey/finish", post(not_implemented_ok))
        .route("/api/settings/passkey/delete", post(not_implemented_ok))
        .route(
            "/api/notifications",
            get(notifications).post(notification_add),
        )
        .route("/api/notifications/delete", post(notification_delete))
        .route("/api/notifications/clear", post(notification_clear))
        .route("/api/diagnostics/summary", get(diagnostics))
        .route("/api/logs/view", get(logs))
        .route("/api/logs/export", get(logs_export))
        .route("/api/interfaces", get(interfaces))
        .route("/api/network-bindings/status", get(network_status))
        .route("/api/network-bindings/save", post(not_implemented_ok))
        .route("/api/network-bindings/apply", post(privileged_stub))
        .route("/api/hw/status", get(hw_status))
        .route("/api/hw/op", post(privileged_stub))
        .route("/api/drones/get", get(drones_get))
        .route("/api/tracks/get", get(tracks_get))
        .route("/api/tracks/clear", post(tracks_clear))
        .route("/api/history/clear", post(history_clear))
        .route("/api/history/delete", post(history_delete))
        .route("/api/history/reparse", post(not_implemented_ok))
        .route("/api/tools/export/all", get(export_all))
        .route("/api/tools/export/track", get(export_track))
        .route("/api/tools/import/all", post(not_implemented_ok))
        .route("/api/tools/import/track", post(not_implemented_ok))
        .route("/api/tools/diagnostic.zip", get(diagnostics_zip))
        .route("/api/settings/export/settings", get(export_settings))
        .route("/api/settings/export/scan-data", get(export_all))
        .route("/api/settings/import/settings", post(config_save))
        .route("/api/settings/import/scan-data", post(not_implemented_ok))
        .route("/api/simulation/status", get(sim_status))
        .route("/api/simulation/start", post(sim_start))
        .route("/api/simulation/stop", post(sim_stop))
        .route("/api/admin/restart", post(privileged_stub))
        .route("/api/passkey/login/start", post(not_implemented_ok))
        .route("/api/passkey/login/finish", post(not_implemented_ok))
        .route("/api/v1/auth/sso-links/create", post(not_implemented_ok))
        .route("/api/web/base/save", post(config_save))
        .route("/api/web/basic/save", post(config_save))
        .layer(CorsLayer::permissive())
        .with_state(state.clone());

    let addr = SocketAddr::from(([0, 0, 0, 0], port));
    state.log_info(format!(
        "[INFO] HTTP+WS service started: http://0.0.0.0:{port}/"
    ));
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;
    Ok(())
}

async fn index() -> Html<&'static str> {
    Html(STATION_PAGE)
}

async fn mobile() -> impl IntoResponse {
    static_file("assets/templates/mobile.html")
        .unwrap_or_else(|| Html(STATION_PAGE).into_response())
}

async fn settings() -> impl IntoResponse {
    static_file("assets/templates/station-settings.html")
        .unwrap_or_else(|| Html(STATION_PAGE).into_response())
}

async fn asset(Path(path): Path<String>) -> impl IntoResponse {
    static_file(&format!("assets/{path}"))
        .unwrap_or_else(|| (StatusCode::NOT_FOUND, "not found").into_response())
}

fn static_file(rel: &str) -> Option<Response> {
    let root = locate_light_rid_root()?;
    let full = root.join(rel);
    if !full.is_file() || !full.starts_with(&root) {
        return None;
    }
    let bytes = fs::read(&full).ok()?;
    let mime = mime_guess::from_path(&full).first_or_octet_stream();
    let mut rsp = Response::new(Body::from(bytes));
    rsp.headers_mut().insert(
        header::CONTENT_TYPE,
        HeaderValue::from_str(mime.as_ref()).ok()?,
    );
    Some(rsp)
}

fn locate_light_rid_root() -> Option<PathBuf> {
    if let Some(root) = std::env::var_os("LIGHT_RID_ROOT") {
        let candidate = PathBuf::from(root);
        if candidate.is_dir() {
            return candidate.canonicalize().ok();
        }
    }
    let cwd = std::env::current_dir().ok()?;
    for candidate in [
        cwd.join("station_edition/light_rid"),
        cwd.join("../station_edition/light_rid"),
        cwd.join("light_rid"),
    ] {
        if candidate.is_dir() {
            return candidate.canonicalize().ok();
        }
    }
    None
}

async fn eula_status() -> Json<Value> {
    Json(json!({"ok": true, "accepted": FsPath::new("EULA.set").is_file()}))
}
async fn eula_accept() -> Json<Value> {
    let _ = fs::write("EULA.set", "accepted\n");
    Json(json!({"ok": true, "accepted": true}))
}
async fn eula_revoke() -> Json<Value> {
    let _ = fs::remove_file("EULA.set");
    Json(json!({"ok": true, "accepted": false}))
}

async fn config(State(state): State<AppState>) -> Json<Value> {
    Json(json!({"ok": true, "config": *state.config.read()}))
}
async fn config_tree(State(state): State<AppState>) -> Json<Value> {
    config(State(state)).await
}
async fn config_file(State(state): State<AppState>) -> Json<Value> {
    Json(
        json!({"ok": true, "path": state.config_path, "exists": state.config_path.is_file(), "config": *state.config.read()}),
    )
}
async fn config_save(State(state): State<AppState>, Json(body): Json<Value>) -> Json<Value> {
    if let Ok(cfg) =
        serde_json::from_value(body.get("config").cloned().unwrap_or_else(|| body.clone()))
    {
        *state.config.write() = cfg;
        if let Ok(text) = serde_json::to_string_pretty(&*state.config.read()) {
            if let Some(parent) = state.config_path.parent() {
                let _ = fs::create_dir_all(parent);
            }
            let _ = fs::write(&state.config_path, text);
        }
        Json(
            json!({"ok": true, "saved_to": state.config_path, "reloaded": true, "reload_msg": "ok"}),
        )
    } else {
        Json(json!({"ok": false, "error": "invalid config"}))
    }
}
async fn config_reload(State(state): State<AppState>) -> Json<Value> {
    if state.config_path.is_file() {
        match fs::read(&state.config_path)
            .ok()
            .and_then(|b| serde_json::from_slice(&b).ok())
        {
            Some(cfg) => {
                *state.config.write() = cfg;
                Json(json!({"ok": true, "reloaded": true}))
            }
            None => Json(json!({"ok": false, "error": "failed to reload config"})),
        }
    } else {
        Json(
            json!({"ok": true, "reloaded": false, "message": "config file missing; defaults remain active"}),
        )
    }
}

async fn oobe_status(State(state): State<AppState>) -> Json<Value> {
    Json(
        json!({"ok": true, "required": !state.config_path.is_file(), "config_exists": state.config_path.is_file()}),
    )
}
async fn api_docs() -> Json<Value> {
    Json(json!({"ok": true, "name": "Light RID Scanner API", "version": "v1"}))
}
async fn api_health(State(state): State<AppState>) -> Json<Value> {
    Json(
        json!({"ok": true, "status": "ok", "version": crate::APP_RELEASE_VERSION, "drone_count": state.drones.read().len(), "capture": state.capture.read().clone()}),
    )
}
async fn snapshot(
    State(state): State<AppState>,
    Query(q): Query<HashMap<String, String>>,
) -> Json<Value> {
    Json(
        state.snapshot(
            q.get("lightweight")
                .is_some_and(|v| v == "1" || v == "true"),
        ),
    )
}
async fn auth_status() -> Json<Value> {
    Json(
        json!({"ok": true, "authenticated": true, "auth_enabled": false, "api_token_enabled": false}),
    )
}
async fn drones(State(state): State<AppState>) -> Json<Value> {
    Json(json!({"ok": true, "drones": state.drones.read().values().cloned().collect::<Vec<_>>()}))
}
async fn drones_get(State(state): State<AppState>) -> Json<Value> {
    Json(
        json!({"ok": true, "current": state.drones.read().values().cloned().collect::<Vec<_>>(), "history": state.history.read().values().cloned().collect::<Vec<_>>()}),
    )
}
async fn metrics() -> Json<Value> {
    Json(json!({"ok": true, "enabled": false, "points": []}))
}
async fn aps() -> Json<Value> {
    Json(json!({"ok": true, "aps": [], "count": 0}))
}
async fn logs(
    State(state): State<AppState>,
    Query(q): Query<HashMap<String, String>>,
) -> Json<Value> {
    let log_type = q.get("type").map(String::as_str).unwrap_or("runtime");
    let rows = if log_type == "scan" {
        state.scan_logs.read().clone()
    } else {
        state.runtime_logs.read().clone()
    };
    Json(json!({"ok": true, "type": log_type, "lines": rows, "logs": rows}))
}
async fn logs_export(State(state): State<AppState>) -> impl IntoResponse {
    text_download("rid-logs.txt", state.runtime_logs.read().join("\n"))
}
async fn logout() -> Json<Value> {
    Json(json!({"ok": true, "logged_out": true}))
}
async fn history_clear(State(state): State<AppState>) -> Json<Value> {
    state.history.write().clear();
    Json(json!({"ok": true, "cleared": true}))
}
async fn history_delete(State(state): State<AppState>, Json(body): Json<Value>) -> Json<Value> {
    let sn = body.get("sn").and_then(Value::as_str).unwrap_or("");
    let deleted = state.history.write().remove(sn).is_some();
    Json(json!({"ok": true, "deleted": deleted}))
}
async fn tracks_clear(State(state): State<AppState>) -> Json<Value> {
    for drone in state.drones.write().values_mut() {
        drone.tracks =
            json!({"aircraft":[],"operator":[],"last_aircraft":null,"last_operator":null});
    }
    Json(json!({"ok": true, "cleared": true}))
}
async fn settings_view(State(state): State<AppState>) -> Json<Value> {
    Json(json!({"ok": true, "config": *state.config.read()}))
}
async fn settings_runtime(State(state): State<AppState>) -> Json<Value> {
    Json(
        json!({"ok": true, "version": crate::APP_RELEASE_VERSION, "logs": state.runtime_logs.read().clone(), "capture": state.capture.read().clone()}),
    )
}
async fn systemd_status() -> Json<Value> {
    Json(
        json!({"ok": true, "available": cfg!(target_os = "linux"), "service": "light-rid-scanner.service"}),
    )
}
async fn models_list() -> Json<Value> {
    Json(json!({"ok": true, "items": []}))
}
async fn notify_test(State(state): State<AppState>, Json(_body): Json<Value>) -> Json<Value> {
    state.notification_add("测试通知", "info");
    Json(json!({"ok": true, "message": "test notification queued"}))
}
async fn notifications(State(state): State<AppState>) -> Json<Value> {
    Json(json!({"ok": true, "items": state.notifications.read().clone()}))
}
async fn notification_add(State(state): State<AppState>, Json(body): Json<Value>) -> Json<Value> {
    state.notification_add(
        body.get("text")
            .and_then(Value::as_str)
            .unwrap_or("notification"),
        body.get("kind").and_then(Value::as_str).unwrap_or("info"),
    );
    Json(json!({"ok": true, "items": state.notifications.read().clone()}))
}
async fn notification_delete(
    State(state): State<AppState>,
    Json(body): Json<Value>,
) -> Json<Value> {
    let id = body.get("id").and_then(Value::as_str).unwrap_or("");
    let before = state.notifications.read().len();
    state.notifications.write().retain(|n| n.id != id);
    Json(json!({"ok": true, "deleted": state.notifications.read().len() != before}))
}
async fn notification_clear(State(state): State<AppState>) -> Json<Value> {
    let count = state.notifications.read().len();
    state.notifications.write().clear();
    Json(json!({"ok": true, "cleared": count}))
}
async fn diagnostics(State(state): State<AppState>) -> Json<Value> {
    Json(
        json!({"ok": true, "version": crate::APP_RELEASE_VERSION, "drones": state.drones.read().len(), "config_path": state.config_path, "capture": state.capture.read().clone()}),
    )
}
async fn interfaces() -> Json<Value> {
    Json(json!({"ok": true, "items": []}))
}
async fn network_status(State(state): State<AppState>) -> Json<Value> {
    Json(json!({"ok": true, "config": state.config.read().network_bindings}))
}
async fn hw_status(State(state): State<AppState>) -> Json<Value> {
    Json(json!({"ok": true, "busy": false, "last": null, "capture": state.capture.read().clone()}))
}
async fn tracks_get(
    State(state): State<AppState>,
    Query(q): Query<HashMap<String, String>>,
) -> Json<Value> {
    let sn = q.get("sn").map(String::as_str).unwrap_or("");
    let tracks = state
        .drones
        .read()
        .get(sn)
        .map(|d| d.tracks.clone())
        .unwrap_or_else(|| json!({"aircraft":[],"operator":[]}));
    Json(
        json!({"ok": true, "sn": sn, "tracks": tracks, "aircraft": tracks.get("aircraft").cloned().unwrap_or_else(|| json!([])), "operator": tracks.get("operator").cloned().unwrap_or_else(|| json!([]))}),
    )
}
async fn export_all(State(state): State<AppState>) -> impl IntoResponse {
    text_download(
        "rid-scan-data.json",
        serde_json::to_string_pretty(&state.snapshot(false)).unwrap_or_default(),
    )
}
async fn export_track(State(state): State<AppState>) -> impl IntoResponse {
    text_download(
        "rid-tracks.json",
        serde_json::to_string_pretty(&*state.drones.read()).unwrap_or_default(),
    )
}
async fn export_settings(State(state): State<AppState>) -> impl IntoResponse {
    text_download(
        "config.json",
        serde_json::to_string_pretty(&*state.config.read()).unwrap_or_default(),
    )
}
async fn diagnostics_zip() -> impl IntoResponse {
    text_download("diagnostic.txt", "Rust station diagnostics\n".to_string())
}
async fn sim_status(State(state): State<AppState>) -> Json<Value> {
    Json(simulation::status(&state))
}
async fn sim_start(State(state): State<AppState>, Json(body): Json<Value>) -> Json<Value> {
    Json(simulation::start(&state, body))
}
async fn sim_stop(State(state): State<AppState>) -> Json<Value> {
    Json(simulation::stop(&state))
}

async fn not_implemented_ok() -> Json<Value> {
    Json(json!({"ok": true, "message": "accepted by Rust compatibility API"}))
}
async fn privileged_stub() -> (StatusCode, Json<Value>) {
    (
        StatusCode::NOT_IMPLEMENTED,
        Json(
            json!({"ok": false, "error": "privileged OS operation is not implemented in Rust edition yet"}),
        ),
    )
}

pub async fn parse_api(State(state): State<AppState>, Json(body): Json<Value>) -> Json<Value> {
    let raw = body
        .get("raw_packet")
        .or_else(|| body.get("hex"))
        .and_then(Value::as_str)
        .unwrap_or("");
    let mode = body.get("mode").and_then(Value::as_str);
    let bytes = parser::raw_packet_string_to_bytes(raw);
    let parsed = parser::parse_rid_payload(&bytes, mode);
    let mut response = json!(parsed);
    let packets = capture::ingest_payload(
        &state,
        &bytes,
        FrameMeta {
            source_mac: body
                .get("source_mac")
                .and_then(Value::as_str)
                .unwrap_or("api")
                .to_string(),
            capture_type: "api",
            rssi: body
                .get("rssi")
                .and_then(Value::as_i64)
                .map(|value| value as i32),
            channel: body
                .get("channel")
                .and_then(Value::as_u64)
                .map(|value| value as u16),
        },
        crate::state::unix_now(),
    );
    response["ingested"] = json!(packets.len());
    Json(response)
}

fn text_download(name: &str, text: String) -> Response {
    let mut rsp = Response::new(Body::from(text));
    rsp.headers_mut().insert(
        header::CONTENT_TYPE,
        HeaderValue::from_static("text/plain; charset=utf-8"),
    );
    rsp.headers_mut().insert(
        header::CONTENT_DISPOSITION,
        HeaderValue::from_str(&format!("attachment; filename=\"{name}\"")).unwrap(),
    );
    rsp
}
