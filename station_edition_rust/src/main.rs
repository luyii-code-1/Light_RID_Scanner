use anyhow::Result;
use clap::Parser;
use light_rid_station::{server, state, state::AppStateExt};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

#[derive(Debug, Clone, Parser)]
#[command(
    name = "light-rid-station",
    about = "Light RID Scanner station edition"
)]
struct Args {
    #[arg(long, default_value = "config.json")]
    config: String,
    #[arg(long)]
    iface: Option<String>,
    #[arg(long)]
    channel: Option<u16>,
    #[arg(long)]
    hop: bool,
    #[arg(long = "hop-5g")]
    hop_5g: bool,
    #[arg(long = "scan-wifi-fast")]
    scan_wifi_fast: bool,
    #[arg(long = "dwell-2g", default_value_t = 250)]
    dwell_2g: u64,
    #[arg(long = "dwell-5g", default_value_t = 800)]
    dwell_5g: u64,
    #[arg(long, default_value_t = 30)]
    settle: u64,
    #[arg(long = "dwell-on-hit", default_value_t = 2500)]
    dwell_on_hit: u64,
    #[arg(long = "hit-cap", default_value_t = 6000)]
    hit_cap: u64,
    #[arg(long = "time", default_value_t = 2.0)]
    print_interval: f64,
    #[arg(long = "min-gap", default_value_t = 1.0)]
    min_gap: f64,
    #[arg(long = "lost-timeout", default_value_t = 15.0)]
    lost_timeout: f64,
    #[arg(long = "rssi-delta", default_value_t = 3)]
    rssi_delta: i32,
    #[arg(long = "change-on-rssi")]
    change_on_rssi: bool,
    #[arg(long = "change-on-payload")]
    change_on_payload: bool,
    #[arg(long = "model-map", default_value = "rid_model.json")]
    model_map: String,
    #[arg(long = "history-file", default_value = "rid_storage.db")]
    history_file: String,
    #[arg(long = "no-tui", default_value_t = true)]
    no_tui: bool,
    #[arg(long)]
    tui: bool,
    #[arg(long)]
    debug: bool,
    #[arg(long = "notify-test")]
    notify_test: bool,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env().unwrap_or_else(|_| "info".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    let args = Args::parse();
    let state = state::load(&args.config, &args.history_file)?;
    state.log_info(format!(
        "[INFO] Rust station edition started config={}",
        args.config
    ));
    state.log_info("[INFO] Python runtime is not used by this station binary");
    if args.notify_test {
        state.notification_add(
            "WeCom notify test is configured through /api/settings/notify/test",
            "info",
        );
        return Ok(());
    }
    if args.tui || !args.no_tui {
        state.log_info(
            "[WARN] TUI compatibility mode is pending in Rust edition; web UI remains available",
        );
    }
    server::serve(state).await
}
