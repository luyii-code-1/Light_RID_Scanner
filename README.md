# Light RID Scanner

[English](README.md) | [简体中文](README.zh-CN.md)

Light RID Scanner is a fixed-station Remote ID (ASTM F3411 / OpenDroneID) Wi-Fi monitor built for Raspberry Pi and other Linux-based capture nodes. It passively listens for drone Remote ID broadcasts over Wi-Fi, decodes them in real time, and presents the results through a local web dashboard.

It also includes a portable edition for mobile deployments and a node-center viewer that aggregates multiple stations into a single pane of glass.

- `station_edition/`
  Full fixed-station build. It contains the source runtime, web UI, security/auth controls, systemd/AP maintenance, and Raspberry Pi deployment defaults.
- `portable_edition/`
  WIP (Work in Progress). The portable runtime code has been removed while the product policy is being revised; the directory currently contains only a WIP README.
- Root `run.py`
  Compatibility wrapper for `station_edition/run.py`.
- Root `rid_model.json`
  Public GitHub Raw model map. Binaries also embed this file and restore it if runtime download fails.

The station edition is meant to be usable from its own directory. Runtime files such as `config.json`, `rid_storage.db`, and `rid_model.json` are resolved relative to the current working directory unless explicit paths are passed. Older `history-cache.json` / `rid_history_cache.json` files are treated as legacy migration sources.

- [Architecture](#architecture)
  - [Editions](#editions)
  - [Module Layout](#module-layout)
- [Features](#features)
- [Getting Started](#getting-started)
  - [Source (Station)](#source-station)
  - [Source (Portable)](#source-portable)
  - [Binary Deployment](#binary-deployment)
  - [Build from Source](#build-from-source)
- [Configuration](#configuration)
  - [Top-level Sections](#top-level-sections)
  - [Example Config](#example-config)
  - [Runtime File Resolution](#runtime-file-resolution)
- [Web UI](#web-ui)
  - [Main Page (`/`)](#main-page-)
  - [Settings Page (`/settings`)](#settings-page-settings)
  - [Hardware Assistant (`/hardware-assistant`)](#hardware-assistant-hardware-assistant)
  - [Logs Page (`/logs`)](#logs-page-logs)
- [NIC Binding & OOBE](#nic-binding--oobe)
  - [Fixed NIC Binding](#fixed-nic-binding)
  - [Out-of-Box Experience (OOBE)](#out-of-box-experience-oobe)
  - [AP Hotspot Mode](#ap-hotspot-mode)
- [Authentication](#authentication)
  - [Web UI Auth](#web-ui-auth)
  - [Passkey Login](#passkey-login)
  - [SSO Login Links](#sso-login-links)
  - [Session Lifecycle](#session-lifecycle)
- [External API](#external-api)
  - [Enabling the API](#enabling-the-api)
  - [Sending the Token](#sending-the-token)
  - [Token Generation](#token-generation)
  - [API Endpoint Reference](#api-endpoint-reference)
  - [IP Whitelist](#ip-whitelist)
  - [Session-only Helper Endpoints](#session-only-helper-endpoints)
- [Notification Center](#notification-center)
- [Enterprise WeCom Notifications](#enterprise-wecom-notifications)
- [Alarm Zones](#alarm-zones)
- [Host Metrics](#host-metrics)
- [Model Map Updates](#model-map-updates)
- [Import & Export](#import--export)
- [Node Center Viewer](#node-center-viewer)
  - [Running the Viewer](#running-the-viewer)
  - [Viewer Pages](#viewer-pages)
  - [Viewer Module Layout](#viewer-module-layout)
  - [Building the Viewer](#building-the-viewer)
- [Important Files](#important-files)
- [Git & Privacy Rules](#git--privacy-rules)
- [OpenDroneID References](#opendroneid-references)

---

## Architecture

### Editions

The repository contains three distinct editions, each serving a different deployment scenario:

| Directory | Purpose |
|---|---|
| `station_edition/` | **Full fixed-station build.** Includes the scanner core, web server with embedded UI, authentication and session management, systemd service helpers, AP hotspot mode, and Raspberry Pi deployment defaults. This is the primary edition for permanent installations. |
| `portable_edition/` | **Minimal mobile build.** Reuses the scanner and web core but disables web login, API tokens, SSO links, passkeys, host monitoring, and Enterprise WeCom notifications on startup. Designed for quick field deployments where authentication overhead is undesirable. |
| `viewer/` | **Node-center aggregator.** A standalone web service that connects to multiple `station_edition` instances, fetches their live data via the external API, and renders a unified dashboard. |

The root `run.py` is a thin compatibility wrapper that delegates directly to `station_edition/run.py`. Each edition is self-contained and can be run from its own directory.

### Module Layout

```
Light_RID_Scanner/
├── station_edition/
│   ├── run.py                       # Station entry point
│   ├── config.example.json          # Safe example config (committable)
│   └── light_rid/
│       ├── app.py                   # Application bootstrap & orchestration
│       ├── common_core.py           # Shared utilities and constants
│       ├── scan_core.py             # Wi-Fi capture, ODID decoding, DJI Beacon parsing
│       ├── process_core.py          # Aircraft state machine, history, tracks
│       ├── hardware_core.py         # NIC management, iw control, channel ops
│       ├── auth_core.py             # Password/passkey auth, session management
│       ├── network_binding_core.py  # NIC role assignment, AP hotspot setup
│       ├── web_server.py            # HTTP/WebSocket server, embedded HTML/CSS/JS
│       ├── cli_app.py               # CLI/TUI interface
│       ├── runtime.py               # Runtime context and chunk loader
│       └── platform_compat.py       # Platform-specific compatibility layer
├── portable_edition/
│   ├── pe.py                        # Portable entry point
│   └── bootstrap.py                 # Startup overrides (disable auth/notify/etc.)
├── viewer/
│   ├── server.py                    # HTTP/API/WebSocket routing
│   ├── storage.py                   # SQLite config, node records, auth state
│   ├── aggregation.py               # Live station API fetching & aggregation
│   ├── station_ui.py                # Station template loading & DOM patching
│   ├── settings_ui.py               # Viewer settings page
│   ├── nodes_ui.py                  # Node manager page
│   ├── ui_common.py                 # Shared CSS extraction
│   └── paths.py                     # Resource path resolution
├── pytools/
│   ├── build_release.py             # CI/local release builder
│   └── build_viewer.py              # Viewer binary builder
├── run.py                           # Root compatibility wrapper
├── rid_model.json                  # RID model prefix map
├── requirements.txt                 # Python dependencies
└── .github/workflows/               # CI build pipelines
```

The station runtime uses a chunk-loading architecture: `app.py` loads and executes the core modules (`common_core.py`, `scan_core.py`, `process_core.py`, `hardware_core.py`, `auth_core.py`, `network_binding_core.py`, `web_server.py`, `cli_app.py`) in order, assembling them into a single namespace at runtime. This design simplifies the build process while keeping source modules independently readable.

---

## Features

### Scanning & Decoding
- Passive Wi-Fi Remote ID capture (ASTM F3411 / OpenDroneID)
- 2.4 GHz and 5 GHz band support with configurable channel dwell times
- RSSI-based hit detection with configurable delta
- DJI newer-firmware RID Beacon parsing (extracts UAS ID and firmware type)
- Pilot position extraction from RID `System` messages
- Wi-Fi AP scanning with vendor OUI lookup

### Web Dashboard
- Real-time map with Leaflet, showing aircraft markers, base station, and alarm zones
- Target simulation over the configured scan interface, with an explicit memory-only demo mode (circle, line, or stationary patterns; up to 100 targets)
- Configurable Leaflet tile/API template for licensed map providers
- Aircraft list panel with live detail cards (SN, model, altitude, speed, heading, RSSI)
- AP list panel with vendor identification
- Dark/light theme toggle
- Responsive grid layout adaptable to different screen sizes
- Map auto-center with configurable idle timeout

### Data Persistence
- Aircraft history with first-seen / last-seen timestamps
- Per-aircraft GPS track storage
- SQLite-backed history storage (`rid_storage.db`) surviving service restarts
- Automatic one-time migration from legacy `history-cache.json` / `rid_history_cache.json` on first startup after upgrade
- Configurable aircraft offline detection timeout (default 15 seconds)

### Settings Page (`/settings`)
- Visual editing of all runtime configuration sections
- Base station position management (manual entry or browser geolocation)
- Multiple WeCom webhook channel management
- Multiple rectangular alarm zone configuration
- Passkey registration and deletion for passwordless browser login
- Managed SSO login link generation (requires password re-verification)
- Raw config tree browser — view, edit, save, delete files within the config root (requires secondary password unlock)
- One-click runtime security repair — creates the `rid` service user, grants capture/hotspot capabilities
- `iw` wireless tools installation helper
- systemd service registration and update
- Manual app version check by Git commit comparison
- Online model map updates with configurable URL and manual trigger
- Optional remote config update from a configurable URL
- Host load trend cards (CPU, memory, temperature, system load, AP count) with 12h / 24h / 7d windows
- Configurable metrics retention (default 7 days)

### Hardware Assistant (`/hardware-assistant`)
- List all wireless interfaces with status
- Inspect `iw dev`, `iw info`, `iw link` output
- Switch interfaces between monitor and managed mode
- Set channel on a specific interface
- Restart individual NICs
- Restart the main scanner process

### Notifications
- Server-side notification center, synchronized across all active browser sessions
- Aircraft online/offline events
- Alarm zone entry/exit events
- Model map update results (success/failure)
- Manual browser notices from the built-in UI
- Single delete or clear-all operations

### Enterprise WeCom
- Multiple webhook channel support
- Per-channel enable/disable toggle
- Online notification to all enabled channels
- Test notification to all enabled channels
- Configurable send timeout and re-online cooldown
- Backward compatibility with legacy single-key config

### Security
- Password-based browser login with scrypt-hashed credentials
- Passkey (WebAuthn) support bootstrapped from initial password login
- SSO login links with server-side check codes
- Configurable session TTL (default 30 minutes)
- IP whitelist for external API access
- Rate limiting on login, SSO creation, token reveal, and API token failures
- Sensitive fields (webhook keys, API tokens) masked in visual settings

---

## Getting Started

### Prerequisites

- **Linux** (Raspberry Pi OS recommended; 64-bit OS for `arm64` binaries)
- Wireless NIC with **monitor mode** support
- Root privileges for monitor mode and channel switching
- `iw` and `hostapd` when using NIC binding with AP hotspot mode
- Python 3.10+

### Source (Station)

```bash
cd station_edition
python3 -m venv .venv
source .venv/bin/activate
pip install -r ../requirements.txt
python run.py --no-tui
```

The portable edition is currently WIP and has no runnable source entrypoint. When available, it will automatically disable authentication, notifications, and host monitoring for quick field deployments.

### Binary Deployment

CI produces single-file compiled binaries for Linux. Only the binary is required for a first start — missing config and history files are created automatically.

```bash
install -m 0755 light_rid_station-arm64 /opt/light-rid/light_rid_station-arm64
```

Configure systemd to run it directly:

```ini
[Unit]
Description=Light RID Scanner
After=network.target

[Service]
ExecStart=/opt/light-rid/light_rid_station-arm64 --config /opt/light-rid/config.json --no-tui
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
```

The binary resolves runtime files relative to its working directory. If `rid_model.json` is missing, it downloads the latest version from GitHub Raw; if the network is unavailable, it falls back to the embedded resource shipped inside the binary.

### Build from Source

```bash
# Station edition
python pytools/build_release.py --edition station --target arm64
python pytools/build_release.py --edition station --target x86_64

# Portable edition
python pytools/build_release.py --edition portable --target x86_64
python pytools/build_release.py --edition portable --target x32
```

The `x32` target requires a 32-bit Python runtime; the GitHub Actions workflow handles this in a dedicated 32-bit Docker job.

**CI artifact matrix:**

| Edition | Architecture | Runner |
|---|---|---|
| station | x86_64 | ubuntu-24.04 |
| station | arm64 | ubuntu-24.04-arm |
| portable | x86_64 | ubuntu-24.04 |
| portable | arm64 | ubuntu-24.04-arm |
| portable | x32 | 32-bit Docker |

---

## Configuration

### Top-level Sections

The runtime configuration is a single JSON file (`config.json`) organized into the following sections:

| Section | Purpose |
|---|---|
| `basic` | Capture and runtime behavior — interface, channel, hop settings, dwell times, RSSI delta, aircraft timeout, debug mode |
| `notify` | Enterprise WeCom notification channels — per-webhook enable/disable, send timeout, re-online cooldown |
| `web` | Map and UI configuration — base station coordinates, default zoom, heading reference, DJI lookup URL, alarm zone definitions |
| `ap` | Wi-Fi AP scan limits and vendor database settings — max AP list size, OUI file source |
| `auth` | Browser login and session authentication — user/password hashes, session TTL, passkey storage, SSO link list |
| `api` | External API token authentication — enable flag, token hash, token list with expiry, IP whitelist |
| `model_update` | Online RID model map updates — enable flag, JSON source URL |
| `config_update` | Remote runtime config updates — enable flag, JSON source URL, last-check tracking |
| `app_update` | Upstream Git commit comparison — enable flag, commit API URL |
| `metrics` | Host load metrics — enable flag, retention days, temperature sensor source |
| `network_bindings` | NIC role assignments and AP hotspot profile — per-interface roles, SSID, DHCP range |

### Example Config

A complete, commented example is provided at `station_edition/config.example.json`. It contains safe defaults for all sections and is designed to be copied and customized:

```bash
cp station_edition/config.example.json config.json
```

Then edit `config.json` to match your hardware and deployment requirements.

### Runtime File Resolution

Runtime files are resolved relative to the current working directory unless explicit paths are passed via command-line arguments:

| File | Purpose | Auto-created? |
|---|---|---|
| `config.json` | Main runtime configuration | Yes (from defaults) |
| `rid_storage.db` | SQLite history store and retained raw packet data | Yes |
| `history-cache.json` | Legacy JSON history source, auto-imported once when present | Legacy migration source |
| `rid_history_cache.json` | Older legacy JSON history source, auto-imported once when present | Legacy migration source |
| `rid_model.json` | RID model prefix-to-name mapping | Yes (from GitHub or embedded resource) |
| `oui.txt` | MAC OUI vendor database | Optional (auto-downloaded) |
| `light_rid_scanner/host_metrics.jsonl` | Host load samples | Yes (system temp dir) |

## Web UI

### Main Page (`/`)

The landing page presents a full-screen dashboard with four zones:

1. **Header** — live statistics (aircraft count, AP count, uptime), scan status indicator, theme toggle
2. **Map panel** — Leaflet-based map displaying aircraft markers (with heading arrows), base station icon, and enabled alarm zone rectangles. Aircraft markers update in real time via WebSocket push. Clicking a marker opens a detail card with SN, model, altitude, speed, heading, RSSI, and last-seen time.
3. **Bottom panel** — switchable between aircraft list, AP list, and event log views. The aircraft list shows compact cards sorted by last-seen time. The AP list displays detected Wi-Fi access points with vendor names from the OUI database.
4. **Footer** — navigation links to `/settings`, `/logs`, `/hardware-assistant`, and theme toggle.

### Map Provider Configuration

The Station dashboard uses Leaflet. When no map provider is configured, it falls back to the built-in default online tile template for local testing. That fallback may have legal or service-terms risk; do not expose the Station page to the public internet or use it commercially without configuring a licensed map provider.

Configure a licensed XYZ tile/API template in `/settings` under **Map & Base Station**, or set these fields in `config.json`:

```json
{
  "web": {
    "map_tile_url": "https://example.com/tiles/{z}/{x}/{y}.png?key=YOUR_KEY",
    "map_tile_subdomains": "",
    "map_tile_attribution": "(c) Your Map Provider",
    "map_tile_max_native_zoom": 18
  }
}
```

`map_tile_url` must include `{z}`, `{x}`, and `{y}`. Optional `{s}` subdomains are supplied through `map_tile_subdomains` as a comma-separated list. Once `map_tile_url` is set, the dashboard hides the default-map legal-risk hint.

### Settings Page (`/settings`)

The settings page provides visual editors organized as collapsible cards:

- **Basic** — interface, channel, hop behavior, dwell times, lost timeout, debug toggle
- **Notification** — WeCom channel list with add/edit/delete/test per channel
- **Web** — base station name, coordinates (with browser geolocation fill-in), default zoom, DJI lookup URL
- **Alarm Zones** — multiple rectangular zones with enable/disable per zone
- **AP** — max list size, vendor database settings
- **Auth** — enable/disable web login, session TTL, login methods (password / passkey)
- **Passkeys** — register new passkeys, delete existing ones
- **SSO Links** — generate managed login links (requires password re-check), delete to invalidate
- **API** — external API enable/disable, token management with expiry and single-use options
- **Model Update** — URL field, enable/disable auto-check, manual update button
- **Config Update** — URL field, enable/disable, manual pull button
- **App Update** — commit comparison against upstream
- **Metrics** — enable/disable host monitoring, retention period, trend charts
- **Raw Config** — password-rechecked config tree browser with inline edit/save/delete
- **Security Repair** — one-click service user creation, capability grant, `iw` install, systemd registration
- **Import/Export** — separate flows for settings files and scan data

### Hardware Assistant (`/hardware-assistant`)

A dedicated page for wireless NIC operations:

- Lists all detected wireless interfaces with current mode, channel, and state
- Displays raw `iw dev`, `iw info`, and `iw link` output for inspection
- Buttons to switch each interface between monitor and managed mode
- Channel setter with per-interface target selection
- NIC restart button
- Scanner process restart button

### Logs Page (`/logs`)

Provides multiple log views in a tabbed interface:

- **Runtime log** — main scanner log output
- **Operation log** — audit trail of config changes, auth events, updates
- **Scan log** — raw Wi-Fi capture log
- **Diff view** — unified diff between runtime and scan logs
- **Export** — text export for a single view, or ZIP export for all views
- **API docs** — rendered view of `GET /api/docs`

Sensitive fields (webhook keys, API tokens) are masked in the visual display. Leaving a masked field unchanged preserves the stored value.

---

## NIC Binding & OOBE

### Fixed NIC Binding

`basic.iface` is treated as a fixed binding. The scanner does not auto-rotate across available NICs. If the specified interface is missing at startup, the service remains alive in a degraded state and surfaces a configuration warning through the web UI, rather than silently switching to another adapter.

This design ensures predictable behavior in multi-NIC deployments — the scanner always uses the intended interface, and startup problems are surfaced as explicit configuration issues.

### Out-of-Box Experience (OOBE)

When `config.json` is missing, broken, or has no bound NIC, the web UI automatically enters the OOBE flow at `/oobe`. This guided setup collects the minimum required configuration:

1. **Select wireless NIC** — choose from detected interfaces
2. **Set RID channel** — pick the monitoring channel
3. **Base station coordinates** (optional) — set the map center point
4. **Web login credentials** (optional) — set username and password for browser auth

After OOBE completes, the configuration is written to disk and the normal dashboard loads.

### AP Hotspot Mode

NICs can be assigned the `ap_web` role through the Custom NIC Binding settings. When configured:

- `hostapd` creates a Wi-Fi hotspot with the specified SSID and password
- A built-in DHCP server assigns addresses in the `172.16.0.0/24` range
- The web UI is exposed at `172.16.0.1:80`
- The hotspot runs on a configurable channel (default: 6)

This allows the scanner to serve its web UI over its own Wi-Fi network, useful for field deployments without existing infrastructure.

Each detected NIC can be assigned one of these roles: `scan`, `web`, `ap_web`, `disabled`, `idle`, or `none`. The `scan` role is synchronized back to `basic.iface`.

---

## Authentication

### Web UI Auth

Browser-based authentication uses a normal `/login` page with session cookies, not HTTP Basic Auth prompts. Configuration:

```json
{
  "auth": {
    "enabled": true,
    "username_hash": "<scrypt(username)>",
    "password_hash": "<scrypt(password)>",
    "session_ttl_min": 30,
    "realm": "Light RID Scanner",
    "login_methods": ["password", "passkey"]
  }
}
```

Generate scrypt hashes matching the app's format:

```bash
python3 - <<'PY'
import base64, hashlib, secrets

def hash_secret(text):
    salt = secrets.token_bytes(16)
    digest = hashlib.scrypt(
        text.encode(), salt=salt,
        n=2**14, r=8, p=1, dklen=32
    )
    return "scrypt$16384$8$1$%s$%s" % (
        base64.urlsafe_b64encode(salt).decode().rstrip("="),
        base64.urlsafe_b64encode(digest).decode().rstrip("="),
    )

print("user:", hash_secret("your_username"))
print("pass:", hash_secret("your_password"))
PY
```

### Passkey Login

Passkeys (WebAuthn) provide passwordless browser login after an initial bootstrap:

1. Log in with username and password
2. In `/settings`, register a passkey — the browser creates a credential pair
3. The public key is stored in `auth.passkeys`
4. On subsequent logins, the `/login` page offers passkey authentication
5. Passkeys can be deleted from Settings at any time

### SSO Login Links

For trusted external launchers, SSO-style login links use a server-side `check` code:

```
/login?check=<server-check-code>
```

The Settings page generates these links after a fresh username/password verification. The generated URL remains valid until its `check` code is deleted from the Settings list. Old-style URLs carrying `user` or `password` query parameters are tolerated as inert strings — only `check` is validated.

### Session Lifecycle

- Session TTL is configurable via `auth.session_ttl_min` (default: 30 minutes)
- When a session expires, page API requests return an auth failure
- Built-in pages automatically redirect to `/login`
- Login, SSO creation, token reveal, and API token failures are rate-limited in memory and written to the operation log

---

## External API

The external API provides machine-readable access to scanner data for integrations, scripts, and the Node Center Viewer.

### Enabling the API

All three conditions must be met:

1. Web login auth is **enabled** (`auth.enabled: true`)
2. Username and password hashes are **configured**
3. API token is **configured** (`api.token` or `api.token_hash`)

This design ensures the external API is only exposed when the operator has explicitly set up authentication.

### Sending the Token

Two request header styles are supported:

```bash
# Style 1: Custom header
curl -H "X-API-Token: YOUR_TOKEN" http://0.0.0.0:4600/api/v1/snapshot

# Style 2: Bearer token
curl -H "Authorization: Bearer YOUR_TOKEN" http://0.0.0.0:4600/api/v1/drones
```

### Token Generation

Generate a token hash using the same scrypt format:

```bash
python3 - <<'PY'
import base64, hashlib, secrets
salt = secrets.token_bytes(16)
digest = hashlib.scrypt(b"YOUR_TOKEN_HERE", salt=salt, n=2**14, r=8, p=1, dklen=32)
print("scrypt$16384$8$1$%s$%s" % (
    base64.urlsafe_b64encode(salt).decode().rstrip("="),
    base64.urlsafe_b64encode(digest).decode().rstrip("="),
))
PY
```

The API supports multiple tokens, each with optional expiry and single-use flags. If only `api.token_hash` is stored (without `api.token`), the external API still works, but the Settings page cannot reveal or copy the plain token.

**Recommended workflow:**
- Generate a random token locally
- Keep both `api.token` and `api.token_hash` if you want Settings to reveal/copy it later
- Use IP whitelist mode when the caller IP range is predictable
- Store the plain token only in your API client, script, or secrets manager
- Never commit real tokens to Git

### API Endpoint Reference

#### Discovery

| Method | Path | Description |
|---|---|---|
| GET | `/api/docs` | API metadata, auth hints, and endpoint index |
| GET | `/api/health` | Simple health check |

#### Read

| Method | Path | Description |
|---|---|---|
| GET | `/api/v1/snapshot` | Full runtime snapshot for integrations |
| GET | `/api/v1/auth/status` | Auth status summary |
| GET | `/api/v1/drones` | Current aircraft list |
| GET | `/api/v1/drones/{sn}` | Single aircraft detail |
| GET | `/api/v1/tracks/{sn}` | Track points for one aircraft |
| GET | `/api/v1/aps` | Current AP list |
| GET | `/api/v1/logs?type=event\|scan\|ap&limit=200` | Event/scan/AP logs |

#### Write

| Method | Path | Description |
|---|---|---|
| POST | `/api/v1/history/clear` | Clear all history |
| POST | `/api/v1/history/delete` | Delete one aircraft from history |
| POST | `/api/v1/tracks/clear` | Clear all tracks or one aircraft's tracks |
| POST | `/api/v1/config/reload` | Reload config from disk |

### IP Whitelist

When `api.whitelist_enabled` is `true`, only requests from addresses in `api.whitelist` pass token auth:

```json
{
  "api": {
    "whitelist_enabled": true,
    "whitelist": [
      "127.0.0.1",
      "192.168.1.0/24"
    ]
  }
}
```

### Session-only Helper Endpoints

These endpoints are for the built-in web UI and require a valid browser session (they are **not** part of the token-protected `/api/v1/*` namespace):

**Notifications**
- `GET /api/notifications?limit=200`
- `POST /api/notifications` / `POST /api/notifications/delete` / `POST /api/notifications/clear`

**Settings**
- `GET /api/settings/view` / `GET /api/settings/runtime`
- `GET /api/settings/metrics?window=12h|24h|7d`
- `GET /api/settings/systemd/status` / `GET /api/settings/api-docs`
- `POST /api/settings/visual/test` / `POST /api/settings/visual/save`
- `POST /api/settings/raw/unlock` / `POST /api/settings/raw/save`
- `POST /api/settings/notify/test`
- `POST /api/settings/passkey/start` / `POST /api/settings/passkey/finish` / `POST /api/settings/passkey/delete`
- `POST /api/settings/login-link/create` / `POST /api/settings/login-link/delete`
- `POST /api/settings/models/save` / `POST /api/settings/models/upsert` / `POST /api/settings/models/update` / `GET /api/settings/models/list`
- `POST /api/settings/app-update/check`
- `POST /api/settings/systemd/register` / `POST /api/settings/iw/install` / `POST /api/settings/security/repair`

**Config**
- `GET /api/config` / `GET /api/config/file?path=<within-config-root>`
- `POST /api/config/file/delete`

**Logs**
- `GET /api/logs/view?type=runtime|operation|scan|scan_diff|ap`
- `GET /api/logs/export?type=all|runtime|operation|scan|scan_diff|ap`

**Hardware**
- `GET /api/hw/status` / `POST /api/hw/op`

**Tools**
- `GET /api/tools/export/all` / `GET /api/tools/export/track?sn=<SN>`
- `GET /api/tools/diagnostic.zip`
- `POST /api/tools/import/all` / `POST /api/tools/import/track`
- `GET /api/tracks/get?sn=<SN>` / `POST /api/tracks/clear`
- `POST /api/history/delete` / `POST /api/history/clear`

**Passkey Login**
- `POST /api/passkey/login/start` / `POST /api/passkey/login/finish`

When `api.enabled` is `false`, `/api/docs`, `/api/health`, and all `/api/v1/*` paths are **not** open on the LAN — they only work from the built-in web pages through the browser session flow. External scripts must wait until the API is explicitly enabled.

- The current API token is shown as a masked password field
- Revealing or copying it requires a fresh username/password check
- That re-check uses the same web auth credentials, but API routes still require the API token when external API mode is enabled
- Generating a managed SSO login link also requires the same fresh username/password check
- Login, SSO login link, token reveal, and external API token failures are rate-limited in memory and written to the operation log.

## Notification Center

The notification center is server-side, backed by in-memory storage and synchronized across all active browser sessions via `/api/notifications`. Unlike browser-local storage, notifications survive page refreshes and are visible from any connected browser.

**Sources:**
- Aircraft online / offline events
- Alarm zone entry events
- Model map update results (success / failure)
- Manual notices posted by the built-in UI

Notifications can be deleted individually or cleared in bulk from the UI.

---

## Enterprise WeCom Notifications

The system supports multiple WeCom (企业微信) webhook channels for aircraft online alerts:

```json
{
  "notify": {
    "enabled": true,
    "send_timeout_sec": 8,
    "notify_reonline": true,
    "reonline_cooldown_sec": 300,
    "wecom_webhooks": [
      {
        "name": "Primary Channel",
        "enabled": true,
        "key": "YOUR_WEBHOOK_KEY"
      },
      {
        "name": "Backup Channel",
        "enabled": false,
        "key": "YOUR_BACKUP_KEY"
      }
    ]
  }
}
```

**Behavior:**
- Online notifications are sent to all enabled channels
- Test notifications (from Settings) are sent to all enabled channels
- Re-online notifications are rate-limited by `reonline_cooldown_sec` (default: 300 seconds)
- The legacy `notify.wecom_webhook_key` single-key field is still accepted for backward compatibility
- Webhook keys are masked in the Settings UI

---

## Alarm Zones

Multiple rectangular alarm zones can be defined, drawn on the map as red rectangles:

```json
{
  "web": {
    "alarm_zones": [
      {
        "name": "North Field",
        "enabled": true,
        "lat1": 30.000000,
        "lon1": 121.000000,
        "lat2": 30.010000,
        "lon2": 121.010000
      }
    ]
  }
}
```

**Behavior:**
- Enabled zones are rendered as red rectangles on the map
- A drone entering an enabled zone triggers a fullscreen browser warning
- Browser notification is sent if the user has granted notification permission
- Legazy `web.alarm_zone` single-zone field is still accepted for backward compatibility

---

## Host Metrics

When enabled, the scanner samples host metrics approximately once per minute and stores them in the system temp directory under `light_rid_scanner/host_metrics.jsonl`. The file is created automatically, preserved across service restarts, and pruned according to `metrics.retention_days` (default: 7 days).

**Tracked metrics:**
- CPU usage
- Memory usage
- Temperature (auto-detected sensor or manual source)
- System load
- AP count

The Settings page renders these as separate mini trend charts with selectable time windows: 12 hours, 24 hours, or 7 days.

```json
{
  "metrics": {
    "enabled": true,
    "retention_days": 7,
    "temperature_source": "auto"
  }
}
```

Metrics are disabled by default. Enable them in `/settings` to start collecting.

---

## Model Map Updates

The RID model map (`rid_model.json`) maps RID prefix codes to human-readable drone model names. It can be updated online from a configurable URL.

**Default source:**
```
https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/rid_model.json
```

**Behavior:**
- Automatic checks run once per day when `model_update.enabled` is `true`
- Manual update uses the same URL field in Settings
- The URL must start with `http://` or `https://`
- Successful and failed updates are written to the operation log and notification center
- The Settings page also allows direct editing of the model list as a prefix/model table
- Aircraft detail cards showing "N/A" for the model offer options to add a local mapping or open a prefilled GitHub Issue / PR edit page

Binary builds embed a snapshot of `rid_model.json` as a fallback resource. If the file is missing at runtime and the network is unavailable, the embedded copy is restored automatically.

---

## Import & Export

The system provides separate export/import flows for settings and scan data:

**Settings (configuration):**
- `GET /api/settings/export/settings` — export current settings JSON
- `POST /api/settings/import/settings` — import and merge settings

**Scan data (history + tracks):**
- `GET /api/settings/export/scan-data` — export aircraft history and tracks
- `POST /api/settings/import/scan-data` — import scan data

**Combined tools:**
- `GET /api/tools/export/all` — export all data as ZIP
- `GET /api/tools/export/track?sn=<SN>` — export single aircraft track as ZIP
- `POST /api/tools/import/all` — import all data from ZIP
- `POST /api/tools/import/track` — import track data

These helpers are available from the Settings page and via direct API calls from the built-in UI.

---

## Node Center Viewer

`viewer/server.py` is a standalone web service that aggregates multiple `station_edition` instances into a unified dashboard. It is designed for operators managing several fixed stations who want a single-pane-of-glass view.

### Running the Viewer

```bash
python viewer/server.py --host 0.0.0.0 --port 4700
```

Open `http://<center-ip>:4700/`.

### Data Flow

The viewer stores only its own configuration in `viewer/cfg.db`:
- Node API root URLs
- Node API tokens
- Optional viewer password and SSO login settings

It does **not** store remote aircraft, base-station, AP, track, or health data. Every dashboard refresh fetches current data from each configured station API in parallel and renders the aggregate result. This means the viewer is stateless with respect to scan data — stop the viewer, and no scan data is retained.

### Viewer Pages

**`/` — Dashboard**
- Reuses the Station page template from `station_edition/light_rid/web_server.py`
- Viewer code patches the data/API layer to fetch from remote stations instead of a local scanner
- Station-only controls (scanner start/stop, channel change, etc.) are removed from the DOM

**`/settings` — Viewer Settings**
- Viewer host status (uptime, version)
- Default map center position and zoom level
- Password login configuration for the viewer itself
- SSO check login configuration
- EULA acceptance controls

**`/nodes` — Node Manager**
- Add, edit, test, and delete station nodes
- Node info cards with live status
- Load charts and scan count displays
- One-click remote SSO URL creation for each node
- Batch restart and batch model-database update across selected nodes

### Adding a Node

Enter only the API root URL, for example `http://192.168.1.10:4600`. Paths, query strings, fragments, and user-info are rejected — the viewer appends `/api/v1` paths itself and validates by making real API calls before saving.

The viewer sends the configured token as both `X-API-Token` and `Authorization: Bearer <token>` headers.

### Viewer Module Layout

| Module | Responsibility |
|---|---|
| `viewer/server.py` | HTTP routing, API proxying, WebSocket |
| `viewer/storage.py` | SQLite database for config, nodes, auth/session state |
| `viewer/aggregation.py` | Parallel station API fetching and data aggregation |
| `viewer/station_ui.py` | Station HTML template loading and viewer DOM patching |
| `viewer/settings_ui.py` | Viewer-specific settings page (Station-styled) |
| `viewer/nodes_ui.py` | Node manager page (Station-styled) |
| `viewer/ui_common.py` | Shared CSS extraction from Station templates |
| `viewer/paths.py` | Resource path resolution |

### Building the Viewer

```bash
python pytools/build_viewer.py --target x86_64
```

CI builds viewer binaries through `.github/workflows/build-viewer.yml` for Linux `x86_64`, Linux `x32`, Linux `arm64`, Windows `windows-x86_64`, and Windows `windows-x32`.

---

## Important Files

| File | Description | Commit? |
|---|---|---|
| `run.py` | Root compatibility wrapper for station edition | Yes |
| `station_edition/run.py` | Station edition entry point | Yes |
| `station_edition/light_rid/` | All scanner, parser, server, auth, and UI modules | Yes |
| `portable_edition/pe.py` | Portable edition entry point | Yes |
| `rid_model.json` | RID model prefix-to-name mapping | Yes |
| `rid_build_info.json` | Local build marker (commit + build number) | Yes |
| `station_edition/config.example.json` | Safe example configuration | Yes |
| `config.json` | Real runtime configuration | **Never** |
| `rid_storage.db` | Runtime SQLite history store | **Never** |
| `history-cache.json` | Legacy JSON history cache kept only for one-time upgrade import | **Never** |
| `rid_history_cache.json` | Older legacy JSON history cache kept only for one-time upgrade import | **Never** |
| `config.json.rollback` | Automatic rollback copy for recovery | **Never** |
| `oui.txt` | MAC OUI vendor database (auto-downloaded) | **Never** |
| `light_rid_scanner/host_metrics.jsonl` | Host metrics samples (system temp dir) | **Never** |
| `viewer/cfg.db` | Viewer node and auth configuration | **Never** |

The build version shown in the UI follows the format `commit:<short-sha>#<build-number>`, read from `rid_build_info.json`. The current release line is `v2.0`, but the UI uses the commit-based label for traceability of local builds.

---

## Git & Privacy Rules

Before pushing to GitHub, verify:

- [ ] `config.json` is **not** staged
- [ ] No real webhook keys are in any tracked file
- [ ] No real API tokens are in any tracked file
- [ ] No runtime-generated history or cache files are staged
- [ ] Only `station_edition/config.example.json` contains example config values

---

## OpenDroneID References

- [Open Drone ID Core C Library](https://github.com/opendroneid/opendroneid-core-c) — official reference implementation
- [OpenDroneID Specs Repository](https://github.com/opendroneid/specs) — specification drafts and documentation

For the final, authoritative ASTM Remote ID standard text, obtain ASTM F3411 directly from [ASTM International](https://www.astm.org/).
