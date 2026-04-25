# Light RID Scanner

[English](README.md) | [简体中文](README.zh-CN.md)

Light RID Scanner is a fixed-station Remote ID / OpenDroneID Wi-Fi monitor designed for Raspberry Pi and other Linux-based capture nodes.

It keeps the runtime model deliberately simple: one main process in `run.py`, long-running stability features, guarded config writes, persistent history/track storage, and a LAN web UI for map/list/log viewing.

## Highlights

- Modern LAN web UI with three main views:
  - `Map`
  - `Aircraft List`
  - `Other` (Realtime AP list + AP scan log)
- Dedicated `/settings` page for visual config editing
- Dedicated `/hardware-assistant` page for NIC / `iw` operations
- RID history and track persistence
- Pilot position extraction from RID `System` messages
- Export helpers for aircraft detail and per-aircraft tracks
- Optional token-protected external API
- Optional browser login / session auth for the web UI
- Enterprise WeCom notifications with multiple webhook channels
- Multiple custom alarm zones drawn on the map

## Runtime

Recommended environment:

- Linux
- Raspberry Pi OS recommended
- Python 3.10+
- Wireless NIC with monitor mode support
- Root privileges for monitor mode / channel switching

Start:

```bash
sudo ~/rid/.venv/bin/python3 run.py
```

The program now defaults to non-TUI mode. `--no-tui` is no longer required.

Default web URL:

- `http://<device-ip>:4600/`

## Fixed NIC Binding and OOBE

- The scanner no longer auto-rotates across NICs.
- `basic.iface` is treated as a fixed binding. If that NIC is missing, the service stays alive in degraded mode and shows a configuration warning instead of silently switching to another adapter.
- If `rid_config.json` is missing, broken, or still has no bound NIC, the web UI enters the OOBE flow at `/oobe`.
- OOBE is used to finish the minimum required setup:
  - choose the default wireless NIC
  - set the RID channel
  - optionally set base-station coordinates
  - optionally set the web login account/password

Operationally, this makes multi-NIC deployments much safer: the scanner keeps using the intended adapter, and startup problems are surfaced as configuration work rather than hidden auto-fallback.

## Main Pages

- `/`
  Main UI with map, aircraft list, and AP/log view switching.
- `/settings`
  Visual settings editor, raw config editor, token/API overview, alarm zone editor, notification editor.
- `/hardware-assistant`
  Visual hardware helper for NIC status, `iw` inspection, monitor/managed switching, channel change, NIC restart, and process restart.

## Important Files

- `run.py`
  Main scanner, parser, HTTP/WS server, embedded pages, API handlers.
- `rid_models.json`
  Model prefix mapping.
- `rid_config.example.json`
  Safe Git-tracked example config.
- `rid_config.json`
  Real runtime config. Do not commit it.
- `rid_history_cache.json`
  Runtime-generated history / track cache.
- `rid_config.json.rollback`
  Rollback copy for config recovery.

## Configuration Model

The runtime config is split into these top-level sections:

- `basic`
  Capture/runtime behavior.
- `notify`
  WeCom notification channels and notification timing.
- `web`
  Map/base-station/alarm-zone behavior and UI labels.
- `ap`
  AP list limits and vendor DB settings.
- `auth`
  Browser UI login/session auth.
- `api`
  External token API auth.

Example file:

- `rid_config.example.json`

## Token API

### What the token protects

When enabled, token auth protects:

- `GET /api/docs`
- `GET /api/health`
- all `/api/v1/*` endpoints

Examples:

- `GET /api/v1/snapshot`
- `GET /api/v1/drones`
- `GET /api/v1/drones/{sn}`
- `GET /api/v1/tracks/{sn}`
- `GET /api/v1/aps`
- `GET /api/v1/logs?type=event|scan|ap&limit=200`
- `POST /api/v1/history/clear`
- `POST /api/v1/history/delete`
- `POST /api/v1/tracks/clear`
- `POST /api/v1/config/reload`

### How to send the token

Two supported request styles:

1. Header `X-API-Token`
2. Header `Authorization: Bearer <token>`

Examples:

```bash
curl -H "X-API-Token: YOUR_TOKEN" \
  http://192.168.1.32:4600/api/v1/snapshot
```

```bash
curl -H "Authorization: Bearer YOUR_TOKEN" \
  http://192.168.1.32:4600/api/v1/drones
```

### How to enable the external API

The external API can only be enabled when all three conditions are true:

- Web login auth is enabled
- Web login username/password are configured
- API token is configured

```json
{
  "auth": {
    "enabled": true,
    "username_sha256": "<sha256(username)>",
    "password_sha256": "<sha256(password)>"
  },
  "api": {
    "enabled": true,
    "token": "YOUR_TOKEN_HERE",
    "token_sha256": "<sha256(token)>",
    "whitelist_enabled": true,
    "whitelist": [
      "127.0.0.1",
      "192.168.1.0/24"
    ]
  }
}
```

Generate a token hash:

```bash
python3 - <<'PY'
import hashlib
print(hashlib.sha256(b"YOUR_TOKEN_HERE").hexdigest())
PY
```

If you only keep `api.token_sha256`, the external API still works, but the Settings page cannot reveal/copy the current token because only the hash is stored.

### Recommended token workflow

- Generate a random token locally
- Keep `api.token` and `api.token_sha256` in sync if you want Settings to reveal/copy the token later
- Use whitelist mode if the caller IP range is predictable
- Keep the plain token in your API client, script, secret manager, or password manager
- Never commit the real token to Git

### Important behavior when disabled

If `api.enabled` is `false`, `/api/docs`, `/api/health`, and `/api/v1/*` are no longer open on the LAN. They only work from the built-in web pages through the current page session flow.

That means:

- external scripts must wait until the external API is explicitly enabled
- browser pages inside Light RID Scanner still work
- the web login session does not grant direct access to token API paths

## Web UI Auth vs Token API Auth

These are separate mechanisms.

### Web UI auth

Used for browser pages and session-based helper endpoints. The browser now uses a normal `/login` page and a session cookie, not a browser HTTP Basic prompt.

Config example:

```json
{
  "auth": {
    "enabled": true,
    "username_sha256": "<sha256(username)>",
    "password_sha256": "<sha256(password)>",
    "realm": "Light RID Scanner"
  }
}
```

Generate username/password hashes:

```bash
python3 - <<'PY'
import hashlib
print("user:", hashlib.sha256("your_user".encode()).hexdigest())
print("pass:", hashlib.sha256("your_pass".encode()).hexdigest())
PY
```

SSO-style login is available for trusted local launchers:

```text
/login?user=<sha256(username)>&password=<sha256(password)>
```

For compatibility with old local shortcuts, a comma form is also accepted:

```text
/login?user=<sha256(username)>,password=<sha256(password)>
```

### Session-only helper endpoints

These are meant for the built-in web UI and current browser session:

- `GET /api/settings/view`
- `GET /api/settings/runtime`
- `GET /api/settings/api-docs`
- `GET /api/logs/view?type=runtime|operation|scan|scan_diff|ap`
- `GET /api/logs/export?type=all|runtime|operation|scan|scan_diff|ap`
- `POST /api/settings/visual/save`
- `POST /api/settings/raw/save`
- `POST /api/settings/notify/test`
- `GET /api/hw/status`
- `POST /api/hw/op`
- `GET /api/config`
- `GET /api/tools/export/all`
- `GET /api/tools/export/track?sn=<SN>`
- `GET /api/tools/diagnostic.zip`
- `POST /api/tools/import/all`
- `POST /api/tools/import/track`
- `GET /api/tracks/get?sn=<SN>`
- `POST /api/tracks/clear`
- `POST /api/history/delete`
- `POST /api/history/clear`

These are not the same thing as `/api/v1/*`.

### Token reveal/copy in Settings

- The current API token is shown as a masked password field
- Revealing or copying it requires a fresh username/password check
- That re-check uses the same web auth credentials, but API routes still require the API token when external API mode is enabled
- Login, token reveal, and external API token failures are rate-limited in memory and written to the operation log.

## API Overview

### Discovery

- `GET /api/docs`
  Returns API metadata, auth hints, and endpoint index.
- `GET /api/health`
  Simple health endpoint.

### Read endpoints

- `GET /api/v1/snapshot`
  Full runtime snapshot for integrations.
- `GET /api/v1/auth/status`
  Auth status summary.
- `GET /api/v1/drones`
  Current aircraft list.
- `GET /api/v1/drones/{sn}`
  One aircraft detail.
- `GET /api/v1/tracks/{sn}`
  Track points for one aircraft.
- `GET /api/v1/aps`
  Current AP list.
- `GET /api/v1/logs?type=event|scan|ap&limit=200`
  Event/scan/AP logs.

### Write endpoints

- `POST /api/v1/history/clear`
  Clear all history.
- `POST /api/v1/history/delete`
  Delete one aircraft history item.
- `POST /api/v1/tracks/clear`
  Clear all tracks or one track, depending on body.
- `POST /api/v1/config/reload`
  Reload config from disk.

## Settings Page

Open:

- `/settings`

It supports:

- visual editing of runtime/capture settings
- visual editing of multiple WeCom channels
- visual editing of multiple alarm zones
- base station position editing
- browser geolocation fill-in for base station position
- raw `rid_config.json` editing

## Logs Page

Open:

- `/logs`

It provides:

- runtime log
- operation/audit log
- full scan log
- unified diff between runtime and scan logs
- text export for one view or ZIP export for all views
- API documentation view
- jump to hardware assistant

Sensitive fields stay masked in visual mode:

- WeCom webhook keys
- API token

Leaving a masked/empty secret field unchanged keeps the stored value.

## Enterprise WeCom Notifications

The config now supports multiple webhook channels:

```json
{
  "notify": {
    "enabled": true,
    "send_timeout_sec": 8,
    "notify_reonline": true,
    "reonline_cooldown_sec": 300,
    "wecom_webhooks": [
      {
        "name": "Default",
        "enabled": true,
        "key": "YOUR_WEBHOOK_KEY"
      },
      {
        "name": "Backup",
        "enabled": false,
        "key": "YOUR_SECOND_KEY"
      }
    ]
  }
}
```

Behavior:

- online notifications are sent to all enabled channels
- test notifications are sent to all enabled channels
- legacy `notify.wecom_webhook_key` is still accepted for backward compatibility

## Alarm Zones

The config now supports multiple rectangular alarm zones:

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

Behavior:

- enabled zones are drawn on the map in red
- a drone entering a zone triggers fullscreen browser warning UI
- browser notification is sent if permission has been granted
- legacy `web.alarm_zone` is still accepted for backward compatibility

## Hardware Assistant

Open directly:

- `/hardware-assistant`

Supported operations:

- list wireless interfaces
- inspect `iw dev`, `iw info`, `iw link`
- switch monitor / managed mode
- restart NIC
- set channel
- restart the main scanner process

## Export / Import Helpers

Useful helper APIs from the built-in UI:

- `GET /api/tools/export/all`
- `GET /api/tools/export/track?sn=<SN>`
- `POST /api/tools/import/all`
- `POST /api/tools/import/track`

## Git / Privacy Rules

Before pushing to GitHub:

- do not commit `rid_config.json`
- do not commit real webhook keys
- do not commit real API tokens
- do not commit runtime-generated history/cache files
- commit `rid_config.example.json` only

## Notes

- The browser geolocation helper may require HTTPS or localhost, depending on browser security policy.
- The map base station, alarm zones, track drawing, and aircraft/pilot markers are all driven by runtime state from `run.py`.
- For current machine-readable endpoint metadata, prefer `GET /api/docs`.
