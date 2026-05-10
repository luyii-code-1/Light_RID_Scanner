# Light RID Scanner

[English](README.md) | [简体中文](README.zh-CN.md)

Light RID Scanner is a fixed-station Remote ID / OpenDroneID Wi-Fi monitor designed for Raspberry Pi and other Linux-based capture nodes.

## Highlights

- Modern LAN web UI
- Dedicated `/settings` page for visual config editing
- Dedicated `/hardware-assistant` page for NIC / `iw` operations
- Server-side notification center, synchronized across browser sessions
- RID history and track persistence
- Pilot position extraction from RID `System` messages
- Export helpers for aircraft detail and per-aircraft tracks
- Optional token-protected external API
- Optional browser login / session auth for the web UI
- Passkey-based browser login after an initial username/password bootstrap
- Separate settings-file and scan-data import/export flows in `/settings`
- Configurable browser session lifetime, defaulting to 30 minutes
- Enterprise WeCom notifications with multiple webhook channels
- Multiple custom alarm zones drawn on the map
- DJI newer-firmware RID Beacon parsing, with UAS ID and firmware-type display
- Password-rechecked raw config tree browsing/edit/save/delete inside the config root
- One-click runtime security repair, `iw` install, and systemd service registration/update
- Online RID model map updates from a configurable URL
- Optional remote config updates from a configurable URL
- Manual app version check by Git commit comparison
- Optional host load trends for CPU, memory, temperature, system load, and AP count

## Runtime

Recommended environment:

- Linux
- Raspberry Pi OS recommended
- 64-bit OS for the `linux-arm64` release artifact
- Wireless NIC with monitor mode support
- Root privileges for monitor mode / channel switching
- `iw` and `hostapd` when using NIC binding with AP hotspot mode

Deploy the Linux binary:

```bash
install -m 0755 light_rid_scanner-linux-arm64 /opt/light-rid/light_rid_scanner
```

The runtime directory should keep the binary and runtime data together:

```text
/opt/light-rid/light_rid_scanner
/opt/light-rid/rid_config.json
/opt/light-rid/rid_models.json
/opt/light-rid/EULA.md
```

Systemd should execute the binary directly:

```ini
ExecStart=/opt/light-rid/light_rid_scanner --config /opt/light-rid/rid_config.json --no-tui
```

Default web URL:

- `http://<device-ip>:4600/`

## Fixed NIC Binding and OOBE

- The scanner no longer auto-rotates across NICs.
- `basic.iface` is treated as a fixed binding. If that NIC is missing, the service stays alive in degraded mode and shows a configuration warning instead of silently switching to another adapter.
- `basic.lost_timeout` controls aircraft offline detection in seconds. The default is 15 seconds.
- Settings and OOBE include a **Custom NIC Binding** flow. Each detected NIC can be assigned to `scan`, `web`, `ap_web`, `disabled`, `idle`, or `none`; the `scan` role is synchronized back to `basic.iface`.
- The `ap_web` role configures an AP hotspot profile through `hostapd`, starts the built-in DHCP server on `172.16.0.0/24`, and exposes the web UI at `172.16.0.1:80` when the service has the required Linux capabilities.
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
  Visual settings editor, password/passkey login controls, raw config editor, runtime security repair, config/app update tools, token/API overview, alarm zone editor, notification editor.
- `/hardware-assistant`
  Visual hardware helper for NIC status, `iw` inspection, monitor/managed switching, channel change, NIC restart, and process restart.

## Important Files

- `run.py`
  Thin source/build entry point.
- `light_rid/`
  Split scanner, parser, HTTP/WS server, embedded pages, API handlers, settings, auth, hardware, and CLI/TUI modules.
- `light_rid_scanner`
  Installed Linux one-file runtime binary on deployment targets.
- `rid_models.json`
  Model prefix mapping.
- `rid_config.example.json`
  Safe Git-tracked example config.
- `rid_config.json`
  Real runtime config. Do not commit it.
- `EULA.md`
  Source text shown by the built-in EULA acceptance flow.
- `rid_history_cache.json`
  Runtime-generated history / track cache.
- `rid_config.json.rollback`
  Rollback copy for config recovery.
- `rid_build_info.json`
  Local build marker used for the UI version string, for example `commit:ba15d57#3`.
- Temp directory `light_rid_scanner/host_metrics.jsonl`
  Runtime host-metrics store. It is recreated automatically and should not be committed.

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
  Browser UI login/session auth, passkeys, and SSO links.
- `api`
  External token API auth.
- `model_update`
  Online model-map update settings.
- `config_update`
  Optional remote config update settings.
- `app_update`
  Upstream commit-check settings for manual version comparison.
- `metrics`
  Host-metrics retention settings.

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
  http://0.0.0.0:4600/api/v1/snapshot
```

```bash
curl -H "Authorization: Bearer YOUR_TOKEN" \
  http://0.0.0.0:4600/api/v1/drones
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
      "<trusted-lan-cidr>"
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
    "session_ttl_min": 30,
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

SSO-style login is available for trusted launchers. The URL uses the configured username/password SHA-256 hashes plus a server-side `check` code:

```text
/login?user=<sha256(username)>&password=<sha256(password)>&check=<server-check-code>
```

The Settings page generates and stores the `check` code. Deleting that item from the Settings list invalidates the link immediately.

For compatibility with old local shortcuts, the password separator can also be parsed from these forms, but a valid `check` code is still required:

```text
/login?user=<sha256(username)>,password=<sha256(password)>&check=<server-check-code>
/login?user=<sha256(username)>?password=<sha256(password)>?check=<server-check-code>
```

Settings generates SSO links after a fresh username/password check. The generated URL can be used by an external SSO launcher and remains valid until its `check` code is deleted from the list.

When a browser session expires, page API requests return an auth failure and the built-in pages redirect back to `/login`.

### Session-only helper endpoints

These are meant for the built-in web UI and current browser session:

- `GET /api/notifications?limit=200`
- `POST /api/notifications`
- `POST /api/notifications/delete`
- `POST /api/notifications/clear`
- `GET /api/settings/view`
- `GET /api/settings/runtime`
- `GET /api/settings/metrics?window=12h|24h|7d`
- `GET /api/settings/systemd/status`
- `GET /api/settings/api-docs`
- `GET /api/logs/view?type=runtime|operation|scan|scan_diff|ap`
- `GET /api/logs/export?type=all|runtime|operation|scan|scan_diff|ap`
- `POST /api/settings/visual/test`
- `POST /api/settings/visual/save`
- `POST /api/settings/raw/unlock`
- `POST /api/settings/raw/save`
- `GET /api/config/file?path=<within-config-root>`
- `POST /api/config/file/delete`
- `POST /api/settings/notify/test`
- `POST /api/settings/passkey/start`
- `POST /api/settings/passkey/finish`
- `POST /api/settings/passkey/delete`
- `POST /api/passkey/login/start`
- `POST /api/passkey/login/finish`
- `GET /api/settings/models/list`
- `POST /api/settings/models/save`
- `POST /api/settings/models/upsert`
- `POST /api/settings/models/update`
- `POST /api/settings/app-update/check`
- `POST /api/settings/systemd/register`
- `POST /api/settings/iw/install`
- `POST /api/settings/security/repair`
- `POST /api/settings/login-link/create`
- `POST /api/settings/login-link/delete`
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
- Generating a managed SSO login link also requires the same fresh username/password check
- Login, SSO login link, token reveal, and external API token failures are rate-limited in memory and written to the operation log.

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
- online RID model-map updates, with a configurable URL and manual update button
- optional remote config updates from a configurable URL
- optional host load trend cards for CPU, memory, temperature, load, and AP count
- selectable host-metrics windows: 12 hours, 24 hours, and 7 days
- configurable host-metrics retention, defaulting to 7 days
- managed SSO login link generation and deletion after username/password re-check
- passkey registration/deletion for browser login
- raw config tree browsing/edit/save/delete after password re-check
- runtime security repair, `iw` install, and systemd service registration/update
- manual upstream app commit comparison

### Online model-map updates

The Settings page can update `rid_models.json` from a remote JSON file. The default URL is:

```text
https://raw.githubusercontent.com/luyii-code-1/Light_RID_Scanner/refs/heads/main/rid_models.json
```

Behavior:

- automatic checks run once per day when enabled
- manual update uses the same URL field
- the URL must start with `http://` or `https://`
- successful and failed update attempts are written to the operation log and notification center
- the same Settings card can edit `rid_models.json` as a prefix/model list
- N/A aircraft detail cards can add a local mapping or open a prefilled GitHub Issue / PR edit page


### Passkeys, raw config, and runtime repair

- Passkeys are bootstrapped from the existing web username/password once, then stored inside `auth.passkeys`.
- Raw config editing is limited to files inside the active config root and requires a short-lived secondary unlock from the current browser session.
- The runtime repair card can create/confirm the dedicated `rid` service user, grant capture/hotspot capabilities, install wireless tools, and register/update `light-rid-scanner.service`.
- Binary deployments should keep the systemd unit pointed at the installed `light_rid_scanner` binary, current config path, and `--no-tui` service mode.

### Host load trends

The Settings page shows host trends as separate mini charts:

- CPU
- memory
- temperature
- system load
- AP count

Metrics are disabled by default. When enabled in `/settings`, they are sampled about once per minute and stored in the system temp directory under `light_rid_scanner/host_metrics.jsonl`. The file is created automatically, kept across service restarts, and pruned according to `metrics.retention_days`.

### Build version

The UI version string is shown as:

```text
commit:<git-short-commit>#<local-build-number>
```

`rid_build_info.json` stores the current short commit and local build number. The CI workflow produces one-file Linux artifacts for deployment, including `light_rid_scanner-linux-arm64` for 64-bit Raspberry Pi OS.

The Settings page can manually compare the local app commit with the upstream Git commit. This check only reports whether a newer commit exists; it does not download, apply, or restart code automatically.

The release line prepared by this checkout is `v2.0`, but the UI keeps using the commit-based build label above so local builds remain traceable.

## Notification Center

The notification center is backed by the server, not browser local storage. It keeps recent runtime messages in memory and exposes them to all active browser sessions through `/api/notifications`.

Current notification sources include:

- aircraft online/offline events
- alarm-zone events
- model-map update results
- manual browser notices posted by the built-in UI

Entries can be deleted individually or cleared from the UI.

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

- `GET /api/settings/export/settings`
- `GET /api/settings/export/scan-data`
- `POST /api/settings/import/settings`
- `POST /api/settings/import/scan-data`
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

## OpenDroneID Reference

- Open Drone ID Core C Library (official): https://github.com/opendroneid/opendroneid-core-c
- OpenDroneID specs repository: https://github.com/opendroneid/specs
- The specs repository explicitly notes that it contains early drafts; for final ASTM Remote ID text, obtain the official ASTM F3411 standard directly.
