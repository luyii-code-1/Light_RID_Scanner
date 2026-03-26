# Light RID Scanner

Light RID Scanner is a practical Remote ID / OpenDroneID Wi-Fi monitor for Raspberry Pi fixed-station deployments.

The project is built around one runtime file (`run.py`) and focuses on long-running stability:
- live web UI (drone list, AP list, map, tracks)
- history and track persistence
- config guard + rollback
- hardware assistant page for NIC recovery operations
- optional Basic Auth (username/password stored as SHA256 hashes)

## Runtime

Required:
- Linux (Raspberry Pi OS recommended)
- Python 3.10+
- wireless NIC with monitor mode support
- root privileges for mode/channel operations

Start:

```bash
sudo ~/rid/.venv/bin/python3 run.py --no-tui
```

Default web URL:

- `http://<device-ip>:4600/`

## Files

- `run.py`: scanner, parser, HTTP/WS server, embedded web pages
- `rid_models.json`: model prefix map
- `rid_config.example.json`: safe template for Git
- `rid_config.json`: local runtime config (do not commit)

Runtime-generated files:
- `rid_config.json.rollback`
- `rid_history_cache.json`

## Authentication

Set hashes in `rid_config.json`:

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

Generate hash values:

```bash
python3 - <<'PY'
import hashlib
print("user:", hashlib.sha256("your_user".encode()).hexdigest())
print("pass:", hashlib.sha256("your_pass".encode()).hexdigest())
PY
```

## Hardware Assistant

Open from main page button, or directly:

- `/hardware-assistant`

Supported operations:
- list interfaces
- `iw dev`, `iw info`, `iw link`
- switch monitor/managed mode
- restart NIC
- set channel
- restart main service process

## Useful APIs

- `GET /api/interfaces`
- `GET /api/tracks/get?sn=<SN>`
- `POST /api/tracks/clear`
- `POST /api/history/delete`
- `POST /api/history/clear`
- `GET /api/tools/export/all`
- `GET /api/tools/export/track?sn=<SN>`
- `POST /api/tools/import/all`
- `POST /api/tools/import/track`
- `GET /api/hw/status`
- `POST /api/hw/op`

## Commit Rules

Before pushing to GitHub:
- do not commit `rid_config.json`
- do not commit history/cache/output artifacts
- commit `rid_config.example.json` only
