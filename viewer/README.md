# Light RID Node Center Viewer

`viewer/server.py` is a standalone node-center web service for aggregating multiple `station_edition` base-station APIs.

Run it from the repository root:

```powershell
python viewer\server.py --host 0.0.0.0 --port 4700
```

Open `http://127.0.0.1:4700/`.

The viewer stores only its own configuration in `viewer/cfg.db`: node API URLs, node API tokens, and optional viewer login settings. It does not store remote aircraft, base-station status, tracks, AP data, or other live node payloads; those are fetched from each station API on every refresh.

Each station node should expose the `station_edition` token API, especially:

- `GET /api/health`
- `GET /api/v1/snapshot`
- `GET /api/v1/drones`

The viewer sends the configured token as both `X-API-Token` and `Authorization: Bearer <token>`.

Build a standalone viewer binary locally:

```powershell
python pytools\build_viewer.py --target x86_64
```

CI builds viewer artifacts through `.github/workflows/build-viewer.yml` for Linux `x86_64`, Linux `arm64`, and Windows `x86_64`.
