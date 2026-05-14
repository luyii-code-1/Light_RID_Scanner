# Light RID Node Center Viewer

`viewer/server.py` is a standalone node-center web service for aggregating multiple `station_edition` base-station APIs.

Run it from the repository root:

```powershell
python viewer\server.py --host 0.0.0.0 --port 4700
```

Open `http://127.0.0.1:4700/`.

The viewer stores only its own configuration in `viewer/cfg.db`: node API URLs, node API tokens, and optional viewer login settings. It does not store remote aircraft, base-station status, tracks, AP data, or other live node payloads; those are fetched from each station API on every refresh.

The live/history UI is built from the same Station page template used by `station_edition/light_rid/web_server.py`. Viewer-specific code only patches the data/API layer and removes Station-only controls from the DOM.

- `/settings`: Station-styled viewer settings with host status, default map center/zoom, password login, SSO check login, and EULA controls.
- `/nodes`: node manager with add/edit/test/delete, basic info cards, load cards and charts, scan counts, one-click remote SSO URL creation, and batch restart/model-database update actions.

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

Module layout:

- `viewer/server.py`: HTTP, API, and WebSocket routing.
- `viewer/storage.py`: SQLite config, node records, and viewer auth/session state.
- `viewer/aggregation.py`: live station API fetching and aggregation.
- `viewer/station_ui.py`: Station template loading and viewer DOM patch.
- `viewer/settings_ui.py`: Station-styled viewer settings page.
- `viewer/nodes_ui.py`: Station-styled node manager page.
- `viewer/ui_common.py`: shared Station settings CSS extraction.
