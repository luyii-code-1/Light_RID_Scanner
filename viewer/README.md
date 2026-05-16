# Light RID Node Center Viewer

`viewer/server.py` is a standalone node-center web service for aggregating multiple `station_edition` base-station APIs.

Run it from the repository root:

```powershell
python viewer\server.py --host 0.0.0.0 --port 4700
```

Open `http://127.0.0.1:4700/`.

The viewer stores its own configuration in `viewer/cfg.db`: node API root URLs, node API tokens, optional viewer login settings, and the viewer-side history aggregation cache. Live aircraft, base-station status, AP data, and normal track refreshes are fetched from station APIs on demand.

The live/history UI is built from the same Station page template used by `station_edition/light_rid/web_server.py`. Viewer-specific code only patches the data/API layer and removes Station-only controls from the DOM.

- `/settings`: Station-styled viewer settings with host status, default map center/zoom, password login, SSO check login, and EULA controls.
- `/nodes`: node manager with add/edit/test/delete, basic info cards, load cards and charts, scan counts, one-click remote SSO URL creation, and batch restart/model-database update actions.
- Live refresh fetches enabled nodes concurrently and merges duplicate aircraft by `SN`; when multiple base stations see the same aircraft, the merged card includes `发现的基站:{name1}{name2}` and conflicting fields prefer the strongest RSSI version.
- History aggregation is available from `/settings`. It pulls all enabled station snapshots/tracks, merges duplicate aircraft onto one timeline, stores the result in `viewer/cfg.db`, and defaults to a 24-hour cache TTL.

Each station node should expose the `station_edition` token API, especially:

- `GET /api/v1`
- `GET /api/health`
- `GET /api/v1/snapshot`
- `GET /api/v1/drones`

When adding a node, enter only the URL root, for example `http://192.168.1.10:4600`. Paths, query strings, fragments, and user-info are rejected; the viewer appends `/api/v1` paths itself and tests real API responses before saving.

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
