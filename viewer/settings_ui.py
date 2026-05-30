"""Vue-driven viewer settings page."""

from __future__ import annotations

from viewer.paths import ASSETS_DIR
from viewer.ui_common import station_page


def _viewer_settings_asset_url() -> str:
    asset_url = "/assets/vue/viewer-settings.js"
    asset_path = ASSETS_DIR / "vue" / "viewer-settings.js"
    try:
        st = asset_path.stat()
        return f"{asset_url}?v={int(st.st_mtime)}-{int(st.st_size)}"
    except OSError:
        return asset_url


def build_settings_page() -> str:
    body = '<div id="viewer-settings-root"></div>'
    extra_css = """
.viewer-settings-root{display:grid;gap:0}
.viewer-settings-root .topbar{padding:14px 18px;border:1px solid color-mix(in srgb,var(--border) 92%,transparent);border-radius:22px;background:linear-gradient(180deg,color-mix(in srgb,var(--card) 96%,transparent),color-mix(in srgb,var(--card2) 94%,transparent));box-shadow:0 10px 28px rgba(0,0,0,.18)}
.viewer-settings-root .draft-bar{border-radius:20px;box-shadow:0 8px 24px rgba(0,0,0,.16)}
.viewer-settings-root .settings-jump .btn{border-radius:10px}
.viewer-settings-root .card{border-radius:22px;box-shadow:0 8px 24px rgba(0,0,0,.18)}
.viewer-settings-root .status{white-space:pre-line}
.viewer-settings-root .stat-card{border-radius:18px;background:color-mix(in srgb,var(--surface-tonal, #17283d) 72%,var(--card))}
body.theme-dark .viewer-settings-root .topbar,
body.theme-dark .viewer-settings-root .draft-bar,
body.theme-dark .viewer-settings-root .card{background:color-mix(in srgb,var(--card) 96%,#08111d)}
body.theme-dark .viewer-settings-root .stat-card{background:color-mix(in srgb,var(--surface-tonal, #12253b) 76%,var(--card))}
body.theme-light .viewer-settings-root .topbar{box-shadow:0 10px 28px rgba(15,23,42,.08)}
body.theme-light .viewer-settings-root .draft-bar{box-shadow:0 8px 24px rgba(15,23,42,.06)}
body.theme-light .viewer-settings-root .card{box-shadow:0 8px 24px rgba(15,23,42,.08)}
body.theme-light .viewer-settings-root .stat-card{background:color-mix(in srgb,var(--surface-tonal, #eaf2ff) 36%,white)}
"""
    script = "window.__RID_VIEWER_SETTINGS_VUE__=true;"
    return station_page(
        "Viewer 设置",
        body,
        script,
        extra_css=extra_css,
        extra_scripts=(_viewer_settings_asset_url(),),
    )
