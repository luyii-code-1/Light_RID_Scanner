"""Shared HTML helpers for Station-styled viewer pages."""

from __future__ import annotations

import ast
from functools import lru_cache

from viewer.paths import APP_NAME, APP_VERSION, STATION_WEB_SERVER


@lru_cache(maxsize=1)
def station_settings_css() -> str:
    if not STATION_WEB_SERVER.exists():
        raise FileNotFoundError(f"missing station web template: {STATION_WEB_SERVER}")
    tree = ast.parse(STATION_WEB_SERVER.read_text(encoding="utf-8"))
    html = ""
    for node in tree.body:
        if isinstance(node, ast.FunctionDef) and node.name == "_build_settings_html":
            for stmt in node.body:
                if isinstance(stmt, ast.Return):
                    html = str(ast.literal_eval(stmt.value))
                    break
        if html:
            break
    start = html.find("<style>")
    end = html.find("</style>", start)
    if start < 0 or end < 0:
        raise RuntimeError("station settings style block not found")
    return html[start + len("<style>") : end]


def station_page(title: str, body: str, script: str, extra_css: str = "") -> str:
    css = station_settings_css()
    return f"""<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} - {APP_NAME}</title>
<style>
{css}
{extra_css}
</style></head><body><div class="wrap">
{body}
</div>
<script>
window.LIGHT_RID_VIEWER_VERSION = {APP_VERSION!r};
{script}
</script></body></html>"""
