"""Station UI template reuse for the viewer live/history pages."""

from __future__ import annotations

import ast

from viewer.paths import APP_VERSION, STATION_WEB_SERVER


_CACHE: dict[str, str] | None = None


def _inject_html_once(html_src: str, marker: str, extra: str) -> str:
    if marker not in html_src:
        return html_src + extra
    return html_src.replace(marker, extra + marker, 1)


def _load_station_template_parts() -> dict[str, str]:
    global _CACHE
    if _CACHE is not None:
        return dict(_CACHE)
    if not STATION_WEB_SERVER.exists():
        raise FileNotFoundError(f"missing station web template: {STATION_WEB_SERVER}")
    tree = ast.parse(STATION_WEB_SERVER.read_text(encoding="utf-8"))
    wanted = {"_PAGE_HTML", "_MAIN_PAGE_PATCH_CSS", "_MAIN_PAGE_PATCH_JS"}
    found: dict[str, str] = {}
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        for target in node.targets:
            if isinstance(target, ast.Name) and target.id in wanted:
                found[target.id] = str(ast.literal_eval(node.value))
    missing = wanted - set(found)
    if missing:
        raise RuntimeError("station template missing: " + ", ".join(sorted(missing)))
    _CACHE = dict(found)
    return found


def _viewer_patch_js() -> str:
    return r"""
(function(){
  document.body.classList.add('viewer-mode');
  var viewerThemeBound = false;
  function qs(id){ return document.getElementById(id); }
  function removeNode(node){ if(node && node.parentNode) node.parentNode.removeChild(node); }
  function removeId(id){ removeNode(qs(id)); }
  function removeClosestById(id, selector){
    var node = qs(id);
    if(node && node.closest) removeNode(node.closest(selector));
  }
  function patchTitle(){
    try{ document.title = 'Light RID Node Center'; }catch(_e){}
    var title = document.querySelector('header h1');
    if(title) title.textContent = 'Light RID Node Center';
    var ver = document.querySelector('.app-version-label');
    if(ver && ver.textContent.indexOf('viewer') < 0) ver.textContent = String(ver.textContent || '') + ' viewer';
  }
  function syncViewerBaseLabels(){
    var rows = Array.isArray(window.latestDroneRows) ? window.latestDroneRows : [];
    var bySn = {};
    rows.forEach(function(e){
      var sn = String((e && e.sn) || '');
      if(sn) bySn[sn] = e;
    });
    Array.prototype.slice.call(document.querySelectorAll('.live-card[data-sn]')).forEach(function(card){
      var sn = card.getAttribute('data-sn') || '';
      var e = bySn[sn] || {};
      var text = String(e.discovered_base_text || '');
      var old = card.querySelector('.viewer-base-label');
      if(!text){
        if(old && old.parentNode) old.parentNode.removeChild(old);
        return;
      }
      if(!old){
        old = document.createElement('div');
        old.className = 'viewer-base-label';
        var grid = card.querySelector('.live-card-grid');
        if(grid && grid.parentNode) grid.parentNode.insertBefore(old, grid);
        else card.appendChild(old);
      }
      old.textContent = text;
      old.title = text;
    });
  }
  function patchViewerFunctions(){
    if(typeof window.buildInfoHtml === 'function' && !window.buildInfoHtml.__viewerPatched){
      var oldInfo = window.buildInfoHtml;
      window.buildInfoHtml = function(e){
        var html = oldInfo(e);
        var text = String((e && e.discovered_base_text) || '');
        if(text && html.indexOf('发现的基站') < 0){
          html = html.replace('<div class="info-grid">', '<div class="info-grid"><div class="info-row"><span class="k">发现的基站</span><span class="v">'+esc(text)+'</span></div>');
        }
        return html;
      };
      window.buildInfoHtml.__viewerPatched = true;
    }
    if(typeof window.renderLiveCards === 'function' && !window.renderLiveCards.__viewerPatched){
      var oldCards = window.renderLiveCards;
      window.renderLiveCards = function(list){
        oldCards(list);
        syncViewerBaseLabels();
      };
      window.renderLiveCards.__viewerPatched = true;
    }
  }
  function ensureThemeButton(){
    var settings = qs('btn-settings');
    if(settings && !qs('btn-theme')){
      var theme = document.createElement('button');
      theme.className = settings.className || 'btn-mini';
      theme.id = 'btn-theme';
      theme.type = 'button';
      theme.textContent = document.body.classList.contains('theme-light') ? '深色' : '浅色';
      if(settings.parentNode) settings.parentNode.insertBefore(theme, settings.nextSibling);
    }
    var btn = qs('btn-theme');
    if(btn){
      btn.style.display = '';
      if(!viewerThemeBound){
        btn.addEventListener('click', function(ev){
          ev.preventDefault();
          ev.stopPropagation();
          if(typeof window.applyTheme === 'function'){
            window.applyTheme(document.body.classList.contains('theme-light') ? 'dark' : 'light');
          }
          setTimeout(ensureThemeButton, 0);
        });
        viewerThemeBound = true;
      }
    }
  }
  function deleteStationOnlyUi(){
    ['btn-freeze','btn-web-notify','btn-clear-history','btn-adv-open','btn-hw-assistant','btn-logs','adv-modal','notify-center-button','notify-center-panel'].forEach(removeId);
    removeClosestById('ap-list', '.panel');
    removeClosestById('ap-list-count', '.panel');
    var settings = qs('btn-settings');
    if(settings && settings.getAttribute('data-viewer-bound') !== '1'){
      settings.setAttribute('data-viewer-bound','1');
      settings.textContent = '设置';
      settings.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); location.href='/settings'; });
    }
    if(settings && !qs('btn-viewer-nodes')){
      var nodes = document.createElement('button');
      nodes.className = settings.className || 'btn';
      nodes.id = 'btn-viewer-nodes';
      nodes.type = 'button';
      nodes.textContent = '节点管理';
      nodes.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); location.href='/nodes'; });
      if(settings.parentNode) settings.parentNode.insertBefore(nodes, settings.nextSibling);
    }
    ensureThemeButton();
    var morePop = qs('main-more-pop');
    if(morePop){
      Array.prototype.slice.call(morePop.querySelectorAll('button')).forEach(function(btn){
        if(btn.id === 'btn-logs') removeNode(btn);
      });
    }
  }
  function tick(){ patchTitle(); patchViewerFunctions(); deleteStationOnlyUi(); syncViewerBaseLabels(); }
  var timer = setInterval(tick, 250);
  setTimeout(function(){ clearInterval(timer); tick(); }, 8000);
})();
"""


def build_station_viewer_page() -> str:
    parts = _load_station_template_parts()
    html_src = parts["_PAGE_HTML"]
    html_src = html_src.replace("__APP_VERSION_LABEL__", "viewer " + APP_VERSION)
    html_src = html_src.replace("<title>Light RID Scanner</title>", "<title>Light RID Node Center</title>")
    html_src = html_src.replace("Light RID Scanner", "Light RID Node Center")
    viewer_css = """
.viewer-base-label{margin:8px 0 6px;padding:6px 8px;border:1px solid var(--border);border-radius:4px;background:color-mix(in srgb,var(--blue) 8%,var(--panel2));color:var(--txt);font:600 12px/1.35 var(--font-ui);white-space:normal;word-break:break-word}
body.theme-light .viewer-base-label{background:color-mix(in srgb,var(--blue) 7%,var(--panel2))}
"""
    html_src = _inject_html_once(html_src, "</style>", parts["_MAIN_PAGE_PATCH_CSS"] + "\n" + viewer_css + "\n")
    html_src = _inject_html_once(
        html_src,
        "</body>",
        "<script>\n" + parts["_MAIN_PAGE_PATCH_JS"] + "\n" + _viewer_patch_js() + "\n</script>\n",
    )
    return html_src
