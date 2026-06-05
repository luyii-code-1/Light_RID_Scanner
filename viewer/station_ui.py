"""Station UI template reuse for the viewer live/history pages."""

from __future__ import annotations

import ast

from viewer.paths import APP_VERSION, ASSETS_DIR, STATION_WEB_SERVER


_CACHE: dict[str, str] | None = None


def _inject_html_once(html_src: str, marker: str, extra: str) -> str:
    if marker not in html_src:
        return html_src + extra
    return html_src.replace(marker, extra + marker, 1)

def _rid_home_asset_url() -> str:
    asset_url = "/assets/vue/rid-home.js"
    asset_path = ASSETS_DIR / "vue" / "rid-home.js"
    try:
        st = asset_path.stat()
        return f"{asset_url}?v={int(st.st_mtime)}-{int(st.st_size)}"
    except OSError:
        return asset_url


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
  var viewerDataLoaded = false;
  var viewerLoadingStartedAt = 0;
  var viewerLoadingTargetText = '远端 Station 节点';
  var viewerLoadingTimeoutSec = 15;
  function qs(id){ return document.getElementById(id); }
  function removeNode(node){ if(node && node.parentNode) node.parentNode.removeChild(node); }
  function removeId(id){ removeNode(qs(id)); }
  function escViewer(v){
    return String(v == null ? '' : v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
  }
  function removeClosestById(id, selector){
    var node = qs(id);
    if(node && node.closest) removeNode(node.closest(selector));
  }
  function stripDetailReparseUi(){
    Array.prototype.slice.call(document.querySelectorAll('.detail-reparse-box')).forEach(removeNode);
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
    if(typeof window.detailReparseControls === 'function' && !window.detailReparseControls.__viewerDisabled){
      window.detailReparseControls = function(){ return ''; };
      window.detailReparseControls.__viewerDisabled = true;
    }
    if(typeof window.buildInfoHtml === 'function' && !window.buildInfoHtml.__viewerPatched){
      var oldInfo = window.buildInfoHtml;
      window.buildInfoHtml = function(e){
        var html = oldInfo(e);
        var text = String((e && e.discovered_base_text) || '');
        if(text && html.indexOf('发现的基站') < 0){
          html = html.replace('<div class="info-grid">', '<div class="info-grid"><div class="info-row"><span class="k">发现的基站：</span><span class="v">'+esc(text)+'</span></div>');
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
    if(typeof window.onData === 'function' && !window.onData.__viewerLoadingPatched){
      var oldOnData = window.onData;
      window.onData = function(d){
        var isLoading = !!(d && d.meta && d.meta.viewer_loading);
        if(isLoading){
          var targets = Array.isArray(d.meta.viewer_loading_targets) ? d.meta.viewer_loading_targets : [];
          if(targets.length){
            viewerLoadingTargetText = targets.slice(0, 4).join('、') + (targets.length > 4 ? ' 等' : '');
          }
          viewerLoadingTimeoutSec = Math.max(5, Number(d.meta.viewer_loading_timeout_sec || 15) || 15);
        }else{
          viewerDataLoaded = true;
          clearViewerLoadingState();
        }
        oldOnData(d);
        setTimeout(tick, 0);
        if(isLoading) setViewerLoadingState();
      };
      window.onData.__viewerLoadingPatched = true;
    }
  }
  function loadingMessage(){
    if(!viewerLoadingStartedAt) viewerLoadingStartedAt = Date.now();
    var elapsed = Math.floor((Date.now() - viewerLoadingStartedAt) / 1000);
    var remain = Math.max(0, viewerLoadingTimeoutSec - elapsed);
    if(remain > 0){
      return '正在从 ' + viewerLoadingTargetText + ' 读取数据，预计 ' + remain + 's 后提示超时';
    }
    return viewerLoadingTargetText + ' 返回较慢，仍在等待数据';
  }
  function loadingState(){
    if(!viewerLoadingStartedAt) viewerLoadingStartedAt = Date.now();
    var elapsed = Math.floor((Date.now() - viewerLoadingStartedAt) / 1000);
    var remain = Math.max(0, viewerLoadingTimeoutSec - elapsed);
    if(remain > 0){
      return {
        detail: '\u6b63\u5728\u5411 ' + viewerLoadingTargetText + ' \u83b7\u53d6\u6570\u636e',
        status: '\u5df2\u7b49\u5f85 ' + elapsed + 's\uff0c\u9884\u8ba1 ' + remain + 's \u540e\u63d0\u793a\u8d85\u65f6'
      };
    }
    return {
      detail: '\u5411 ' + viewerLoadingTargetText + ' \u83b7\u53d6\u6570\u636e\u8d85\u65f6\uff0c\u4ecd\u5728\u7b49\u5f85\u8fd4\u56de',
      status: '\u5df2\u7b49\u5f85 ' + elapsed + 's\uff0c\u6682\u4e0d\u5173\u95ed\u9875\u9762'
    };
  }
  function ensureLoadingOverlay(state){
    var host = qs('rid-loading-overlay');
    if(!host){
      host = document.createElement('div');
      host.id = 'rid-loading-overlay';
      host.className = 'rid-loading-overlay';
      host.innerHTML = '<div class="rid-loading-shell"><div class="rid-loading-box"><div class="rid-loading-head"><div class="rid-loading-spinner"><div class="rid-loading-spinner-core"><div class="rid-loading-bars"><span></span><span></span><span></span><span></span><span></span></div></div></div><div class="rid-loading-copy-wrap"><div class="rid-loading-title">\u6b63\u5728\u8bfb\u53d6\u6570\u636e</div><div class="rid-loading-copy"></div></div></div><div class="rid-loading-meta"><div class="rid-loading-meta-line"><span class="rid-loading-meta-label">\u5f53\u524d\u76ee\u6807</span><span class="rid-loading-meta-value" data-role="target"></span></div><div class="rid-loading-meta-line"><span class="rid-loading-meta-label">\u8be6\u7ec6\u72b6\u6001</span><span class="rid-loading-meta-value" data-role="status"></span></div></div></div></div>';
      document.body.appendChild(host);
    }
    var title = host.querySelector('.rid-loading-title');
    var copy = host.querySelector('.rid-loading-copy');
    if(copy) copy.textContent = state.detail;
    if(title) title.textContent = '\u6b63\u5728\u8bfb\u53d6\u6570\u636e';
    var target = host.querySelector('[data-role="target"]');
    if(target) target.textContent = viewerLoadingTargetText;
    var status = host.querySelector('[data-role="status"]');
    if(status) status.textContent = state.status;
    host.classList.add('show');
    document.body.classList.add('rid-loading-active');
  }
  function clearViewerLoadingState(){
    var host = qs('rid-loading-overlay');
    if(host) host.classList.remove('show');
    document.body.classList.remove('rid-loading-active');
    try{
      var rows = Array.isArray(window.latestDroneRows) ? window.latestDroneRows : [];
      if(typeof window.renderDroneTable === 'function') window.renderDroneTable(rows);
      if(typeof window.renderLiveCards === 'function') window.renderLiveCards(rows);
    }catch(_e){}
  }
  function setViewerLoadingState(){
    if(viewerDataLoaded) return;
    var msg = loadingState();
    ensureLoadingOverlay(msg);
    var count = qs('live-card-count');
    if(count) count.textContent = '-';
    var hint = qs('map-hint');
    if(hint) hint.textContent = msg.detail;
    var status = qs('ws-status');
    if(status) status.textContent = '正在读取数据';
    var ts = qs('cur-ts');
    if(ts) ts.textContent = '读取中';
    if(status) status.textContent = '\u6b63\u5728\u8bfb\u53d6\u6570\u636e';
    if(ts) ts.textContent = '\u8bfb\u53d6\u4e2d';
    var logbox = qs('logbox');
    if(logbox && !logbox.childElementCount){
      var line = document.createElement('div');
      line.className = 'ap';
      line.textContent = '[loading] ' + msg.detail;
      logbox.appendChild(line);
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
    stripDetailReparseUi();
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
  function tick(){ patchTitle(); patchViewerFunctions(); deleteStationOnlyUi(); syncViewerBaseLabels(); setViewerLoadingState(); }
  function scheduleTicks(){
    [0, 120, 360, 900, 1800].forEach(function(delay){
      setTimeout(tick, delay);
    });
  }
  scheduleTicks();
})();
"""


def build_station_viewer_page() -> str:
    parts = _load_station_template_parts()
    html_src = parts["_PAGE_HTML"]
    html_src = html_src.replace("__APP_VERSION_LABEL__", "viewer " + APP_VERSION)
    html_src = html_src.replace("<title>Light RID Scanner</title>", "<title>Light RID Node Center</title>")
    html_src = html_src.replace("Light RID Scanner", "Light RID Node Center")
    viewer_css = """
.viewer-base-label{margin:8px 0 6px;padding:8px 10px;border:1px solid var(--border);border-radius:var(--radius);background:color-mix(in srgb,var(--blue) 8%,var(--panel2));color:var(--txt);font:600 12px/1.35 var(--font-ui);white-space:normal;word-break:break-word}
body.theme-light .viewer-base-label{background:color-mix(in srgb,var(--blue) 7%,var(--panel2))}
.viewer-mode .detail-reparse-box{display:none !important}
.viewer-loading-state{color:var(--dim);font-weight:650}
.banner-stack{top:74px;width:auto;max-width:calc(100vw - 28px);align-items:center}
.banner{width:min(420px,calc(100vw - 32px));min-height:78px;border-radius:var(--radius-lg)}
"""
    html_src = _inject_html_once(html_src, "</style>", parts["_MAIN_PAGE_PATCH_CSS"] + "\n" + viewer_css + "\n")
    html_src = _inject_html_once(
        html_src,
        "</body>",
        "<script>\n"
        + parts["_MAIN_PAGE_PATCH_JS"]
        + "\n"
        + _viewer_patch_js()
        + "\n</script>\n"
        + f'<script src="{_rid_home_asset_url()}"></script>\n',
    )
    return html_src
