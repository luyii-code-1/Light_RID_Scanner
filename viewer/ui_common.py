"""Shared HTML helpers for Station-styled viewer pages."""

from __future__ import annotations

import ast
from functools import lru_cache

from viewer.paths import APP_NAME, APP_VERSION, STATION_WEB_SERVER


@lru_cache(maxsize=1)
def station_settings_css() -> str:
    html = ""
    candidates = [
        STATION_WEB_SERVER.parent / "assets" / "templates" / "station-settings.html",
        STATION_WEB_SERVER.parent.parent / "station_edition" / "light_rid" / "assets" / "templates" / "station-settings.html",
    ]
    for template_path in candidates:
        if template_path.exists():
            html = template_path.read_text(encoding="utf-8")
            break
    if not html:
        if not STATION_WEB_SERVER.exists():
            raise FileNotFoundError(f"missing station web template: {STATION_WEB_SERVER}")
        tree = ast.parse(STATION_WEB_SERVER.read_text(encoding="utf-8"))
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


def station_page(
    title: str,
    body: str,
    script: str,
    extra_css: str = "",
    extra_scripts: tuple[str, ...] = (),
) -> str:
    css = station_settings_css()
    shared_css = """
.rid-loading-overlay{position:fixed;inset:0;z-index:2600;display:none;align-items:center;justify-content:center;padding:24px;background:rgba(9,15,24,.38);backdrop-filter:blur(12px);pointer-events:auto}
.rid-loading-overlay.show{display:flex}
.rid-loading-shell{width:min(460px,calc(100vw - 32px))}
.rid-loading-box{display:grid;gap:16px;padding:22px 22px 18px;border-radius:16px;border:1px solid color-mix(in srgb,var(--border) 96%,rgba(255,255,255,.42));background:linear-gradient(180deg,color-mix(in srgb,var(--panel2) 92%,rgba(255,255,255,.38)),color-mix(in srgb,var(--card) 96%,rgba(255,255,255,.18)));box-shadow:0 18px 40px rgba(19,42,71,.12);backdrop-filter:blur(14px)}
.rid-loading-head{display:grid;grid-template-columns:48px minmax(0,1fr);gap:14px;align-items:center}
.rid-loading-spinner{position:relative;width:48px;height:48px;border-radius:14px;border:1px solid color-mix(in srgb,var(--blue) 22%,var(--border));background:linear-gradient(180deg,rgba(255,255,255,.46),rgba(255,255,255,.16));display:grid;place-items:center}
.rid-loading-spinner::before{content:"";width:22px;height:22px;border-radius:50%;border:2px solid color-mix(in srgb,var(--blue) 14%,var(--border));border-top-color:var(--blue);animation:ridLoadingSpin .9s linear infinite}
.rid-loading-copy-wrap{display:grid;gap:6px}
.rid-loading-title{font:700 18px/1.14 var(--font-ui);color:var(--txt);letter-spacing:.01em}
.rid-loading-copy{font:600 13px/1.55 var(--font-ui);color:color-mix(in srgb,var(--txt) 82%,var(--muted));text-align:left}
.rid-loading-meta{display:grid;gap:8px;padding-top:12px;border-top:1px solid color-mix(in srgb,var(--border) 84%,transparent)}
.rid-loading-meta-line{display:grid;grid-template-columns:72px minmax(0,1fr);gap:10px;font:600 12px/1.5 var(--font-ui)}
.rid-loading-meta-label{color:var(--muted)}
.rid-loading-meta-value{color:var(--txt);text-align:left;word-break:break-word}
body.rid-loading-active{overflow:hidden}
@keyframes ridLoadingSpin{to{transform:rotate(360deg)}}
@keyframes toastIn{0%{opacity:0;transform:translateX(40px)}100%{opacity:1;transform:translateX(0)}}
.rid-toast-host{position:fixed;right:18px;bottom:84px;z-index:10000;display:flex;flex-direction:column;gap:8px;pointer-events:none;max-width:min(360px,calc(100vw - 28px))}
.rid-toast{display:grid;grid-template-columns:4px minmax(0,1fr);gap:10px;align-items:start;padding:12px 14px;border-radius:6px;background:color-mix(in srgb,var(--card) 94%,transparent);backdrop-filter:blur(14px);border:1px solid var(--border);box-shadow:0 8px 24px rgba(0,0,0,.18);animation:toastIn .3s ease-out;pointer-events:auto;cursor:pointer}
.rid-toast.out{animation:toastOut .26s ease-in forwards}
.rid-toast-bar{width:4px;height:100%;min-height:24px;border-radius:999px;background:var(--blue)}
.rid-toast.success .rid-toast-bar{background:var(--green)}
.rid-toast.error .rid-toast-bar{background:var(--warn)}
.rid-toast-msg{font:600 13px/1.4 var(--font-ui);color:var(--txt);white-space:pre-wrap;word-break:break-word}
@keyframes toastOut{0%{opacity:1;transform:translateX(0)}100%{opacity:0;transform:translateX(40px)}}
body.theme-light .rid-loading-overlay{background:rgba(236,242,250,.58)}
body.theme-light .rid-loading-box{background:linear-gradient(180deg,rgba(255,255,255,.94),rgba(245,249,255,.90));box-shadow:0 18px 36px rgba(35,53,79,.10)}
"""
    shared_script = """
window._ridToasts=[];
window.showToast=function(msg,kind,ms){
  kind=String(kind||'info');ms=Number(ms)||2800;
  var t={id:Date.now()+Math.random(),msg:String(msg||''),kind:kind};
  window._ridToasts.push(t);
  renderViewerToasts();
  setTimeout(function(){dismissViewerToast(t.id);},ms);
};
function dismissViewerToast(id){
  var el=document.getElementById('rid-toast-'+id);
  if(el){el.classList.add('out');setTimeout(function(){if(el.parentNode)el.parentNode.removeChild(el);},280);}
  window._ridToasts=window._ridToasts.filter(function(t){return t.id!==id;});
}
function renderViewerToasts(){
  var host=document.getElementById('rid-toast-host');
  if(!host){
    host=document.createElement('div');host.id='rid-toast-host';host.className='rid-toast-host';
    document.body.appendChild(host);
  }
  var html='';
  window._ridToasts.forEach(function(t){
    html+='<div class=\"rid-toast '+t.kind+'\" id=\"rid-toast-'+t.id+'\"><span class=\"rid-toast-bar\"></span><span class=\"rid-toast-msg\">'+String(t.msg).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')+'</span></div>';
  });
  host.innerHTML=html;
}
var viewerPageLoadingStartedAt = 0;
var viewerPageLoadingTimer = null;
function viewerPageLoadingState(target, timeoutSec){
  if(!viewerPageLoadingStartedAt) viewerPageLoadingStartedAt = Date.now();
  var elapsed = Math.floor((Date.now() - viewerPageLoadingStartedAt) / 1000);
  var limit = Math.max(5, Number(timeoutSec || 15) || 15);
  var remain = Math.max(0, limit - elapsed);
  var name = String(target || '\u9875\u9762\u6570\u636e');
  if(remain > 0){
    return {
      target: name,
      detail: '\u6b63\u5728\u8bfb\u53d6 ' + name,
      status: '\u5df2\u7b49\u5f85 ' + elapsed + 's\uff0c\u9884\u8ba1 ' + remain + 's \u540e\u63d0\u793a\u8d85\u65f6'
    };
  }
  return {
    target: name,
    detail: '\u8bfb\u53d6 ' + name + ' \u8d85\u65f6\uff0c\u4ecd\u5728\u7b49\u5f85\u8fd4\u56de',
    status: '\u5df2\u7b49\u5f85 ' + elapsed + 's\uff0c\u6682\u4e0d\u5173\u95ed\u9875\u9762'
  };
}
function viewerPageLoadingText(target, timeoutSec){
  if(!viewerPageLoadingStartedAt) viewerPageLoadingStartedAt = Date.now();
  var elapsed = Math.floor((Date.now() - viewerPageLoadingStartedAt) / 1000);
  var limit = Math.max(5, Number(timeoutSec || 15) || 15);
  var remain = Math.max(0, limit - elapsed);
  var name = String(target || '页面数据');
  if(remain > 0) return '正在读取 ' + name + '，' + remain + 's 后超时';
  return '读取 ' + name + '超时，仍在等待返回';
}
function showViewerPageLoading(target, title, timeoutSec){
  viewerPageLoadingStartedAt = Date.now();
  var host = document.getElementById('rid-loading-overlay');
  if(!host){
    host = document.createElement('div');
    host.id = 'rid-loading-overlay';
    host.className = 'rid-loading-overlay';
    host.innerHTML = '<div class="rid-loading-shell"><div class="rid-loading-box"><div class="rid-loading-head"><div class="rid-loading-spinner"></div><div class="rid-loading-copy-wrap"><div class="rid-loading-title"></div><div class="rid-loading-copy"></div></div></div><div class="rid-loading-meta"><div class="rid-loading-meta-line"><span class="rid-loading-meta-label">\u5f53\u524d\u76ee\u6807</span><span class="rid-loading-meta-value" data-role="target"></span></div><div class="rid-loading-meta-line"><span class="rid-loading-meta-label">\u8be6\u7ec6\u72b6\u6001</span><span class="rid-loading-meta-value" data-role="status"></span></div></div></div></div>';
    document.body.appendChild(host);
  }
  var titleEl = host.querySelector('.rid-loading-title');
  var copyEl = host.querySelector('.rid-loading-copy');
  var targetEl = host.querySelector('[data-role="target"]');
  var statusEl = host.querySelector('[data-role="status"]');
  function tick(){
    var state = viewerPageLoadingState(target, timeoutSec);
    if(titleEl) titleEl.textContent = String(title || '\u6b63\u5728\u8bfb\u53d6\u6570\u636e');
    if(copyEl) copyEl.textContent = state.detail;
    if(targetEl) targetEl.textContent = state.target;
    if(statusEl) statusEl.textContent = state.status;
  }
  tick();
  host.classList.add('show');
  document.body.classList.add('rid-loading-active');
  if(viewerPageLoadingTimer) clearInterval(viewerPageLoadingTimer);
  viewerPageLoadingTimer = setInterval(tick, 1000);
}
function hideViewerPageLoading(){
  var host = document.getElementById('rid-loading-overlay');
  if(host) host.classList.remove('show');
  document.body.classList.remove('rid-loading-active');
  if(viewerPageLoadingTimer){
    clearInterval(viewerPageLoadingTimer);
    viewerPageLoadingTimer = null;
  }
}
async function withViewerPageLoading(target, title, fn){
  showViewerPageLoading(target, title, 15);
  try{
    return await fn();
  }finally{
    hideViewerPageLoading();
  }
}
"""
    external_scripts = "".join(f'<script src="{src}"></script>\n' for src in extra_scripts)
    return f"""<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} - {APP_NAME}</title>
<style>
{css}
{shared_css}
{extra_css}
</style></head><body><div class="wrap">
{body}
</div>{external_scripts}
<script>
window.LIGHT_RID_VIEWER_VERSION = {APP_VERSION!r};
{shared_script}
{script}
</script></body></html>"""
