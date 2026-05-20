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
    shared_css = """
.rid-loading-overlay{position:fixed;inset:0;z-index:2600;display:none;align-items:flex-start;justify-content:center;pointer-events:none;padding-top:74px;background:transparent}
.rid-loading-overlay.show{display:flex}
.rid-loading-box{width:min(420px,calc(100vw - 28px));min-height:78px;display:grid;grid-template-columns:28px minmax(0,1fr);gap:6px 12px;align-items:start;padding:14px 16px;border:1px solid color-mix(in srgb,var(--blue) 32%,var(--border));border-left:4px solid var(--blue);border-radius:10px;background:color-mix(in srgb,var(--card) 94%,transparent);box-shadow:0 12px 30px rgba(0,0,0,.24);backdrop-filter:blur(12px);animation:toastIn .3s ease-out}
.rid-loading-spinner{grid-row:1/3;width:22px;height:22px;margin-top:2px;border-radius:50%;border:2px solid color-mix(in srgb,var(--blue) 18%,var(--border));border-top-color:var(--blue);animation:ridLoadingSpin .82s linear infinite}
.rid-loading-title{font:700 14px/1.2 var(--font-ui);color:var(--txt)}
.rid-loading-copy{font:600 12px/1.45 var(--font-ui);color:var(--muted);text-align:left;max-width:44ch}
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
body.theme-light .rid-loading-box{background:rgba(255,255,255,.94);box-shadow:0 18px 48px rgba(0,0,0,.14)}
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
    host.innerHTML = '<div class="rid-loading-box"><div class="rid-loading-spinner"></div><div class="rid-loading-title"></div><div class="rid-loading-copy"></div></div>';
    document.body.appendChild(host);
  }
  var titleEl = host.querySelector('.rid-loading-title');
  var copyEl = host.querySelector('.rid-loading-copy');
  function tick(){
    if(titleEl) titleEl.textContent = String(title || '正在读取数据');
    if(copyEl) copyEl.textContent = viewerPageLoadingText(target, timeoutSec);
  }
  tick();
  host.classList.add('show');
  if(viewerPageLoadingTimer) clearInterval(viewerPageLoadingTimer);
  viewerPageLoadingTimer = setInterval(tick, 1000);
}
function hideViewerPageLoading(){
  var host = document.getElementById('rid-loading-overlay');
  if(host) host.classList.remove('show');
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
</div>
<script>
window.LIGHT_RID_VIEWER_VERSION = {APP_VERSION!r};
{shared_script}
{script}
</script></body></html>"""
