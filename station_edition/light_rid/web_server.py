import os
import sys
from pathlib import Path

_PAGE_HTML = """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Light RID Scanner</title>
<link rel="stylesheet" href="/assets/leaflet/leaflet.css"/>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
<link href="https://fonts.googleapis.com/css2?family=Rajdhani:wght@500;600;700&family=Share+Tech+Mono&display=swap" rel="stylesheet">
<script src="/assets/leaflet/leaflet.js"></script>
<style>
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
:root{
  --font-ui:Inter,Roboto,"Noto Sans SC","Microsoft YaHei UI","Segoe UI Variable Text","Segoe UI",sans-serif;
  --font-mono:"Roboto Mono","SFMono-Regular","Cascadia Mono","Consolas",monospace;
  --bg:#f3f5f8;--bg2:#e8edf3;--panel:rgba(255,255,255,.98);--panel2:#f7f9fc;--border:rgba(15,23,42,.09);--txt:#162033;
  --green:#1f9d68;--yellow:#d99315;--dim:#617083;--blue:#2f6fed;
  --purple:#6d63ff;--cyan:#3182ce;--glow:rgba(47,111,237,.12);--soft:rgba(255,255,255,.86);
  --warn:#d95050;--muted:#7c889a;--surface-tonal:#eef4fb;
  --selected-surface:rgba(47,111,237,.10);--selected-surface-card:rgba(47,111,237,.08);
  --selected-border:rgba(47,111,237,.28);--selected-muted:#43566f;
  --radius-sm:8px;--radius:10px;--radius-lg:16px;--radius-xl:18px;
  --shadow-sm:0 1px 2px rgba(15,23,42,.04);--shadow:0 8px 18px rgba(15,23,42,.06);--shadow-lg:0 14px 30px rgba(15,23,42,.10);
  --transition:0.32s cubic-bezier(.22,1,.36,1)
}
body{background:var(--bg);color:var(--txt);font-family:var(--font-ui);font-size:16px;
     height:100dvh;display:grid;grid-template-rows:auto minmax(0,1fr) minmax(240px,38vh) auto;
     row-gap:12px;overflow:hidden;position:relative;
     transition:background-color .24s ease,color .24s ease;
     background:
        radial-gradient(circle at top left, rgba(255,255,255,.98), rgba(255,255,255,0) 36%),
        radial-gradient(circle at top right, rgba(96,165,250,.18), rgba(96,165,250,0) 30%),
        linear-gradient(180deg,var(--bg),var(--bg2) 34%,var(--bg))}
body.theme-light{
  --bg:#f3f5f8;--bg2:#e8edf3;--panel:#ffffff;--panel2:#f7f9fc;--border:rgba(15,23,42,.09);--txt:#162033;
  --green:#1f9d68;--yellow:#d99315;--dim:#617083;--blue:#2f6fed;
  --purple:#6d63ff;--cyan:#3182ce;--glow:rgba(47,111,237,.12);--soft:rgba(255,255,255,.86);
  --warn:#d95050;--muted:#7c889a;
  --selected-surface:rgba(47,111,237,.10);--selected-surface-card:rgba(47,111,237,.08);
  --selected-border:rgba(47,111,237,.28);--selected-muted:#43566f;
  --shadow-sm:0 1px 2px rgba(15,23,42,.04);--shadow:0 8px 18px rgba(15,23,42,.06);--shadow-lg:0 14px 30px rgba(15,23,42,.10)
}
body.theme-dark{
  --bg:#0f1724;--bg2:#142033;--panel:rgba(18,27,42,.96);--panel2:#172336;--border:rgba(148,163,184,.18);--txt:#e7eef9;
  --green:#39b980;--yellow:#e2a24a;--dim:#9aacbf;--blue:#6ea8ff;
  --purple:#8a86ff;--cyan:#58b6ff;--glow:rgba(110,168,255,.18);--soft:rgba(11,18,28,.88);
  --warn:#ff8d8d;--muted:#95a6bc;--surface-tonal:#17283d;
  --selected-surface:rgba(110,168,255,.16);--selected-surface-card:rgba(110,168,255,.12);
  --selected-border:rgba(110,168,255,.34);--selected-muted:#d4e3f6;
  --shadow-sm:0 1px 2px rgba(0,0,0,.26);--shadow:0 12px 24px rgba(0,0,0,.28);--shadow-lg:0 18px 40px rgba(0,0,0,.34)
}
body::before{
  content:""; position:fixed; inset:0; pointer-events:none; z-index:0;
  background:
    radial-gradient(circle at 12% 12%, rgba(255,255,255,.82), rgba(255,255,255,0) 28%),
    radial-gradient(circle at 82% 0%, rgba(104,174,255,.18), rgba(104,174,255,0) 24%);
}
body.theme-dark::before{
  background:
    radial-gradient(circle at 12% 12%, rgba(110,168,255,.12), rgba(110,168,255,0) 28%),
    radial-gradient(circle at 82% 0%, rgba(63,131,248,.12), rgba(63,131,248,0) 24%);
}
body.theme-light::before{
  background:
    radial-gradient(circle at 10% 8%, rgba(255,255,255,.94), rgba(255,255,255,0) 30%),
    radial-gradient(circle at 88% 0%, rgba(95,172,255,.16), rgba(95,172,255,0) 24%);
}
header,.tbl-wrap,.panel,footer{position:relative;z-index:1}
.mono, code, .logbox, .aplist, .adv-input, .stat b{font-family:var(--font-mono)}

/* -- Header -- */
header{background:var(--panel);border:1px solid color-mix(in srgb,var(--border) 96%,transparent);
       margin:10px 12px 0;padding:12px 16px;display:grid;grid-template-columns:auto auto minmax(0,1fr);
       align-items:center;gap:8px 16px;position:sticky;top:10px;z-index:10;border-radius:16px;
       box-shadow:0 8px 18px rgba(15,23,42,.05)}
header .head-stats{display:flex;align-items:center;justify-content:flex-end;
       gap:8px 16px;flex-wrap:wrap;min-width:0;grid-column:3}
header h1{font-size:20px;font-weight:700;color:var(--txt);letter-spacing:.01em;text-transform:none}
.app-version-label{font-family:var(--font-mono);font-size:11px;font-weight:600;line-height:1;color:var(--muted);white-space:nowrap;padding:4px 8px;border-radius:8px;background:var(--panel2);border:1px solid color-mix(in srgb,var(--border) 90%,transparent)}
.adv-modal{
  position:fixed;inset:0;z-index:10006;background:rgba(3,8,14,.62);
  display:none;align-items:center;justify-content:center;padding:12px;
}
.adv-modal.show{display:flex}
.adv-window{
  width:min(1120px, calc(100vw - 24px));max-height:calc(100vh - 24px);overflow:auto;
  border:1px solid var(--border);border-radius:4px;background:var(--panel);
  box-shadow:0 18px 36px rgba(0,0,0,.20);
}
.adv-window-hd{
  display:flex;align-items:center;justify-content:space-between;gap:8px;
  padding:10px 12px;border-bottom:1px solid var(--border);color:var(--txt);font-size:14px;font-weight:600;
}
.adv-window-hd .btn-mini{padding:4px 8px}
.adv-body{
  padding:10px;
  display:grid;
  grid-template-columns:repeat(2,minmax(0,1fr));
  gap:10px;
}
.adv-col{display:grid;gap:8px;min-width:0;align-content:start}
.adv-row{display:flex;gap:8px;align-items:center;flex-wrap:wrap;min-width:0}
.adv-row label{font-size:13px;color:var(--dim)}
.adv-row.focus-pulse{
  border:1px solid color-mix(in srgb, var(--blue) 48%, var(--border));
  border-radius:4px;
  padding:6px;
  box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 24%, transparent);
  animation:hwPulse .9s ease-out 2;
}
@keyframes hwPulse{
  0%{box-shadow:0 0 0 0 rgba(88,166,255,.30)}
  100%{box-shadow:0 0 0 10px rgba(88,166,255,0)}
}
@keyframes alarmRowPulse{from{box-shadow:inset 3px 0 0 rgba(255,79,79,.55)}to{box-shadow:inset 3px 0 0 rgba(255,79,79,1)}}
.adv-input{min-width:260px;flex:1 1 420px;background:var(--panel2);color:var(--txt);border:1px solid var(--border);border-radius:4px;padding:7px 9px;font:inherit}
.adv-note{font-size:13px;color:var(--dim);word-break:break-all}
.adv-note code{color:var(--txt)}
.adv-actions{display:flex;gap:8px;flex-wrap:wrap}
.cfg-editor{
  width:100%;min-height:220px;resize:vertical;
  background:var(--panel2);color:var(--txt);border:1px solid var(--border);border-radius:4px;
  padding:8px 10px;font:13px/1.5 var(--font-mono);
}
.stat{font-size:15px;color:var(--dim);white-space:nowrap}
.stat b{color:var(--green)}
.stat.ls b{color:var(--dim)}
.stat.cs b{color:var(--purple)}
.stat.ts b{color:var(--cyan);font-weight:400}
.stat.snf b.ok{color:var(--green)}
.stat.snf b.warn{color:var(--yellow)}
.stat.snf b.err{color:#ff7b72}
.sniff-banner{
  display:none;
  grid-column:1/-1;
  margin-top:6px;
  padding:8px 12px;
  border:1px solid color-mix(in srgb, var(--warn) 44%, var(--border));
  border-radius:4px;
  background:color-mix(in srgb, var(--warn) 10%, var(--panel));
  color:#ffd7cc;
  font-size:13px;
  line-height:1.35;
  z-index:12;
}
.sniff-banner.warn{
  border-color:color-mix(in srgb, var(--yellow) 38%, var(--border));
  background:color-mix(in srgb, var(--yellow) 11%, var(--panel));
  color:#f5e2a8;
}
.security-banner{
  align-items:center;
  justify-content:space-between;
  gap:10px;
}
.security-banner .btn-mini{flex:0 0 auto}
.banner-stack{
  position:fixed;top:74px;left:50%;transform:translateX(-50%);
  display:flex;flex-direction:column;align-items:center;gap:10px;z-index:9998;
  width:auto;max-width:calc(100vw - 28px);pointer-events:none;
}
.banner{
  opacity:0;transform:translateY(-12px) scale(.97);position:relative;overflow:hidden;
  transition:opacity .28s ease-out,transform .28s cubic-bezier(.22,.61,.36,1);
  width:min(420px,calc(100vw - 32px));min-height:78px;pointer-events:auto;cursor:pointer;
  border:1px solid var(--border);border-radius:14px;
  background:var(--panel);color:var(--txt);
  padding:14px 16px 14px 18px;font:650 13px/1.45 var(--font-ui);
  box-shadow:0 12px 24px rgba(15,23,42,.10);
}
.banner:before{content:"";position:absolute;left:0;top:0;bottom:0;width:4px;background:var(--blue)}
.banner.show{opacity:1;transform:translateY(0) scale(1)}
.banner.ok{border-color:color-mix(in srgb, var(--green) 40%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel));color:color-mix(in srgb, var(--green) 72%, white)}
.banner.warn{border-color:color-mix(in srgb, var(--yellow) 34%, var(--border));background:color-mix(in srgb, var(--yellow) 10%, var(--panel));color:#ffd9a9}
.banner.ok:before{background:var(--green)}
.banner.warn:before{background:var(--yellow)}
.rid-loading-overlay{position:fixed;inset:0;z-index:2600;display:none;align-items:center;justify-content:center;padding:24px;background:rgba(9,15,24,.32);pointer-events:auto}
.rid-loading-overlay.show{display:flex}
.rid-loading-shell{width:min(460px,calc(100vw - 32px))}
.rid-loading-box{display:grid;gap:16px;padding:22px 22px 18px;border-radius:16px;border:1px solid color-mix(in srgb,var(--border) 96%,rgba(255,255,255,.42));background:linear-gradient(180deg,color-mix(in srgb,var(--panel2) 96%,rgba(255,255,255,.38)),color-mix(in srgb,var(--panel) 98%,rgba(255,255,255,.18)));box-shadow:0 12px 28px rgba(19,42,71,.10)}
.rid-loading-head{display:grid;grid-template-columns:48px minmax(0,1fr);gap:14px;align-items:center}
.rid-loading-spinner{position:relative;width:48px;height:48px;border-radius:14px;border:1px solid color-mix(in srgb,var(--blue) 22%,var(--border));background:linear-gradient(180deg,rgba(255,255,255,.46),rgba(255,255,255,.16));display:grid;place-items:center}
.rid-loading-spinner::before{content:"";width:22px;height:22px;border-radius:50%;border:2px solid color-mix(in srgb,var(--blue) 14%,var(--border));border-top-color:var(--blue);animation:ridLoadingSpin .9s linear infinite}
.rid-loading-copy-wrap{display:grid;gap:6px}
.rid-loading-title{font:700 18px/1.14 var(--font-ui);color:var(--txt);letter-spacing:.01em}
.rid-loading-copy{font:600 13px/1.55 var(--font-ui);color:color-mix(in srgb,var(--txt) 82%,var(--muted));text-align:left}
.rid-loading-meta{display:grid;gap:8px;padding-top:12px;border-top:1px solid color-mix(in srgb,var(--border) 84%,transparent)}
.rid-loading-meta-line{display:grid;grid-template-columns:72px minmax(0,1fr);gap:10px;font:600 12px/1.5 var(--font-ui)}
.rid-loading-meta-label{color:var(--dim)}
.rid-loading-meta-value{color:var(--txt);text-align:left;word-break:break-word}
body.rid-loading-active{overflow:hidden}
@keyframes ridLoadingSpin{to{transform:rotate(360deg)}}
.notify-center-button{
  position:fixed;right:18px;bottom:18px;z-index:9999;width:52px;height:52px;border-radius:14px;
  border:1px solid color-mix(in srgb, var(--blue) 40%, var(--border));
  background:color-mix(in srgb, var(--panel) 92%, transparent);color:var(--txt);
  box-shadow:0 10px 22px rgba(15,23,42,.12);
  display:flex;align-items:center;justify-content:center;cursor:pointer;
  transition:background-color 160ms ease,border-color 160ms ease,color 160ms ease,box-shadow 160ms ease,transform 160ms ease;
}
.notify-center-button:hover,.notify-center-button.active{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--panel));box-shadow:0 12px 24px rgba(37,99,235,.12)}
.notify-center-glyph{position:relative;width:20px;height:20px;border:2px solid currentColor;border-radius:50%;display:block}
.notify-center-glyph::before{content:"";position:absolute;left:50%;top:4px;width:2px;height:8px;background:currentColor;transform:translateX(-50%);border-radius:1px}
.notify-center-glyph::after{content:"";position:absolute;left:50%;bottom:3px;width:5px;height:5px;border-radius:50%;background:currentColor;transform:translateX(-50%)}
.notify-center-count{
  position:absolute;right:-4px;top:-4px;min-width:20px;height:20px;padding:0 5px;border-radius:999px;
  display:none;align-items:center;justify-content:center;background:#d83b01;color:#fff;
  border:2px solid var(--panel);font:700 11px/1 var(--font-ui);
  animation:notifyBadgePop .3s ease-out
}
@keyframes notifyBadgePop{0%{transform:scale(0)}60%{transform:scale(1.15)}100%{transform:scale(1)}}
.notify-center-button.has-items .notify-center-count{display:flex}
.notify-center-panel{
  position:fixed;right:18px;bottom:84px;z-index:9999;width:min(380px,calc(100vw - 28px));
  max-height:min(560px,calc(100vh - 110px));display:none;flex-direction:column;overflow:hidden;
  border:1px solid var(--border);border-radius:16px;background:var(--panel);
  box-shadow:0 14px 28px rgba(15,23,42,.12);
  transform:translateX(calc(100% + 20px));opacity:0;
  transition:transform .28s cubic-bezier(.22,.61,.36,1),opacity .22s ease-out;
}
.notify-center-panel.show{display:flex;transform:translateX(0);opacity:1}
.notify-center-head{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:14px 16px;border-bottom:1px solid var(--border);background:color-mix(in srgb, var(--panel2) 84%, transparent)}
.notify-center-title{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.notify-center-sub{margin-top:4px;color:var(--dim);font-size:12px}
.notify-center-list{padding:8px;display:grid;gap:8px;overflow:auto}
.notify-center-empty{padding:28px 12px;text-align:center;color:var(--dim);font-size:13px}
.notify-item{display:grid;grid-template-columns:4px minmax(0,1fr) auto;gap:10px;align-items:start;padding:10px 12px;border:1px solid color-mix(in srgb, var(--border) 86%, transparent);border-radius:var(--radius);background:color-mix(in srgb, var(--panel2) 82%, transparent);animation:notifyItemIn .35s ease-out}
@keyframes notifyItemIn{0%{opacity:0;transform:translateX(12px)}100%{opacity:1;transform:translateX(0)}}
.notify-item-bar{width:4px;height:100%;min-height:42px;border-radius:999px;background:var(--blue)}
.notify-item.ok .notify-item-bar{background:var(--green)}
.notify-item.warn .notify-item-bar{background:var(--yellow)}
.notify-item-text{color:var(--txt);font-size:13px;line-height:1.4;white-space:pre-wrap;word-break:break-word}
.notify-item-time{margin-top:6px;color:var(--dim);font-size:11px}
.notify-item-del{width:26px;height:26px;border:1px solid var(--border);border-radius:var(--radius);background:var(--panel);color:var(--dim);cursor:pointer;line-height:1;transition:all var(--transition)}
.notify-item-del:hover{border-color:var(--warn);color:var(--warn);background:color-mix(in srgb, var(--warn) 10%, var(--panel));transform:scale(1.05)}
#dot-ws{width:9px;height:9px;border-radius:50%;background:var(--dim);
        display:inline-block;margin-right:4px;transition:background .3s}
#dot-ws.on{background:var(--green)}

/* -- Table -- */
.tbl-wrap{margin:0 12px;min-height:0;overflow:auto;
          border:1px solid color-mix(in srgb,var(--border) 92%,transparent);border-radius:18px;background:var(--panel);
          box-shadow:0 4px 14px rgba(15,23,42,.06)}
table{width:100%;border-collapse:collapse;table-layout:fixed;min-width:980px}
thead tr{background:var(--panel2);position:sticky;top:0;z-index:9}
thead th{padding:10px 12px;text-align:left;font-size:12px;font-weight:600;color:var(--dim);
          border-bottom:1px solid var(--border);white-space:nowrap}
thead th.sortable{cursor:pointer;user-select:none;position:relative;padding-right:24px;transition:color var(--transition),background-color var(--transition)}
thead th.sortable:hover{color:var(--txt);background:color-mix(in srgb,var(--blue) 5%,transparent)}
thead th.sortable::after{
  content:"";position:absolute;right:10px;top:50%;width:8px;height:12px;transform:translateY(-50%);
  opacity:.42;background-repeat:no-repeat;background-position:center;background-size:8px 12px;
  background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="8" height="12" viewBox="0 0 8 12"><path d="M4 1 6.8 4H1.2L4 1Z" fill="%237d91aa"/><path d="M4 11 1.2 8h5.6L4 11Z" fill="%237d91aa"/></svg>');
}
thead th.sortable.sorted-asc,thead th.sortable.sorted-desc{color:var(--txt)}
thead th.sortable.sorted-asc::after{
  opacity:.95;background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="8" height="12" viewBox="0 0 8 12"><path d="M4 1 6.8 4H1.2L4 1Z" fill="%231677ff"/><path d="M4 11 1.2 8h5.6L4 11Z" fill="%2397a8bc"/></svg>');
}
thead th.sortable.sorted-desc::after{
  opacity:.95;background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="8" height="12" viewBox="0 0 8 12"><path d="M4 1 6.8 4H1.2L4 1Z" fill="%2397a8bc"/><path d="M4 11 1.2 8h5.6L4 11Z" fill="%231677ff"/></svg>');
}
tbody tr{border-bottom:1px solid color-mix(in srgb, var(--border) 58%, transparent);transition:background-color 120ms ease,border-color 120ms ease}
tbody tr:hover{background:#f4f8ff}
tbody tr.lost{opacity:.4}
tbody tr.selected{background:var(--selected-surface);box-shadow:inset 3px 0 0 var(--blue)}
tbody tr.selected td,
tbody tr.selected .mono{color:var(--txt)}
tbody tr.selected .idx-cell,
tbody tr.selected .uas-line{color:var(--selected-muted)}
tbody tr.selected .icon-btn{
  background:color-mix(in srgb, var(--selected-surface) 60%, var(--panel2));
  border-color:color-mix(in srgb, var(--selected-border) 75%, var(--border));
  color:var(--selected-muted);
}
tbody tr.selected .icon-btn:hover{color:var(--txt)}
tbody tr.alarm-zone{background:color-mix(in srgb, #ff3b30 12%, var(--panel));animation:alarmRowPulse .9s ease-in-out infinite alternate}
td{padding:9px 12px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:13px;line-height:1.25}
.empty{text-align:center;padding:40px;color:var(--dim);font-size:15px}
th:nth-child(1),td:nth-child(1){width:46px}
th:nth-child(2),td:nth-child(2){width:46px}
th:nth-child(3),td:nth-child(3){width:330px}
th:nth-child(4),td:nth-child(4){width:132px}
th:nth-child(5),td:nth-child(5){width:96px}
th:nth-child(6),td:nth-child(6){width:62px}
th:nth-child(7),td:nth-child(7){width:68px}
th:nth-child(8),td:nth-child(8){width:92px}
th:nth-child(9),td:nth-child(9){width:176px}
th:nth-child(10),td:nth-child(10){width:112px}
.sel-wrap{display:flex;align-items:center;justify-content:center}
.sel-sn{width:16px;height:16px;accent-color:var(--blue);cursor:pointer}
.idx-cell{color:var(--dim);text-align:center}

/* -- Bottom Panels: Map + Logs -- */
.bottom{display:grid;grid-template-columns:minmax(0,1.15fr) minmax(0,1fr) minmax(0,.95fr);gap:12px;
        margin:0 12px;min-height:0}
.bottom.map-collapsed{grid-template-columns:max-content minmax(0,1fr) minmax(0,1.35fr)}
.bottom.log-collapsed{grid-template-columns:minmax(0,1.15fr) max-content minmax(0,1.35fr)}
.bottom.ap-collapsed{grid-template-columns:minmax(0,1.2fr) minmax(0,1fr) max-content}
.bottom.map-collapsed.log-collapsed{grid-template-columns:max-content max-content minmax(0,1fr)}
.bottom.map-collapsed.ap-collapsed{grid-template-columns:max-content minmax(0,1fr) max-content}
.bottom.log-collapsed.ap-collapsed{grid-template-columns:minmax(0,1fr) max-content max-content}
.bottom.all-collapsed{display:none}
body.bottom-all-collapsed{
  grid-template-rows:auto minmax(0,1fr) 0 auto;
  row-gap:8px;
}
@media(max-width:960px){
  header{
    grid-template-columns:auto auto;
    padding:8px 10px;
    gap:8px 10px;
  }
  header h1{font-size:18px}
  header .head-stats{
    grid-column:1/-1;
    justify-content:flex-start;
    gap:6px 10px;
  }
  .stat{font-size:13px}
  .head-stats .btn-mini{padding:6px 8px}
  .head-stats .stat:last-child{margin-left:auto}
  .tbl-wrap,.bottom{margin:0 8px}
  .adv-body{grid-template-columns:1fr}
}
@media(max-width:1180px){
  .bottom{grid-template-columns:minmax(0,1fr) minmax(0,1fr)}
  .bottom.map-collapsed,.bottom.log-collapsed,.bottom.ap-collapsed,.bottom.map-collapsed.log-collapsed,.bottom.map-collapsed.ap-collapsed,.bottom.log-collapsed.ap-collapsed{
    grid-template-columns:minmax(0,1fr) minmax(0,1fr)
  }
  .bottom .panel.ap-panel{grid-column:1/-1;min-height:220px}
}
@media(max-width:800px){
  body{
    grid-template-rows:auto minmax(0,1fr) minmax(0,1fr) auto;
    row-gap:8px;
  }
  .tbl-wrap{margin:0 8px}
  table{min-width:680px}
  thead th{padding:7px 8px;font-size:13px}
  td{padding:6px 8px;font-size:13px}
  th:nth-child(3),td:nth-child(3){width:260px}
  th:nth-child(7),td:nth-child(7),
  th:nth-child(9),td:nth-child(9),
  th:nth-child(10),td:nth-child(10){display:none}
  .bottom{
    grid-template-columns:1fr;
    grid-template-rows:none;
    grid-auto-rows:minmax(170px,auto);
    gap:8px;
    margin:0 8px;
  }
  .bottom.map-collapsed,.bottom.log-collapsed,.bottom.ap-collapsed,.bottom.map-collapsed.log-collapsed,.bottom.map-collapsed.ap-collapsed,.bottom.log-collapsed.ap-collapsed{
    grid-template-columns:1fr
  }
  .bottom .panel.ap-panel{grid-column:auto;min-height:180px}
  .panel-hdr{padding:7px 10px;font-size:13px}
  .panel-hdr span.sub{font-size:12px}
  .btn-mini{min-height:30px;padding:6px 8px;font-size:12px}
  .icon-btn{width:22px;height:22px}
  .sn-badge{font-size:10px;padding:1px 5px}
  .adv-row{flex-direction:column;align-items:stretch}
  .adv-window{width:calc(100vw - 12px);max-height:calc(100vh - 12px)}
  .map-mini-list{
    width:min(92vw,340px);
    right:8px;
    top:54px;
    max-height:55vh;
  }
  .aprow{
    grid-template-columns:30px minmax(96px, 13ch) 54px 72px minmax(0,1fr);
    gap:6px;
    padding:5px 4px;
  }
  .aprow > :nth-child(6){display:none}
  .adv-input{min-width:0;flex-basis:100%}
}
@media(max-width:600px){
  header h1{font-size:16px}
  .app-version-label{font-size:11px}
  .stat{font-size:12px}
  table{min-width:500px}
  th:nth-child(4),td:nth-child(4){display:none}
  th:nth-child(6),td:nth-child(6){display:none}
  th:nth-child(3),td:nth-child(3){width:200px}
  th:nth-child(8),td:nth-child(8){width:96px}
  .info-row{grid-template-columns:86px 1fr}
  .info-modal{padding:70px 10px 10px}
  .info-card{width:calc(100vw - 14px);max-height:74vh;border-radius:16px}
  .info-card-body{padding:10px 12px;font-size:13px}
  .cfg-editor{min-height:170px}
}
@media(max-width:480px){
  header{padding:7px 8px;gap:6px 8px}
  header h1{font-size:15px}
  header .head-stats{gap:5px 8px}
  .head-stats .btn-mini{padding:5px 7px;font-size:11px}
  .tbl-wrap,.bottom{margin:0 6px}
  table{min-width:440px}
  th:nth-child(2),td:nth-child(2){display:none}
  th:nth-child(3),td:nth-child(3){width:186px}
  th:nth-child(5),td:nth-child(5){width:72px}
  th:nth-child(8),td:nth-child(8){width:88px}
  thead th{padding:6px 7px;font-size:12px}
  td{padding:5px 7px;font-size:12px}
  .bottom{gap:6px}
  .panel-hdr{padding:6px 9px;font-size:12px}
  .panel-hdr span.sub{font-size:11px}
  .map-mini-list{width:min(94vw,320px);right:6px;top:46px;max-height:52vh}
  .info-row{grid-template-columns:78px 1fr;gap:6px}
  .info-card-hd{padding:8px 10px}
}

.panel{border:1px solid color-mix(in srgb,var(--border) 92%,transparent);border-radius:16px;overflow:hidden;
       display:flex;flex-direction:column;min-height:0;
       box-shadow:var(--shadow-sm);background:var(--panel)}
.panel-hdr{background:var(--panel2);padding:10px 16px;font-size:14px;
           color:var(--txt);font-weight:600;border-bottom:1px solid var(--border);
           display:flex;justify-content:space-between;align-items:center}
.panel-hdr span.sub{color:var(--dim);font-size:13px;font-weight:400}
.panel-hdr .hdr-actions{display:flex;align-items:center;gap:8px}
.panel.collapsible.collapsed{align-self:start;min-height:0}
.panel.collapsible.collapsed .panel-hdr{padding:8px 10px;gap:8px}
.panel.collapsible.collapsed .panel-hdr .sub{display:none}
.panel.collapsible.collapsed .panel-hdr label{display:none}
.panel.collapsible.collapsed .panel-hdr .hdr-actions{gap:6px}
.panel.log-panel.collapsed .logbox{display:none}
.panel.log-panel.collapsed .panel-hdr{border-bottom:none}
.panel.map-panel.collapsed #map{display:none}
.panel.map-panel.collapsed .panel-hdr{border-bottom:none}
.panel.ap-panel.collapsed .aplist{display:none}
.panel.ap-panel.collapsed .panel-hdr{border-bottom:none}

/* -- Leaflet Map -- */
#map{flex:1;width:100%;min-height:0}
.offline-map-tile{
  display:flex;align-items:flex-start;justify-content:flex-start;
  width:256px;height:256px;padding:8px;
  background:
    linear-gradient(to right, color-mix(in srgb,var(--border) 58%,transparent) 1px, transparent 1px),
    linear-gradient(to bottom, color-mix(in srgb,var(--border) 58%,transparent) 1px, transparent 1px),
    color-mix(in srgb,var(--panel) 92%, black);
  background-size:64px 64px;
  color:var(--dim);font:700 11px/1 var(--font-ui);
}
.offline-map-badge{
  padding:4px 6px;border:1px solid var(--border);border-radius:4px;
  background:color-mix(in srgb,var(--panel) 88%,transparent);
}
.rid-drone-icon{background:transparent;border:0}
.drone-pin{position:relative;width:74px;height:58px;pointer-events:none;opacity:var(--drone-op,1)}
.drone-symbol{
  position:absolute;left:2px;top:7px;width:46px;height:46px;transform:rotate(var(--drone-rot,0deg));
  transform-origin:50% 50%;filter:drop-shadow(0 2px 4px rgba(0,0,0,.32));
}
.drone-pin.selected .drone-symbol{filter:drop-shadow(0 0 8px rgba(255,255,255,.62)) drop-shadow(0 2px 4px rgba(0,0,0,.32))}
.drone-index{
  position:absolute;left:46px;top:5px;min-width:24px;height:22px;padding:0 5px;border-radius:999px;
  display:flex;align-items:center;justify-content:center;
  border:1px solid rgba(255,255,255,.92);background:rgba(20,24,28,.86);color:#fff;
  font:800 11px/1 var(--font-mono);box-shadow:0 2px 5px rgba(0,0,0,.24);
}
.drone-pin.alarm .drone-symbol,.drone-pin.alarm .drone-index{animation:droneAlarmBlink .72s ease-in-out infinite alternate}
@keyframes droneAlarmBlink{from{opacity:.38;filter:drop-shadow(0 0 0 rgba(255,59,48,0)) drop-shadow(0 2px 4px rgba(0,0,0,.32))}to{opacity:1;filter:drop-shadow(0 0 10px rgba(255,59,48,.88)) drop-shadow(0 2px 4px rgba(0,0,0,.32))}}
.replay-sync-banner{
  display:none;position:absolute;left:50%;top:60px;z-index:1210;transform:translateX(-50%);
  align-items:center;gap:8px;padding:8px 12px;border:1px solid rgba(255,185,0,.52);border-radius:5px;
  background:color-mix(in srgb, var(--panel) 90%, transparent);color:#ffe4a3;
  box-shadow:0 8px 20px rgba(0,0,0,.22);backdrop-filter:blur(8px);font:700 13px/1 var(--font-ui);
}
#map-panel.replay-sync-paused .replay-sync-banner{display:flex}
.replay-sync-dot{width:8px;height:8px;border-radius:50%;background:#ffb900;box-shadow:0 0 0 0 rgba(255,185,0,.42);animation:replaySyncPulse 1s ease-out infinite}
@keyframes replaySyncPulse{to{box-shadow:0 0 0 9px rgba(255,185,0,0)}}
.panel.map-panel.fullscreen{
  position:fixed;inset:0;z-index:9997;border-radius:0;margin:0;background:var(--bg);
}
.panel.map-panel.fullscreen .panel-hdr{
  position:absolute;left:12px;right:12px;top:10px;z-index:1200;border-radius:8px;
}
.panel.map-panel.fullscreen #map{
  position:absolute;inset:0;height:100%;width:100%;
}
.map-mini-list{
  display:none;
  position:absolute;right:16px;top:68px;z-index:1201;
  width:min(320px,45vw);max-height:48vh;overflow:auto;
  border:1px solid color-mix(in srgb,var(--border) 88%,transparent);border-radius:18px;
  background:color-mix(in srgb, var(--panel) 97%, white);backdrop-filter:blur(10px);
  padding:10px;
  box-shadow:var(--shadow);
}
.map-mini-list .mini-title{font-size:12px;color:var(--dim);margin-bottom:6px}
.map-mini-list .mini-item{
  display:flex;align-items:center;gap:8px;padding:4px 2px;font-size:13px;white-space:nowrap;
}
.map-mini-list .mini-item .sn{overflow:hidden;text-overflow:ellipsis}
.map-mini-list .mini-item .mini-model{margin-left:auto;max-width:42%;overflow:hidden;text-overflow:ellipsis;color:var(--dim)}
.panel.map-panel.fullscreen .map-mini-list{display:block}

/* -- Log Box -- */
.logbox{flex:1;overflow-y:auto;padding:7px 12px;
        font-size:14px;line-height:1.65;
        background:var(--bg);min-height:0}
.logbox .ap{color:var(--txt)}
.logbox .rid{color:var(--green);font-weight:700}
.panel-hdr label{display:flex;align-items:center;gap:6px;cursor:pointer;
                 color:var(--dim);font-weight:400;font-size:13px}
.btn-mini{
  border:1px solid color-mix(in srgb,var(--border) 92%,transparent);background:var(--panel2);color:var(--txt);
  padding:7px 12px;border-radius:9px;font:600 13px/1 var(--font-ui);cursor:pointer;
  letter-spacing:0;display:inline-flex;align-items:center;gap:5px;user-select:none;
  transition:background-color 160ms ease,border-color 160ms ease,color 160ms ease,box-shadow 160ms ease,transform 160ms ease;
  box-shadow:var(--shadow-sm);
}
.btn-mini:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));border-color:var(--blue);box-shadow:0 4px 10px rgba(37,99,235,.10);transform:translateY(-1px)}
.btn-mini:active{transform:scale(.97)}
.btn-mini:disabled{opacity:.5;cursor:not-allowed;transform:none;box-shadow:none}
.btn-mini.primary{background:var(--blue);border-color:var(--blue);color:#fff;font-weight:700}
.btn-mini.primary:hover{background:color-mix(in srgb, var(--blue) 90%, #0f172a);box-shadow:0 4px 14px var(--glow);transform:translateY(-1px)}
.btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:var(--warn)}
.btn-mini.warn:hover{background:var(--warn);color:#fff;border-color:var(--warn);box-shadow:0 4px 14px rgba(255,123,114,.18)}
.btn-mini.ghost{background:transparent;border-color:transparent;color:var(--dim);box-shadow:none}
.btn-mini.ghost:hover{background:var(--panel2);color:var(--txt);border-color:var(--border);box-shadow:var(--shadow-sm)}
#bottom-restore{
  position:fixed;right:12px;bottom:12px;z-index:9996;display:none;
  box-shadow:0 8px 24px rgba(0,0,0,.26);
}
body.bottom-all-collapsed #bottom-restore{display:inline-flex}
.sn-cell{display:flex;align-items:center;gap:6px;min-width:0}
.sn-text-stack{display:flex;flex-direction:column;gap:2px;min-width:0}
.sn-cell .mono{min-width:0;overflow:hidden;text-overflow:ellipsis}
.uas-line{font:700 11px/1.2 var(--font-mono);color:var(--dim);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.uas-line.empty{opacity:.6}
.sn-badge{
  display:inline-block;padding:2px 6px;border-radius:9px;font-size:11px;font-weight:700;
  border:1px solid color-mix(in srgb, var(--yellow) 48%, var(--border));background:color-mix(in srgb, var(--yellow) 20%, var(--panel2));color:#d8a31a;line-height:1.25;flex:0 0 auto;
}
.sn-badge.firmware-new{border-color:rgba(46,204,113,.62);background:rgba(46,204,113,.20);color:#42d587}
.sn-badge.firmware-old{border-color:color-mix(in srgb, var(--blue) 44%, var(--border));background:color-mix(in srgb, var(--blue) 16%, var(--panel2));color:#62b2ff}
.sn-badge.alarm{border-color:rgba(255,79,79,.8);background:rgba(255,79,79,.22);color:#ff9187}
.icon-btn{
  border:1px solid var(--border);background:var(--panel2);color:var(--dim);
  width:28px;height:28px;display:inline-flex;align-items:center;justify-content:center;
  border-radius:var(--radius);cursor:pointer;font-size:13px;line-height:1;flex:0 0 auto;
  transition:background-color 160ms ease,border-color 160ms ease,color 160ms ease,box-shadow 160ms ease,transform 160ms ease;
  box-shadow:var(--shadow-sm);
}
.icon-btn:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));color:var(--txt);border-color:var(--blue);transform:translateY(-1px);box-shadow:0 2px 6px rgba(37,99,235,.08)}
.icon-btn:active{transform:scale(.94)}
.icon-btn.done{border-color:color-mix(in srgb, var(--green) 42%, var(--border));color:color-mix(in srgb, var(--green) 72%, white)}
tbody tr.data-row{cursor:pointer}
tbody td.hl{
  background-color:rgba(255,216,96,calc(var(--hl-alpha,.0) * .58));
}
.info-modal{
  position:fixed;inset:0;display:none;align-items:flex-start;justify-content:flex-end;
  background:transparent;backdrop-filter:none;z-index:9999;padding:78px 18px 18px;
  pointer-events:none;
}
.info-modal.show{display:flex}
.info-card{
  width:min(360px, calc(100vw - 24px));
  max-height:min(68vh, 560px);
  border:1px solid color-mix(in srgb, var(--border) 92%, transparent);border-radius:16px;overflow:hidden;
  background:var(--panel);
  box-shadow:0 12px 28px rgba(15,23,42,.10);
  display:flex;flex-direction:column;
  pointer-events:auto;
  animation:icloudFloatIn .32s cubic-bezier(.22,1,.36,1);
}
@keyframes icloudFloatIn{0%{opacity:0;transform:translateY(16px) scale(.985)}100%{opacity:1;transform:translateY(0) scale(1)}}
.info-card-hd{
  display:flex;align-items:center;justify-content:space-between;gap:8px;
  padding:12px 14px;border-bottom:1px solid color-mix(in srgb, var(--border) 80%, transparent);color:var(--txt);font-weight:700;
  cursor:move;user-select:none;touch-action:none;
}
.info-card.dragging{user-select:none}
.info-card-close{
  border:1px solid var(--border);background:var(--panel2);color:var(--dim);
  width:30px;height:30px;border-radius:999px;cursor:pointer;line-height:1;
}
.info-card-close:hover{background:color-mix(in srgb, var(--blue) 10%, var(--panel2));color:var(--txt);border-color:var(--blue)}
.info-card-body{
  padding:12px 14px 14px;overflow:auto;
  white-space:normal;line-height:1.6;color:var(--txt);font-size:14px;
}
.info-grid{display:grid;grid-template-columns:1fr;gap:4px}
.info-row{display:grid;grid-template-columns:110px 1fr;gap:8px;align-items:start}
.info-row .k{color:var(--dim)}
.info-row .v{word-break:break-all}
.raw-title{margin:10px 0 6px 0;font-weight:600;color:var(--txt)}
.raw-meta{font-size:12px;color:var(--dim);margin:6px 0 4px 0}
.raw-code{
  margin:0 0 8px 0;padding:8px 10px;border-radius:4px;
  border:1px solid var(--border);background:var(--panel2);color:var(--txt);
  font:12px/1.45 var(--font-mono);white-space:pre-wrap;word-break:break-all;
}
.raw-empty{color:var(--dim);font-size:13px}
.info-card-body .mono{font-family:var(--font-mono)}
.aplist{flex:1;min-height:0;max-height:min(34vh,360px);overflow:auto;background:var(--panel);font-size:13px;line-height:1.45;padding:6px 8px}
.aplist .ap-empty{color:var(--dim);padding:14px 8px}
.aprow{display:grid;grid-template-columns:42px minmax(116px, 15ch) 62px 86px minmax(0,1.15fr) minmax(0,1fr);gap:8px;padding:6px 6px;border-bottom:1px solid color-mix(in srgb, var(--border) 70%, transparent);align-items:start}
.aprow:hover{background:color-mix(in srgb, var(--blue) 6%, var(--panel))}
.aprow.hd{position:sticky;top:0;background:var(--panel2);color:var(--dim);font-weight:600;z-index:1}
.aprow .idx{text-align:right;color:var(--dim)}
.aprow .mono{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.aprow .ap-mac{font-feature-settings:"tnum" 1}
.aplist.wide .aprow{grid-template-columns:42px minmax(170px, 20ch) 64px 92px minmax(0,1.15fr) minmax(0,1fr)}
.aplist.narrow .aprow{grid-template-columns:30px minmax(96px, 12ch) 54px minmax(0,1fr)}
.aplist.narrow .aprow > :nth-child(4),
.aplist.narrow .aprow > :nth-child(6){display:none}
.aprow .ssid{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all}
.aprow .vendor{white-space:normal;overflow:visible;text-overflow:clip;word-break:break-all;color:var(--txt)}
.aprow .ssid-col,.aprow .vendor-col{min-width:0}
.subline{font-size:11px;color:var(--dim)}

body.theme-light header{
  background:var(--panel);
  box-shadow:0 1px 3px rgba(0,0,0,.06);
}
body.theme-light .adv-window{
  background:var(--panel);
  border-color:var(--border);
  box-shadow:0 16px 30px rgba(15,23,42,.12);
}
body.theme-light .adv-window-hd{
  color:var(--txt);border-bottom-color:var(--border);
}
body.theme-light .tbl-wrap{
  background:var(--panel);
  box-shadow:0 1px 3px rgba(15,23,42,.06);
}
body.theme-light thead tr{background:var(--panel2)}
body.theme-light thead th{color:var(--dim)}
body.theme-light tbody tr{border-bottom-color:#e6e3e1}
body.theme-light tbody tr:hover{background:color-mix(in srgb, var(--blue) 6%, var(--panel))}
body.theme-light .panel{
  box-shadow:0 1px 3px rgba(15,23,42,.06);
}
body.theme-light .panel-hdr{
  background:var(--panel2);
}
body.theme-light .panel-hdr,
body.theme-light .panel-hdr span.sub,
body.theme-light .panel-hdr label,
body.theme-light .adv-row label,
body.theme-light .adv-note,
body.theme-light .stat,
body.theme-light footer,
body.theme-light .subline{color:#5b6470}
body.theme-light .logbox,
body.theme-light .aplist{background:var(--panel)}
body.theme-light .aprow{border-bottom-color:#ece8e6}
body.theme-light .aprow:hover{background:color-mix(in srgb, var(--blue) 5%, var(--panel))}
body.theme-light .aprow.hd{background:var(--panel2);color:var(--dim)}
body.theme-light .aprow .vendor{color:var(--txt)}
body.theme-light .adv-input{
  background:var(--panel2);color:var(--txt);border-color:var(--border);
}
body.theme-light .adv-row.focus-pulse{
  border-color:color-mix(in srgb, var(--blue) 45%, var(--border));
  box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 18%, transparent);
}
body.theme-light .adv-note code{color:var(--txt)}
body.theme-light .cfg-editor{
  background:var(--panel2);color:var(--txt);border-color:var(--border);
}
body.theme-light .btn-mini{
  border-color:var(--border);
  background:var(--panel2);
  color:var(--txt);
}
body.theme-light .btn-mini:hover{
  background:color-mix(in srgb, var(--blue) 8%, var(--panel2));
  border-color:var(--blue);
  box-shadow:0 2px 8px var(--glow);
}
body.theme-light .btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 40%, var(--border));color:var(--warn)}
body.theme-light .btn-mini.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--panel2))}
body.theme-light .icon-btn{
  border-color:var(--border);background:var(--panel2);color:var(--dim);
}
body.theme-light .icon-btn:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));color:var(--txt)}
body.theme-light .icon-btn.done{border-color:color-mix(in srgb, var(--green) 38%, var(--border));color:#0f7a3b}
body.theme-light .sn-badge{border-color:color-mix(in srgb, var(--yellow) 44%, var(--border));background:color-mix(in srgb, var(--yellow) 18%, var(--panel2));color:#8a5a00}
body.theme-light .sn-badge.firmware-new{border-color:rgba(21,128,61,.46);background:rgba(21,128,61,.15);color:#166534}
body.theme-light .sn-badge.firmware-old{border-color:color-mix(in srgb, var(--blue) 36%, var(--border));background:color-mix(in srgb, var(--blue) 14%, var(--panel2));color:#184f90}
body.theme-light .sn-badge.alarm{border-color:rgba(209,52,56,.64);background:rgba(209,52,56,.16);color:#97222a}
body.theme-light tbody td.hl{
  background-color:rgba(250,213,97,calc(var(--hl-alpha,.0) * .52));
}
body.theme-light tbody tr.selected{background:var(--selected-surface)}
body.theme-light .map-mini-list{
  border-color:var(--border);background:rgba(255,255,255,.96);
}
body.theme-light .map-mini-list .mini-title{color:var(--dim)}
body.theme-light .info-modal{background:transparent}
body.theme-light .info-card{
  border-color:var(--border);
  background:color-mix(in srgb, #ffffff 92%, rgba(255,255,255,.74));
  box-shadow:0 20px 48px rgba(15,23,42,.12);
}
body.theme-light .info-card-hd{
  color:var(--txt);border-bottom-color:var(--border);
}
body.theme-light .info-card-close{
  border-color:var(--border);background:var(--panel2);color:var(--dim);
}
body.theme-light .info-card-close:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));color:var(--txt)}
body.theme-light .info-card-body{color:var(--txt)}
body.theme-light .info-row .k{color:var(--dim)}
body.theme-light .raw-title{color:var(--txt)}
body.theme-light .raw-meta{color:var(--dim)}
body.theme-light .raw-code{
  border-color:var(--border);background:var(--panel2);color:var(--txt);
}
body.theme-light .raw-empty{color:var(--dim)}
body.theme-light .sniff-banner{
  border-color:color-mix(in srgb, var(--warn) 40%, var(--border));
  background:color-mix(in srgb, var(--warn) 10%, var(--panel));
  color:#9f2a2a;
}
body.theme-light .sniff-banner.warn{
  border-color:color-mix(in srgb, var(--yellow) 35%, var(--border));
  background:color-mix(in srgb, var(--yellow) 12%, var(--panel));
  color:#8a6800;
}
body.theme-light .banner{border-color:var(--border);background:rgba(255,255,255,.96);color:var(--txt);box-shadow:0 16px 38px rgba(0,0,0,.12)}
body.theme-light .banner.ok{border-color:color-mix(in srgb, var(--green) 38%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel));color:#14532d}
body.theme-light .banner.warn{border-color:color-mix(in srgb, var(--yellow) 34%, var(--border));background:color-mix(in srgb, var(--yellow) 12%, var(--panel));color:#7c2d12}
body.theme-light .rid-loading-overlay{background:rgba(236,242,250,.58)}
body.theme-light .rid-loading-box{background:linear-gradient(180deg,rgba(255,255,255,.94),rgba(245,249,255,.90));box-shadow:0 18px 36px rgba(35,53,79,.10)}
 
footer{text-align:center;padding:8px 10px;font-size:12px;color:#5b6470}
</style>
</head><body>
<header>
  <h1>✈ Light RID Scanner</h1><code class="app-version-label">__APP_VERSION_LABEL__</code>
  <div class="head-stats">
  <span class="stat">全部/在线 <b id="n-total">-</b>/<b id="n-live">-</b></span>
  <span class="stat ts">更新 <b id="cur-ts">-</b></span>
  <span class="stat"><span id="dot-ws"></span><span id="ws-status">连接中</span></span>
  <button class="btn-mini" id="btn-clear-history" type="button">清空历史</button>
  </div>
</header>

<div class="tbl-wrap">
<table id="dtable">
<thead><tr>
  <th><div class="sel-wrap"><input id="sel-all" class="sel-sn" type="checkbox" title="全选"></div></th><th class="sortable" data-sort="index">#</th><th class="sortable" data-sort="sn">SN</th><th class="sortable" data-sort="model">机型</th><th class="sortable" data-sort="rssi">信号</th><th class="sortable" data-sort="pkts">包</th><th class="sortable" data-sort="dir">方向</th><th class="sortable" data-sort="age">数据更新</th><th class="sortable" data-sort="last_seen">末次发现</th><th class="sortable" data-sort="uas_id">UAS ID</th>
</tr></thead>
<tbody id="tbody"></tbody>
</table>
</div>

<div class="bottom">
  <div class="panel">
    <div class="panel-hdr">
      🗺 地图
      <span class="sub" id="map-hint">等待坐标...</span>
    </div>
    <div id="map"></div>
  </div>
  <div class="panel">
    <div class="panel-hdr">
      📡 AP 扫描日志
      <label><input type="checkbox" id="autoscroll" checked>自动滚动</label>
    </div>
    <div class="logbox" id="logbox"></div>
  </div>
</div>

<footer>Light RID Scanner</footer>

<script>
// -- WebSocket ------------------------------------------------
var ws, reconnTimer;
var lastLogsSeq = -1;
var lastApsSeq = -1;
var clearHistoryBusy = false;
var deleteHistorySnBusy = {};
var restartBusy = false;
var metaState = {};
var uiFrozen = false;
var frozenPendingData = null;
var homeFreezeAfterFirstRender = false;
var uiTheme = 'dark';
var activeInfoSn = '';
var infoCardEscBound = false;
var infoCardDragState = {x:null, y:null, pointerId:null, startX:0, startY:0, cardX:0, cardY:0};
var webNotifyEnabled = false;
var droneStatePrev = {};
var droneFieldPrev = {};
var droneFieldHl = {};
var latestDroneMap = {};
var latestDroneRows = [];
var latestMapRows = [];
var latestApsRows = [];
var latestApsTotal = 0;
var selectedSnSet = {};
var selectedMacSet = {};
var historyHiddenSnSet = {};
var historySelectionTouched = false;
var historyTrackFilterTs = null;
var zoneAlarmSnSet = {};
var rowClickTimer = null;
var trackCache = {};
var trackLoading = {};
var trackFetchMeta = {};
var trackRenderQueue = {};
var trackRenderScheduled = false;
var COOKIE_TRACK_REALTIME = 'rid_realtime_track';
var COOKIE_TRACK_2H_ONLY = 'rid_track_2h_only';
var FREEZE_ON_HOME_KEY = 'rid_freeze_on_home_once';
var NEW_FIRMWARE_PARSE_KEY = 'rid_new_firmware_parse_enabled';
var LIVE_LOST_WINDOW_SEC = 120;
var HISTORY_DEFAULT_WINDOW_SEC = 12 * 3600;
var TRACK_HISTORY_FETCH_LIMIT = 4000;
var TRACK_FORCE_RELOAD_MS = 8000;
var notificationItems = [];
var notificationSeq = 0;
var notificationSyncBusy = false;
var notificationPollTimer = null;
var authRedirecting = false;
var replaySyncPaused = false;
var suppressNextDroneNotifications = false;
var replayState = {sn:null,snList:[],points:[],min:null,max:null,start:null,end:null,cursor:null,startIndex:0,endIndex:null,cursorIndex:null,playing:false,speed:1,timer:null,userRange:false};
var replayMarkers = {};
var replayUiSig = '';
var HL_FADE_IN_MS = 0;
var HL_HOLD_MS = 0;
var HL_FADE_OUT_MS = 2000;
var HL_TOTAL_MS = HL_FADE_IN_MS + HL_HOLD_MS + HL_FADE_OUT_MS;
var highlightAnimRunning = false;
var ifaceOptionsLoaded = false;
var sniffBannerPrevState = '';
var mapCollapsedBeforeFullscreen = null;
var mapFsUiTimer = null;
var miniListRenderSig = '';
var TABLE_SORT_STORAGE_KEY = 'rid_table_sort_v1';
var tableSortState = {field:'', dir:'desc'};
var mapLastUserInputTs = 0;
var mapHeadingRefDeg = 0;
var mapAutoCenterIdleSec = 20;

function qs(id){ return document.getElementById(id); }
function fmt(v,dec,unit){ return v==null?'N/A':Number(v).toFixed(dec)+unit; }
function numOrNull(v){
  if(v==null) return null;
  var s = String(v).trim();
  if(!s) return null;
  var n = Number(s);
  return isFinite(n) ? n : null;
}
function intOrDefault(v, defv){
  if(v==null || v==='') return defv;
  var n = parseInt(v, 10);
  return isFinite(n) ? n : defv;
}
function normDeg(v){
  var d = Number(v);
  if(!isFinite(d)) return 0;
  d = d % 360;
  if(d < 0) d += 360;
  return d;
}
function headingDeltaDeg(nowDeg, refDeg){
  var a = normDeg(nowDeg);
  var b = normDeg(refDeg);
  var d = a - b;
  if(d > 180) d -= 360;
  if(d < -180) d += 360;
  return d;
}
function mapAutoState(){
  var cd = Number(mapAutoCenterIdleSec);
  if(!isFinite(cd) || cd < 5) cd = 20;
  if(!mapLastUserInputTs) return {allow:true, remain:0};
  var now = Date.now() / 1000;
  var elapsed = now - Number(mapLastUserInputTs);
  if(elapsed >= cd) return {allow:true, remain:0};
  return {allow:false, remain:Math.max(0, cd - elapsed)};
}
function markMapUserInteracted(){
  mapLastUserInputTs = Date.now() / 1000;
  if(map) map._rid_user_moved = true;
}
function cookieGet(name){
  var key = String(name || '').trim();
  if(!key) return null;
  var parts = String(document.cookie || '').split(';');
  for(var i=0;i<parts.length;i++){
    var p = String(parts[i] || '').trim();
    if(!p) continue;
    var pos = p.indexOf('=');
    var k = (pos < 0) ? p : p.slice(0, pos).trim();
    if(k !== key) continue;
    var raw = (pos < 0) ? '' : p.slice(pos + 1);
    try{ return decodeURIComponent(raw); }catch(_e){ return raw; }
  }
  return null;
}
function cookieSet(name, value, days){
  var key = String(name || '').trim();
  if(!key) return;
  var val = encodeURIComponent(String(value == null ? '' : value));
  var nDays = Number(days);
  if(!isFinite(nDays) || nDays <= 0) nDays = 365;
  var secure = (location.protocol === 'https:') ? '; Secure' : '';
  document.cookie = key + '=' + val + '; Max-Age=' + Math.round(nDays * 86400) + '; Path=/; SameSite=Lax' + secure;
}
function cookieDelete(name){
  var key = String(name || '').trim();
  if(!key) return;
  var secure = (location.protocol === 'https:') ? '; Secure' : '';
  document.cookie = key + '=; Max-Age=0; Path=/; SameSite=Lax' + secure;
}
function cookieBool(name, defVal){
  var v = cookieGet(name);
  if(v == null || v === '') return !!defVal;
  v = String(v).toLowerCase();
  return (v === '1' || v === 'true' || v === 'on' || v === 'yes');
}
function loadTrackPrefs(){
  saveTrackPrefs();
}
function saveTrackPrefs(){
  cookieDelete(COOKIE_TRACK_REALTIME);
  cookieDelete(COOKIE_TRACK_2H_ONLY);
}
function syncTrackPrefsUi(){
}
function consumeFreezeOnHomeRequest(){
  try{
    homeFreezeAfterFirstRender = (localStorage.getItem(FREEZE_ON_HOME_KEY) === '1');
  }catch(_e){
    homeFreezeAfterFirstRender = false;
  }
}
function historyVisibleSnList(rows){
  var out = [];
  (Array.isArray(rows) ? rows : []).forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn || historyHiddenSnSet[sn]) return;
    out.push(sn);
  });
  return out;
}
function displayTrackSnList(page, rows){
  return page === 'history' ? historyVisibleSnList(rows) : [];
}
function isHistoryTrackVisible(sn){
  sn = String(sn || '');
  return !!sn && !historyHiddenSnSet[sn];
}
function isSnCheckedForCurrentPage(sn){
  return currentAppPage() === 'history' ? isHistoryTrackVisible(sn) : isSnSelected(sn);
}
function historyTrackLastAgeSec(e){
  var age = Number((e && e.age) || 0);
  if(!isFinite(age) || age < 0) return null;
  return age;
}
function pruneHistoryHiddenSnSet(rows){
  var keep = {};
  (Array.isArray(rows) ? rows : []).forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(sn) keep[sn] = true;
  });
  Object.keys(historyHiddenSnSet).forEach(function(sn){
    if(!keep[sn]) delete historyHiddenSnSet[sn];
  });
}
function applyHistoryDefaultSelection(rows){
  pruneHistoryHiddenSnSet(rows);
  if(historySelectionTouched) return;
  var nextHidden = {};
  (Array.isArray(rows) ? rows : []).forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return;
    var age = historyTrackLastAgeSec(e);
    if(age == null || age > HISTORY_DEFAULT_WINDOW_SEC){
      nextHidden[sn] = true;
    }
  });
  historyHiddenSnSet = nextHidden;
}
function _trackTsSec(p){
  var ts = Number((p && p.ts) || 0);
  return (isFinite(ts) && ts > 0) ? ts : null;
}
function activeHistoryTrackFilterTs(){
  return null;
}
function filterTrackByHistoryTime(track){
  var arr = Array.isArray(track) ? track.slice() : [];
  return arr;
}
function filterTrackForDisplay(track, page, sn){
  if(page !== 'history') return [];
  var arr = Array.isArray(track) ? track.slice() : [];
  arr = filterTrackByHistoryTime(arr);
  return arr;
}
function trackLatLngSignature(latlngs){
  if(!Array.isArray(latlngs) || !latlngs.length) return '0';
  var first = latlngs[0] || {};
  var last = latlngs[latlngs.length - 1] || {};
  function key(p){
    var lat = Array.isArray(p) ? p[0] : p.lat;
    var lng = Array.isArray(p) ? p[1] : p.lng;
    return Number(lat || 0).toFixed(6) + ',' + Number(lng || 0).toFixed(6);
  }
  return String(latlngs.length) + '|' + key(first) + '|' + key(last);
}
function baseFromMeta(meta){
  meta = (meta && typeof meta === 'object') ? meta : {};
  var lat = numOrNull(meta.base_lat);
  var lon = numOrNull(meta.base_lon);
  var zoom = intOrDefault(meta.base_zoom, 13);
  zoom = Math.max(3, Math.min(30, zoom));
  var name = String(meta.base_name || '基站').trim() || '基站';
  if(lat==null || lon==null) return {ok:false, name:name, lat:null, lon:null, zoom:zoom};
  if(Math.abs(lat) < 0.000001 && Math.abs(lon) < 0.000001) return {ok:false, name:name, lat:null, lon:null, zoom:zoom};
  if(lat < -90 || lat > 90 || lon < -180 || lon > 180) return {ok:false, name:name, lat:null, lon:null, zoom:zoom};
  return {ok:true, name:name, lat:lat, lon:lon, zoom:zoom};
}
function baseSignature(meta){
  var b = baseFromMeta(meta);
  if(!b.ok) return 'none';
  return [b.name, b.lat.toFixed(7), b.lon.toFixed(7), String(b.zoom)].join('|');
}
function shortMac(mac){
  mac = String(mac||'');
  if(mac.length <= 11) return mac;
  return mac.slice(0,8)+'...'+mac.slice(-5);
}
function infoRowHtml(label, value){
  return '<div class="info-row"><span class="k">'+esc(label)+'</span><span class="v">'+esc(value==null?'':value)+'</span></div>';
}
function snSourceText(e){
  var idType = String((e && e.id_type) || '').toUpperCase();
  return (idType === 'SSID') ? 'SSID' : 'RID包';
}
function scanTypeText(e){
  var k = String((e && e.scan_type_key) || '').toLowerCase();
  if(k === 'phone') return '手机快传';
  return 'RID报送';
}
function newFirmwareParseEnabled(){
  try{ return localStorage.getItem(NEW_FIRMWARE_PARSE_KEY) !== '0'; }catch(_e){ return true; }
}
function firmwareTypeKey(e){
  var k = String((e && e.firmware_type_key) || '').toLowerCase();
  if(k === 'new') return 'new';
  if(String((e && e.firmware_type) || '').indexOf('新') >= 0) return 'new';
  return 'old';
}
function firmwareTypeText(e){
  return firmwareTypeKey(e) === 'new' ? '新版固件' : '旧版固件';
}
function uasIdText(e){
  var s = String((e && e.uas_id) || '').trim();
  return s ? s : '-';
}
function ridFormatText(e){
  var s = String((e && (e.rid_format || e.dji_rid_kind || e.kind)) || '').trim();
  return s ? s : '-';
}
function parseNoteText(e){
  var s = String((e && e.parse_note) || '').trim();
  return s ? s : '';
}
function includeDroneByFirmware(e){
  if(newFirmwareParseEnabled()) return true;
  return String((e && e.scan_type_key) || '').toLowerCase() === 'phone';
}
function buildInfoHtml(e){
  e = e || {};
  var detailSn = String(e.sn || '');
  var html = '<div class="info-actions">'+
    '<button class="btn-mini export-track-btn" type="button" data-sn="'+escAttr(detailSn)+'">导出轨迹</button>'+
    '<button class="btn-mini warn delete-history-btn" type="button" data-sn="'+escAttr(detailSn)+'">删除历史</button>'+
    '</div><div class="info-grid">';
  html += infoRowHtml('SN', String(e.sn || '-'));
  html += infoRowHtml('UAS ID', uasIdText(e));
  html += infoRowHtml('机型', String(e.model || 'N/A'));
  html += infoRowHtml('在线状态', e.lost ? '离线' : '在线');
  html += infoRowHtml('归档', e.archived ? '是' : '否');
  html += infoRowHtml('MAC', String(e.mac || '-'));
  html += infoRowHtml('SSID', String(e.ssid || '(hidden)'));
  html += infoRowHtml('RID格式', ridFormatText(e));
  if(parseNoteText(e)) html += infoRowHtml('解析状态', parseNoteText(e));
  html += infoRowHtml('来源', snSourceText(e));
  html += infoRowHtml('扫描类型', scanTypeText(e));
  html += infoRowHtml('固件', firmwareTypeText(e));
  html += infoRowHtml('扫描类型Key', String(e.scan_type_key || '-'));
  html += infoRowHtml('捕获类型', String(e.capture_type || '-'));
  html += infoRowHtml('捕获时间', String(e.capture_time || '-'));
  html += infoRowHtml('最后数据包', String(e.last_pkt_time || e.capture_time || '-'));
  html += infoRowHtml('ID类型', String(e.id_type || '-'));
  html += infoRowHtml('信号', e.rssi==null ? 'N/A' : (e.rssi + 'dBm'));
  html += infoRowHtml('包数', String(e.pkts==null?0:e.pkts));
  html += infoRowHtml('纬度', fmt(e.lat,6,''));
  html += infoRowHtml('经度', fmt(e.lon,6,''));
  html += infoRowHtml('遥控站纬度', fmt(e.pilot_lat,6,''));
  html += infoRowHtml('遥控站经度', fmt(e.pilot_lon,6,''));
  var homeAuxRows = appendHomeAuxRows([], e);
  homeAuxRows.forEach(function(row){
    html += infoRowHtml(row[0], row[1]);
  });
  html += infoRowHtml('飞手位置类型', String(e.pilot_loc_type_text || e.pilot_loc_type || '-'));
  html += infoRowHtml('高度', fmt(e.alt,1,'m'));
  html += infoRowHtml('相对高度', fmt(e.alt_relative,1,'m'));
  html += infoRowHtml('大地高度', fmt(e.alt_geoid,1,'m'));
  html += infoRowHtml('气压高度', fmt(e.alt_baro,1,'m'));
  html += infoRowHtml('速度', fmt(e.spd,2,'m/s'));
  html += infoRowHtml('垂直速度', fmt(e.vspd,2,'m/s'));
  html += infoRowHtml('报送速度', fmt(e.track_deg,1,'°') + ' / ' + fmt(e.ground_speed,2,'m/s') + ' / ' + fmt(e.vertical_speed,2,'m/s'));
  html += infoRowHtml('水平/垂直/速度精度', String(e.horizontal_accuracy ?? '-') + ' / ' + String(e.vertical_accuracy ?? '-') + ' / ' + String(e.speed_accuracy ?? '-'));
  html += infoRowHtml('坐标系', String(e.coord_sys_text || e.coord_sys || '-'));
  html += infoRowHtml('运行类别/分类', String(e.operation_category_text || e.operation_category || '-') + ' / ' + String(e.aircraft_category_text || e.aircraft_category || '-'));
  html += infoRowHtml('运行状态', String(e.operation_state_text || e.operation_state || '-'));
  html += infoRowHtml('方向', String(e.dir || '-'));
  html += infoRowHtml('首次上线', String(e.first_seen || '-'));
  html += infoRowHtml('最后上线', String(e.last_seen || '-'));
  html += infoRowHtml('在线时长', fmtDurSec(e.online_dur));
  html += infoRowHtml('数据更新时间', String(e.age_text || fmtAge(e.age)));
  html += infoRowHtml('轨迹点数', String(e.track_count==null?0:e.track_count));
  html += '</div>';
  var raws = Array.isArray(e.raw_packets) ? e.raw_packets : [];
  html += '<div class="raw-title">原始包</div>';
  if(raws.length){
    raws.forEach(function(p, idx){
      p = p || {};
      html += '<div class="raw-meta">#'+(idx+1)+' ['+esc(String(p.capture_type || e.capture_type || '-'))+'] '+esc(String(p.ts || e.capture_time || '-'))+'</div>';
      html += '<pre class="raw-code">'+esc(String(p.hex || ''))+'</pre>';
    });
  } else {
    html += '<div class="raw-empty">暂无</div>';
  }
  return html;
}
function fmtDurSec(sec){
  if(sec==null || !isFinite(sec)) return '-';
  sec = Math.max(0, Math.round(Number(sec)||0));
  var d = Math.floor(sec / 86400); sec %= 86400;
  var h = Math.floor(sec / 3600); sec %= 3600;
  var m = Math.floor(sec / 60); sec %= 60;
  if(d) return d+'d'+h+'h';
  if(h) return h+'h'+m+'m';
  if(m) return m+'m'+sec+'s';
  return sec+'s';
}
function fmtAge(sec){
  if(sec==null || !isFinite(sec)) return '-';
  sec = Math.max(0, Math.round(Number(sec)||0));
  if(sec < 60) return sec + 's';
  if(sec < 3600) return Math.floor(sec / 60) + 'm';
  if(sec <= 216000) return Math.floor(sec / 3600) + 'h';
  return Math.floor(sec / 86400) + 'd';
}
function isSnSelected(sn){
  sn = String(sn || '');
  return !!selectedSnSet[sn];
}
function selectedSnList(){
  return Object.keys(selectedSnSet).filter(function(sn){ return !!selectedSnSet[sn]; });
}
function clearLiveSelections(keepSn){
  var keep = String(keepSn || '');
  Object.keys(selectedSnSet).forEach(function(sn){
    if(sn !== keep) delete selectedSnSet[sn];
  });
  Object.keys(selectedMacSet).forEach(function(mac){
    var matched = false;
    if(keep){
      var e = latestDroneMap[keep] || null;
      var keepMac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
      matched = !!keepMac && keepMac === mac;
    }
    if(!matched) delete selectedMacSet[mac];
  });
}
function trackFetchUrl(sn){
  var url = '/api/tracks/get?sn=' + encodeURIComponent(sn);
  url += '&limit=' + encodeURIComponent(String(TRACK_HISTORY_FETCH_LIMIT));
  return url;
}
async function ensureTrackLoaded(sn, force){
  sn = String(sn || '');
  if(!sn) return;
  if(trackLoading[sn]) return;
  var nowMs = Date.now();
  var meta = trackFetchMeta[sn] || {};
  var scope = 'history|' + TRACK_HISTORY_FETCH_LIMIT;
  if(trackCache[sn] && !force && meta.scope === scope) return;
  trackLoading[sn] = true;
  try{
    var data = await getJson(trackFetchUrl(sn));
    var tr = Array.isArray(data.track) ? data.track : [];
    trackCache[sn] = tr;
    trackFetchMeta[sn] = {
      ts: Date.now(),
      scope: scope,
      total: Number(data.count_total || data.count || tr.length || 0),
      shown: Number(tr.length || 0)
    };
    if(currentAppPage() === 'history' && isHistoryTrackVisible(sn)){
      if(replaySyncPaused) renderReplayFrame();
      else updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    }
  }catch(_e){
    if(!trackCache[sn]) trackCache[sn] = [];
  }finally{
    delete trackLoading[sn];
  }
}
function syncSelectedFromRows(rows){
  var arr = Array.isArray(rows) ? rows : [];
  var nextMac = {};
  for(var i=0;i<arr.length;i++){
    var e = arr[i] || {};
    var sn = String(e.sn || '');
    var mac = String(e.mac || e.src_mac || '').toLowerCase();
    if(!sn) continue;
    if(selectedSnSet[sn]){
      if(mac) nextMac[mac] = true;
      continue;
    }
    if(mac && selectedMacSet[mac]){
      selectedSnSet[sn] = true;
      nextMac[mac] = true;
    }
  }
  selectedMacSet = nextMac;
}
function setSnSelected(sn, on, opts){
  opts = (opts && typeof opts === 'object') ? opts : {};
  sn = String(sn || '');
  if(!sn) return;
  var e = latestDroneMap[sn] || null;
  var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
  if(on){
    if(opts.exclusive) clearLiveSelections(sn);
    selectedSnSet[sn] = true;
    if(mac) selectedMacSet[mac] = true;
  }else{
    delete selectedSnSet[sn];
    if(mac) delete selectedMacSet[mac];
  }
  syncTableSelectionUi();
  renderLiveCards(latestDroneRows);
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function setHistoryVisibleSet(snList, opts){
  opts = (opts && typeof opts === 'object') ? opts : {};
  historySelectionTouched = true;
  var visibleSet = {};
  (Array.isArray(snList) ? snList : []).forEach(function(sn){
    sn = String(sn || '');
    if(sn) visibleSet[sn] = true;
  });
  var nextHidden = {};
  (Array.isArray(latestDroneRows) ? latestDroneRows : []).forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return;
    if(visibleSet[sn]){
      ensureTrackLoaded(sn, false);
    }else{
      nextHidden[sn] = true;
    }
  });
  historyHiddenSnSet = nextHidden;
  if(!opts.keepReplay && (replayState.sn || (replayState.points || []).length)) clearReplaySelection({render:false});
  syncTableSelectionUi();
  if(replaySyncPaused){
    renderReplayFrame();
    return;
  }
  renderDroneTable(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  renderMapMiniList(latestDroneRows);
  refreshReplayBounds(false);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function setHistorySnVisible(sn, on, opts){
  sn = String(sn || '');
  if(!sn) return;
  var current = historyVisibleSnList(latestDroneRows);
  var next = {};
  current.forEach(function(id){ if(id) next[id] = true; });
  if(on) next[sn] = true;
  else delete next[sn];
  setHistoryVisibleSet(Object.keys(next), opts);
}
function setHistoryExclusiveVisible(sn, opts){
  sn = String(sn || '');
  setHistoryVisibleSet(sn ? [sn] : [], opts);
}
function setAllVisibleSelected(on){
  if(currentAppPage() === 'history'){
    var hRows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
    var next = on ? hRows.map(function(e){ return String((e && e.sn) || ''); }).filter(function(sn){ return !!sn; }) : [];
    setHistoryVisibleSet(next, {});
    return;
  }
  var rows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
  rows.forEach(function(e){
    var sn = String((e && e.sn) || '');
    var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
    if(!sn) return;
    if(on){
      selectedSnSet[sn] = true;
      if(mac) selectedMacSet[mac] = true;
      ensureTrackLoaded(sn, false);
    }else{
      delete selectedSnSet[sn];
      if(mac) delete selectedMacSet[mac];
    }
  });
  syncTableSelectionUi();
  renderLiveCards(latestDroneRows);
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function esc(v){
  return String(v==null?'':v)
    .replace(/&/g,'&amp;')
    .replace(/</g,'&lt;')
    .replace(/>/g,'&gt;')
    .replace(/"/g,'&quot;')
    .replace(/'/g,'&#39;');
}
function escAttr(v){
  return esc(v).replace(/\\n/g,'&#10;');
}
function isTypingTarget(el){
  var t = el || document.activeElement;
  if(!t || !t.tagName) return false;
  var tag = String(t.tagName || '').toLowerCase();
  if(tag === 'input' || tag === 'textarea' || tag === 'select') return true;
  return !!t.isContentEditable;
}
function openAdvModal(){
  var m = qs('adv-modal');
  if(m) m.classList.add('show');
}
function closeAdvModal(){
  var m = qs('adv-modal');
  if(m) m.classList.remove('show');
}
function hideInfoCard(){
  var modal = qs('info-modal');
  if(!modal) return;
  modal.classList.remove('show');
  activeInfoSn = '';
}
function clampInfoCardPosition(card, x, y){
  var margin = 8;
  var rect = card.getBoundingClientRect();
  var w = Math.max(1, rect.width || card.offsetWidth || 360);
  var h = Math.max(1, rect.height || card.offsetHeight || 220);
  var vw = Math.max(w + margin * 2, window.innerWidth || document.documentElement.clientWidth || w);
  var vh = Math.max(h + margin * 2, window.innerHeight || document.documentElement.clientHeight || h);
  return {
    x: Math.max(margin, Math.min(Number(x) || margin, vw - w - margin)),
    y: Math.max(margin, Math.min(Number(y) || margin, vh - h - margin))
  };
}
function placeInfoCard(card, x, y){
  if(!card) return;
  var pos = clampInfoCardPosition(card, x, y);
  infoCardDragState.x = pos.x;
  infoCardDragState.y = pos.y;
  card.style.position = 'fixed';
  card.style.left = pos.x + 'px';
  card.style.top = pos.y + 'px';
  card.style.right = 'auto';
  card.style.bottom = 'auto';
  card.style.margin = '0';
}
function applyInfoCardDragPosition(){
  var card = qs('info-modal') ? qs('info-modal').querySelector('.info-card') : null;
  if(!card || infoCardDragState.x == null || infoCardDragState.y == null) return;
  placeInfoCard(card, infoCardDragState.x, infoCardDragState.y);
}
function bindInfoCardDrag(){
  var modal = qs('info-modal');
  if(!modal || modal.getAttribute('data-drag-bound') === '1') return;
  var card = modal.querySelector('.info-card');
  var hd = modal.querySelector('.info-card-hd');
  if(!card || !hd) return;
  modal.setAttribute('data-drag-bound', '1');
  hd.addEventListener('pointerdown', function(ev){
    if(ev.button != null && ev.button !== 0) return;
    if(ev.target && ev.target.closest && ev.target.closest('button,a,input,select,textarea')) return;
    var rect = card.getBoundingClientRect();
    infoCardDragState.pointerId = ev.pointerId;
    infoCardDragState.startX = ev.clientX;
    infoCardDragState.startY = ev.clientY;
    infoCardDragState.cardX = rect.left;
    infoCardDragState.cardY = rect.top;
    placeInfoCard(card, rect.left, rect.top);
    card.classList.add('dragging');
    try{ hd.setPointerCapture(ev.pointerId); }catch(_e){}
    ev.preventDefault();
  });
  hd.addEventListener('pointermove', function(ev){
    if(infoCardDragState.pointerId !== ev.pointerId) return;
    var nextX = infoCardDragState.cardX + (ev.clientX - infoCardDragState.startX);
    var nextY = infoCardDragState.cardY + (ev.clientY - infoCardDragState.startY);
    placeInfoCard(card, nextX, nextY);
    ev.preventDefault();
  });
  function finish(ev){
    if(infoCardDragState.pointerId !== ev.pointerId) return;
    infoCardDragState.pointerId = null;
    card.classList.remove('dragging');
    try{ hd.releasePointerCapture(ev.pointerId); }catch(_e){}
  }
  hd.addEventListener('pointerup', finish);
  hd.addEventListener('pointercancel', finish);
}
function stripUnsafeHtml(html){
  var t = document.createElement('template');
  t.innerHTML = String(html || '');
  t.content.querySelectorAll('script,iframe,object,embed,link[rel="import"]').forEach(function(n){ n.remove(); });
  t.content.querySelectorAll('*').forEach(function(n){
    Array.prototype.slice.call(n.attributes || []).forEach(function(a){
      var name = String(a.name || '').toLowerCase();
      var val = String(a.value || '').trim().toLowerCase();
      if(name.indexOf('on') === 0 || name === 'srcdoc' || ((name === 'href' || name === 'src') && val.indexOf('javascript:') === 0)){
        n.removeAttribute(a.name);
      }
    });
  });
  return t.innerHTML;
}
function showInfoCard(msg, asHtml){
  var modal = qs('info-modal');
  var body = qs('info-card-body');
  if(!modal || !body) return;
  if(asHtml){
    body.innerHTML = stripUnsafeHtml(msg);
  }else{
    body.textContent = String(msg || '无详情');
  }
  modal.classList.add('show');
  applyInfoCardDragPosition();
}
function showDroneInfoCard(e){
  e = e || {};
  activeInfoSn = String(e.sn || '');
  showInfoCard(buildInfoHtml(e), true);
}
function findDisplayRowBySn(rows, sn){
  sn = String(sn || '');
  if(!sn) return null;
  var arr = Array.isArray(rows) ? rows : [];
  for(var i=0;i<arr.length;i++){
    var row = arr[i] || {};
    if(String(row.sn || '') === sn) return row;
  }
  return null;
}
function refreshActiveInfoCard(rows){
  var modal = qs('info-modal');
  var body = qs('info-card-body');
  var sn = String(activeInfoSn || '');
  if(!modal || !body || !sn || !modal.classList.contains('show')) return;
  var row = findDisplayRowBySn(rows, sn) || latestDroneMap[sn] || null;
  if(!row) return;
  var oldScroll = body.scrollTop;
  body.innerHTML = stripUnsafeHtml(buildInfoHtml(row));
  body.scrollTop = oldScroll;
}
function fieldKey(sn, field){ return String(sn||'') + '|' + String(field||''); }
function markFieldHighlight(sn, field, ms){
  var now = Date.now();
  droneFieldHl[fieldKey(sn, field)] = {start: now, end: now + (ms || HL_TOTAL_MS)};
}
function highlightAlpha(sn, field){
  var it = droneFieldHl[fieldKey(sn, field)];
  if(!it) return 0;
  var now = Date.now();
  var end = Number(it.end || 0);
  if(now >= end){
    delete droneFieldHl[fieldKey(sn, field)];
    return 0;
  }
  var start = Number(it.start || now);
  var t = Math.max(0, now - start);
  var fi = Math.max(0, Number(HL_FADE_IN_MS || 0));
  var ho = Math.max(0, Number(HL_HOLD_MS || 0));
  var fo = Math.max(0, Number(HL_FADE_OUT_MS || 0));
  if(fi > 0 && t <= fi){
    return Math.max(0, Math.min(1, t / fi));
  }
  if(t <= (fi + ho)){
    return 1;
  }
  var elapsedFo = t - fi - ho;
  if(fo <= 0){
    return 0;
  }
  if(elapsedFo >= fo){
    return 0;
  }
  return Math.max(0, 1 - (elapsedFo / fo));
}
function fieldCellAttrs(sn, field, extraCls){
  var cls = extraCls ? String(extraCls) : '';
  var attrs = ' data-hl-sn="'+escAttr(sn)+'" data-hl-field="'+escAttr(field)+'"';
  var a = highlightAlpha(sn, field);
  if(a <= 0){
    return (cls ? (' class="'+cls+'"') : '') + attrs;
  }
  cls = (cls ? (cls + ' ') : '') + 'hl';
  return ' class=\"'+cls+'\"'+attrs+' style=\"--hl-alpha:'+a.toFixed(3)+'\"';
}
function animateHighlightsStep(){
  var nodes = document.querySelectorAll('#tbody td[data-hl-sn][data-hl-field]');
  var active = false;
  for(var i=0;i<nodes.length;i++){
    var td = nodes[i];
    var sn = td.getAttribute('data-hl-sn') || '';
    var field = td.getAttribute('data-hl-field') || '';
    var a = highlightAlpha(sn, field);
    if(a > 0){
      active = true;
      if(!td.classList.contains('hl')) td.classList.add('hl');
      td.style.setProperty('--hl-alpha', a.toFixed(3));
    }else{
      if(td.classList.contains('hl')) td.classList.remove('hl');
      td.style.removeProperty('--hl-alpha');
    }
  }
  if(active){
    requestAnimationFrame(animateHighlightsStep);
  }else{
    highlightAnimRunning = false;
  }
}
function ensureHighlightAnimation(){
  if(highlightAnimRunning) return;
  highlightAnimRunning = true;
  requestAnimationFrame(animateHighlightsStep);
}
function syncFieldHighlights(list){
  var seen = {};
  (list || []).forEach(function(e){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    seen[sn] = true;
    var cur = {
      model: String(e.model || ''),
      uas_id: String(e.uas_id || ''),
      rssi: String(e.rssi == null ? '' : e.rssi),
      pkts: String(e.pkts == null ? '' : e.pkts),
      dir: String(e.dir || ''),
      last_seen: String(e.last_seen || ''),
      age_text: String(e.age_text || fmtAge(e.age)),
      lat: String(e.lat == null ? '' : e.lat),
      lon: String(e.lon == null ? '' : e.lon),
      alt: String(e.alt == null ? '' : e.alt),
      spd: String(e.spd == null ? '' : e.spd),
      vspd: String(e.vspd == null ? '' : e.vspd)
    };
    var prev = droneFieldPrev[sn];
    if(prev){
      Object.keys(cur).forEach(function(k){
        if(prev[k] !== cur[k]) markFieldHighlight(sn, k, HL_TOTAL_MS);
      });
    }
    droneFieldPrev[sn] = cur;
  });
  Object.keys(droneFieldPrev).forEach(function(sn){
    if(!seen[sn]) delete droneFieldPrev[sn];
  });
}
function redirectToLogin(){
  if(authRedirecting) return;
  authRedirecting = true;
  try{ if(ws) ws.close(); }catch(_e){}
  location.href = '/login?next=/';
}
function isAuthExpiredResponse(resp, data){
  var status = resp && Number(resp.status || 0);
  var err = String((data && data.error) || '');
  return status === 401 && (!!(data && data.auth_expired) || err === 'login required' || err === 'auth required');
}
function handleAuthExpired(resp, data){
  if(isAuthExpiredResponse(resp, data)){
    redirectToLogin();
    return true;
  }
  return false;
}
function authAwareError(resp, data){
  if(handleAuthExpired(resp, data)){
    var e = new Error('login required');
    e.authRedirect = true;
    return e;
  }
  return null;
}
function showBanner(text, kind, timeoutMs, opts){
  if(!opts || opts.persist !== false){
    addNotificationEntry(text, kind || 'info');
  }
  var host = qs('banner-stack');
  if(!host){
    host = document.createElement('div');
    host.id = 'banner-stack';
    host.className = 'banner-stack';
    document.body.appendChild(host);
  }
  var node = document.createElement('div');
  node.className = 'banner ' + (kind || 'info');
  node.title = '点击关闭';
  node.textContent = String(text || '');
  host.appendChild(node);
  setTimeout(function(){ node.classList.add('show'); }, 10);
  var ttl = Math.max(1200, Number(timeoutMs || 3200));
  var closed = false;
  function closeBanner(){
    if(closed) return;
    closed = true;
    node.classList.remove('show');
    setTimeout(function(){ if(node.parentNode) node.parentNode.removeChild(node); }, 280);
  }
  node.addEventListener('click', closeBanner);
  setTimeout(closeBanner, ttl);
}
var initialLoadingStartedAt = 0;
var initialLoadingTimeoutSec = 15;
var initialLoadingTimer = null;
function loadingStateForTarget(target){
  if(!initialLoadingStartedAt) initialLoadingStartedAt = Date.now();
  var elapsed = Math.floor((Date.now() - initialLoadingStartedAt) / 1000);
  var remain = Math.max(0, initialLoadingTimeoutSec - elapsed);
  var name = String(target || '\u672c\u673a\u57fa\u7ad9');
  if(remain > 0){
    return {
      target: name,
      detail: '\u6b63\u5728\u8bfb\u53d6 ' + name + ' \u6570\u636e',
      status: '\u5df2\u7b49\u5f85 ' + elapsed + 's\uff0c\u9884\u8ba1 ' + remain + 's \u540e\u63d0\u793a\u8d85\u65f6'
    };
  }
  return {
    target: name,
    detail: '\u8bfb\u53d6 ' + name + ' \u6570\u636e\u8d85\u65f6\uff0c\u4ecd\u5728\u7b49\u5f85\u540e\u7aef\u8fd4\u56de',
    status: '\u5df2\u7b49\u5f85 ' + elapsed + 's\uff0c\u6682\u4e0d\u5173\u95ed\u9875\u9762'
  };
}
function loadingTextForTarget(target){
  if(!initialLoadingStartedAt) initialLoadingStartedAt = Date.now();
  var elapsed = Math.floor((Date.now() - initialLoadingStartedAt) / 1000);
  var remain = Math.max(0, initialLoadingTimeoutSec - elapsed);
  var name = String(target || '本机基站');
  if(remain > 0) return '正在读取 ' + name + ' 数据，' + remain + 's 后超时';
  return '读取 ' + name + ' 数据超时，仍在等待返回';
}
function showInitialDataLoading(target, title){
  var host = qs('rid-loading-overlay');
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
  function tickLoading(){
    var state = loadingStateForTarget(target);
    if(titleEl) titleEl.textContent = String(title || '\u6b63\u5728\u8bfb\u53d6\u6570\u636e');
    if(copyEl) copyEl.textContent = state.detail;
    if(targetEl) targetEl.textContent = state.target;
    if(statusEl) statusEl.textContent = state.status;
  }
  tickLoading();
  host.classList.add('show');
  document.body.classList.add('rid-loading-active');
  if(initialLoadingTimer) clearInterval(initialLoadingTimer);
  initialLoadingTimer = setInterval(tickLoading, 1000);
}
function clearInitialDataLoading(){
  var host = qs('rid-loading-overlay');
  if(host) host.classList.remove('show');
  document.body.classList.remove('rid-loading-active');
  if(initialLoadingTimer){
    clearInterval(initialLoadingTimer);
    initialLoadingTimer = null;
  }
}
function notificationKindLabel(kind){
  kind = String(kind || 'info');
  if(kind === 'ok') return '完成';
  if(kind === 'warn') return '警告';
  return '通知';
}
function normalizeNotificationItems(items){
  return (Array.isArray(items) ? items : []).filter(function(x){ return x && x.text; }).slice(0, 200);
}
async function refreshNotificationCenter(){
  if(notificationSyncBusy) return;
  notificationSyncBusy = true;
  try{
    var data = await getJson('/api/notifications?limit=200');
    notificationItems = normalizeNotificationItems(data.items);
    notificationSeq = Number(data.seq || notificationSeq || 0);
    renderNotificationCenter();
  }catch(e){
    if(!(e && e.authRedirect) && qs('notify-center-sub')){
      qs('notify-center-sub').textContent = '通知同步失败';
    }
  }finally{
    notificationSyncBusy = false;
  }
}
function applyNotificationPayload(data){
  if(data && Array.isArray(data.items)){
    notificationItems = normalizeNotificationItems(data.items);
    notificationSeq = Number(data.seq || notificationSeq || 0);
    renderNotificationCenter();
  }
}
function addNotificationEntry(text, kind){
  var msg = String(text || '').trim();
  if(!msg) return;
  fetch(apiUrl('/api/notifications'), {
    method:'POST',
    cache:'no-store',
    headers:{'Content-Type':'application/json','X-LightRID-Page':'1'},
    body: JSON.stringify({text: msg, kind: String(kind || 'info')})
  }).then(function(resp){
    return resp.json().catch(function(){ return {}; }).then(function(data){
      var authErr = authAwareError(resp, data);
      if(authErr) throw authErr;
      if(resp.ok && data.ok !== false) applyNotificationPayload(data);
    });
  }).catch(function(e){
    if(!(e && e.authRedirect)) refreshNotificationCenter();
  });
}
function fmtNotificationTime(ts){
  var n = Number(ts || 0);
  if(!isFinite(n) || n <= 0) return '-';
  try{ return new Date(n).toLocaleString(); }catch(_e){ return '-'; }
}
function ensureNotificationCenter(){
  if(!qs('notify-center-button')){
    var btn = document.createElement('button');
    btn.id = 'notify-center-button';
    btn.className = 'notify-center-button';
    btn.type = 'button';
    btn.title = '通知中心';
    btn.setAttribute('aria-label', '通知中心');
    btn.innerHTML = '<span class="notify-center-glyph" aria-hidden="true"></span><span id="notify-center-count" class="notify-center-count">0</span>';
    btn.addEventListener('click', function(ev){
      ev.preventDefault();
      toggleNotificationCenter();
    });
    document.body.appendChild(btn);
  }
  if(!qs('notify-center-panel')){
    var panel = document.createElement('aside');
    panel.id = 'notify-center-panel';
    panel.className = 'notify-center-panel';
    panel.setAttribute('aria-label', '通知中心');
    panel.innerHTML =
      '<div class="notify-center-head">'+
      '  <div><div class="notify-center-title">通知中心</div><div id="notify-center-sub" class="notify-center-sub">暂无通知</div></div>'+
      '  <button class="btn-mini" id="notify-center-clear" type="button">清空</button>'+
      '</div>'+
      '<div id="notify-center-list" class="notify-center-list"></div>';
    document.body.appendChild(panel);
    panel.addEventListener('click', function(ev){
      var del = ev.target && ev.target.closest ? ev.target.closest('.notify-item-del[data-id]') : null;
      if(!del) return;
      ev.preventDefault();
      deleteNotificationItem(del.getAttribute('data-id'));
    });
  }
  if(qs('notify-center-clear') && qs('notify-center-clear').getAttribute('data-bound') !== '1'){
    qs('notify-center-clear').setAttribute('data-bound', '1');
    qs('notify-center-clear').addEventListener('click', function(ev){
      ev.preventDefault();
      postJson('/api/notifications/clear', {}).then(applyNotificationPayload).catch(function(e){
        if(!(e && e.authRedirect)) showBanner('清空通知失败: ' + ((e && e.message) ? e.message : e), 'warn', 3200, {persist:false});
      });
    });
  }
  renderNotificationCenter();
  refreshNotificationCenter();
  if(!notificationPollTimer){
    notificationPollTimer = setInterval(refreshNotificationCenter, 5000);
  }
}
function toggleNotificationCenter(force){
  ensureNotificationCenter();
  var panel = qs('notify-center-panel');
  var btn = qs('notify-center-button');
  var show = (typeof force === 'boolean') ? force : !(panel && panel.classList.contains('show'));
  if(panel) panel.classList.toggle('show', show);
  if(btn) btn.classList.toggle('active', show);
}
function deleteNotificationItem(id){
  postJson('/api/notifications/delete', {id: id}).then(applyNotificationPayload).catch(function(e){
    if(!(e && e.authRedirect)) showBanner('删除通知失败: ' + ((e && e.message) ? e.message : e), 'warn', 3200, {persist:false});
  });
}
function renderNotificationCenter(){
  var btn = qs('notify-center-button');
  var count = qs('notify-center-count');
  var sub = qs('notify-center-sub');
  var list = qs('notify-center-list');
  var n = Array.isArray(notificationItems) ? notificationItems.length : 0;
  if(btn) btn.classList.toggle('has-items', n > 0);
  if(count) count.textContent = n > 99 ? '99+' : String(n);
  if(sub) sub.textContent = n ? ('保留 ' + n + ' 条历史通知') : '暂无通知';
  if(!list) return;
  if(!n){
    list.innerHTML = '<div class="notify-center-empty">暂无通知</div>';
    return;
  }
  list.innerHTML = notificationItems.map(function(item){
    item = item || {};
    var id = String(item.id || '');
    var kind = String(item.kind || 'info');
    return '<article class="notify-item '+escAttr(kind)+'">'+
      '<span class="notify-item-bar"></span>'+
      '<div><div class="notify-item-text">'+esc(item.text || '')+'</div>'+
      '<div class="notify-item-time">'+esc(notificationKindLabel(kind))+' · '+esc(fmtNotificationTime(item.ts))+'</div></div>'+
      '<button class="notify-item-del" type="button" data-id="'+escAttr(id)+'" title="删除">×</button>'+
      '</article>';
  }).join('');
}
function notifyBtnText(){
  if(!('Notification' in window)) return '网页通知(不支持)';
  if(webNotifyEnabled && Notification.permission === 'granted') return '网页通知(已开)';
  if(Notification.permission === 'denied') return '网页通知(已拒绝)';
  return '网页通知';
}
function updateNotifyButton(){
  var btn = qs('btn-web-notify');
  if(!btn) return;
  btn.textContent = notifyBtnText();
  btn.disabled = !('Notification' in window) || Notification.permission === 'denied';
}
async function requestWebNotifyPermission(){
  if(!('Notification' in window)){
    showBanner('当前浏览器不支持网页通知', 'warn', 4200);
    return;
  }
  try{
    if(Notification.permission === 'granted'){
      webNotifyEnabled = true;
      updateNotifyButton();
      showBanner('网页通知已启用', 'ok', 2200);
      return;
    }
    var perm = await Notification.requestPermission();
    webNotifyEnabled = (perm === 'granted');
    updateNotifyButton();
    if(webNotifyEnabled){
      try{
        new Notification('Light RID Scanner 通知已启用', {body:'将推送飞机上下线事件'});
      }catch(_e){}
      showBanner('网页通知权限已授权', 'ok', 2400);
    } else if(perm === 'denied'){
      showBanner('网页通知权限被拒绝', 'warn', 4200);
    }
  }catch(_e){}
}
function pushWebNotification(title, body, tag){
  if(!webNotifyEnabled) return;
  if(!('Notification' in window) || Notification.permission !== 'granted') return;
  try{
    new Notification(title, {body: body || '', tag: tag || ('rid-'+Date.now())});
  }catch(_e){}
}
function replayPreviewActive(){
  return currentAppPage() === 'history' && !!replaySyncPaused;
}
function resetDroneNotificationBaseline(list){
  var next = {};
  (Array.isArray(list) ? list : []).forEach(function(e){
    e = e || {};
    var sn = String(e.sn || '');
    if(sn) next[sn] = !!e.lost;
  });
  droneStatePrev = next;
}
function handleDroneNotifications(list){
  if(replayPreviewActive() || suppressNextDroneNotifications){
    suppressNextDroneNotifications = false;
    resetDroneNotificationBaseline(list);
    return;
  }
  var seen = {};
  var nowLabel = new Date().toLocaleTimeString();
  (list || []).forEach(function(e){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    seen[sn] = true;
    var isLost = !!e.lost;
    if(typeof droneStatePrev[sn] === 'undefined'){
      droneStatePrev[sn] = isLost;
      return;
    }
    if(droneStatePrev[sn] !== isLost){
      var title = isLost ? '飞机下线' : '飞机上线';
      var body = nowLabel + '  ' + sn + '\\n' + String(e.model || 'N/A') + '  ' +
        (e.rssi == null ? 'N/A' : (e.rssi + 'dBm'));
      pushWebNotification(title, body, 'rid-'+sn+'-'+(isLost?'off':'on'));
      showBanner(title + '  ' + sn, isLost ? 'warn' : 'ok', 2600, {persist:false});
    }
    droneStatePrev[sn] = isLost;
  });
  Object.keys(droneStatePrev).forEach(function(sn){
    if(!seen[sn]) delete droneStatePrev[sn];
  });
}
async function getJson(url){
  var resp = await fetch(apiUrl(url), {cache:'no-store', headers:{'X-LightRID-Page':'1'}});
  var data = {};
  try{ data = await resp.json(); }catch(_e){}
  if(!resp.ok || data.ok===false){
    var authErr = authAwareError(resp, data);
    if(authErr) throw authErr;
    throw new Error((data && data.error) ? data.error : ('HTTP '+resp.status));
  }
  return data;
}
function apiUrl(url){
  var u = String(url || '');
  try{
    return new URL(u, window.location.origin).toString();
  }catch(_e){
    return u;
  }
}
function loadThemePref(){
  try{
    var s = localStorage.getItem('rid_ui_theme');
    if(s === 'dark' || s === 'light') return s;
  }catch(_e){}
  try{
    if(window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches){
      return 'light';
    }
  }catch(_e){}
  return 'dark';
}
function applyTheme(theme){
  uiTheme = (theme === 'light') ? 'light' : 'dark';
  var light = (uiTheme === 'light');
  if(document.body){
    document.body.classList.toggle('theme-light', light);
    document.body.classList.toggle('theme-dark', !light);
  }
  try{ localStorage.setItem('rid_ui_theme', uiTheme); }catch(_e){}
  var btn = qs('btn-theme');
  if(btn){
    btn.textContent = light ? '深色' : '浅色';
    btn.title = light ? '切换为深色' : '切换为浅色';
  }
}
function toggleTheme(){
  applyTheme(uiTheme === 'light' ? 'dark' : 'light');
}
async function postJson(url, body){
  var resp = await fetch(apiUrl(url), {
    method:'POST',
    headers:{'Content-Type':'application/json','X-LightRID-Page':'1'},
    body: JSON.stringify(body||{})
  });
  var data = {};
  try{ data = await resp.json(); }catch(_e){}
  if(!resp.ok || data.ok===false){
    var authErr = authAwareError(resp, data);
    if(authErr) throw authErr;
    throw new Error((data && data.error) ? data.error : ('HTTP '+resp.status));
  }
  return data;
}

function setToolsStatus(text){
  var st = qs('tools-status');
  if(st) st.textContent = String(text || '-');
}

function _toolStamp(){
  var d = new Date();
  function p2(n){ return String(n).padStart(2, '0'); }
  return d.getFullYear() + p2(d.getMonth()+1) + p2(d.getDate()) + '_' + p2(d.getHours()) + p2(d.getMinutes()) + p2(d.getSeconds());
}

function _downloadJsonFile(name, data){
  var text = JSON.stringify(data, null, 2);
  var blob = new Blob([text], {type:'application/json;charset=utf-8'});
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = String(name || ('rid_export_' + _toolStamp() + '.json'));
  document.body.appendChild(a);
  a.click();
  setTimeout(function(){
    try{ URL.revokeObjectURL(url); }catch(_e){}
    if(a.parentNode) a.parentNode.removeChild(a);
  }, 200);
}

function _readFileText(file){
  return new Promise(function(resolve, reject){
    if(!file){
      reject(new Error('未选择文件'));
      return;
    }
    var fr = new FileReader();
    fr.onload = function(){ resolve(String(fr.result || '')); };
    fr.onerror = function(){ reject(new Error('文件读取失败')); };
    fr.readAsText(file, 'utf-8');
  });
}

function _pickImportFile(id){
  var input = qs(id);
  if(!input) return;
  input.value = '';
  input.click();
}

function _pickToolSn(){
  var sel = qs('track-sn-select');
  var sn = sel ? String(sel.value || '').trim() : '';
  if(sn) return sn;
  var selected = selectedSnList();
  if(selected.length) return String(selected[0] || '');
  return '';
}

async function toolsExportAllDetails(){
  setToolsStatus('导出全部详情中...');
  try{
    var data = await getJson('/api/tools/export/all');
    _downloadJsonFile('rid_details_all_' + _toolStamp() + '.json', data);
    setToolsStatus('导出完成：全部详情 ' + Number(data.count || 0) + ' 架');
    showBanner('已导出全部详情', 'ok', 2200);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导出失败: ' + msg);
    showBanner('导出全部详情失败', 'warn', 3600);
  }
}

async function toolsExportSingleTrack(){
  var sn = _pickToolSn();
  if(!sn){
    setToolsStatus('请先在“历史/轨迹”中选择飞机，或勾选目标飞机');
    showBanner('请先选择飞机再导出轨迹', 'warn', 3200);
    return;
  }
  setToolsStatus('导出轨迹中: ' + sn);
  try{
    var data = await getJson('/api/tools/export/track?sn=' + encodeURIComponent(sn));
    _downloadJsonFile('rid_track_' + sn + '_' + _toolStamp() + '.json', data);
    setToolsStatus('导出完成: ' + sn + ' (' + Number(data.count || 0) + ' 点)');
    showBanner('已导出轨迹: ' + sn, 'ok', 2200);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导出轨迹失败: ' + msg);
    showBanner('导出轨迹失败', 'warn', 3600);
  }
}

async function toolsImportAllDetailsFromFile(file){
  try{
    setToolsStatus('导入全部详情中...');
    var txt = await _readFileText(file);
    var payload = JSON.parse(txt);
    var data = await postJson('/api/tools/import/all', {payload: payload});
    setToolsStatus('导入完成: 新增 ' + Number(data.added || 0) + '，更新 ' + Number(data.updated || 0) + '，跳过 ' + Number(data.skipped || 0));
    showBanner('全部详情导入完成', 'ok', 2400);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导入失败: ' + msg);
    showBanner('导入全部详情失败', 'warn', 4200);
  }
}

async function toolsImportSingleTrackFromFile(file){
  try{
    setToolsStatus('导入单机轨迹中...');
    var txt = await _readFileText(file);
    var obj = JSON.parse(txt);
    var sn = _pickToolSn();
    var payload = null;
    if(Array.isArray(obj)){
      payload = {sn: sn, track: obj};
    }else if(obj && typeof obj === 'object'){
      if(obj.payload && typeof obj.payload === 'object'){
        payload = obj.payload;
      }else{
        payload = obj;
      }
    }else{
      throw new Error('文件格式无效');
    }
    if(!payload || typeof payload !== 'object'){
      throw new Error('文件格式无效');
    }
    if(!payload.sn){
      payload.sn = sn;
    }
    payload.sn = String(payload.sn || '').trim();
    if(!payload.sn){
      throw new Error('文件内无 SN，且当前未选择飞机');
    }
    if(!Array.isArray(payload.track)){
      throw new Error('文件内缺少 track 数组');
    }
    var data = await postJson('/api/tools/import/track', {payload: payload});
    trackCache[payload.sn] = payload.track.slice();
    delete trackFetchMeta[payload.sn];
    delete trackLineSig[payload.sn];
    ensureTrackLoaded(payload.sn, true);
    setToolsStatus('导入完成: ' + payload.sn + ' (' + Number(data.count || 0) + ' 点)');
    showBanner('轨迹导入完成: ' + payload.sn, 'ok', 2400);
  }catch(e){
    var msg = (e && e.message) ? e.message : e;
    setToolsStatus('导入轨迹失败: ' + msg);
    showBanner('导入单机轨迹失败', 'warn', 4200);
  }
}

async function loadIfaceOptions(force){
  if(ifaceOptionsLoaded && !force) return;
  var sel = qs('iface-select');
  var st = qs('iface-status');
  if(!sel) return;
  try{
    var data = await getJson('/api/interfaces');
    var items = Array.isArray(data.items) ? data.items : [];
    var html = '<option value="">请选择默认网卡</option>';
    items.forEach(function(it){
      it = it || {};
      var name = String(it.name || '');
      if(!name) return;
      var mode = String(it.mode || '');
      var s5 = it.supports_5g ? '5G' : '2.4G';
      var lb = name + (mode ? (' ['+mode+']') : '') + ' ' + s5;
      html += '<option value=\"'+escAttr(name)+'\">'+esc(lb)+'</option>';
    });
    sel.innerHTML = html;
    var chosen = (metaState && metaState.iface_selected!=null) ? String(metaState.iface_selected) : String(data.selected_iface || '');
    if(chosen) sel.value = chosen;
    var chk = qs('scan-wifi-fast');
    if(chk && !chk.dataset.edited){
      chk.checked = !!(metaState && metaState.scan_wifi_fast);
      if(typeof data.scan_wifi_fast !== 'undefined') chk.checked = !!data.scan_wifi_fast;
    }
    if(st){
      var active = String((metaState && metaState.sniff_iface) || data.active_iface || '-');
      st.textContent = '当前采集网卡: ' + active;
    }
    ifaceOptionsLoaded = true;
  }catch(e){
    if(st) st.textContent = '网卡加载失败: ' + ((e && e.message) ? e.message : e);
  }
}

function setFreezeState(frozen){
  uiFrozen = !!frozen;
  var btn = qs('btn-freeze');
  if(btn){
    btn.textContent = uiFrozen ? '恢复同步' : '冻结列表';
    btn.classList.toggle('warn', uiFrozen);
  }
}

function toggleFreeze(){
  if(!uiFrozen){
    frozenPendingData = null;
    setFreezeState(true);
    return;
  }
  setFreezeState(false);
  if(frozenPendingData && !replaySyncPaused){
    var d = frozenPendingData;
    frozenPendingData = null;
    onData(d);
  }
}

function setLogPanelCollapsed(collapsed){
  var panel = qs('log-panel');
  if(!panel) return;
  if(collapsed) panel.classList.add('collapsed');
  else panel.classList.remove('collapsed');
  var btn = qs('log-panel-toggle');
  if(btn) btn.textContent = collapsed ? '展开' : '收起';
  syncBottomPanelLayout();
}

function toggleLogPanel(){
  var panel = qs('log-panel');
  if(!panel) return;
  setLogPanelCollapsed(!panel.classList.contains('collapsed'));
}

function setMapPanelCollapsed(collapsed){
  var panel = qs('map-panel');
  if(!panel) return;
  if(collapsed) panel.classList.add('collapsed');
  else panel.classList.remove('collapsed');
  var btn = qs('map-panel-toggle');
  if(btn) btn.textContent = collapsed ? '展开' : '收起';
  syncBottomPanelLayout();
  if(!collapsed && map){
    setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 0);
  }
}

function toggleMapPanel(){
  var panel = qs('map-panel');
  if(!panel) return;
  setMapPanelCollapsed(!panel.classList.contains('collapsed'));
}

function setApPanelCollapsed(collapsed){
  var panel = qs('ap-panel');
  if(!panel) return;
  if(collapsed) panel.classList.add('collapsed');
  else panel.classList.remove('collapsed');
  var btn = qs('ap-panel-toggle');
  if(btn) btn.textContent = collapsed ? '展开' : '收起';
  syncBottomPanelLayout();
}

function toggleApPanel(){
  var panel = qs('ap-panel');
  if(!panel) return;
  setApPanelCollapsed(!panel.classList.contains('collapsed'));
}

function syncBottomPanelLayout(){
  var bottom = document.querySelector('.bottom');
  if(!bottom) return;
  var mapPanel = qs('map-panel');
  var logPanel = qs('log-panel');
  var apPanel = qs('ap-panel');
  var mapCollapsed = !!(mapPanel && mapPanel.classList.contains('collapsed'));
  var logCollapsed = !!(logPanel && logPanel.classList.contains('collapsed'));
  var apCollapsed = !!(apPanel && apPanel.classList.contains('collapsed'));
  var allCollapsed = mapCollapsed && logCollapsed && apCollapsed;
  bottom.classList.toggle('map-collapsed', mapCollapsed);
  bottom.classList.toggle('log-collapsed', logCollapsed);
  bottom.classList.toggle('ap-collapsed', apCollapsed);
  bottom.classList.toggle('all-collapsed', allCollapsed);
  document.body.classList.toggle('bottom-all-collapsed', allCollapsed);
  if(map && !mapCollapsed && !allCollapsed){
    setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 0);
  }
}

function isMapFullscreen(){
  var panel = qs('map-panel');
  var fe = document.fullscreenElement || document.webkitFullscreenElement || document.msFullscreenElement || null;
  return !!(panel && fe && (fe === panel || panel.contains(fe)));
}

function ensureMapMiniList(){
  var panel = qs('map-panel');
  if(!panel) return null;
  var box = qs('map-mini-list');
  if(!box){
    box = document.createElement('div');
    box.id = 'map-mini-list';
    box.className = 'map-mini-list';
    panel.appendChild(box);
  }
  return box;
}

function updateMapFullscreenButton(){
  var btn = qs('btn-map-fullscreen');
  if(!btn) return;
  var allow = currentAppPage() === 'history';
  btn.style.display = allow ? '' : 'none';
  btn.disabled = !allow;
  if(!allow){
    btn.textContent = '全屏';
    return;
  }
  btn.textContent = isMapFullscreen() ? '退出全屏' : '全屏';
}

function syncMapFullscreenUi(){
  var panel = qs('map-panel');
  var entering = isMapFullscreen();
  ensureMapMiniList();
  if(panel){
    panel.classList.toggle('fullscreen', entering);
    if(entering && panel.classList.contains('collapsed')){
      setMapPanelCollapsed(false);
    }
    if(!entering && mapCollapsedBeforeFullscreen === true){
      setMapPanelCollapsed(true);
    }
  }
  if(!entering) mapCollapsedBeforeFullscreen = null;
  updateMapFullscreenButton();
  renderMapMiniList(latestDroneRows);
  if(map){
    setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 0);
  }
}

async function toggleMapFullscreen(){
  var panel = qs('map-panel');
  if(!panel) return;
  if(currentAppPage() !== 'history'){
    showBanner('实时页不提供地图全屏，请切到历史记录使用。', 'info', 2600);
    return;
  }
  try{
    if(isMapFullscreen()){
      if(document.exitFullscreen) await document.exitFullscreen();
      else if(document.webkitExitFullscreen) document.webkitExitFullscreen();
    }else{
      mapCollapsedBeforeFullscreen = panel.classList.contains('collapsed');
      if(mapCollapsedBeforeFullscreen){
        setMapPanelCollapsed(false);
      }
      if(panel.requestFullscreen) await panel.requestFullscreen();
      else if(panel.webkitRequestFullscreen) panel.webkitRequestFullscreen();
    }
    if(mapFsUiTimer){
      clearInterval(mapFsUiTimer);
      mapFsUiTimer = null;
    }
    var tries = 0;
    mapFsUiTimer = setInterval(function(){
      syncMapFullscreenUi();
      tries += 1;
      if(tries >= 24){
        clearInterval(mapFsUiTimer);
        mapFsUiTimer = null;
      }
    }, 80);
  }catch(e){
    showBanner('全屏切换失败: ' + ((e && e.message) ? e.message : e), 'warn', 3200);
  }
}

document.addEventListener('fullscreenchange', syncMapFullscreenUi);
document.addEventListener('webkitfullscreenchange', syncMapFullscreenUi);
document.addEventListener('msfullscreenchange', syncMapFullscreenUi);

function renderMapMiniList(list){
  var box = ensureMapMiniList();
  if(!box) return;
  var panel = qs('map-panel');
  var show = currentAppPage() === 'history'
    && (isMapFullscreen() || !!(panel && panel.classList && panel.classList.contains('fullscreen')));
  box.style.display = show ? 'block' : '';
  var rows = (Array.isArray(list) ? list : []).slice().filter(function(e){
    return !!String((e && e.sn) || '');
  });
  rows.sort(function(a,b){
    return String(a.sn || '').localeCompare(String(b.sn || ''));
  });
  var snSig = rows.map(function(e){ return String(e.sn || ''); }).join('|');
  var selSig = (currentAppPage() === 'history' ? historyVisibleSnList(rows) : selectedSnList()).slice().sort().join('|');
  var sig = snSig + '::' + selSig + '::' + (show ? '1' : '0');
  if(sig === miniListRenderSig){
    return;
  }
  miniListRenderSig = sig;
  if(!rows.length){
    box.innerHTML = '<div class="mini-title">暂无飞机</div>';
    return;
  }
  var html = '<div class="mini-title">历史记录 · 勾选飞机显示轨迹</div>';
  rows.forEach(function(e, idx){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    var model = String(e.model || 'N/A');
    var checked = isHistoryTrackVisible(sn) ? ' checked' : '';
    var chip = '<span class="track-color-chip" style="--track-color:'+escAttr(trackColorForSn(sn))+';'+(checked ? '' : 'display:none')+'" title="轨迹颜色"></span>';
    html += '<label class="mini-item"><input class="mini-sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+checked+'>'+
      chip+'<span class="mono">#'+(idx+1)+'</span><span class="sn" title="'+esc(sn)+'">'+esc(sn)+'</span><span class="mini-model" title="'+esc(model)+'">'+esc(model)+'</span></label>';
  });
  box.innerHTML = html;
  var cbs = box.querySelectorAll('.mini-sel-sn');
  for(var i=0;i<cbs.length;i++){
    cbs[i].addEventListener('change', function(ev){
      var sn = ev.target.getAttribute('data-sn') || '';
      setHistorySnVisible(sn, !!ev.target.checked);
      syncTableSelectionUi();
    });
  }
}

function refreshTrackMgrOptions(list){
  var sel = qs('track-sn-select');
  if(!sel) return;
  var rows = Array.isArray(list) ? list : [];
  var cur = String(sel.value || '');
  var html = '<option value="">请选择飞机</option>';
  rows.forEach(function(e){
    e = e || {};
    var sn = String(e.sn || '');
    if(!sn) return;
    var model = String(e.model || 'N/A');
    var cnt = Number(e.track_count || 0);
    var t = String(e.last_seen || '-');
    html += '<option value="'+escAttr(sn)+'">'+esc(sn+' | '+model+' | 轨迹'+cnt+'点 | 末次'+t)+'</option>';
  });
  sel.innerHTML = html;
  if(cur && rows.some(function(e){ return String((e && e.sn) || '') === cur; })){
    sel.value = cur;
  }
}

function syncTableSelectionUi(){
  var cbs = document.querySelectorAll('#tbody .sel-sn');
  var total = 0;
  var checked = 0;
  var page = currentAppPage();
  for(var i=0;i<cbs.length;i++){
    var sn = String(cbs[i].getAttribute('data-sn') || '');
    cbs[i].checked = (page === 'history') ? isHistoryTrackVisible(sn) : isSnSelected(sn);
    var chip = cbs[i].parentNode ? cbs[i].parentNode.querySelector('.track-color-chip') : null;
    if(chip) chip.style.display = cbs[i].checked ? '' : 'none';
    var tr = cbs[i].closest ? cbs[i].closest('tr[data-sn]') : null;
    if(tr) tr.classList.toggle('selected', !!cbs[i].checked);
    total += 1;
    if(cbs[i].checked) checked += 1;
  }
  var allCb = qs('sel-all');
  if(allCb){
    allCb.disabled = (total === 0);
    allCb.checked = (total > 0 && checked === total);
    allCb.indeterminate = (checked > 0 && checked < total);
  }
}

function buildExtraUi(){
  if(window.__ridExtraUiReady) return;
  window.__ridExtraUiReady = true;

  ensureNotificationCenter();

  if(!qs('info-modal')){
    var modal = document.createElement('div');
    modal.id = 'info-modal';
    modal.className = 'info-modal';
    modal.innerHTML =
      '<div class="info-card" role="dialog" aria-modal="false" aria-label="详情信息">'+
      '  <div class="info-card-hd"><span>详情信息</span><button id="info-card-close" class="info-card-close" type="button" title="关闭">×</button></div>'+
      '  <div id="info-card-body" class="info-card-body"></div>'+
      '</div>';
    document.body.appendChild(modal);
    modal.addEventListener('click', function(ev){
      var btn = ev.target && ev.target.closest ? ev.target.closest('.export-track-btn[data-sn]') : null;
      if(btn){
        ev.preventDefault();
        exportTrackForSn(btn.getAttribute('data-sn') || '');
        return;
      }
      var delBtn = ev.target && ev.target.closest ? ev.target.closest('.delete-history-btn[data-sn]') : null;
      if(delBtn){
        ev.preventDefault();
        deleteHistoryForSn(delBtn.getAttribute('data-sn') || '', {button: delBtn, hideCard: true});
        return;
      }
      if(ev.target === modal) hideInfoCard();
    });
  }
  bindInfoCardDrag();
  if(qs('info-card-close')) qs('info-card-close').addEventListener('click', hideInfoCard);
  if(!infoCardEscBound){
    document.addEventListener('keydown', function(ev){
      if(ev && ev.key === 'Escape'){
        hideInfoCard();
        closeAdvModal();
      }
    });
    infoCardEscBound = true;
  }

  var clearBtn = qs('btn-clear-history');
  if(clearBtn && !qs('sniff-state')){
    var sniffStat = document.createElement('span');
    sniffStat.className = 'stat snf';
    sniffStat.innerHTML = '采集 <b id="sniff-state" class="warn">-</b>';
    clearBtn.parentNode.insertBefore(sniffStat, clearBtn);
  }
  if(false && clearBtn && !qs('btn-theme')){
    var themeBtn = document.createElement('button');
    themeBtn.className = 'btn-mini';
    themeBtn.id = 'btn-theme';
    themeBtn.type = 'button';
    themeBtn.textContent = '浅色';
    clearBtn.parentNode.insertBefore(themeBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-dji-lookup')){
    var djiBtn = document.createElement('button');
    djiBtn.className = 'btn-mini';
    djiBtn.id = 'btn-dji-lookup';
    djiBtn.type = 'button';
    djiBtn.textContent = 'DJI查询';
    clearBtn.parentNode.insertBefore(djiBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-freeze')){
    var freezeBtn = document.createElement('button');
    freezeBtn.className = 'btn-mini';
    freezeBtn.id = 'btn-freeze';
    freezeBtn.type = 'button';
    freezeBtn.textContent = '冻结列表';
    clearBtn.parentNode.insertBefore(freezeBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-web-notify')){
    var notifyBtn = document.createElement('button');
    notifyBtn.className = 'btn-mini';
    notifyBtn.id = 'btn-web-notify';
    notifyBtn.type = 'button';
    notifyBtn.textContent = '网页通知';
    clearBtn.parentNode.insertBefore(notifyBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-hw-assistant')){
    var hwBtn = document.createElement('button');
    hwBtn.className = 'btn-mini';
    hwBtn.id = 'btn-hw-assistant';
    hwBtn.type = 'button';
    hwBtn.textContent = '硬件助手';
    clearBtn.parentNode.insertBefore(hwBtn, clearBtn);
  }
  if(clearBtn && !qs('btn-adv-open')){
    var advBtn = document.createElement('button');
    advBtn.className = 'btn-mini';
    advBtn.id = 'btn-adv-open';
    advBtn.type = 'button';
    advBtn.textContent = '高级设置';
    clearBtn.parentNode.insertBefore(advBtn, clearBtn);
  }

  var header = document.querySelector('header');
  if(header && !qs('security-banner')){
    var secBanner = document.createElement('div');
    secBanner.id = 'security-banner';
    secBanner.className = 'sniff-banner warn security-banner';
    secBanner.style.display = 'none';
    secBanner.innerHTML = '<span id="security-banner-text">当前处于 root 权限，存在安全风险。</span><button class="btn-mini warn" id="btn-security-settings" type="button">去设置修复</button>';
    header.appendChild(secBanner);
  }
  if(qs('btn-security-settings') && qs('btn-security-settings').getAttribute('data-bound') !== '1'){
    qs('btn-security-settings').setAttribute('data-bound', '1');
    qs('btn-security-settings').addEventListener('click', function(ev){
      ev.preventDefault();
      location.href = '/settings';
    });
  }
  if(header && !qs('sniff-banner')){
    var banner = document.createElement('div');
    banner.id = 'sniff-banner';
    banner.className = 'sniff-banner';
    header.appendChild(banner);
  }
  if(!qs('adv-modal')){
    var modal = document.createElement('div');
    modal.className = 'adv-modal';
    modal.id = 'adv-modal';
    modal.innerHTML =
      '<div class="adv-window" role="dialog" aria-modal="true" aria-label="高级设置">'+
      '<div class="adv-window-hd"><span>高级设置</span><button class="btn-mini" id="btn-adv-close" type="button">关闭</button></div>'+
      '<div class="adv-body">'+
      '  <div class="adv-col">'+
      '    <div class="adv-row">'+
      '      <label for="restart-args">参数</label>'+
      '      <input id="restart-args" class="adv-input" type="text" placeholder="例如: --no-tui --channel 6">'+
      '    </div>'+
      '    <div class="adv-row" id="hw-assistant-row">'+
      '      <label for="iface-select">硬件配置助手</label>'+
      '      <select id="iface-select" class="adv-input"><option value="">请选择默认网卡</option></select>'+
      '      <button class="btn-mini" id="btn-iface-refresh" type="button">刷新网卡</button>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label><input id="scan-wifi-fast" type="checkbox"> 扫描WiFi快传(5GHz常见信道)</label>'+
      '    </div>'+
      '    <div class="adv-note">新版固件解析显示偏好已保存到当前浏览器</div>'+
      '    <div class="adv-row">'+
      '      <label for="base-name">基站名称</label>'+
      '      <input id="base-name" class="adv-input" type="text" placeholder="例如: 基站A">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-lat">基站纬度</label>'+
      '      <input id="base-lat" class="adv-input" type="text" inputmode="decimal" placeholder="例如: 30.0678192">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-lon">基站经度</label>'+
      '      <input id="base-lon" class="adv-input" type="text" inputmode="decimal" placeholder="例如: 121.1854406">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="base-zoom">基站缩放</label>'+
      '      <input id="base-zoom" class="adv-input" type="number" min="3" max="30" step="1" placeholder="13">'+
      '      <button class="btn-mini" id="btn-base-save" type="button">保存基站</button>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="heading-ref">参考航向(°)</label>'+
      '      <input id="heading-ref" class="adv-input" type="number" min="0" max="359.99" step="0.1" placeholder="0">'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label for="map-idle-sec">自动回中冷却(s)</label>'+
      '      <input id="map-idle-sec" class="adv-input" type="number" min="5" max="600" step="1" placeholder="20">'+
      '    </div>'+
      '    <div class="adv-note" id="base-status">-</div>'+
      '    <div class="adv-note" id="iface-status">-</div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-save-iface-default" type="button">保存默认网卡</button>'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-restart-once" type="button">仅本次重启</button>'+
      '      <button class="btn-mini warn" id="btn-restart-save" type="button">保存并重启</button>'+
      '    </div>'+
      '    <div class="adv-note">DJI地址: <code id="dji-url-text">-</code></div>'+
      '    <div class="adv-note">当前参数: <code id="restart-current-args">-</code></div>'+
      '    <div class="adv-note">已保存参数: <code id="restart-saved-args">-</code></div>'+
      '  </div>'+
      '  <div class="adv-col">'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-config-load" type="button">读取配置</button>'+
      '      <button class="btn-mini" id="btn-config-save" type="button">保存并热重载</button>'+
      '    </div>'+
      '    <div class="adv-note" id="config-editor-status">-</div>'+
      '    <textarea id="config-editor" class="cfg-editor" spellcheck="false" placeholder="在这里编辑 config.json"></textarea>'+
      '    <div class="adv-row">'+
      '      <label for="track-sn-select">历史/轨迹</label>'+
      '      <select id="track-sn-select" class="adv-input"><option value="">请选择飞机</option></select>'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini warn" id="btn-history-delete" type="button">删除该飞机</button>'+
      '      <button class="btn-mini" id="btn-track-clear-one" type="button">清空该机轨迹</button>'+
      '      <button class="btn-mini warn" id="btn-track-clear-all" type="button">清空全部轨迹</button>'+
      '    </div>'+
      '    <div class="adv-note">TOOLS</div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-tools-export-all" type="button">导出全部详情</button>'+
      '      <button class="btn-mini" id="btn-tools-import-all" type="button">导入全部详情</button>'+
      '      <input id="tools-import-all-file" type="file" accept=".json,application/json" style="display:none">'+
      '    </div>'+
      '    <div class="adv-actions">'+
      '      <button class="btn-mini" id="btn-tools-export-track" type="button">导出单机轨迹</button>'+
      '      <button class="btn-mini" id="btn-tools-import-track" type="button">导入单机轨迹</button>'+
      '      <input id="tools-import-track-file" type="file" accept=".json,application/json" style="display:none">'+
      '    </div>'+
      '    <div class="adv-note" id="tools-status">-</div>'+
      '    <div class="adv-note" id="track-mgr-status">-</div>'+
      '  </div>'+
      '</div></div>';
    document.body.appendChild(modal);
    modal.addEventListener('click', function(ev){
      if(ev.target === modal) closeAdvModal();
    });
  }

  var bottom = document.querySelector('.bottom');
  if(bottom && !qs('aplist')){
    var panel = document.createElement('div');
    panel.className = 'panel ap-panel';
    panel.innerHTML =
      '<div class="panel-hdr">📋 实时AP列表 <span class="sub" id="ap-list-count">0</span></div>'+
      '<div class="aplist" id="aplist"></div>';
    bottom.appendChild(panel);
  }
  if(!qs('bottom-restore')){
    var restoreBtn = document.createElement('button');
    restoreBtn.className = 'btn-mini';
    restoreBtn.id = 'bottom-restore';
    restoreBtn.type = 'button';
    restoreBtn.textContent = '展开底部面板';
    restoreBtn.addEventListener('click', function(){
      setMapPanelCollapsed(false);
      setLogPanelCollapsed(false);
      setApPanelCollapsed(true);
      syncBottomPanelLayout();
    });
    document.body.appendChild(restoreBtn);
  }

  var mapEl = qs('map');
  if(mapEl){
    var mapPanel = mapEl.closest ? mapEl.closest('.panel') : null;
    if(mapPanel){
      mapPanel.id = 'map-panel';
      mapPanel.classList.add('map-panel', 'collapsible');
      var mapHdr = mapPanel.querySelector('.panel-hdr');
      if(mapHdr && !qs('map-panel-toggle')){
        var mapActions = document.createElement('div');
        mapActions.className = 'hdr-actions';
        var hint = mapHdr.querySelector('#map-hint');
        if(hint) mapActions.appendChild(hint);
        var fsBtn = document.createElement('button');
        fsBtn.className = 'btn-mini';
        fsBtn.id = 'btn-map-fullscreen';
        fsBtn.type = 'button';
        fsBtn.textContent = '全屏';
        fsBtn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleMapFullscreen(); });
        mapActions.appendChild(fsBtn);
        var mapBtn = document.createElement('button');
        mapBtn.className = 'btn-mini';
        mapBtn.id = 'map-panel-toggle';
        mapBtn.type = 'button';
        mapBtn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleMapPanel(); });
        mapActions.appendChild(mapBtn);
        mapHdr.appendChild(mapActions);
        mapHdr.style.cursor = 'pointer';
        mapHdr.addEventListener('click', function(ev){
          var t = ev.target;
          if(t && t.closest && t.closest('button')) return;
          toggleMapPanel();
        });
      }
      ensureMapMiniList();
      setMapPanelCollapsed(false);
    }
  }

  var logBox = qs('logbox');
  if(logBox){
    var logPanel = logBox.closest ? logBox.closest('.panel') : null;
    if(logPanel){
      logPanel.id = 'log-panel';
      logPanel.classList.add('log-panel', 'collapsible');
      var hdr = logPanel.querySelector('.panel-hdr');
      if(hdr && !qs('log-panel-toggle')){
        var actions = document.createElement('div');
        actions.className = 'hdr-actions';
        var label = hdr.querySelector('label');
        if(label) actions.appendChild(label);
        var btn = document.createElement('button');
        btn.className = 'btn-mini';
        btn.id = 'log-panel-toggle';
        btn.type = 'button';
        btn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleLogPanel(); });
        actions.appendChild(btn);
        hdr.appendChild(actions);
        hdr.style.cursor = 'pointer';
        hdr.addEventListener('click', function(ev){
          var t = ev.target;
          if(t && t.closest && t.closest('input,label,button')) return;
          toggleLogPanel();
        });
      }
      setLogPanelCollapsed(true);
    }
  }
  var apBox = qs('aplist');
  if(apBox){
    var apPanel = apBox.closest ? apBox.closest('.panel') : null;
    if(apPanel){
      apPanel.id = 'ap-panel';
      apPanel.classList.add('ap-panel', 'collapsible');
      var apHdr = apPanel.querySelector('.panel-hdr');
      if(apHdr && !qs('ap-panel-toggle')){
        var apActions = document.createElement('div');
        apActions.className = 'hdr-actions';
        var apBtn = document.createElement('button');
        apBtn.className = 'btn-mini';
        apBtn.id = 'ap-panel-toggle';
        apBtn.type = 'button';
        apBtn.addEventListener('click', function(ev){ ev.preventDefault(); ev.stopPropagation(); toggleApPanel(); });
        apActions.appendChild(apBtn);
        apHdr.appendChild(apActions);
        apHdr.style.cursor = 'pointer';
        apHdr.addEventListener('click', function(ev){
          var t = ev.target;
          if(t && t.closest && t.closest('button')) return;
          toggleApPanel();
        });
      }
      setApPanelCollapsed(false);
    }
  }
  syncBottomPanelLayout();

  if(qs('btn-clear-history')) qs('btn-clear-history').addEventListener('click', clearHistory);
  if(qs('btn-theme')) qs('btn-theme').style.display = 'none';
  if(qs('btn-dji-lookup')) qs('btn-dji-lookup').addEventListener('click', openDjiLookup);
  if(qs('btn-freeze')) qs('btn-freeze').addEventListener('click', toggleFreeze);
  if(qs('btn-web-notify')) qs('btn-web-notify').addEventListener('click', requestWebNotifyPermission);
  if(qs('btn-hw-assistant')) qs('btn-hw-assistant').addEventListener('click', openHardwareAssistant);
  if(qs('btn-adv-open')) qs('btn-adv-open').addEventListener('click', openAdvModal);
  if(qs('btn-adv-close')) qs('btn-adv-close').addEventListener('click', closeAdvModal);
  if(qs('btn-restart-once')) qs('btn-restart-once').addEventListener('click', function(){ restartProgram(false); });
  if(qs('btn-restart-save')) qs('btn-restart-save').addEventListener('click', function(){ restartProgram(true); });
  if(qs('btn-config-load')) qs('btn-config-load').addEventListener('click', loadConfigEditor);
  if(qs('btn-config-save')) qs('btn-config-save').addEventListener('click', saveConfigEditor);
  if(qs('btn-history-delete')) qs('btn-history-delete').addEventListener('click', deleteHistoryBySelect);
  if(qs('btn-track-clear-one')) qs('btn-track-clear-one').addEventListener('click', clearTrackBySelect);
  if(qs('btn-track-clear-all')) qs('btn-track-clear-all').addEventListener('click', clearTrackAll);
  if(qs('btn-tools-export-all')) qs('btn-tools-export-all').addEventListener('click', toolsExportAllDetails);
  if(qs('btn-tools-import-all')) qs('btn-tools-import-all').addEventListener('click', function(){ _pickImportFile('tools-import-all-file'); });
  if(qs('btn-tools-export-track')) qs('btn-tools-export-track').addEventListener('click', toolsExportSingleTrack);
  if(qs('btn-tools-import-track')) qs('btn-tools-import-track').addEventListener('click', function(){ _pickImportFile('tools-import-track-file'); });
  if(qs('tools-import-all-file')) qs('tools-import-all-file').addEventListener('change', function(ev){
    var f = (ev && ev.target && ev.target.files && ev.target.files[0]) ? ev.target.files[0] : null;
    if(f) toolsImportAllDetailsFromFile(f);
  });
  if(qs('tools-import-track-file')) qs('tools-import-track-file').addEventListener('change', function(ev){
    var f = (ev && ev.target && ev.target.files && ev.target.files[0]) ? ev.target.files[0] : null;
    if(f) toolsImportSingleTrackFromFile(f);
  });
  if(qs('btn-iface-refresh')) qs('btn-iface-refresh').addEventListener('click', function(){ loadIfaceOptions(true); });
  if(qs('btn-save-iface-default')) qs('btn-save-iface-default').addEventListener('click', saveDefaultIfaceConfig);
  if(qs('iface-select')) qs('iface-select').addEventListener('change', function(){ this.dataset.edited='1'; });
  if(qs('scan-wifi-fast')) qs('scan-wifi-fast').addEventListener('change', function(){ this.dataset.edited='1'; });
  if(qs('restart-args')) qs('restart-args').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-name')) qs('base-name').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-lat')) qs('base-lat').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-lon')) qs('base-lon').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('base-zoom')) qs('base-zoom').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('heading-ref')) qs('heading-ref').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('map-idle-sec')) qs('map-idle-sec').addEventListener('input', function(){ this.dataset.edited='1'; });
  if(qs('btn-base-save')) qs('btn-base-save').addEventListener('click', saveBaseConfig);
  if(qs('sel-all')) qs('sel-all').addEventListener('change', function(ev){ setAllVisibleSelected(!!(ev && ev.target && ev.target.checked)); });
  var tableHead = document.querySelector('#dtable thead');
  if(tableHead) tableHead.addEventListener('click', function(ev){
    var th = ev.target && ev.target.closest ? ev.target.closest('th.sortable[data-sort]') : null;
    if(!th) return;
    if(ev.target && ev.target.closest && ev.target.closest('input,button,label')) return;
    setTableSort(th.getAttribute('data-sort') || '');
  });
  if(qs('tbody')) qs('tbody').addEventListener('click', function(ev){
    var cb = ev.target && ev.target.closest ? ev.target.closest('.sel-sn') : null;
    if(cb){
      ev.stopPropagation();
      var snCb = cb.getAttribute('data-sn') || '';
      if(currentAppPage() === 'history') setHistorySnVisible(snCb, !!cb.checked);
      else setSnSelected(snCb, !!cb.checked);
      return;
    }
    var btn = ev.target && ev.target.closest ? ev.target.closest('.copy-sn') : null;
    if(btn){
      ev.stopPropagation();
      copySn(btn.getAttribute('data-sn') || '');
      return;
    }
    var tr = ev.target && ev.target.closest ? ev.target.closest('tr[data-sn]') : null;
    if(tr){
      var sn = tr.getAttribute('data-sn') || '';
      if(rowClickTimer){
        clearTimeout(rowClickTimer);
        rowClickTimer = null;
      }
      rowClickTimer = setTimeout(function(){
        rowClickTimer = null;
        if(currentAppPage() === 'history'){
          focusHistoryAircraft(sn);
          return;
        }
        var e = latestDroneMap[sn];
        if(e) showDroneInfoCard(e);
      }, 220);
    }
  });
  if(qs('tbody')) qs('tbody').addEventListener('dblclick', function(ev){
    var cb = ev.target && ev.target.closest ? ev.target.closest('.sel-sn') : null;
    if(cb) return;
    var btn = ev.target && ev.target.closest ? ev.target.closest('.copy-sn') : null;
    if(btn) return;
    var tr = ev.target && ev.target.closest ? ev.target.closest('tr[data-sn]') : null;
    if(!tr) return;
    var sn = tr.getAttribute('data-sn') || '';
    if(!sn) return;
    ev.preventDefault();
    ev.stopPropagation();
    if(rowClickTimer){
      clearTimeout(rowClickTimer);
      rowClickTimer = null;
    }
    setSnSelected(sn, true);
    hideInfoCard();
    if(typeof window.__ridNavSet === 'function'){
      window.__ridNavSet('history');
    }else{
      document.body.setAttribute('data-page', 'history');
      setTimeout(function(){ if(map) map.invalidateSize(false); }, 80);
    }
  });
  applyTheme(uiTheme);
  if(('Notification' in window) && Notification.permission === 'granted'){
    webNotifyEnabled = true;
  }
  updateNotifyButton();
  loadConfigEditor();
  loadIfaceOptions(false);
  syncTrackPrefsUi();
  setFreezeState(false);
  updateMapFullscreenButton();
  renderMapMiniList([]);
}

function applyMeta(meta){
  metaState = (meta && typeof meta === 'object') ? meta : {};
  var djiUrl = String(metaState.dji_lookup_url || '');
  var allowRestart = metaState.allow_restart !== false;
  if(qs('dji-url-text')) qs('dji-url-text').textContent = djiUrl || '-';
  if(qs('restart-current-args')) qs('restart-current-args').textContent = String(metaState.restart_args_current || '-');
  if(qs('restart-saved-args')) qs('restart-saved-args').textContent = String(metaState.restart_args_saved || '-');
  if(qs('btn-dji-lookup')) qs('btn-dji-lookup').disabled = !djiUrl;
  if(qs('btn-restart-once')) qs('btn-restart-once').disabled = restartBusy || !allowRestart;
  if(qs('btn-restart-save')) qs('btn-restart-save').disabled = restartBusy || !allowRestart;
  var input = qs('restart-args');
  if(input && !input.dataset.edited){
    var preset = String(metaState.restart_args_saved || metaState.restart_args_current || '');
    input.value = preset;
  }
  var ifaceSel = qs('iface-select');
  if(ifaceSel && !ifaceSel.dataset.edited){
    var ifaceVal = metaState.iface_selected;
    if(ifaceVal == null || ifaceVal === '') ifaceVal = '';
    ifaceSel.value = String(ifaceVal);
  }
  var scanFast = qs('scan-wifi-fast');
  if(scanFast && !scanFast.dataset.edited){
    scanFast.checked = !!metaState.scan_wifi_fast;
  }
  var baseNameInput = qs('base-name');
  if(baseNameInput && !baseNameInput.dataset.edited){
    baseNameInput.value = String(metaState.base_name || '基站');
  }
  var baseLatInput = qs('base-lat');
  if(baseLatInput && !baseLatInput.dataset.edited){
    baseLatInput.value = (metaState.base_lat==null) ? '' : String(metaState.base_lat);
  }
  var baseLonInput = qs('base-lon');
  if(baseLonInput && !baseLonInput.dataset.edited){
    baseLonInput.value = (metaState.base_lon==null) ? '' : String(metaState.base_lon);
  }
  var baseZoomInput = qs('base-zoom');
  if(baseZoomInput && !baseZoomInput.dataset.edited){
    var bz = intOrDefault(metaState.base_zoom, 13);
    baseZoomInput.value = String(Math.max(3, Math.min(30, bz)));
  }
  var headingRefInput = qs('heading-ref');
  if(headingRefInput && !headingRefInput.dataset.edited){
    var hr = Number(metaState.heading_ref_deg);
    if(!isFinite(hr)) hr = 0;
    headingRefInput.value = String(normDeg(hr).toFixed(1));
  }
  var mapIdleInput = qs('map-idle-sec');
  if(mapIdleInput && !mapIdleInput.dataset.edited){
    var mi = intOrDefault(metaState.map_auto_center_idle_sec, 20);
    mapIdleInput.value = String(Math.max(5, Math.min(600, mi)));
  }
  mapHeadingRefDeg = normDeg(metaState.heading_ref_deg);
  mapAutoCenterIdleSec = Math.max(5, Math.min(600, intOrDefault(metaState.map_auto_center_idle_sec, 20)));
  var baseCfg = baseFromMeta(metaState);
  var baseStatus = qs('base-status');
  if(baseStatus){
    if(baseCfg.ok){
      baseStatus.textContent = '基站: ' + baseCfg.name + ' (' + baseCfg.lat.toFixed(6) + ', ' + baseCfg.lon.toFixed(6) + ') z' + baseCfg.zoom + ' | 参考航向 ' + mapHeadingRefDeg.toFixed(1) + '° | 回中冷却 ' + mapAutoCenterIdleSec + 's';
    } else {
      baseStatus.textContent = '基站未配置 | 参考航向 ' + mapHeadingRefDeg.toFixed(1) + '° | 回中冷却 ' + mapAutoCenterIdleSec + 's';
    }
  }
  var newBaseSig = baseSignature(metaState);
  if(applyMeta.__baseSig !== newBaseSig){
    applyMeta.__baseSig = newBaseSig;
    if(map){
      map._rid_base_fitted = false;
      applyBaseMarker(false);
      if(baseCfg.ok){
        map.setView([baseCfg.lat, baseCfg.lon], baseCfg.zoom);
        map._rid_base_fitted = true;
      }
    }
  }
  var ifaceStatus = qs('iface-status');
  if(ifaceStatus){
    var activeIface = String(metaState.sniff_iface || '-');
    var extra = '';
    if(!!metaState.scan_wifi_fast){
      var supported = metaState.wifi_fast_supported;
      if(supported === false) extra = ' | 5GHz不支持';
      else if(supported === true) extra = ' | 5GHz可用';
      if(metaState.wifi_fast_msg) extra += ' | ' + String(metaState.wifi_fast_msg);
    }
    var statText = '当前采集网卡: ' + activeIface + extra;
    if((activeIface === '-' || activeIface === '') && String(metaState.sniff_state || '') !== 'ok'){
      statText += ' | 请打开“高级设置 - 硬件配置助手”检查网卡';
    }
    ifaceStatus.textContent = statText;
  }
  if(!!metaState.scan_wifi_fast && metaState.wifi_fast_supported === false){
    var warnMsg = String(metaState.wifi_fast_msg || '网卡不支持5GHz，WiFi快传扫描不可用');
    if(applyMeta.__fastWarn !== warnMsg){
      showBanner(warnMsg, 'warn', 4200);
      applyMeta.__fastWarn = warnMsg;
    }
  }
  applyRuntimeSecurity(metaState);
  updateNotifyButton();
  applySniffStatus(metaState);
}

function applyRuntimeSecurity(meta){
  var sec = (meta && meta.runtime_security) || {};
  var banner = qs('security-banner');
  if(!banner) return;
  if(sec.running_as_root){
    if(qs('security-banner-text')){
      qs('security-banner-text').textContent = '当前处于 root 权限，存在安全风险。请在设置中一键修复为 rid 专用账号运行。';
    }
    banner.className = 'sniff-banner warn security-banner';
    banner.style.display = 'flex';
    if(applyRuntimeSecurity.__last !== 'root'){
      showBanner('当前处于 root 权限，存在安全风险。', 'warn', 5200);
    }
    applyRuntimeSecurity.__last = 'root';
  }else{
    banner.style.display = 'none';
    applyRuntimeSecurity.__last = 'ok';
  }
}

function applySniffStatus(meta){
  var state = String((meta && meta.sniff_state) || 'warn');
  var msg = String((meta && meta.sniff_msg) || '');
  var iface = String((meta && meta.sniff_iface) || '');
  var idle = Number((meta && meta.sniff_idle_sec) || 0);
  var lastPkt = String((meta && meta.sniff_last_pkt) || '-');

  var badge = qs('sniff-state');
  if(badge){
    badge.classList.remove('ok','warn','err');
    if(state === 'ok'){
      badge.classList.add('ok');
      badge.textContent = '正常';
    } else if(state === 'error'){
      badge.classList.add('err');
      badge.textContent = '异常';
    } else {
      badge.classList.add('warn');
      badge.textContent = '警告';
    }
  }

  var banner = qs('sniff-banner');
  if(!banner) return;
  if(state === 'ok'){
    banner.style.display = 'none';
    banner.textContent = '';
    banner.className = 'sniff-banner';
    sniffBannerPrevState = state;
    return;
  }
  var tip = (state === 'error' ? '采集异常：' : '采集告警：') + (msg || '未知');
  if(iface) tip += ' [iface: '+iface+']';
  if(idle > 0) tip += ' (' + Math.round(idle) + 's)';
  if(lastPkt && lastPkt !== '-') tip += '  上次帧: ' + lastPkt;
  banner.textContent = tip;
  banner.className = 'sniff-banner ' + (state === 'error' ? 'error' : 'warn');
  banner.style.display = 'block';
  if(state !== sniffBannerPrevState){
    showBanner(tip, state === 'error' ? 'warn' : 'info', 4200);
    sniffBannerPrevState = state;
  }
}

function openHardwareAssistant(){
  var mobile = false;
  try { mobile = window.matchMedia('(max-width: 900px)').matches; } catch(_e) {}
  if(mobile){
    window.open('/hardware-assistant', '_blank', 'noopener,noreferrer');
  } else {
    window.open('/hardware-assistant', 'hardware_assistant_window', 'noopener,noreferrer,width=1120,height=860');
  }
}

function openDjiLookup(){
  var url = String(metaState.dji_lookup_url || '');
  if(!url){
    alert('未配置DJI查询地址');
    return;
  }
  var mobile = false;
  try { mobile = window.matchMedia('(max-width: 900px)').matches; } catch(_e) {}
  if(mobile){
    window.open(url, '_blank', 'noopener,noreferrer');
  } else {
    window.open(url, 'dji_lookup_window', 'noopener,noreferrer,width=1180,height=820');
  }
}

async function copyText(text){
  if(!text) return false;
  try{
    if(navigator.clipboard && navigator.clipboard.writeText){
      await navigator.clipboard.writeText(text);
      return true;
    }
  }catch(_e){}
  var ta = document.createElement('textarea');
  ta.value = text;
  ta.setAttribute('readonly', 'readonly');
  ta.style.position = 'fixed';
  ta.style.opacity = '0';
  document.body.appendChild(ta);
  ta.select();
  var ok = false;
  try{ ok = document.execCommand('copy'); }catch(_e){}
  document.body.removeChild(ta);
  return ok;
}

async function copySn(sn){
  if(!sn) return;
  var ok = await copyText(sn);
  var btn = null;
  if(window.CSS && CSS.escape){
    try{ btn = document.querySelector('.copy-sn[data-sn="'+CSS.escape(sn)+'"]'); }catch(_e){}
  }
  if(!btn){
    var all = document.querySelectorAll('.copy-sn');
    for(var i=0;i<all.length;i++){
      if((all[i].getAttribute('data-sn')||'') === sn){ btn = all[i]; break; }
    }
  }
  if(btn){
    var old = btn.textContent;
    btn.classList.add('done');
    btn.textContent = ok ? '已' : '!';
    setTimeout(function(){ btn.classList.remove('done'); btn.textContent = old; }, 1200);
  }
}

async function clearHistory(){
  if(clearHistoryBusy) return;
  if(!confirm('清空历史无人机记录，并删除本地缓存文件？')) return;
  var btn = qs('btn-clear-history');
  clearHistoryBusy = true;
  if(btn){ btn.disabled = true; btn.textContent = '清空中...'; }
  try{
    var data = await postJson('/api/history/clear', {});
    selectedSnSet = {};
    selectedMacSet = {};
    trackCache = {};
    trackFetchMeta = {};
    trackLineSig = {};
    showBanner('历史已清空' + (typeof data.cleared==='number' ? ('（'+data.cleared+'架）') : ''), 'ok', 2600);
  }catch(e){
    showBanner('清空失败: ' + ((e && e.message) ? e.message : e), 'warn', 4200);
  }finally{
    if(btn){ btn.disabled = false; btn.textContent = '清空历史'; }
    clearHistoryBusy = false;
  }
}

function removeHistorySnClientState(sn){
  sn = String(sn || '').trim();
  if(!sn) return;
  var e = latestDroneMap[sn] || null;
  var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
  delete selectedSnSet[sn];
  if(mac) delete selectedMacSet[mac];
  delete historyHiddenSnSet[sn];
  delete trackCache[sn];
  delete trackLoading[sn];
  delete trackFetchMeta[sn];
  delete trackLineSig[sn];
  if(latestDroneMap) delete latestDroneMap[sn];
  function keepOther(row){
    return String((row && row.sn) || '') !== sn;
  }
  latestDroneRows = (Array.isArray(latestDroneRows) ? latestDroneRows : []).filter(keepOther);
  latestMapRows = (Array.isArray(latestMapRows) ? latestMapRows : []).filter(keepOther);
  syncTableSelectionUi();
  renderLiveCards(latestDroneRows);
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  refreshReplayBounds(false);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}

async function deleteHistoryForSn(sn, opts){
  opts = opts || {};
  sn = String(sn || '').trim();
  if(!sn){
    if(opts.statusEl) opts.statusEl.textContent = '请先选择飞机';
    return false;
  }
  if(deleteHistorySnBusy[sn]) return false;
  if(opts.confirm !== false && !confirm('删除该飞机历史记录？\\n' + sn)) return false;
  var btn = opts.button || null;
  var oldText = btn ? btn.textContent : '';
  deleteHistorySnBusy[sn] = true;
  if(btn){
    btn.disabled = true;
    btn.textContent = '删除中...';
  }
  if(opts.statusEl) opts.statusEl.textContent = '删除中...';
  try{
    var data = await postJson('/api/history/delete', {sn: sn});
    removeHistorySnClientState(sn);
    if(opts.hideCard !== false) hideInfoCard();
    if(opts.statusEl) opts.statusEl.textContent = data.removed ? ('已删除: ' + sn) : ('未找到: ' + sn);
    showBanner(data.removed ? ('已删除历史: ' + sn) : ('未找到历史: ' + sn), data.removed ? 'ok' : 'info', 2600);
    return !!data.removed;
  }catch(e){
    if(opts.statusEl) opts.statusEl.textContent = '删除失败: ' + ((e && e.message) ? e.message : e);
    showBanner('删除历史失败: ' + ((e && e.message) ? e.message : e), 'warn', 4200);
    return false;
  }finally{
    if(btn){
      btn.disabled = false;
      btn.textContent = oldText || '删除历史';
    }
    delete deleteHistorySnBusy[sn];
  }
}

async function deleteHistoryBySelect(){
  var sel = qs('track-sn-select');
  var st = qs('track-mgr-status');
  var sn = sel ? String(sel.value || '').trim() : '';
  await deleteHistoryForSn(sn, {statusEl: st, hideCard: false});
}

async function clearTrackBySelect(){
  var sel = qs('track-sn-select');
  var st = qs('track-mgr-status');
  var sn = sel ? String(sel.value || '').trim() : '';
  if(!sn){
    if(st) st.textContent = '请先选择飞机';
    return;
  }
  if(!confirm('清空该飞机轨迹？\\n' + sn)) return;
  if(st) st.textContent = '清空中...';
  try{
    var data = await postJson('/api/tracks/clear', {sn: sn});
    trackCache[sn] = [];
    delete trackFetchMeta[sn];
    delete trackLineSig[sn];
    if(st) st.textContent = '已清空轨迹: ' + sn + '（影响' + Number(data.affected || 0) + '架）';
    showBanner('轨迹已清空: ' + sn, 'ok', 2400);
  }catch(e){
    if(st) st.textContent = '清空失败: ' + ((e && e.message) ? e.message : e);
    showBanner('清空轨迹失败', 'warn', 3200);
  }
}

async function clearTrackAll(){
  var st = qs('track-mgr-status');
  if(!confirm('清空所有飞机轨迹？')) return;
  if(st) st.textContent = '清空中...';
  try{
    var data = await postJson('/api/tracks/clear', {});
    trackCache = {};
    trackFetchMeta = {};
    trackLineSig = {};
    if(st) st.textContent = '已清空全部轨迹（影响' + Number(data.affected || 0) + '架）';
    showBanner('全部轨迹已清空', 'ok', 2600);
  }catch(e){
    if(st) st.textContent = '清空失败: ' + ((e && e.message) ? e.message : e);
    showBanner('清空全部轨迹失败', 'warn', 3200);
  }
}

async function restartProgram(saveCfg){
  if(restartBusy) return;
  var input = qs('restart-args');
  var argsText = input ? String(input.value || '').trim() : '';
  var ifaceSel = qs('iface-select');
  var iface = ifaceSel ? String(ifaceSel.value || '').trim() : '';
  var scanFast = !!(qs('scan-wifi-fast') && qs('scan-wifi-fast').checked);
  var tip = saveCfg ? '保存配置并重启程序？' : '按当前输入参数重启程序（仅本次）？';
  if(!confirm(tip)) return;
  restartBusy = true;
  applyMeta(metaState);
  try{
    await postJson('/api/admin/restart', {
      args: argsText,
      save: !!saveCfg,
      iface: iface,
      scan_wifi_fast: scanFast
    });
    showBanner(saveCfg ? '已提交：保存并重启' : '已提交：仅本次重启', 'ok', 2800);
  }catch(e){
    showBanner('重启失败: ' + ((e && e.message) ? e.message : e), 'warn', 4800);
  }finally{
    restartBusy = false;
    applyMeta(metaState);
  }
}

async function loadConfigEditor(){
  var ta = qs('config-editor');
  var st = qs('config-editor-status');
  if(!ta) return;
  if(st) st.textContent = '读取中...';
  try{
    var data = await getJson('/api/config');
    ta.value = String(data.text || '');
    if(st) st.textContent = '已读取: ' + String(data.path || '-');
  }catch(e){
    if(st) st.textContent = '读取失败: ' + ((e && e.message) ? e.message : e);
  }
}

async function saveConfigEditor(){
  var ta = qs('config-editor');
  var st = qs('config-editor-status');
  if(!ta) return;
  var text = String(ta.value || '');
  if(!text.trim()){
    if(st) st.textContent = '配置内容为空';
    return;
  }
  if(st) st.textContent = '保存中...';
  try{
    var data = await postJson('/api/config/save', {text: text});
    if(st){
      st.textContent = '保存成功: ' + String(data.saved_to || '-') + '，' +
        (data.reloaded ? '已热重载' : '未热重载');
    }
    showBanner('配置已保存', 'ok', 2400);
    loadIfaceOptions(true);
  }catch(e){
    if(st) st.textContent = '保存失败: ' + ((e && e.message) ? e.message : e);
    showBanner('配置保存失败', 'warn', 4200);
  }
}

async function saveBaseConfig(){
  var st = qs('base-status');
  var btn = qs('btn-base-save');
  var nameInput = qs('base-name');
  var latInput = qs('base-lat');
  var lonInput = qs('base-lon');
  var zoomInput = qs('base-zoom');
  var headingInput = qs('heading-ref');
  var idleInput = qs('map-idle-sec');
  var name = nameInput ? String(nameInput.value || '').trim() : '';
  var latRaw = latInput ? String(latInput.value || '').trim() : '';
  var lonRaw = lonInput ? String(lonInput.value || '').trim() : '';
  var zoomRaw = zoomInput ? String(zoomInput.value || '').trim() : '';
  var headingRaw = headingInput ? String(headingInput.value || '').trim() : '';
  var idleRaw = idleInput ? String(idleInput.value || '').trim() : '';
  if(!name) name = '基站';

  var lat = (latRaw === '') ? null : numOrNull(latRaw);
  var lon = (lonRaw === '') ? null : numOrNull(lonRaw);
  var zoom = intOrDefault(zoomRaw, 13);
  var headingRef = (headingRaw === '') ? 0 : numOrNull(headingRaw);
  var idleSec = intOrDefault(idleRaw, 20);
  zoom = Math.max(3, Math.min(30, zoom));
  idleSec = Math.max(5, Math.min(600, idleSec));
  if(headingRef == null || !isFinite(Number(headingRef))){
    if(st) st.textContent = '参考航向需为数字';
    return;
  }
  headingRef = normDeg(headingRef);

  if((lat === null) !== (lon === null)){
    if(st) st.textContent = '基站坐标需要同时填写经纬度';
    return;
  }
  if(lat !== null && (lat < -90 || lat > 90)){
    if(st) st.textContent = '纬度范围需在 -90 ~ 90';
    return;
  }
  if(lon !== null && (lon < -180 || lon > 180)){
    if(st) st.textContent = '经度范围需在 -180 ~ 180';
    return;
  }

  if(st) st.textContent = '保存中...';
  if(btn) btn.disabled = true;
  try{
    var data = await postJson('/api/web/base/save', {
      base_name: name,
      base_lat: lat,
      base_lon: lon,
      base_zoom: zoom,
      heading_ref_deg: headingRef,
      map_auto_center_idle_sec: idleSec
    });
    metaState = Object.assign({}, metaState, {
      base_name: data.base_name,
      base_lat: data.base_lat,
      base_lon: data.base_lon,
      base_zoom: data.base_zoom,
      heading_ref_deg: data.heading_ref_deg,
      map_auto_center_idle_sec: data.map_auto_center_idle_sec
    });
    if(nameInput){ delete nameInput.dataset.edited; }
    if(latInput){ delete latInput.dataset.edited; }
    if(lonInput){ delete lonInput.dataset.edited; }
    if(zoomInput){ delete zoomInput.dataset.edited; }
    if(headingInput){ delete headingInput.dataset.edited; }
    if(idleInput){ delete idleInput.dataset.edited; }
    applyMeta(metaState);
    applyBaseMarker(true);
    if(st){
      st.textContent = '基站已保存: ' + String(data.base_name || '基站');
    }
    showBanner('基站配置已保存', 'ok', 2200);
  }catch(e){
    if(st) st.textContent = '保存失败: ' + ((e && e.message) ? e.message : e);
    showBanner('基站保存失败', 'warn', 4200);
  }finally{
    if(btn) btn.disabled = false;
  }
}

async function saveDefaultIfaceConfig(){
  var st = qs('iface-status');
  var btn = qs('btn-save-iface-default');
  var ifaceSel = qs('iface-select');
  var iface = ifaceSel ? String(ifaceSel.value || '').trim() : '';
  var scanFast = !!(qs('scan-wifi-fast') && qs('scan-wifi-fast').checked);
  if(btn) btn.disabled = true;
  if(st) st.textContent = '保存默认网卡中...';
  try{
    var data = await postJson('/api/web/basic/save', {
      iface: iface,
      scan_wifi_fast: scanFast
    });
    metaState = Object.assign({}, metaState, {
      iface_selected: data.iface_selected,
      scan_wifi_fast: data.scan_wifi_fast
    });
    if(ifaceSel){ delete ifaceSel.dataset.edited; }
    var scanFastEl = qs('scan-wifi-fast');
    if(scanFastEl){ delete scanFastEl.dataset.edited; }
    applyMeta(metaState);
    if(st){
      st.textContent = '默认网卡已保存: ' + (data.iface_selected || '未设置') + '，WiFi快传=' + (data.scan_wifi_fast ? '开' : '关');
    }
    showBanner('默认网卡配置已保存', 'ok', 2200);
  }catch(e){
    if(st) st.textContent = '保存失败: ' + ((e && e.message) ? e.message : e);
    showBanner('默认网卡保存失败', 'warn', 3600);
  }finally{
    if(btn) btn.disabled = false;
  }
}

function renderAps(aps, total){
  var box = qs('aplist');
  if(!box) return;
  var rows = Array.isArray(aps) ? aps : [];
  latestApsRows = rows.slice();
  latestApsTotal = Number(total||0);
  var t = Number(total||0);
  if(qs('ap-list-count')){
    qs('ap-list-count').textContent = (t > rows.length) ? (rows.length + '/' + t) : String(rows.length);
  }
  if(!rows.length){
    box.innerHTML = '<div class="ap-empty">暂无AP数据</div>';
    return;
  }
  var wide = (Number(box.clientWidth || 0) >= 780);
  var narrow = (Number(box.clientWidth || 0) <= 520);
  box.classList.toggle('wide', wide);
  box.classList.toggle('narrow', narrow);
  rows.sort(function(a,b){
    var ar = (a && a.rssi != null) ? Number(a.rssi) : -9999;
    var br = (b && b.rssi != null) ? Number(b.rssi) : -9999;
    return br - ar;
  });
  var html = '';
  html += '<div class="aprow hd"><div class="idx">#</div><div>MAC</div><div>信号</div><div>类型</div><div>SSID</div><div>设备</div></div>';
  for(var i=0;i<rows.length;i++){
    var a = rows[i] || {};
    var rssi = (a.rssi==null) ? 'N/A' : (a.rssi+'dBm');
    var mac = String(a.mac || '');
    var ssid = String(a.ssid || '(hidden)');
    var vt = String(a.vendor_type || 'AP');
    var vn = String(a.vendor || '未知');
    if(vn === '加载中' && Number(a.age || 0) >= 10) vn = '未知';
    html += '<div class="aprow">'+
      '<div class="idx">'+(i+1)+'</div>'+
      '<div class="mono ap-mac" title="'+esc(mac)+'">'+esc(wide ? mac : shortMac(mac))+'</div>'+
      '<div>'+esc(rssi)+'</div>'+
      '<div>'+esc(vt)+'</div>'+
      '<div class="ssid-col"><div class="ssid" title="'+esc(ssid)+'">'+esc(ssid)+'</div></div>'+
      '<div class="vendor-col"><div class="vendor" title="'+esc(vn)+'">'+esc(vn)+'</div></div>'+
      '</div>';
  }
  box.innerHTML = html;
}

function renderLiveCards(list){
  var box = qs('live-card-list');
  if(!box) return;
  var rows = liveRecentRows(list).slice();
  rows.sort(function(a,b){
    var al = !!(a && a.lost), bl = !!(b && b.lost);
    if(al !== bl) return al ? 1 : -1;
    var ar = (a && a.rssi != null) ? Number(a.rssi) : -9999;
    var br = (b && b.rssi != null) ? Number(b.rssi) : -9999;
    return br - ar;
  });
  if(qs('live-card-count')) qs('live-card-count').textContent = String(rows.length);
  if(!rows.length){
    box.innerHTML = '<div class="ap-empty">暂无实时目标</div>';
    return;
  }
  var html = '';
  rows.forEach(function(e, idx){
    e = e || {};
    var sn = String(e.sn || '');
    var selected = isSnSelected(sn);
    var inAlarmZone = !!zoneAlarmSnSet[sn];
    var cls = 'live-card' + (selected ? ' selected' : '') + (e.lost ? ' lost' : '') + (inAlarmZone ? ' alarm-zone' : '');
    var rssi = e.rssi == null ? 'N/A' : (String(e.rssi) + 'dBm');
    var model = String(e.model || 'N/A');
    var latlon = (e.lat == null || e.lon == null) ? 'N/A' : (fmt(e.lat,6,'') + ', ' + fmt(e.lon,6,''));
    var pilot = coordText(e.pilot_lat, e.pilot_lon, 6);
    var homeAux = homeAuxCoordText(e);
    var alt = fmt(e.alt,1,'m');
    var spd = fmt(e.spd,2,'m/s');
    var heading = String(e.dir || '-');
    var stateCls = e.lost ? 'lost' : 'live';
    var stateTxt = e.lost ? '2分钟内离线' : '在线';
    var firmwareTxt = firmwareTypeText(e);
    var uas = uasIdText(e);
    html += '<article class="'+cls+'" data-sn="'+escAttr(sn)+'">'
      + '<div class="live-card-top">'
      +   '<div class="live-card-title" title="'+esc(model)+'">'+esc(model)+'</div>'
      +   '<div class="live-card-actions">'
      +     '<label class="live-card-pick"><input class="sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+(selected?' checked':'')+'><span>选中</span></label>'
      +     (inAlarmZone ? '<span class="live-card-state alarm">区域告警</span>' : '')
      +     '<span class="live-card-state firmware">'+esc(firmwareTxt)+'</span>'
      +     '<span class="live-card-state '+stateCls+'">'+esc(stateTxt)+'</span>'
      +   '</div>'
      + '</div>'
      + '<div class="live-card-snrow"><span class="label">SN</span><span class="live-card-sntext" title="'+esc(sn)+'">'+esc(sn || '-')+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+escAttr(sn)+'" title="复制 SN">⧉</button></div>'
      + '<div class="live-card-snrow live-card-uasrow"><span class="label">UAS ID</span><span class="live-card-sntext" title="'+esc(uas)+'">'+esc(uas)+'</span><span></span></div>'
      + '<div class="live-card-grid">'
      +   '<div class="live-card-item"><div class="k">经纬度</div><div class="v">'+esc(latlon)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">高度</div><div class="v">'+esc(alt)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">速度</div><div class="v">'+esc(spd)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">航向</div><div class="v">'+esc(heading)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">遥控站位置</div><div class="v">'+esc(pilot)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">Aux/Home</div><div class="v">'+esc(homeAux)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">信号 / 更新</div><div class="v">'+esc(rssi + ' / ' + String(e.age_text || fmtAge(e.age)))+'</div></div>'
      + '</div>'
      + '<div class="live-card-foot"><span>最后数据包 '+esc(String(e.last_pkt_time || e.capture_time || '-'))+'</span><span>#'+(idx+1)+'</span></div>'
      + '</article>';
  });
  box.innerHTML = html;
}

function loadTableSortState(){
  try{
    var raw = localStorage.getItem(TABLE_SORT_STORAGE_KEY);
    if(!raw) return;
    var data = JSON.parse(raw);
    if(!data || typeof data !== 'object') return;
    var field = String(data.field || '');
    var dir = String(data.dir || 'desc') === 'asc' ? 'asc' : 'desc';
    if(field) tableSortState = {field:field, dir:dir};
  }catch(_e){}
}
function saveTableSortState(){
  try{
    localStorage.setItem(TABLE_SORT_STORAGE_KEY, JSON.stringify(tableSortState || {field:'', dir:'desc'}));
  }catch(_e){}
}
function sortValueNumber(v, fallback){
  var n = Number(v);
  return Number.isFinite(n) ? n : fallback;
}
function sortValueText(v){
  var s = String(v == null ? '' : v).trim();
  return s.toUpperCase();
}
function compareMaybeNumericText(a, b){
  var an = Number(a), bn = Number(b);
  var aNum = Number.isFinite(an), bNum = Number.isFinite(bn);
  if(aNum && bNum){
    if(an < bn) return -1;
    if(an > bn) return 1;
    return 0;
  }
  return sortValueText(a).localeCompare(sortValueText(b), 'zh-Hans-CN', {numeric:true, sensitivity:'base'});
}
function tableSortComparator(field, left, right){
  left = left || {};
  right = right || {};
  if(field === 'index') return 0;
  if(field === 'sn') return sortValueText(left.sn).localeCompare(sortValueText(right.sn), 'zh-Hans-CN', {numeric:true, sensitivity:'base'});
  if(field === 'model') return sortValueText(left.model || 'N/A').localeCompare(sortValueText(right.model || 'N/A'), 'zh-Hans-CN', {numeric:true, sensitivity:'base'});
  if(field === 'rssi') return sortValueNumber(left.rssi, -99999) - sortValueNumber(right.rssi, -99999);
  if(field === 'pkts') return sortValueNumber(left.pkts, -1) - sortValueNumber(right.pkts, -1);
  if(field === 'dir') return compareMaybeNumericText(left.dir || '', right.dir || '');
  if(field === 'age') return sortValueNumber(left.age, Number.MAX_SAFE_INTEGER) - sortValueNumber(right.age, Number.MAX_SAFE_INTEGER);
  if(field === 'last_seen') return sortValueText(left.last_seen).localeCompare(sortValueText(right.last_seen), 'zh-Hans-CN', {numeric:true, sensitivity:'base'});
  if(field === 'uas_id') return sortValueText(uasIdText(left)).localeCompare(sortValueText(uasIdText(right)), 'zh-Hans-CN', {numeric:true, sensitivity:'base'});
  return 0;
}
function sortedDroneRows(list){
  list = Array.isArray(list) ? list.slice() : [];
  var field = String((tableSortState && tableSortState.field) || '');
  if(!field) return list;
  var dirMul = (tableSortState && tableSortState.dir) === 'asc' ? 1 : -1;
  return list
    .map(function(item, idx){ return {item:item || {}, idx:idx}; })
    .sort(function(a, b){
      var cmp = tableSortComparator(field, a.item, b.item);
      if(cmp === 0) cmp = a.idx - b.idx;
      return cmp * dirMul;
    })
    .map(function(entry){ return entry.item; });
}
function applyTableSortUi(){
  var heads = document.querySelectorAll ? document.querySelectorAll('#dtable thead th.sortable[data-sort]') : [];
  for(var i=0;i<heads.length;i++){
    var th = heads[i];
    var field = String(th.getAttribute('data-sort') || '');
    th.classList.remove('sorted-asc', 'sorted-desc');
    if(field && tableSortState && field === tableSortState.field){
      th.classList.add(tableSortState.dir === 'asc' ? 'sorted-asc' : 'sorted-desc');
    }
  }
}
function setTableSort(field){
  field = String(field || '');
  if(!field) return;
  if(tableSortState.field === field){
    tableSortState.dir = tableSortState.dir === 'asc' ? 'desc' : 'asc';
  }else{
    tableSortState = {
      field: field,
      dir: field === 'sn' || field === 'model' || field === 'uas_id' || field === 'last_seen' ? 'asc' : 'desc'
    };
  }
  saveTableSortState();
  applyTableSortUi();
  renderDroneTable(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}

function renderDroneTable(list){
  var displayList = sortedDroneRows(list);
  var rows='';
  var page = currentAppPage();
  list = Array.isArray(list) ? list : [];
  var live = list.filter(function(x){ return x && !x.lost; }).length;
  if(qs('n-total')) qs('n-total').textContent = String(list.length);
  if(qs('n-live')) qs('n-live').textContent = String(live);
  if(qs('n-lost')) qs('n-lost').textContent = String(list.length - live);
  if(!displayList.length){
    rows='<tr><td colspan="10" class="empty">暂无数据</td></tr>';
  } else {
    displayList.forEach(function(e, idx){
      e = e || {};
      var sn = String(e.sn || '');
      if(sn) latestDroneMap[sn] = e;
      var selected = (page === 'history') ? isHistoryTrackVisible(sn) : isSnSelected(sn);
      var snSrc = snSourceText(e);
      var scanType = scanTypeText(e);
      var firmwareType = firmwareTypeText(e);
      var firmwareKey = firmwareTypeKey(e);
      var uas = uasIdText(e);
      var cls = e.lost ? 'lost' : (sn.indexOf('MAC:')===0 ? 'mac' : 'live');
      if(selected) cls += ' selected';
      if(zoneAlarmSnSet[sn]) cls += ' alarm-zone';
      var snMeta = '<span class="sn-badge">'+esc(snSrc)+'</span><span class="sn-badge">'+esc(scanType)+'</span><span class="sn-badge firmware-'+escAttr(firmwareKey)+'">'+esc(firmwareType)+'</span>'+(zoneAlarmSnSet[sn] ? '<span class="sn-badge alarm">报警</span>' : '');
      var modelCls = fieldCellAttrs(sn, 'model', '');
      var rssiCls = fieldCellAttrs(sn, 'rssi', '');
      var pktCls = fieldCellAttrs(sn, 'pkts', '');
      var dirCls = fieldCellAttrs(sn, 'dir', '');
      var ageCls = fieldCellAttrs(sn, 'age_text', 'mono');
      var lastSeenCls = fieldCellAttrs(sn, 'last_seen', 'mono');
      var uasCls = fieldCellAttrs(sn, 'uas_id', 'mono');
      var checked = selected ? ' checked' : '';
      var chip = '<span class="track-color-chip" style="--track-color:'+escAttr(trackColorForSn(sn))+';'+(selected ? '' : 'display:none')+'" title="轨迹颜色"></span>';
      rows += '<tr class="'+cls+' data-row" data-sn="'+escAttr(sn)+'">'+
        '<td><div class="sel-wrap track-sel-wrap"><input class="sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+checked+'>'+chip+'</div></td>'+
        '<td class="idx-cell">'+(idx+1)+'</td>'+
        '<td><div class="sn-cell">'+snMeta+'<span class="mono">'+esc(sn)+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+escAttr(sn)+'" title="复制SN">⧉</button></div></td>'+
        '<td'+modelCls+'>'+esc(e.model || 'N/A')+'</td>'+
        '<td'+rssiCls+'>'+fmt(e.rssi,0,'dBm')+'</td>'+
        '<td'+pktCls+'>'+esc(e.pkts==null?'0':e.pkts)+'</td>'+
        '<td'+dirCls+'>'+esc(e.dir || '-')+'</td>'+
        '<td'+ageCls+'>'+esc(e.age_text || fmtAge(e.age))+'</td>'+
        '<td'+lastSeenCls+'>'+esc(e.last_seen || '-')+'</td>'+
        '<td'+uasCls+'>'+esc(uas)+'</td>'+
        '</tr>';
    });
  }
  qs('tbody').innerHTML = rows;
  applyTableSortUi();
  syncTableSelectionUi();
  renderLiveCards(list);
  renderMapMiniList(list);
  refreshTrackMgrOptions(list);
  refreshActiveInfoCard(list);
}

function connect(){
  var wsProto = (location.protocol === 'https:') ? 'wss://' : 'ws://';
  ws = new WebSocket(wsProto + location.host + '/ws');
  ws.onopen  = function(){ setWsState(true); };
  ws.onclose = function(){ setWsState(false); reconnTimer=setTimeout(connect,2000); };
  ws.onerror = function(){ ws.close(); };
  ws.onmessage = function(ev){
    var d = JSON.parse(ev.data);
    if(uiFrozen || replaySyncPaused){
      frozenPendingData = d;
      renderReplayCard();
      return;
    }
    onData(d);
  };
}
function setWsState(ok){
  qs('dot-ws').className = ok ? 'on' : '';
  qs('ws-status').textContent = replaySyncPaused ? '重演中' : (ok ? '实时' : '重连中');
}

function onData(d){
  clearInitialDataLoading();
  buildExtraUi();
  applyMeta((d && d.meta) || {});
  qs('cur-ts').textContent = d.ts;
  if(qs('cur-ch')) qs('cur-ch').textContent = d.ch;
  var list = (Array.isArray(d.drones) ? d.drones : []).filter(includeDroneByFirmware);
  var live = list.filter(function(x){ return x && !x.lost; }).length;
  if(qs('n-total')) qs('n-total').textContent = String(list.length);
  qs('n-live').textContent = live;
  if(qs('n-lost')) qs('n-lost').textContent = list.length - live;
  syncFieldHighlights(list);
  handleDroneNotifications(list);
  latestDroneMap = {};
  latestDroneRows = list.slice();
  applyHistoryDefaultSelection(latestDroneRows);
  syncSelectedFromRows(latestDroneRows);
  displayTrackSnList(currentAppPage(), latestDroneRows).forEach(function(sn){ ensureTrackLoaded(sn, false); });

  renderDroneTable(list);
  ensureHighlightAnimation();

  var box = qs('logbox');
  var autoEl = qs('autoscroll');
  var auto = !autoEl || autoEl.checked;
  var logs = Array.isArray(d.logs) ? d.logs : [];
  if(box && (lastLogsSeq !== d.logs_seq || box.childElementCount !== logs.length)){
    box.innerHTML='';
    var frag=document.createDocumentFragment();
    for(var i=0;i<logs.length;i++){
      var line = String(logs[i] || '');
      var dv=document.createElement('div');
      var isRid=line.includes('RID-')||/1581[A-Z0-9]{4}/.test(line);
      dv.className='ap'+(isRid?' rid':'');
      dv.textContent=line;
      frag.appendChild(dv);
    }
    box.appendChild(frag);
    lastLogsSeq = d.logs_seq;
  }
  if(box && auto) box.scrollTop=box.scrollHeight;

  if(lastApsSeq !== d.aps_seq){
    renderAps(d.aps || [], d.aps_total || 0);
    lastApsSeq = d.aps_seq;
  }

  latestMapRows = Array.isArray(d.map_drones) ? d.map_drones : (Array.isArray(d.drones) ? d.drones : []);
  displayTrackSnList(currentAppPage(), latestDroneRows).forEach(function(sn){
    var e = latestDroneMap[sn];
    if(e){
      var tm = trackFetchMeta[sn] || {};
      var cachedTotal = Number(tm.total || (trackCache[sn] || []).length || 0);
      if(Number(e.track_count || 0) === cachedTotal) return;
      if(currentAppPage() === 'history' || (Date.now() - Number(tm.ts || 0)) >= TRACK_FORCE_RELOAD_MS){
        ensureTrackLoaded(sn, true);
      }
    }
  });
  initMap();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}

loadTrackPrefs();
loadTableSortState();
consumeFreezeOnHomeRequest();
applyTheme(loadThemePref());
buildExtraUi();
applyTableSortUi();
showInitialDataLoading('本机基站', '正在读取数据');
connect();

var map = null, markers = {}, pilotMarkers = {}, trackLines = {}, trackLineSig = {}, twsLines = {}, baseMarker = null;
var motionState = {};
var COLORS = ['#58a6ff','#3fb950','#d29922','#d2a8ff','#79c0ff','#ff7b72'];
var TRACK_COLORS = ['#1f9dff','#12b886','#ff8f1f','#ff4d6d','#8b5cf6','#06b6d4','#84cc16','#eab308'];
var colorIdx = {};
var LIVE_RECENT_WINDOW_SEC = 300;
window.addEventListener('resize', function(){
  applyInfoCardDragPosition();
  if(map) map.invalidateSize(false);
  if(latestApsRows.length){
    renderAps(latestApsRows, latestApsTotal);
  }
});
function currentAppPage(){
  var p = String(document.body.getAttribute('data-page') || 'live');
  return p === 'history' ? 'history' : 'live';
}
function liveRecentRows(rows){
  return (Array.isArray(rows) ? rows : []).filter(function(e){
    if(!e || e.archived) return false;
    var age = Number(e.age || 0);
    if(!isFinite(age) || age < 0) age = 0;
    if(e.lost) return age <= LIVE_LOST_WINDOW_SEC;
    return age <= LIVE_RECENT_WINDOW_SEC;
  });
}

function _gcjOutOfChina(lat, lon){
  return (lon < 72.004 || lon > 137.8347 || lat < 0.8293 || lat > 55.8271);
}
function _gcjTransformLat(x, y){
  var ret = -100.0 + 2.0*x + 3.0*y + 0.2*y*y + 0.1*x*y + 0.2*Math.sqrt(Math.abs(x));
  ret += (20.0*Math.sin(6.0*x*Math.PI) + 20.0*Math.sin(2.0*x*Math.PI)) * 2.0 / 3.0;
  ret += (20.0*Math.sin(y*Math.PI) + 40.0*Math.sin(y/3.0*Math.PI)) * 2.0 / 3.0;
  ret += (160.0*Math.sin(y/12.0*Math.PI) + 320*Math.sin(y*Math.PI/30.0)) * 2.0 / 3.0;
  return ret;
}
function _gcjTransformLon(x, y){
  var ret = 300.0 + x + 2.0*y + 0.1*x*x + 0.1*x*y + 0.1*Math.sqrt(Math.abs(x));
  ret += (20.0*Math.sin(6.0*x*Math.PI) + 20.0*Math.sin(2.0*x*Math.PI)) * 2.0 / 3.0;
  ret += (20.0*Math.sin(x*Math.PI) + 40.0*Math.sin(x/3.0*Math.PI)) * 2.0 / 3.0;
  ret += (150.0*Math.sin(x/12.0*Math.PI) + 300.0*Math.sin(x/30.0*Math.PI)) * 2.0 / 3.0;
  return ret;
}
function wgs84ToGcj02(lat, lon){
  lat = Number(lat);
  lon = Number(lon);
  if(!isFinite(lat) || !isFinite(lon)) return [lat, lon];
  if(_gcjOutOfChina(lat, lon)) return [lat, lon];
  var a = 6378245.0;
  var ee = 0.00669342162296594323;
  var dLat = _gcjTransformLat(lon - 105.0, lat - 35.0);
  var dLon = _gcjTransformLon(lon - 105.0, lat - 35.0);
  var radLat = lat / 180.0 * Math.PI;
  var magic = Math.sin(radLat);
  magic = 1 - ee * magic * magic;
  var sqrtMagic = Math.sqrt(magic);
  dLat = (dLat * 180.0) / ((a * (1 - ee)) / (magic * sqrtMagic) * Math.PI);
  dLon = (dLon * 180.0) / (a / sqrtMagic * Math.cos(radLat) * Math.PI);
  var mgLat = lat + dLat;
  var mgLon = lon + dLon;
  return [mgLat, mgLon];
}
function toMapLatLng(lat, lon){
  return wgs84ToGcj02(lat, lon);
}
function validMapCoord(lat, lon){
  lat = numOrNull(lat);
  lon = numOrNull(lon);
  if(lat == null || lon == null) return false;
  if(lat < -90 || lat > 90 || lon < -180 || lon > 180) return false;
  if(Math.abs(lat) < 0.000001 && Math.abs(lon) < 0.000001) return false;
  return true;
}
function safeMapLatLng(lat, lon){
  if(!validMapCoord(lat, lon)) return null;
  return toMapLatLng(Number(lat), Number(lon));
}
function mapLatLngsNeedFit(latlngs, marginPx){
  if(!map || !Array.isArray(latlngs) || !latlngs.length) return false;
  if(!map.getBounds || !map.latLngToContainerPoint || !map.getSize) return true;
  try{
    var b = map.getBounds();
    var size = map.getSize();
    var margin = Math.max(12, Number(marginPx || 26));
    for(var i=0;i<latlngs.length;i++){
      var ll = latlngs[i];
      if(!b.contains(ll)) return true;
      var p = map.latLngToContainerPoint(ll);
      if(p.x < margin || p.y < margin || p.x > size.x - margin || p.y > size.y - margin) return true;
    }
    return false;
  }catch(_e){
    return true;
  }
}
function fitMapDisplayLatLngs(latlngs, singleZoom, padRatio, marginPx){
  if(!map || !Array.isArray(latlngs) || !latlngs.length) return false;
  if(map._rid_fitted && !map._rid_user_moved && !mapLatLngsNeedFit(latlngs, marginPx)) return false;
  try{
    if(latlngs.length === 1){
      map.setView(latlngs[0], singleZoom || 14);
    }else{
      map.fitBounds(L.latLngBounds(latlngs).pad(padRatio == null ? 0.16 : padRatio), {padding:[24,24]});
    }
    map._rid_fitted = true;
    map._rid_base_fitted = false;
    map._rid_user_moved = false;
    return true;
  }catch(_e){
    return false;
  }
}
function focusEntryOnMap(e, zoom){
  if(!map || !e) return;
  var lat = Number(e.lat), lon = Number(e.lon);
  var pos = safeMapLatLng(lat, lon);
  if(!pos) return;
  var nextZoom = Math.max(Number(zoom || 16), Number(map.getZoom ? map.getZoom() : 0) || 0);
  markMapUserInteracted();
  try{
    if(map.flyTo) map.flyTo(pos, nextZoom, {animate:true, duration:0.35});
    else map.setView(pos, nextZoom);
  }catch(_e){
    try{ map.setView(pos, nextZoom); }catch(_e2){}
  }
}
function focusLiveAircraft(sn){
  sn = String(sn || '');
  if(!sn) return;
  setSnSelected(sn, true, {exclusive:true});
  var e = latestDroneMap[sn];
  if(e){
    showDroneInfoCard(e);
    focusEntryOnMap(e, 16);
  }
}
function focusHistoryAircraft(sn){
  sn = String(sn || '');
  if(!sn) return;
  setHistoryVisibleSet([sn], {keepReplay:false});
  var e = latestDroneMap[sn];
  if(e){
    showDroneInfoCard(e);
    focusEntryOnMap(e, 16);
  }
}

function _deg2rad(d){ return d * Math.PI / 180; }
function calcDistanceMeters(lat1, lon1, lat2, lon2){
  var p1 = _deg2rad(lat1), p2 = _deg2rad(lat2);
  var dLat = p2 - p1;
  var dLon = _deg2rad(lon2 - lon1);
  var sa = Math.sin(dLat / 2.0);
  var sb = Math.sin(dLon / 2.0);
  var a = sa * sa + Math.cos(p1) * Math.cos(p2) * sb * sb;
  var c = 2.0 * Math.atan2(Math.sqrt(a), Math.sqrt(Math.max(0, 1.0 - a)));
  return 6371000.0 * c;
}
function calcBearing(lat1, lon1, lat2, lon2){
  var p1 = _deg2rad(lat1), p2 = _deg2rad(lat2);
  var dLon = _deg2rad(lon2 - lon1);
  var y = Math.sin(dLon) * Math.cos(p2);
  var x = Math.cos(p1) * Math.sin(p2) - Math.sin(p1) * Math.cos(p2) * Math.cos(dLon);
  var b = Math.atan2(y, x) * 180 / Math.PI;
  if(!isFinite(b)) return null;
  if(b < 0) b += 360;
  return b;
}
function calcHeadingByLatLon(prevLat, prevLon, curLat, curLon, minMoveMeters){
  var dist = calcDistanceMeters(prevLat, prevLon, curLat, curLon);
  var mm = Number(minMoveMeters);
  if(!isFinite(mm) || mm < 0.1) mm = 2.0;
  if(!isFinite(dist) || dist < mm){
    return {ok:false, heading:null, dist:isFinite(dist)?dist:0};
  }
  var b = calcBearing(prevLat, prevLon, curLat, curLon);
  if(!isFinite(Number(b))){
    return {ok:false, heading:null, dist:dist};
  }
  return {ok:true, heading:normDeg(b), dist:dist};
}
function destinationPoint(lat, lon, bearingDeg, distMeter){
  var R = 6371000.0;
  var br = _deg2rad(bearingDeg);
  var lat1 = _deg2rad(lat), lon1 = _deg2rad(lon);
  var ad = distMeter / R;
  var sinLat1 = Math.sin(lat1), cosLat1 = Math.cos(lat1);
  var sinAd = Math.sin(ad), cosAd = Math.cos(ad);
  var lat2 = Math.asin(sinLat1 * cosAd + cosLat1 * sinAd * Math.cos(br));
  var lon2 = lon1 + Math.atan2(Math.sin(br) * sinAd * cosLat1, cosAd - sinLat1 * Math.sin(lat2));
  return {lat:lat2 * 180/Math.PI, lon:lon2 * 180/Math.PI};
}
function interpLatLng(a, b, t){
  return [
    Number(a[0]) + (Number(b[0]) - Number(a[0])) * t,
    Number(a[1]) + (Number(b[1]) - Number(a[1])) * t
  ];
}
function splitLatLngsByMeters(latlngs, meters){
  var pts = Array.isArray(latlngs) ? latlngs : [];
  var target = Math.max(10, Number(meters || 100));
  if(pts.length < 2) return [];
  var out = [];
  var cur = [pts[0]];
  var prev = pts[0];
  var inSeg = 0;
  for(var i=1;i<pts.length;i++){
    var next = pts[i];
    var remaining = calcDistanceMeters(Number(prev[0]), Number(prev[1]), Number(next[0]), Number(next[1]));
    if(!isFinite(remaining) || remaining <= 0){
      continue;
    }
    while(inSeg + remaining >= target){
      var need = target - inSeg;
      if(need <= 0.001){
        if(cur.length > 1) out.push(cur);
        cur = [prev];
        inSeg = 0;
        continue;
      }
      var frac = Math.max(0, Math.min(1, need / remaining));
      var cut = interpLatLng(prev, next, frac);
      cur.push(cut);
      if(cur.length > 1) out.push(cur);
      cur = [cut];
      prev = cut;
      remaining = calcDistanceMeters(Number(prev[0]), Number(prev[1]), Number(next[0]), Number(next[1]));
      inSeg = 0;
      if(!isFinite(remaining) || remaining <= 0) break;
    }
    cur.push(next);
    inSeg += remaining;
    prev = next;
  }
  if(cur.length > 1) out.push(cur);
  return out;
}
function makeTrackLayer(latlngs, color){
  return L.polyline(latlngs, {
    color: color,
    weight: 4,
    opacity: 0.9,
    lineCap: 'round',
    lineJoin: 'round',
    smoothFactor: 1
  });
}
function dropTrackLayer(sn){
  sn = String(sn || '');
  if(!sn) return;
  delete trackRenderQueue[sn];
  if(trackLines[sn]){
    try{ map.removeLayer(trackLines[sn]); }catch(_e){}
    delete trackLines[sn];
  }
  delete trackLineSig[sn];
}
function queueTrackLayerRender(sn, latlngs, color, sig){
  sn = String(sn || '');
  if(!sn || !Array.isArray(latlngs) || latlngs.length < 2) return;
  trackRenderQueue[sn] = {sn:sn, latlngs:latlngs, color:color, sig:String(sig || '')};
  if(trackRenderScheduled) return;
  trackRenderScheduled = true;
  requestAnimationFrame(flushTrackLayerRenderQueue);
}
function flushTrackLayerRenderQueue(){
  trackRenderScheduled = false;
  if(!map){
    trackRenderQueue = {};
    return;
  }
  var nowFn = (window.performance && typeof window.performance.now === 'function')
    ? function(){ return window.performance.now(); }
    : function(){ return Date.now(); };
  var deadline = nowFn() + 10;
  while(true){
    var keys = Object.keys(trackRenderQueue);
    if(!keys.length) break;
    var sn = keys[0];
    var task = trackRenderQueue[sn];
    delete trackRenderQueue[sn];
    if(!task) continue;
    if(trackLines[sn] && trackLineSig[sn] === task.sig) continue;
    if(trackLines[sn]){
      try{ map.removeLayer(trackLines[sn]); }catch(_e){}
      delete trackLines[sn];
    }
    trackLines[sn] = makeTrackLayer(task.latlngs, task.color).addTo(map);
    trackLineSig[sn] = task.sig;
    if(nowFn() >= deadline) break;
  }
  if(Object.keys(trackRenderQueue).length){
    trackRenderScheduled = true;
    requestAnimationFrame(flushTrackLayerRenderQueue);
  }
}

function initMap(){
  if(map) return;
  map = L.map('map', {zoomControl:true, attributionControl:true, maxZoom:30});
  var offlineLayer = null;
  function ensureOfflineLayer(){
    if(offlineLayer){
      if(!map.hasLayer(offlineLayer)) offlineLayer.addTo(map);
      return;
    }
    var OfflineGrid = L.GridLayer.extend({
      createTile: function(coords){
        var tile = L.DomUtil.create('div', 'offline-map-tile');
        tile.innerHTML = '<span class="offline-map-badge">离线地图</span>';
        return tile;
      }
    });
    offlineLayer = new OfflineGrid({tileSize:256, maxZoom:30, attribution:'本地离线底图'});
    offlineLayer.addTo(map);
    showBanner('当前客户端无法加载在线底图，已切换为本地离线地图。飞机、轨迹和报警区域仍可显示。', 'warn', 5200, {persist:false});
  }
  var onlineLayer = L.tileLayer('https://webrd0{s}.is.autonavi.com/appmaptile?lang=zh_cn&size=1&scale=1&style=8&x={x}&y={y}&z={z}',{
    subdomains:['1','2','3','4'],
    maxZoom:30,
    maxNativeZoom:18,
    attribution:'&copy; 高德地图'
  });
  var tileErrors = 0;
  onlineLayer.on('tileerror', function(){
    tileErrors += 1;
    if(tileErrors >= 2) ensureOfflineLayer();
  });
  onlineLayer.addTo(map);
  var b = baseFromMeta(metaState);
  if(b.ok) map.setView([b.lat, b.lon], b.zoom);
  else map.setView([30, 114], 5);
  map._rid_user_moved = false;
  var mapEl = map.getContainer ? map.getContainer() : null;
  if(mapEl){
    mapEl.addEventListener('wheel', markMapUserInteracted, {passive:true});
    mapEl.addEventListener('pointerdown', markMapUserInteracted, {passive:true});
    mapEl.addEventListener('touchstart', markMapUserInteracted, {passive:true});
  }
  applyBaseMarker(false);
  setTimeout(function(){ if(map) map.invalidateSize(false); }, 0);
}

function baseIcon(){
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="48" height="48" viewBox="0 0 24 24">'
    +'<circle cx="12" cy="12" r="10.6" fill="#2f81f7" fill-opacity="0.92" stroke="#fff" stroke-width="1.1"/>'
    +'<path d="M12 6.3v10.2M9.4 17.1h5.2M10.2 10.8L12 9l1.8 1.8M9.8 8.5c.9-.92 2.05-1.38 3.2-1.38 1.15 0 2.3.46 3.2 1.38M8.3 7c1.32-1.34 3.03-2.01 4.74-2.01 1.71 0 3.42.67 4.74 2.01" stroke="#fff" stroke-linecap="round" stroke-linejoin="round" stroke-width="1.35" fill="none"/>'
    +'<path d="M10.8 16.6l-1.15 2.3M13.2 16.6l1.15 2.3" stroke="#fff" stroke-linecap="round" stroke-width="1.2"/>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[48,48], iconAnchor:[24,24], popupAnchor:[0,-22]
  });
}

function applyBaseMarker(forceCenter){
  if(!map) return;
  var b = baseFromMeta(metaState);
  if(!b.ok){
    if(baseMarker){
      map.removeLayer(baseMarker);
      baseMarker = null;
    }
    return;
  }
  var popup = '<b>' + esc(b.name) + '</b><br>' + b.lat.toFixed(6) + ', ' + b.lon.toFixed(6) + '<br>z=' + b.zoom;
  var mapPos = [b.lat, b.lon];
  if(baseMarker){
    baseMarker.setLatLng(mapPos).setPopupContent(popup);
  }else{
    baseMarker = L.marker(mapPos, {icon: baseIcon()}).addTo(map).bindPopup(popup);
  }
  if(forceCenter){
    map.setView(mapPos, b.zoom);
  }
}

function trackColorForSn(sn){
  var id = String(sn || '');
  if(!id) return '#1f9dff';
  var h = 0;
  for(var i=0;i<id.length;i++){
    h = ((h * 31) + id.charCodeAt(i)) >>> 0;
  }
  return TRACK_COLORS[h % TRACK_COLORS.length];
}

function fmtReplayTime(ts){
  var n = Number(ts);
  if(!isFinite(n) || n <= 0) return '-';
  try{
    return new Date(n * 1000).toLocaleString();
  }catch(_e){
    return '-';
  }
}
function collectHistoryTrackBounds(){
  var selected = historyVisibleSnList(latestDroneRows);
  var minTs = null;
  var maxTs = null;
  var loadedCount = 0;
  var pointCount = 0;
  selected.forEach(function(sn){
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    if(tr.length) loadedCount += 1;
    for(var i=0;i<tr.length;i++){
      var ts = _trackTsSec(tr[i]);
      if(ts == null) continue;
      pointCount += 1;
      if(minTs == null || ts < minTs) minTs = ts;
      if(maxTs == null || ts > maxTs) maxTs = ts;
    }
  });
  return {selectedCount:selected.length, loadedCount:loadedCount, pointCount:pointCount, min:minTs, max:maxTs};
}
function historyFilterSliderToTs(bounds, val){
  if(!bounds || bounds.min == null || bounds.max == null) return null;
  var span = Number(bounds.max) - Number(bounds.min);
  if(!isFinite(span) || span <= 0) return Number(bounds.min);
  var v = Math.max(0, Math.min(1000, Number(val || 0)));
  return Number(bounds.min) + span * (v / 1000);
}
function historyFilterTsToSlider(bounds, ts){
  if(!bounds || bounds.min == null || bounds.max == null) return 0;
  var span = Number(bounds.max) - Number(bounds.min);
  if(!isFinite(span) || span <= 0) return 0;
  var target = (ts == null) ? Number(bounds.min) : Number(ts);
  var v = (target - Number(bounds.min)) / span;
  return Math.max(0, Math.min(1000, Math.round(v * 1000)));
}
function normalizeHistoryTrackFilterTs(bounds){
  if(!bounds || bounds.min == null || bounds.max == null || bounds.max <= bounds.min){
    historyTrackFilterTs = null;
    return;
  }
  var ts = activeHistoryTrackFilterTs();
  if(ts == null) return;
  if(ts < Number(bounds.min)) historyTrackFilterTs = Number(bounds.min);
  else if(ts > Number(bounds.max)) historyTrackFilterTs = Number(bounds.max);
}
function onHistoryTrackFilterInput(){
  var bounds = collectHistoryTrackBounds();
  var slider = qs('history-filter-progress');
  var nextTs = historyFilterSliderToTs(bounds, slider ? slider.value : 0);
  if(nextTs == null) return;
  if(replayState.sn || (replayState.points || []).length) clearReplaySelection({render:false});
  historyTrackFilterTs = nextTs;
  renderReplayCard();
  renderDroneTable(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function resetHistoryTrackFilter(){
  if(replayState.sn || (replayState.points || []).length) clearReplaySelection({render:false});
  historyTrackFilterTs = null;
  renderReplayCard();
  renderDroneTable(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function replaySliderToTs(val){
  var points = Array.isArray(replayState.points) ? replayState.points : [];
  var idx = Math.round(Number(val || 0));
  if(!points.length || !isFinite(idx)) return null;
  idx = Math.max(0, Math.min(points.length - 1, idx));
  return Number(points[idx].ts);
}
function replayTsToSlider(ts){
  var points = Array.isArray(replayState.points) ? replayState.points : [];
  if(!points.length) return 0;
  var idx = replayState.cursorIndex;
  if(idx == null && ts != null){
    var target = Number(ts);
    idx = 0;
    for(var i=0;i<points.length;i++){
      if(Number(points[i].ts) <= target) idx = i;
      else break;
    }
  }
  idx = Math.round(Number(idx == null ? 0 : idx));
  if(!isFinite(idx)) idx = 0;
  return Math.max(0, Math.min(points.length - 1, idx));
}
function replayBuildPoints(){
  var selected = historyVisibleSnList(latestDroneRows);
  var points = [];
  var loadedCount = 0;
  selected.forEach(function(sn){
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    if(tr.length) loadedCount += 1;
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var ts = _trackTsSec(p);
      if(ts == null) continue;
      if(!validMapCoord(p.lat, p.lon)) continue;
      points.push({sn:String(sn), point:p, ts:ts, sourceIndex:i});
    }
  });
  points.sort(function(a,b){
    var dt = Number(a.ts) - Number(b.ts);
    if(dt) return dt;
    var ds = String(a.sn).localeCompare(String(b.sn));
    if(ds) return ds;
    return Number(a.sourceIndex || 0) - Number(b.sourceIndex || 0);
  });
  return {snList:selected, points:points, selectedCount:selected.length, loadedCount:loadedCount};
}
function replaySelectedSet(){
  var set = {};
  (Array.isArray(replayState.snList) ? replayState.snList : []).forEach(function(sn){ if(sn) set[String(sn)] = true; });
  return set;
}
function ensureTrackReplayCard(){
  var panel = qs('map-panel');
  if(!panel) return null;
  if(!qs('replay-sync-banner')){
    var syncBanner = document.createElement('div');
    syncBanner.id = 'replay-sync-banner';
    syncBanner.className = 'replay-sync-banner';
    syncBanner.innerHTML = '<span class="replay-sync-dot"></span><span id="replay-sync-text">轨迹重演中，同步已暂停</span>';
    panel.appendChild(syncBanner);
  }
  var card = qs('track-replay-card');
  if(card) return card;
  card = document.createElement('aside');
  card.id = 'track-replay-card';
  card.className = 'track-replay-card';
  card.innerHTML =
    '<div class="track-replay-head"><div><div class="track-replay-title">轨迹回放</div><div id="track-replay-count" class="track-replay-sub">-</div></div></div>'+
    '<div class="track-replay-time" id="track-history-filter-time">-</div>'+
    '<div class="track-replay-time" id="track-replay-time">-</div>'+
    '<div class="track-replay-ranges">'+
      '  <input id="replay-progress" type="range" min="0" max="1000" step="1" value="0" aria-label="重放进度">'+
    '</div>'+
    '<div class="track-replay-controls">'+
    '  <button class="btn-mini" id="btn-replay-play" type="button">播放</button>'+
    '  <button class="btn-mini warn" id="btn-replay-exit" type="button" style="display:none">退出回放</button>'+
    '  <label class="track-speed-label"><span>速度</span><input id="replay-speed" type="range" min="1" max="10" step="0.1" value="1" aria-label="重放速度"><span id="replay-speed-value" class="track-speed-value">1.0x</span></label>'+
    '  <button class="btn-mini" id="btn-replay-100x" type="button">100x</button>'+
    '</div>'+
    '<div class="track-replay-status" id="track-replay-status">勾选飞机后，默认显示最后位置和完整轨迹。</div>';
  panel.appendChild(card);
  var progress = qs('replay-progress');
  if(progress) progress.addEventListener('input', onReplayRangeInput);
  var play = qs('btn-replay-play');
  if(play) play.addEventListener('click', function(){ setReplayPlaying(!replayState.playing); });
  var exit = qs('btn-replay-exit');
  if(exit) exit.addEventListener('click', function(){
    exitReplayToLatest();
  });
  var speed = qs('replay-speed');
  if(speed) speed.addEventListener('input', function(){
    replayState.speed = Math.max(1, Math.min(10, Number(speed.value || 1)));
    renderReplayCard();
  });
  var speed100 = qs('btn-replay-100x');
  if(speed100) speed100.addEventListener('click', function(){
    replayState.speed = (Number(replayState.speed || 1) === 100) ? Math.max(1, Math.min(10, Number((qs('replay-speed') || {}).value || 1))) : 100;
    renderReplayCard();
  });
  return card;
}
function replayCandidateList(){
  var rows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
  var selectedSet = {};
  historyVisibleSnList(rows).forEach(function(sn){ if(sn) selectedSet[sn] = true; });
  var seen = {};
  var out = [];
  rows.forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn || seen[sn] || !selectedSet[sn]) return;
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    if(!tr.length) return;
    seen[sn] = true;
    out.push({sn:sn, count:tr.length, label:sn + ' · ' + tr.length + ' 点'});
  });
  out.sort(function(a,b){ return String(a.sn).localeCompare(String(b.sn)); });
  return out;
}
function replaySelectedSn(){
  var candidates = replayCandidateList();
  var set = {};
  candidates.forEach(function(x){ set[String(x.sn)] = true; });
  var cur = String(replayState.sn || '');
  if(cur && set[cur]) return cur;
  return '';
}
function syncReplaySelect(candidates, selectedSn){
  var sel = qs('replay-sn-select');
  if(!sel) return;
  var prev = sel.value;
  var opts = ['<option value="">选择飞机</option>'];
  (candidates || []).forEach(function(x){
    opts.push('<option value="'+escAttr(x.sn)+'">'+esc(x.label || x.sn)+'</option>');
  });
  var html = opts.join('');
  if(sel.innerHTML !== html) sel.innerHTML = html;
  sel.value = selectedSn || (prev && (candidates || []).some(function(x){ return x.sn === prev; }) ? prev : '');
}
function collectReplayBounds(){
  var built = replayBuildPoints();
  replayState.snList = built.snList.slice();
  replayState.points = built.points.slice();
  replayState.sn = built.snList.length ? built.snList.join(', ') : null;
  if(!built.points.length){
    return {sn:null, min:null, max:null, visibleCount:built.selectedCount, candidateCount:built.snList.length, count:0, loadedCount:built.loadedCount};
  }
  var lastIdx = built.points.length - 1;
  return {
    sn:replayState.sn,
    min:built.points[0].ts,
    max:built.points[lastIdx].ts,
    startIndex:0,
    endIndex:lastIdx,
    visibleCount:built.selectedCount,
    candidateCount:built.snList.length,
    count:built.points.length,
    loadedCount:built.loadedCount
  };
}
function clearReplaySelection(opts){
  opts = (opts && typeof opts === 'object') ? opts : {};
  stopReplayTimer();
  setReplaySyncPaused(false);
  replayState.sn = null;
  replayState.snList = [];
  replayState.points = [];
  replayState.min = null;
  replayState.max = null;
  replayState.start = null;
  replayState.end = null;
  replayState.cursor = null;
  replayState.startIndex = 0;
  replayState.endIndex = null;
  replayState.cursorIndex = null;
  replayState.userRange = false;
  clearReplayMarkers();
  if(opts.render !== false) renderReplayCard();
}
function refreshReplayBounds(keepRange){
  ensureTrackReplayCard();
  var b = collectReplayBounds();
  replayState.sn = b.sn || null;
  if(!b.sn){
    if(replayState.playing) setReplayPlaying(false);
    else {
      stopReplayTimer();
      setReplaySyncPaused(false);
    }
    replayState.min = replayState.max = replayState.start = replayState.end = replayState.cursor = null;
    replayState.startIndex = 0;
    replayState.endIndex = replayState.cursorIndex = null;
    replayState.userRange = false;
    renderReplayCard();
    clearReplayMarkers();
    return;
  }
  if(b.min == null || b.max == null || !b.count){
    if(replayState.playing) setReplayPlaying(false);
    else {
      stopReplayTimer();
      setReplaySyncPaused(false);
    }
    replayState.min = replayState.max = replayState.start = replayState.end = replayState.cursor = null;
    replayState.startIndex = 0;
    replayState.endIndex = replayState.cursorIndex = null;
    replayState.userRange = false;
    renderReplayCard();
    clearReplayMarkers();
    return;
  }
  replayState.min = b.min;
  replayState.max = b.max;
  replayState.startIndex = 0;
  replayState.endIndex = b.endIndex;
  replayState.start = b.min;
  replayState.end = b.max;
  if(!keepRange || replayState.cursorIndex == null || replayState.cursorIndex < 0 || replayState.cursorIndex > b.endIndex){
    replayState.cursorIndex = b.endIndex;
    replayState.cursor = replayState.max;
  }else{
    replayState.cursorIndex = Math.max(0, Math.min(b.endIndex, Math.round(Number(replayState.cursorIndex))));
    replayState.cursor = replayState.points[replayState.cursorIndex] ? Number(replayState.points[replayState.cursorIndex].ts) : replayState.start;
  }
  renderReplayCard();
}
function renderReplayCard(){
  var card = ensureTrackReplayCard();
  if(!card) return;
  var page = currentAppPage();
  card.style.display = (page === 'history') ? '' : 'none';
  var historyBounds = collectHistoryTrackBounds();
  normalizeHistoryTrackFilterTs(historyBounds);
  var b = collectReplayBounds();
  var pointCount = Number(b.count || 0);
  var selectedCount = Number(b.visibleCount || 0);
  var countEl = qs('track-replay-count');
  if(countEl){
    if(pointCount) countEl.textContent = '已勾选 ' + selectedCount + ' 架 · 重放点 ' + pointCount + ' 个';
    else if(selectedCount) countEl.textContent = '已勾选 ' + selectedCount + ' 架 · 等待轨迹点';
    else countEl.textContent = '默认仅勾选 12 小时内飞机';
  }
  var hasHistoryRange = historyBounds.min != null && historyBounds.max != null && historyBounds.max > historyBounds.min;
  var historyTime = qs('track-history-filter-time');
  if(historyTime){
    if(!historyBounds.selectedCount){
      historyTime.textContent = '进入历史记录后默认显示最后位置和完整轨迹。';
    }else if(!hasHistoryRange){
      historyTime.textContent = historyBounds.loadedCount ? '已勾选飞机的轨迹点不足。' : '正在加载已勾选飞机的轨迹...';
    }else{
      historyTime.textContent = '完整轨迹范围 ' + fmtReplayTime(historyBounds.min) + '  ~  ' + fmtReplayTime(historyBounds.max);
    }
  }
  var progressEl = qs('replay-progress');
  var hasRange = pointCount > 0;
  var curIndex = replayTsToSlider(replayState.cursor == null ? replayState.start : replayState.cursor);
  if(progressEl){
    progressEl.disabled = !hasRange;
    progressEl.min = '0';
    progressEl.max = hasRange ? String(pointCount - 1) : '0';
    progressEl.step = '1';
    progressEl.value = hasRange ? String(curIndex) : '0';
  }
  var play = qs('btn-replay-play');
  if(play){
    play.disabled = !hasRange;
    play.textContent = replayState.playing ? '暂停' : '播放';
  }
  var exit = qs('btn-replay-exit');
  if(exit) exit.style.display = replaySyncPaused ? '' : 'none';
  var speed = qs('replay-speed');
  if(speed){
    speed.disabled = !hasRange;
    if(Number(replayState.speed || 1) !== 100){
      speed.value = String(Math.max(1, Math.min(10, Number(replayState.speed || 1))));
    }
  }
  var speedValue = qs('replay-speed-value');
  if(speedValue) speedValue.textContent = (Number(replayState.speed || 1) === 100) ? '100x' : (Number(replayState.speed || 1).toFixed(1) + 'x');
  var speed100 = qs('btn-replay-100x');
  if(speed100){
    speed100.disabled = !hasRange;
    speed100.classList.toggle('warn', Number(replayState.speed || 1) === 100);
  }
  var time = qs('track-replay-time');
  if(time){
    var curPoint = replayState.points && replayState.points[curIndex] ? replayState.points[curIndex] : null;
    time.textContent = hasRange
      ? ('第 ' + (curIndex + 1) + ' / ' + pointCount + ' 点  ' + (curPoint ? curPoint.sn : '') + '\\n当前 ' + fmtReplayTime(replayState.cursor == null ? replayState.start : replayState.cursor))
      : '暂无可重放轨迹';
  }
  var status = qs('track-replay-status');
  if(status){
    var speedText = speedValue ? speedValue.textContent : ((Number(replayState.speed || 1) === 100) ? '100x' : (Number(replayState.speed || 1).toFixed(1) + 'x'));
    if(!selectedCount) status.textContent = '请先在历史列表中勾选要重放的飞机。';
    else if(!hasRange) status.textContent = '已勾选飞机的轨迹正在加载或没有有效轨迹点。';
    else if(replaySyncPaused) status.textContent = replayState.playing ? ('按轨迹点重放中，实时数据同步已暂停。倍速 ' + speedText + '。') : '回放已暂停，卡片和地图显示当前回放点。';
    else status.textContent = '默认显示最后位置和完整轨迹；拖动进度或播放后进入回放。';
  }
  updateReplaySyncUi();
}
function onReplayRangeInput(){
  var b = collectReplayBounds();
  if(!b.count) return;
  var progressEl = qs('replay-progress');
  var points = Array.isArray(replayState.points) ? replayState.points : [];
  var idx = Math.round(Number(progressEl ? progressEl.value : 0));
  if(!isFinite(idx)) idx = 0;
  idx = Math.max(0, Math.min(points.length - 1, idx));
  replayState.playing = false;
  setReplaySyncPaused(true);
  replayState.userRange = true;
  replayState.cursorIndex = idx;
  replayState.cursor = Number(points[idx].ts);
  renderReplayFrame();
}
function resetReplayRange(){
  var b = collectReplayBounds();
  if(!b.count) return;
  replayState.startIndex = 0;
  replayState.endIndex = b.endIndex;
  replayState.start = b.min;
  replayState.end = b.max;
  replayState.cursorIndex = b.endIndex;
  replayState.cursor = replayState.max;
  replayState.userRange = false;
  renderReplayFrame();
}
function stopReplayTimer(){
  if(replayState.timer){
    clearInterval(replayState.timer);
    replayState.timer = null;
  }
  replayState.playing = false;
}
function updateReplaySyncUi(){
  var panel = qs('map-panel');
  if(panel) panel.classList.toggle('replay-sync-paused', !!replaySyncPaused);
  var txt = qs('replay-sync-text');
  if(txt) txt.textContent = replayState.snList && replayState.snList.length ? ('轨迹重演中，同步已暂停：' + replayState.snList.length + ' 架') : '轨迹重演中，同步已暂停';
  if(qs('ws-status')){
    if(replaySyncPaused) qs('ws-status').textContent = '重演中';
    else if(ws && ws.readyState === WebSocket.OPEN) qs('ws-status').textContent = '实时';
  }
}
function applyPendingLiveData(){
  if(!frozenPendingData) return false;
  var d = frozenPendingData;
  frozenPendingData = null;
  onData(d);
  return true;
}
function exitReplayToLatest(){
  var hadPending = !!frozenPendingData;
  clearReplaySelection({render:false});
  if(!hadPending || !applyPendingLiveData()){
    renderDroneTable(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    renderMapMiniList(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    refreshReplayBounds(false);
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  }
  showBanner('已退出回放，恢复最后状态。', 'ok', 2400, {persist:false});
}
function setReplaySyncPaused(paused){
  var next = !!paused;
  if(replaySyncPaused === next){
    updateReplaySyncUi();
    return;
  }
  if(replaySyncPaused && !next){
    suppressNextDroneNotifications = true;
  }
  replaySyncPaused = next;
  updateReplaySyncUi();
}
function setReplayPlaying(on){
  if(!on){
    stopReplayTimer();
    if(replaySyncPaused) renderReplayFrame();
    else {
      renderReplayCard();
      updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    }
    return;
  }
  var b = collectReplayBounds();
  if(!b.sn){
    showBanner('请先在历史列表中勾选要重放的飞机。', 'warn', 3200);
    renderReplayCard();
    return;
  }
  if(b.min == null || b.max == null || !b.count){
    showBanner('已勾选飞机没有有效轨迹点，暂不能重演。', 'warn', 3200);
    renderReplayCard();
    return;
  }
  replayState.sn = b.sn;
  replayState.min = b.min;
  replayState.max = b.max;
  replayState.startIndex = 0;
  replayState.endIndex = b.endIndex;
  replayState.cursorIndex = 0;
  replayState.start = b.min;
  replayState.end = b.max;
  replayState.cursor = replayState.start;
  if(replayState.start == null || replayState.end == null) return;
  replayState.playing = true;
  setReplaySyncPaused(true);
  if(replayState.timer) clearInterval(replayState.timer);
  replayState.timer = setInterval(function(){
    var points = Array.isArray(replayState.points) ? replayState.points : [];
    if(!points.length){
      stopReplayTimer();
      renderReplayFrame();
      return;
    }
    var step = Math.max(1, Math.round(Number(replayState.speed || 1)));
    var idx = Math.max(0, Math.min(points.length - 1, Math.round(Number(replayState.cursorIndex || 0)) + step));
    replayState.cursorIndex = idx;
    replayState.cursor = Number(points[idx].ts);
    if(idx >= points.length - 1){
      stopReplayTimer();
      showBanner('轨迹回放已结束。', 'ok', 2600, {persist:false});
    }
    renderReplayFrame();
  }, 250);
  showBanner('轨迹重演开始，新的数据同步已暂停。', 'warn', 3600, {persist:false});
  renderReplayFrame();
}
function replayWindowEnd(){
  if(replayState.cursor != null) return replayState.cursor;
  return replayState.end;
}
function filterTrackByReplay(track, sn){
  var arr = Array.isArray(track) ? track.slice() : [];
  return arr;
}
function replayRowsAtCursor(){
  var selectedSet = replaySelectedSet();
  var end = Number(replayWindowEnd());
  if(!isFinite(end)) return [];
  var rowsBySn = {};
  (Array.isArray(latestDroneRows) ? latestDroneRows : []).forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(sn && selectedSet[sn]) rowsBySn[sn] = Object.assign({}, e);
  });
  (Array.isArray(replayState.snList) ? replayState.snList : []).forEach(function(sn){
    sn = String(sn || '');
    if(!sn || !selectedSet[sn]) return;
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    var point = null;
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var ts = _trackTsSec(p);
      if(ts == null || ts > end) continue;
      if(!validMapCoord(p.lat, p.lon)) continue;
      point = p;
    }
    if(!point) return;
    var row = rowsBySn[sn] || {sn:sn};
    row = Object.assign({}, row);
    row.lat = Number(point.lat);
    row.lon = Number(point.lon);
    row.last_seen = fmtReplayTime(point.ts);
    row.last_pkt_time = fmtReplayTime(point.ts);
    row.capture_time = fmtReplayTime(point.ts);
    row.age_text = '重放 ' + fmtReplayTime(point.ts);
    row.age = 0;
    row.lost = false;
    rowsBySn[sn] = row;
  });
  return (Array.isArray(replayState.snList) ? replayState.snList : []).map(function(sn){
    return rowsBySn[String(sn || '')];
  }).filter(function(e){ return !!e; });
}
function renderReplayFrame(){
  var mapRows = replayRowsAtCursor();
  renderReplayCard();
  renderDroneTable(mapRows);
  updateMap(mapRows);
}
function clearReplayMarkers(){
  if(!map) return;
  Object.keys(replayMarkers).forEach(function(sn){
    try{ map.removeLayer(replayMarkers[sn]); }catch(_e){}
    delete replayMarkers[sn];
  });
}
function updateReplayMarkers(){
  if(!map) return;
  var selected = Array.isArray(replayState.snList) ? replayState.snList : [];
  if(currentAppPage() !== 'history' || !replaySyncPaused || !selected.length || replayState.start == null || replayWindowEnd() == null){
    clearReplayMarkers();
    return;
  }
  var active = {};
  var end = Number(replayWindowEnd());
  var start = Number(replayState.start);
  selected.forEach(function(replaySn, idx){
    replaySn = String(replaySn || '');
    if(!replaySn) return;
    var tr = Array.isArray(trackCache[replaySn]) ? trackCache[replaySn] : [];
    var point = null;
    var prevPoint = null;
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var ts = _trackTsSec(p);
      if(ts == null || ts < start || ts > end) continue;
      if(!validMapCoord(p.lat, p.lon)) continue;
      if(point) prevPoint = point;
      point = p;
    }
    if(point){
      var lat = Number(point.lat), lon = Number(point.lon);
      if(isFinite(lat) && isFinite(lon)){
        active[replaySn] = true;
        var pos = toMapLatLng(lat, lon);
        var col = trackColorForSn(replaySn);
        var heading = null;
        if(prevPoint && isFinite(Number(prevPoint.lat)) && isFinite(Number(prevPoint.lon))){
          var hs = calcHeadingByLatLon(Number(prevPoint.lat), Number(prevPoint.lon), lat, lon, 0.5);
          if(hs.ok) heading = hs.heading;
        }
        var popup = '<b>'+esc(replaySn)+'</b><br>重放位置<br>'+fmtReplayTime(point.ts);
        var icon = droneIcon(col, false, heading, true, idx + 1, false);
        if(replayMarkers[replaySn] && replayMarkers[replaySn].setIcon){
          replayMarkers[replaySn].setLatLng(pos).setIcon(icon).setPopupContent(popup);
        }else{
          if(replayMarkers[replaySn]){
            try{ map.removeLayer(replayMarkers[replaySn]); }catch(_e){}
          }
          replayMarkers[replaySn] = L.marker(pos, {icon: icon}).addTo(map).bindPopup(popup);
        }
      }
    }
  });
  Object.keys(replayMarkers).forEach(function(sn){
    if(!active[sn]){
      map.removeLayer(replayMarkers[sn]);
      delete replayMarkers[sn];
    }
  });
}

function droneIcon(color, lost, headingDeg, selected, indexNo, alarm){
  var op = lost ? 0.34 : 1.0;
  var rot = Number(headingDeg);
  if(!isFinite(rot)) rot = 0;
  var idx = Number(indexNo);
  if(!isFinite(idx) || idx <= 0) idx = 0;
  var idxTxt = idx > 99 ? '99+' : String(Math.round(idx));
  var cls = 'drone-pin' + (selected ? ' selected' : '') + (alarm ? ' alarm' : '');
  var svg = '<div class="'+cls+'" style="--drone-color:'+escAttr(color)+';--drone-rot:'+rot.toFixed(1)+'deg;--drone-op:'+op.toFixed(2)+'">'
    +'<div class="drone-symbol"><svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 48 48" width="46" height="46" aria-hidden="true">'
    +'<path d="M24 3.8 39.7 41.5 24 33.8 8.3 41.5 24 3.8Z" fill="'+escAttr(color)+'" stroke="#fff" stroke-width="2.5" stroke-linejoin="round"/>'
    +'<path d="M24 8.6v24.8M15.5 37.9 24 29.4l8.5 8.5" fill="none" stroke="rgba(255,255,255,.82)" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"/>'
    +'</svg></div><div class="drone-index">'+esc(idxTxt)+'</div></div>';
  return L.divIcon({
    html: svg, className:'rid-drone-icon', iconSize:[74,58], iconAnchor:[25,30], popupAnchor:[0,-30]
  });
}

function pilotIcon(color, lost){
  var op = lost ? 0.4 : 1.0;
  var fill = color || '#ffb84d';
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="48" height="48" viewBox="0 0 24 24">'
    +'<rect x="3.5" y="3.5" width="17" height="17" rx="4" ry="4" fill="'+fill+'" fill-opacity="'+op+'" stroke="#fff" stroke-width="1.4"/>'
    +'<text x="12" y="16" text-anchor="middle" font-size="12" fill="#fff" font-family="monospace" font-weight="bold">👤</text>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[48,48], iconAnchor:[24,24], popupAnchor:[0,-20]
  });
}

function homeAuxIcon(color, lost){
  var op = lost ? 0.4 : 1.0;
  var fill = color || '#ffb84d';
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="48" height="48" viewBox="0 0 24 24">'
    +'<rect x="3.5" y="3.5" width="17" height="17" rx="4" ry="4" fill="'+fill+'" fill-opacity="'+op+'" stroke="#fff" stroke-width="1.4"/>'
    +'<path d="M6.8 12.1 12 7.6l5.2 4.5M8.3 11.2v5.5h7.4v-5.5" fill="none" stroke="#fff" stroke-width="1.7" stroke-linecap="round" stroke-linejoin="round"/>'
    +'<path d="M10.9 16.7v-3.1h2.2v3.1" fill="none" stroke="#fff" stroke-width="1.5" stroke-linecap="round" stroke-linejoin="round"/>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[48,48], iconAnchor:[24,24], popupAnchor:[0,-20]
  });
}

function coordText(lat, lon, dec){
  dec = dec == null ? 6 : dec;
  return validMapCoord(lat, lon) ? (Number(lat).toFixed(dec) + ', ' + Number(lon).toFixed(dec)) : 'N/A';
}

function sameCoord(aLat, aLon, bLat, bLon){
  if(!validMapCoord(aLat, aLon) || !validMapCoord(bLat, bLon)) return false;
  return Math.abs(Number(aLat) - Number(bLat)) < 0.000001 && Math.abs(Number(aLon) - Number(bLon)) < 0.000001;
}

function homeAuxLocations(e){
  e = e || {};
  var locs = [];
  var hasHome = validMapCoord(e.home_lat, e.home_lon);
  var hasAux = validMapCoord(e.aux_lat, e.aux_lon);
  var auxDiff = hasAux && (!hasHome || !sameCoord(e.home_lat, e.home_lon, e.aux_lat, e.aux_lon));
  if(hasHome){
    locs.push({kind:'home', label:auxDiff ? 'Home' : 'Aux/Home', lat:e.home_lat, lon:e.home_lon});
  }
  if(auxDiff){
    locs.push({kind:'aux', label:hasHome ? 'Aux' : 'Aux/Home', lat:e.aux_lat, lon:e.aux_lon});
  }
  return locs;
}

function aircraftMapCoord(e){
  e = e || {};
  var aircraft = (e.aircraft_position && typeof e.aircraft_position === 'object') ? e.aircraft_position : null;
  if(aircraft && validMapCoord(aircraft.lat, aircraft.lon)){
    return {lat:aircraft.lat, lon:aircraft.lon, source:String(aircraft.source || 'aircraft_position')};
  }
  if(validMapCoord(e.lat, e.lon)){
    return {lat:e.lat, lon:e.lon, source:'lat_lon'};
  }
  return null;
}

function primaryOperatorCoord(e){
  e = e || {};
  var ops = Array.isArray(e.operator_positions) ? e.operator_positions : [];
  for(var i=0;i<ops.length;i++){
    var op = ops[i] || {};
    if(validMapCoord(op.lat, op.lon)){
      return {
        lat:op.lat,
        lon:op.lon,
        typeText:String(op.source || op.role || 'operator'),
        source:String(op.source || 'operator_positions')
      };
    }
  }
  if(validMapCoord(e.pilot_lat, e.pilot_lon)){
    return {
      lat:e.pilot_lat,
      lon:e.pilot_lon,
      typeText:String(e.pilot_loc_type_text || e.pilot_loc_type || 'operator'),
      source:'pilot_fields'
    };
  }
  return null;
}

function operatorLocationEntries(e){
  e = e || {};
  var locs = [];
  var op = primaryOperatorCoord(e);
  if(op){
    locs.push({
      kind:'remote',
      label:'遥控站位置',
      lat:op.lat,
      lon:op.lon,
      typeText:op.typeText,
      icon:'pilot'
    });
  }
  homeAuxLocations(e).forEach(function(loc){
    locs.push({
      kind:loc.kind,
      label:loc.label,
      lat:loc.lat,
      lon:loc.lon,
      typeText:'Aux/Home',
      icon:'home'
    });
  });
  return locs;
}

function homeAuxCoordText(e){
  var locs = homeAuxLocations(e);
  if(!locs.length) return 'N/A';
  return locs.map(function(loc){
    return loc.label + ': ' + coordText(loc.lat, loc.lon, 6);
  }).join(' / ');
}

function appendHomeAuxRows(rows, e){
  var locs = homeAuxLocations(e);
  if(!locs.length){
    rows.push(['Aux/Home 纬度', fmt((e || {}).home_lat ?? (e || {}).aux_lat,6,'')]);
    rows.push(['Aux/Home 经度', fmt((e || {}).home_lon ?? (e || {}).aux_lon,6,'')]);
    return rows;
  }
  locs.forEach(function(loc){
    rows.push([loc.label + ' 纬度', fmt(loc.lat,6,'')]);
    rows.push([loc.label + ' 经度', fmt(loc.lon,6,'')]);
  });
  return rows;
}

function updateMap(drones){
  if(!map) return;
  applyBaseMarker(false);
  var autoState = mapAutoState();
  var page = currentAppPage();
  var rows = Array.isArray(drones) ? drones : [];
  var replaySelected = (page === 'history' && replaySyncPaused && (replayState.snList || []).length)
    ? (replayState.snList || []).slice()
    : null;
  var selected = replaySelected || ((page === 'history') ? historyVisibleSnList(rows) : selectedSnList());
  var selectedSet = {};
  selected.forEach(function(sn){ selectedSet[sn] = true; });
  var recentRows = liveRecentRows(rows);
  var trackSn = replaySelected || displayTrackSnList(page, rows);
  var liveAir = (page === 'live' ? recentRows : rows).filter(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return false;
    if(page === 'history' && !selectedSet[sn]) return false;
    return !!aircraftMapCoord(e);
  });
  var liveOperatorLocations = [];
  (page === 'live' ? recentRows : rows).forEach(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return;
    if(page === 'history' && !selectedSet[sn]) return;
    operatorLocationEntries(e).forEach(function(loc){
      liveOperatorLocations.push({sn:sn, row:e, loc:loc});
    });
  });
  var mapHintTxt = '';
  if(page === 'live'){
    mapHintTxt = '实时目标:' + recentRows.length + '  飞机:' + liveAir.length + '  飞手位置:' + liveOperatorLocations.length + '  离线:2分钟';
  }else{
    mapHintTxt = '显示飞机:' + liveAir.length + '  已选:' + selected.length + '  轨迹:' + trackSn.length + '  飞手位置:' + liveOperatorLocations.length;
  }
  if(!autoState.allow){
    mapHintTxt += '  |  自动回中冷却 ' + Math.ceil(autoState.remain) + 's';
  }
  document.getElementById('map-hint').textContent = mapHintTxt;

  // color assignment by SN
  rows.forEach(function(e){
    if(!colorIdx[e.sn]){
      var n = Object.keys(colorIdx).length;
      colorIdx[e.sn] = COLORS[n % COLORS.length];
    }
  });

  var activeAir = {};
  var activeTws = {};
  var nowSec = Date.now() / 1000;
  var headingMinMove = 2.0;
  var headingMaxGapSec = 90.0;
  liveAir.forEach(function(e, idx){
    var sn = String(e.sn || '');
    if(!sn) return;
    var airCoord = aircraftMapCoord(e);
    if(!airCoord) return;
    activeAir[sn] = true;
    var col = colorIdx[sn];
    var isSel = !!selectedSet[sn];
    var inAlarmZone = !!zoneAlarmSnSet[sn];
    var latRaw = Number(airCoord.lat), lonRaw = Number(airCoord.lon);
    var prev = motionState[sn] || {};
    var heading = null;
    var headingDelta = null;
    if(isFinite(Number(prev.lat)) && isFinite(Number(prev.lon))){
      var dt = nowSec - Number(prev.ts || 0);
      if(isFinite(dt) && dt >= 0 && dt <= headingMaxGapSec){
        var hs = calcHeadingByLatLon(Number(prev.lat), Number(prev.lon), latRaw, lonRaw, headingMinMove);
        if(hs.ok) heading = hs.heading;
      }
    }
    if(heading == null && isFinite(Number(prev.heading))){
      heading = Number(prev.heading);
    }
    if(heading != null && isFinite(Number(heading))){
      heading = normDeg(heading);
      headingDelta = headingDeltaDeg(heading, mapHeadingRefDeg);
    }else{
      heading = null;
      headingDelta = null;
    }
    motionState[sn] = {lat:latRaw, lon:lonRaw, heading:heading, ts:nowSec};

    var popup = '<b>'+sn+'</b><br>'+e.model+'<br>'
      +(validMapCoord(latRaw, lonRaw)?Number(latRaw).toFixed(5):'-')+', '+(validMapCoord(latRaw, lonRaw)?Number(lonRaw).toFixed(5):'-')
      +'<br>高度: '+(e.alt!=null?e.alt.toFixed(1)+'m':'N/A')
      +'<br>速度: '+(e.spd!=null?e.spd.toFixed(1)+'m/s':'N/A')
      +'<br>信号: '+(e.rssi!=null?e.rssi+'dBm':'N/A')
      +'<br>航向: '+(isFinite(Number(heading))?Number(heading).toFixed(1)+'°':'N/A')
      +'<br>航向差: '+(isFinite(Number(headingDelta))?((headingDelta>=0?'+':'')+Number(headingDelta).toFixed(1)+'°'):'N/A')
      +'<br>数据更新: '+esc(String(e.age_text || fmtAge(e.age)));

    var airPos = safeMapLatLng(latRaw, lonRaw);
    if(!airPos) return;
    var dispNo = idx + 1;
    if(markers[sn]){
      markers[sn].setLatLng(airPos)
                   .setIcon(droneIcon(col, e.lost, heading, isSel, dispNo, inAlarmZone))
                   .setPopupContent(popup);
    } else {
      markers[sn] = L.marker(airPos, {icon: droneIcon(col, e.lost, heading, isSel, dispNo, inAlarmZone)})
        .addTo(map).bindPopup(popup);
      (function(snLocal){
        markers[snLocal].on('click', function(){
          if(currentAppPage() === 'history') setHistorySnVisible(snLocal, true);
          else focusLiveAircraft(snLocal);
        });
      })(sn);
    }

  });

  var activePilot = {};
  liveOperatorLocations.forEach(function(item){
    var e = item.row || {};
    var loc = item.loc || {};
    var sn = String(item.sn || e.sn || '');
    if(!sn) return;
    var markerKey = sn + ':' + String(loc.kind || 'remote');
    activePilot[markerKey] = true;
    var col = colorIdx[sn] || '#ffb84d';
    var ptxt = String(loc.typeText || '-');
    var pilotPos = safeMapLatLng(loc.lat, loc.lon);
    if(!pilotPos) return;
    var icon = (loc.icon === 'home') ? homeAuxIcon(col, e.lost) : pilotIcon(col, e.lost);
    var popup = '<b>'+sn+'</b><br>'+esc(String(loc.label || '飞手位置'))+'<br>'
      +(validMapCoord(loc.lat, loc.lon)?Number(loc.lat).toFixed(5):'-')+', '+(validMapCoord(loc.lat, loc.lon)?Number(loc.lon).toFixed(5):'-')
      +'<br>类型: '+esc(ptxt);
    if(pilotMarkers[markerKey]){
      pilotMarkers[markerKey].setLatLng(pilotPos)
        .setIcon(icon)
        .setPopupContent(popup);
    }else{
      pilotMarkers[markerKey] = L.marker(pilotPos, {icon: icon})
        .addTo(map).bindPopup(popup);
      (function(snLocal){
        pilotMarkers[markerKey].on('click', function(){
          if(currentAppPage() === 'history') setHistorySnVisible(snLocal, true);
          else focusLiveAircraft(snLocal);
        });
      })(sn);
    }
  });

  var activeTrack = {};
  var trackLatLngsAll = [];
  trackSn.forEach(function(sn){
    sn = String(sn || '');
    if(!sn) return;
    var tr = filterTrackForDisplay(Array.isArray(trackCache[sn]) ? trackCache[sn] : [], page, sn);
    if(tr.length < 2){
      dropTrackLayer(sn);
      return;
    }
    var latlngs = [];
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var lat = Number(p.lat), lon = Number(p.lon);
      if(validMapCoord(lat, lon)){
        var ll = safeMapLatLng(lat, lon);
        if(!ll) continue;
        latlngs.push(ll);
        trackLatLngsAll.push(ll);
      }
    }
    if(latlngs.length < 2){
      dropTrackLayer(sn);
      return;
    }
    activeTrack[sn] = true;
    var tColor = trackColorForSn(sn);
    var sig = trackLatLngSignature(latlngs);
    if(trackLines[sn] && trackLineSig[sn] === sig){
      return;
    }
    queueTrackLayerRender(sn, latlngs, tColor, sig);
  });

  // remove stale aircraft markers
  Object.keys(markers).forEach(function(sn){
    if(!activeAir[sn]){
      map.removeLayer(markers[sn]); delete markers[sn];
    }
  });
  // remove stale pilot markers
  Object.keys(pilotMarkers).forEach(function(sn){
    if(!activePilot[sn]){
      map.removeLayer(pilotMarkers[sn]); delete pilotMarkers[sn];
    }
  });
  Object.keys(twsLines).forEach(function(sn){
    if(!activeTws[sn]){
      map.removeLayer(twsLines[sn]); delete twsLines[sn];
    }
  });
  // remove stale or unselected tracks
  Object.keys(trackLines).forEach(function(sn){
    if(!activeTrack[sn]){
      dropTrackLayer(sn);
    }
  });
  Object.keys(motionState).forEach(function(sn){
    if(!activeAir[sn]) delete motionState[sn];
  });

  if(!liveAir.length){
    var b = baseFromMeta(metaState);
    if(page === 'history' && trackLatLngsAll.length && autoState.allow){
      fitMapDisplayLatLngs(trackLatLngsAll, 15, 0.14, 26);
      document.getElementById('map-hint').textContent = '历史轨迹 ' + trackSn.length + ' 架';
      return;
    }
    if(b.ok){
      if(autoState.allow){
        document.getElementById('map-hint').textContent = (page === 'live')
          ? '实时页暂无可显示目标'
          : '未勾选飞机或无可显示坐标';
      }else{
        document.getElementById('map-hint').textContent = ((page === 'live')
          ? '实时页暂无可显示目标'
          : '未勾选飞机或无可显示坐标')
          + ' | 自动回中冷却 ' + Math.ceil(autoState.remain) + 's';
      }
    } else {
      document.getElementById('map-hint').textContent='无坐标数据';
    }
    return;
  }

  // Keep all visible aircraft in range; use history tracks only when no aircraft position is displayable.
  var aircraftLatLngs = liveAir.map(function(e){
    var c = aircraftMapCoord(e);
    return c ? safeMapLatLng(c.lat, c.lon) : null;
  }).filter(function(x){ return !!x; });
  var latlngs = aircraftLatLngs.length ? aircraftLatLngs : (page === 'history' ? trackLatLngsAll : []);
  if(latlngs.length && autoState.allow){
    var singleZoom = aircraftLatLngs.length ? baseFromMeta(metaState).zoom : 15;
    fitMapDisplayLatLngs(latlngs, singleZoom, 0.18, 30);
  }
}
</script>
</body></html>"""

_HW_PAGE_HTML = """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>硬件配置助手 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}
:root{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --muted:#c8c6c4;--blue:#2899f5;--green:#92c353;--warn:#f7630c;--glow:rgba(40,153,245,.12);--soft:rgba(255,255,255,.03);--app-vh:100dvh;
  --radius:6px;--radius-lg:10px;--shadow-sm:0 1px 3px rgba(0,0,0,.08);--shadow:0 2px 8px rgba(0,0,0,.14);--transition:0.2s cubic-bezier(.4,0,.2,1)
}
body.theme-light{
  --bg:#f3f2f1;--bg2:#edebe9;--card:#ffffff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;
  --muted:#605e5c;--blue:#0078d4;--green:#107c10;--warn:#d83b01;--glow:rgba(0,120,212,.10);--soft:rgba(0,0,0,.018)
}
html,body{margin:0;padding:0;background:var(--bg);color:var(--txt);font-family:var(--font-ui)}
body{min-height:100vh;background:linear-gradient(180deg,var(--bg),var(--bg2) 18%,var(--bg));}
.wrap{max-width:1360px;margin:0 auto;padding:22px 18px 32px}
.topbar{display:flex;justify-content:space-between;align-items:flex-start;gap:14px;flex-wrap:wrap;margin-bottom:16px}
.title{font:600 32px/1 var(--font-ui);letter-spacing:.01em}
.sub{color:var(--muted);margin-top:6px}
.actions{display:flex;gap:10px;flex-wrap:wrap}
.btn{border:1px solid var(--border);background:var(--card2);color:var(--txt);padding:10px 14px;border-radius:var(--radius);cursor:pointer;font:600 14px/1 var(--font-ui);letter-spacing:0;transition:all var(--transition);box-shadow:var(--shadow-sm);display:inline-flex;align-items:center;gap:6px;user-select:none}
.btn:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--card2));box-shadow:0 4px 14px var(--glow)}
.btn:active{transform:scale(.97)}
.btn.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:var(--warn)}
.btn.warn:hover{background:var(--warn);color:#fff;border-color:var(--warn);box-shadow:0 4px 14px rgba(255,123,114,.16)}
.layout{display:grid;grid-template-columns:minmax(320px,.92fr) minmax(400px,1.08fr);gap:14px}
.stack{display:grid;gap:14px}
.card{border:1px solid var(--border);border-radius:var(--radius-lg);background:var(--card);padding:18px;box-shadow:var(--shadow-sm);animation:officeFade .16s ease-out both;transition:all var(--transition)}
.card:hover{box-shadow:var(--shadow)}
.card h2{margin:0 0 12px;font:600 18px/1 var(--font-ui);letter-spacing:.01em}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.field{display:grid;gap:6px}
.field label{font:600 12px/1 var(--font-ui);letter-spacing:.01em;color:var(--muted);text-transform:none}
select,input{width:100%;background:var(--card2);color:var(--txt);border:1px solid var(--border);border-radius:var(--radius);padding:10px 12px;font:600 14px/1.35 var(--font-ui);transition:all var(--transition)}
select:focus,input:focus{outline:none;border-color:var(--blue);box-shadow:0 0 0 3px color-mix(in srgb, var(--blue) 24%, transparent)}
.btn-row{display:flex;gap:10px;flex-wrap:wrap}
.btn-group{display:grid;gap:10px}
.status-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:10px}
.status-tile{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
.status-tile .k{font:600 11px/1 var(--font-ui);letter-spacing:.01em;color:var(--muted);text-transform:none}
.status-tile .v{margin-top:8px;font:600 20px/1.1 var(--font-ui)}
.status-tile .s{margin-top:6px;color:var(--muted);font-size:13px;word-break:break-word}
.iface-grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(180px,1fr));gap:10px}
.iface-card{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
.iface-name{font:600 16px/1 var(--font-ui)}
.iface-meta{margin-top:6px;color:var(--muted);font-size:13px;line-height:1.55}
.tag{display:inline-flex;align-items:center;gap:6px;padding:3px 8px;border:1px solid var(--border);border-radius:999px;font:600 12px/1 var(--font-ui);letter-spacing:0}
.tag.ok{color:var(--green);border-color:color-mix(in srgb, var(--green) 34%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--card2))}
.tag.warn{color:var(--warn);border-color:color-mix(in srgb, var(--warn) 34%, var(--border));background:color-mix(in srgb, var(--warn) 8%, var(--card2))}
.status-line{white-space:pre-wrap;color:var(--muted);font-size:13px;line-height:1.6}
pre{margin:0;min-height:360px;max-height:60vh;overflow:auto;background:var(--card2);border:1px solid var(--border);border-radius:4px;padding:14px;color:var(--txt);font:13px/1.55 var(--font-mono)}
@keyframes officeFade{from{opacity:.0;transform:translateY(4px)}to{opacity:1;transform:none}}
@media (max-width:1080px){.layout{grid-template-columns:1fr}.grid,.status-grid{grid-template-columns:1fr}}
</style>
</head><body>
<div class="wrap">
  <div class="topbar">
    <div>
      <div class="title">硬件配置助手</div>
      <div class="sub">查看网卡硬件信息，切换工作模式，并处理采集异常。</div>
    </div>
    <div class="actions">
      <button class="btn" id="btn-back" type="button">返回设置</button>
      <button class="btn" id="btn-theme" type="button" style="display:none">浅色</button>
      <button class="btn" id="btn-refresh" type="button">刷新状态</button>
    </div>
  </div>
  <div class="layout">
    <div class="stack">
      <div class="card">
        <h2>采集状态</h2>
        <div class="status-grid">
          <div class="status-tile"><div class="k">采集状态</div><div class="v" id="tile-state">-</div><div class="s" id="tile-msg">-</div></div>
          <div class="status-tile"><div class="k">当前网卡</div><div class="v" id="tile-active-iface">-</div><div class="s" id="tile-selected-iface">默认/未设置</div></div>
          <div class="status-tile"><div class="k">当前信道</div><div class="v" id="tile-channel">-</div><div class="s" id="tile-extra">-</div></div>
        </div>
        <div id="status" class="status-line" style="margin-top:12px">-</div>
      </div>
      <div class="card">
        <h2>网卡控制</h2>
        <div class="grid">
          <div class="field"><label for="iface">目标网卡</label><select id="iface"><option value="">请选择默认网卡</option></select></div>
          <div class="field"><label for="channel">目标信道</label><input id="channel" type="number" min="1" max="196" value="6"></div>
        </div>
        <div class="btn-group" style="margin-top:14px">
          <div class="btn-row">
            <button class="btn" id="btn-iw-dev" type="button">查看 iw dev</button>
            <button class="btn" id="btn-iw-info" type="button">查看 iw info</button>
            <button class="btn" id="btn-iw-link" type="button">查看 iw link</button>
          </div>
          <div class="btn-row">
            <button class="btn" id="btn-set-monitor" type="button">切换为监控模式</button>
            <button class="btn" id="btn-set-managed" type="button">切换为托管模式</button>
            <button class="btn" id="btn-set-channel" type="button">应用目标信道</button>
          </div>
          <div class="btn-row">
            <button class="btn" id="btn-restart-iface" type="button">重启网卡</button>
            <button class="btn warn" id="btn-restart-program" type="button">重启主程序</button>
          </div>
        </div>
      </div>
      <div class="card">
        <h2>网卡总览</h2>
        <div id="iface-grid" class="iface-grid"></div>
      </div>
    </div>
    <div class="stack">
      <div class="card">
        <h2>命令输出</h2>
        <pre id="output">-</pre>
      </div>
    </div>
  </div>
</div>
<script>
function qs(id){ return document.getElementById(id); }
function esc(v){ return String(v==null?'':v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function showStatus(s){ qs('status').textContent = String(s||'-'); }
function showOut(t){ qs('output').textContent = String(t||'-'); }
function loadTheme(){
  try{
    var s = localStorage.getItem('rid_ui_theme');
    if(s === 'dark' || s === 'light') return s;
  }catch(_e){}
  if(window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches) return 'light';
  return 'dark';
}
function applyTheme(theme){
  var light = (theme === 'light');
  document.body.classList.toggle('theme-light', light);
  document.body.classList.toggle('theme-dark', !light);
  try{ localStorage.setItem('rid_ui_theme', light ? 'light' : 'dark'); }catch(_e){}
  qs('btn-theme').textContent = light ? '深色' : '浅色';
}
function apiUrl(url){
  const u = String(url || '');
  try{
    return new URL(u, window.location.origin).toString();
  }catch(_e){
    return u;
  }
}
let authRedirecting = false;
function authExpired(r, d){
  const err = String((d && d.error) || '');
  return r && r.status === 401 && (!!(d && d.auth_expired) || err === 'login required' || err === 'auth required');
}
function redirectLogin(){
  if(authRedirecting) return;
  authRedirecting = true;
  location.href = '/login?next=/';
}
async function getJson(url){
  const r = await fetch(apiUrl(url), {cache:'no-store', headers:{'X-LightRID-Page':'1'}});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
async function postJson(url, body){
  const r = await fetch(apiUrl(url), {method:'POST', headers:{'Content-Type':'application/json','X-LightRID-Page':'1'}, body:JSON.stringify(body||{})});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
function curIface(){ return String(qs('iface').value || '').trim(); }
function fmtOpResult(d){
  if(!d) return '-';
  if(Array.isArray(d.steps)){
    return d.steps.map((x, i)=>`[${i+1}] ${x.cmd}\\ncode=${x.code}\\n${x.stdout||''}\\n${x.stderr||''}`).join('\\n\\n');
  }
  if(typeof d.stdout === 'string' || typeof d.stderr === 'string'){
    return `cmd: ${d.cmd||'-'}\\ncode: ${d.code}\\n\\n${d.stdout||''}${(d.stderr?('\\n'+d.stderr):'')}`;
  }
  return JSON.stringify(d, null, 2);
}
function renderIfaceGrid(items){
  const root = qs('iface-grid');
  const arr = Array.isArray(items) ? items : [];
  if(!root) return;
  if(!arr.length){
    root.innerHTML = '<div class="iface-card"><div class="iface-name">未发现网卡</div><div class="iface-meta">请检查 USB 网卡、驱动与权限。</div></div>';
    return;
  }
  root.innerHTML = arr.map(it=>{
    const mode = String(it.mode || '-');
    const band = it.supports_5g ? '2.4G / 5G' : '2.4G';
    const monitor = mode.toLowerCase().indexOf('monitor') >= 0;
    const model = String(it.model || it.driver || '未知型号');
    const driver = String(it.driver || '-');
    const state = (it.admin_up === false ? '已禁用' : String(it.state || '-'));
    return '<div class="iface-card">'
      +'<div class="iface-name">'+esc(it.name || '-')+'</div>'
      +'<div style="margin-top:10px"><span class="tag '+(monitor ? 'ok' : 'warn')+'">'+(monitor ? '监控模式' : '非监控模式')+'</span></div>'
      +'<div class="iface-meta">型号: '+esc(model)+'<br>驱动: '+esc(driver)+'<br>状态: '+esc(state)+'<br>模式: '+esc(mode)+'<br>频段: '+esc(band)+'<br>5G: '+(it.supports_5g ? '支持' : '未检测到')+'</div>'
      +'</div>';
  }).join('');
}
async function refreshStatus(){
  try{
    const d = await getJson('/api/hw/status');
    const items = Array.isArray(d.items) ? d.items : [];
    const sel = qs('iface');
    const old = sel.value;
    sel.innerHTML = '<option value="">请选择固定网卡</option>' + items.map(it=>{
      const n = String(it.name||'');
      const m = String(it.mode||'');
      const model = String(it.model || it.driver || '');
      const g = it.supports_5g ? '5G' : '2.4G';
      return `<option value="${esc(n)}">${esc(n)} [${esc(m || 'net')}] ${esc(model || g)}</option>`;
    }).join('');
    if(old) sel.value = old;
    const snf = d.sniff_state || {};
    qs('tile-state').textContent = String(snf.state || '-');
    qs('tile-msg').textContent = String(snf.msg || '-');
    qs('tile-active-iface').textContent = String(d.active_iface || '-');
    qs('tile-selected-iface').textContent = '选择: ' + String(curIface() || '未绑定');
    qs('tile-channel').textContent = String((snf.channel || d.current_channel || '-') || '-');
    qs('tile-extra').textContent = '网卡数: ' + String(items.length || 0);
    showStatus(`采集网卡: ${d.active_iface||'-'}\n状态: ${snf.state||'-'}\n说明: ${snf.msg||'-'}`);
    renderIfaceGrid(items);
    showOut(JSON.stringify(d, null, 2));
  }catch(e){
    showStatus('刷新失败: ' + (e.message || e));
  }
}
async function runOp(op, ext){
  try{
    showStatus('执行中: ' + op);
    const body = Object.assign({op: op, iface: curIface()}, ext||{});
    const d = await postJson('/api/hw/op', body);
    showStatus('完成: ' + op + (d.ok ? ' (OK)' : ' (FAILED)'));
    showOut(fmtOpResult(d));
    if(op === 'restart_program'){ setTimeout(refreshStatus, 1200); }
  }catch(e){
    showStatus('执行失败: ' + (e.message || e));
  }
}
qs('btn-back').addEventListener('click', ()=>{ location.href = '/settings'; });
qs('btn-theme').addEventListener('click', ()=>applyTheme(document.body.classList.contains('theme-light') ? 'dark' : 'light'));
qs('btn-refresh').addEventListener('click', refreshStatus);
qs('btn-iw-dev').addEventListener('click', ()=>runOp('iw_dev'));
qs('btn-iw-info').addEventListener('click', ()=>runOp('iw_info'));
qs('btn-iw-link').addEventListener('click', ()=>runOp('iw_link'));
qs('btn-set-monitor').addEventListener('click', ()=>runOp('set_monitor'));
qs('btn-set-managed').addEventListener('click', ()=>runOp('set_managed'));
qs('btn-restart-iface').addEventListener('click', ()=>runOp('restart_iface'));
qs('btn-set-channel').addEventListener('click', ()=>runOp('set_channel', {channel: Number(qs('channel').value||0)}));
qs('btn-restart-program').addEventListener('click', ()=>{
  if(confirm('确认重启主程序？')) runOp('restart_program');
});
applyTheme(loadTheme());
refreshStatus();
</script>
</body></html>"""

_MAIN_PAGE_PATCH_CSS = r"""
:root{
  --app-vh:100dvh;
  --rid-home-header-height:108px;
  --rid-home-content-height:calc(var(--app-vh) - var(--rid-home-header-height));
}
header.app-shell-header{
  margin:12px 12px 0;
  padding:10px 12px;
  display:flex;
  align-items:center;
  gap:10px;
  flex-wrap:nowrap;
  overflow-x:visible;
  overflow-y:visible;
  white-space:nowrap;
  background:var(--panel);
  border:1px solid var(--border);
  border-radius:var(--radius);
  box-shadow:var(--shadow-sm);
}
header.app-shell-header::-webkit-scrollbar{height:6px}
.main-shell-top{
  display:flex;
  align-items:center;
  gap:10px;
  flex:1 1 auto;
  min-width:0;
}
.main-title-block{
  min-width:0;
  display:flex;
  align-items:center;
  gap:10px;
}
header.app-shell-header h1{
  margin:0;
  font:600 20px/1 var(--font-ui);
  letter-spacing:.01em;
  color:var(--txt);
  text-transform:none;
  white-space:nowrap;
}
.main-title-sub{
  display:none;
}
.main-head-side{
  display:flex;
  align-items:center;
  gap:8px;
  justify-content:flex-end;
  min-width:0;
  flex:1 1 auto;
}
.main-menu-actions{
  display:flex;
  gap:8px;
  flex-wrap:nowrap;
  justify-content:flex-end;
  position:relative;
}
.main-live-stats{
  display:flex;
  gap:8px;
  flex-wrap:nowrap;
  justify-content:flex-end;
}
.main-live-stats .stat{
  border:1px solid var(--border);
  border-radius:4px;
  background:var(--panel2);
  padding:6px 10px;
  color:var(--txt);
  box-shadow:0 1px 2px rgba(0,0,0,.05);
  font-size:13px;
  white-space:nowrap;
}
.main-live-stats .stat b{font-weight:700}
.app-tab-nav{
  display:inline-grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:3px;padding:3px;
  width:auto;min-width:188px;margin:0;
  border:1px solid var(--border);background:var(--panel2);border-radius:var(--radius);
  box-shadow:var(--shadow-sm)
}
.main-more-menu{position:relative;display:inline-flex}
.main-more-pop{position:absolute;right:0;top:calc(100% + 8px);display:none;min-width:170px;padding:8px;border:1px solid var(--border);border-radius:14px;background:var(--panel);box-shadow:0 12px 28px rgba(15,23,42,.10);z-index:45}
.main-more-menu.open .main-more-pop{display:grid;gap:6px}
.main-more-pop .header-link-btn{width:100%;text-align:left;box-shadow:none}
.app-tab-btn,.header-link-btn,.btn-mini,.icon-btn,.info-card-close{
  border:1px solid var(--border);
  background:var(--panel2);
  color:var(--txt);
  border-radius:9px;
  font:600 14px/1 var(--font-ui);
  letter-spacing:0;
  cursor:pointer;
  transition:background-color 160ms ease,border-color 160ms ease,color 160ms ease,box-shadow 160ms ease,transform 160ms ease;
  box-shadow:var(--shadow-sm);
}
.app-tab-btn,.header-link-btn,.btn-mini{
  padding:8px 14px;
  text-align:center;
  white-space:nowrap;
}
.icon-btn,.info-card-close{
  width:28px;
  height:28px;
  display:inline-flex;
  align-items:center;
  justify-content:center;
  padding:0;
}
.app-tab-btn:hover,.header-link-btn:hover,.btn-mini:hover,.icon-btn:hover,.info-card-close:hover{
  transform:translateY(-1px);
  border-color:var(--blue);
  background:color-mix(in srgb, var(--blue) 10%, var(--panel2));
  box-shadow:0 4px 14px var(--glow);
}
.app-tab-btn:active,.header-link-btn:active,.btn-mini:active,.icon-btn:active,.info-card-close:active{transform:scale(.97)}
.app-tab-btn.active{
  border-color:var(--blue);
  background:color-mix(in srgb, var(--blue) 10%, var(--panel2));
  color:var(--txt);
  box-shadow:inset 0 0 0 1px color-mix(in srgb, var(--blue) 18%, transparent)
}
.btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:var(--warn)}
.btn-mini.warn:hover{background:var(--warn);color:#fff;border-color:var(--warn);box-shadow:0 4px 14px rgba(255,123,114,.18)}
body.theme-light .app-tab-nav{background:var(--panel2);box-shadow:0 1px 2px rgba(15,23,42,.05)}
body.theme-light .app-tab-btn:hover,body.theme-light .header-link-btn:hover,body.theme-light .btn-mini:hover,body.theme-light .icon-btn:hover,body.theme-light .info-card-close:hover{background:color-mix(in srgb, var(--blue) 8%, var(--panel2));border-color:var(--blue);box-shadow:0 2px 8px var(--glow)}
body.theme-light .app-tab-btn.active{
  background:color-mix(in srgb, var(--blue) 12%, var(--panel2));
  color:var(--txt);border-color:var(--blue);box-shadow:inset 0 0 0 1px color-mix(in srgb, var(--blue) 20%, transparent)
}
body.theme-light header.app-shell-header{
  background:var(--panel);
}
body.theme-light .main-live-stats .stat{background:var(--panel2)}
body.theme-light .btn-mini,body.theme-light .header-link-btn,body.theme-light .app-tab-btn,body.theme-light .icon-btn,body.theme-light .info-card-close{
  background:var(--panel2);
  border-color:var(--border);
  color:var(--txt);
}
body.theme-light .btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 40%, var(--border));color:var(--warn)}
body.app-paged{grid-template-rows:auto minmax(0,1fr) auto}
.app-pages{min-height:0;padding:0 14px 10px;display:block;height:max(320px,var(--rid-home-content-height))}
.app-page{display:none;min-height:0;height:100%}
body[data-page="live"] .app-page[data-page="live"],
body[data-page="history"] .app-page[data-page="history"]{display:block}
.live-layout{display:grid;grid-template-columns:minmax(340px,30vw) minmax(0,1fr);gap:14px;height:100%;min-height:0}
.live-card-panel{border:1px solid color-mix(in srgb,var(--border) 92%,transparent);background:var(--panel);border-radius:18px;box-shadow:var(--shadow-sm);display:flex;flex-direction:column;min-height:0;overflow:hidden}
.live-card-head{padding:14px 16px;border-bottom:1px solid color-mix(in srgb,var(--border) 84%,transparent);font:700 14px/1 var(--font-ui);color:var(--txt);display:flex;justify-content:space-between;gap:10px;background:var(--panel2)}
.live-card-list{padding:12px;display:grid;gap:10px;overflow:auto;min-height:0;align-content:start}
.live-card{border:1px solid color-mix(in srgb,var(--border) 88%,transparent);background:var(--panel2);border-radius:14px;padding:14px;display:grid;gap:10px;cursor:pointer;transition:background-color 120ms ease,border-color 120ms ease,box-shadow 120ms ease}
.live-card:hover{border-color:color-mix(in srgb,var(--blue) 18%,var(--border));box-shadow:0 4px 10px rgba(15,23,42,.05)}
.live-card.selected{
  border-color:color-mix(in srgb,var(--selected-border) 88%,var(--border));
  background:var(--selected-surface-card);
  box-shadow:inset 3px 0 0 var(--blue)
}
.live-card.selected .live-card-pick,
.live-card.selected .live-card-state,
.live-card.selected .live-card-snrow .label,
.live-card.selected .live-card-item .k,
.live-card.selected .live-card-foot{color:var(--selected-muted)}
.live-card.selected .icon-btn{
  background:color-mix(in srgb, var(--selected-surface-card) 58%, var(--panel2));
  border-color:color-mix(in srgb, var(--selected-border) 75%, var(--border));
  color:var(--selected-muted);
}
.live-card.selected .icon-btn:hover{color:var(--txt)}
.live-card.lost{opacity:.72}
.live-card.alarm-zone{border-color:rgba(255,79,79,.78);background:color-mix(in srgb, #ff3b30 10%, var(--panel2));animation:alarmRowPulse .9s ease-in-out infinite alternate}
.live-card-top{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:10px;align-items:start}
.live-card-title{font:700 20px/1.12 var(--font-ui);letter-spacing:.01em;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.live-card-actions{display:flex;align-items:center;gap:8px;flex-wrap:wrap;justify-content:flex-end}
.live-card-pick{display:inline-flex;align-items:center;gap:6px;color:var(--dim);font-size:12px}
.live-card-state{display:inline-flex;align-items:center;padding:4px 8px;border:1px solid color-mix(in srgb,var(--border) 86%,transparent);border-radius:9px;font:600 11px/1 var(--font-ui);color:var(--dim)}
.live-card-state.live{color:var(--green);border-color:rgba(22,163,74,.22);background:rgba(220,252,231,.9)}
.live-card-state.lost{color:var(--warn);border-color:rgba(239,68,68,.20);background:rgba(254,226,226,.88)}
.live-card-state.firmware{color:var(--blue);border-color:rgba(37,99,235,.18);background:rgba(219,234,254,.9)}
.live-card-state.alarm{color:#c2410c;border-color:rgba(245,158,11,.24);background:rgba(255,247,237,.96)}
.live-card-snrow{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:8px;align-items:center}
.live-card-snrow .label{font-size:11px;color:var(--dim);letter-spacing:.04em;text-transform:uppercase}
.live-card-sntext{font:700 13px/1.25 var(--font-mono);min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.live-card-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px}
.live-card-item{border:1px solid color-mix(in srgb, var(--border) 84%, transparent);border-radius:12px;padding:9px 10px;background:color-mix(in srgb, var(--surface-tonal) 48%, white)}
.live-card-item .k{font-size:11px;color:var(--dim);line-height:1;text-transform:uppercase;letter-spacing:.04em}
.live-card-item .v{margin-top:6px;font:600 13px/1.35 var(--font-ui);word-break:break-word}
.live-card-foot{display:flex;justify-content:space-between;gap:8px;flex-wrap:wrap;color:var(--dim);font-size:12px}
.live-map-slot{min-height:0;height:100%;display:flex;flex-direction:column}
.live-map-slot .panel{height:100%}
.live-map-slot #map{height:100%}
.history-layout{display:grid;grid-template-rows:minmax(240px,1fr) minmax(240px,1fr);gap:14px;height:100%;min-height:0}
.history-table-slot,.history-map-slot{min-height:0;display:flex;flex-direction:column}
.history-table-slot .tbl-wrap,.history-map-slot .panel{height:100%;min-height:0}
.history-table-slot .tbl-wrap{overflow:auto}
.history-table-slot .tbl-wrap table{min-width:100%}
.history-map-slot #map{height:100%}
.track-sel-wrap{gap:6px}
.track-color-chip{display:inline-block;width:10px;height:10px;border-radius:50%;background:var(--track-color,#1f9dff);box-shadow:0 0 0 2px color-mix(in srgb, var(--track-color,#1f9dff) 24%, transparent);flex:0 0 auto}
.track-replay-card{
  display:none;
  position:absolute;
  right:16px;
  top:68px;
  bottom:14px;
  z-index:1200;
  width:clamp(260px,25%,360px);
  border:1px solid color-mix(in srgb,var(--border) 88%,transparent);
  border-radius:18px;
  background:var(--panel);
  backdrop-filter:blur(12px);
  box-shadow:var(--shadow-lg);
  padding:16px;
  overflow:auto;
}
#map-panel.history-mounted .track-replay-card{display:block}
.track-replay-head{display:flex;justify-content:space-between;align-items:flex-start;gap:10px;margin-bottom:10px}
.track-replay-title{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.track-replay-sub,.track-replay-status{margin-top:5px;color:var(--dim);font-size:12px;line-height:1.45}
.track-replay-card .input-mini{width:100%;height:36px;border:1px solid color-mix(in srgb,var(--border) 84%,transparent);background:color-mix(in srgb,var(--panel2) 96%,white);color:var(--txt);border-radius:12px;padding:6px 10px;font:600 13px/1.2 var(--font-ui);margin-bottom:10px}
.track-replay-time{border:1px solid color-mix(in srgb,var(--border) 84%,transparent);border-radius:14px;background:color-mix(in srgb,var(--surface-tonal) 42%,white);padding:10px 12px;font-size:12px;line-height:1.45;color:var(--txt);margin-bottom:10px;white-space:pre-line}
.track-replay-ranges{display:grid;gap:8px;margin:10px 0}
.track-replay-ranges input{width:100%;accent-color:var(--blue)}
.track-replay-controls{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.track-speed-label{display:grid;grid-template-columns:auto minmax(110px,1fr) 42px;align-items:center;gap:7px;color:var(--dim);font-size:12px;flex:1 1 190px;min-width:0}
.track-speed-label input{width:100%;accent-color:var(--blue)}
.track-speed-value{font:700 12px/1 var(--font-mono);color:var(--txt);text-align:right}
#map-panel.fullscreen .track-replay-card{right:350px;bottom:auto;max-height:calc(100vh - 82px)}
#map-panel.fullscreen .map-mini-list{max-height:calc(100vh - 82px)}
.app-page[data-page="ops"]{display:none!important}
.app-page[data-page="ops"] .bottom .panel .logbox,
.app-page[data-page="ops"] .bottom .panel .aplist{flex:1;min-height:0;max-height:none}
#map-panel-toggle,#log-panel-toggle,#ap-panel-toggle,#bottom-restore{display:none!important}
#map-panel .panel-hdr,#log-panel .panel-hdr,#ap-panel .panel-hdr{cursor:default!important}
.app-page .panel{border-radius:16px;box-shadow:var(--shadow-sm);animation:officeFade .16s ease-out both}
.app-page .panel-hdr{font-size:13px;letter-spacing:.01em}
.tbl-wrap,.app-page .panel,.map-mini-list{
  border-radius:16px;
}
.tbl-wrap{
  box-shadow:0 1px 3px rgba(0,0,0,.08);
}
.app-page .panel{
  border:1px solid var(--border);
  background:var(--panel);
}
.app-page .panel-hdr{
  padding:12px 14px;
  border-bottom:1px solid var(--border);
  color:var(--txt);
}
.app-page .panel-hdr .sub{color:var(--dim)}
.app-page .panel-hdr label{color:var(--dim)}
.app-page .panel.map-panel{position:relative}
.zone-alarm{
  position:fixed;inset:18px;display:none;z-index:9996;border:2px solid rgba(255,79,79,.92);
  border-radius:4px;box-shadow:0 0 0 999px rgba(255,0,0,.12), inset 0 0 0 1px rgba(255,80,80,.18);
  pointer-events:none;align-items:center;justify-content:center;padding:24px;text-align:center;
  background:rgba(255,90,90,.06);
}
.zone-alarm.show{display:flex;animation:zonePulse 1.15s ease-in-out infinite alternate}
.zone-alarm-card{backdrop-filter:blur(8px);background:color-mix(in srgb, var(--panel) 92%, transparent);border:1px solid rgba(255,96,96,.75);border-radius:4px;padding:26px 28px;max-width:min(640px,88vw);box-shadow:0 18px 28px rgba(0,0,0,.18)}
.zone-alarm-title{font:600 34px/1 var(--font-ui);color:#ff7b7b;letter-spacing:.06em;margin-bottom:10px}
.zone-alarm-text{font:500 18px/1.55 var(--font-ui);color:#ffe8e8}
body.zone-alert-active header.app-shell-header,body.zone-alert-active header{box-shadow:0 0 0 2px rgba(255,79,79,.42),0 8px 22px rgba(255,0,0,.16)}
@keyframes zonePulse{from{transform:scale(1);opacity:.92}to{transform:scale(1.01);opacity:1}}
.info-sections{display:grid;gap:14px}
.info-block{border:1px solid var(--border);border-radius:4px;padding:14px;background:var(--panel2);box-shadow:0 1px 2px rgba(0,0,0,.04)}
.info-block h3{font:600 15px/1 var(--font-ui);letter-spacing:.01em;margin-bottom:12px;color:var(--txt)}
.info-actions{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:12px}
.info-actions .btn-mini{padding:7px 12px}
.detail-reparse-box{display:flex;align-items:center;gap:8px;flex-wrap:wrap;margin:0 0 12px;padding:10px 12px;border:1px solid color-mix(in srgb,var(--yellow) 36%,var(--border));border-radius:4px;background:color-mix(in srgb,var(--yellow) 8%,var(--panel2));font:600 13px/1.4 var(--font-ui)}
.detail-reparse-box select{min-width:150px;background:var(--panel);color:var(--txt);border:1px solid var(--border);border-radius:4px;padding:6px 8px}
.detail-reparse-status{flex:1 1 100%;color:var(--muted);font-size:12px}
.info-model-cell{display:flex;align-items:center;gap:8px;flex-wrap:wrap}
.info-model-na{font:700 13px/1 var(--font-mono);color:var(--dim)}
.model-row-actions{display:inline-flex;gap:6px;flex-wrap:wrap;vertical-align:middle}
.model-row-actions .btn-mini{padding:5px 8px;font-size:12px;line-height:1.1}
@keyframes officeFade{from{opacity:0;transform:translateY(4px)}to{opacity:1;transform:none}}
@media (max-width: 960px){
  header.app-shell-header{gap:8px}
  .app-tab-nav{min-width:188px}
  .live-layout{grid-template-columns:1fr;height:auto}
  .live-card-panel{max-height:40vh}
  .history-layout{grid-template-rows:minmax(220px,1fr) minmax(300px,1fr);height:auto}
  .history-table-slot .tbl-wrap{height:auto;max-height:max(260px,var(--rid-home-content-height))}
  .track-replay-card{left:10px;right:10px;top:auto;bottom:10px;width:auto;max-height:42%}
  #map-panel.fullscreen .track-replay-card{left:10px;right:10px;top:auto;bottom:10px;max-height:34vh}
  #map-panel.fullscreen .map-mini-list{right:10px;top:62px;max-height:calc(66vh - 82px)}
  body[data-page="live"] .live-map-slot .panel{height:max(360px,calc(var(--rid-home-content-height) - 40vh - 14px))}
  .main-shell-top,.main-head-side,.main-menu-actions,.main-live-stats{gap:6px}
  header.app-shell-header h1{font-size:18px}
}
@media (max-width: 720px){
  .live-card-grid{grid-template-columns:1fr}
  .live-card-title{font-size:17px}
}
.rid-toast-host{position:fixed;right:18px;bottom:84px;z-index:10000;display:flex;flex-direction:column;gap:8px;pointer-events:none;max-width:min(360px,calc(100vw - 28px))}
.rid-toast{display:grid;grid-template-columns:4px minmax(0,1fr);gap:10px;align-items:start;padding:12px 14px;border-radius:var(--radius);background:color-mix(in srgb,var(--panel) 96%,transparent);border:1px solid var(--border);box-shadow:0 10px 22px rgba(15,23,42,.10);animation:toastIn .3s ease-out;pointer-events:auto;cursor:pointer}
.rid-toast.out{animation:toastOut .26s ease-in forwards}
.rid-toast-bar{width:4px;height:100%;min-height:24px;border-radius:999px;background:var(--blue)}
.rid-toast.success .rid-toast-bar{background:var(--green)}
.rid-toast.error .rid-toast-bar{background:var(--warn)}
.rid-toast.warn .rid-toast-bar{background:var(--yellow)}
.rid-toast-msg{font:600 13px/1.4 var(--font-ui);color:var(--txt);white-space:pre-wrap;word-break:break-word}
@keyframes toastIn{0%{opacity:0;transform:translateX(40px)}100%{opacity:1;transform:translateX(0)}}
@keyframes toastOut{0%{opacity:1;transform:translateX(0)}100%{opacity:0;transform:translateX(40px)}}
"""

_MAIN_PAGE_PATCH_JS = r"""
(function(){
  var PAGE_COOKIE='rid_home_page';
  var pageReady=false;
  var alarmRects=[];
  var alarmOverlayHideTimer=null;
  var detailReparseModeCache={};
  var alarmLastSig='';
  /* ---- Toast notification system ---- */
  window._ridToasts=[];
  window.showToast=function(msg,kind,ms){
    kind=String(kind||'info');ms=Number(ms)||2800;
    var t={id:Date.now()+Math.random(),msg:String(msg||''),kind:kind};
    window._ridToasts.push(t);
    renderToasts();
    setTimeout(function(){dismissToast(t.id);},ms);
  };
  function dismissToast(id){
    var el=document.getElementById('rid-toast-'+id);
    if(el){el.classList.add('out');setTimeout(function(){if(el.parentNode)el.parentNode.removeChild(el);},280);}
    window._ridToasts=window._ridToasts.filter(function(t){return t.id!==id;});
  }
  function renderToasts(){
    var host=document.getElementById('rid-toast-host');
    if(!host){
      host=document.createElement('div');host.id='rid-toast-host';host.className='rid-toast-host';
      document.body.appendChild(host);
    }
    var html='';
    window._ridToasts.forEach(function(t){
      html+='<div class="rid-toast '+t.kind+'" id="rid-toast-'+t.id+'"><span class="rid-toast-bar"></span><span class="rid-toast-msg">'+String(t.msg).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')+'</span></div>';
    });
    host.innerHTML=html;
  }
  /* ---- End Toast ---- */
  function syncHomeViewport(){
    var vp = window.visualViewport;
    var vh = Math.max(320, Math.round((vp && vp.height) ? vp.height : window.innerHeight || 0));
    document.documentElement.style.setProperty('--app-vh', vh + 'px');
    var header = document.querySelector('header.app-shell-header') || document.querySelector('header');
    var headerBudget = 108;
    if(header && header.getBoundingClientRect){
      var rect = header.getBoundingClientRect();
      var cs = window.getComputedStyle(header);
      headerBudget = Math.ceil(rect.top + rect.height + (parseFloat(cs.marginBottom) || 0) + 14);
    }
    var contentH = Math.max(320, vh - headerBudget);
    document.documentElement.style.setProperty('--rid-home-header-height', headerBudget + 'px');
    document.documentElement.style.setProperty('--rid-home-content-height', contentH + 'px');
    if(map){
      setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 40);
    }
  }
  function ensureZoneOverlay(){
    var el = document.getElementById('zone-alarm');
    if(el) return el;
    el = document.createElement('div');
    el.id = 'zone-alarm';
    el.className = 'zone-alarm';
    el.innerHTML = '<div class="zone-alarm-card"><div class="zone-alarm-title">当前有飞机侵入报警区域</div><div id="zone-alarm-text" class="zone-alarm-text">请查看地图和列表中的报警标记</div></div>';
    document.body.appendChild(el);
    return el;
  }
  function navSet(page){
    var p = (page === 'history') ? 'history' : 'live';
    if(p === 'live' && isMapFullscreen()){
      try{
        if(document.exitFullscreen) document.exitFullscreen();
        else if(document.webkitExitFullscreen) document.webkitExitFullscreen();
      }catch(_e){}
    }
    if(p !== 'history' && (replayState.playing || replaySyncPaused || replayState.sn || (replayState.points || []).length)) clearReplaySelection({render:false});
    document.body.setAttribute('data-page', p);
    cookieSet(PAGE_COOKIE, p, 365);
    if(p === 'history') applyHistoryDefaultSelection(latestDroneRows);
    var tabs = document.querySelectorAll('.app-tab-btn');
    for(var i=0;i<tabs.length;i++){
      tabs[i].classList.toggle('active', tabs[i].getAttribute('data-page') === p);
    }
    mountMainMapPanel(p);
    displayTrackSnList(p, latestDroneRows).forEach(function(sn){ ensureTrackLoaded(sn, false); });
    refreshReplayBounds(true);
    if(p === 'live'){
      setTimeout(function(){ if(map) map.invalidateSize(false); }, 80);
    }
    renderLiveCards(latestDroneRows);
    renderMapMiniList(latestDroneRows);
    syncTableSelectionUi();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    syncHomeViewport();
  }
  window.__ridNavSet = navSet;
  function mountMainMapPanel(page){
    var panel = qs('map-panel');
    var liveSlot = qs('live-map-slot');
    var historySlot = qs('history-map-slot');
    if(!panel || !liveSlot || !historySlot) return;
    var target = (page === 'history') ? historySlot : liveSlot;
    if(panel.parentNode !== target){
      target.appendChild(panel);
    }
    panel.classList.toggle('history-mounted', page === 'history');
    panel.classList.toggle('live-mounted', page !== 'history');
    ensureTrackReplayCard();
    renderReplayCard();
    updateMapFullscreenButton();
    if(map){
      setTimeout(function(){ try{ map.invalidateSize(false); }catch(_e){} }, 40);
    }
  }
  function neutralizeCollapseHeader(hdr){
    if(!hdr || hdr.getAttribute('data-no-collapse') === '1') return;
    hdr.setAttribute('data-no-collapse', '1');
    hdr.style.cursor = 'default';
    hdr.addEventListener('click', function(ev){
      var t = ev.target;
      if(t && t.closest && t.closest('button,input,label,a,select,textarea')) return;
      ev.stopImmediatePropagation();
    }, true);
  }
  function neutralizeLegacyCollapsers(){
    ['map-panel','log-panel','ap-panel'].forEach(function(id){
      var panel = qs(id);
      if(!panel || !panel.querySelector) return;
      neutralizeCollapseHeader(panel.querySelector('.panel-hdr'));
    });
  }
  function ensureHeaderChrome(){
    var header = document.querySelector('header');
    if(!header) return;
    header.classList.add('app-shell-header');
    var title = header.querySelector('h1');
    if(title && !qs('main-title-sub')){
      var titleBlock = document.createElement('div');
      titleBlock.className = 'main-title-block';
      title.parentNode.insertBefore(titleBlock, title);
      titleBlock.appendChild(title);
      var versionLabel = header.querySelector('.app-version-label');
      if(versionLabel) titleBlock.appendChild(versionLabel);
      var sub = document.createElement('div');
      sub.id = 'main-title-sub';
      sub.className = 'main-title-sub';
      sub.textContent = '地图、列表、日志。';
      titleBlock.appendChild(sub);
    }
    var statsWrap = header.querySelector('.head-stats');
    if(statsWrap && !qs('main-shell-top')){
      var titleBlockNode = header.querySelector('.main-title-block') || title;
      var top = document.createElement('div');
      top.id = 'main-shell-top';
      top.className = 'main-shell-top';
      var side = document.createElement('div');
      side.id = 'main-head-side';
      side.className = 'main-head-side';
      var actions = document.createElement('div');
      actions.id = 'main-menu-actions';
      actions.className = 'main-menu-actions';
      var stats = document.createElement('div');
      stats.id = 'main-live-stats';
      stats.className = 'main-live-stats';
      var children = Array.prototype.slice.call(statsWrap.children || []);
      children.forEach(function(node){
        if(!node) return;
        if(String(node.tagName || '').toUpperCase() === 'BUTTON'){
          node.classList.add('header-link-btn');
          actions.appendChild(node);
        }else{
          stats.appendChild(node);
        }
      });
      side.appendChild(actions);
      side.appendChild(stats);
      top.appendChild(titleBlockNode);
      top.appendChild(side);
      header.insertBefore(top, header.firstChild);
      if(statsWrap.parentNode) statsWrap.parentNode.removeChild(statsWrap);
    }else if(statsWrap){
      Array.prototype.slice.call(statsWrap.children || []).forEach(function(node){
        if(String(node.tagName || '').toUpperCase() === 'BUTTON'){
          node.classList.add('header-link-btn');
        }
      });
    }
  }
  function ensureMainPages(){
    var header = document.querySelector('header');
    if(header && !qs('app-tab-nav')){
      var nav = document.createElement('div');
      nav.id = 'app-tab-nav';
      nav.className = 'app-tab-nav';
      nav.innerHTML =
        '<button class="app-tab-btn" data-page="live" type="button">实时</button>'+
        '<button class="app-tab-btn" data-page="history" type="button">历史记录</button>';
      nav.addEventListener('click', function(ev){
        var btn = ev.target && ev.target.closest ? ev.target.closest('.app-tab-btn') : null;
        if(!btn) return;
        navSet(btn.getAttribute('data-page') || 'live');
      });
      (qs('main-head-side') || header).appendChild(nav);
    }
    var clearBtn = qs('btn-clear-history');
    var actions = qs('main-menu-actions') || (clearBtn ? clearBtn.parentNode : null);
    if(actions && !qs('main-more-menu')){
      var menu = document.createElement('div');
      menu.id = 'main-more-menu';
      menu.className = 'main-more-menu';
      menu.innerHTML = '<button class="btn-mini header-link-btn" id="btn-main-more" type="button">更多</button><div class="main-more-pop" id="main-more-pop"></div>';
      actions.appendChild(menu);
      var pop = qs('main-more-pop');
      [['btn-settings','设置','/settings'], ['btn-logs','日志','/logs']].forEach(function(item){
        var b = document.createElement('button');
        b.id = item[0];
        b.className = 'btn-mini header-link-btn';
        b.type = 'button';
        b.textContent = item[1];
        b.addEventListener('click', function(){ location.href = item[2]; });
        pop.appendChild(b);
      });
      qs('btn-main-more').addEventListener('click', function(ev){
        ev.stopPropagation();
        menu.classList.toggle('open');
      });
      document.addEventListener('click', function(){ menu.classList.remove('open'); });
    }
    ['btn-freeze','btn-web-notify','btn-clear-history'].forEach(function(id){
      var node = qs(id);
      if(node && node.parentNode) node.parentNode.removeChild(node);
    });
    var advBtn = qs('btn-adv-open'); if(advBtn && advBtn.parentNode) advBtn.parentNode.removeChild(advBtn);
    var hwBtn = qs('btn-hw-assistant'); if(hwBtn && hwBtn.parentNode) hwBtn.parentNode.removeChild(hwBtn);
    var advModal = qs('adv-modal'); if(advModal && advModal.parentNode) advModal.parentNode.removeChild(advModal);
    try{
      if(typeof setMapPanelCollapsed === 'function') setMapPanelCollapsed(false);
      if(typeof setLogPanelCollapsed === 'function') setLogPanelCollapsed(false);
      if(typeof setApPanelCollapsed === 'function') setApPanelCollapsed(false);
      if(typeof syncBottomPanelLayout === 'function') syncBottomPanelLayout();
    }catch(_e){}
    ensureHeaderChrome();
    neutralizeLegacyCollapsers();
    if(pageReady) return;
    var listWrap = document.querySelector('.tbl-wrap');
    var bottom = document.querySelector('.bottom');
    var mapEl = qs('map');
    var mapPanel = mapEl && mapEl.closest ? mapEl.closest('.panel') : null;
    if(!header || !listWrap || !mapPanel) return;
    document.body.classList.add('app-paged');
    var pages = document.getElementById('app-pages');
    if(!pages){
      pages = document.createElement('div');
      pages.id = 'app-pages';
      pages.className = 'app-pages';
      header.insertAdjacentElement('afterend', pages);
    }
    function ensurePage(name){
      var el = document.querySelector('.app-page[data-page="'+name+'"]');
      if(el) return el;
      el = document.createElement('section');
      el.className = 'app-page';
      el.setAttribute('data-page', name);
      pages.appendChild(el);
      return el;
    }
    var livePage = ensurePage('live');
    var liveLayout = qs('live-layout');
    if(!liveLayout){
      liveLayout = document.createElement('div');
      liveLayout.id = 'live-layout';
      liveLayout.className = 'live-layout';
      liveLayout.innerHTML = '<aside class="live-card-panel"><div class="live-card-head"><span>实时目标</span><span id="live-card-count">0</span></div><div id="live-card-list" class="live-card-list"></div></aside><div id="live-map-slot" class="live-map-slot"></div>';
      livePage.appendChild(liveLayout);
    }
    var historyPage = ensurePage('history');
    var historyLayout = qs('history-layout');
    if(!historyLayout){
      historyLayout = document.createElement('div');
      historyLayout.id = 'history-layout';
      historyLayout.className = 'history-layout';
      historyLayout.innerHTML = '<div id="history-table-slot" class="history-table-slot"></div><div id="history-map-slot" class="history-map-slot"></div>';
      historyPage.appendChild(historyLayout);
    }
    var liveCards = qs('live-card-list');
    if(liveCards && liveCards.getAttribute('data-bound') !== '1'){
      liveCards.setAttribute('data-bound', '1');
      liveCards.addEventListener('click', function(ev){
        var copyBtn = ev.target && ev.target.closest ? ev.target.closest('.copy-sn') : null;
        if(copyBtn){
          ev.preventDefault();
          ev.stopPropagation();
          copySn(copyBtn.getAttribute('data-sn') || '');
          return;
        }
        var cb = ev.target && ev.target.closest ? ev.target.closest('.sel-sn') : null;
        var card = ev.target && ev.target.closest ? ev.target.closest('.live-card[data-sn]') : null;
        if(!card) return;
        var sn = card.getAttribute('data-sn') || '';
        if(cb){
          setSnSelected(sn, !!cb.checked);
          return;
        }
        focusLiveAircraft(sn);
      });
    }
    var historyTableSlot = qs('history-table-slot');
    if(historyTableSlot && listWrap.parentNode !== historyTableSlot){
      historyTableSlot.appendChild(listWrap);
    }
    if(bottom){
      bottom.style.display = 'none';
      bottom.setAttribute('aria-hidden', 'true');
    }
    mountMainMapPanel(cookieGet(PAGE_COOKIE) || 'live');
    pageReady = true;
    syncHomeViewport();
    navSet(cookieGet(PAGE_COOKIE) || 'live');
  }
  function buildInfoSection(title, rows){
    var html = '<section class="info-block"><h3>'+esc(title)+'</h3><div class="info-grid">';
    for(var i=0;i<rows.length;i++){
      if(rows[i][2] === 'html'){
        html += '<div class="info-row"><span class="k">'+esc(rows[i][0])+'</span><span class="v">'+String(rows[i][1] == null ? '' : rows[i][1])+'</span></div>';
      }else{
        html += infoRowHtml(rows[i][0], rows[i][1]);
      }
    }
    html += '</div></section>';
    return html;
  }
  window.exportTrackForSn = async function(sn){
    sn = String(sn || '').trim();
    if(!sn) return;
    var data = await getJson('/api/tools/export/track?sn=' + encodeURIComponent(sn));
    _downloadJsonFile('rid_track_' + sn + '_' + _toolStamp() + '.json', data);
  };
  function cleanModelPrefixFromSn(sn){
    var raw = String(sn || '');
    if(raw.toUpperCase().indexOf('MAC:') === 0) return '';
    return raw.replace(/[^0-9A-Za-z]+/g, '').toUpperCase().slice(0, 8);
  }
  function isUnknownModel(model){
    var v = String(model || '').trim().toUpperCase();
    return !v || v === 'N/A' || v === 'NA' || v === '-';
  }
  function isMissingDetailValue(v){
    if(v == null) return true;
    var s = String(v).trim().toUpperCase();
    return !s || s === 'N/A' || s === 'NA' || s === '-' || s === '--';
  }
  function detailNeedsReparse(e){
    e = e || {};
    var raws = Array.isArray(e.raw_packets) ? e.raw_packets : [];
    if(!raws.length) return false;
    if(isUnknownModel(e.model)) return true;
    if(e.lat == null || e.lon == null) return true;
    if(isMissingDetailValue(e.rid_format || e.dji_rid_kind || e.kind)) return true;
    return false;
  }
  function detailReparseModeOptions(){
    return [
      ['auto', 'Auto'],
      ['gb46750_2025', 'GB46750-2025'],
      ['dji_old_odid', 'DJI OLD ODID']
    ].map(function(item){
      return '<option value="'+escAttr(item[0])+'">'+esc(item[1])+'</option>';
    }).join('');
  }
  function detailReparseControls(e){
    e = e || {};
    if(!detailNeedsReparse(e)) return '';
    var sn = String(e.sn || '');
    return '<div class="detail-reparse-box" data-sn="'+escAttr(sn)+'">'
      + '<span>以</span><select class="detail-reparse-mode" data-sn="'+escAttr(sn)+'">'+detailReparseModeOptions()+'</select><span>方式重新解析</span>'
      + '<button class="btn-mini warn detail-reparse-btn" type="button" data-sn="'+escAttr(sn)+'">重试</button>'
      + '<div class="detail-reparse-status" data-sn="'+escAttr(sn)+'">自动批量重新解析仍会按默认分配覆盖这些结果。</div>'
      + '</div>';
  }
  function detailReparseModeStorageKey(sn){
    return 'rid_detail_reparse_mode:' + String(sn || '');
  }
  function detailReparseTargetSn(e){
    e = e || {};
    return String(e.sn || e.uas_id || e.mac || e.src_mac || '').trim();
  }
  function normalizeDetailReparseMode(mode){
    mode = String(mode || 'auto').trim();
    var aliases = {'dji_gb46750':'gb46750_2025','gb46750':'gb46750_2025','odid_legacy':'dji_old_odid','old':'dji_old_odid','legacy':'dji_old_odid'};
    mode = aliases[mode] || mode;
    var allowed = {'auto':1,'gb46750_2025':1,'dji_old_odid':1};
    return allowed[mode] ? mode : 'auto';
  }
  function currentDetailReparseSelectMode(sn){
    sn = String(sn || '');
    var list = document.querySelectorAll ? document.querySelectorAll('.detail-reparse-mode') : [];
    for(var i=0;i<list.length;i++){
      var itemSn = String(list[i].getAttribute('data-sn') || '');
      if(itemSn === sn) return normalizeDetailReparseMode(list[i].value);
    }
    return '';
  }
  function rememberVisibleDetailReparseMode(){
    var list = document.querySelectorAll ? document.querySelectorAll('.detail-reparse-mode') : [];
    for(var i=0;i<list.length;i++){
      var sn = String(list[i].getAttribute('data-sn') || '');
      if(sn) setDetailReparseModeForSn(sn, list[i].value);
    }
  }
  function detailReparseSelectIsActive(){
    var active = document.activeElement;
    return !!(active && active.closest && active.closest('.detail-reparse-mode'));
  }
  function detailReparseModeForSn(sn){
    sn = String(sn || '');
    var current = currentDetailReparseSelectMode(sn);
    if(current) return current;
    if(Object.prototype.hasOwnProperty.call(detailReparseModeCache, sn)){
      return normalizeDetailReparseMode(detailReparseModeCache[sn]);
    }
    try{ return normalizeDetailReparseMode(localStorage.getItem(detailReparseModeStorageKey(sn))); }
    catch(_e){ return 'auto'; }
  }
  function setDetailReparseModeForSn(sn, mode){
    sn = String(sn || '');
    mode = normalizeDetailReparseMode(mode);
    detailReparseModeCache[sn] = mode;
    try{ localStorage.setItem(detailReparseModeStorageKey(sn), mode); }catch(_e){}
    return mode;
  }
  detailReparseModeOptions = function(current){
    current = normalizeDetailReparseMode(current);
    return [
      ['auto', 'Auto'],
      ['gb46750_2025', 'GB46750-2025'],
      ['dji_old_odid', 'DJI OLD ODID']
    ].map(function(item){
      var selected = item[0] === current ? ' selected' : '';
      return '<option value="'+escAttr(item[0])+'"'+selected+'>'+esc(item[1])+'</option>';
    }).join('');
  };
  detailReparseControls = function(e){
    e = e || {};
    var sn = detailReparseTargetSn(e);
    var raws = Array.isArray(e.raw_packets) ? e.raw_packets : [];
    var hint = raws.length ? '按选定方式重新解析该机历史包，并重建轨迹。' : '暂无原始包，无法重新解析。';
    var disabled = sn ? '' : ' disabled';
    return '<div class="detail-reparse-box" data-sn="'+escAttr(sn)+'">'
      + '<span>以</span><select class="detail-reparse-mode" data-sn="'+escAttr(sn)+'">'+detailReparseModeOptions(detailReparseModeForSn(sn))+'</select><span>方式重新解析</span>'
      + '<button class="btn-mini warn detail-reparse-btn" type="button" data-sn="'+escAttr(sn)+'"'+disabled+'>重试</button>'
      + '<div class="detail-reparse-status" data-sn="'+escAttr(sn)+'">'+esc(hint)+'</div>'
      + '</div>';
  };
  function detailReparseApiUrl(){
    return String(window.LIGHT_RID_DETAIL_REPARSE_API || '/api/history/reparse');
  }
  function updateLocalRowAfterReparse(sn, item){
    sn = String(sn || '');
    if(!sn || !item) return;
    latestDroneMap[sn] = item;
    [latestDroneRows, latestMapRows].forEach(function(list){
      if(!Array.isArray(list)) return;
      for(var i=0;i<list.length;i++){
        if(String((list[i] && list[i].sn) || '') === sn) list[i] = item;
      }
    });
  }
  async function refreshAircraftAfterReparse(oldSn, data){
    oldSn = String(oldSn || '');
    data = data || {};
    var sn = String(data.sn_now || data.sn || oldSn || '');
    if(!sn) return;
    setDetailReparseModeForSn(sn, data.mode || detailReparseModeForSn(oldSn));
    if(oldSn && oldSn !== sn){
      setDetailReparseModeForSn(oldSn, detailReparseModeForSn(oldSn));
      delete trackCache[oldSn];
      delete trackFetchMeta[oldSn];
      delete trackLineSig[oldSn];
    }
    delete trackFetchMeta[sn];
    delete trackLineSig[sn];
    if(Array.isArray(data.track)){
      trackCache[sn] = data.track.slice();
      trackFetchMeta[sn] = {
        ts: Date.now(),
        scope: 'history|' + TRACK_HISTORY_FETCH_LIMIT,
        total: Number(data.track_count || data.track.length || 0),
        shown: Number(data.track.length || 0)
      };
    }else{
      delete trackCache[sn];
    }
    try{
      var detail = await getJson('/api/v1/drones/' + encodeURIComponent(sn));
      if(detail && detail.item){
        updateLocalRowAfterReparse(sn, detail.item);
        if(Array.isArray(detail.track)){
          trackCache[sn] = detail.track.slice();
          trackFetchMeta[sn] = {
            ts: Date.now(),
            scope: 'history|' + TRACK_HISTORY_FETCH_LIMIT,
            total: Number(detail.track_count || detail.track.length || 0),
            shown: Number(detail.track.length || 0)
          };
        }
      }
    }catch(_e){}
    selectedSnSet[sn] = true;
    delete historyHiddenSnSet[sn];
    renderLiveCards(latestDroneRows);
    renderMapMiniList(latestDroneRows);
    refreshTrackMgrOptions(latestDroneRows);
    if(currentAppPage() === 'history'){
      if(replaySyncPaused) renderReplayFrame();
      else updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    }else{
      updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    }
    var row = findDisplayRowBySn(latestDroneRows, sn) || latestDroneMap[sn] || null;
    if(row) showDroneInfoCard(row);
  }
  async function retryDetailReparse(btn){
    if(!btn) return;
    var sn = String(btn.getAttribute('data-sn') || '').trim();
    if(!sn) return;
    var root = btn.closest ? btn.closest('.detail-reparse-box') : null;
    var sel = root ? root.querySelector('.detail-reparse-mode') : null;
    var status = root ? root.querySelector('.detail-reparse-status') : null;
    var mode = setDetailReparseModeForSn(sn, (sel && sel.value) || 'auto');
    btn.disabled = true;
    if(status) status.textContent = '正在重新解析...';
    try{
      var data = await postJson(detailReparseApiUrl(), {sn:sn, mode:mode});
      setDetailReparseModeForSn(sn, mode);
      if(data && data.sn_now) setDetailReparseModeForSn(data.sn_now, mode);
      var msg = data.message || ('重新解析完成: ' + String(data.mode || mode));
      if(status) status.textContent = msg;
      showBanner(msg, 'ok', 2800, {persist:false});
      await refreshAircraftAfterReparse(sn, data);
      if(!data.refresh){
        try{ if(ws) ws.close(); }catch(_e){}
      }
    }catch(e){
      var err = (e && e.message) ? e.message : String(e || 'failed');
      if(status) status.textContent = '重新解析失败: ' + err;
      showBanner('重新解析失败: ' + err, 'warn', 4200, {persist:false});
    }finally{
      btn.disabled = false;
    }
  }
  function modelActionCell(e){
    e = e || {};
    var model = String(e.model || 'N/A');
    if(!isUnknownModel(model)) return esc(model);
    var sn = String(e.sn || '');
    var prefix = cleanModelPrefixFromSn(sn);
    var disabled = prefix ? '' : ' disabled';
    return '<span class="info-model-cell"><span class="info-model-na">N/A</span>'
      + '<span class="model-row-actions">'
      + '<button class="btn-mini model-map-add" type="button" data-sn="'+escAttr(sn)+'" data-prefix="'+escAttr(prefix)+'"'+disabled+'>添加到识别库</button>'
      + '<button class="btn-mini model-map-issue" type="button" data-sn="'+escAttr(sn)+'" data-prefix="'+escAttr(prefix)+'"'+disabled+'>Issue</button>'
      + '<button class="btn-mini model-map-pr" type="button" data-sn="'+escAttr(sn)+'" data-prefix="'+escAttr(prefix)+'"'+disabled+'>PR</button>'
      + '</span></span>';
  }
  function modelIssueUrl(sn, prefix){
    var title = 'RID model mapping: ' + (prefix || sn || 'unknown');
    var body = [
      'SN: ' + String(sn || ''),
      'Prefix: ' + String(prefix || ''),
      'Current model: N/A',
      '',
      'Please add this RID model mapping to rid-models.json.'
    ].join('\\n');
    return 'https://github.com/luyii-code-1/Light_RID_Scanner/issues/new?title='
      + encodeURIComponent(title) + '&body=' + encodeURIComponent(body);
  }
  function modelPrEditUrl(){
    return 'https://github.com/luyii-code-1/Light_RID_Scanner/edit/main/rid-models.json';
  }
  function patchLocalModel(sn, model){
    sn = String(sn || '');
    model = String(model || '').trim();
    if(!sn || !model) return;
    if(latestDroneMap && latestDroneMap[sn]) latestDroneMap[sn].model = model;
    [latestDroneRows, latestMapRows].forEach(function(list){
      if(!Array.isArray(list)) return;
      list.forEach(function(row){ if(row && String(row.sn || '') === sn) row.model = model; });
    });
    var tr = null;
    if(window.CSS && CSS.escape){
      tr = document.querySelector('tr[data-sn="'+CSS.escape(sn)+'"]');
    }else{
      var rows = document.querySelectorAll('tr[data-sn]');
      for(var i=0;i<rows.length;i++){
        if(String(rows[i].getAttribute('data-sn') || '') === sn){ tr = rows[i]; break; }
      }
    }
    if(tr && tr.children && tr.children[3]) tr.children[3].textContent = model;
    renderLiveCards(latestDroneRows);
  }
  async function addModelFromDetail(sn, prefix){
    sn = String(sn || '');
    prefix = String(prefix || cleanModelPrefixFromSn(sn));
    if(!prefix){
      showBanner('无法从 SN 提取识别库前缀。', 'warn', 3200);
      return;
    }
    var model = window.prompt('请输入 ' + prefix + ' 对应的机型名称', '');
    model = String(model || '').trim();
    if(!model) return;
    try{
      await postJson('/api/settings/models/upsert', {sn:sn, prefix:prefix, model:model});
      patchLocalModel(sn, model);
      showBanner('识别库已添加：' + prefix + ' → ' + model, 'ok', 3200);
      if(latestDroneMap && latestDroneMap[sn]) showDroneInfoCard(latestDroneMap[sn]);
    }catch(e){
      showBanner('识别库添加失败：' + (e.message || e), 'warn', 4800);
    }
  }
  function openModelIssue(sn, prefix){
    if(!prefix){
      showBanner('无法从 SN 提取识别库前缀。', 'warn', 3200);
      return;
    }
    window.open(modelIssueUrl(sn, prefix), '_blank', 'noopener');
  }
  async function openModelPr(sn, prefix){
    if(!prefix){
      showBanner('无法从 SN 提取识别库前缀。', 'warn', 3200);
      return;
    }
    var model = window.prompt('请输入机型名称；会复制 JSON 条目并打开 GitHub 编辑页', '');
    model = String(model || '').trim();
    if(model && navigator.clipboard && navigator.clipboard.writeText){
      try{ await navigator.clipboard.writeText('"' + prefix + '": "' + model.replace(/"/g, '\\\\"') + '"'); }catch(_e){}
    }
    window.open(modelPrEditUrl(), '_blank', 'noopener');
    showBanner(model ? 'JSON 条目已复制，已打开 GitHub 编辑页。' : '已打开 GitHub 编辑页。', 'ok', 3600);
  }
  function bindModelActionButtons(){
    var modal = qs('info-modal');
    if(!modal || modal.getAttribute('data-model-actions') === '1') return;
    modal.setAttribute('data-model-actions', '1');
    modal.addEventListener('click', function(ev){
      var addBtn = ev.target && ev.target.closest ? ev.target.closest('.model-map-add') : null;
      var issueBtn = ev.target && ev.target.closest ? ev.target.closest('.model-map-issue') : null;
      var prBtn = ev.target && ev.target.closest ? ev.target.closest('.model-map-pr') : null;
      var reparseBtn = ev.target && ev.target.closest ? ev.target.closest('.detail-reparse-btn') : null;
      if(reparseBtn){
        ev.preventDefault();
        ev.stopPropagation();
        retryDetailReparse(reparseBtn);
        return;
      }
      var btn = addBtn || issueBtn || prBtn;
      if(!btn) return;
      ev.preventDefault();
      ev.stopPropagation();
      var sn = btn.getAttribute('data-sn') || '';
      var prefix = btn.getAttribute('data-prefix') || cleanModelPrefixFromSn(sn);
      if(addBtn) addModelFromDetail(sn, prefix);
      else if(issueBtn) openModelIssue(sn, prefix);
      else openModelPr(sn, prefix);
    });
    function rememberReparseModeEvent(ev){
      var sel = ev.target && ev.target.closest ? ev.target.closest('.detail-reparse-mode') : null;
      if(!sel) return;
      setDetailReparseModeForSn(sel.getAttribute('data-sn') || '', sel.value);
    }
    modal.addEventListener('change', rememberReparseModeEvent);
    modal.addEventListener('input', rememberReparseModeEvent);
  }
  function patchInfoCard(){
    if(typeof refreshActiveInfoCard === 'function' && !refreshActiveInfoCard.__reparseModePatched){
      var oldRefreshActiveInfoCard = refreshActiveInfoCard;
      refreshActiveInfoCard = function(rows){
        if(detailReparseSelectIsActive()) return;
        rememberVisibleDetailReparseMode();
        return oldRefreshActiveInfoCard(rows);
      };
      refreshActiveInfoCard.__reparseModePatched = true;
    }
    if(typeof showDroneInfoCard === 'function' && !showDroneInfoCard.__reparseModePatched){
      var oldShowDroneInfoCard = showDroneInfoCard;
      showDroneInfoCard = function(e){
        rememberVisibleDetailReparseMode();
        return oldShowDroneInfoCard(e);
      };
      showDroneInfoCard.__reparseModePatched = true;
    }
    buildInfoHtml = function(e){
      e = e || {};
      var base = [
        ['SN', String(e.sn || '-')],
        ['UAS ID', uasIdText(e)],
        ['机型', modelActionCell(e), 'html'],
        ['在线状态', e.lost ? '离线' : '在线'],
        ['来源', snSourceText(e)],
        ['扫描类型', scanTypeText(e)],
        ['固件', firmwareTypeText(e)],
        ['RID格式', ridFormatText(e)],
        ['解析状态', parseNoteText(e) || '-'],
        ['MAC', String(e.mac || '-')],
        ['SSID', String(e.ssid || '(hidden)')],
        ['捕获类型', String(e.capture_type || '-')],
        ['捕获时间', String(e.capture_time || '-')],
        ['最后数据包', String(e.last_pkt_time || e.capture_time || '-')],
        ['信号', e.rssi==null ? 'N/A' : (e.rssi + 'dBm')],
        ['包数', String(e.pkts==null?0:e.pkts)],
        ['数据更新时间', String(e.age_text || fmtAge(e.age))],
        ['在线时长', fmtDurSec(e.online_dur)],
        ['首次上线', String(e.first_seen || '-')],
        ['最后上线', String(e.last_seen || '-')],
        ['轨迹点数', String(e.track_count==null?0:e.track_count)]
      ];
      var dronePos = [
        ['纬度', fmt(e.lat,6,'')],
        ['经度', fmt(e.lon,6,'')],
        ['当前高度', fmt(e.alt,1,'m')],
        ['相对/大地/气压高度', fmt(e.alt_relative,1,'m') + ' / ' + fmt(e.alt_geoid,1,'m') + ' / ' + fmt(e.alt_baro,1,'m')],
        ['报送 速度/地速垂速', fmt(e.track_deg,1,'°') + ' / ' + fmt(e.ground_speed,2,'m/s') + ' / ' + fmt(e.vertical_speed,2,'m/s')],
        ['水平/垂直/速度 精度', String(e.horizontal_accuracy ?? '-') + ' / ' + String(e.vertical_accuracy ?? '-') + ' / ' + String(e.speed_accuracy ?? '-')],
        ['坐标系', String(e.coord_sys_text || e.coord_sys || '-')],
        ['运行类别/分类', String(e.operation_category_text || e.operation_category || '-') + ' / ' + String(e.aircraft_category_text || e.aircraft_category || '-')],
        ['运行状态', String(e.operation_state_text || e.operation_state || '-')],
        ['方向', String(e.dir || '-')]
      ];
      var pilotPos = [
        ['遥控站纬度', fmt(e.pilot_lat,6,'')],
        ['遥控站经度', fmt(e.pilot_lon,6,'')]
      ];
      appendHomeAuxRows(pilotPos, e);
      pilotPos.push(['飞手高度', fmt(e.pilot_alt,1,'m')]);
      pilotPos.push(['飞手位置类型', String(e.pilot_loc_type_text || e.pilot_loc_type || '-')]);
      var actionSn = detailReparseTargetSn(e);
      var html = '<div class="info-actions">'+
        '<button class="btn-mini export-track-btn" type="button" data-sn="'+escAttr(actionSn)+'">导出轨迹</button>'+
        '<button class="btn-mini warn delete-history-btn" type="button" data-sn="'+escAttr(actionSn)+'">删除历史</button>'+
        '</div>'+detailReparseControls(e)+'<div class="info-sections">';
      html += buildInfoSection('飞机位置信息', dronePos);
      html += buildInfoSection('飞手位置信息', pilotPos);
      html += buildInfoSection('其他信息', base);
      var raws = Array.isArray(e.raw_packets) ? e.raw_packets : [];
      html += '<section class="info-block"><h3>原始包</h3>';
      if(raws.length){
        for(var i=0;i<raws.length;i++){
          var p = raws[i] || {};
          html += '<div class="raw-meta">#'+(i+1)+' ['+esc(String(p.capture_type || e.capture_type || '-'))+'] '+esc(String(p.ts || e.capture_time || '-'))+'</div>';
          html += '<pre class="raw-code">'+esc(String(p.hex || ''))+'</pre>';
        }
      }else{
        html += '<div class="raw-empty">暂无</div>';
      }
      html += '</section></div>';
      return html;
    };
  }
  function zoneList(){
    var list = metaState && metaState.alert_zones;
    if(Array.isArray(list) && list.length){
      return list.filter(function(z){ return !!z && typeof z === 'object'; });
    }
    var z = metaState && metaState.alert_zone;
    return (z && typeof z === 'object') ? [z] : [];
  }
  function zoneBounds(z){
    var lat1 = numOrNull(z.lat1), lat2 = numOrNull(z.lat2), lon1 = numOrNull(z.lon1), lon2 = numOrNull(z.lon2);
    if(lat1==null || lat2==null || lon1==null || lon2==null) return null;
    return {
      south: Math.min(lat1, lat2),
      north: Math.max(lat1, lat2),
      west: Math.min(lon1, lon2),
      east: Math.max(lon1, lon2)
    };
  }
  function clearAlarmZones(){
    if(!map) return;
    while(alarmRects.length){
      try{ map.removeLayer(alarmRects.pop()); }catch(_e){}
    }
  }
  function drawAlarmZones(){
    if(!map) return;
    clearAlarmZones();
    zoneList().forEach(function(z){
      var b = zoneBounds(z || {});
      if(!z || !z.enabled || !b) return;
      var rect = L.rectangle([[b.south, b.west], [b.north, b.east]], {color:'#ff5b5b', weight:2, fillColor:'#ff3b3b', fillOpacity:0.08}).addTo(map);
      rect.bindPopup('<b>'+esc(String(z.name || '报警区域'))+'</b>');
      alarmRects.push(rect);
    });
  }
  function zoneHitGroups(rows){
    var groups = [];
    rows = Array.isArray(rows) ? rows : [];
    zoneList().forEach(function(z){
      var b = zoneBounds(z || {});
      if(!z || !z.enabled || !b) return;
      var hits = [];
      for(var i=0;i<rows.length;i++){
        var e = rows[i] || {};
        if(e.lost || e.archived) continue;
        var lat = numOrNull(e.lat), lon = numOrNull(e.lon);
        if(lat==null || lon==null) continue;
        if(lat >= b.south && lat <= b.north && lon >= b.west && lon <= b.east){
          hits.push(e);
        }
      }
      if(hits.length){
        groups.push({zone:z, hits:hits});
      }
    });
    return groups;
  }
  function zoneHitSnSetFromGroups(groups){
    var out = {};
    (Array.isArray(groups) ? groups : []).forEach(function(group){
      (Array.isArray(group.hits) ? group.hits : []).forEach(function(e){
        var sn = String((e && e.sn) || '');
        if(sn) out[sn] = true;
      });
    });
    return out;
  }
  function zoneHitSnSet(rows){
    return zoneHitSnSetFromGroups(zoneHitGroups(rows));
  }
  function setZoneAlarm(rows){
    var overlay = ensureZoneOverlay();
    var groups = zoneHitGroups(rows);
    zoneAlarmSnSet = zoneHitSnSetFromGroups(groups);
    if(!groups.length){
      overlay.classList.remove('show');
      document.body.classList.remove('zone-alert-active');
      alarmLastSig = '';
      return;
    }
    document.body.classList.add('zone-alert-active');
    var sigParts = [];
    var lines = [];
    groups.forEach(function(group){
      var zoneName = String((group.zone && group.zone.name) || '报警区域');
      var names = group.hits.map(function(x){ return String(x.sn||'-') + ' / ' + String(x.model || 'N/A'); }).join('；');
      lines.push(zoneName + '：' + names);
      sigParts.push(zoneName + '>' + group.hits.map(function(x){ return String(x.sn||''); }).sort().join('|'));
    });
    var sig = sigParts.sort().join(' || ');
    var lineText = lines.join(' / ');
    qs('zone-alarm-text').textContent = lineText ? ('侵入目标：' + lineText) : '请查看地图和列表中的报警标记';
    overlay.classList.add('show');
    if(sig !== alarmLastSig){
      if(!replayPreviewActive()){
        showBanner('当前有飞机侵入报警区域：' + lineText, 'warn', 5200, {persist:false});
        if(webNotifyEnabled && window.Notification && Notification.permission === 'granted'){
          try{ new Notification('当前有飞机侵入报警区域', {body:lineText}); }catch(_e){}
        }
      }
      alarmLastSig = sig;
    }
    if(alarmOverlayHideTimer) clearTimeout(alarmOverlayHideTimer);
    alarmOverlayHideTimer = setTimeout(function(){
      if(!zoneHitGroups(latestDroneRows).length){
        overlay.classList.remove('show');
        document.body.classList.remove('zone-alert-active');
        zoneAlarmSnSet = {};
      }
    }, 6000);
  }
  var _origBuildExtraUi = buildExtraUi;
  buildExtraUi = function(){
    _origBuildExtraUi();
    neutralizeLegacyCollapsers();
    ensureMainPages();
  };
  var _origApplyMeta = applyMeta;
  applyMeta = function(meta){
    _origApplyMeta(meta);
    ensureMainPages();
    neutralizeLegacyCollapsers();
    drawAlarmZones();
  };
  var _origOnData = onData;
  onData = function(d){
    zoneAlarmSnSet = zoneHitSnSet((d && Array.isArray(d.drones)) ? d.drones : []);
    _origOnData(d);
    if(homeFreezeAfterFirstRender && !uiFrozen){
      homeFreezeAfterFirstRender = false;
      try{ localStorage.removeItem(FREEZE_ON_HOME_KEY); }catch(_e){}
      setFreezeState(true);
      showBanner('列表已冻结，刷新或恢复同步后继续更新。', 'ok', 2600);
    }
  };
  var _origUpdateMap = updateMap;
  updateMap = function(drones){
    zoneAlarmSnSet = zoneHitSnSet(drones);
    refreshReplayBounds(true);
    _origUpdateMap(drones);
    drawAlarmZones();
    setZoneAlarm(drones);
    renderReplayCard();
    updateReplayMarkers();
  };
  document.addEventListener('DOMContentLoaded', function(){
    patchInfoCard();
    bindModelActionButtons();
    ensureMainPages();
    neutralizeLegacyCollapsers();
    drawAlarmZones();
    syncHomeViewport();
  });
  window.addEventListener('resize', syncHomeViewport);
  if(window.visualViewport){
    try{
      window.visualViewport.addEventListener('resize', syncHomeViewport);
      window.visualViewport.addEventListener('scroll', syncHomeViewport);
    }catch(_e){}
  }
})();
"""

def _inject_html_once(html_src: str, marker: str, extra: str) -> str:
    if not extra:
        return html_src
    if extra in html_src:
        return html_src
    return html_src.replace(marker, extra + marker, 1)

def _rid_home_asset_url() -> str:
    asset_url = "/assets/vue/rid-home.js"
    asset_path = os.path.join(os.path.dirname(__file__), "assets", "vue", "rid-home.js")
    try:
        st = os.stat(asset_path)
        return f"{asset_url}?v={int(st.st_mtime)}-{int(st.st_size)}"
    except OSError:
        return asset_url

def _build_html() -> str:
    html_src = _PAGE_HTML
    html_src = html_src.replace("__APP_VERSION_LABEL__", _app_version_label())
    html_src = _inject_html_once(html_src, "</style>", _MAIN_PAGE_PATCH_CSS + "\n")
    html_src = _inject_html_once(
        html_src,
        "</body>",
        "<script>\n"
        + _MAIN_PAGE_PATCH_JS
        + "\n</script>\n"
        + f'<script src="{_rid_home_asset_url()}"></script>\n',
    )
    return html_src

def _build_login_html(next_path: str = "/", status_message: str = "", status_error: bool = False) -> str:
    safe_next = str(next_path or "/")
    if not safe_next.startswith("/") or safe_next.startswith("//"):
        safe_next = "/"
    password_enabled = _auth_login_method_enabled("password")
    sso_available = any(bool(_sso_link_state(item).get("active")) for item in _normalize_sso_links(AUTH_CFG.get("sso_links")))
    passkey_enabled = _auth_login_method_enabled("passkey")
    has_passkey = passkey_enabled and any(bool(item.get("enabled", True)) for item in _normalize_passkeys(AUTH_CFG.get("passkeys")))
    password_login_html = (
        '  <form id="login-form">\n'
        '    <div class="field"><label for="user">账号</label><input id="user" autocomplete="username" autofocus></div>\n'
        '    <div class="field"><label for="password">密码</label><input id="password" type="password" autocomplete="current-password"></div>\n'
        '    <div class="row"><button id="submit" type="submit">登录</button></div>\n'
        '  </form>\n'
        if password_enabled else ""
    )
    passkey_login_html = (
        '  <div class="row" style="margin-top:12px">\n'
        '    <button id="btn-passkey-login" type="button">使用通行密钥登录</button>\n'
        '  </div>'
        if has_passkey else ""
    )
    if not status_message:
        if passkey_enabled and (not has_passkey) and (not password_enabled) and (not sso_available):
            status_message = "已启用 PassKey 登录，但还没有登记可用密钥。"
        elif (not password_enabled) and (not has_passkey):
            if sso_available:
                status_message = "当前只允许通过 SSO URL 登录，请使用已生成的登录链接进入。"
            else:
                status_message = "现在没有可用的网页登录方式，请回到设置页检查登录方式。"
    status_class = "status err" if status_error else "status"
    status_html = '<div class="' + status_class + '" id="status">' + _html_escape(status_message, quote=False) + "</div>"
    method_labels: list[str] = []
    if password_enabled:
        method_labels.append("账号密码")
    if has_passkey:
        method_labels.append("PassKey")
    elif passkey_enabled:
        method_labels.append("PassKey（待登记）")
    if sso_available:
        method_labels.append("SSO URL（优先）")
    login_method_copy = ("可用方式：" + " / ".join(method_labels)) if method_labels else "现在没有可用的网页登录方式。"
    return f"""<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>登录 - Light RID Scanner</title>
<style>
*{{box-sizing:border-box}}
:root{{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --bg:#f3f2f1;--card:#fff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01
}}
@media (prefers-color-scheme:dark){{
  :root{{--bg:#201f1e;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;--muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c}}
}}
html,body{{margin:0;min-height:100dvh;background:linear-gradient(180deg,var(--bg),var(--card2));color:var(--txt);font-family:var(--font-ui)}}
body{{display:grid;place-items:center;padding:22px}}
.card{{width:min(420px,100%);border:1px solid var(--border);background:var(--card);box-shadow:0 16px 34px rgba(0,0,0,.16);border-radius:4px;padding:26px;animation:fade .18s ease-out both}}
.brand{{font:700 24px/1.1 var(--font-ui);letter-spacing:.01em;margin:0 0 6px}}
.desc{{color:var(--muted);font-size:14px;line-height:1.5;margin:0 0 22px}}
.field{{display:grid;gap:7px;margin-top:14px}}
label{{font:600 12px/1 var(--font-ui);color:var(--muted)}}
input{{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 12px;font:600 15px/1.2 var(--font-ui);outline:none;transition:border-color .14s ease,box-shadow .14s ease}}
input:focus{{border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 34%, transparent)}}
.row{{display:flex;justify-content:space-between;align-items:center;gap:10px;margin-top:20px}}
button{{height:42px;border:1px solid var(--blue);background:var(--blue);color:white;border-radius:4px;padding:0 18px;font:700 14px/1 var(--font-ui);cursor:pointer;transition:transform .14s ease,filter .14s ease}}
button:hover{{transform:translateY(-1px);filter:brightness(1.05)}}
.status{{min-height:20px;margin-top:14px;color:var(--muted);font-size:13px;white-space:pre-wrap}}
.status.err{{color:var(--warn)}}
@keyframes fade{{from{{opacity:0;transform:translateY(5px)}}to{{opacity:1;transform:none}}}}
</style></head><body>
<main class="card">
  <h1 class="brand">Light RID Scanner</h1>
  <p class="desc">登录监控平台。{_html_escape(login_method_copy, quote=False)}</p>
{password_login_html}{passkey_login_html}
  {status_html}
</main>
<script>
const nextPath = {json.dumps(safe_next, ensure_ascii=False)};
const form = document.getElementById('login-form');
const statusEl = document.getElementById('status');
const passkeyBtn = document.getElementById('btn-passkey-login');
function pageHeaders(extra){{
  var h = {{'X-LightRID-Page':'1'}};
  if(extra) Object.keys(extra).forEach(function(k){{ h[k] = extra[k]; }});
  return h;
}}
function setStatus(text, err){{
  if(!statusEl) return;
  statusEl.textContent = text || '';
  statusEl.classList.toggle('err', !!err);
}}
function b64uToBytes(text){{
  var raw = String(text || '').replace(/-/g,'+').replace(/_/g,'/');
  while(raw.length % 4) raw += '=';
  if(!raw) return new Uint8Array(0);
  var bin = atob(raw);
  var out = new Uint8Array(bin.length);
  for(var i=0;i<bin.length;i++) out[i] = bin.charCodeAt(i);
  return out;
}}
function bytesToB64u(bytes){{
  var view = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes || []);
  var bin = '';
  for(var i=0;i<view.length;i++) bin += String.fromCharCode(view[i]);
  return btoa(bin).replace(/\\+/g,'-').replace(/\\//g,'_').replace(/=+$/,'');
}}
async function loginWithPasskey(){{
  if(!window.PublicKeyCredential || !navigator.credentials || !navigator.credentials.get){{
      throw new Error('当前浏览器不支持通行密钥登录');
  }}
  setStatus('正在准备通行密钥登录...', false);
  const startR = await fetch('/api/passkey/login/start', {{
    method:'POST',
    headers:pageHeaders({{'Content-Type':'application/json'}}),
    body:'{{}}'
  }});
  const start = await startR.json().catch(() => ({{}}));
  if(!startR.ok || start.ok === false) throw new Error(start.error || ('HTTP ' + startR.status));
  const pk = start.publicKey || {{}};
  const allowCredentials = Array.isArray(pk.allowCredentials) ? pk.allowCredentials : [];
  const cred = await navigator.credentials.get({{
    publicKey: {{
      challenge: b64uToBytes(pk.challenge || start.challenge || ''),
      rpId: pk.rpId || pk.rp_id || location.hostname,
      timeout: pk.timeout || start.timeout_ms || 300000,
      userVerification: pk.userVerification || 'preferred',
      allowCredentials: allowCredentials.map(function(item){{ return {{type:'public-key', id:b64uToBytes(item.id || '')}}; }})
    }}
  }});
  if(!cred) throw new Error('未获取到通行密钥凭据');
  const response = cred.response || {{}};
  const finishR = await fetch('/api/passkey/login/finish', {{
    method:'POST',
    headers:pageHeaders({{'Content-Type':'application/json'}}),
    body:JSON.stringify({{
      challenge: start.challenge || start.challenge_token || '',
      id: cred.id || '',
      rawId: bytesToB64u(cred.rawId || new Uint8Array(0)),
      type: cred.type || 'public-key',
      response: {{
        clientDataJSON: bytesToB64u(response.clientDataJSON || new Uint8Array(0)),
        authenticatorData: bytesToB64u(response.authenticatorData || new Uint8Array(0)),
        signature: bytesToB64u(response.signature || new Uint8Array(0)),
        userHandle: response.userHandle ? bytesToB64u(response.userHandle) : ''
      }},
      next: nextPath || '/'
    }})
  }});
  const finish = await finishR.json().catch(() => ({{}}));
  if(!finishR.ok || finish.ok === false) throw new Error(finish.error || ('HTTP ' + finishR.status));
  location.href = nextPath || finish.next || '/';
}}
if(form){{
  form.addEventListener('submit', async function(ev){{
    ev.preventDefault();
    const btn = document.getElementById('submit');
    btn.disabled = true;
    setStatus('正在验证...', false);
    try{{
      const r = await fetch('/login', {{
        method:'POST',
        headers:{{'Content-Type':'application/json'}},
        body:JSON.stringify({{username:document.getElementById('user').value || '', password:document.getElementById('password').value || ''}})
      }});
      const d = await r.json().catch(() => ({{}}));
      if(!r.ok || d.ok === false) throw new Error(d.error || '登录失败');
      location.href = nextPath || d.next || '/';
    }}catch(e){{
      setStatus(e.message || String(e), true);
    }}finally{{
      btn.disabled = false;
    }}
  }});
}}
if(passkeyBtn){{
  passkeyBtn.addEventListener('click', async function(){{
    passkeyBtn.disabled = true;
    try{{
      await loginWithPasskey();
    }}catch(e){{
      setStatus(e.message || String(e), true);
    }}finally{{
      passkeyBtn.disabled = false;
    }}
  }});
}}
</script>
</body></html>"""

def _build_eula_html(next_path: str = "/") -> str:
    safe_next = str(next_path or "/")
    if not safe_next.startswith("/") or safe_next.startswith("//"):
        safe_next = "/"
    eula_html = _markdown_to_html(_load_eula_markdown())
    return f"""<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>许可协议 - Light RID Scanner</title>
<style>
*{{box-sizing:border-box}}
:root{{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;--muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c
}}
@media (prefers-color-scheme:light){{
  :root{{--bg:#f3f2f1;--card:#fff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01}}
}}
html,body{{margin:0;min-height:100dvh;background:var(--bg);color:var(--txt);font-family:var(--font-ui)}}
body{{display:grid;place-items:center;padding:18px}}
.shell{{width:min(960px,100%);display:grid;gap:12px}}
.head{{display:flex;justify-content:space-between;align-items:flex-end;gap:12px;flex-wrap:wrap}}
h1{{margin:0;font:700 26px/1.1 var(--font-ui);letter-spacing:0}}
.source{{font:600 12px/1.5 var(--font-ui);color:var(--muted)}}
.source a,.license a{{color:var(--blue);text-decoration:none}}
.source a:hover,.license a:hover{{text-decoration:underline}}
.license{{border:1px solid var(--border);background:var(--card);border-radius:4px;padding:18px;max-height:min(68dvh,720px);overflow:auto;box-shadow:0 16px 34px rgba(0,0,0,.18)}}
.license h1,.license h2,.license h3,.license h4{{margin:18px 0 8px;letter-spacing:0}}
.license h1:first-child,.license h2:first-child{{margin-top:0}}
.license p{{margin:8px 0;line-height:1.65;color:var(--txt)}}
.license ul{{margin:8px 0 12px 20px;padding:0;line-height:1.6}}
.eula-code{{white-space:pre-wrap;word-break:break-word;border:1px solid var(--border);background:var(--card2);border-radius:4px;padding:12px;font:600 12px/1.45 var(--font-mono);color:var(--txt)}}
.accept{{border:1px solid var(--border);background:var(--card);border-radius:4px;padding:14px;display:grid;gap:12px}}
.check{{display:flex;gap:10px;align-items:flex-start;line-height:1.5;color:var(--txt)}}
input[type=checkbox]{{width:16px;height:16px;flex:0 0 auto;margin-top:2px;accent-color:var(--blue)}}
.read-state{{font:600 13px/1.5 var(--font-ui);color:var(--muted)}}
.actions{{display:flex;justify-content:flex-end;gap:10px;flex-wrap:wrap}}
button{{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:0 16px;font:700 14px/1 var(--font-ui);cursor:pointer}}
button.primary{{border-color:var(--blue);background:var(--blue);color:white}}
button.warn{{border-color:color-mix(in srgb,var(--warn) 50%,var(--border));color:var(--warn)}}
button:disabled{{opacity:.58;cursor:not-allowed}}
.status{{min-height:20px;color:var(--muted);font-size:13px;white-space:pre-wrap}}
.status.err{{color:var(--warn)}}
</style></head><body>
<main class="shell">
  <div class="head">
    <div>
      <h1>Light RID Scanner 许可协议</h1>
      <div class="source">EULA 来源：<a href="{_html_escape(EULA_URL)}" target="_blank" rel="noopener noreferrer">{_html_escape(EULA_URL)}</a></div>
    </div>
  </div>
  <article class="license" id="eula-scroll" tabindex="0" aria-label="许可协议正文">{eula_html}</article>
  <section class="accept">
    <div class="read-state" id="read-state">请先阅读 EULA，5 秒后才能勾选同意。</div>
    <label class="check"><input id="agree" type="checkbox" disabled> <span>我已完整阅读并同意以上许可协议，确认继续使用本软件。</span></label>
    <div class="actions">
      <button class="warn" id="decline" type="button">不同意</button>
      <button class="primary" id="accept" type="button" disabled>同意并继续</button>
    </div>
    <div id="status" class="status">首次运行必须同意许可协议后才能进入系统。</div>
  </section>
</main>
<script>
const nextPath = {json.dumps(safe_next, ensure_ascii=False)};
const READ_WAIT_MS = 5000;
const readStartMs = Date.now();
function qs(id){{ return document.getElementById(id); }}
function pageHeaders(extra){{ var h={{'X-LightRID-Page':'1'}}; if(extra) Object.keys(extra).forEach(function(k){{ h[k]=extra[k]; }}); return h; }}
function setStatus(text, err){{ qs('status').textContent = text || '-'; qs('status').classList.toggle('err', !!err); }}
function readWaitLeft(){{
  return Math.max(0, READ_WAIT_MS - (Date.now() - readStartMs));
}}
function updateReadState(){{
  var left = readWaitLeft();
  var ready = left <= 0;
  qs('agree').disabled = !ready;
  if(!ready){{
    qs('agree').checked = false;
    qs('accept').disabled = true;
    qs('read-state').textContent = '请先阅读 EULA，' + Math.ceil(left / 1000) + ' 秒后才能勾选同意。';
  }}else{{
    qs('read-state').textContent = '已达到阅读等待时间，可以勾选同意。';
    qs('accept').disabled = !qs('agree').checked;
  }}
}}
window.addEventListener('resize', updateReadState);
window.addEventListener('load', updateReadState);
var readTimer = setInterval(function(){{
  updateReadState();
  if(readWaitLeft() <= 0) clearInterval(readTimer);
}}, 250);
setTimeout(updateReadState, 60);
qs('agree').addEventListener('change', function(){{ updateReadState(); }});
qs('decline').addEventListener('click', function(){{ setStatus('你还没有同意许可协议，当前不会进入系统。', true); }});
qs('accept').addEventListener('click', async function(){{
  if(readWaitLeft() > 0){{ setStatus('请先阅读 EULA，等待时间结束后再继续。', true); return; }}
  if(!qs('agree').checked){{ setStatus('请先勾选同意许可协议。', true); return; }}
  var btn = qs('accept');
  btn.disabled = true;
  setStatus('正在保存许可状态...', false);
  try{{
    const r = await fetch('/api/eula/accept', {{
      method:'POST',
      headers:pageHeaders({{'Content-Type':'application/json'}}),
      body:JSON.stringify({{accepted:true,next:nextPath}})
    }});
    const d = await r.json().catch(function(){{ return {{}}; }});
    if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
    location.href = d.next || nextPath || '/';
  }}catch(e){{
    setStatus(e.message || String(e), true);
    btn.disabled = false;
  }}
}});
</script></body></html>"""

def _build_logs_html() -> str:
    return """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>日志 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}
:root{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c;--green:#92c353;--glow:rgba(40,153,245,.12)
}
body.theme-light{--bg:#f3f2f1;--bg2:#edebe9;--card:#ffffff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01;--green:#107c10;--glow:rgba(0,120,212,.10)}
html,body{margin:0;min-height:100dvh;background:linear-gradient(180deg,var(--bg),var(--bg2));color:var(--txt);font-family:var(--font-ui)}
.wrap{width:min(1500px,calc(100vw - 24px));margin:0 auto;padding:16px 12px 26px}
.topbar{display:flex;align-items:center;justify-content:space-between;gap:12px;flex-wrap:wrap;margin-bottom:12px}
.title{font:700 28px/1 var(--font-ui)}
.actions,.tabs{display:flex;gap:8px;flex-wrap:wrap}
.btn,.tab{border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 13px;font:700 14px/1 var(--font-ui);cursor:pointer;transition:background-color .14s ease,border-color .14s ease,transform .14s ease,box-shadow .14s ease}
.btn:hover,.tab:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb,var(--blue) 10%,var(--card2));box-shadow:0 2px 8px var(--glow)}
.tab.active{border-color:var(--blue);background:color-mix(in srgb,var(--blue) 14%,var(--card2))}
.panel{border:1px solid var(--border);background:var(--card);border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,.08);overflow:hidden}
.toolbar{display:flex;justify-content:space-between;gap:10px;flex-wrap:wrap;align-items:center;padding:12px;border-bottom:1px solid var(--border)}
.meta{color:var(--muted);font-size:13px}
select,input{height:40px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:8px 10px;font:600 14px/1 var(--font-ui)}
pre{margin:0;height:calc(100dvh - 176px);min-height:420px;overflow:auto;padding:14px;background:#0e1116;color:#d6deeb;font:13px/1.55 var(--font-mono);white-space:pre-wrap;word-break:break-word}
body.theme-light pre{background:#fbfbfb;color:#24292f}
.status{padding:8px 12px;color:var(--muted);font-size:13px;border-top:1px solid var(--border)}
@media(max-width:720px){.wrap{width:calc(100vw - 10px);padding:10px 5px}.title{font-size:22px}pre{height:calc(100dvh - 230px);font-size:12px}}
</style></head><body><div class="wrap">
  <div class="topbar">
    <div><div class="title">日志</div><div class="meta">查看运行、操作、扫描、解析状态 Diff、AP 和系统报错日志。</div></div>
    <div class="actions">
      <button class="btn" id="btn-back" type="button">返回主页</button>
      <button class="btn" id="btn-settings" type="button">设置</button>
      <button class="btn" id="btn-theme" type="button" style="display:none">浅色</button>
    </div>
  </div>
  <div class="panel">
    <div class="toolbar">
      <div class="tabs">
        <button class="tab active" data-type="runtime" type="button">运行日志</button>
        <button class="tab" data-type="operation" type="button">操作日志</button>
        <button class="tab" data-type="scan" type="button">扫描日志</button>
        <button class="tab" data-type="scan_diff" type="button">扫描 Diff</button>
        <button class="tab" data-type="ap" type="button">AP 日志</button>
        <button class="tab" data-type="system" type="button">系统报错</button>
      </div>
      <div class="actions">
        <input id="limit" type="number" min="20" max="5000" value="500" title="行数">
        <button class="btn" id="btn-refresh" type="button">刷新</button>
        <button class="btn" id="btn-export" type="button">导出当前</button>
        <button class="btn" id="btn-export-all" type="button">导出全部</button>
      </div>
    </div>
    <pre id="log-view">正在读取日志...</pre>
    <div id="status" class="status">-</div>
  </div>
</div>
<script>
function qs(id){return document.getElementById(id)}
function pageHeaders(extra){var h={'X-LightRID-Page':'1'}; if(extra){Object.keys(extra).forEach(function(k){h[k]=extra[k]})} return h}
function apiUrl(path){return new URL(path, location.origin).toString()}
var authRedirecting=false;
function authExpired(r,d){var e=String((d&&d.error)||'');return r&&r.status===401&&((d&&d.auth_expired)||e==='login required'||e==='auth required')}
function redirectLogin(){if(authRedirecting)return;authRedirecting=true;location.href='/login?next=/'}
function loadTheme(){try{var s=localStorage.getItem('rid_ui_theme'); if(s==='light'||s==='dark') return s}catch(_e){} return (matchMedia && matchMedia('(prefers-color-scheme: light)').matches)?'light':'dark'}
function applyTheme(t){var light=t==='light'; document.body.classList.toggle('theme-light', light); try{localStorage.setItem('rid_ui_theme', light?'light':'dark')}catch(_e){} qs('btn-theme').textContent=light?'深色':'浅色'}
var currentType='runtime';
async function loadLogs(){
  var limit=Math.max(20, Math.min(5000, Number(qs('limit').value||500)));
  qs('status').textContent='正在读取...';
  var r=await fetch(apiUrl('/api/logs/view?type='+encodeURIComponent(currentType)+'&limit='+limit), {cache:'no-store', headers:pageHeaders()});
  var d=await r.json().catch(function(){return {}});
  if(authExpired(r,d)){redirectLogin();throw new Error('login required')}
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  qs('log-view').textContent=(d.items||[]).join('\\n') || '(empty)';
  qs('status').textContent=String(d.type||currentType)+' | '+String(d.count||0)+' lines';
}
function setType(t){
  currentType=t||'runtime';
  document.querySelectorAll('.tab').forEach(function(x){x.classList.toggle('active', x.getAttribute('data-type')===currentType)});
  loadLogs().catch(function(e){qs('status').textContent=e.message||String(e)});
}
async function downloadLogs(type){
  var limit=Math.max(20, Math.min(5000, Number(qs('limit').value||500)));
  var r=await fetch(apiUrl('/api/logs/export?type='+encodeURIComponent(type||currentType)+'&limit='+limit), {cache:'no-store', headers:pageHeaders()});
  if(r.status===401){
    var d=await r.clone().json().catch(function(){return {}});
    if(authExpired(r,d)){redirectLogin();throw new Error('login required')}
  }
  if(!r.ok) throw new Error('导出失败 HTTP '+r.status);
  var blob=await r.blob();
  if(!blob || !blob.size) throw new Error('导出内容为空');
  var cd=r.headers.get('Content-Disposition')||'';
  var m=/filename="([^"]+)"/.exec(cd);
  var name=m?m[1]:'light-rid-logs.log';
  var url=URL.createObjectURL(blob);
  var a=document.createElement('a'); a.href=url; a.download=name; document.body.appendChild(a); a.click();
  setTimeout(function(){URL.revokeObjectURL(url); if(a.parentNode)a.parentNode.removeChild(a)}, 8000);
}
document.querySelectorAll('.tab').forEach(function(btn){btn.addEventListener('click', function(){setType(btn.getAttribute('data-type'))})});
qs('btn-refresh').addEventListener('click', function(){loadLogs().catch(function(e){qs('status').textContent=e.message||String(e)})});
qs('btn-export').addEventListener('click', function(){downloadLogs(currentType).catch(function(e){qs('status').textContent=e.message||String(e)})});
qs('btn-export-all').addEventListener('click', function(){downloadLogs('all').catch(function(e){qs('status').textContent=e.message||String(e)})});
qs('btn-back').addEventListener('click', function(){location.href='/'});
qs('btn-settings').addEventListener('click', function(){location.href='/settings'});
qs('btn-theme').addEventListener('click', function(){applyTheme(document.body.classList.contains('theme-light')?'dark':'light')});
applyTheme(loadTheme());
loadLogs().catch(function(e){qs('status').textContent=e.message||String(e)});
</script></body></html>"""

def _build_oobe_html() -> str:
    return """<!doctype html><html lang="zh"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>初始化 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}:root{--font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;--bg:#f3f2f1;--card:#fff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;--muted:#605e5c;--blue:#0078d4;--warn:#d83b01}
@media(prefers-color-scheme:dark){:root{--bg:#201f1e;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;--muted:#c8c6c4;--blue:#2899f5;--warn:#f7630c}}
html,body{margin:0;min-height:100dvh;background:linear-gradient(180deg,var(--bg),var(--card2));color:var(--txt);font-family:var(--font-ui)}body{display:grid;place-items:center;padding:22px}
.card{width:min(720px,100%);border:1px solid var(--border);background:var(--card);border-radius:4px;box-shadow:0 16px 34px rgba(0,0,0,.16);padding:24px}
h1{margin:0 0 8px;font:700 28px/1.1 var(--font-ui)}.desc{color:var(--muted);line-height:1.55;margin-bottom:18px}.reason{border:1px solid color-mix(in srgb,var(--warn) 45%,var(--border));background:color-mix(in srgb,var(--warn) 10%,var(--card2));border-radius:4px;padding:10px 12px;margin-bottom:16px}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}.field{display:grid;gap:7px}.field.full{grid-column:1/-1}label{font:700 12px/1 var(--font-ui);color:var(--muted)}
input,select{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 12px;font:600 14px/1.2 var(--font-ui)}input:focus,select:focus{outline:none;border-color:var(--blue)}
.actions{display:flex;gap:10px;flex-wrap:wrap;justify-content:flex-end;margin-top:18px}.btn{height:42px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:0 16px;font:700 14px/1 var(--font-ui);cursor:pointer}.btn.primary{border-color:var(--blue);background:var(--blue);color:#fff}.status{margin-top:12px;color:var(--muted);white-space:pre-wrap}.status.err{color:var(--warn)}.micro{font-size:12px;color:var(--muted);line-height:1.5}@media(max-width:720px){body{padding:10px}.grid{grid-template-columns:1fr}.card{padding:18px}}
</style></head><body><main class="card">
<h1>Light RID Scanner 初始化</h1>
<div class="desc">程序需要绑定一张固定无线网卡。不会再自动递增选择其他网卡，避免多网卡环境下抓错设备。</div>
<div class="reason" id="reason">正在读取状态...</div>
<div class="grid">
  <div class="field full"><label>默认网卡</label><select id="iface"><option value="">正在扫描...</option></select><div class="micro">如果没有网卡，请插入支持 monitor 的无线网卡后刷新。</div></div>
  <div class="field"><label>RID 信道</label><input id="channel" type="number" min="1" max="196" value="6"><div class="micro">默认 CH6，通常无需修改。</div></div>
  <div class="field"><label>基站名称</label><input id="base-name" value="基站"></div>
  <div class="field"><label>基站纬度</label><input id="base-lat" type="number" step="0.000001"></div>
  <div class="field"><label>基站经度</label><input id="base-lon" type="number" step="0.000001"></div>
  <div class="field"><label>网页登录账号</label><input id="username" autocomplete="username" placeholder="可选"></div>
  <div class="field"><label>网页登录密码</label><input id="password" type="password" autocomplete="new-password" placeholder="可选"></div>
</div>
<div class="actions"><button class="btn" id="btn-refresh" type="button">刷新网卡</button><button class="btn" id="btn-custom-bind" type="button">自定义网卡绑定</button><button class="btn" id="btn-location" type="button">读取浏览器位置</button><button class="btn primary" id="btn-save" type="button">保存并进入系统</button></div>
<div class="field full" id="bind-panel" style="display:none;margin-top:14px"><label>网卡用途</label><div id="bind-list" class="grid"></div><div class="micro">“扫描”会同步为默认网卡；“AP热点网页服务”使用 172.16.0.1/24、内置 DHCP 和 172.16.0.1:80。</div></div>
<div id="status" class="status">-</div>
</main><script>
function qs(id){return document.getElementById(id)}function pageHeaders(extra){var h={'X-LightRID-Page':'1'};if(extra){Object.keys(extra).forEach(function(k){h[k]=extra[k]})}return h}function setStatus(t,e){qs('status').textContent=t||'-';qs('status').classList.toggle('err',!!e)}function enc(v){return String(v==null?'':v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;')}var authRedirecting=false;var oobeIfaces=[];var oobeBindings={items:[],ap:{}};function authExpired(r,d){var e=String((d&&d.error)||'');return r&&r.status===401&&((d&&d.auth_expired)||e==='login required'||e==='auth required')}function redirectLogin(){if(authRedirecting)return;authRedirecting=true;location.href='/login?next=/'}
function roleOpts(sel){var roles=[['none','None'],['scan','扫描'],['web','网页服务'],['ap_web','AP热点网页服务'],['disabled','禁用'],['idle','闲置']];return roles.map(function(r){return '<option value="'+r[0]+'" '+(r[0]===sel?'selected':'')+'>'+r[1]+'</option>'}).join('')}
function renderBindList(){var map={};(oobeBindings.items||[]).forEach(function(x){if(x&&x.iface)map[x.iface]=x.role||'none'});var selected=qs('iface').value||'';if(selected&&!map[selected])map[selected]='scan';qs('bind-list').innerHTML=(oobeIfaces||[]).map(function(it){var name=String(it.name||'');if(!name)return '';var role=map[name]||(name===selected?'scan':String(it.detected_role||'none'));var meta=(it.model?('型号 '+it.model+' | '):'')+(it.is_wireless?'无线 ':'有线 ')+(it.mode||'')+(it.admin_up===false?' | 已禁用':'')+(it.state?(' | '+it.state):'')+((it.ipv4&&it.ipv4.length)?(' | '+it.ipv4.join(',')):'');return '<div class="field"><label>'+enc(name)+'</label><select class="bind-role" data-iface="'+enc(name)+'">'+roleOpts(role)+'</select><div class="micro">'+enc(meta)+'</div></div>'}).join('')||'<div class="micro">未检测到网卡</div>'}
function collectBindings(){var items=[].slice.call(document.querySelectorAll('.bind-role')).map(function(sel){return {iface:sel.getAttribute('data-iface')||'',role:sel.value||'none'}}).filter(function(x){return x.iface});if(!items.some(function(x){return x.role==='scan'})&&qs('iface').value)items.push({iface:qs('iface').value,role:'scan'});return {items:items,ap:Object.assign({ssid:'LightRID-HotSpot',password:'',channel:6,address:'172.16.0.1',cidr:'172.16.0.1/24',dhcp_start:'172.16.0.20',dhcp_end:'172.16.0.240',http_port:80},oobeBindings.ap||{})}}
async function loadStatus(){const r=await fetch('/api/oobe/status',{cache:'no-store',headers:pageHeaders()});const d=await r.json().catch(()=>({}));if(authExpired(r,d)){redirectLogin();throw new Error('login required')}if(!r.ok||d.ok===false)throw new Error(d.error||('HTTP '+r.status));qs('reason').textContent=(d.oobe&&d.oobe.reason)||'需要完成基础配置。';oobeIfaces=d.interfaces||[];oobeBindings=d.network_bindings||{items:[],ap:{}};var opts=['<option value="">请选择默认网卡</option>'];(oobeIfaces||[]).forEach(function(it){var name=String(it.name||'');var kind=it.is_wireless?((it.mode||'wireless')+' '+(it.supports_5g?'5G':'2.4G')):'LAN';if(it.admin_up===false)kind+=' disabled';if(name)opts.push('<option value="'+enc(name)+'">'+enc(name+' ['+kind+']')+'</option>')});qs('iface').innerHTML=opts.join('');qs('iface').value=d.selected_iface||'';qs('channel').value=String(d.channel||6);qs('base-name').value=String(d.base_name||'基站');qs('base-lat').value=d.base_lat==null?'':String(d.base_lat);qs('base-lon').value=d.base_lon==null?'':String(d.base_lon);renderBindList();setStatus((oobeIfaces||[]).length?'请选择网卡后保存。':'未检测到网卡。',!(oobeIfaces||[]).length)}
async function save(){var body={iface:qs('iface').value,channel:Number(qs('channel').value||6),base_name:qs('base-name').value,base_lat:qs('base-lat').value,base_lon:qs('base-lon').value,username:qs('username').value,password:qs('password').value,network_bindings:collectBindings()};setStatus('正在保存...',false);const r=await fetch('/api/oobe/save',{method:'POST',headers:pageHeaders({'Content-Type':'application/json'}),body:JSON.stringify(body)});const d=await r.json().catch(()=>({}));if(authExpired(r,d)){redirectLogin();throw new Error('login required')}if(!r.ok||d.ok===false)throw new Error(d.error||('HTTP '+r.status));setStatus(d.login_required?'已保存，请先登录。':'已保存，正在进入系统...',false);setTimeout(function(){location.href=String(d.next||'/')},600)}
qs('btn-refresh').addEventListener('click',function(){loadStatus().catch(e=>setStatus(e.message||String(e),true))});qs('btn-custom-bind').addEventListener('click',function(){var p=qs('bind-panel');p.style.display=p.style.display==='none'?'block':'none';renderBindList()});qs('iface').addEventListener('change',renderBindList);qs('btn-save').addEventListener('click',function(){save().catch(e=>setStatus(e.message||String(e),true))});qs('btn-location').addEventListener('click',function(){if(!navigator.geolocation){setStatus('浏览器不支持定位',true);return}navigator.geolocation.getCurrentPosition(function(pos){qs('base-lat').value=String(pos.coords.latitude||'');qs('base-lon').value=String(pos.coords.longitude||'');setStatus('已读取浏览器位置',false)},function(err){setStatus('定位失败: '+(err&&err.message?err.message:err),true)},{enableHighAccuracy:true,timeout:12000,maximumAge:0})});loadStatus().catch(e=>setStatus(e.message||String(e),true));
</script></body></html>"""

def _station_asset_roots() -> list[Path]:
    roots: list[Path] = []
    base_dir = Path(__file__).resolve().parent
    roots.append(base_dir)
    frozen_root = getattr(sys, "_MEIPASS", None)
    if frozen_root:
        roots.append(Path(frozen_root) / "station_edition" / "light_rid")
    roots.append(Path.cwd() / "station_edition" / "light_rid")
    roots.append(Path.cwd() / "light_rid")
    unique_roots: list[Path] = []
    seen: set[str] = set()
    for root in roots:
        key = os.path.normcase(str(root))
        if key in seen:
            continue
        seen.add(key)
        unique_roots.append(root)
    return unique_roots


def _station_asset_path(*parts: str) -> Path | None:
    for root in _station_asset_roots():
        candidate = root.joinpath(*parts)
        try:
            if candidate.is_file():
                return candidate
        except OSError:
            continue
    return None


def _station_settings_asset_url() -> str:
    asset_url = "/assets/vue/station-settings.js"
    asset_path = _station_asset_path("assets", "vue", "station-settings.js")
    if asset_path is None:
        return asset_url
    try:
        st = asset_path.stat()
        return f"{asset_url}?v={int(st.st_mtime)}-{int(st.st_size)}"
    except OSError:
        return asset_url

def _station_settings_template_path() -> Path | None:
    return _station_asset_path("assets", "templates", "station-settings.html")

def _build_settings_html() -> str:
    template_path = _station_settings_template_path()
    if template_path is None:
        return '<!doctype html><html lang="zh"><head><meta charset="utf-8"><title>Light RID Scanner</title></head><body>settings template missing</body></html>'
    try:
        html_src = template_path.read_text(encoding="utf-8")
    except OSError:
        return '<!doctype html><html lang="zh"><head><meta charset="utf-8"><title>Light RID Scanner</title></head><body>settings template missing</body></html>'
    return html_src.replace("</body>", f'<script src="{_station_settings_asset_url()}"></script></body>', 1)

def sanitize_http_header_value(value, fallback: str = "") -> str:
    raw = value if value not in (None, "") else fallback
    return str(raw).replace("\r", "").replace("\n", "")

def http_server_thread() -> None:
    import socket as _socket
    import threading as _threading
    from http.server import BaseHTTPRequestHandler, HTTPServer
    from socketserver import ThreadingMixIn

    class ThreadingHTTPServer(ThreadingMixIn, HTTPServer):
        daemon_threads = True
        allow_reuse_address = True

    class Handler(BaseHTTPRequestHandler):
        server_version = APP_SERVER_HEADER
        sys_version = ""

        def end_headers(self):
            set_tok = getattr(self, "_auth_set_cookie_token", "")
            if set_tok:
                self.send_header(
                    "Set-Cookie",
                    sanitize_http_header_value(
                        f"{AUTH_SESSION_COOKIE}={set_tok}; Max-Age={int(AUTH_SESSION_TTL_SEC)}; Path=/; HttpOnly; SameSite=Lax"
                    ),
                )
                self._auth_set_cookie_token = ""
            if getattr(self, "_auth_clear_cookie", False):
                self.send_header(
                    "Set-Cookie",
                    sanitize_http_header_value(
                        f"{AUTH_SESSION_COOKIE}=; Max-Age=0; Path=/; HttpOnly; SameSite=Lax"
                    ),
                )
                self._auth_clear_cookie = False
            self.send_header("X-Content-Type-Options", "nosniff")
            self.send_header("X-Frame-Options", "DENY")
            self.send_header("Referrer-Policy", "strict-origin-when-cross-origin")
            self.send_header("Permissions-Policy", "geolocation=(self), microphone=(), camera=()")
            self.send_header(
                "Content-Security-Policy",
                "default-src 'self'; "
                "base-uri 'self'; object-src 'none'; frame-ancestors 'none'; form-action 'self'; "
                "script-src 'self' 'unsafe-inline' https://unpkg.com; "
                "style-src 'self' 'unsafe-inline' https://unpkg.com https://fonts.googleapis.com; "
                "font-src 'self' https://fonts.gstatic.com data:; "
                "img-src 'self' data: blob: https://*.is.autonavi.com; "
                "connect-src 'self' ws: wss: https://unpkg.com; "
                "media-src 'none'"
            )
            super().end_headers()

        def handle(self):
            try:
                return super().handle()
            except OSError as e:
                # Browser/WebSocket clients may disconnect abruptly; avoid noisy traceback.
                if getattr(e, "errno", None) in (32, 54, 104, 10053, 10054):
                    return
                raise

        def _send_json(self, obj: dict, code: int = 200):
            body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except OSError as e:
                if getattr(e, "errno", None) not in (32, 54, 104, 10053, 10054):
                    raise

        def _send_bytes(self, body: bytes, content_type: str, filename: str | None = None, code: int = 200):
            body = bytes(body or b"")
            self.send_response(code)
            self.send_header(
                "Content-Type",
                sanitize_http_header_value(content_type, "application/octet-stream"),
            )
            self.send_header("Cache-Control", "no-store")
            if filename:
                safe = (
                    re.sub(r'[^A-Za-z0-9._-]+', '_', str(filename or "download.bin")).strip("._")
                    or "download.bin"
                )
                self.send_header(
                    "Content-Disposition",
                    sanitize_http_header_value(f'attachment; filename="{safe}"'),
                )
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except OSError as e:
                if getattr(e, "errno", None) not in (32, 54, 104, 10053, 10054):
                    raise

        def _redirect(self, location: str, code: int = 302):
            self.send_response(code)
            self.send_header("Location", sanitize_http_header_value(location, "/"))
            self.send_header("Content-Length", "0")
            self.end_headers()

        def _read_json_body(self) -> dict:
            try:
                n = int(self.headers.get("Content-Length", "0") or "0")
            except Exception:
                n = 0
            if n > HTTP_JSON_MAX_BYTES:
                try:
                    self.rfile.read(min(n, 4096))
                except Exception:
                    pass
                return {}
            raw = b""
            if n > 0:
                try:
                    raw = self.rfile.read(n)
                except Exception:
                    raw = b""
            if not raw:
                return {}
            try:
                obj = json.loads(raw.decode("utf-8", errors="replace"))
            except Exception:
                return {}
            return obj if isinstance(obj, dict) else {}

        def _read_binary_upload_info(self) -> tuple[str, int]:
            raw_name = str(self.headers.get(APP_UPDATE_UPLOAD_NAME_HEADER) or "").strip()
            try:
                file_name = unquote(raw_name) if raw_name else ""
            except Exception:
                file_name = raw_name
            try:
                n = int(self.headers.get("Content-Length", "0") or "0")
            except Exception:
                n = 0
            return file_name, max(0, n)

        def _auth_fail(self):
            self.send_response(401)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            body = json.dumps({
                "ok": False,
                "error": "auth required",
                "auth_expired": True,
                "login_url": "/login?next=/",
            }, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _api_token_fail(self):
            self.send_response(401)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            body = json.dumps({
                "ok": False,
                "error": "api token required",
                "hint": "use X-API-Token or Authorization: Bearer <token>",
            }, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _rate_limit_fail(self, retry_after: int = 60):
            body = json.dumps({
                "ok": False,
                "error": "too many attempts",
                "retry_after_sec": int(max(1, retry_after)),
            }, ensure_ascii=False).encode("utf-8")
            self.send_response(429)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Retry-After", str(int(max(1, retry_after))))
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _page_api_fail(self, code: int = 403, message: str = "page session required"):
            self.send_response(code)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            payload = {
                "ok": False,
                "error": message,
                "hint": "call this endpoint from the built-in web pages",
            }
            if int(code) == 401:
                payload["auth_expired"] = True
                payload["login_url"] = "/login?next=/"
            body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _api_whitelist_fail(self):
            self.send_response(403)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            body = json.dumps({
                "ok": False,
                "error": "当前无权访问该界面",
            }, ensure_ascii=False).encode("utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _access_denied_page(self):
            body = '<!doctype html><html lang="zh"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>403</title><style>body{margin:0;min-height:100dvh;display:grid;place-items:center;background:#201f1e;color:#f3f2f1;font-family:"Segoe UI","Microsoft YaHei",sans-serif}.box{border:1px solid #3b3a39;background:#2b2a29;padding:24px;border-radius:4px}h1{margin:0;font-size:26px}</style></head><body><div class="box"><h1>当前无权访问该界面</h1></div></body></html>'.encode("utf-8")
            self.send_response(403)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            try:
                self.wfile.write(body)
            except Exception:
                pass

        def _require_auth(self) -> bool:
            if not _web_access_allowed(_client_ip_from_handler(self)):
                _op_log("web-access-deny", str(self.path or ""), ip=_client_ip_from_handler(self), ok=False)
                self._access_denied_page()
                return False
            if not _auth_enabled():
                return True
            if _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                return True
            req_path = str(self.path or "").split("?", 1)[0]
            if req_path == "/ws":
                # Avoid Safari repeatedly showing Basic-Auth dialog on websocket reconnect.
                self.send_response(403)
                self.send_header("Content-Length", "0")
                self.end_headers()
                return False
            if req_path.startswith("/api/"):
                self._auth_fail()
                return False
            try:
                from urllib.parse import quote
                target = str(self.path or "/")
                if not target.startswith("/") or target.startswith("//"):
                    target = "/"
                self._redirect("/login?next=" + quote(target, safe="/?=&%"))
            except Exception:
                self._redirect("/login")
            return False

        def _require_page_api(self) -> bool:
            if not _web_access_allowed(_client_ip_from_handler(self)):
                _op_log("web-api-deny", str(self.path or ""), ip=_client_ip_from_handler(self), ok=False)
                self._page_api_fail(403, "当前无权访问该界面")
                return False
            if not _request_same_origin(self.headers):
                self._page_api_fail(403, "cross-origin page api denied")
                return False
            if not _page_api_header_ok(self.headers):
                self._page_api_fail(403, "page api header required")
                return False
            if _auth_enabled() and not _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                self._page_api_fail(401, "login required")
                return False
            return True

        def _require_raw_config_access(self) -> bool:
            if not self._require_page_api():
                return False
            if not (_auth_enabled() and _auth_hashes_present(AUTH_CFG)):
                return True
            if _raw_config_unlocked(self.headers.get("Cookie")):
                return True
            self._page_api_fail(403, "raw config unlock required")
            return False

        def _require_api_token(self, query: dict | None = None) -> bool:
            if not _api_token_enabled():
                return False
            ip = self.client_address[0] if self.client_address else ""
            if bool(API_CFG.get("whitelist_enabled")) and (not _api_access_allowed(ip)):
                _op_log("api-whitelist-deny", str(self.path or ""), ip=str(ip or "-"), ok=False)
                self._api_whitelist_fail()
                return False
            limited, retry_after = _rate_limited("api-token", ip, str(self.path or ""), limit=24, window_sec=120, block_sec=600)
            if limited:
                self._rate_limit_fail(retry_after)
                return False
            token = _api_token_from_request(self.headers, query)
            matched_token = _api_token_check_value(token)
            if matched_token:
                if bool(matched_token.get("single_use")):
                    _api_mark_token_used(str(matched_token.get("id") or ""))
                _rate_note("api-token", ip, str(self.path or ""), success=True, limit=24, window_sec=120, block_sec=600)
                return True
            _rate_note("api-token", ip, str(self.path or ""), success=False, limit=24, window_sec=120, block_sec=600)
            _op_log("api-token-deny", str(self.path or ""), ip=str(ip or "-"), ok=False)
            self._api_token_fail()
            return False

        def _require_public_api(self, query: dict | None = None) -> bool:
            if _api_token_enabled():
                return self._require_api_token(query)
            return self._require_page_api()

        def _send_captive_portal_page(self) -> None:
            host = str(globals().get("AP_WEB_ADDRESS_DEFAULT", "172.16.0.1") or "172.16.0.1")
            target = f"http://{host}/"
            body = (
                "<!doctype html><html><head><meta charset=\"utf-8\">"
                f"<meta http-equiv=\"refresh\" content=\"0;url={target}\">"
                "<title>Light RID Scanner</title></head>"
                f"<body><p>正在打开 Light RID Scanner 页面。<a href=\"{target}\">立即打开</a></p></body></html>"
            ).encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Cache-Control", "no-store")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)

        def _send_asset_file(self, path: str) -> bool:
            from urllib.parse import unquote
            rel = unquote(str(path or "")[len("/assets/"):]).replace("\\", "/")
            parts = [p for p in rel.split("/") if p and p not in (".", "..")]
            if not parts or "/".join(parts) != rel:
                self._send_json({"ok": False, "error": "invalid asset path"}, 400)
                return True
            try:
                package_dir = getattr(globals().get("RUNTIME_CONTEXT"), "package_dir", None)
                base_dir = os.path.join(str(package_dir or os.path.dirname(__file__)), "assets")
                full = os.path.abspath(os.path.join(base_dir, *parts))
                base_abs = os.path.abspath(base_dir)
                if not (full == base_abs or full.startswith(base_abs + os.sep)) or not os.path.isfile(full):
                    self.send_response(404)
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                    return True
                ext = os.path.splitext(full)[1].lower()
                ctype = {
                    ".css": "text/css; charset=utf-8",
                    ".js": "application/javascript; charset=utf-8",
                    ".png": "image/png",
                    ".svg": "image/svg+xml; charset=utf-8",
                    ".map": "application/json; charset=utf-8",
                }.get(ext, "application/octet-stream")
                with open(full, "rb") as f:
                    body = f.read()
                self.send_response(200)
                self.send_header("Content-Type", ctype)
                if path.startswith("/assets/vue/") and ext in {".js", ".map"}:
                    self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                else:
                    self.send_header("Cache-Control", "public, max-age=86400")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return True
            except Exception as e:
                self._send_json({"ok": False, "error": str(e)}, 500)
                return True

        def do_GET(self):
            from urllib.parse import urlparse, parse_qs, quote, unquote
            parsed = urlparse(self.path)
            path = parsed.path
            query = parse_qs(parsed.query or "")
            if path.startswith("/assets/"):
                self._send_asset_file(path)
                return
            if path in (
                "/generate_204",
                "/gen_204",
                "/hotspot-detect.html",
                "/library/test/success.html",
                "/connecttest.txt",
                "/ncsi.txt",
                "/canonical.html",
                "/success.txt",
            ):
                self._send_captive_portal_page()
                return
            if path == "/favicon.ico":
                self.send_response(204)
                self.send_header("Cache-Control", "max-age=86400")
                self.send_header("Content-Length", "0")
                self.end_headers()
                return
            if path == "/api/eula/status":
                self._send_json(_eula_status_payload(), 200)
                return
            if path == "/api/config/tree":
                if not self._require_raw_config_access():
                    return
                try:
                    root = _config_root_dir()
                    self._send_json({
                        "ok": True,
                        "root": root,
                        "root_name": os.path.basename(root.rstrip("\\/")) or root,
                        "tree": _config_tree_entries(root).get("tree") or [],
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path == "/api/config/file":
                if not self._require_raw_config_access():
                    return
                try:
                    file_path = _config_resolve_path((query.get("path") or [""])[0] if isinstance(query, dict) else None)
                    if not file_path:
                        self._send_json({"ok": False, "error": "invalid path"}, 400)
                        return
                    root = _config_root_dir()
                    with open(file_path, "r", encoding="utf-8") as f:
                        text = f.read()
                    st = os.stat(file_path)
                    self._send_json({
                        "ok": True,
                        "path": file_path,
                        "rel_path": _config_rel_path(file_path, root),
                        "root": root,
                        "name": os.path.basename(file_path),
                        "text": text,
                        "size": int(st.st_size),
                        "mtime": float(st.st_mtime),
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path in ("/eula", "/eula.html"):
                next_path = str((query.get("next") or ["/"])[0] or "/")
                if not next_path.startswith("/") or next_path.startswith("//"):
                    next_path = "/"
                body = _build_eula_html(next_path).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            if _eula_redirect_required(path):
                if path.startswith("/api/"):
                    self._send_json({
                        "ok": False,
                        "error": "eula required",
                        "eula_url": EULA_URL,
                    }, 428)
                else:
                    target = str(self.path or "/")
                    if not target.startswith("/") or target.startswith("//"):
                        target = "/"
                    self._redirect("/eula?next=" + quote(target, safe="/?=&%"))
                return
            if (not path.startswith("/api/")) and path != "/ws" and (not _web_access_allowed(_client_ip_from_handler(self))):
                _op_log("web-access-deny", str(self.path or ""), ip=_client_ip_from_handler(self), ok=False)
                self._access_denied_page()
                return
            if path == "/api/oobe/status":
                if not self._require_page_api():
                    return
                self._send_json(_oobe_status_payload(), 200)
                return
            if path in ("/oobe", "/oobe.html"):
                manual_oobe = _to_bool((query.get("manual") or ["0"])[0], False)
                if not _oobe_state().get("required") and not manual_oobe:
                    self._redirect("/")
                    return
                if (_auth_enabled() and _auth_hashes_present(AUTH_CFG)) and not _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                    self._redirect("/login?next=/oobe")
                    return
                body = _build_oobe_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            if _oobe_redirect_required(path) and not (path in ("/login", "/login.html") and _oobe_auth_required()):
                if path == "/ws":
                    self.send_response(503)
                    self.send_header("Content-Length", "0")
                    self.end_headers()
                elif path.startswith("/api/"):
                    self._send_json({
                        "ok": False,
                        "error": "oobe required",
                        "oobe": _oobe_state(),
                    }, 409)
                else:
                    self._redirect("/oobe")
                return
            if path in ("/login", "/login.html"):
                next_path = str((query.get("next") or ["/"])[0] or "/")
                if not next_path.startswith("/") or next_path.startswith("//"):
                    next_path = "/"
                if not _auth_enabled():
                    self._redirect(next_path)
                    return
                user_value = str((query.get("user") or [""])[0] or "")
                pass_value = str((query.get("password") or [""])[0] or "")
                check_code = str((query.get("check") or [""])[0] or "")
                if user_value and not pass_value and ",password=" in user_value:
                    _ignored_user, pass_value = user_value.split(",password=", 1)
                if user_value and not pass_value and "?password=" in user_value:
                    _ignored_user, pass_value = user_value.split("?password=", 1)
                if pass_value and not check_code and "?check=" in pass_value:
                    _ignored_pass, check_code = pass_value.split("?check=", 1)
                if check_code:
                    ip = _client_ip_from_handler(self)
                    subject = check_code[:12]
                    limited, retry_after = _rate_limited("login-sso", ip, subject, limit=8, window_sec=300, block_sec=900)
                    if limited:
                        self._rate_limit_fail(retry_after)
                        return
                    sso_item = _auth_check_sso_link(check_code)
                    ok_login = bool(sso_item)
                    _rate_note("login-sso", ip, subject, success=ok_login, limit=8, window_sec=300, block_sec=900)
                    _op_log("login-sso", "next=" + next_path, actor=subject, ip=ip, ok=ok_login)
                    if ok_login:
                        if bool((sso_item or {}).get("single_use")):
                            _auth_mark_sso_used(check_code)
                        self._auth_set_cookie_token = _auth_issue_session()
                        sso_next = str((sso_item or {}).get("next") or next_path or "/")
                        if not sso_next.startswith("/") or sso_next.startswith("//"):
                            sso_next = "/"
                        self._redirect(sso_next)
                    else:
                        body = _build_login_html(next_path, "SSO 登录失败或链接已失效", True).encode("utf-8")
                        self.send_response(401)
                        self.send_header("Content-Type", "text/html; charset=utf-8")
                        self.send_header("Content-Length", str(len(body)))
                        self.end_headers()
                        self.wfile.write(body)
                    return
                if _auth_check_session_cookie(self.headers.get("Cookie"), refresh=True):
                    self._redirect(next_path)
                    return
                body = _build_login_html(next_path).encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
                return
            if path == "/logout":
                _op_log("logout", "", ip=_client_ip_from_handler(self), ok=True)
                self._auth_clear_cookie = True
                self._redirect("/login")
                return
            if path == "/api/update-health":
                if not _update_probe_header_ok(self.headers):
                    self._send_json({"ok": False, "error": "probe header required"}, 403)
                    return
                now_wall = time.time()
                self._send_json({
                    "ok": True,
                    "time": _api_iso_now(now_wall),
                    "service": {
                        "uptime_sec": int(max(0.0, now_wall - APP_START_WALL)),
                    },
                }, 200)
                return
            if _path_uses_api_token(path):
                if not self._require_public_api(query):
                    return
            elif _path_is_page_api(path):
                if not self._require_page_api():
                    return
            elif not self._require_auth():
                return
            if path in ("/api", "/api/"):
                if not self._require_page_api():
                    return
                self._send_json(_api_token_docs_payload(), 200)
                return
            if path == "/api/docs":
                self._send_json(_api_token_docs_payload(), 200)
                return
            if path == "/api/health":
                now_mono = time.monotonic()
                now_wall = time.time()
                sniff = _sniff_health_meta(now_mono, now_wall)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "service": {
                        "uptime_sec": int(max(0.0, now_wall - APP_START_WALL)),
                        "sniff_state": sniff.get("state"),
                        "sniff_msg": sniff.get("msg"),
                        "sniff_iface": sniff.get("iface"),
                        "current_channel": int(current_channel or 0),
                    },
                }, 200)
                return
            if path in ("/api/v1", "/api/v1/"):
                self._send_json(_api_v1_home_payload(), 200)
                return
            if path == "/api/v1/snapshot":
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "data": _state_snapshot(),
                }, 200)
                return
            if path == "/api/v1/auth/status":
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "auth": (_api_v1_home_payload().get("auth") or {}),
                }, 200)
                return
            if path == "/api/v1/drones":
                online_only = _to_bool((query.get("online_only") or ["0"])[0], False)
                include_archived = _to_bool((query.get("include_archived") or ["1"])[0], True)
                snap = _state_snapshot()
                items = list(snap.get("drones") or [])
                if online_only:
                    items = [x for x in items if not bool(x.get("lost")) and not bool(x.get("archived"))]
                elif not include_archived:
                    items = [x for x in items if not bool(x.get("archived"))]
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "count": len(items),
                    "items": items,
                }, 200)
                return
            if path == "/api/v1/metrics":
                raw_window = str((query.get("window") or ["24h"])[0] or "24h").strip().lower()
                if raw_window in ("12h", "12"):
                    window_sec = 12 * 3600
                elif raw_window in ("7d", "7"):
                    window_sec = 7 * 86400
                else:
                    window_sec = 24 * 3600
                payload = _host_metrics_payload(window_sec=window_sec)
                payload["api"] = _api_meta()
                self._send_json(payload, 200)
                return
            if path.startswith("/api/v1/drones/"):
                sn = unquote(path[len("/api/v1/drones/"):]).strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                snap = _state_snapshot()
                item = None
                for x in (snap.get("drones") or []):
                    if str(x.get("sn") or "") == sn:
                        item = x
                        break
                if not item:
                    self._send_json({"ok": False, "error": "sn not found"}, 404)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    track = _track_for_query(src.get("track") or [], query, firmware_type=src.get("firmware_type"))
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "item": item,
                    "track_count": len(track),
                    "track": track,
                }, 200)
                return
            if path == "/api/v1/aps":
                aps, aps_seq, aps_total = _ap_snapshot()
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "seq": aps_seq,
                    "total": aps_total,
                    "count": len(aps),
                    "items": aps,
                }, 200)
                return
            if path == "/api/v1/logs":
                log_type = str((query.get("type") or ["event"])[0] or "event").strip().lower()
                try:
                    limit = int((query.get("limit") or ["200"])[0] or "200")
                except Exception:
                    limit = 200
                limit = max(1, min(2000, limit))
                with log_lock:
                    if log_type == "scan":
                        rows = list(scan_buf)[-limit:]
                    elif log_type == "ap":
                        rows = list(ap_buf)[-limit:]
                    else:
                        log_type = "event"
                        rows = list(log_buf)[-limit:]
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "type": log_type,
                    "count": len(rows),
                    "items": rows,
                }, 200)
                return
            if path.startswith("/api/v1/tracks/"):
                sn = unquote(path[len("/api/v1/tracks/"):]).strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    track = _track_for_query(src.get("track") or [], query, firmware_type=src.get("firmware_type"))
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "sn": sn,
                    "count": len(track),
                    "track": track,
                }, 200)
                return
            if path in ("/", "/index.html"):
                body = _build_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path in ("/settings", "/settings.html"):
                body = _build_settings_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path in ("/logs", "/logs.html"):
                body = _build_logs_html().encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path in ("/hardware-assistant", "/hardware-assistant.html"):
                body = _HW_PAGE_HTML.encode("utf-8")
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Cache-Control", "no-store, no-cache, must-revalidate, max-age=0")
                self.send_header("Pragma", "no-cache")
                self.send_header("Expires", "0")
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)
            elif path == "/api/config":
                if not self._require_raw_config_access():
                    return
                try:
                    self._send_json(_config_file_payload(APP_CONFIG_PATH), 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/config/tree":
                if not self._require_raw_config_access():
                    return
                try:
                    root = _config_root_dir()
                    self._send_json({
                        "ok": True,
                        "root": root,
                        "root_name": os.path.basename(root.rstrip("\\/")) or root,
                        "tree": _config_tree_entries(root).get("tree") or [],
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/config/file":
                if not self._require_raw_config_access():
                    return
                try:
                    file_path = _config_resolve_path((query.get("path") or [""])[0] if isinstance(query, dict) else None)
                    if not file_path:
                        self._send_json({"ok": False, "error": "invalid path"}, 400)
                        return
                    root = _config_root_dir()
                    with open(file_path, "r", encoding="utf-8") as f:
                        text = f.read()
                    st = os.stat(file_path)
                    self._send_json({
                        "ok": True,
                        "path": file_path,
                        "rel_path": _config_rel_path(file_path, root),
                        "root": root,
                        "name": os.path.basename(file_path),
                        "text": text,
                        "size": int(st.st_size),
                        "mtime": float(st.st_mtime),
                        "raw_access": _raw_config_access_payload(self.headers),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/settings/view":
                try:
                    self._send_json(_settings_view_payload(), 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/notifications":
                try:
                    limit = int((query.get("limit") or [str(NOTIFICATION_CENTER_MAX)])[0] or NOTIFICATION_CENTER_MAX)
                except Exception:
                    limit = NOTIFICATION_CENTER_MAX
                self._send_json(_notification_payload(limit), 200)
            elif path == "/api/settings/runtime":
                try:
                    limit = int((query.get("limit") or ["180"])[0] or "180")
                except Exception:
                    limit = 180
                self._send_json(_settings_runtime_payload(limit=limit), 200)
            elif path == "/api/settings/metrics":
                raw_window = str((query.get("window") or ["24h"])[0] or "24h").strip().lower()
                if raw_window in ("12h", "12"):
                    window_sec = 12 * 3600
                elif raw_window in ("7d", "7"):
                    window_sec = 7 * 86400
                else:
                    window_sec = 24 * 3600
                self._send_json(_host_metrics_payload(window_sec=window_sec), 200)
            elif path == "/api/settings/systemd/status":
                self._send_json(_systemd_service_status_payload(), 200)
            elif path == "/api/settings/models/list":
                self._send_json(_model_map_editor_payload(), 200)
            elif path == "/api/logs/view":
                try:
                    limit = int((query.get("limit") or ["500"])[0] or "500")
                except Exception:
                    limit = 500
                log_type = str((query.get("type") or ["runtime"])[0] or "runtime")
                self._send_json(_logs_snapshot(log_type, limit=limit), 200)
            elif path == "/api/logs/export":
                try:
                    limit = int((query.get("limit") or ["5000"])[0] or "5000")
                except Exception:
                    limit = 5000
                log_type = str((query.get("type") or ["all"])[0] or "all")
                try:
                    body, filename, ctype = _logs_export_bytes(log_type, limit=limit)
                    _op_log("logs-export", f"type={log_type} limit={limit}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_bytes(body, ctype, filename=filename, code=200)
                except Exception as e:
                    _op_log("logs-export", f"type={log_type} error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/interfaces":
                try:
                    basic = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
                    if not isinstance(basic, dict):
                        basic = {}
                    self._send_json({
                        "ok": True,
                        "items": _iface_options_snapshot(),
                        "active_iface": str(sniff_iface_name or ""),
                        "selected_iface": (None if basic.get("iface") in (None, "") else str(basic.get("iface"))),
                        "scan_wifi_fast": bool(basic.get("scan_wifi_fast")),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/network-bindings/status":
                try:
                    self._send_json(_network_bindings_status_payload(), 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/hw/status":
                try:
                    snap = _hw_submit_task({"op": "status"}, timeout_sec=10)
                    if snap.get("ok") and isinstance(snap.get("data"), dict):
                        data = snap.get("data")
                        data["ok"] = True
                        self._send_json(data, 200)
                    else:
                        self._send_json({"ok": False, "error": str(snap.get("error") or "status failed")}, 500)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/tracks/get":
                sn = ""
                try:
                    sn = str((query.get("sn") or [""])[0] or "").strip()
                except Exception:
                    sn = ""
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    firmware_type = src.get("firmware_type")
                    full_track = _track_for_query(src.get("track") or [], firmware_type=firmware_type)
                    track = _track_for_query(src.get("track") or [], query, firmware_type=firmware_type)
                self._send_json({
                    "ok": True,
                    "sn": sn,
                    "count": len(track),
                    "count_total": len(full_track),
                    "track": track,
                }, 200)
            elif path == "/api/tools/export/all":
                with state_lock:
                    items = _history_disk_items_locked()
                _op_log("tools-export-all", f"count={len(items)}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "version": 1,
                    "exported_at": time.time(),
                    "count": len(items),
                    "items": items,
                }, 200)
            elif path == "/api/tools/export/track":
                sn = ""
                try:
                    sn = str((query.get("sn") or [""])[0] or "").strip()
                except Exception:
                    sn = ""
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                with state_lock:
                    src = history_table.get(sn) or state_table.get(sn) or {}
                    track = _sanitize_track(src.get("track") or [])
                _op_log("tools-export-track", f"sn={sn} count={len(track)}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "version": 1,
                    "exported_at": time.time(),
                    "sn": sn,
                    "count": len(track),
                    "track": track,
                }, 200)
            elif path == "/api/settings/export/settings":
                payload = _settings_export_payload()
                _op_log("settings-export", f"path={payload.get('config_path') or '-'}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json(payload, 200)
            elif path == "/api/settings/export/scan-data":
                payload = _scan_data_export_payload()
                _op_log("scan-data-export", f"count={payload.get('count') or 0}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json(payload, 200)
            elif path == "/api/tools/diagnostic.zip":
                try:
                    body, filename = _diagnostic_zip_bytes()
                    _op_log("diagnostic-export", f"filename={filename} bytes={len(body)}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_bytes(body, "application/zip", filename=filename, code=200)
                except Exception as e:
                    _op_log("diagnostic-export", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/ws":
                # Headers are already parsed by BaseHTTPRequestHandler; read key directly.
                origin = str(self.headers.get("Origin") or "").strip()
                host = str(self.headers.get("Host") or "").strip()
                if origin and host:
                    try:
                        from urllib.parse import urlparse as _urlparse
                        o = _urlparse(origin)
                        if o.netloc and o.netloc.lower() != host.lower():
                            self.send_response(403)
                            self.end_headers()
                            return
                    except Exception:
                        pass
                key = self.headers.get("Sec-WebSocket-Key","").strip()
                if not key:
                    self.send_response(400); self.end_headers(); return
                import base64 as _b64, hashlib as _hl
                accept = _b64.b64encode(
                    _hl.sha1((key+"258EAFA5-E914-47DA-95CA-C5AB0DC85B11").encode()).digest()
                ).decode()
                resp = ("HTTP/1.1 101 Switching Protocols\r\n"
                        "Upgrade: websocket\r\nConnection: Upgrade\r\n"
                        f"Sec-WebSocket-Accept: {accept}\r\n\r\n")
                self.connection.sendall(resp.encode())
                sock = self.connection
                with _ws_lock:
                    _ws_clients.append(sock)
                import json as _json
                try:
                    sock.sendall(_ws_frame(
                        _json.dumps(_state_snapshot(), ensure_ascii=False).encode()))
                except Exception:
                    pass
                # Keep connection open and drain incoming frames until disconnect.
                try:
                    sock.settimeout(120)
                    while True:
                        hdr = sock.recv(2)
                        if not hdr or len(hdr) < 2: break
                        b1, b2 = hdr[0], hdr[1]
                        masked = bool(b2 & 0x80)
                        pl = b2 & 0x7F
                        if pl == 126:
                            pl = int.from_bytes(sock.recv(2), "big")
                        elif pl == 127:
                            pl = int.from_bytes(sock.recv(8), "big")
                        to_read = (4 if masked else 0) + pl
                        while to_read > 0:
                            chunk = sock.recv(min(to_read, 4096))
                            if not chunk: break
                            to_read -= len(chunk)
                        if (b1 & 0x0F) == 8: break  # close frame
                except Exception:
                    pass
                with _ws_lock:
                    if sock in _ws_clients: _ws_clients.remove(sock)
                try: sock.close()
                except Exception: pass
            else:
                self.send_response(404); self.end_headers()

        def do_POST(self):
            from urllib.parse import urlparse
            path = urlparse(self.path).path
            if path == "/api/eula/accept":
                if not _request_same_origin(self.headers) or not _page_api_header_ok(self.headers):
                    self._page_api_fail(403, "page api header required")
                    return
                body = self._read_json_body()
                if not _to_bool(body.get("accepted"), False):
                    self._send_json({"ok": False, "error": "必须同意许可协议后才能继续"}, 400)
                    return
                ok, msg = _write_eula_acceptance()
                if not ok:
                    self._send_json({"ok": False, "error": msg}, 500)
                    return
                next_path = str(body.get("next") or "/")
                if not next_path.startswith("/") or next_path.startswith("//"):
                    next_path = "/"
                self._send_json({"ok": True, "accepted": True, "next": next_path, "set_path": msg}, 200)
                return
            if _eula_redirect_required(path):
                self._send_json({
                    "ok": False,
                    "error": "eula required",
                    "eula_url": EULA_URL,
                }, 428)
                return
            if path == "/api/oobe/save":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                rsp = _oobe_save_config(body)
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
                return
            if path == "/api/settings/raw/unlock":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                user = str(body.get("username") or "").strip()
                pwd = str(body.get("password") or "")
                if not user or not pwd:
                    self._send_json({"ok": False, "error": "账号和密码必须同时填写", "raw_access": _raw_config_access_payload(self.headers)}, 400)
                    return
                if not _auth_check_userpass(user, pwd):
                    self._send_json({"ok": False, "error": "账号或密码错误", "raw_access": _raw_config_access_payload(self.headers)}, 401)
                    return
                _raw_config_unlock_set(self.headers.get("Cookie"))
                self._send_json({
                    "ok": True,
                    "unlocked": True,
                    "raw_access": _raw_config_access_payload(self.headers),
                }, 200)
                return
            if path == "/api/passkey/login/start":
                if not _request_same_origin(self.headers) or not _page_api_header_ok(self.headers):
                    self._page_api_fail(403, "page api header required")
                    return
                self._read_json_body()
                rsp = _passkey_login_begin(self.headers)
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
                return
            if path == "/api/passkey/login/finish":
                if not _request_same_origin(self.headers) or not _page_api_header_ok(self.headers):
                    self._page_api_fail(403, "page api header required")
                    return
                body = self._read_json_body()
                rsp, code = _passkey_finish_login(body, self.headers, client_ip=_client_ip_from_handler(self))
                if rsp.get("ok"):
                    self._auth_set_cookie_token = str(rsp.pop("session") or "")
                self._send_json(rsp, code)
                return
            if _oobe_redirect_required(path) and not (path in ("/login", "/login.html") and _oobe_auth_required()):
                self._send_json({
                    "ok": False,
                    "error": "oobe required",
                    "oobe": _oobe_state(),
                }, 409)
                return
            if path in ("/login", "/login.html"):
                body = self._read_json_body()
                user = str(body.get("username") or "")
                pwd = str(body.get("password") or "")
                if not _auth_login_method_enabled("password"):
                    self._send_json({"ok": False, "error": "账号密码登录已关闭"}, 403)
                    return
                ip = _client_ip_from_handler(self)
                limited, retry_after = _rate_limited("login", ip, user, limit=8, window_sec=300, block_sec=900)
                if limited:
                    self._rate_limit_fail(retry_after)
                    return
                ok_login = _auth_check_userpass(user, pwd)
                _rate_note("login", ip, user, success=ok_login, limit=8, window_sec=300, block_sec=900)
                _op_log("login", "", actor=user or "-", ip=ip, ok=ok_login)
                if ok_login:
                    self._auth_set_cookie_token = _auth_issue_session()
                    self._send_json({"ok": True, "next": "/"}, 200)
                else:
                    self._send_json({"ok": False, "error": "账号或密码错误"}, 401)
                return
            if _path_uses_api_token(path):
                if not self._require_public_api(None):
                    return
            elif _path_is_page_api(path):
                if not self._require_page_api():
                    return
            elif not self._require_auth():
                return
            try:
                body_len = int(self.headers.get("Content-Length", "0") or "0")
            except Exception:
                body_len = 0
            if body_len > HTTP_JSON_MAX_BYTES:
                self._send_json({"ok": False, "error": f"request too large (>{HTTP_JSON_MAX_BYTES} bytes)"}, 413)
                return
            if path == "/api/notifications":
                body = self._read_json_body()
                item = _notification_add(
                    str(body.get("text") or ""),
                    str(body.get("kind") or "info"),
                    "page",
                )
                if not item:
                    self._send_json({"ok": False, "error": "text required"}, 400)
                    return
                payload = _notification_payload()
                payload["item"] = item
                self._send_json(payload, 200)
                return
            if path == "/api/notifications/delete":
                body = self._read_json_body()
                removed = _notification_delete(body.get("id"))
                payload = _notification_payload()
                payload["removed"] = bool(removed)
                self._send_json(payload, 200)
                return
            if path == "/api/notifications/clear":
                self._read_json_body()
                cleared = _notification_clear()
                self._send_json({"ok": True, "cleared": cleared, "seq": int(notification_seq), "count": 0, "items": []}, 200)
                return
            if path == "/api/eula/revoke":
                self._read_json_body()
                ok, msg = _revoke_eula_acceptance()
                if not ok:
                    self._send_json({"ok": False, "error": msg}, 500)
                    return
                self._send_json({"ok": True, "accepted": False, "set_path": msg, "next": "/eula?next=/settings"}, 200)
                return
            if path == "/api/v1/auth/logout":
                self._send_json({"ok": True, "api": _api_meta(), "logout": False, "token_api": True}, 200)
                return
            if path == "/api/v1/history/clear":
                try:
                    cleared, removed = clear_history_store(delete_file=True)
                    _op_log("api-v1-history-clear", f"cleared={cleared} file_removed={removed}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_json({
                        "ok": True,
                        "api": _api_meta(),
                        "cleared": cleared,
                        "file_removed": removed,
                        "history_file": HISTORY_STORE_PATH,
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path == "/api/v1/history/delete":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                removed = delete_history_item(sn)
                _op_log("api-v1-history-delete", f"sn={sn} removed={removed}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "sn": sn,
                    "removed": bool(removed),
                }, 200)
                return
            if path == "/api/v1/tracks/clear":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                affected = clear_track_store(sn if sn else None)
                _op_log("api-v1-track-clear", f"sn={sn or '*'} affected={affected}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "api": _api_meta(),
                    "sn": (sn or None),
                    "affected": int(affected),
                }, 200)
                return
            if path == "/api/v1/config/reload":
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                try:
                    cfg_loaded = load_app_config(APP_CONFIG_PATH)
                    r_ok, r_msg = reload_runtime_config(cfg_loaded)
                    _op_log("api-v1-config-reload", f"ok={r_ok} msg={r_msg}", ip=_client_ip_from_handler(self), ok=bool(r_ok))
                    self._send_json({
                        "ok": True,
                        "api": _api_meta(),
                        "reloaded": bool(r_ok),
                        "reload_msg": str(r_msg or ""),
                        "config_path": APP_CONFIG_PATH,
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
                return
            if path == "/api/v1/history/reparse":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip() if isinstance(body, dict) else ""
                mode = str(body.get("mode") or "auto") if isinstance(body, dict) else "auto"
                try:
                    rsp = reidentify_history_packet_for_sn(sn, mode=mode)
                    rsp["api"] = _api_meta()
                    _op_log("api-v1-history-reparse", f"sn={sn} mode={mode} ok={bool(rsp.get('ok'))}", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("api-v1-history-reparse", f"sn={sn} mode={mode} error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e), "api": _api_meta()}, 500)
                return
            if path == "/api/v1/history/reidentify-recent":
                body = self._read_json_body()
                try:
                    limit = int(body.get("limit") or HISTORY_RAW_PACKET_LIMIT) if isinstance(body, dict) else HISTORY_RAW_PACKET_LIMIT
                except Exception:
                    limit = HISTORY_RAW_PACKET_LIMIT
                try:
                    rsp = reidentify_recent_history_packets(limit=limit)
                    rsp["api"] = _api_meta()
                    summary = f"aircraft={rsp.get('updated_aircraft')}/{rsp.get('aircraft_count')} packets={rsp.get('decoded')}/{rsp.get('packet_count')}"
                    _op_log("api-v1-history-reidentify-recent", str(rsp.get("error") or summary), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("api-v1-history-reidentify-recent", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e), "api": _api_meta()}, 500)
                return
            if path == "/api/history/clear":
                self._read_json_body()
                try:
                    cleared, removed = clear_history_store(delete_file=True)
                    _op_log("history-clear", f"cleared={cleared} file_removed={removed}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_json({
                        "ok": True,
                        "cleared": cleared,
                        "file_removed": removed,
                        "history_file": HISTORY_STORE_PATH,
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/history/delete":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                removed = delete_history_item(sn)
                _op_log("history-delete", f"sn={sn} removed={removed}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "sn": sn, "removed": bool(removed)}, 200)
            elif path == "/api/history/reparse":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip() if isinstance(body, dict) else ""
                mode = str(body.get("mode") or "auto") if isinstance(body, dict) else "auto"
                try:
                    rsp = reidentify_history_packet_for_sn(sn, mode=mode)
                    _op_log("history-reparse", f"sn={sn} mode={mode} ok={bool(rsp.get('ok'))}", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("history-reparse", f"sn={sn} mode={mode} error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path in ("/api/settings/history/reidentify-recent", "/api/settings/history/reidentify-latest"):
                body = self._read_json_body()
                try:
                    limit = int(body.get("limit") or HISTORY_RAW_PACKET_LIMIT) if isinstance(body, dict) else HISTORY_RAW_PACKET_LIMIT
                except Exception:
                    limit = HISTORY_RAW_PACKET_LIMIT
                try:
                    rsp = reidentify_recent_history_packets(limit=limit)
                    summary = f"aircraft={rsp.get('updated_aircraft')}/{rsp.get('aircraft_count')} packets={rsp.get('decoded')}/{rsp.get('packet_count')}"
                    _op_log("history-reidentify-recent", str(rsp.get("error") or summary), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("history-reidentify-recent", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/settings/import/settings":
                body = self._read_json_body()
                payload = body.get("payload", body) if isinstance(body, dict) else body
                rsp = _import_settings_payload(payload)
                _op_log("settings-import", f"ok={bool(rsp.get('ok'))}", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
            elif path == "/api/settings/import/scan-data":
                body = self._read_json_body()
                payload = body.get("payload", body) if isinstance(body, dict) else body
                mode = str(body.get("mode") or "merge") if isinstance(body, dict) else "merge"
                rsp = _import_scan_data_payload(payload, mode=mode)
                _op_log("scan-data-import", f"mode={rsp.get('mode') or mode} ok={bool(rsp.get('ok'))}", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
            elif path == "/api/tracks/clear":
                body = self._read_json_body()
                sn = str(body.get("sn") or "").strip()
                affected = clear_track_store(sn if sn else None)
                _op_log("track-clear", f"sn={sn or '*'} affected={affected}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "sn": (sn or None),
                    "affected": int(affected),
                }, 200)
            elif path == "/api/tools/import/all":
                body = self._read_json_body()
                payload = body.get("payload", body) if isinstance(body, dict) else body
                valid_payload = False
                if isinstance(payload, list):
                    valid_payload = True
                elif isinstance(payload, dict):
                    valid_payload = isinstance(payload.get("items"), list) or isinstance(payload.get("drones"), list)
                if not valid_payload:
                    self._send_json({"ok": False, "error": "invalid payload: expect items[]/drones[] or list"}, 400)
                    return
                added, updated, skipped = import_details_payload(payload)
                _op_log("tools-import-all", f"added={added} updated={updated} skipped={skipped}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "added": int(added),
                    "updated": int(updated),
                    "skipped": int(skipped),
                }, 200)
            elif path == "/api/tools/import/track":
                body = self._read_json_body()
                payload = body.get("payload", body) if isinstance(body, dict) else body
                if not isinstance(payload, dict):
                    self._send_json({"ok": False, "error": "payload must be object"}, 400)
                    return
                sn = str(payload.get("sn") or body.get("sn") or "").strip()
                if not sn:
                    self._send_json({"ok": False, "error": "sn required"}, 400)
                    return
                track_raw = payload.get("track")
                if not isinstance(track_raw, list):
                    self._send_json({"ok": False, "error": "track must be array"}, 400)
                    return
                track = _sanitize_track(track_raw if isinstance(track_raw, list) else [])
                with state_lock:
                    h = history_table.get(sn) or {"sn": sn, "pkt_count_total": 0}
                    h["sn"] = sn
                    h["track"] = track
                    h["track_updated_wall_ts"] = (float(track[-1]["ts"]) if track else time.time())
                    history_table[sn] = h
                    e = state_table.get(sn)
                    if isinstance(e, dict):
                        e["track"] = list(track)
                        e["track_updated_wall_ts"] = h["track_updated_wall_ts"]
                    _history_mark_dirty()
                _op_log("tools-import-track", f"sn={sn} count={len(track)}", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({
                    "ok": True,
                    "sn": sn,
                    "count": len(track),
                }, 200)
            elif path == "/api/hw/op":
                body = self._read_json_body()
                op = str(body.get("op") or "").strip().lower()
                if not op:
                    self._send_json({"ok": False, "error": "op required"}, 400)
                    return
                try:
                    rsp = _hw_submit_task(body, timeout_sec=15)
                    code = 200 if rsp.get("ok") else 500
                    _op_log("hw-op", f"op={op} ok={rsp.get('ok')} iface={body.get('iface') or ''}", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                    self._send_json(rsp, code)
                except Exception as e:
                    _op_log("hw-op", f"op={op} error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/admin/restart":
                body = self._read_json_body()
                if not bool(WEB_CFG.get("allow_restart", True)):
                    self._send_json({"ok": False, "error": "restart disabled"}, 403)
                    return
                args_text = str(body.get("args") or "")
                save_cfg = bool(body.get("save"))
                iface_override_raw = body.get("iface")
                iface_override = None if iface_override_raw in (None, "") else str(iface_override_raw).strip()
                scan_wifi_fast_override = body.get("scan_wifi_fast")
                try:
                    tokens, raw = _parse_restart_args_text(args_text)
                    if iface_override_raw is not None:
                        tokens = _merge_token_option(tokens, "--iface", iface_override)
                    if scan_wifi_fast_override is not None:
                        tokens = _merge_token_flag(tokens, "--scan-wifi-fast", _to_bool(scan_wifi_fast_override, False))
                    if save_cfg:
                        overrides: dict = {}
                        if iface_override_raw is not None:
                            overrides["iface"] = iface_override
                        if scan_wifi_fast_override is not None:
                            overrides["scan_wifi_fast"] = _to_bool(scan_wifi_fast_override, False)
                        ok, msg = _save_basic_config_from_tokens(
                            tokens,
                            raw_text=raw or args_text,
                            overrides=overrides,
                        )
                        if not ok:
                            self._send_json({"ok": False, "error": f"save config failed: {msg}"}, 400)
                            return
                    ok, msg = _schedule_self_restart(tokens)
                    if not ok:
                        _op_log("admin-restart", f"schedule_failed={msg}", ip=_client_ip_from_handler(self), ok=False)
                        self._send_json({"ok": False, "error": msg}, 409)
                        return
                    _op_log("admin-restart", f"save={save_cfg} args={tokens}", ip=_client_ip_from_handler(self), ok=True)
                    self._send_json({
                        "ok": True,
                        "restarting": True,
                        "save": save_cfg,
                        "args": tokens,
                    }, 200)
                except ValueError as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/config/save":
                if not self._require_raw_config_access():
                    return
                body = self._read_json_body()
                try:
                    rsp = _config_file_save_payload(str(body.get("path") or APP_CONFIG_PATH or ""), str(body.get("text") or ""), tag="config")
                    self._send_json(rsp, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
            elif path == "/api/settings/visual/test":
                body = self._read_json_body()
                rsp = _save_visual_settings(body, test_only=True)
                _op_log("settings-test", str(rsp.get("error") or rsp.get("reload_msg") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
            elif path == "/api/settings/visual/save":
                body = self._read_json_body()
                rsp = _save_visual_settings(body, test_only=False)
                _op_log("settings-save", str(rsp.get("error") or rsp.get("backup_path") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
            elif path == "/api/settings/raw/save":
                if not self._require_raw_config_access():
                    return
                body = self._read_json_body()
                try:
                    rsp = _config_file_save_payload(str(body.get("path") or APP_CONFIG_PATH or ""), str(body.get("text") or ""), tag="raw")
                    self._send_json(rsp, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
            elif path == "/api/config/file/delete":
                if not self._require_raw_config_access():
                    return
                body = self._read_json_body()
                try:
                    rsp = _config_file_delete_payload(str(body.get("path") or ""))
                    self._send_json(rsp, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 400)
            elif path == "/api/settings/passkey/start":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                rsp = _passkey_register_begin(body, self.headers, client_ip=_client_ip_from_handler(self))
                code = 200
                if isinstance(rsp, tuple):
                    payload, code = rsp
                    self._send_json(payload, code)
                else:
                    code = 200 if rsp.get("ok") else 400
                    self._send_json(rsp, code)
            elif path == "/api/settings/passkey/finish":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                rsp, code = _passkey_finish_register(body, self.headers, client_ip=_client_ip_from_handler(self))
                self._send_json(rsp, code)
            elif path == "/api/settings/passkey/delete":
                if not self._require_page_api():
                    return
                body = self._read_json_body()
                passkey_id = str(body.get("id") or "").strip()
                if not passkey_id:
                    self._send_json({"ok": False, "error": "id required"}, 400)
                    return
                def _remove_passkey(items):
                    return [x for x in items if str((x or {}).get("id") or "") != passkey_id]
                ok, msg, passkeys = _auth_mutate_passkeys(_remove_passkey, tag="passkey_delete")
                if not ok:
                    self._send_json({"ok": False, "error": msg, "passkeys": passkeys}, 500)
                    return
                _op_log("passkey-delete", "id=" + passkey_id[:16], actor="-", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "passkeys": passkeys, "id": passkey_id}, 200)
                return
            elif path == "/api/settings/notify/test":
                ok, resp = send_test_notification_from_config()
                _op_log("notify-test", str(resp or ""), ip=_client_ip_from_handler(self), ok=bool(ok))
                self._send_json({"ok": bool(ok), "resp": resp}, 200 if ok else 500)
            elif path == "/api/settings/models/update":
                body = self._read_json_body()
                rsp = update_model_map_from_url(manual=True, url_override=str(body.get("url") or "").strip() or None)
                self._send_json(rsp, 200 if rsp.get("ok") else 500)
            elif path == "/api/settings/app-update/check":
                self._read_json_body()
                rsp = _check_app_update_once(manual=True)
                self._send_json(rsp, 200 if rsp.get("ok") else 500)
            elif path == "/api/settings/app-update/download":
                self._read_json_body()
                rsp = _start_app_update_download(manual=True)
                _op_log("app-update-download", str(rsp.get("error") or rsp.get("message") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 500)
            elif path == "/api/settings/app-update/upload":
                file_name, body_len = self._read_binary_upload_info()
                if not file_name:
                    self._send_json({"ok": False, "error": "upload file name missing"}, 400)
                    return
                try:
                    meta = _accept_uploaded_app_update_package(file_name, self.rfile, body_len)
                    rsp = {
                        "ok": True,
                        "message": f"{meta.get('asset_name') or file_name} 已上传并通过 SHA256 校验。",
                        "state": _app_update_status_payload(),
                    }
                    _op_log("app-update-upload", str(meta.get("asset_name") or file_name), ip=_client_ip_from_handler(self), ok=True)
                    self._send_json(rsp, 200)
                except Exception as e:
                    _op_log("app-update-upload", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e), "state": _app_update_status_payload()}, 400)
            elif path == "/api/settings/app-update/start":
                body = self._read_json_body()
                if not bool(body.get("confirm")):
                    self._send_json({"ok": False, "error": "confirm required", "state": _app_update_status_payload()}, 400)
                    return
                rsp = _start_app_update_install(manual=True, sudo_password=_sudo_password_from_body(body))
                _op_log("app-update-start", str(rsp.get("error") or rsp.get("message") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                code = 200 if rsp.get("ok") else 500
                if (not rsp.get("ok")) and (bool(rsp.get("need_sudo")) or "root" in str(rsp.get("error") or "") or "sudo" in str(rsp.get("error") or "") or "权限" in str(rsp.get("error") or "")):
                    code = 403
                self._send_json(rsp, code)
            elif path == "/api/network-bindings/save":
                body = self._read_json_body()
                rsp = _network_bindings_save_payload(body)
                _op_log("network-bindings-save", str(rsp.get("error") or rsp.get("reload_msg") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 400)
            elif path == "/api/network-bindings/apply":
                body = self._read_json_body()
                rsp = _network_bindings_apply_payload(body)
                _op_log("network-bindings-apply", str(rsp.get("error") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                self._send_json(rsp, 200 if rsp.get("ok") else 500)
            elif path == "/api/settings/systemd/register":
                body = self._read_json_body()
                if not bool(body.get("confirm")):
                    self._send_json({"ok": False, "error": "confirm required", "status": _systemd_service_status_payload()}, 400)
                    return
                rsp = register_systemd_service(sudo_password=_sudo_password_from_body(body))
                _op_log("systemd-register", str(rsp.get("error") or rsp.get("message") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                if rsp.get("ok"):
                    self._send_json(rsp, 200)
                else:
                    err = str(rsp.get("error") or "")
                    code = 403 if ("root" in err or "权限" in err) else 500
                    self._send_json(rsp, code)
            elif path == "/api/settings/iw/install":
                body = self._read_json_body()
                if not bool(body.get("confirm")):
                    self._send_json({"ok": False, "error": "confirm required", "status": _systemd_service_status_payload()}, 400)
                    return
                rsp = _install_iw_package(sudo_password=_sudo_password_from_body(body))
                status = _systemd_service_status_payload()
                payload = dict(rsp)
                payload["status"] = status
                payload["message"] = "无线工具已安装并可用。" if rsp.get("ok") else str(rsp.get("error") or "无线工具安装失败")
                _op_log("iw-install", payload.get("message") or "", ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                if rsp.get("ok"):
                    self._send_json(payload, 200)
                else:
                    err = str(rsp.get("error") or "")
                    code = 403 if ("root" in err or "权限" in err) else 500
                    self._send_json(payload, code)
            elif path == "/api/settings/security/repair":
                body = self._read_json_body()
                if not bool(body.get("confirm")):
                    self._send_json({"ok": False, "error": "confirm required", "status": _systemd_service_status_payload()}, 400)
                    return
                rsp = repair_runtime_security(sudo_password=_sudo_password_from_body(body))
                _op_log("security-repair", str(rsp.get("error") or rsp.get("message") or ""), ip=_client_ip_from_handler(self), ok=bool(rsp.get("ok")))
                if rsp.get("ok"):
                    self._send_json(rsp, 200)
                else:
                    err = str(rsp.get("error") or "")
                    code = 403 if ("root" in err or "权限" in err or "sudo" in err) else 500
                    self._send_json(rsp, code)
            elif path == "/api/settings/models/save":
                body = self._read_json_body()
                try:
                    rsp = save_model_map_entries(body.get("items") if isinstance(body, dict) else None)
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("model-map-save", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e), "state": _model_update_status_payload()}, 400)
            elif path == "/api/settings/models/upsert":
                body = self._read_json_body()
                try:
                    rsp = upsert_model_map_entry(
                        prefix=str(body.get("prefix") or ""),
                        model=str(body.get("model") or ""),
                        sn=str(body.get("sn") or ""),
                    )
                    self._send_json(rsp, 200 if rsp.get("ok") else 400)
                except Exception as e:
                    _op_log("model-map-upsert", f"error={e}", ip=_client_ip_from_handler(self), ok=False)
                    self._send_json({"ok": False, "error": str(e), "state": _model_update_status_payload()}, 400)
            elif path == "/api/settings/api-token/create":
                body = self._read_json_body()
                ip = _client_ip_from_handler(self)
                subject = str(body.get("username") or "-") if body else "-"
                limited, retry_after = _rate_limited("api-token-create", ip, subject, limit=5, window_sec=300, block_sec=900)
                if limited:
                    self._rate_limit_fail(retry_after)
                    return
                payload, code = _build_api_token_create_payload(body, headers=self.headers, client_ip=ip)
                _rate_note("api-token-create", ip, subject, success=bool(payload.get("ok")), limit=5, window_sec=300, block_sec=900)
                self._send_json(payload, code)
            elif path == "/api/settings/api-token/delete":
                body = self._read_json_body()
                token_id = str(body.get("id") or "").strip()
                if not token_id:
                    self._send_json({"ok": False, "error": "id required"}, 400)
                    return
                def _remove_token(tokens):
                    return [x for x in tokens if str((x or {}).get("id") or "") != token_id]
                ok, msg, tokens = _api_mutate_tokens(_remove_token, tag="api_token_delete")
                if not ok:
                    self._send_json({"ok": False, "error": msg, "tokens": tokens}, 500)
                    return
                _op_log("api-token-delete", "id=" + token_id[:16], actor="-", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "deleted": True, "tokens": tokens}, 200)
            elif path == "/api/v1/auth/sso-links/create":
                body = self._read_json_body()
                ip = _client_ip_from_handler(self)
                payload, code = _build_sso_link_payload(body, require_reauth=False, headers=self.headers, client_ip=ip)
                if payload.get("ok"):
                    host = str(self.headers.get("Host") or "").strip()
                    scheme = "https" if str(self.headers.get("X-Forwarded-Proto") or "").lower() == "https" else "http"
                    path_url = str(payload.get("path") or "")
                    payload["url"] = (f"{scheme}://{host}{path_url}" if host and path_url else path_url)
                    _op_log("api-sso-create", "next=" + str(payload.get("next") or "/"), ip=ip, ok=True)
                self._send_json(payload, code)
            elif path == "/api/settings/login-link/create":
                body = self._read_json_body()
                ip = _client_ip_from_handler(self)
                subject = str(body.get("username") or "-") if body else "-"
                limited, retry_after = _rate_limited("login-link-create", ip, subject, limit=5, window_sec=300, block_sec=900)
                if limited:
                    self._rate_limit_fail(retry_after)
                    return
                payload, code = _build_sso_link_payload(body, require_reauth=True, headers=self.headers, client_ip=ip)
                if payload.get("ok"):
                    _rate_note("login-link-create", ip, subject, success=True, limit=5, window_sec=300, block_sec=900)
                    host = str(self.headers.get("Host") or "").strip()
                    scheme = "https" if str(self.headers.get("X-Forwarded-Proto") or "").lower() == "https" else "http"
                    path_url = str(payload.get("path") or "")
                    payload["url"] = (f"{scheme}://{host}{path_url}" if host and path_url else path_url)
                    _op_log("login-link-create", "sso next=" + str(payload.get("next") or "/"), actor=subject, ip=ip, ok=True)
                elif code == 401:
                    _rate_note("login-link-create", ip, subject, success=False, limit=5, window_sec=300, block_sec=900)
                self._send_json(payload, code)
            elif path == "/api/settings/login-link/delete":
                body = self._read_json_body()
                check = str(body.get("check") or "").strip()
                if not check:
                    self._send_json({"ok": False, "error": "check required"}, 400)
                    return
                def _remove_link(links):
                    return [x for x in links if str((x or {}).get("check") or "") != check]
                ok, msg, links = _auth_mutate_sso_links(_remove_link, tag="sso_delete")
                if not ok:
                    self._send_json({"ok": False, "error": msg, "links": links}, 500)
                    return
                _op_log("login-link-delete", "check=" + check[:12], actor="-", ip=_client_ip_from_handler(self), ok=True)
                self._send_json({"ok": True, "deleted": True, "links": links}, 200)
            elif path == "/api/web/base/save":
                body = self._read_json_body()
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                base_name = str(body.get("base_name") or "基站").strip() or "基站"
                lat_raw = body.get("base_lat")
                lon_raw = body.get("base_lon")
                zoom_raw = body.get("base_zoom")
                heading_ref_raw = body.get("heading_ref_deg")
                map_idle_raw = body.get("map_auto_center_idle_sec")
                try:
                    base_lat = None if lat_raw in (None, "") else float(lat_raw)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid base_lat"}, 400)
                    return
                try:
                    base_lon = None if lon_raw in (None, "") else float(lon_raw)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid base_lon"}, 400)
                    return
                if (base_lat is None) != (base_lon is None):
                    self._send_json({"ok": False, "error": "base_lat/base_lon must be both set or both empty"}, 400)
                    return
                if base_lat is not None and not (-90.0 <= base_lat <= 90.0):
                    self._send_json({"ok": False, "error": "base_lat out of range [-90,90]"}, 400)
                    return
                if base_lon is not None and not (-180.0 <= base_lon <= 180.0):
                    self._send_json({"ok": False, "error": "base_lon out of range [-180,180]"}, 400)
                    return
                try:
                    base_zoom = int(zoom_raw if zoom_raw not in (None, "") else 13)
                except Exception:
                    base_zoom = 13
                base_zoom = max(3, min(30, base_zoom))
                try:
                    heading_ref_deg = float(heading_ref_raw if heading_ref_raw not in (None, "") else 0.0)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid heading_ref_deg"}, 400)
                    return
                heading_ref_deg = heading_ref_deg % 360.0
                if heading_ref_deg < 0:
                    heading_ref_deg += 360.0
                try:
                    map_auto_center_idle_sec = int(map_idle_raw if map_idle_raw not in (None, "") else 20)
                except Exception:
                    self._send_json({"ok": False, "error": "invalid map_auto_center_idle_sec"}, 400)
                    return
                map_auto_center_idle_sec = max(5, min(600, map_auto_center_idle_sec))
                try:
                    cfg = load_app_config(APP_CONFIG_PATH)
                    web_cfg = cfg.get("web")
                    if not isinstance(web_cfg, dict):
                        web_cfg = {}
                    web_cfg["base_name"] = base_name
                    web_cfg["base_lat"] = base_lat
                    web_cfg["base_lon"] = base_lon
                    web_cfg["base_zoom"] = base_zoom
                    web_cfg["heading_ref_deg"] = round(float(heading_ref_deg), 2)
                    web_cfg["map_auto_center_idle_sec"] = int(map_auto_center_idle_sec)
                    cfg["web"] = web_cfg
                    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="web-base")
                    if not b_ok:
                        self._send_json({"ok": False, "error": f"backup failed: {backup_path}"}, 500)
                        return
                    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
                    if not ok:
                        self._send_json({"ok": False, "error": f"save failed: {msg}"}, 500)
                        return
                    cfg_loaded = load_app_config(APP_CONFIG_PATH)
                    r_ok, r_msg = reload_runtime_config(cfg_loaded)
                    if not r_ok:
                        restore_config_backup(APP_CONFIG_PATH, backup_path)
                        self._send_json({"ok": False, "error": f"reload failed: {r_msg}", "backup_path": backup_path}, 500)
                        return
                    self._send_json({
                        "ok": True,
                        "saved_to": APP_CONFIG_PATH,
                        "backup_path": backup_path,
                        "reloaded": bool(r_ok),
                        "reload_msg": r_msg,
                        "base_name": str(WEB_CFG.get("base_name") or base_name),
                        "base_lat": WEB_CFG.get("base_lat"),
                        "base_lon": WEB_CFG.get("base_lon"),
                        "base_zoom": WEB_CFG.get("base_zoom"),
                        "heading_ref_deg": WEB_CFG.get("heading_ref_deg"),
                        "map_auto_center_idle_sec": WEB_CFG.get("map_auto_center_idle_sec"),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            elif path == "/api/web/basic/save":
                body = self._read_json_body()
                if not APP_CONFIG_PATH:
                    self._send_json({"ok": False, "error": "config path missing"}, 500)
                    return
                iface_raw = body.get("iface")
                iface = None if iface_raw in (None, "") else str(iface_raw).strip()
                if not iface:
                    self._send_json({"ok": False, "error": "必须选择默认网卡"}, 400)
                    return
                safe_iface = _hw_safe_iface(iface)
                if not safe_iface:
                    self._send_json({"ok": False, "error": "invalid iface"}, 400)
                    return
                iface = safe_iface
                scan_wifi_fast = _to_bool(body.get("scan_wifi_fast"), False)
                try:
                    cfg = load_app_config(APP_CONFIG_PATH)
                    basic_cfg = cfg.get("basic")
                    if not isinstance(basic_cfg, dict):
                        basic_cfg = {}
                    basic_cfg["iface"] = iface
                    basic_cfg["scan_wifi_fast"] = bool(scan_wifi_fast)
                    cfg["basic"] = basic_cfg
                    b_ok, backup_path = create_config_backup(APP_CONFIG_PATH, tag="web-basic")
                    if not b_ok:
                        self._send_json({"ok": False, "error": f"backup failed: {backup_path}"}, 500)
                        return
                    ok, msg = save_app_config(APP_CONFIG_PATH, cfg)
                    if not ok:
                        self._send_json({"ok": False, "error": f"save failed: {msg}"}, 500)
                        return
                    cfg_loaded = load_app_config(APP_CONFIG_PATH)
                    r_ok, r_msg = reload_runtime_config(cfg_loaded)
                    if not r_ok:
                        restore_config_backup(APP_CONFIG_PATH, backup_path)
                        self._send_json({"ok": False, "error": f"reload failed: {r_msg}", "backup_path": backup_path}, 500)
                        return
                    basic_now = APP_CONFIG.get("basic") if isinstance(APP_CONFIG, dict) else {}
                    if not isinstance(basic_now, dict):
                        basic_now = {}
                    self._send_json({
                        "ok": True,
                        "saved_to": APP_CONFIG_PATH,
                        "backup_path": backup_path,
                        "reloaded": bool(r_ok),
                        "reload_msg": r_msg,
                        "iface_selected": (None if basic_now.get("iface") in (None, "") else str(basic_now.get("iface"))),
                        "scan_wifi_fast": bool(basic_now.get("scan_wifi_fast")),
                    }, 200)
                except Exception as e:
                    self._send_json({"ok": False, "error": str(e)}, 500)
            else:
                self._send_json({"ok": False, "error": "not found"}, 404)

        def log_message(self, *_): pass

    try:
        srv = ThreadingHTTPServer(("0.0.0.0", HTTP_PORT), Handler)
    except OSError as e:
        _log(f"[WARN] HTTP+WS start failed (port {HTTP_PORT} in use): {e}; continue sniff only")
        return

    _threading.Thread(target=_ws_push_loop, daemon=True).start()
    start_bound_http_servers(ThreadingHTTPServer, Handler)
    start_network_binding_services()
    _log(f"[INFO] HTTP+WS service started: http://0.0.0.0:{HTTP_PORT}/")
    if not _auth_enabled():
        _log("[WARN] Web auth disabled: Web UI is exposed to LAN; enable auth in config for safety")
    if not _api_token_enabled():
        _log("[INFO] API public mode disabled: /api/docs, /api/health and /api/v1/* stay page-session-only")
    try:
        srv.serve_forever()
    except Exception as e:
        _log(f"[WARN] HTTP+WS service exception: {e}")

# -----------------------------------------------------------------------------
# parse_frame
# -----------------------------------------------------------------------------

