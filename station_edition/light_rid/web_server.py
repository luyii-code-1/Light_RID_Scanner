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
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--panel:#2b2a29;--panel2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --green:#92c353;--yellow:#ffb900;--dim:#c8c6c4;--blue:#2899f5;
  --purple:#caa0ff;--cyan:#7dc6ff;--glow:rgba(40,153,245,.12);--soft:rgba(255,255,255,.03)
}
body{background:var(--bg);color:var(--txt);font-family:var(--font-ui);font-size:16px;
     height:100dvh;display:grid;grid-template-rows:auto minmax(0,1fr) minmax(240px,38vh) auto;
     row-gap:12px;overflow:hidden;position:relative;
     transition:background-color .16s ease,color .16s ease;
     background:linear-gradient(180deg,var(--bg),var(--bg2) 18%,var(--bg))}
body.theme-light{
  --bg:#f3f2f1;--bg2:#edebe9;--panel:#ffffff;--panel2:#faf9f8;--border:#e1dfdd;--txt:#323130;
  --green:#107c10;--yellow:#986f0b;--dim:#605e5c;--blue:#0078d4;
  --purple:#6b5bd2;--cyan:#005a9e;--glow:rgba(0,120,212,.10);--soft:rgba(0,0,0,.018)
}
body::before{
  content:""; position:fixed; inset:0; pointer-events:none; z-index:0;
  background:linear-gradient(180deg, rgba(255,255,255,.04), rgba(255,255,255,0) 140px);
}
body.theme-light::before{
  background:linear-gradient(180deg, rgba(255,255,255,.65), rgba(255,255,255,0) 140px);
}
header,.tbl-wrap,.panel,footer{position:relative;z-index:1}
.mono, code, .logbox, .aplist, .adv-input, .stat b{font-family:var(--font-mono)}

/* -- Header -- */
header{background:var(--panel);border-bottom:1px solid var(--border);
       padding:10px 14px;display:grid;grid-template-columns:auto auto minmax(0,1fr);
       align-items:center;gap:8px 16px;position:sticky;top:0;z-index:10;
       box-shadow:0 1px 3px rgba(0,0,0,.12)}
header .head-stats{display:flex;align-items:center;justify-content:flex-end;
       gap:8px 16px;flex-wrap:wrap;min-width:0;grid-column:3}
header h1{font-size:20px;font-weight:600;color:var(--txt);letter-spacing:.01em;text-transform:none}
.app-version-label{font-family:var(--font-mono);font-size:12px;font-weight:600;line-height:1;color:var(--dim);white-space:nowrap}
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
  position:fixed;top:10px;left:50%;transform:translateX(-50%);
  display:flex;flex-direction:column;gap:8px;z-index:9998;
  width:min(92vw, 860px);pointer-events:none;
}
.banner{
  opacity:0;transform:translateY(-6px);
  transition:opacity .18s ease,transform .18s ease;
  border:1px solid var(--border);border-radius:4px;
  background:var(--panel);color:var(--txt);
  padding:9px 12px;font-size:13px;line-height:1.35;
  box-shadow:0 8px 18px rgba(0,0,0,.16);
}
.banner.show{opacity:1;transform:translateY(0)}
.banner.ok{border-color:color-mix(in srgb, var(--green) 40%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel));color:color-mix(in srgb, var(--green) 72%, white)}
.banner.warn{border-color:color-mix(in srgb, var(--yellow) 34%, var(--border));background:color-mix(in srgb, var(--yellow) 10%, var(--panel));color:#ffd9a9}
.notify-center-button{
  position:fixed;right:18px;bottom:18px;z-index:9999;width:54px;height:54px;border-radius:50%;
  border:1px solid color-mix(in srgb, var(--blue) 40%, var(--border));
  background:color-mix(in srgb, var(--panel) 92%, transparent);color:var(--txt);
  box-shadow:0 12px 28px rgba(0,0,0,.28);backdrop-filter:blur(10px);
  display:flex;align-items:center;justify-content:center;cursor:pointer;font:700 18px/1 var(--font-ui);
  transition:transform .14s ease,border-color .14s ease,background-color .14s ease,box-shadow .14s ease;
}
.notify-center-button:hover,.notify-center-button.active{transform:translateY(-2px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 12%, var(--panel));box-shadow:0 16px 34px rgba(0,0,0,.34)}
.notify-center-glyph{position:relative;width:22px;height:22px;border:2px solid currentColor;border-radius:50%;display:block}
.notify-center-glyph::before{content:"";position:absolute;left:50%;top:4px;width:2px;height:9px;background:currentColor;transform:translateX(-50%)}
.notify-center-glyph::after{content:"";position:absolute;left:50%;bottom:4px;width:4px;height:4px;border-radius:50%;background:currentColor;transform:translateX(-50%)}
.notify-center-count{
  position:absolute;right:-3px;top:-3px;min-width:20px;height:20px;padding:0 5px;border-radius:999px;
  display:none;align-items:center;justify-content:center;background:#d83b01;color:#fff;
  border:2px solid var(--panel);font:700 11px/1 var(--font-ui);
}
.notify-center-button.has-items .notify-center-count{display:flex}
.notify-center-panel{
  position:fixed;right:18px;bottom:84px;z-index:9999;width:min(380px,calc(100vw - 28px));
  max-height:min(560px,calc(100vh - 110px));display:none;flex-direction:column;overflow:hidden;
  border:1px solid var(--border);border-radius:6px;background:color-mix(in srgb, var(--panel) 96%, transparent);
  box-shadow:0 18px 42px rgba(0,0,0,.34);backdrop-filter:blur(14px);
}
.notify-center-panel.show{display:flex}
.notify-center-head{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:12px 14px;border-bottom:1px solid var(--border);background:color-mix(in srgb, var(--panel2) 84%, transparent)}
.notify-center-title{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.notify-center-sub{margin-top:4px;color:var(--dim);font-size:12px}
.notify-center-list{padding:8px;display:grid;gap:8px;overflow:auto}
.notify-center-empty{padding:28px 12px;text-align:center;color:var(--dim);font-size:13px}
.notify-item{display:grid;grid-template-columns:4px minmax(0,1fr) auto;gap:10px;align-items:start;padding:10px;border:1px solid color-mix(in srgb, var(--border) 86%, transparent);border-radius:5px;background:color-mix(in srgb, var(--panel2) 82%, transparent)}
.notify-item-bar{width:4px;height:100%;min-height:42px;border-radius:999px;background:var(--blue)}
.notify-item.ok .notify-item-bar{background:var(--green)}
.notify-item.warn .notify-item-bar{background:var(--yellow)}
.notify-item-text{color:var(--txt);font-size:13px;line-height:1.4;white-space:pre-wrap;word-break:break-word}
.notify-item-time{margin-top:6px;color:var(--dim);font-size:11px}
.notify-item-del{width:24px;height:24px;border:1px solid var(--border);border-radius:4px;background:var(--panel);color:var(--dim);cursor:pointer;line-height:1}
.notify-item-del:hover{border-color:var(--blue);color:var(--txt);background:color-mix(in srgb, var(--blue) 10%, var(--panel))}
#dot-ws{width:9px;height:9px;border-radius:50%;background:var(--dim);
        display:inline-block;margin-right:4px;transition:background .3s}
#dot-ws.on{background:var(--green)}

/* -- Table -- */
.tbl-wrap{margin:0 12px;min-height:0;overflow:auto;
          border:1px solid var(--border);border-radius:4px;background:var(--panel);
          box-shadow:0 1px 3px rgba(0,0,0,.08)}
table{width:100%;border-collapse:collapse;table-layout:fixed;min-width:980px}
thead tr{background:var(--panel2);position:sticky;top:0;z-index:9}
thead th{padding:9px 10px;text-align:left;font-size:14px;color:var(--dim);
          border-bottom:1px solid var(--border);white-space:nowrap}
tbody tr{border-bottom:1px solid color-mix(in srgb, var(--border) 70%, transparent);transition:background-color .14s ease}
tbody tr:hover{background:color-mix(in srgb, var(--blue) 7%, var(--panel))}
tbody tr.lost{opacity:.4}
tbody tr.selected{background:color-mix(in srgb, var(--blue) 12%, var(--panel))}
tbody tr.alarm-zone{background:color-mix(in srgb, #ff3b30 12%, var(--panel));animation:alarmRowPulse .9s ease-in-out infinite alternate}
td{padding:8px 10px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;font-size:16px}
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

.panel{border:1px solid var(--border);border-radius:8px;overflow:hidden;
       display:flex;flex-direction:column;min-height:0;
       box-shadow:0 12px 26px rgba(0,0,0,.22), 0 0 0 1px rgba(97,183,255,.04) inset}
.panel-hdr{background:var(--panel2);padding:8px 14px;font-size:14px;
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
  position:absolute;right:14px;top:62px;z-index:1201;
  width:min(320px,45vw);max-height:48vh;overflow:auto;
  border:1px solid var(--border);border-radius:4px;
  background:color-mix(in srgb, var(--panel) 94%, transparent);backdrop-filter:blur(6px);
  padding:8px;
  box-shadow:0 8px 18px rgba(0,0,0,.14);
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
  border:1px solid var(--border);background:var(--panel2);color:var(--txt);
  padding:5px 9px;border-radius:4px;font:600 13px/1 var(--font-ui);cursor:pointer;
  letter-spacing:0;
  transition:background-color .14s ease,border-color .14s ease,box-shadow .14s ease,color .14s ease,transform .14s ease;
  box-shadow:0 1px 2px rgba(0,0,0,.06);
}
.btn-mini:hover{background:color-mix(in srgb, var(--blue) 10%, var(--panel2));border-color:var(--blue);box-shadow:0 2px 8px var(--glow);transform:translateY(-1px)}
.btn-mini:disabled{opacity:.55;cursor:wait}
.btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:color-mix(in srgb, var(--warn) 74%, white)}
.btn-mini.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--panel2))}
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
  display:inline-block;padding:1px 6px;border-radius:999px;font-size:11px;
  border:1px solid color-mix(in srgb, var(--yellow) 38%, var(--border));background:color-mix(in srgb, var(--yellow) 12%, var(--panel2));color:#ffd85f;line-height:1.3;flex:0 0 auto;
}
.sn-badge.firmware-new{border-color:rgba(46,204,113,.55);background:rgba(46,204,113,.14);color:#98f5be}
.sn-badge.firmware-old{border-color:color-mix(in srgb, var(--blue) 34%, var(--border));background:color-mix(in srgb, var(--blue) 9%, var(--panel2));color:#9fd0ff}
.sn-badge.alarm{border-color:rgba(255,79,79,.72);background:rgba(255,79,79,.16);color:#ffb3ae}
.icon-btn{
  border:1px solid var(--border);background:var(--panel2);color:var(--dim);
  width:24px;height:24px;display:inline-flex;align-items:center;justify-content:center;
  border-radius:4px;cursor:pointer;font-size:12px;line-height:1;flex:0 0 auto;
  transition:background-color .14s ease,border-color .14s ease,color .14s ease,transform .14s ease,box-shadow .14s ease;
  box-shadow:0 1px 2px rgba(0,0,0,.05);
}
.icon-btn:hover{background:color-mix(in srgb, var(--blue) 10%, var(--panel2));color:var(--txt);border-color:var(--blue);transform:translateY(-1px)}
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
  border:1px solid color-mix(in srgb, var(--border) 82%, transparent);border-radius:18px;overflow:hidden;
  background:color-mix(in srgb, var(--panel) 94%, rgba(255,255,255,.08));
  backdrop-filter:blur(16px);
  box-shadow:0 20px 48px rgba(0,0,0,.24);
  display:flex;flex-direction:column;
  pointer-events:auto;
}
.info-card-hd{
  display:flex;align-items:center;justify-content:space-between;gap:8px;
  padding:12px 14px;border-bottom:1px solid color-mix(in srgb, var(--border) 80%, transparent);color:var(--txt);font-weight:700;
}
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
body.theme-light .sn-badge{border-color:color-mix(in srgb, var(--yellow) 35%, var(--border));background:color-mix(in srgb, var(--yellow) 12%, var(--panel2));color:#7b5b00}
body.theme-light .sn-badge.firmware-new{border-color:rgba(21,128,61,.38);background:rgba(21,128,61,.09);color:#166534}
body.theme-light .sn-badge.firmware-old{border-color:color-mix(in srgb, var(--blue) 30%, var(--border));background:color-mix(in srgb, var(--blue) 8%, var(--panel2));color:#1f4e79}
body.theme-light .sn-badge.alarm{border-color:rgba(209,52,56,.55);background:rgba(209,52,56,.10);color:#a4262c}
body.theme-light tbody td.hl{
  background-color:rgba(250,213,97,calc(var(--hl-alpha,.0) * .52));
}
body.theme-light tbody tr.selected{background:color-mix(in srgb, var(--blue) 10%, var(--panel))}
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
body.theme-light .banner{border-color:var(--border);background:rgba(255,255,255,.97);color:var(--txt)}
body.theme-light .banner.ok{border-color:color-mix(in srgb, var(--green) 38%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel));color:#14532d}
body.theme-light .banner.warn{border-color:color-mix(in srgb, var(--yellow) 34%, var(--border));background:color-mix(in srgb, var(--yellow) 12%, var(--panel));color:#7c2d12}
 
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
  <th><div class="sel-wrap"><input id="sel-all" class="sel-sn" type="checkbox" title="全选"></div></th><th>#</th><th>SN</th><th>机型</th><th>信号</th><th>包</th><th>方向</th><th>数据更新</th><th>末次发现</th><th>UAS ID</th>
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
var infoCardEscBound = false;
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
var replayState = {sn:null,min:null,max:null,start:null,end:null,cursor:null,playing:false,speed:1,timer:null,userRange:false};
var replayMarkers = {};
var replayUiSig = '';
var REPLAY_GAP_SKIP_SEC = 10;
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
  var ts = Number(historyTrackFilterTs);
  return (isFinite(ts) && ts > 0) ? ts : null;
}
function filterTrackByHistoryTime(track){
  var arr = Array.isArray(track) ? track.slice() : [];
  if(currentAppPage() !== 'history') return arr;
  var start = activeHistoryTrackFilterTs();
  if(start == null) return arr;
  return arr.filter(function(p){
    var ts = _trackTsSec(p);
    return ts == null ? true : (ts >= start);
  });
}
function filterTrackForDisplay(track, page, sn){
  if(page !== 'history') return [];
  var arr = Array.isArray(track) ? track.slice() : [];
  arr = filterTrackByHistoryTime(arr);
  arr = filterTrackByReplay(arr, sn);
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
  html += infoRowHtml('飞手纬度', fmt(e.pilot_lat,6,''));
  html += infoRowHtml('飞手经度', fmt(e.pilot_lon,6,''));
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
      updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
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
  if(!opts.keepReplay && replayState.sn) clearReplaySelection({render:false});
  syncTableSelectionUi();
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
  node.textContent = String(text || '');
  host.appendChild(node);
  setTimeout(function(){ node.classList.add('show'); }, 10);
  var ttl = Math.max(1200, Number(timeoutMs || 3200));
  setTimeout(function(){
    node.classList.remove('show');
    setTimeout(function(){ if(node.parentNode) node.parentNode.removeChild(node); }, 280);
  }, ttl);
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
function handleDroneNotifications(list){
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
        if(e) showInfoCard(buildInfoHtml(e), true);
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
    var pilot = (e.pilot_lat == null || e.pilot_lon == null) ? 'N/A' : (fmt(e.pilot_lat,6,'') + ', ' + fmt(e.pilot_lon,6,''));
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
      +   '<div class="live-card-item"><div class="k">飞手坐标</div><div class="v">'+esc(pilot)+'</div></div>'
      +   '<div class="live-card-item"><div class="k">信号 / 更新</div><div class="v">'+esc(rssi + ' / ' + String(e.age_text || fmtAge(e.age)))+'</div></div>'
      + '</div>'
      + '<div class="live-card-foot"><span>最后数据包 '+esc(String(e.last_pkt_time || e.capture_time || '-'))+'</span><span>#'+(idx+1)+'</span></div>'
      + '</article>';
  });
  box.innerHTML = html;
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

  var rows='';
  var page = currentAppPage();
  if(!list.length){
    rows='<tr><td colspan="10" class="empty">暂无数据</td></tr>';
  } else {
    list.forEach(function(e, idx){
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
  syncTableSelectionUi();
  renderLiveCards(list);
  renderMapMiniList(list);
  refreshTrackMgrOptions(list);
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
consumeFreezeOnHomeRequest();
applyTheme(loadThemePref());
buildExtraUi();
connect();

var map = null, markers = {}, pilotMarkers = {}, trackLines = {}, trackLineSig = {}, twsLines = {}, baseMarker = null;
var motionState = {};
var COLORS = ['#58a6ff','#3fb950','#d29922','#d2a8ff','#79c0ff','#ff7b72'];
var TRACK_COLORS = ['#1f9dff','#12b886','#ff8f1f','#ff4d6d','#8b5cf6','#06b6d4','#84cc16','#eab308'];
var colorIdx = {};
var LIVE_RECENT_WINDOW_SEC = 300;
window.addEventListener('resize', function(){
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
function focusEntryOnMap(e, zoom){
  if(!map || !e) return;
  var lat = Number(e.lat), lon = Number(e.lon);
  if(!isFinite(lat) || !isFinite(lon)) return;
  var pos = toMapLatLng(lat, lon);
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
    showInfoCard(buildInfoHtml(e), true);
    focusEntryOnMap(e, 16);
  }
}
function focusHistoryAircraft(sn){
  sn = String(sn || '');
  if(!sn) return;
  setHistoryVisibleSet([sn], {keepReplay:false});
  var e = latestDroneMap[sn];
  if(e){
    showInfoCard(buildInfoHtml(e), true);
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
  if(replayState.sn) clearReplaySelection({render:false});
  historyTrackFilterTs = nextTs;
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function resetHistoryTrackFilter(){
  if(replayState.sn) clearReplaySelection({render:false});
  historyTrackFilterTs = null;
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function replaySliderToTs(val){
  if(replayState.min == null || replayState.max == null) return null;
  var span = Number(replayState.max) - Number(replayState.min);
  if(!isFinite(span) || span <= 0) return Number(replayState.min);
  var v = Math.max(0, Math.min(1000, Number(val || 0)));
  return Number(replayState.min) + span * (v / 1000);
}
function replayTsToSlider(ts){
  if(replayState.min == null || replayState.max == null) return 0;
  var span = Number(replayState.max) - Number(replayState.min);
  if(!isFinite(span) || span <= 0) return 0;
  var v = (Number(ts) - Number(replayState.min)) / span;
  return Math.max(0, Math.min(1000, Math.round(v * 1000)));
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
    '<div class="track-replay-head"><div><div class="track-replay-title">轨迹时间线</div><div id="track-replay-count" class="track-replay-sub">-</div></div><button class="btn-mini" id="btn-replay-play" type="button">播放</button></div>'+
    '<div class="track-replay-time" id="track-history-filter-time">-</div>'+
    '<div class="track-replay-ranges">'+
    '  <input id="history-filter-progress" type="range" min="0" max="1000" step="1" value="0" aria-label="轨迹时间线过滤">'+
    '</div>'+
    '<div class="track-replay-controls">'+
    '  <button class="btn-mini" id="btn-history-filter-reset" type="button">显示全部</button>'+
    '</div>'+
    '<select id="replay-sn-select" class="input-mini" aria-label="选择重放目标"><option value="">选择飞机</option></select>'+
    '<div class="track-replay-time" id="track-replay-time">-</div>'+
    '<div class="track-replay-ranges">'+
      '  <input id="replay-progress" type="range" min="0" max="1000" step="1" value="0" aria-label="重放进度">'+
    '</div>'+
    '<div class="track-replay-controls">'+
    '  <button class="btn-mini" id="btn-replay-reset" type="button">重放起点</button>'+
    '  <label class="track-speed-label"><span>速度</span><input id="replay-speed" type="range" min="1" max="10" step="0.1" value="1" aria-label="重放速度"><span id="replay-speed-value" class="track-speed-value">1.0x</span></label>'+
    '  <button class="btn-mini" id="btn-replay-100x" type="button">100x</button>'+
    '</div>'+
    '<div class="track-replay-status" id="track-replay-status">勾选飞机只影响地图显示。需要回放时，请在下方手动选择一架飞机。</div>';
  panel.appendChild(card);
  var historyFilter = qs('history-filter-progress');
  if(historyFilter) historyFilter.addEventListener('input', onHistoryTrackFilterInput);
  var historyReset = qs('btn-history-filter-reset');
  if(historyReset) historyReset.addEventListener('click', resetHistoryTrackFilter);
  var progress = qs('replay-progress');
  if(progress) progress.addEventListener('input', onReplayRangeInput);
  var play = qs('btn-replay-play');
  if(play) play.addEventListener('click', function(){ setReplayPlaying(!replayState.playing); });
  var sel = qs('replay-sn-select');
  if(sel) sel.addEventListener('change', function(){
    var sn = String(sel.value || '').trim();
    if(!sn){
      clearReplaySelection();
      updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
      return;
    }
    replayState.sn = sn;
    setHistoryExclusiveVisible(sn, {keepReplay:true});
  });
  var reset = qs('btn-replay-reset');
  if(reset) reset.addEventListener('click', resetReplayRange);
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
  var candidates = replayCandidateList();
  var sn = replaySelectedSn();
  syncReplaySelect(candidates, sn);
  var visibleCount = historyVisibleSnList(latestDroneRows).length;
  if(!sn){
    return {sn:null, min:null, max:null, visibleCount:visibleCount, candidateCount:candidates.length, count:0};
  }
  replayState.sn = sn;
  var minTs = null;
  var maxTs = null;
  var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
  for(var i=0;i<tr.length;i++){
    var ts = _trackTsSec(tr[i]);
    if(ts == null) continue;
    if(minTs == null || ts < minTs) minTs = ts;
    if(maxTs == null || ts > maxTs) maxTs = ts;
  }
  return {sn:sn, min:minTs, max:maxTs, visibleCount:visibleCount, candidateCount:candidates.length, count:tr.length};
}
function clearReplaySelection(opts){
  opts = (opts && typeof opts === 'object') ? opts : {};
  stopReplayTimer();
  setReplaySyncPaused(false);
  replayState.sn = null;
  replayState.min = null;
  replayState.max = null;
  replayState.start = null;
  replayState.end = null;
  replayState.cursor = null;
  replayState.userRange = false;
  var sel = qs('replay-sn-select');
  if(sel) sel.value = '';
  clearReplayMarkers();
  if(opts.render !== false) renderReplayCard();
}
function refreshReplayBounds(keepRange){
  ensureTrackReplayCard();
  var b = collectReplayBounds();
  var filterStart = activeHistoryTrackFilterTs();
  replayState.sn = b.sn || null;
  if(!b.sn){
    if(replayState.playing) setReplayPlaying(false);
    else {
      stopReplayTimer();
      setReplaySyncPaused(false);
    }
    replayState.min = replayState.max = replayState.start = replayState.end = replayState.cursor = null;
    replayState.userRange = false;
    renderReplayCard();
    clearReplayMarkers();
    return;
  }
  if(b.min == null || b.max == null || b.max <= b.min){
    if(replayState.playing) setReplayPlaying(false);
    else {
      stopReplayTimer();
      setReplaySyncPaused(false);
    }
    replayState.min = replayState.max = replayState.start = replayState.end = replayState.cursor = null;
    replayState.userRange = false;
    renderReplayCard();
    clearReplayMarkers();
    return;
  }
  replayState.min = b.min;
  replayState.max = b.max;
  replayState.start = (filterStart != null && filterStart >= b.min && filterStart <= b.max) ? filterStart : b.min;
  replayState.end = b.max;
  if(!keepRange || replayState.cursor == null || replayState.cursor < replayState.start || replayState.cursor > b.max){
    replayState.cursor = replayState.start;
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
  var activeFilter = activeHistoryTrackFilterTs();
  var candidates = replayCandidateList();
  var selectedSn = replaySelectedSn();
  syncReplaySelect(candidates, selectedSn);
  var countEl = qs('track-replay-count');
  if(countEl){
    if(selectedSn) countEl.textContent = '已勾选 ' + historyBounds.selectedCount + ' 架 · 回放目标 ' + selectedSn;
    else if(historyBounds.selectedCount) countEl.textContent = '已勾选 ' + historyBounds.selectedCount + ' 架 · 回放未开启';
    else countEl.textContent = '默认仅勾选 12 小时内飞机';
  }
  var historyFilterEl = qs('history-filter-progress');
  var hasHistoryRange = historyBounds.min != null && historyBounds.max != null && historyBounds.max > historyBounds.min;
  if(historyFilterEl){
    historyFilterEl.disabled = !hasHistoryRange;
    historyFilterEl.value = String(historyFilterTsToSlider(historyBounds, activeFilter));
  }
  var historyFilterReset = qs('btn-history-filter-reset');
  if(historyFilterReset){
    historyFilterReset.disabled = !hasHistoryRange || (activeFilter == null && !selectedSn);
  }
  var historyTime = qs('track-history-filter-time');
  if(historyTime){
    if(!historyBounds.selectedCount){
      historyTime.textContent = '进入历史记录后默认只勾选 12 小时内飞机。勾选目标后，可拖动时间线仅显示指定时间点后的轨迹。';
    }else if(!hasHistoryRange){
      historyTime.textContent = historyBounds.loadedCount ? '已勾选飞机的轨迹点不足，暂不能按时间线过滤。' : '正在加载已勾选飞机的轨迹...';
    }else if(activeFilter == null){
      historyTime.textContent = '当前显示全部已勾选轨迹\\n范围 ' + fmtReplayTime(historyBounds.min) + '  ~  ' + fmtReplayTime(historyBounds.max);
    }else{
      historyTime.textContent = '当前显示 ' + fmtReplayTime(activeFilter) + ' 之后的轨迹\\n范围 ' + fmtReplayTime(historyBounds.min) + '  ~  ' + fmtReplayTime(historyBounds.max);
    }
  }
  var progressEl = qs('replay-progress');
  var hasRange = replayState.min != null && replayState.max != null && replayState.max > replayState.min;
  if(progressEl) progressEl.disabled = !hasRange;
  if(progressEl && hasRange) progressEl.value = String(replayTsToSlider(replayState.cursor == null ? replayState.start : replayState.cursor));
  var play = qs('btn-replay-play');
  if(play){
    play.disabled = !hasRange || !selectedSn;
    play.textContent = replayState.playing ? '暂停' : '播放';
  }
  var reset = qs('btn-replay-reset');
  if(reset) reset.disabled = !hasRange;
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
    time.textContent = hasRange
      ? ('当前 ' + fmtReplayTime(replayState.cursor == null ? replayState.start : replayState.cursor) + '\\n重放起点 ' + fmtReplayTime(replayState.start) + '  末包 ' + fmtReplayTime(replayState.end))
      : '暂无可重放轨迹';
  }
  var status = qs('track-replay-status');
  if(status){
    var speedText = speedValue ? speedValue.textContent : ((Number(replayState.speed || 1) === 100) ? '100x' : (Number(replayState.speed || 1).toFixed(1) + 'x'));
    if(!selectedSn) status.textContent = candidates.length ? '勾选飞机只影响地图显示。需要回放时，请在下方手动选择一架飞机。' : '当前没有可重放轨迹。';
    else if(!hasRange) status.textContent = '轨迹正在加载或时间点不足。';
    else status.textContent = replayState.playing ? ('正在重演中，新的数据同步已暂停。倍速 ' + speedText + '，超过 ' + REPLAY_GAP_SKIP_SEC + 's 的空白段会自动跳过。') : '已锁定单机回放。拖动上方时间线或点“显示全部”会退出回放。';
  }
  updateReplaySyncUi();
}
function onReplayRangeInput(){
  if(replayState.min == null || replayState.max == null) return;
  var progressEl = qs('replay-progress');
  var curTs = replaySliderToTs(progressEl ? progressEl.value : 0);
  if(curTs == null) return;
  replayState.cursor = Math.max(Number(replayState.start), Math.min(Number(replayState.end), Number(curTs)));
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function resetReplayRange(){
  if(replayState.min == null || replayState.max == null) return;
  var filterStart = activeHistoryTrackFilterTs();
  replayState.start = (filterStart != null && filterStart >= replayState.min && filterStart <= replayState.max)
    ? filterStart
    : replayState.min;
  replayState.end = replayState.max;
  replayState.cursor = replayState.start;
  replayState.userRange = false;
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function nextReplayTrackTsAfter(curTs){
  var sn = String(replayState.sn || '');
  if(!sn) return null;
  var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
  var cur = Number(curTs);
  if(!isFinite(cur)) return null;
  var next = null;
  for(var i=0;i<tr.length;i++){
    var ts = _trackTsSec(tr[i]);
    if(ts == null || ts <= cur + 0.001) continue;
    if(replayState.end != null && ts > Number(replayState.end)) continue;
    if(next == null || ts < next) next = ts;
  }
  return next;
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
  if(txt) txt.textContent = replayState.sn ? ('轨迹重演中，同步已暂停：' + replayState.sn) : '轨迹重演中，同步已暂停';
  if(qs('ws-status')){
    if(replaySyncPaused) qs('ws-status').textContent = '重演中';
    else if(ws && ws.readyState === WebSocket.OPEN) qs('ws-status').textContent = '实时';
  }
}
function setReplaySyncPaused(paused){
  var next = !!paused;
  if(replaySyncPaused === next){
    updateReplaySyncUi();
    return;
  }
  replaySyncPaused = next;
  updateReplaySyncUi();
  if(!replaySyncPaused && !uiFrozen && frozenPendingData){
    var d = frozenPendingData;
    frozenPendingData = null;
    onData(d);
  }
}
function setReplayPlaying(on){
  if(!on){
    stopReplayTimer();
    setReplaySyncPaused(false);
    renderReplayCard();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    return;
  }
  var b = collectReplayBounds();
  if(!b.sn){
    showBanner('请先在轨迹重放卡片中选择一架飞机。', 'warn', 3200);
    renderReplayCard();
    return;
  }
  if(b.min == null || b.max == null || b.max <= b.min){
    showBanner('该飞机轨迹点不足，暂不能重演。', 'warn', 3200);
    renderReplayCard();
    return;
  }
  replayState.sn = b.sn;
  replayState.min = b.min;
  replayState.max = b.max;
  var filterStart = activeHistoryTrackFilterTs();
  replayState.start = (filterStart != null && filterStart >= b.min && filterStart <= b.max) ? filterStart : b.min;
  replayState.end = b.max;
  replayState.cursor = replayState.start;
  if(replayState.start == null || replayState.end == null || replayState.end <= replayState.start) return;
  replayState.playing = true;
  setReplaySyncPaused(true);
  if(replayState.timer) clearInterval(replayState.timer);
  replayState.timer = setInterval(function(){
    var step = 0.25 * Math.max(1, Number(replayState.speed || 1));
    var cur = Number(replayState.cursor || replayState.start);
    var nextCursor = cur + step;
    var nextPointTs = nextReplayTrackTsAfter(cur);
    if(nextPointTs != null && (nextPointTs - cur) > REPLAY_GAP_SKIP_SEC && nextCursor < nextPointTs){
      nextCursor = nextPointTs;
    }
    replayState.cursor = Math.min(Number(replayState.end), nextCursor);
    if(replayState.cursor >= replayState.end){
      stopReplayTimer();
      setReplaySyncPaused(false);
      showBanner('轨迹重演已结束，数据同步已恢复。', 'ok', 2600);
    }
    renderReplayCard();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  }, 250);
  showBanner('轨迹重演开始，新的数据同步已暂停。', 'warn', 3600);
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function replayWindowEnd(){
  if(replayState.playing && replayState.cursor != null) return replayState.cursor;
  return replayState.end;
}
function filterTrackByReplay(track, sn){
  var arr = Array.isArray(track) ? track.slice() : [];
  if(currentAppPage() !== 'history') return arr;
  var targetSn = String(replayState.sn || '');
  if(!targetSn || String(sn || '') !== targetSn) return arr;
  if(replayState.start == null || replayState.end == null) return arr;
  var start = Number(replayState.start);
  var end = Number(replayWindowEnd());
  if(!isFinite(start) || !isFinite(end) || end < start) return arr;
  return arr.filter(function(p){
    var ts = _trackTsSec(p);
    return ts == null ? true : (ts >= start && ts <= end);
  });
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
  var replaySn = String(replayState.sn || '');
  if(currentAppPage() !== 'history' || !replaySn || replayState.start == null || replayWindowEnd() == null){
    clearReplayMarkers();
    return;
  }
  var active = {};
  var end = Number(replayWindowEnd());
  var start = Number(replayState.start);
  var tr = Array.isArray(trackCache[replaySn]) ? trackCache[replaySn] : [];
  var point = null;
  var prevPoint = null;
  for(var i=0;i<tr.length;i++){
    var p = tr[i] || {};
    var ts = _trackTsSec(p);
    if(ts == null || ts < start || ts > end) continue;
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
      var icon = droneIcon(col, false, heading, true, 1, false);
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

function updateMap(drones){
  if(!map) return;
  applyBaseMarker(false);
  var autoState = mapAutoState();
  var page = currentAppPage();
  var rows = Array.isArray(drones) ? drones : [];
  var selected = (page === 'history') ? historyVisibleSnList(rows) : selectedSnList();
  var selectedSet = {};
  selected.forEach(function(sn){ selectedSet[sn] = true; });
  var recentRows = liveRecentRows(rows);
  var trackSn = displayTrackSnList(page, rows);
  var liveAir = (page === 'live' ? recentRows : rows).filter(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return false;
    if(page === 'history' && !selectedSet[sn]) return false;
    if(e.lat==null || e.lon==null) return false;
    return true;
  });
  var livePilot = (page === 'live' ? recentRows : rows).filter(function(e){
    var sn = String((e && e.sn) || '');
    if(!sn) return false;
    if(page === 'history' && !selectedSet[sn]) return false;
    if(e.pilot_lat==null || e.pilot_lon==null) return false;
    return true;
  });
  var mapHintTxt = '';
  if(page === 'live'){
    mapHintTxt = '实时目标:' + recentRows.length + '  飞机:' + liveAir.length + '  飞手:' + livePilot.length + '  离线:2分钟';
  }else{
    mapHintTxt = '显示飞机:' + liveAir.length + '  已选:' + selected.length + '  轨迹:' + trackSn.length + '  飞手:' + livePilot.length;
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
    activeAir[sn] = true;
    var col = colorIdx[sn];
    var isSel = !!selectedSet[sn];
    var inAlarmZone = !!zoneAlarmSnSet[sn];
    var latRaw = Number(e.lat), lonRaw = Number(e.lon);
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
      +(e.lat!=null?e.lat.toFixed(5):'-')+', '+(e.lon!=null?e.lon.toFixed(5):'-')
      +'<br>高度: '+(e.alt!=null?e.alt.toFixed(1)+'m':'N/A')
      +'<br>速度: '+(e.spd!=null?e.spd.toFixed(1)+'m/s':'N/A')
      +'<br>信号: '+(e.rssi!=null?e.rssi+'dBm':'N/A')
      +'<br>航向: '+(isFinite(Number(heading))?Number(heading).toFixed(1)+'°':'N/A')
      +'<br>航向差: '+(isFinite(Number(headingDelta))?((headingDelta>=0?'+':'')+Number(headingDelta).toFixed(1)+'°'):'N/A')
      +'<br>数据更新: '+esc(String(e.age_text || fmtAge(e.age)));

    var airPos = toMapLatLng(latRaw, lonRaw);
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
  livePilot.forEach(function(e){
    var sn = String(e.sn || '');
    if(!sn) return;
    activePilot[sn] = true;
    var col = colorIdx[sn] || '#ffb84d';
    var ptxt = String(e.pilot_loc_type_text || e.pilot_loc_type || 'unknown');
    var pilotPos = toMapLatLng(e.pilot_lat, e.pilot_lon);
    var popup = '<b>'+sn+'</b><br>飞手位置<br>'
      +(e.pilot_lat!=null?e.pilot_lat.toFixed(5):'-')+', '+(e.pilot_lon!=null?e.pilot_lon.toFixed(5):'-')
      +'<br>类型: '+esc(ptxt);
    if(pilotMarkers[sn]){
      pilotMarkers[sn].setLatLng(pilotPos)
        .setIcon(pilotIcon(col, e.lost))
        .setPopupContent(popup);
    }else{
      pilotMarkers[sn] = L.marker(pilotPos, {icon: pilotIcon(col, e.lost)})
        .addTo(map).bindPopup(popup);
      (function(snLocal){
        pilotMarkers[snLocal].on('click', function(){
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
      if(isFinite(lat) && isFinite(lon)){
        var ll = toMapLatLng(lat, lon);
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
    if(page === 'history' && trackLatLngsAll.length && autoState.allow && (!map._rid_fitted || !!map._rid_user_moved)){
      if(trackLatLngsAll.length === 1) map.setView(trackLatLngsAll[0], 15);
      else map.fitBounds(L.latLngBounds(trackLatLngsAll).pad(0.14));
      map._rid_fitted = true;
      map._rid_user_moved = false;
      document.getElementById('map-hint').textContent = '历史轨迹 ' + trackSn.length + ' 架';
      return;
    }
    if(b.ok){
      if(autoState.allow && (!map._rid_base_fitted || !!map._rid_user_moved)){
        map.setView([b.lat, b.lon], b.zoom);
        map._rid_base_fitted = true;
        map._rid_user_moved = false;
      }
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

  // first-time fit bounds for visible aircraft only
  var latlngs = liveAir.map(function(e){ return toMapLatLng(e.lat, e.lon); }).concat(page === 'history' ? trackLatLngsAll : []);
  if(latlngs.length && autoState.allow && (!map._rid_fitted || !!map._rid_user_moved)){
    if(latlngs.length === 1) map.setView(latlngs[0], 14);
    else map.fitBounds(L.latLngBounds(latlngs).pad(0.3));
    map._rid_fitted = true;
    map._rid_user_moved = false;
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
  --muted:#c8c6c4;--blue:#2899f5;--green:#92c353;--warn:#f7630c;--glow:rgba(40,153,245,.12);--soft:rgba(255,255,255,.03);--app-vh:100dvh
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
.btn{border:1px solid var(--border);background:var(--card2);color:var(--txt);padding:10px 14px;border-radius:4px;cursor:pointer;font:600 14px/1 var(--font-ui);letter-spacing:0;transition:border-color .14s ease,background-color .14s ease,color .14s ease,transform .14s ease,box-shadow .14s ease;box-shadow:0 1px 2px rgba(0,0,0,.06)}
.btn:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--card2));box-shadow:0 2px 8px var(--glow)}
.btn.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:var(--warn)}
.btn.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--card2))}
.layout{display:grid;grid-template-columns:minmax(320px,.92fr) minmax(400px,1.08fr);gap:14px}
.stack{display:grid;gap:14px}
.card{border:1px solid var(--border);border-radius:4px;background:var(--card);padding:16px;box-shadow:0 1px 3px rgba(0,0,0,.08);animation:officeFade .16s ease-out both}
.card h2{margin:0 0 12px;font:600 18px/1 var(--font-ui);letter-spacing:.01em}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.field{display:grid;gap:6px}
.field label{font:600 12px/1 var(--font-ui);letter-spacing:.01em;color:var(--muted);text-transform:none}
select,input{width:100%;background:var(--card2);color:var(--txt);border:1px solid var(--border);border-radius:4px;padding:10px 12px;font:600 14px/1.35 var(--font-ui);transition:border-color .14s ease,box-shadow .14s ease,background-color .14s ease}
select:focus,input:focus{outline:none;border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 38%, transparent)}
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
  border-radius:4px;
  box-shadow:0 1px 3px rgba(0,0,0,.08);
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
  border:1px solid var(--border);background:var(--panel2);border-radius:4px;
  box-shadow:0 1px 2px rgba(0,0,0,.05)
}
.main-more-menu{position:relative;display:inline-flex}
.main-more-pop{position:absolute;right:0;top:calc(100% + 8px);display:none;min-width:150px;padding:6px;border:1px solid var(--border);border-radius:4px;background:var(--panel);box-shadow:0 14px 28px rgba(0,0,0,.22);z-index:45}
.main-more-menu.open .main-more-pop{display:grid;gap:6px}
.main-more-pop .header-link-btn{width:100%;text-align:left;box-shadow:none}
.app-tab-btn,.header-link-btn,.btn-mini,.icon-btn,.info-card-close{
  border:1px solid var(--border);
  background:var(--panel2);
  color:var(--txt);
  border-radius:4px;
  font:600 14px/1 var(--font-ui);
  letter-spacing:0;
  cursor:pointer;
  transition:background-color .14s ease,border-color .14s ease,color .14s ease,transform .14s ease,box-shadow .14s ease;
  box-shadow:0 1px 2px rgba(0,0,0,.05);
}
.app-tab-btn,.header-link-btn,.btn-mini{
  padding:8px 11px;
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
  box-shadow:0 2px 8px var(--glow);
}
.app-tab-btn.active{
  border-color:var(--blue);
  background:color-mix(in srgb, var(--blue) 14%, var(--panel2));
  color:var(--txt);
  box-shadow:inset 0 0 0 1px color-mix(in srgb, var(--blue) 26%, transparent)
}
.btn-mini.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:color-mix(in srgb, var(--warn) 74%, white)}
.btn-mini.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--panel2));border-color:var(--warn);box-shadow:0 2px 8px color-mix(in srgb, var(--warn) 16%, transparent)}
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
.live-card-panel{border:1px solid var(--border);background:var(--panel);border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,.08);display:flex;flex-direction:column;min-height:0;overflow:hidden}
.live-card-head{padding:12px 14px;border-bottom:1px solid var(--border);font:600 14px/1 var(--font-ui);color:var(--txt);display:flex;justify-content:space-between;gap:10px}
.live-card-list{padding:10px;display:grid;gap:10px;overflow:auto;min-height:0;align-content:start}
.live-card{border:1px solid var(--border);background:var(--panel2);border-radius:4px;padding:12px;display:grid;gap:10px;cursor:pointer;transition:background-color .14s ease,border-color .14s ease,transform .14s ease,box-shadow .14s ease}
.live-card:hover{transform:translateY(-1px);border-color:var(--blue);box-shadow:0 2px 8px var(--glow)}
.live-card.selected{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--panel2))}
.live-card.lost{opacity:.72}
.live-card.alarm-zone{border-color:rgba(255,79,79,.78);background:color-mix(in srgb, #ff3b30 10%, var(--panel2));animation:alarmRowPulse .9s ease-in-out infinite alternate}
.live-card-top{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:10px;align-items:start}
.live-card-title{font:700 20px/1.12 var(--font-ui);letter-spacing:.01em;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.live-card-actions{display:flex;align-items:center;gap:8px;flex-wrap:wrap;justify-content:flex-end}
.live-card-pick{display:inline-flex;align-items:center;gap:6px;color:var(--dim);font-size:12px}
.live-card-state{display:inline-flex;align-items:center;padding:3px 8px;border:1px solid var(--border);border-radius:999px;font:600 11px/1 var(--font-ui);color:var(--dim)}
.live-card-state.live{color:var(--green);border-color:color-mix(in srgb, var(--green) 40%, var(--border));background:color-mix(in srgb, var(--green) 10%, var(--panel2))}
.live-card-state.lost{color:var(--warn);border-color:color-mix(in srgb, var(--warn) 38%, var(--border));background:color-mix(in srgb, var(--warn) 8%, var(--panel2))}
.live-card-state.firmware{color:#9fd0ff;border-color:color-mix(in srgb, var(--blue) 34%, var(--border));background:color-mix(in srgb, var(--blue) 9%, var(--panel2))}
.live-card-state.alarm{color:#ffb3ae;border-color:rgba(255,79,79,.68);background:rgba(255,79,79,.14)}
.live-card-snrow{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:8px;align-items:center}
.live-card-snrow .label{font-size:11px;color:var(--dim);letter-spacing:.04em;text-transform:uppercase}
.live-card-sntext{font:700 13px/1.25 var(--font-mono);min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.live-card-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:8px}
.live-card-item{border:1px solid color-mix(in srgb, var(--border) 84%, transparent);border-radius:4px;padding:8px 9px;background:color-mix(in srgb, var(--panel) 74%, var(--panel2))}
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
  right:14px;
  top:62px;
  bottom:14px;
  z-index:1200;
  width:clamp(260px,25%,360px);
  border:1px solid var(--border);
  border-radius:4px;
  background:color-mix(in srgb, var(--panel) 94%, transparent);
  backdrop-filter:blur(8px);
  box-shadow:0 12px 24px rgba(0,0,0,.18);
  padding:12px;
  overflow:auto;
}
#map-panel.history-mounted .track-replay-card{display:block}
.track-replay-head{display:flex;justify-content:space-between;align-items:flex-start;gap:10px;margin-bottom:10px}
.track-replay-title{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.track-replay-sub,.track-replay-status{margin-top:5px;color:var(--dim);font-size:12px;line-height:1.45}
.track-replay-card .input-mini{width:100%;height:34px;border:1px solid var(--border);background:var(--panel2);color:var(--txt);border-radius:4px;padding:6px 8px;font:600 13px/1.2 var(--font-ui);margin-bottom:10px}
.track-replay-time{border:1px solid var(--border);border-radius:4px;background:var(--panel2);padding:8px 10px;font-size:12px;line-height:1.45;color:var(--txt);margin-bottom:10px;white-space:pre-line}
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
.app-page .panel{border-radius:4px;box-shadow:0 1px 3px rgba(0,0,0,.08);animation:officeFade .16s ease-out both}
.app-page .panel-hdr{font-size:13px;letter-spacing:.01em}
.tbl-wrap,.app-page .panel,.map-mini-list,.banner{
  border-radius:4px;
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
"""

_MAIN_PAGE_PATCH_JS = r"""
(function(){
  var PAGE_COOKIE='rid_home_page';
  var pageReady=false;
  var alarmRects=[];
  var alarmOverlayHideTimer=null;
  var alarmLastSig='';
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
    if(p !== 'history' && replayState.playing) setReplayPlaying(false);
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
      if(latestDroneMap && latestDroneMap[sn]) showInfoCard(buildInfoHtml(latestDroneMap[sn]), true);
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
  }
  function patchInfoCard(){
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
        ['飞手纬度', fmt(e.pilot_lat,6,'')],
        ['飞手经度', fmt(e.pilot_lon,6,'')],
        ['飞手高度', fmt(e.pilot_alt,1,'m')],
        ['飞手位置类型', String(e.pilot_loc_type_text || e.pilot_loc_type || '-')]
      ];
      var actionSn = String(e.sn || '');
      var html = '<div class="info-actions">'+
        '<button class="btn-mini export-track-btn" type="button" data-sn="'+escAttr(actionSn)+'">导出轨迹</button>'+
        '<button class="btn-mini warn delete-history-btn" type="button" data-sn="'+escAttr(actionSn)+'">删除历史</button>'+
        '</div><div class="info-sections">';
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
      showBanner('当前有飞机侵入报警区域：' + lineText, 'warn', 5200, {persist:false});
      if(webNotifyEnabled && window.Notification && Notification.permission === 'granted'){
        try{ new Notification('当前有飞机侵入报警区域', {body:lineText}); }catch(_e){}
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

def _build_html() -> str:
    html_src = _PAGE_HTML
    html_src = html_src.replace("__APP_VERSION_LABEL__", _app_version_label())
    html_src = _inject_html_once(html_src, "</style>", _MAIN_PAGE_PATCH_CSS + "\n")
    html_src = _inject_html_once(html_src, "</body>", "<script>\n" + _MAIN_PAGE_PATCH_JS + "\n</script>\n")
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
            status_message = "当前已启用 PassKey 登录，但尚未登记可用密钥。"
        elif (not password_enabled) and (not has_passkey):
            if sso_available:
                status_message = "当前仅允许通过 SSO URL 登录，请使用已生成的登录链接进入。"
            else:
                status_message = "当前没有可用的网页登录方式，请返回设置检查登录方式配置。"
    status_class = "status err" if status_error else "status"
    status_html = '<div class="' + status_class + '" id="status">' + _html_escape(status_message, quote=False) + "</div>"
    method_labels: list[str] = []
    if password_enabled:
        method_labels.append("账号密码")
    if has_passkey:
        method_labels.append("PassKey")
    elif passkey_enabled:
        method_labels.append("PassKey(待登记)")
    if sso_available:
        method_labels.append("SSO URL(最高优先级)")
    login_method_copy = ("可用方式: " + " / ".join(method_labels)) if method_labels else "当前没有可用的网页登录方式。"
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
  <p class="desc">登录到在线监控平台。{_html_escape(login_method_copy, quote=False)}</p>
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
    <div class="read-state" id="read-state">请阅读 EULA，5 秒后才能勾选同意。</div>
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
    qs('read-state').textContent = '请阅读 EULA，' + Math.ceil(left / 1000) + ' 秒后才能勾选同意。';
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
qs('decline').addEventListener('click', function(){{ setStatus('未同意许可协议，当前不会进入系统。', true); }});
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
    <div><div class="title">日志</div><div class="meta">运行、操作、扫描与扫描差异。</div></div>
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
      </div>
      <div class="actions">
        <input id="limit" type="number" min="20" max="5000" value="500" title="行数">
        <button class="btn" id="btn-refresh" type="button">刷新</button>
        <button class="btn" id="btn-export" type="button">导出当前</button>
        <button class="btn" id="btn-export-all" type="button">导出全部</button>
      </div>
    </div>
    <pre id="log-view">正在加载...</pre>
    <div id="status" class="status">-</div>
  </div>
</div>
<script>
function qs(id){return document.getElementById(id)}
function enc(v){return String(v==null?'':v)}
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
  qs('status').textContent='读取中...';
  var r=await fetch(apiUrl('/api/logs/view?type='+encodeURIComponent(currentType)+'&limit='+limit), {cache:'no-store', headers:pageHeaders()});
  var d=await r.json().catch(function(){return {}});
  if(authExpired(r,d)){redirectLogin();throw new Error('login required')}
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  qs('log-view').textContent=(d.items||[]).join('\\n') || '(empty)';
  qs('status').textContent=String(d.type||currentType)+' · '+String(d.count||0)+' 行';
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

def _build_settings_html() -> str:
    return """<!doctype html><html lang="zh"><head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>设置 - Light RID Scanner</title>
<style>
*{box-sizing:border-box}
:root{
  --font-ui:"Segoe UI Variable Text","Segoe UI","PingFang SC","Microsoft YaHei","Noto Sans SC",sans-serif;
  --font-mono:"Cascadia Mono","Consolas","SFMono-Regular",monospace;
  --bg:#201f1e;--bg2:#252423;--card:#2b2a29;--card2:#252423;--border:#3b3a39;--txt:#f3f2f1;
  --muted:#c8c6c4;--blue:#2899f5;--green:#92c353;--warn:#f7630c;--glow:rgba(40,153,245,.12);--soft:rgba(255,255,255,.03);--app-vh:100dvh
}
body.theme-light{
  --bg:#f3f2f1;--bg2:#edebe9;--card:#ffffff;--card2:#faf9f8;--border:#e1dfdd;--txt:#323130;
  --muted:#605e5c;--blue:#0078d4;--green:#107c10;--warn:#d83b01;--glow:rgba(0,120,212,.10);--soft:rgba(0,0,0,.018)
}
html,body{margin:0;padding:0;background:var(--bg);color:var(--txt);font-family:var(--font-ui)}
body{min-height:var(--app-vh);background:linear-gradient(180deg,var(--bg),var(--bg2) 18%,var(--bg))}
.wrap{width:min(1420px,calc(100vw - 24px));margin:0 auto;padding:clamp(14px,1.8vw,22px) clamp(10px,1.5vw,18px) 30px}
.settings-sticky-head{position:relative;z-index:1;background:linear-gradient(180deg,var(--bg),color-mix(in srgb,var(--bg) 94%,transparent));padding-top:clamp(8px,1.2vw,14px)}
.topbar{display:flex;justify-content:space-between;align-items:center;gap:14px;flex-wrap:wrap;margin-bottom:12px}
.title{font:600 32px/1 var(--font-ui);letter-spacing:.01em}
.sub{color:var(--muted);margin-top:5px;max-width:780px;line-height:1.45}
.actions{display:flex;gap:10px;flex-wrap:wrap}
.btn[disabled]{opacity:.58;cursor:not-allowed;transform:none!important;box-shadow:none!important}
.btn{border:1px solid var(--border);background:var(--card2);color:var(--txt);padding:10px 14px;border-radius:4px;cursor:pointer;font:600 14px/1 var(--font-ui);letter-spacing:0;transition:border-color .14s ease,background-color .14s ease,transform .14s ease,box-shadow .14s ease,color .14s ease;box-shadow:0 1px 2px rgba(0,0,0,.06)}
.btn:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 10%, var(--card2));box-shadow:0 2px 8px var(--glow)}
.btn.warn{border-color:color-mix(in srgb, var(--warn) 45%, var(--border));color:color-mix(in srgb, var(--warn) 70%, white)}
.btn.warn:hover{background:color-mix(in srgb, var(--warn) 8%, var(--card2))}
.btn.ghost{background:transparent}
.draft-bar{display:flex;justify-content:space-between;align-items:center;gap:12px;flex-wrap:wrap;margin:0 auto 12px;padding:10px 12px;border:1px solid var(--border);border-radius:4px;background:var(--card);box-shadow:0 1px 3px rgba(0,0,0,.08)}
.draft-copy{display:grid;gap:4px}
.draft-title{font:600 15px/1.2 var(--font-ui)}
.draft-meta{font-size:12px;color:var(--muted);line-height:1.5}
.draft-actions{display:flex;gap:10px;flex-wrap:wrap}
.tabs{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:3px;padding:3px;border:1px solid var(--border);background:var(--card2);border-radius:4px;margin:0 auto 12px;width:min(680px,100%);box-shadow:0 1px 2px rgba(0,0,0,.05)}
.tab{border:1px solid transparent;background:transparent;color:var(--txt);padding:11px 16px;border-radius:4px;cursor:pointer;font:600 14px/1 var(--font-ui);letter-spacing:0;text-align:center;transition:border-color .14s ease,background-color .14s ease,transform .14s ease,box-shadow .14s ease}
.tab:hover{transform:translateY(-1px);border-color:var(--blue);background:color-mix(in srgb, var(--blue) 8%, var(--card2));box-shadow:0 2px 8px var(--glow)}
.tab.active{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 12%, var(--card2));box-shadow:inset 0 0 0 1px color-mix(in srgb, var(--blue) 18%, transparent)}
body.theme-light .tabs{background:var(--card2)}
body.theme-light .tab.active{background:color-mix(in srgb, var(--blue) 12%, var(--card2));border-color:var(--blue)}
.settings-jump{display:flex;gap:8px;overflow-x:auto;padding:0 2px 12px;margin:0 auto;max-width:980px;scrollbar-width:thin}
.settings-jump{justify-content:center}
.settings-jump .btn{flex:0 0 auto;padding:8px 11px}
.panel{display:none}.panel.active{display:block}
.raw-layout{display:grid;grid-template-columns:minmax(260px,.82fr) minmax(0,1.18fr);gap:12px;min-width:0}
.raw-pane{min-width:0;display:grid;gap:10px;align-content:start}
.raw-tree{border:1px solid var(--border);background:var(--card2);border-radius:4px;min-height:460px;max-height:min(72dvh,840px);overflow:auto;padding:10px}
.raw-tree .empty-state{margin:0}
.raw-tree details{margin:0 0 4px 0;padding-left:0}
.raw-tree summary{cursor:pointer;list-style:none;display:flex;align-items:center;gap:6px;padding:6px 8px;border-radius:4px}
.raw-tree summary::-webkit-details-marker{display:none}
.raw-tree summary:hover{background:color-mix(in srgb, var(--blue) 10%, var(--card2))}
.raw-tree .raw-file-btn{display:flex;align-items:center;justify-content:space-between;width:100%;border:1px solid transparent;background:transparent;color:var(--txt);padding:6px 8px;border-radius:4px;cursor:pointer;font:600 13px/1.3 var(--font-ui);text-align:left}
.raw-tree .raw-file-btn:hover{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 8%, var(--card2))}
.raw-tree .raw-file-btn.active{border-color:var(--blue);background:color-mix(in srgb, var(--blue) 14%, var(--card2))}
.raw-tree .raw-dir-child{padding-left:14px;border-left:1px solid var(--border);margin:2px 0 6px 10px}
.raw-main{display:grid;gap:10px;min-width:0}
.raw-meta{display:flex;justify-content:space-between;gap:10px;flex-wrap:wrap;align-items:flex-start;padding:10px 12px;border:1px solid var(--border);border-radius:4px;background:var(--card2)}
.raw-meta .meta-copy{display:grid;gap:4px;min-width:0}
.raw-meta .meta-title{font:600 15px/1.2 var(--font-ui)}
.raw-meta .meta-sub{font-size:12px;color:var(--muted);line-height:1.5;word-break:break-word}
.raw-editor{min-height:54dvh;height:calc(100dvh - 390px);max-height:min(78dvh,920px)}
.raw-lock{padding:14px;border:1px dashed var(--border);border-radius:4px;background:color-mix(in srgb, var(--warn) 6%, var(--card2));display:grid;gap:10px}
.raw-lock strong{font-size:15px}
.raw-toolbar{display:flex;gap:10px;flex-wrap:wrap;justify-content:space-between;align-items:center}
.raw-toolbar .row-actions{justify-content:flex-end}
.passkey-list{display:grid;gap:8px}
.passkey-row{display:flex;align-items:center;justify-content:space-between;gap:10px;padding:10px 12px;border:1px solid var(--border);border-radius:4px;background:var(--card2)}
.passkey-meta{display:grid;gap:4px;min-width:0}
.passkey-title{font:600 14px/1.2 var(--font-ui)}
.passkey-sub{font-size:12px;color:var(--muted);line-height:1.4;word-break:break-word}
.passkey-badges{display:flex;gap:6px;flex-wrap:wrap}
.passkey-badge{font-size:11px;line-height:1;padding:4px 7px;border:1px solid var(--border);border-radius:999px;background:var(--card)}
.visual-grid{display:grid;grid-template-columns:minmax(0,1.12fr) minmax(360px,.88fr);gap:12px}
.stack{display:grid;gap:12px;min-width:0;align-content:start}
.stack-label{font:700 12px/1 var(--font-ui);letter-spacing:0;color:var(--muted);padding:2px 2px 0}
.card{border:1px solid var(--border);border-radius:4px;background:var(--card);padding:14px;box-shadow:0 1px 3px rgba(0,0,0,.08);min-width:0;overflow:hidden;animation:officeFade .16s ease-out both}
.card.dirty{border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 22%, transparent),0 8px 18px var(--glow)}
.card.dirty h2{color:var(--blue)}
.card h2{margin:0;font:600 18px/1 var(--font-ui);letter-spacing:.01em}
.card.settings-collapsible>.section-head{cursor:pointer;user-select:none}
.card.settings-collapsible>.section-head::after{content:'收起';font:700 12px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:5px 7px;background:var(--card)}
.card.settings-collapsible.collapsed>.section-head::after{content:'展开'}
.card.settings-collapsible.collapsed>:not(.section-head){display:none}
.hint{color:var(--muted);font-size:13px;line-height:1.6}
.section-head{display:flex;justify-content:space-between;align-items:flex-start;gap:12px;flex-wrap:wrap}
.section-copy{margin-top:4px;color:var(--muted);font-size:13px;line-height:1.45;max-width:58ch}
.grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.field{display:grid;gap:6px}
.field.full{grid-column:1/-1}
.field label{font:600 12px/1.15 var(--font-ui);letter-spacing:.01em;color:var(--muted)}
.field input,.field select,.field textarea{width:100%;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:10px 12px;font:600 14px/1.35 var(--font-ui);transition:border-color .14s ease,box-shadow .14s ease,background-color .14s ease}
.field input[type="checkbox"],input[type="checkbox"]{width:16px;height:16px;min-width:16px;flex:0 0 auto;padding:0;margin:0;accent-color:var(--blue)}
.field input:not([type="checkbox"]),.field select,.token-actions input{height:42px}
.field-inline .btn,.token-actions .btn{height:42px}
.field input:focus,.field select:focus,.field textarea:focus{outline:none;border-color:var(--blue);box-shadow:0 0 0 1px color-mix(in srgb, var(--blue) 38%, transparent)}
.field textarea{min-height:440px;resize:vertical;font-family:var(--font-mono);font-size:13px}
.field-inline{display:grid;grid-template-columns:minmax(0,1fr) auto auto;gap:8px;align-items:center}
.field-inline input[disabled]{opacity:.9;background:color-mix(in srgb, var(--card2) 92%, black)}
.checks{display:flex;flex-wrap:wrap;gap:12px}
.checks label{display:flex;align-items:center;gap:8px;font-size:15px;color:var(--txt)}
.checks.pref-checks{display:grid;grid-template-columns:1fr;gap:10px}
.row-actions{display:flex;gap:10px;flex-wrap:wrap}
.token-actions{display:flex;gap:10px;flex-wrap:wrap;align-items:center;min-width:0}
.token-actions input{flex:1 1 260px;min-width:0}
.sso-link-list{margin-top:10px}
.sso-link-options{display:grid;grid-template-columns:minmax(120px,.8fr) minmax(110px,.7fr) auto;gap:10px;align-items:end;margin-top:10px}
.sso-link-options .field{min-width:0}
.sso-single-use{height:42px;display:flex;align-items:center;gap:8px;font-size:13px;color:var(--txt)}
.sso-link-row{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:10px;align-items:center}
.sso-link-row .btn{white-space:nowrap}
.sso-link-meta{min-width:0;overflow:hidden}
.sso-link-title{font:700 13px/1.25 var(--font-ui);color:var(--txt);display:flex;gap:8px;align-items:center;min-width:0;flex-wrap:wrap}
.sso-link-badge{font:700 11px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:3px 5px;background:var(--card)}
.sso-link-badge.bad{color:var(--warn);border-color:color-mix(in srgb,var(--warn) 45%,var(--border))}
.field.hidden{display:none}
.policy-grid{display:grid;grid-template-columns:150px minmax(0,1fr);gap:10px;align-items:end}
.disabled-block{opacity:.52;filter:saturate(.65);pointer-events:none}
.status{margin-top:12px;color:#8fd0a8;white-space:pre-wrap;line-height:1.65}
.status.err{color:#ff9b9b}
.secret-note,.micro{font-size:12px;color:var(--muted);line-height:1.55}
.micro{margin-top:6px}
.list-head{display:flex;justify-content:space-between;align-items:center;gap:10px;flex-wrap:wrap;margin-bottom:10px}
.list-wrap{display:grid;gap:8px}
.list-row{border:1px solid var(--border);border-radius:4px;padding:10px;background:var(--card2)}
.access-group{display:grid;gap:12px}
.access-subgrid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:12px}
.access-subcard{border:1px solid var(--border);border-radius:4px;background:var(--card2);padding:12px;display:grid;gap:12px;min-width:0}
.access-subcard.full{grid-column:1/-1}
.access-subhead{display:flex;justify-content:space-between;gap:10px;align-items:flex-start;flex-wrap:wrap}
.access-subcard.collapsible>.access-subhead{cursor:pointer;user-select:none}
.access-subcard.collapsible>.access-subhead::after{content:'收起';font:700 12px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:5px 7px;background:var(--card)}
.access-subcard.collapsible.collapsed>.access-subhead::after{content:'展开'}
.access-subcard.collapsible.collapsed>:not(.access-subhead){display:none}
.access-subtitle{font:700 15px/1.2 var(--font-ui);color:var(--txt)}
.access-subcopy{margin-top:4px;color:var(--muted);font-size:12px;line-height:1.5}
.access-subcard .list-row,.access-subcard .empty-state{background:var(--card)}
.api-token-list{display:grid;gap:8px;max-height:420px;overflow:auto;padding-right:4px}
.api-token-row{border:1px solid var(--border);border-radius:4px;background:var(--card);padding:10px;display:grid;gap:10px;min-width:0}
.api-token-head{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px;align-items:center}
.api-token-name{font:700 13px/1.25 var(--font-ui);min-width:0;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.api-token-badges{display:flex;gap:6px;flex-wrap:wrap;align-items:center}
.api-token-badge{font:700 11px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:4px 6px;background:var(--card2);white-space:nowrap}
.api-token-badge.bad{color:var(--warn);border-color:color-mix(in srgb,var(--warn) 45%,var(--border))}
.api-token-create-grid{display:grid;grid-template-columns:minmax(150px,1fr) minmax(130px,.65fr) minmax(120px,.6fr) auto auto;gap:8px;align-items:end}
.api-token-grid{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px;align-items:center}
.api-token-grid .field{min-width:0}
.api-token-grid input:not([type="checkbox"]),.api-token-grid select,.api-token-create-grid input:not([type="checkbox"]),.api-token-create-grid select{height:38px}
.model-update-row{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:10px;align-items:center}
.model-editor{display:grid;gap:10px;margin-top:10px}
.model-editor-toolbar{display:grid;grid-template-columns:minmax(0,1fr) auto auto;gap:8px;align-items:center}
.model-editor-toolbar input{height:42px}
.model-map-list{display:grid;gap:8px;max-height:360px;overflow:auto;padding-right:4px}
.model-map-row{display:grid;grid-template-columns:minmax(100px,.42fr) minmax(0,1fr) auto;gap:8px;align-items:center;border:1px solid var(--border);border-radius:4px;background:var(--card2);padding:8px}
.model-map-row input{height:38px;border:1px solid var(--border);background:var(--card);color:var(--txt);border-radius:4px;padding:8px 10px;font:600 13px/1.25 var(--font-ui);min-width:0}
.model-map-row input.model-prefix{font-family:var(--font-mono);text-transform:uppercase}
.model-map-empty{padding:16px;border:1px dashed var(--border);border-radius:4px;color:var(--muted);background:var(--card2)}
.metric-toolbar{display:flex;align-items:center;gap:8px;flex-wrap:wrap;margin-top:12px}
.metric-toolbar .btn.active{border-color:var(--blue);background:color-mix(in srgb,var(--blue) 12%,var(--card2))}
.metric-toggle{display:flex;align-items:center;gap:7px;color:var(--muted);font-size:12px;margin-right:4px}
.metric-toggle input{width:16px;height:16px}
.metric-retention{display:grid;grid-template-columns:auto 82px auto;gap:8px;align-items:center;margin-left:auto;color:var(--muted);font-size:12px}
.metric-retention input{height:36px;border:1px solid var(--border);background:var(--card2);color:var(--txt);border-radius:4px;padding:7px 9px;font:600 13px/1 var(--font-ui)}
.metric-list{display:grid;gap:12px;margin-top:12px}
.metric-item{display:grid;grid-template-columns:minmax(0,1fr) auto;grid-template-areas:"label value" "chart chart";gap:9px;align-items:center;border:1px solid var(--border);border-radius:4px;background:var(--card2);padding:10px 12px;min-width:0}
.metric-label{grid-area:label;display:flex;align-items:center;gap:7px;min-width:0;font:600 13px/1.2 var(--font-ui)}
.metric-label i{width:12px;height:12px;border-radius:50%;display:inline-block;flex:0 0 auto}
.metric-spark-wrap{grid-area:chart;position:relative;height:136px;min-width:0;cursor:crosshair;touch-action:none;user-select:none}
.metric-spark-wrap.dragging{cursor:grabbing}
.metric-spark{width:100%;height:100%;display:block}
.metric-chart-tip{position:absolute;z-index:3;display:none;max-width:240px;transform:translate(-50%,calc(-100% - 10px));padding:7px 9px;border:1px solid color-mix(in srgb,var(--blue) 46%,var(--border));border-radius:4px;background:color-mix(in srgb,var(--card) 94%,transparent);box-shadow:0 12px 28px rgba(0,0,0,.24);font:600 12px/1.45 var(--font-mono);color:var(--txt);white-space:pre-line;pointer-events:none}
.metric-chart-tip.below{transform:translate(-50%,10px)}
.metric-value{grid-area:value;font:700 13px/1.2 var(--font-mono);text-align:right;color:var(--txt)}
.metric-zoom{display:grid;grid-template-columns:auto minmax(120px,1fr) auto;gap:8px;align-items:center;margin-top:10px;color:var(--muted);font-size:12px}
.metric-zoom input{width:100%}
.hook-layout{display:grid;grid-template-columns:minmax(110px,.7fr) minmax(0,1.5fr) 88px auto;gap:10px;align-items:end;min-width:0}
.zone-layout{display:grid;grid-template-columns:minmax(120px,1.2fr) 86px repeat(4,minmax(0,1fr)) auto;gap:10px;align-items:end;min-width:0}
.hook-layout>.field,.zone-layout>.field{min-width:0}
.empty-state{padding:14px;border:1px dashed var(--border);border-radius:4px;color:var(--muted);background:var(--card2)}
.security-alert{display:none;gap:8px;margin-top:14px;padding:12px;border:1px solid color-mix(in srgb,var(--warn) 46%,var(--border));border-radius:4px;background:color-mix(in srgb,var(--warn) 10%,var(--card2));color:var(--txt)}
.security-alert.show{display:grid}
.security-alert.ok{border-color:color-mix(in srgb,var(--green) 38%,var(--border));background:color-mix(in srgb,var(--green) 9%,var(--card2))}
.security-alert-title{font:700 14px/1.2 var(--font-ui);color:var(--txt)}
.security-alert-copy{font-size:13px;line-height:1.55;color:var(--muted)}
.security-alert.warn .security-alert-copy{color:color-mix(in srgb,var(--warn) 58%,white)}
.security-alert-actions{display:flex;gap:10px;flex-wrap:wrap}
.stats-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.stat{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
.stat .k{font:600 12px/1 var(--font-ui);color:var(--muted);letter-spacing:.01em}
.stat .v{margin-top:8px;font:600 20px/1.1 var(--font-ui)}
.stat .v.ip-lines{font:600 13px/1.45 var(--font-mono);display:grid;gap:5px;max-width:100%}
.ip-line{display:grid;grid-template-columns:minmax(0,1fr) auto;gap:8px;align-items:center;min-width:0}
.ip-text{display:block;min-width:0;max-width:100%;white-space:nowrap;overflow-x:auto;overflow-y:hidden;text-overflow:clip;scrollbar-width:thin}
.ip-len{font:600 11px/1 var(--font-ui);color:var(--muted);border:1px solid var(--border);border-radius:4px;padding:3px 5px;background:var(--card)}
.settings-ap-scroll{max-height:min(42vh,420px);overflow:auto;padding-right:4px}
.settings-ap-row-grid{display:grid;grid-template-columns:46px minmax(120px,.9fr) minmax(0,1.2fr) 86px;gap:10px;align-items:center;min-width:0}
.settings-ap-row-grid>*{min-width:0}
.settings-ap-row-grid .clip{white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
details.advanced{border:1px solid var(--border);border-radius:4px;padding:12px;background:var(--card2)}
details.advanced summary{cursor:pointer;font:600 14px/1.2 var(--font-ui);letter-spacing:.01em}
.split-actions{display:flex;justify-content:space-between;gap:10px;flex-wrap:wrap;align-items:center}
.modal-mask{position:fixed;inset:0;background:rgba(4,8,14,.66);backdrop-filter:blur(8px);display:none;align-items:center;justify-content:center;padding:20px;z-index:60}
.modal-mask.show{display:flex}
.modal-card{width:min(480px,100%);border:1px solid var(--border);border-radius:4px;background:var(--card);padding:18px;box-shadow:0 18px 32px rgba(0,0,0,.18)}
.modal-card.wide{width:min(900px,100%)}
.modal-card h3{margin:0 0 10px;font:600 20px/1 var(--font-ui)}
.one-time-secret{font:600 12px/1.55 var(--font-mono);word-break:break-all;border:1px solid var(--border);background:var(--card2);border-radius:4px;padding:12px;margin-top:12px;max-height:160px;overflow:auto}
.toast-stack{position:fixed;right:18px;bottom:18px;display:grid;gap:10px;z-index:72;width:min(420px,calc(100vw - 28px));pointer-events:none}
.toast{border:1px solid var(--border);border-radius:4px;background:color-mix(in srgb, var(--card) 96%, transparent);padding:12px 14px;box-shadow:0 14px 28px rgba(0,0,0,.18);opacity:0;transform:translateY(6px);transition:opacity .18s ease,transform .18s ease,border-color .18s ease;background-clip:padding-box;pointer-events:auto}
.toast.show{opacity:1;transform:translateY(0)}
.toast.ok{border-color:color-mix(in srgb, var(--green) 38%, var(--border))}
.toast.warn{border-color:color-mix(in srgb, var(--warn) 42%, var(--border))}
.toast-title{font:600 14px/1.2 var(--font-ui);margin-bottom:5px}
.toast-text{font-size:13px;line-height:1.5;color:var(--muted);white-space:pre-wrap}
@keyframes officeFade{from{opacity:0;transform:translateY(4px)}to{opacity:1;transform:none}}
@media (max-width:1360px){
  .hook-layout{grid-template-columns:repeat(2,minmax(0,1fr))}
  .api-token-create-grid{grid-template-columns:repeat(3,minmax(0,1fr))}
  .zone-layout{grid-template-columns:repeat(3,minmax(0,1fr))}
  .hook-layout .field:last-child,.api-token-create-grid .field:last-child,.zone-layout .field:last-child{grid-column:1/-1}
}
@media (max-width:1200px){.visual-grid{grid-template-columns:1fr}.access-subgrid,.hook-layout,.api-token-head,.api-token-create-grid,.api-token-grid,.policy-grid,.zone-layout,.field-inline,.model-update-row,.model-editor-toolbar,.model-map-row,.sso-link-options{grid-template-columns:1fr}.stats-grid{grid-template-columns:1fr}.metric-retention{margin-left:0}}
@media (max-width:700px){
  .wrap{width:min(100vw - 12px,1420px);padding:10px 6px 18px}
  .topbar,.draft-bar{gap:10px}
  .actions,.draft-actions{width:100%}
  .actions .btn,.draft-actions .btn{flex:1 1 140px}
  .card{padding:14px}
  .metric-item{grid-template-columns:minmax(0,1fr) auto;gap:7px}
  .metric-spark-wrap{height:118px}
  .toast-stack{right:10px;left:10px;bottom:10px;width:auto}
}
</style></head><body><div class="wrap">
  <div class="settings-sticky-head">
  <div class="topbar">
    <div>
      <div class="title">设置</div>
      <div class="sub">常用运行项在配置面板；文件级修改放在原始配置。</div>
    </div>
    <div class="actions">
      <button class="btn" id="btn-back" type="button">返回主页</button>
      <button class="btn" id="btn-logs" type="button">日志</button>
      <button class="btn ghost" id="btn-logout" type="button">登出</button>
      <button class="btn" id="btn-theme" type="button" style="display:none">浅色</button>
      <button class="btn" id="btn-reload-view" type="button">刷新</button>
    </div>
  </div>
  <div class="draft-bar">
    <div class="draft-copy">
      <div class="draft-title" id="draft-title">当前没有未保存修改</div>
      <div class="draft-meta" id="draft-meta">修改会先进入草稿；保存前可测试，或直接写入配置。</div>
    </div>
    <div class="draft-actions">
      <button class="btn" id="btn-test-visual" type="button" disabled>测试</button>
      <button class="btn warn" id="btn-save-visual" type="button" disabled>测试并保存</button>
      <button class="btn ghost" id="btn-save-visual-direct" type="button">直接保存</button>
    </div>
  </div>
  <div class="tabs">
    <button class="tab active" data-tab="visual" type="button">配置面板</button>
    <button class="tab" data-tab="raw" type="button">原始配置</button>
  </div>
  <div class="settings-jump" aria-label="设置分组导航">
    <button class="btn ghost" data-jump="settings-capture" type="button">采集</button>
    <button class="btn ghost" data-jump="settings-map" type="button">地图</button>
    <button class="btn ghost" data-jump="settings-access" type="button">访问</button>
    <button class="btn ghost" data-jump="settings-status" type="button">状态</button>
    <button class="btn ghost" data-jump="settings-data" type="button">数据</button>
    <button class="btn ghost" data-jump="settings-runtime" type="button">诊断</button>
  </div>
  </div>
  <div class="panel active" data-tab="visual">
    <div class="visual-grid">
      <div class="stack">
        <div class="stack-label">采集与访问</div>
        <div class="card" id="settings-capture" data-card-key="capture">
          <div class="section-head">
            <div>
              <h2>采集</h2>
              <div class="section-copy">设置采集网卡、信道、离线判定和机型识别库。</div>
            </div>
          </div>
          <div class="grid" style="margin-top:14px">
            <div class="field"><label>默认网卡</label><select id="cfg-iface"><option value="">未绑定</option></select><div class="micro"><button class="btn ghost" id="btn-network-bindings" type="button">自定义网卡绑定</button></div></div>
            <div class="field">
              <label>固定信道</label>
              <div class="field-inline">
                <input id="cfg-channel" type="number" min="1" max="196" disabled>
                <button class="btn ghost" id="btn-channel-edit" type="button">编辑</button>
                <button class="btn ghost" id="btn-channel-reset" type="button">默认</button>
              </div>
              <div class="micro" id="channel-hint" style="display:none"></div>
            </div>
            <div class="field"><label>飞机离线判定(s)</label><input id="cfg-lost-timeout" type="number" min="3" max="3600" step="1"></div>
            <div class="field full"><label>机型识别库</label><input id="cfg-model-map" type="text"></div>
            <div style="display:none">
              <input id="cfg-time" type="number" step="0.1">
              <input id="cfg-min-gap" type="number" step="0.1">
              <input id="cfg-rssi-delta" type="number">
              <input id="cfg-rssi-change" type="checkbox">
              <input id="cfg-payload-change" type="checkbox">
            </div>
            <div class="field full" data-card-key="capture">
              <label>识别库在线更新</label>
              <div class="model-update-row">
                <label><input id="cfg-model-update-enabled" type="checkbox"> 自动更新</label>
                <input id="cfg-model-update-url" type="text" placeholder="留空使用官方源">
                <button class="btn" id="btn-model-update-now" type="button">立即更新</button>
              </div>
              <div class="micro" id="model-update-state">识别库可从默认源或自定义地址同步。</div>
              <div class="model-update-row" style="margin-top:10px">
                <label><input id="cfg-app-update-enabled" type="checkbox"> 启动自动检查版本</label>
                <div class="micro" id="app-update-state">当前版本与最新版本尚未检查。</div>
                <button class="btn ghost" id="btn-app-update-check" type="button">手动检查版本</button>
              </div>
              <div class="row-actions" style="margin-top:10px"><button class="btn ghost" id="btn-model-map-open" type="button">编辑识别库</button></div>
            </div>
            <div class="field full"><label>扫描数据文件</label><input id="cfg-history-file" type="text"></div>
          </div>
          <div class="checks" style="margin-top:14px">
            <label><input id="cfg-heal" type="checkbox"> 自愈恢复</label>
            <label><input id="cfg-debug" type="checkbox"> 调试日志</label>
          </div>
          <details class="advanced" style="margin-top:14px">
            <summary>高级采集参数</summary>
            <div class="grid" style="margin-top:14px">
              <div class="field"><label>2.4G 驻留(ms)</label><input id="cfg-dwell2g" type="number"></div>
              <div class="field"><label>5G 驻留(ms)</label><input id="cfg-dwell5g" type="number"></div>
              <div class="field"><label>切换稳定等待(ms)</label><input id="cfg-settle" type="number"></div>
              <div class="field"><label>命中驻留(ms)</label><input id="cfg-hit-dwell" type="number"></div>
              <div class="field"><label>命中上限(ms)</label><input id="cfg-hit-cap" type="number"></div>
            </div>
            <div class="checks" style="margin-top:14px">
              <label><input id="cfg-hop" type="checkbox"> 自动跳频</label>
              <label><input id="cfg-hop5g" type="checkbox"> 跳频含 5G</label>
              <label><input id="cfg-fast" type="checkbox"> 扫描 WiFi 快传</label>
            </div>
          </details>
        </div>
        <div class="card" id="settings-map" data-card-key="map">
          <div class="section-head">
            <div>
              <h2>地图与基站</h2>
              <div class="section-copy">控制地图中心、基站坐标、默认缩放和航向参考。</div>
            </div>
          </div>
          <div class="grid">
            <div class="field"><label>基站名称</label><input id="cfg-base-name" type="text"></div>
            <div class="field"><label>DJI 查询地址</label><input id="cfg-dji-url" type="text"></div>
            <div class="field"><label>基站纬度</label><input id="cfg-base-lat" type="number" step="0.000001"></div>
            <div class="field"><label>基站经度</label><input id="cfg-base-lon" type="number" step="0.000001"></div>
            <div class="field"><label>默认缩放</label><input id="cfg-base-zoom" type="number" min="3" max="30"></div>
            <div class="field"><label>参考航向(°)</label><input id="cfg-heading-ref" type="number" step="0.1"></div>
            <div class="field"><label>自动回中冷却(s)</label><input id="cfg-map-idle" type="number" min="5" max="600"></div>
            <div class="field full">
              <label>定位</label>
              <div class="row-actions">
                <button class="btn" id="btn-browser-loc" type="button">读取浏览器位置</button>
                <button class="btn ghost" id="btn-clear-base-loc" type="button">清空基站坐标</button>
              </div>
              <div class="micro" id="base-geo-hint">浏览器定位能力由当前访问协议和浏览器权限决定。</div>
            </div>
          </div>
        </div>
        <div class="card" data-card-key="zones">
          <div class="list-head">
            <div>
              <h2>报警区域</h2>
              <div class="section-copy">用两组经纬度边界定义矩形告警范围。</div>
            </div>
            <button class="btn" id="btn-zone-add" type="button">添加区域</button>
          </div>
          <div id="zone-list" class="list-wrap"></div>
        </div>
        <div class="card access-group" id="settings-access" data-card-key="access">
          <div class="section-head">
            <div>
              <h2>通知与访问控制</h2>
              <div class="section-copy">管理通知、登录方式、API Token 和访问来源规则。</div>
            </div>
          </div>
          <div class="access-subgrid">
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">通知通道</div>
                  <div class="access-subcopy">企业微信机器人通道、通知开关和发送节奏。</div>
                </div>
                <button class="btn" id="btn-hook-add" type="button">添加通道</button>
              </div>
              <div id="wecom-list" class="list-wrap"></div>
              <div class="grid">
                <div class="field"><label>重上线冷却(s)</label><input id="cfg-reonline" type="number"></div>
                <div class="field"><label>通知超时(s)</label><input id="cfg-send-timeout" type="number"></div>
              </div>
              <div class="checks">
                <label><input id="cfg-notify-enabled" type="checkbox"> 启用企业微信通知</label>
                <label><input id="cfg-notify-reonline" type="checkbox"> 允许重上线通知</label>
              </div>
            </div>
            <div class="access-subcard full collapsible collapsed">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">网页登录</div>
                  <div class="access-subcopy">控制设置页和内置页面的账号密码登录会话。</div>
                </div>
              </div>
              <div class="grid">
                <div class="field"><label>登录标题</label><input id="cfg-auth-realm" type="text"><div class="micro">显示在登录框和认证域。</div></div>
                <div class="field"><label>会话有效期(min)</label><input id="cfg-auth-ttl" type="number" min="1" max="10080" step="1"><div class="micro">范围 1 分钟到 7 天。</div></div>
                <div class="field"><label>网页登录账号</label><input id="cfg-auth-user" type="text" placeholder="留空即不修改"></div>
                <div class="field"><label>网页登录密码</label><input id="cfg-auth-pass" type="password" placeholder="留空即不修改"></div>
              </div>
              <div class="checks">
                <label><input id="cfg-auth-enabled" type="checkbox"> 启用网页登录鉴权</label>
              </div>
              <div class="checks">
                <label><input id="cfg-auth-method-password" type="checkbox"> 账号密码登录</label>
                <label><input id="cfg-auth-method-passkey" type="checkbox"> PassKey 登录</label>
              </div>
              <div class="micro" id="auth-method-state">至少保留一种网页登录方式；关闭账号密码直接登录后，账号密码仍用于设置页二次确认。</div>
            </div>
            <div class="access-subcard full collapsible collapsed">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">通行密钥登录</div>
                  <div class="access-subcopy">为网页登录账号绑定浏览器通行密钥，支持一键登录。</div>
                </div>
              </div>
              <div class="grid">
                <div class="field full"><label>通行密钥名称</label><input id="cfg-passkey-name" type="text" placeholder="留空即自动命名"><div class="micro">用于区分不同设备或浏览器。</div></div>
              </div>
              <div class="row-actions">
                <button class="btn" id="btn-passkey-add" type="button">验证并添加</button>
              </div>
              <div class="micro" id="passkey-state">完成网页登录账号和密码配置后，可在这里添加通行密钥。</div>
              <div id="passkey-list" class="passkey-list"></div>
            </div>
            <div class="access-subcard full collapsible collapsed">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">SSO 登录链接</div>
                  <div class="access-subcopy">SSO 不作为可关闭的登录方式；只要存在有效链接，它就是最高优先级验证入口。</div>
                </div>
              </div>
              <div class="token-actions">
                <input id="login-link-name" type="text" placeholder="链接名称">
                <button class="btn" id="btn-login-link-create" type="button">生成</button>
              </div>
              <div class="sso-link-options">
                <div class="field"><label>有效期</label><select id="login-link-expire-mode">
                  <option value="86400">24 小时</option>
                  <option value="3600">1 小时</option>
                  <option value="604800">7 天</option>
                  <option value="never">无限时间</option>
                  <option value="custom">自定义分钟</option>
                </select></div>
                <div class="field hidden" id="login-link-custom-field"><label>自定义有效期(min)</label><input id="login-link-ttl-min" type="number" min="1" max="5256000" step="1" value="1440"></div>
                <label class="sso-single-use"><input id="login-link-single-use" type="checkbox"> 单次登录</label>
              </div>
              <div class="micro" id="login-link-state">SSO 链接由校验码、有效期和单次登录状态控制；命中有效 SSO 链接时优先于其它网页登录方式。</div>
              <div id="login-link-list" class="list-wrap sso-link-list"></div>
            </div>
            <div class="access-subcard full collapsible collapsed">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">API Token</div>
                  <div class="access-subcopy">外部 API Token 随机生成，只在创建成功时显示一次。</div>
                </div>
              </div>
              <div class="api-token-create-grid">
                <div class="field"><label>名称</label><input id="api-token-new-name" type="text" placeholder="Token 名称"></div>
                <div class="field"><label>有效期</label><select id="api-token-new-expire-mode">
                  <option value="86400">24 小时</option>
                  <option value="3600">1 小时</option>
                  <option value="604800">7 天</option>
                  <option value="never">无限时间</option>
                  <option value="custom">自定义分钟</option>
                </select></div>
                <div class="field hidden" id="api-token-custom-field"><label>自定义(min)</label><input id="api-token-new-ttl-min" type="number" min="1" max="5256000" step="1" value="1440"></div>
                <label class="sso-single-use"><input id="api-token-new-single-use" type="checkbox"> 单次使用</label>
                <div class="field"><label>&nbsp;</label><button class="btn" id="btn-api-token-add" type="button">验证并生成</button></div>
              </div>
              <div id="api-token-list" class="api-token-list"></div>
              <div class="checks">
                <label><input id="cfg-api-enabled" type="checkbox"> 启用外部 API</label>
              </div>
            </div>
            <div class="access-subcard full collapsible collapsed">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">API 白名单</div>
                  <div class="access-subcopy">限制外部 API 来源地址</div>
                </div>
              </div>
              <div id="api-whitelist-block">
                <div class="policy-grid">
                  <div class="field"><label>模式</label><select id="cfg-api-whitelist-mode"><option value="allow">白名单</option><option value="deny">黑名单</option></select></div>
                  <div class="checks"><label><input id="cfg-api-whitelist-enabled" type="checkbox"> 启用 API 访问规则</label></div>
                </div>
                <div class="field full"><label>地址列表</label><textarea id="cfg-api-whitelist" spellcheck="false" style="min-height:140px"></textarea><div class="micro">每行一个 IP 或 CIDR。</div></div>
              </div>
            </div>
            <div class="access-subcard full collapsible collapsed">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">网页访问规则</div>
                  <div class="access-subcopy">限制设置页、主页和内置页面的访问来源。</div>
                </div>
              </div>
              <div class="policy-grid">
                <div class="field"><label>模式</label><select id="cfg-web-access-mode"><option value="allow">白名单</option><option value="deny">黑名单</option></select></div>
                <div class="checks"><label><input id="cfg-web-access-enabled" type="checkbox"> 启用网页访问规则</label></div>
              </div>
              <div class="field full"><label>地址列表</label><textarea id="cfg-web-access-list" spellcheck="false" style="min-height:120px"></textarea><div class="micro">每行一个 IP 或 CIDR；拒绝时页面返回 403。</div></div>
            </div>
          </div>
          <div class="secret-note" id="secret-state">通知、登录、Token 和外部 API 状态摘要。</div>
          <div id="status-visual" class="status">-</div>
        </div>
      </div>
      <div class="stack">
        <div class="stack-label">状态与维护</div>
        <div class="card" id="settings-status">
          <div class="section-head">
            <div>
              <h2>主机状态</h2>
              <div class="section-copy">查看主机负载、网络地址和当前采集状态。</div>
            </div>
            <button class="btn ghost" id="btn-refresh-host" type="button">刷新状态</button>
          </div>
          <div id="host-stats" class="stats-grid" style="margin-top:14px"></div>
          <div id="host-meta" class="micro">-</div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn" id="btn-open-hw" type="button">打开硬件助手</button>
            <button class="btn" id="btn-diagnostic-export" type="button">导出质量分析包</button>
          </div>
        </div>
        <div class="card settings-collapsible collapsed" id="settings-data">
          <div class="section-head">
            <div>
              <h2>权限与 systemd 服务</h2>
              <div class="section-copy">检查运行权限；需要修复时再写入 systemd 配置。</div>
            </div>
          </div>
          <div id="runtime-security-alert" class="security-alert">
            <div class="security-alert-title" id="runtime-security-title">权限检测</div>
            <div class="security-alert-copy" id="runtime-security-copy">正在读取运行权限...</div>
            <div class="security-alert-actions">
              <button class="btn warn" id="btn-security-repair" type="button">一键修复</button>
            </div>
          </div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn ghost" id="btn-service-refresh" type="button">刷新服务状态</button>
            <button class="btn" id="btn-service-register" type="button">注册/更新服务</button>
            <button class="btn" id="btn-iw-install" type="button">安装无线工具</button>
          </div>
          <div class="micro" style="margin-top:10px">修复会创建运行账号、整理文件权限，并授予采集与热点所需能力；sudo 密码只用于本次操作。</div>
          <div id="status-system-service" class="status">正在读取服务状态...</div>
        </div>
        <div class="card" data-card-key="metrics">
          <div class="section-head">
            <div>
              <h2>节点负载</h2>
              <div class="section-copy">记录 CPU、内存、温度、负载和 AP 数趋势。</div>
            </div>
          </div>
          <div class="metric-toolbar">
            <label class="metric-toggle"><input id="cfg-metrics-enabled" type="checkbox"><span>启用节点负载记录</span></label>
            <button class="btn ghost metric-window active" data-window="12h" type="button">12小时</button>
            <button class="btn ghost metric-window" data-window="24h" type="button">24小时</button>
            <button class="btn ghost metric-window" data-window="7d" type="button">7天</button>
            <label class="metric-retention"><span>保留</span><input id="cfg-metrics-retention" type="number" min="1" max="90" step="1"><span>天</span></label>
          </div>
          <div class="grid" style="margin-top:12px">
            <div class="field">
              <label>温度数据来源</label>
              <select id="cfg-metrics-temp-source">
                <option value="auto">自动（优先 vcgencmd）</option>
                <option value="vcgencmd">仅 vcgencmd</option>
                <option value="thermal_zone">仅 /sys/class/thermal</option>
                <option value="hwmon">仅 /sys/class/hwmon</option>
                <option value="off">关闭温度采集</option>
              </select>
              <div class="micro">节点温度会写入主机状态和温度曲线；关闭后显示为空值。</div>
            </div>
          </div>
          <div class="metric-list" id="metrics-list">
            <div class="metric-item" data-metric="cpu"><div class="metric-label"><i style="background:#2899f5"></i>CPU</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="cpu"></canvas></div><div class="metric-value" id="metric-value-cpu">—</div></div>
            <div class="metric-item" data-metric="mem"><div class="metric-label"><i style="background:#92c353"></i>内存</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="mem"></canvas></div><div class="metric-value" id="metric-value-mem">—</div></div>
            <div class="metric-item" data-metric="temp"><div class="metric-label"><i style="background:#f7630c"></i>温度</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="temp"></canvas></div><div class="metric-value" id="metric-value-temp">—</div></div>
            <div class="metric-item" data-metric="load"><div class="metric-label"><i style="background:#c19c00"></i>负载</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="load"></canvas></div><div class="metric-value" id="metric-value-load">—</div></div>
            <div class="metric-item" data-metric="ap"><div class="metric-label"><i style="background:#8764b8"></i>AP数</div><div class="metric-spark-wrap"><canvas class="metric-spark" data-metric="ap"></canvas></div><div class="metric-value" id="metric-value-ap">—</div></div>
          </div>
          <label class="metric-zoom"><span>缩放</span><input id="metrics-zoom" type="range" min="1" max="100" step="1" value="1"><span id="metrics-zoom-value">1x</span></label>
          <div id="status-metrics" class="micro">-</div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>设置与扫描数据</h2>
              <div class="section-copy">分别导入导出配置与扫描数据，避免两类文件混用。</div>
            </div>
          </div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn" id="btn-export-settings-file" type="button">导出设置文件</button>
            <button class="btn ghost" id="btn-import-settings-file" type="button">导入设置文件</button>
            <input id="import-settings-file" type="file" accept=".json,application/json" style="display:none">
          </div>
          <div class="row-actions" style="margin-top:10px">
            <button class="btn" id="btn-export-scan-data" type="button">导出扫描数据</button>
            <button class="btn ghost" id="btn-import-scan-data" type="button">导入扫描数据</button>
            <input id="import-scan-data-file" type="file" accept=".json,application/json" style="display:none">
          </div>
          <div class="micro" id="settings-config-path" style="margin-top:10px">设置文件: -</div>
          <div class="micro" id="settings-scan-data-path">扫描数据文件: -</div>
          <div id="status-data-transfer" class="status">-</div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>许可协议</h2>
              <div class="section-copy">查看或撤回 EULA 确认；撤回后会重新要求确认。</div>
            </div>
          </div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn" id="btn-eula-view" type="button">查看 EULA</button>
            <button class="btn warn" id="btn-eula-revoke" type="button">撤回同意</button>
          </div>
          <div id="status-eula" class="status">-</div>
        </div>
        <div class="card">
          <div class="section-head">
            <div>
              <h2>浏览器偏好</h2>
              <div class="section-copy">仅影响当前浏览器的显示偏好。</div>
            </div>
          </div>
          <div class="checks pref-checks" style="margin-top:14px">
            <label><input id="pref-new-firmware-parser" type="checkbox"> 显示 RID 包解析结果</label>
          </div>
          <div class="micro">只控制当前浏览器显示；后台仍按旧 ODID 和新版 DJI Beacon 两套规则分别解析。默认开启。</div>
        </div>
        <div class="card settings-collapsible collapsed" id="settings-runtime">
          <div class="section-head">
            <div>
              <h2>实时 AP</h2>
              <div class="section-copy">查看最近扫描到的 AP 和运行日志片段。</div>
            </div>
            <button class="btn ghost" id="btn-refresh-runtime" type="button">刷新</button>
          </div>
          <div id="settings-ap-list" class="list-wrap" style="margin-top:14px"></div>
          <div class="field full" style="margin-top:14px"><label>扫描日志</label><textarea id="settings-runtime-log" readonly spellcheck="false" style="min-height:220px"></textarea></div>
          <div id="status-runtime" class="status">-</div>
        </div>
      </div>
    </div>
  </div>
  <div class="panel" data-tab="raw">
    <div class="card">
      <div class="raw-toolbar">
        <div>
          <h2>原始配置</h2>
          <div class="section-copy">浏览配置目录树、切换文件、编辑保存和删除配置文件。进入前需要先验证网页登录密码。</div>
        </div>
        <div class="row-actions">
          <button class="btn" id="btn-load-raw" type="button">刷新目录</button>
          <button class="btn warn" id="btn-save-raw" type="button">保存当前文件</button>
          <button class="btn warn" id="btn-delete-raw" type="button">删除当前文件</button>
          <button class="btn ghost" id="btn-raw-unlock" type="button">验证密码</button>
        </div>
      </div>
      <div class="raw-lock" id="raw-lock-card">
        <strong id="raw-lock-title">原始配置已锁定</strong>
        <div class="micro" id="raw-lock-copy">需要先验证网页登录密码，才能查看和编辑配置文件。</div>
        <div class="row-actions">
          <button class="btn" id="btn-raw-unlock-inline" type="button">验证密码</button>
        </div>
      </div>
      <div class="raw-layout" id="raw-layout">
        <aside class="raw-pane">
          <div class="raw-meta">
            <div class="meta-copy">
              <div class="meta-title" id="raw-tree-title">配置目录</div>
              <div class="meta-sub" id="raw-tree-path">-</div>
            </div>
          </div>
          <div id="raw-tree" class="raw-tree"></div>
        </aside>
        <section class="raw-main">
          <div class="raw-meta">
            <div class="meta-copy">
              <div class="meta-title" id="raw-file-title">未选择文件</div>
              <div class="meta-sub" id="raw-file-path">-</div>
            </div>
            <div class="meta-copy" style="text-align:right">
              <div class="meta-title" id="raw-file-size">-</div>
              <div class="meta-sub" id="raw-file-mtime">-</div>
            </div>
          </div>
          <textarea id="raw-editor" class="raw-editor" spellcheck="false"></textarea>
          <div id="status-raw" class="status">-</div>
        </section>
      </div>
    </div>
  </div>
<div id="settings-toast-stack" class="toast-stack" aria-live="polite" aria-atomic="true"></div>
<div class="modal-mask" id="network-bind-modal">
  <div class="modal-card wide">
    <h3>自定义网卡绑定</h3>
    <div class="section-copy">按网卡现状分配用途。“扫描”会写回默认采集网卡；AP 热点使用 hostapd、内置 DHCP 和 172.16.0.1:80。</div>
    <div class="model-editor">
      <div class="model-editor-toolbar">
        <button class="btn ghost" id="btn-network-bind-refresh" type="button">扫描网卡</button>
        <button class="btn" id="btn-network-bind-save" type="button">写入草稿</button>
        <button class="btn warn" id="btn-network-bind-apply" type="button">应用到系统</button>
      </div>
      <div class="grid">
        <div class="field"><label>热点 SSID</label><input id="net-ap-ssid" type="text"></div>
        <div class="field"><label>热点密码</label><input id="net-ap-password" type="password" placeholder="留空为开放热点"></div>
        <div class="field"><label>热点信道</label><input id="net-ap-channel" type="number" min="1" max="196"></div>
        <div class="field"><label>HTTP 监听</label><input id="net-ap-http" type="text" value="172.16.0.1:80" disabled></div>
      </div>
      <div id="network-bind-list" class="list-wrap"></div>
      <div id="status-network-bind" class="status">-</div>
    </div>
    <div class="row-actions" style="margin-top:14px;justify-content:flex-end">
      <button class="btn ghost" id="btn-network-bind-close" type="button">关闭</button>
    </div>
  </div>
</div>
<div class="modal-mask" id="reauth-modal">
  <div class="modal-card">
    <h3>再次验证</h3>
    <div class="section-copy">二次验证保护 Token 显示、复制、PassKey 添加和原始配置解锁。</div>
    <div class="grid" style="margin-top:14px">
      <div class="field full"><label>账号</label><input id="reauth-user" type="text" autocomplete="username"></div>
      <div class="field full"><label>密码</label><input id="reauth-pass" type="password" autocomplete="current-password"></div>
    </div>
    <div class="row-actions" style="margin-top:14px">
      <button class="btn ghost" id="btn-reauth-cancel" type="button">取消</button>
      <button class="btn" id="btn-reauth-confirm" type="button">确认</button>
    </div>
    <div id="reauth-status" class="status">-</div>
  </div>
</div>
<div class="modal-mask" id="elevate-modal">
  <div class="modal-card">
    <h3>临时提权</h3>
    <div class="section-copy" id="elevate-copy">此操作需要 root 权限；sudo 密码只用于本次请求，不会保存。</div>
    <div class="grid" style="margin-top:14px">
      <div class="field full"><label>sudo 密码</label><input id="elevate-pass" type="password" autocomplete="off"></div>
    </div>
    <div class="row-actions" style="margin-top:14px">
      <button class="btn ghost" id="btn-elevate-cancel" type="button">取消</button>
      <button class="btn" id="btn-elevate-confirm" type="button">确认</button>
    </div>
    <div id="elevate-status" class="status">-</div>
  </div>
</div>
<div class="modal-mask" id="one-time-modal">
  <div class="modal-card">
    <h3 id="one-time-title">只显示一次</h3>
    <div class="section-copy" id="one-time-note">关闭后不能再次查看或复制。</div>
    <div class="one-time-secret" id="one-time-secret"></div>
    <div class="row-actions" style="margin-top:14px">
      <button class="btn" id="btn-one-time-copy" type="button">复制</button>
      <button class="btn ghost" id="btn-one-time-close" type="button">关闭</button>
    </div>
  </div>
</div>
<div class="modal-mask" id="model-map-modal">
  <div class="modal-card wide">
    <h3>识别库编辑</h3>
    <div class="section-copy">编辑本地 rid-models.json 条目，保存后立即刷新实时和历史机型。</div>
    <div class="model-editor">
      <div class="model-editor-toolbar">
        <input id="model-map-search" type="text" placeholder="前缀或机型">
        <button class="btn ghost" id="btn-model-map-add" type="button">新增</button>
        <button class="btn" id="btn-model-map-save" type="button">保存列表</button>
      </div>
      <div id="model-map-list" class="model-map-list"></div>
      <div class="micro" id="model-map-editor-state">当前机型识别库保存识别条目。</div>
    </div>
    <div class="row-actions" style="margin-top:14px"><button class="btn ghost" id="btn-model-map-close" type="button">关闭</button></div>
  </div>
</div>
<script>
function qs(id){ return document.getElementById(id); }
function qsa(sel){ return Array.prototype.slice.call(document.querySelectorAll(sel) || []); }
function enc(v){ return String(v == null ? '' : v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function splitLines(text){
  var raw = String(text || '');
  if(raw.indexOf('\\r') >= 0) raw = raw.split('\\r').join('');
  return raw.split('\\n');
}
function isLocalHostName(host){
  var h = String(host || '').toLowerCase();
  return h === 'localhost' || h === '127.0.0.1';
}
var apiTokenRows = [];
var oneTimeSecretValue = '';
var reauthAction = null;
var elevateResolve = null;
var lastSystemServiceStatus = null;
var loginLinks = [];
var modelMapRows = [];
var modelMapPath = '';
var settingsState = {visualLoaded:false, rawLoaded:false, rawUnlocked:false, rawRoot:'', rawTree:null, rawSelectedPath:'', rawSelectedRel:'', channelUseDefault:true, channelEditing:false, visualInitial:null, visualDirty:false, dirtyCards:{}, authConfigured:false, networkBindings:null, interfaceItems:[]};
var metricsState = {window:'12h', zoom:1, panSec:0, hover:null, drag:null, chartMeta:{}, items:[]};
var SETTINGS_DRAFT_SECTIONS = [
  {key:'capture', label:'采集'},
  {key:'map', label:'地图与基站'},
  {key:'zones', label:'报警区域'},
  {key:'access', label:'通知与访问控制'},
  {key:'metrics', label:'节点负载'}
];
var COOKIE_TRACK_REALTIME = 'rid_realtime_track';
var COOKIE_TRACK_2H_ONLY = 'rid_track_2h_only';
var FREEZE_ON_HOME_KEY = 'rid_freeze_on_home_once';
var NEW_FIRMWARE_PARSE_KEY = 'rid_new_firmware_parse_enabled';
function on(id, type, handler){
  var el = qs(id);
  if(el) el.addEventListener(type, handler);
  return el;
}
function bindAccessCollapsibles(){
  qsa('.access-subcard.collapsible > .access-subhead').forEach(function(head){
    head.setAttribute('role', 'button');
    head.setAttribute('tabindex', '0');
    function toggle(){
      var card = head.closest('.access-subcard');
      if(card) card.classList.toggle('collapsed');
    }
    head.addEventListener('click', toggle);
    head.addEventListener('keydown', function(ev){
      if(ev.key === 'Enter' || ev.key === ' '){
        ev.preventDefault();
        toggle();
      }
    });
  });
}
function bindSettingsCardCollapsibles(){
  qsa('.card.settings-collapsible > .section-head').forEach(function(head){
    head.setAttribute('role', 'button');
    head.setAttribute('tabindex', '0');
    function toggle(){
      var card = head.closest('.card.settings-collapsible');
      if(card) card.classList.toggle('collapsed');
    }
    head.addEventListener('click', function(ev){
      var t = ev.target;
      if(t && t.closest && t.closest('button,input,label,a,select,textarea')) return;
      toggle();
    });
    head.addEventListener('keydown', function(ev){
      if(ev.key === 'Enter' || ev.key === ' '){
        ev.preventDefault();
        toggle();
      }
    });
  });
}
async function guarded(action, statusId, okText, okMs, warnMs){
  try{
    await action();
    if(okText) showNotice(okText, 'ok', okMs || 2200);
  }catch(e){
    if(statusId) setStatus(statusId, e.message || e, true);
    showNotice(e.message || e, 'warn', warnMs || 3800);
  }
}
function syncSettingsViewport(){
  var vp = window.visualViewport;
  var vh = Math.max(320, Math.round((vp && vp.height) ? vp.height : window.innerHeight || 0));
  document.documentElement.style.setProperty('--app-vh', vh + 'px');
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
  var nDays = Number(days);
  if(!isFinite(nDays) || nDays <= 0) nDays = 365;
  var secure = (location.protocol === 'https:') ? '; Secure' : '';
  document.cookie = key + '=' + encodeURIComponent(String(value == null ? '' : value))
    + '; Max-Age=' + Math.round(nDays * 86400) + '; Path=/; SameSite=Lax' + secure;
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
function setStatus(id, text, err){
  var el = qs(id); if(!el) return;
  el.textContent = String(text || '-');
  el.classList.toggle('err', !!err);
}
function showNotice(text, kind, timeoutMs){
  var host = qs('settings-toast-stack');
  if(!host) return;
  var node = document.createElement('div');
  var tone = (kind === 'warn' || kind === 'error') ? 'warn' : 'ok';
  node.className = 'toast ' + tone;
  node.innerHTML = '<div class="toast-title">' + (tone === 'warn' ? '操作结果' : '已完成') + '</div>'
    + '<div class="toast-text">' + enc(String(text || '')) + '</div>';
  host.appendChild(node);
  requestAnimationFrame(function(){ node.classList.add('show'); });
  var ttl = Math.max(1800, Number(timeoutMs || 3200));
  window.setTimeout(function(){
    node.classList.remove('show');
    window.setTimeout(function(){ if(node.parentNode) node.parentNode.removeChild(node); }, 220);
  }, ttl);
}
function apiUrl(url){
  try{ return new URL(String(url||''), window.location.origin).toString(); }catch(_e){ return String(url||''); }
}
function pageHeaders(extra){
  var headers = {'X-LightRID-Page':'1'};
  if(extra && typeof extra === 'object'){
    Object.keys(extra).forEach(function(k){ headers[k] = extra[k]; });
  }
  return headers;
}
var authRedirecting = false;
function authExpired(r, d){
  var err = String((d && d.error) || '');
  return r && r.status === 401 && (!!(d && d.auth_expired) || err === 'login required' || err === 'auth required');
}
function redirectLogin(){
  if(authRedirecting) return;
  authRedirecting = true;
  location.href = '/login?next=/';
}
async function copyTextPlain(text){
  var raw = String(text || '');
  if(!raw) throw new Error('没有可复制的内容');
  if(navigator.clipboard && navigator.clipboard.writeText){
    try{
      await navigator.clipboard.writeText(raw);
      return;
    }catch(_e){}
  }
  var ta = document.createElement('textarea');
  ta.value = raw;
  ta.style.position = 'fixed';
  ta.style.opacity = '0';
  ta.style.pointerEvents = 'none';
  document.body.appendChild(ta);
  ta.focus();
  ta.select();
  try{
    if(!document.execCommand('copy')) throw new Error('copy failed');
  }finally{
    if(ta.parentNode) ta.parentNode.removeChild(ta);
  }
}
function parseFilenameFromDisposition(headerValue){
  var cd = String(headerValue || '');
  var marker = 'filename=';
  var pos = cd.toLowerCase().indexOf(marker);
  if(pos < 0) return '';
  var raw = cd.slice(pos + marker.length).trim();
  if(raw.charAt(0) === '"'){
    var end = raw.indexOf('"', 1);
    raw = end > 0 ? raw.slice(1, end) : raw.slice(1);
  }else{
    var semi = raw.indexOf(';');
    if(semi >= 0) raw = raw.slice(0, semi);
  }
  return raw.trim();
}
async function downloadQualityReport(){
  showNotice('正在生成质量分析包...', 'ok', 2200);
  const r = await fetch(apiUrl('/api/tools/diagnostic.zip'), {cache:'no-store', headers:pageHeaders()});
  if(!r.ok){
    var errText = '';
    try{
      var errJson = await r.json();
      if(authExpired(r, errJson)){ redirectLogin(); throw new Error('login required'); }
      errText = errJson.error || '';
    }catch(_e){
      try{ errText = await r.text(); }catch(_e2){}
    }
    throw new Error(errText || ('HTTP ' + r.status));
  }
  const blob = await r.blob();
  if(!blob || Number(blob.size || 0) < 128){
    throw new Error('质量分析包为空，请稍后重试或查看服务日志');
  }
  var filename = parseFilenameFromDisposition(r.headers.get('Content-Disposition')) || 'light-rid-quality.zip';
  var url = URL.createObjectURL(blob);
  var a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  window.setTimeout(function(){
    URL.revokeObjectURL(url);
    if(a.parentNode) a.parentNode.removeChild(a);
  }, 15000);
  showNotice('质量分析包已生成。', 'ok', 3200);
}
function transferStamp(){
  var d = new Date();
  function pad(n){ return String(n).padStart(2, '0'); }
  return String(d.getFullYear()) + pad(d.getMonth() + 1) + pad(d.getDate()) + '_' + pad(d.getHours()) + pad(d.getMinutes()) + pad(d.getSeconds());
}
function downloadBlobFile(name, blob){
  var fileName = String(name || 'download.bin').trim() || 'download.bin';
  var data = blob instanceof Blob ? blob : new Blob([blob == null ? '' : blob], {type:'application/octet-stream'});
  var url = URL.createObjectURL(data);
  var a = document.createElement('a');
  a.href = url;
  a.download = fileName;
  document.body.appendChild(a);
  a.click();
  window.setTimeout(function(){
    URL.revokeObjectURL(url);
    if(a.parentNode) a.parentNode.removeChild(a);
  }, 15000);
}
function downloadJsonObject(name, data){
  var text = JSON.stringify(data == null ? {} : data, null, 2) + '\\n';
  downloadBlobFile(name, new Blob([text], {type:'application/json;charset=utf-8'}));
}
function pickFileInput(id){
  var input = qs(id);
  if(!input) return;
  input.value = '';
  input.click();
}
function readJsonFile(file){
  return new Promise(function(resolve, reject){
    if(!file){
      reject(new Error('未选择文件'));
      return;
    }
    var fr = new FileReader();
    fr.onload = function(){
      try{
        resolve(JSON.parse(String(fr.result || '')));
      }catch(e){
        reject(new Error('JSON 解析失败: ' + (e && e.message ? e.message : e)));
      }
    };
    fr.onerror = function(){ reject(new Error('文件读取失败')); };
    fr.readAsText(file, 'utf-8');
  });
}
async function exportSettingsFile(){
  setStatus('status-data-transfer', '正在导出设置文件...', false);
  var data = await getJson('/api/settings/export/settings');
  downloadJsonObject('rid_settings_' + transferStamp() + '.json', data);
  setStatus('status-data-transfer', '设置文件已导出: ' + String(data.config_path || '-'), false);
  showNotice('设置文件已导出。', 'ok', 2600);
}
async function exportScanDataFile(){
  setStatus('status-data-transfer', '正在导出扫描数据...', false);
  var data = await getJson('/api/settings/export/scan-data');
  downloadJsonObject('rid_scan_data_' + transferStamp() + '.json', data);
  setStatus('status-data-transfer', '扫描数据已导出: ' + Number(data.count || 0) + ' 条', false);
  showNotice('扫描数据已导出。', 'ok', 2600);
}
async function importSettingsFileFromFile(file){
  setStatus('status-data-transfer', '正在导入设置文件...', false);
  var payload = await readJsonFile(file);
  var data = await postJson('/api/settings/import/settings', {payload: payload});
  var msg = '设置文件导入完成: ' + String(data.saved_to || '-');
  if(data.backup_path) msg += '\\n备份: ' + String(data.backup_path);
  if(data.reload_msg) msg += '\\n' + String(data.reload_msg);
  setStatus('status-data-transfer', msg, false);
  showNotice('设置文件已导入并生效。', 'ok', 3200);
  await loadVisual();
}
async function importScanDataFileFromFile(file){
  var payload = await readJsonFile(file);
  var merge = window.confirm('扫描数据导入方式：\\n确定 = 增量更新\\n取消 = 覆盖已有扫描数据');
  var mode = merge ? 'merge' : 'replace';
  setStatus('status-data-transfer', '正在导入扫描数据(' + (mode === 'merge' ? '增量更新' : '覆盖导入') + ')...', false);
  var data = await postJson('/api/settings/import/scan-data', {mode: mode, payload: payload});
  var parts = [];
  if(data.mode === 'replace') parts.push('已清空 ' + Number(data.replaced || 0) + ' 条旧数据');
  parts.push('新增 ' + Number(data.added || 0));
  parts.push('更新 ' + Number(data.updated || 0));
  parts.push('跳过 ' + Number(data.skipped || 0));
  parts.push('当前共 ' + Number(data.count || 0) + ' 条');
  setStatus('status-data-transfer', '扫描数据导入完成: ' + parts.join('，'), false);
  showNotice('扫描数据导入完成。', 'ok', 3200);
}
async function getJson(url){
  const r = await fetch(apiUrl(url), {cache:'no-store', headers:pageHeaders()});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
async function postJson(url, body){
  const r = await fetch(apiUrl(url), {method:'POST', headers:pageHeaders({'Content-Type':'application/json'}), body:JSON.stringify(body||{})});
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
function closeElevate(value){
  var modal = qs('elevate-modal');
  var pass = qs('elevate-pass');
  var resolver = elevateResolve;
  elevateResolve = null;
  if(pass) pass.value = '';
  if(modal) modal.classList.remove('show');
  if(resolver) resolver(value);
}
function requestElevationPassword(message){
  if(lastSystemServiceStatus && lastSystemServiceStatus.running_as_root) return Promise.resolve('');
  return new Promise(function(resolve){
    elevateResolve = resolve;
    if(qs('elevate-copy')) qs('elevate-copy').textContent = String(message || '此操作需要 root 权限；sudo 密码只用于本次请求，不会保存。');
    if(qs('elevate-status')) setStatus('elevate-status', '密码不会写入配置文件或浏览器存储。', false);
    if(qs('elevate-modal')) qs('elevate-modal').classList.add('show');
    window.setTimeout(function(){ if(qs('elevate-pass')) qs('elevate-pass').focus(); }, 40);
  });
}
async function privilegedBody(base, message){
  var body = Object.assign({}, base || {});
  if(lastSystemServiceStatus && lastSystemServiceStatus.running_as_root) return body;
  var pwd = await requestElevationPassword(message);
  if(pwd == null) throw new Error('已取消提权');
  body.sudo_password = String(pwd || '');
  return body;
}
function v(id){ return String((qs(id) && qs(id).value) || '').trim(); }
function n(id){ var x = v(id); if(!x) return null; var f = Number(x); return isFinite(f) ? f : null; }
function check(id){ return !!(qs(id) && qs(id).checked); }
function cloneJson(obj){ return JSON.parse(JSON.stringify(obj == null ? null : obj)); }
function sameJson(a, b){ return JSON.stringify(a == null ? null : a) === JSON.stringify(b == null ? null : b); }
function loadTheme(){
  try{ var s = localStorage.getItem('rid_ui_theme'); if(s === 'dark' || s === 'light') return s; }catch(_e){}
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
function loadBrowserPrefs(){
  var newFw = qs('pref-new-firmware-parser');
  cookieDelete(COOKIE_TRACK_REALTIME);
  cookieDelete(COOKIE_TRACK_2H_ONLY);
  if(newFw){
    try{ newFw.checked = localStorage.getItem(NEW_FIRMWARE_PARSE_KEY) !== '0'; }
    catch(_e){ newFw.checked = true; }
  }
}
function saveBrowserPrefs(){
  var newFw = qs('pref-new-firmware-parser');
  cookieDelete(COOKIE_TRACK_REALTIME);
  cookieDelete(COOKIE_TRACK_2H_ONLY);
  if(newFw){
    try{ localStorage.setItem(NEW_FIRMWARE_PARSE_KEY, newFw.checked ? '1' : '0'); }catch(_e){}
  }
  showNotice('页面偏好已保存到当前浏览器。', 'ok', 2200);
}
function renderEulaState(eula){
  eula = eula || {};
  var status = qs('status-eula');
  var revokeBtn = qs('btn-eula-revoke');
  if(status){
    status.textContent = (eula.accepted ? '当前已同意许可协议。' : '当前未同意许可协议。')
      + '\\n状态文件: ' + String(eula.set_path || 'EULA.set')
      + '\\n官方文本: ' + String(eula.source_url || '');
    status.classList.toggle('err', !eula.accepted);
  }
  if(revokeBtn) revokeBtn.disabled = !eula.accepted;
}
async function revokeEulaAcceptance(){
  if(!confirm('撤回同意后，系统会立即回到许可协议确认页。确定撤回？')) return;
  var btn = qs('btn-eula-revoke');
  if(btn) btn.disabled = true;
  setStatus('status-eula', '正在撤回许可协议同意状态...', false);
  try{
    const data = await postJson('/api/eula/revoke', {});
    setStatus('status-eula', '已撤回同意。即将跳转到 EULA 页面。\\n状态文件: ' + String(data.set_path || ''), true);
    showNotice('已撤回 EULA 同意状态。', 'warn', 2600);
    window.setTimeout(function(){ location.href = '/eula?next=/settings'; }, 700);
  }catch(e){
    setStatus('status-eula', '撤回失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 3600);
    if(btn) btn.disabled = false;
  }
}
async function ensureTabLoaded(tab){
  if(tab === 'raw' && !settingsState.rawLoaded){
    await loadRaw();
    settingsState.rawLoaded = true;
  }
}
function activateTab(tab){
  qsa('.tab').forEach(function(btn){ btn.classList.toggle('active', btn.getAttribute('data-tab')===tab); });
  qsa('.panel').forEach(function(p){ p.classList.toggle('active', p.getAttribute('data-tab')===tab); });
  ensureTabLoaded(tab).catch(function(e){
    if(tab === 'raw') setStatus('status-raw', e.message || e, true);
  });
}
function applyTabs(){
  qsa('.tab').forEach(function(btn){
    btn.addEventListener('click', function(){
      activateTab(btn.getAttribute('data-tab') || 'visual');
    });
  });
}
function fmtPct(v){
  return (v == null || !isFinite(v)) ? '—' : (Number(v).toFixed(1) + '%');
}
function fmtMb(used, total){
  if(used == null || total == null || !isFinite(used) || !isFinite(total)) return '—';
  return String(used) + ' / ' + String(total) + ' MB';
}
function fmtSecShort(sec){
  sec = Number(sec);
  if(!isFinite(sec) || sec < 0) return '—';
  if(sec < 60) return Math.round(sec) + 's';
  if(sec < 3600) return Math.round(sec / 60) + 'm';
  if(sec < 86400) return Math.round(sec / 3600) + 'h';
  return Math.round(sec / 86400) + 'd';
}
function checkedAuthLoginMethods(){
  var out = [];
  if(check('cfg-auth-method-password')) out.push('password');
  if(check('cfg-auth-method-passkey')) out.push('passkey');
  return out;
}
function ensureAuthLoginMethodSelection(preferredId, noisy){
  var methods = checkedAuthLoginMethods();
  if(methods.length) return methods;
  var fallbackId = preferredId || 'cfg-auth-method-password';
  if(qs(fallbackId)) qs(fallbackId).checked = true;
  methods = checkedAuthLoginMethods();
  if(noisy){
    if(qs('auth-method-state')) qs('auth-method-state').textContent = '至少保留一种网页登录方式；账号密码仍用于设置页二次确认。';
    showNotice('至少保留一种网页登录方式。', 'warn', 2400);
  }
  return methods;
}
function syncAuthMethodUi(){
  var methods = ensureAuthLoginMethodSelection('', false);
  var authEnabled = check('cfg-auth-enabled');
  var authConfigured = !!settingsState.authConfigured;
  var allowPassword = methods.indexOf('password') >= 0;
  var allowPasskey = methods.indexOf('passkey') >= 0;
  if(qs('auth-method-state')){
    var labels = [];
    if(allowPassword) labels.push('账号密码');
    if(allowPasskey) labels.push('PassKey');
    qs('auth-method-state').textContent = '当前允许: ' + (labels.join(' / ') || '未选择') + '。至少保留一种网页登录方式；账号密码仍用于设置页二次确认和 PassKey 注册。';
  }
  if(qs('passkey-state')){
    if(!authEnabled || !authConfigured){
      qs('passkey-state').textContent = '完成网页登录账号和密码配置后，可在这里登记通行密钥。';
    }else if(!allowPasskey){
      qs('passkey-state').textContent = '当前已关闭 PassKey 登录；已登记密钥会保留，但不会生效。';
    }else{
      qs('passkey-state').textContent = '通行密钥可以直接用于网页登录。';
    }
  }
  if(qs('login-link-state')){
    if(!authEnabled || !authConfigured){
      qs('login-link-state').textContent = '网页登录账号密码完整后即可生成 SSO 链接。SSO 不在登录方式开关中关闭。';
    }else{
      qs('login-link-state').textContent = 'SSO 链接已作为最高优先级验证入口；命中有效链接时会先于密码和 PassKey 会话处理。';
    }
  }
  if(qs('btn-login-link-create')) qs('btn-login-link-create').disabled = !(authEnabled && authConfigured);
  if(qs('btn-passkey-add')) qs('btn-passkey-add').disabled = !(authEnabled && authConfigured && allowPasskey);
}
function renderHostStats(host, basic){
  var root = qs('host-stats');
  if(!root) return;
  host = host || {};
  basic = basic || {};
  var sniff = host.sniff_state || {};
  var sniffLabel = sniff.state === 'ok' ? '正常' : (sniff.state === 'warn' ? '等待数据' : (sniff.state === 'error' ? '异常' : '—'));
  var localIps = (Array.isArray(host.local_ips) && host.local_ips.length) ? host.local_ips.map(function(ip){
    ip = String(ip || '');
    return '<div class="ip-line"><span class="ip-text" title="'+enc(ip)+'">'+enc(ip)+'</span><span class="ip-len">'+ip.length+'</span></div>';
  }).join('') : '—';
  var items = [
    ['主机', host.hostname || '—'],
    ['本机 IP', localIps, 'ip-lines'],
    ['CPU', fmtPct(host.cpu_percent)],
    ['内存', fmtPct(host.mem_percent)],
    ['内存容量', fmtMb(host.mem_used_mb, host.mem_total_mb)],
    ['温度', host.temperature_c == null ? '—' : (Number(host.temperature_c).toFixed(1) + '°C')],
    ['当前网卡', host.active_iface || basic.iface || '未绑定'],
    ['当前信道', String(host.current_channel || basic.channel_effective || 6)]
  ];
  root.innerHTML = items.map(function(row){
    var cls = row[2] ? ('v ' + row[2]) : 'v';
    var val = row[2] ? String(row[1]) : enc(row[1]);
    return '<div class="stat"><div class="k">'+enc(row[0])+'</div><div class="'+cls+'">'+val+'</div></div>';
  }).join('');
  var meta = [];
  if(host.cpu_count) meta.push('核心 ' + String(host.cpu_count));
  if(Array.isArray(host.ifaces) && host.ifaces.length) meta.push('网卡 ' + host.ifaces.map(function(x){ return String(x.name || ''); }).filter(Boolean).join(', '));
  if(host.load1 != null) meta.push('负载 ' + String(host.load1) + '/' + String(host.load5) + '/' + String(host.load15));
  if(host.uptime_sec != null) meta.push('运行 ' + fmtSecShort(host.uptime_sec));
  if(host.temperature_source_label) meta.push('温度源 ' + String(host.temperature_source_label));
  if(sniff.state) meta.push('采集 ' + sniffLabel);
  if(sniff.msg) meta.push(String(sniff.msg));
  qs('host-meta').textContent = meta.length ? meta.join(' | ') : '-';
}
function renderSystemServiceStatus(data){
  data = data || {};
  lastSystemServiceStatus = data;
  var iw = data.iw || {};
  var wirelessToolsMissing = !iw.available || !iw.hostapd_available;
  var sec = data.security || {};
  var lines = [];
  if(data.supported){
    if(data.registered && data.unit_matches === false) lines.push('当前服务文件与本页生成的启动参数不一致，可点击注册/更新服务。');
    if(data.running_as_root) lines.push('安全告警: 当前网页服务处于 root 权限，建议一键修复为 rid 专用账号运行。');
    if(data.registered && !data.service_uses_dedicated_user) lines.push('安全告警: 当前服务文件未声明 rid 专用账号。');
  }else{
    lines.push('systemd: 不可用' + (data.reason ? ('，' + String(data.reason)) : ''));
    if(data.manual_hint) lines.push(String(data.manual_hint));
  }
  if(iw.message && wirelessToolsMissing) lines.push(String(iw.message));
  if(iw.manual_hint && wirelessToolsMissing) lines.push(String(iw.manual_hint));
  if(data.last_error) lines.push('状态读取错误: ' + String(data.last_error));
  var securityWarn = !!(data.running_as_root || (data.registered && !data.service_uses_dedicated_user) || !data.dedicated_user_exists);
  setStatus('status-system-service', lines.join('\\n') || '-', wirelessToolsMissing || (!!data.supported && securityWarn));
  renderRuntimeSecurityAlert(data, sec);
  var regBtn = qs('btn-service-register');
  if(regBtn) regBtn.disabled = !data.supported || !data.can_elevate || !data.dedicated_user_exists;
  var iwBtn = qs('btn-iw-install');
  if(iwBtn) iwBtn.disabled = (!!iw.available && !!iw.hostapd_available) || !iw.can_install;
  var repairBtn = qs('btn-security-repair');
  if(repairBtn) repairBtn.disabled = !data.supported || !data.can_elevate;
}
function renderRuntimeSecurityAlert(data, sec){
  var box = qs('runtime-security-alert');
  if(!box) return;
  data = data || {};
  sec = sec || data.security || {};
  var runningRoot = !!(data.running_as_root || sec.running_as_root);
  var serviceOk = !!data.service_uses_dedicated_user && !!data.dedicated_user_exists;
  box.classList.add('show');
  box.classList.toggle('warn', runningRoot || !serviceOk);
  box.classList.toggle('ok', !runningRoot && serviceOk);
  if(qs('runtime-security-title')){
    qs('runtime-security-title').textContent = runningRoot ? '当前处于 root 权限' : (serviceOk ? '运行权限正常' : '专用账号未完成');
  }
    if(qs('runtime-security-copy')){
    if(runningRoot){
      qs('runtime-security-copy').textContent = '当前网页服务和采集进程以 root 运行，存在安全风险。点击一键修复会创建/确认 rid 账号，并把 systemd 服务改为 rid 账号加网络能力运行。';
    }else if(sec && sec.risk === 'missing-capabilities'){
      qs('runtime-security-copy').textContent = '当前进程不是 root，但没有检测到采集所需网络能力。请执行一键修复，让 systemd 以 rid 账号和网络能力启动服务。';
    }else if(!serviceOk){
      qs('runtime-security-copy').textContent = '当前进程不是 root，但 systemd 服务还没有确认使用 rid 专用账号。需要 root 或临时 sudo 提权完成修复。';
    }else{
      qs('runtime-security-copy').textContent = '当前服务目标为 rid 专用账号，采集所需网络能力通过 systemd capability 提供。';
    }
  }
}
async function loadSystemServiceStatus(){
  const data = await getJson('/api/settings/systemd/status');
  renderSystemServiceStatus(data);
  return data;
}
async function registerSystemdServiceFromSettings(){
  if(!confirm('将写入 /etc/systemd/system/light-rid-scanner.service 并启用开机自启。继续？')) return;
  var btn = qs('btn-service-register');
  try{
    if(btn) btn.disabled = true;
    setStatus('status-system-service', '正在注册 systemd 服务...', false);
    const body = await privilegedBody({confirm:true}, '注册/更新 systemd 服务需要 root 权限。请输入 sudo 密码；密码只用于本次请求，不会保存。');
    const data = await postJson('/api/settings/systemd/register', body);
    renderSystemServiceStatus((data && data.status) || {});
    showNotice(data.message || 'systemd 服务已注册。', 'ok', 3600);
  }catch(e){
    setStatus('status-system-service', '注册失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 4200);
  }finally{
    await loadSystemServiceStatus().catch(function(){});
  }
}
async function installIwFromSettings(){
  if(!confirm('将执行 apt-get update，并安装 iw 与 hostapd。继续？')) return;
  var btn = qs('btn-iw-install');
  try{
    if(btn) btn.disabled = true;
    setStatus('status-system-service', '正在安装无线工具...', false);
    const body = await privilegedBody({confirm:true}, '安装 iw 和 hostapd 需要 root 权限；密码只用于本次操作。');
    const data = await postJson('/api/settings/iw/install', body);
    if(data.status) renderSystemServiceStatus(data.status);
    showNotice(data.message || '无线工具安装完成。', 'ok', 3600);
  }catch(e){
    setStatus('status-system-service', '无线工具安装失败: ' + (e.message || e) + '\\n请手动执行: sudo apt-get update && sudo apt-get install -y iw hostapd', true);
    showNotice(e.message || e, 'warn', 4600);
  }finally{
    await loadSystemServiceStatus().catch(function(){});
  }
}
function refreshSystemServiceAfterRestart(delaySec){
  var delayMs = Math.max(5000, Number(delaySec || 3) * 1000 + 4000);
  var attempts = 0;
  function tick(){
    attempts += 1;
    loadSystemServiceStatus().then(function(){
      setStatus('status-system-service', '服务已自动重启，运行状态已刷新。', false);
      showNotice('服务已自动重启，当前状态已刷新。', 'ok', 3600);
    }).catch(function(){
      if(attempts < 8){
        setTimeout(tick, 2000);
      }else{
        setStatus('status-system-service', '服务正在重启。如果状态没有恢复，请稍后手动刷新页面。', true);
        showNotice('服务正在重启。如果页面未恢复，请稍后手动刷新。', 'warn', 5200);
      }
    });
  }
  setTimeout(tick, delayMs);
}
async function repairRuntimeSecurityFromSettings(){
  if(!confirm('将创建/确认 rid 专用账号、授予配置与缓存写权限，把 systemd 服务改为 rid 账号运行，并在完成后自动重启服务。继续？')) return;
  var btn = qs('btn-security-repair');
  var restartScheduled = false;
  var restartDelay = 3;
  try{
    if(btn) btn.disabled = true;
    setStatus('status-system-service', '正在修复运行权限...', false);
    const body = await privilegedBody({confirm:true}, '一键修复需要 root 权限。请输入 sudo 密码；密码只用于创建账号、授权文件和写入 systemd 服务，本系统不会保存。');
    const data = await postJson('/api/settings/security/repair', body);
    restartScheduled = !!(data && data.restart_scheduled);
    restartDelay = Number((data && data.restart_delay_sec) || restartDelay);
    renderSystemServiceStatus((data && data.status) || {});
    if(restartScheduled){
      setStatus('status-system-service', '修复完成，服务将在几秒后自动重启；页面可能短暂断开。', false);
      showNotice(data.message || '运行权限已修复，服务即将自动重启。', 'ok', 8200);
      refreshSystemServiceAfterRestart(restartDelay);
    }else{
      showNotice(data.message || '运行权限已修复。', 'ok', 5200);
    }
  }catch(e){
    setStatus('status-system-service', '修复失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 5200);
  }finally{
    if(!restartScheduled){
      await loadSystemServiceStatus().catch(function(){});
    }
  }
}
function renderSettingsRuntime(data){
  data = data || {};
  var apRoot = qs('settings-ap-list');
  if(apRoot){
    var aps = Array.isArray(data.aps) ? data.aps.slice(0, 40) : [];
    if(!aps.length){
      apRoot.innerHTML = '<div class="empty-state">暂无 AP 数据</div>';
    }else{
      apRoot.innerHTML = '<div class="settings-ap-scroll">' + aps.map(function(a, idx){
        var mac = String(a.mac || '-');
        var ssid = String(a.ssid || '(hidden)');
        var vendor = String(a.vendor || '未知');
        var rssi = (a.rssi == null) ? 'N/A' : (String(a.rssi) + 'dBm');
        return '<div class="list-row"><div class="settings-ap-row-grid">'
          + '<div class="micro">#'+(idx+1)+'</div>'
          + '<div class="clip" title="'+enc(ssid)+'"><b>'+enc(ssid)+'</b><div class="micro clip" title="'+enc(vendor)+'">'+enc(vendor)+'</div></div>'
          + '<div class="micro clip" title="'+enc(mac)+'">'+enc(mac)+'</div>'
          + '<div>'+enc(rssi)+'</div>'
          + '</div></div>';
      }).join('') + '</div>';
    }
  }
  var log = qs('settings-runtime-log');
  if(log){
    var lines = [];
    if(Array.isArray(data.ap_logs) && data.ap_logs.length) lines = lines.concat(['[AP]'], data.ap_logs);
    if(Array.isArray(data.event_logs) && data.event_logs.length) lines = lines.concat(['', '[EVENT]'], data.event_logs);
    if(Array.isArray(data.scan_logs) && data.scan_logs.length) lines = lines.concat(['', '[SCAN]'], data.scan_logs);
    log.value = lines.join('\\n');
  }
  setStatus('status-runtime', 'AP ' + String((data.aps || []).length || 0) + '/' + String(data.aps_total || 0), false);
  if(data.metrics && Array.isArray(data.metrics.items)){
    metricsState.items = data.metrics.items;
    drawMetricsChart();
  }
}
async function loadRuntimePanel(){
  const data = await getJson('/api/settings/runtime?limit=220');
  renderSettingsRuntime(data);
}
function metricWindowSec(){
  if(metricsState.window === '7d') return 7 * 86400;
  if(metricsState.window === '24h') return 24 * 3600;
  return 12 * 3600;
}
function fmtMetricTime(ts){
  var d = new Date(Number(ts || 0) * 1000);
  if(!isFinite(d.getTime())) return '-';
  return d.toLocaleString();
}
function metricNumber(v){
  var n = Number(v);
  return isFinite(n) ? n : null;
}
function metricRowsSorted(){
  var arr = Array.isArray(metricsState.items) ? metricsState.items.slice() : [];
  arr.sort(function(a,b){ return Number(a.ts||0) - Number(b.ts||0); });
  return arr;
}
function metricZoomFactor(){
  var z = Math.max(1, Math.min(100, Number(metricsState.zoom || 1)));
  return Math.pow(24, (z - 1) / 99);
}
function metricCurrentRange(rows){
  var arr = Array.isArray(rows) ? rows : metricRowsSorted();
  var base = metricWindowSec();
  var span = Math.max(1800, base / metricZoomFactor());
  var latest = arr.length ? Number(arr[arr.length - 1].ts || (Date.now()/1000)) : (Date.now()/1000);
  var first = arr.length ? Number(arr[0].ts || latest) : (latest - base);
  var maxPan = Math.max(0, latest - first - span);
  metricsState.panSec = Math.max(0, Math.min(maxPan, Number(metricsState.panSec || 0)));
  var end = latest - Number(metricsState.panSec || 0);
  var start = end - span;
  return {start:start, end:end, span:span, latest:latest, first:first, maxPan:maxPan};
}
function metricVisibleItems(){
  var arr = metricRowsSorted();
  if(!arr.length) return [];
  var range = metricCurrentRange(arr);
  return arr.filter(function(x){ return Number(x.ts || 0) >= range.start && Number(x.ts || 0) <= range.end; });
}
function metricDefs(rows){
  var apMax = (Array.isArray(rows) ? rows : []).reduce(function(m, x){ return Math.max(m, Number(x.ap || 0)); }, 1);
  return [
    {key:'cpu', label:'CPU', color:'#2899f5', fmt:function(v){ return fmtPct(v); }, axis:function(v){ return Math.round(v) + '%'; }, max:100},
    {key:'mem', label:'内存', color:'#92c353', fmt:function(v){ return fmtPct(v); }, axis:function(v){ return Math.round(v) + '%'; }, max:100},
    {key:'temp', label:'温度', color:'#f7630c', fmt:function(v){ return v == null ? '—' : Number(v).toFixed(1) + '°C'; }, axis:function(v){ return Math.round(v) + '°'; }, max:100},
    {key:'load', label:'负载', color:'#c19c00', fmt:function(v){ return fmtPct(v); }, axis:function(v){ return Math.round(v) + '%'; }, max:100},
    {key:'ap', label:'AP数', color:'#8764b8', fmt:function(v){ return v == null ? '—' : String(Math.round(Number(v))); }, axis:function(v){ return String(Math.round(v)); }, max:Math.max(1, apMax)}
  ];
}
function metricTooltipFor(canvas, key){
  var wrap = canvas ? canvas.parentElement : null;
  if(!wrap) return null;
  var tip = wrap.querySelector('.metric-chart-tip');
  if(!tip){
    tip = document.createElement('div');
    tip.className = 'metric-chart-tip';
    tip.setAttribute('data-metric', key || '');
    wrap.appendChild(tip);
  }
  return tip;
}
function metricNearestPoint(rows, key, ts){
  var best = null, bestDiff = Infinity;
  (Array.isArray(rows) ? rows : []).forEach(function(p){
    var value = metricNumber(p && p[key]);
    if(value == null) return;
    var pt = Number(p.ts || 0);
    var diff = Math.abs(pt - ts);
    if(diff < bestDiff){
      bestDiff = diff;
      best = {row:p, ts:pt, value:value};
    }
  });
  return best;
}
function metricSyncZoomControl(){
  var z = Math.max(1, Math.min(100, Number(metricsState.zoom || 1)));
  metricsState.zoom = z;
  var input = qs('metrics-zoom');
  var label = qs('metrics-zoom-value');
  if(input) input.value = String(z);
  if(label) label.textContent = (Math.round(metricZoomFactor() * 10) / 10) + 'x';
}
function metricSetZoom(nextZoom, focusRatio){
  var rows = metricRowsSorted();
  var before = metricCurrentRange(rows);
  var ratio = Math.max(0, Math.min(1, Number(focusRatio == null ? 0.5 : focusRatio)));
  var focusTs = before.start + before.span * ratio;
  metricsState.zoom = Math.max(1, Math.min(100, Number(nextZoom || 1)));
  var span = Math.max(1800, metricWindowSec() / metricZoomFactor());
  var end = focusTs + (1 - ratio) * span;
  metricsState.panSec = before.latest - end;
  metricCurrentRange(rows);
  metricSyncZoomControl();
  drawMetricsChart();
}
function metricPanByPixels(canvas, dx){
  var key = canvas && canvas.getAttribute('data-metric');
  var meta = key ? metricsState.chartMeta[key] : null;
  if(!meta || !meta.range) return;
  var plotW = Math.max(1, meta.width - meta.pad.l - meta.pad.r);
  metricsState.panSec = Number(metricsState.panSec || 0) + (Number(dx || 0) / plotW) * meta.range.span;
  metricCurrentRange(metricRowsSorted());
  drawMetricsChart();
}
function metricPointerRatio(canvas, ev){
  var rect = canvas.getBoundingClientRect();
  if(!rect.width) return 0.5;
  return Math.max(0, Math.min(1, (Number(ev.clientX || 0) - rect.left) / rect.width));
}
function metricUpdateHoverFromEvent(canvas, ev){
  if(!canvas) return;
  metricsState.hover = {key:canvas.getAttribute('data-metric') || '', ratio:metricPointerRatio(canvas, ev)};
  drawMetricsChart();
}
function metricClearHover(){
  metricsState.hover = null;
  drawMetricsChart();
}
function metricBindCanvasEvents(canvas){
  if(!canvas || canvas.__metricBound) return;
  canvas.__metricBound = true;
  canvas.addEventListener('wheel', function(ev){
    ev.preventDefault();
    var step = ev.deltaY < 0 ? 6 : -6;
    metricSetZoom(Number(metricsState.zoom || 1) + step, metricPointerRatio(canvas, ev));
  }, {passive:false});
  canvas.addEventListener('pointerdown', function(ev){
    if(ev.button != null && ev.button !== 0) return;
    metricsState.drag = {key:canvas.getAttribute('data-metric') || '', lastX:Number(ev.clientX || 0), moved:false};
    var wrap = canvas.parentElement;
    if(wrap) wrap.classList.add('dragging');
    try{ canvas.setPointerCapture(ev.pointerId); }catch(_e){}
    ev.preventDefault();
  });
  canvas.addEventListener('pointermove', function(ev){
    if(metricsState.drag && metricsState.drag.key === (canvas.getAttribute('data-metric') || '')){
      var x = Number(ev.clientX || 0);
      var dx = x - Number(metricsState.drag.lastX || x);
      if(Math.abs(dx) >= 1){
        metricsState.drag.lastX = x;
        metricsState.drag.moved = true;
        metricPanByPixels(canvas, dx);
      }
      ev.preventDefault();
      return;
    }
    metricUpdateHoverFromEvent(canvas, ev);
  });
  function endDrag(ev){
    var wasDrag = metricsState.drag && metricsState.drag.key === (canvas.getAttribute('data-metric') || '');
    metricsState.drag = null;
    var wrap = canvas.parentElement;
    if(wrap) wrap.classList.remove('dragging');
    try{ canvas.releasePointerCapture(ev.pointerId); }catch(_e){}
    if(wasDrag) metricUpdateHoverFromEvent(canvas, ev);
  }
  canvas.addEventListener('pointerup', endDrag);
  canvas.addEventListener('pointercancel', endDrag);
  canvas.addEventListener('pointerleave', function(){
    if(metricsState.drag) return;
    metricClearHover();
  });
  canvas.addEventListener('dblclick', function(){
    metricsState.zoom = 1;
    metricsState.panSec = 0;
    metricSyncZoomControl();
    metricClearHover();
  });
}
function drawMetricsChart(){
  var allRows = metricRowsSorted();
  var range = metricCurrentRange(allRows);
  var rows = allRows.filter(function(x){ return Number(x.ts || 0) >= range.start && Number(x.ts || 0) <= range.end; });
  var defs = metricDefs(rows);
  metricsState.chartMeta = {};
  defs.forEach(function(def){ drawMetricSpark(def, rows, range); });
  var last = rows[rows.length - 1] || {};
  var status = qs('status-metrics');
  if(status){
    var panText = Number(metricsState.panSec || 0) > 1 ? (' | 视图偏移 ' + Math.round(Number(metricsState.panSec || 0) / 60) + ' 分钟') : '';
    status.textContent = rows.length ? ('样本 ' + rows.length
      + ' | 最新 CPU ' + fmtPct(last.cpu)
      + ' / 内存 ' + fmtPct(last.mem)
      + ' / 温度 ' + (last.temp == null ? '—' : Number(last.temp).toFixed(1) + '°C')
      + ' / AP ' + String(last.ap == null ? '—' : last.ap)
      + ' | 视图 ' + (Math.round(metricZoomFactor() * 10) / 10) + 'x' + panText) : '暂无负载数据';
  }
}
function drawMetricSpark(def, rows, range){
  var canvas = document.querySelector('.metric-spark[data-metric="'+def.key+'"]');
  var valueEl = qs('metric-value-' + def.key);
  var tip = canvas ? metricTooltipFor(canvas, def.key) : null;
  if(!canvas) return;
  var box = canvas.getBoundingClientRect();
  var dpr = window.devicePixelRatio || 1;
  var cssW = Math.max(260, box.width || (canvas.parentElement ? canvas.parentElement.clientWidth : 0) || 300);
  var cssH = Math.max(110, box.height || (canvas.parentElement ? canvas.parentElement.clientHeight : 0) || 136);
  var w = Math.round(cssW * dpr);
  var h = Math.round(cssH * dpr);
  if(canvas.width !== w) canvas.width = w;
  if(canvas.height !== h) canvas.height = h;
  var ctx = canvas.getContext('2d');
  ctx.clearRect(0,0,w,h);
  var styles = getComputedStyle(document.body);
  var border = (styles.getPropertyValue('--border') || '#444').trim();
  var muted = (styles.getPropertyValue('--muted') || '#888').trim();
  var txt = (styles.getPropertyValue('--txt') || '#fff').trim();
  var pad = {l:42, r:12, t:10, b:24};
  var padPx = {l:pad.l*dpr, r:pad.r*dpr, t:pad.t*dpr, b:pad.b*dpr};
  var plotW = Math.max(1, w - padPx.l - padPx.r);
  var plotH = Math.max(1, h - padPx.t - padPx.b);
  var start = range ? Number(range.start || 0) : 0;
  var end = range ? Number(range.end || (start + 1)) : 1;
  if(end <= start) end = start + 1;
  metricsState.chartMeta[def.key] = {width:cssW, height:cssH, pad:pad, range:{start:start,end:end,span:end-start}, rows:rows, def:def};
  if(tip) tip.style.display = 'none';
  ctx.strokeStyle = border;
  ctx.lineWidth = 1 * dpr;
  ctx.font = String(10 * dpr) + 'px sans-serif';
  ctx.fillStyle = muted;
  ctx.textBaseline = 'middle';
  ctx.beginPath();
  for(var gi=0;gi<=4;gi++){
    var gy = padPx.t + plotH * gi / 4;
    ctx.moveTo(padPx.l, gy); ctx.lineTo(w - padPx.r, gy);
    var gv = Math.max(0, Number(def.max || 100)) * (1 - gi / 4);
    ctx.fillText(def.axis ? def.axis(gv) : String(Math.round(gv)), 4 * dpr, gy);
  }
  for(var vi=0;vi<=4;vi++){
    var gx = padPx.l + plotW * vi / 4;
    ctx.moveTo(gx, padPx.t); ctx.lineTo(gx, h - padPx.b);
  }
  ctx.stroke();
  if(!rows.length){
    if(valueEl) valueEl.textContent = '—';
    ctx.fillStyle = muted;
    ctx.font = String(12 * dpr) + 'px sans-serif';
    ctx.fillText('暂无数据', padPx.l + 4 * dpr, h / 2);
    return;
  }
  function rawValue(p){ return metricNumber(p[def.key]); }
  var lastVal = null;
  for(var li=rows.length-1;li>=0;li--){
    lastVal = rawValue(rows[li]);
    if(lastVal != null) break;
  }
  if(valueEl) valueEl.textContent = def.fmt(lastVal);
  function xFor(ts){ return padPx.l + ((Number(ts || start) - start) / (end - start)) * plotW; }
  function yFor(v){
    var maxV = Math.max(1, Number(def.max || 100));
    var n = Math.max(0, Math.min(maxV, Number(v || 0)));
    return padPx.t + (1 - (n / maxV)) * plotH;
  }
  var drawn = false;
  var firstPt = null, lastPt = null;
  ctx.beginPath();
  rows.forEach(function(p){
    var raw = rawValue(p);
    if(raw == null) return;
    var x = xFor(p.ts), y = yFor(raw);
    if(!drawn){ ctx.moveTo(x,y); firstPt = {x:x,y:y}; drawn = true; }
    else ctx.lineTo(x,y);
    lastPt = {x:x,y:y};
  });
  if(drawn){
    ctx.save();
    ctx.lineTo(lastPt.x, h - padPx.b);
    ctx.lineTo(firstPt.x, h - padPx.b);
    ctx.closePath();
    ctx.globalAlpha = 0.14;
    ctx.fillStyle = def.color;
    ctx.fill();
    ctx.restore();
    ctx.beginPath();
    drawn = false;
    rows.forEach(function(p){
      var raw = rawValue(p);
      if(raw == null) return;
      var x = xFor(p.ts), y = yFor(raw);
      if(!drawn){ ctx.moveTo(x,y); drawn = true; }
      else ctx.lineTo(x,y);
    });
    ctx.strokeStyle = def.color;
    ctx.lineWidth = 2 * dpr;
    ctx.stroke();
  }
  ctx.fillStyle = muted;
  ctx.textBaseline = 'alphabetic';
  ctx.font = String(10 * dpr) + 'px sans-serif';
  ctx.fillText(fmtMetricTime(start).replace(/^[0-9]{4}[/]/,''), padPx.l, h - 6 * dpr);
  var endLabel = fmtMetricTime(end).replace(/^[0-9]{4}[/]/,'');
  var endW = ctx.measureText(endLabel).width;
  ctx.fillText(endLabel, Math.max(padPx.l, w - padPx.r - endW), h - 6 * dpr);
  if(metricsState.hover && metricsState.hover.key === def.key){
    var ratio = Math.max(0, Math.min(1, Number(metricsState.hover.ratio || 0)));
    var targetTs = start + (end - start) * ratio;
    var hit = metricNearestPoint(rows, def.key, targetTs);
    if(hit){
      var hx = xFor(hit.ts), hy = yFor(hit.value);
      ctx.save();
      ctx.setLineDash([4 * dpr, 4 * dpr]);
      ctx.strokeStyle = txt;
      ctx.globalAlpha = 0.48;
      ctx.lineWidth = 1 * dpr;
      ctx.beginPath();
      ctx.moveTo(hx, padPx.t);
      ctx.lineTo(hx, h - padPx.b);
      ctx.moveTo(padPx.l, hy);
      ctx.lineTo(w - padPx.r, hy);
      ctx.stroke();
      ctx.restore();
      ctx.beginPath();
      ctx.arc(hx, hy, 4 * dpr, 0, Math.PI * 2);
      ctx.fillStyle = def.color;
      ctx.fill();
      ctx.lineWidth = 2 * dpr;
      ctx.strokeStyle = txt;
      ctx.stroke();
      if(tip){
        var cssX = hx / dpr, cssY = hy / dpr;
        tip.classList.toggle('below', cssY < 52);
        tip.style.left = Math.max(74, Math.min(cssW - 74, cssX)) + 'px';
        tip.style.top = Math.max(18, Math.min(cssH - 18, cssY)) + 'px';
        tip.textContent = def.label + '  ' + def.fmt(hit.value) + '\\n' + fmtMetricTime(hit.ts);
        tip.style.display = 'block';
      }
    }
  }
}
async function loadMetrics(){
  if(!check('cfg-metrics-enabled')){
    metricsState.items = [];
    drawMetricsChart();
    if(qs('status-metrics')) qs('status-metrics').textContent = '节点负载记录已关闭；开启并保存后开始采样。';
    return;
  }
  const data = await getJson('/api/settings/metrics?window=' + encodeURIComponent(metricsState.window || '12h'));
  metricsState.items = Array.isArray(data.items) ? data.items : [];
  if(data.enabled === false){
    metricsState.items = [];
    drawMetricsChart();
    if(qs('status-metrics')) qs('status-metrics').textContent = '节点负载记录已关闭；开启并保存后开始采样。';
    return;
  }
  if(qs('status-metrics') && data.store_path){
    qs('status-metrics').textContent = '数据文件: ' + String(data.store_path);
  }
  drawMetricsChart();
}
function setMetricWindow(win){
  metricsState.window = (win === '7d' || win === '24h') ? win : '12h';
  metricsState.panSec = 0;
  metricsState.hover = null;
  qsa('.metric-window').forEach(function(btn){ btn.classList.toggle('active', btn.getAttribute('data-window') === metricsState.window); });
  loadMetrics().catch(function(e){ if(qs('status-metrics')) qs('status-metrics').textContent = e.message || String(e); });
}
async function updateModelsNow(){
  var btn = qs('btn-model-update-now');
  try{
    if(btn) btn.disabled = true;
    if(qs('model-update-state')) qs('model-update-state').textContent = '正在更新识别库...';
    const data = await postJson('/api/settings/models/update', {url: v('cfg-model-update-url')});
    if(qs('model-update-state')) qs('model-update-state').textContent = data.message || '识别库已更新。';
    showNotice(data.message || '识别库已更新。', 'ok', 3000);
    await loadVisual();
  }catch(e){
    if(qs('model-update-state')) qs('model-update-state').textContent = '更新失败: ' + (e.message || e);
    showNotice(e.message || e, 'warn', 4200);
  }finally{
    if(btn) btn.disabled = false;
  }
}
function renderAppUpdateState(state){
  var el = qs('app-update-state');
  if(!el) return;
  state = state || {};
  var current = state.current_short || (state.current_commit ? String(state.current_commit).slice(0, 12) : '');
  var latest = state.latest_short || (state.latest_commit ? String(state.latest_commit).slice(0, 12) : '');
  var lines = ['当前 commit: ' + (current || '未知')];
  lines.push('最新 commit: ' + (latest || '尚未检查'));
  if(state.running) lines.push('正在检查版本...');
  else if(state.last_error) lines.push('检查失败: ' + String(state.last_error));
  else if(state.checked) lines.push(state.update_available ? '发现新版本，更新需手动处理。' : '当前已是检查到的最新版本。');
  else lines.push('自动/手动检查只比较版本，不会自动更新程序。');
  el.textContent = lines.join(' | ');
}
async function checkAppVersionNow(){
  var btn = qs('btn-app-update-check');
  try{
    if(btn) btn.disabled = true;
    renderAppUpdateState({running:true});
    const data = await postJson('/api/settings/app-update/check', {});
    renderAppUpdateState((data && data.state) || {});
    showNotice(data && data.state && data.state.update_available ? '发现新版本，请手动更新。' : '版本检查完成。', 'ok', 3000);
  }catch(e){
    showNotice(e.message || e, 'warn', 4200);
  }finally{
    if(btn) btn.disabled = false;
  }
}
function cleanModelPrefix(prefix){
  return String(prefix == null ? '' : prefix).toUpperCase().replace(/[^0-9A-Z]/g, '').slice(0, 32);
}
function syncModelRowsFromInputs(){
  qsa('#model-map-list .model-map-row').forEach(function(row){
    var idx = Number(row.getAttribute('data-index'));
    if(!isFinite(idx) || !modelMapRows[idx]) return;
    var p = row.querySelector('.model-prefix');
    var m = row.querySelector('.model-name');
    modelMapRows[idx].prefix = cleanModelPrefix(p ? p.value : '');
    modelMapRows[idx].model = String((m && m.value) || '').trim();
    if(p) p.value = modelMapRows[idx].prefix;
  });
}
function filteredModelRows(){
  var q = String((qs('model-map-search') && qs('model-map-search').value) || '').trim().toLowerCase();
  return modelMapRows.map(function(row, idx){
    return {idx:idx, prefix:String(row.prefix || ''), model:String(row.model || '')};
  }).filter(function(row){
    if(!q) return true;
    return row.prefix.toLowerCase().indexOf(q) >= 0 || row.model.toLowerCase().indexOf(q) >= 0;
  });
}
function renderModelMapRows(){
  var root = qs('model-map-list');
  if(!root) return;
  var rows = filteredModelRows();
  if(!rows.length){
    root.innerHTML = '<div class="model-map-empty">暂无匹配条目。</div>';
  }else{
    root.innerHTML = rows.map(function(row){
      return '<div class="model-map-row" data-index="'+row.idx+'">'
        + '<input class="model-prefix" value="'+enc(row.prefix)+'" maxlength="32" spellcheck="false" placeholder="前缀">'
        + '<input class="model-name" value="'+enc(row.model)+'" spellcheck="false" placeholder="机型名称">'
        + '<button class="btn warn model-row-delete" type="button">删除</button>'
        + '</div>';
    }).join('');
  }
  var state = qs('model-map-editor-state');
  if(state){
    var suffix = modelMapPath ? (' | ' + modelMapPath) : '';
    state.textContent = '当前 ' + String(modelMapRows.length) + ' 条，保存后会立即刷新实时与历史机型。' + suffix;
  }
}
function collectModelMapRows(){
  syncModelRowsFromInputs();
  var seen = {};
  var out = [];
  modelMapRows.forEach(function(row){
    var prefix = cleanModelPrefix(row && row.prefix);
    var model = String((row && row.model) || '').trim();
    if(!prefix && !model) return;
    if(!prefix || !model) return;
    seen[prefix] = model;
  });
  Object.keys(seen).sort().forEach(function(prefix){
    out.push({prefix:prefix, model:seen[prefix]});
  });
  return out;
}
function addModelMapRow(prefix, model){
  syncModelRowsFromInputs();
  modelMapRows.unshift({prefix:cleanModelPrefix(prefix), model:String(model || '').trim()});
  if(qs('model-map-search')) qs('model-map-search').value = '';
  renderModelMapRows();
  var first = document.querySelector('#model-map-list .model-map-row input');
  if(first) first.focus();
}
async function loadModelEditor(){
  const data = await getJson('/api/settings/models/list');
  modelMapRows = (Array.isArray(data.items) ? data.items : []).map(function(row){
    return {prefix:cleanModelPrefix(row && row.prefix), model:String((row && row.model) || '').trim()};
  });
  modelMapPath = String(data.path || '');
  renderModelMapRows();
  if(data.warning && qs('model-map-editor-state')){
    qs('model-map-editor-state').textContent = String(data.warning);
  }
}
async function saveModelEditor(){
  var btn = qs('btn-model-map-save');
  try{
    if(btn) btn.disabled = true;
    var items = collectModelMapRows();
    const data = await postJson('/api/settings/models/save', {items:items});
    modelMapRows = (Array.isArray(data.items) ? data.items : items).map(function(row){
      return {prefix:cleanModelPrefix(row && row.prefix), model:String((row && row.model) || '').trim()};
    });
    modelMapPath = String(data.path || modelMapPath || '');
    renderModelMapRows();
    if(qs('model-update-state') && data.state){
      qs('model-update-state').textContent = '已加载 ' + String((data.state && data.state.loaded_count) || modelMapRows.length) + ' 条';
    }
    showNotice(data.message || '识别库已保存。', 'ok', 2600);
  }catch(e){
    showNotice(e.message || e, 'warn', 4200);
    if(qs('model-map-editor-state')) qs('model-map-editor-state').textContent = '保存失败: ' + (e.message || e);
  }finally{
    if(btn) btn.disabled = false;
  }
}
function collectVisualPayload(){
  return {
    basic: {
      iface: v('cfg-iface') || null,
      channel: settingsState.channelUseDefault ? null : n('cfg-channel'),
      channel_use_default: !!settingsState.channelUseDefault,
      time: n('cfg-time'),
      min_gap: n('cfg-min-gap'),
      lost_timeout: n('cfg-lost-timeout'),
      rssi_delta: n('cfg-rssi-delta'),
      model_map: v('cfg-model-map'),
      history_file: v('cfg-history-file'),
      auto_self_heal: check('cfg-heal'),
      change_on_rssi: check('cfg-rssi-change'),
      change_on_payload: check('cfg-payload-change'),
      debug: check('cfg-debug'),
      dwell_2g: n('cfg-dwell2g'),
      dwell_5g: n('cfg-dwell5g'),
      settle: n('cfg-settle'),
      dwell_on_hit: n('cfg-hit-dwell'),
      hit_cap: n('cfg-hit-cap'),
      hop: check('cfg-hop'),
      hop_5g: check('cfg-hop5g'),
      scan_wifi_fast: check('cfg-fast'),
      no_tui: true
    },
    web: {
      dji_lookup_url: v('cfg-dji-url'),
      base_name: v('cfg-base-name'),
      base_lat: n('cfg-base-lat'),
      base_lon: n('cfg-base-lon'),
      base_zoom: n('cfg-base-zoom'),
      heading_ref_deg: n('cfg-heading-ref'),
      map_auto_center_idle_sec: n('cfg-map-idle'),
      access_list_enabled: check('cfg-web-access-enabled'),
      access_list_mode: v('cfg-web-access-mode') || 'allow',
      access_list: splitLines(qs('cfg-web-access-list').value || ''),
      alarm_zones: collectZoneRows()
    },
    notify: {
      enabled: check('cfg-notify-enabled'),
      notify_reonline: check('cfg-notify-reonline'),
      reonline_cooldown_sec: n('cfg-reonline'),
      send_timeout_sec: n('cfg-send-timeout'),
      wecom_webhooks: collectHookRows()
    },
    api: {
      enabled: check('cfg-api-enabled'),
      whitelist_enabled: check('cfg-api-whitelist-enabled'),
      whitelist_mode: v('cfg-api-whitelist-mode') || 'allow',
      whitelist: splitLines(qs('cfg-api-whitelist').value || '')
    },
    auth: {
      enabled: check('cfg-auth-enabled'),
      realm: v('cfg-auth-realm'),
      session_ttl_min: n('cfg-auth-ttl'),
      login_methods: ensureAuthLoginMethodSelection('', false),
      username: v('cfg-auth-user') || '__KEEP__',
      password: String((qs('cfg-auth-pass') && qs('cfg-auth-pass').value) || '').trim() || '__KEEP__'
    },
    model_update: {
      enabled: check('cfg-model-update-enabled'),
      url: v('cfg-model-update-url')
    },
    app_update: {
      enabled: check('cfg-app-update-enabled')
    },
    metrics: {
      enabled: check('cfg-metrics-enabled'),
      retention_days: n('cfg-metrics-retention'),
      temperature_source: v('cfg-metrics-temp-source') || 'auto'
    },
    network_bindings: collectNetworkBindings()
  };
}
function visualPayloadSections(payload){
  payload = payload || {};
  return {
    capture: Object.assign({}, payload.basic || {}, {model_update: payload.model_update || {}, app_update: payload.app_update || {}, network_bindings: payload.network_bindings || {}}),
    map: {
      dji_lookup_url: ((payload.web || {}).dji_lookup_url),
      base_name: ((payload.web || {}).base_name),
      base_lat: ((payload.web || {}).base_lat),
      base_lon: ((payload.web || {}).base_lon),
      base_zoom: ((payload.web || {}).base_zoom),
      heading_ref_deg: ((payload.web || {}).heading_ref_deg),
      map_auto_center_idle_sec: ((payload.web || {}).map_auto_center_idle_sec)
    },
    zones: {alarm_zones: ((payload.web || {}).alarm_zones || [])},
    access: {
      web_access: {
        access_list_enabled: ((payload.web || {}).access_list_enabled),
        access_list_mode: ((payload.web || {}).access_list_mode),
        access_list: ((payload.web || {}).access_list || [])
      },
      notify: payload.notify || {},
      api: payload.api || {},
      auth: payload.auth || {}
    },
    metrics: payload.metrics || {}
  };
}
function setDraftUi(dirtyMap){
  dirtyMap = dirtyMap || {};
  settingsState.dirtyCards = dirtyMap;
  settingsState.visualDirty = Object.keys(dirtyMap).some(function(k){ return !!dirtyMap[k]; });
  qsa('.card[data-card-key]').forEach(function(card){
    var key = card.getAttribute('data-card-key') || '';
    card.classList.toggle('dirty', !!dirtyMap[key]);
  });
  if(qs('btn-test-visual')) qs('btn-test-visual').disabled = !settingsState.visualDirty;
  if(qs('btn-save-visual')) qs('btn-save-visual').disabled = !settingsState.visualDirty;
  if(qs('btn-save-visual-direct')) qs('btn-save-visual-direct').disabled = false;
  if(qs('draft-title')) qs('draft-title').textContent = settingsState.visualDirty ? '有未保存修改' : '当前没有未保存修改';
  if(qs('draft-meta')){
    var names = SETTINGS_DRAFT_SECTIONS
      .filter(function(item){ return !!dirtyMap[item.key]; })
      .map(function(item){ return item.label; });
    qs('draft-meta').textContent = settingsState.visualDirty
      ? ('已改动: ' + names.join('、') + '。测试结果独立于保存动作。')
      : '未保存改动按配置分组标记；测试结果独立于配置文件。';
  }
}
function updateVisualDraftState(){
  if(!settingsState.visualLoaded || !settingsState.visualInitial) return;
  var current = collectVisualPayload();
  var initialSections = visualPayloadSections(settingsState.visualInitial);
  var currentSections = visualPayloadSections(current);
  setDraftUi({
    capture: !sameJson(initialSections.capture, currentSections.capture),
    map: !sameJson(initialSections.map, currentSections.map),
    zones: !sameJson(initialSections.zones, currentSections.zones),
    access: !sameJson(initialSections.access, currentSections.access),
    metrics: !sameJson(initialSections.metrics, currentSections.metrics)
  });
}
function resetVisualDraftState(){
  settingsState.visualInitial = cloneJson(collectVisualPayload());
  setDraftUi({});
}
function bindVisualDraftTracking(){
  var root = document.querySelector('.panel[data-tab="visual"]');
  if(!root || root.getAttribute('data-dirty-bind') === '1') return;
  root.setAttribute('data-dirty-bind', '1');
  root.addEventListener('input', function(ev){
    updateVisualDraftState();
  });
  root.addEventListener('change', function(){
    updateVisualDraftState();
  });
}
function setVisualActionBusy(busy){
  ['btn-test-visual','btn-save-visual','btn-save-visual-direct','btn-reload-view'].forEach(function(id){
    var el = qs(id);
    if(!el) return;
    if(id === 'btn-test-visual' || id === 'btn-save-visual'){
      el.disabled = !!busy || (!settingsState.visualDirty);
    }else if(id === 'btn-save-visual-direct'){
      el.disabled = !!busy;
    }else{
      el.disabled = !!busy;
    }
  });
}
function setChannelUi(editing){
  settingsState.channelEditing = !!editing;
  var input = qs('cfg-channel');
  var editBtn = qs('btn-channel-edit');
  var resetBtn = qs('btn-channel-reset');
  var hint = qs('channel-hint');
  if(input) input.disabled = !editing;
  if(editBtn) editBtn.textContent = editing ? '锁定' : '编辑';
  if(resetBtn) resetBtn.style.display = settingsState.channelUseDefault ? 'none' : '';
  if(hint){
    hint.textContent = '';
    hint.style.display = 'none';
  }
}
function openReauth(action){
  reauthAction = action;
  qs('reauth-user').value = '';
  qs('reauth-pass').value = '';
  setStatus('reauth-status', '二次验证使用网页登录账号和密码。', false);
  qs('reauth-modal').classList.add('show');
  window.setTimeout(function(){ try{ qs('reauth-user').focus(); }catch(_e){} }, 30);
}
function closeReauth(){
  reauthAction = null;
  qs('reauth-modal').classList.remove('show');
}
function showOneTimeSecret(title, secret, note){
  oneTimeSecretValue = String(secret || '');
  qs('one-time-title').textContent = String(title || '只显示一次');
  qs('one-time-note').textContent = String(note || '关闭后不能再次查看或复制。');
  qs('one-time-secret').textContent = oneTimeSecretValue;
  qs('one-time-modal').classList.add('show');
}
function closeOneTimeSecret(){
  oneTimeSecretValue = '';
  qs('one-time-secret').textContent = '';
  qs('one-time-modal').classList.remove('show');
}
function b64uToBytes(text){
  var raw = String(text || '').replace(/-/g,'+').replace(/_/g,'/');
  while(raw.length % 4) raw += '=';
  if(!raw) return new Uint8Array(0);
  var bin = atob(raw);
  var out = new Uint8Array(bin.length);
  for(var i=0;i<bin.length;i++) out[i] = bin.charCodeAt(i);
  return out;
}
function bytesToB64u(bytes){
  var view = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes || []);
  var bin = '';
  for(var i=0;i<view.length;i++) bin += String.fromCharCode(view[i]);
  return btoa(bin).replace(/\\+/g,'-').replace(/\\//g,'_').replace(/=+$/,'');
}
function formatBytes(size){
  var n = Number(size);
  if(!isFinite(n) || n < 0) return '-';
  if(n < 1024) return String(n) + ' B';
  if(n < 1024 * 1024) return (n / 1024).toFixed(1).replace(/\\.0$/, '') + ' KB';
  if(n < 1024 * 1024 * 1024) return (n / (1024 * 1024)).toFixed(1).replace(/\\.0$/, '') + ' MB';
  return (n / (1024 * 1024 * 1024)).toFixed(1).replace(/\\.0$/, '') + ' GB';
}
function formatMtime(ts){
  var d = new Date(Number(ts || 0) * 1000);
  return isFinite(d.getTime()) ? d.toLocaleString() : '-';
}
function rawPathLabel(path){
  var raw = String(path || '');
  if(!raw) return '-';
  return raw;
}
function rawActivePath(){
  return String(settingsState.rawSelectedPath || '');
}
function rawDirContainsSelected(node, selectedPath){
  var selected = String(selectedPath || '');
  if(!selected || !node) return false;
  var base = String(node.path || '');
  if(base && selected.indexOf(base + '\\\\') === 0) return true;
  if(base && selected.indexOf(base + '/') === 0) return true;
  var children = Array.isArray(node.children) ? node.children : [];
  for(var i=0;i<children.length;i++){
    var child = children[i] || {};
    if(child.type === 'file' && String(child.path || '') === selected) return true;
    if(child.type === 'dir' && rawDirContainsSelected(child, selected)) return true;
  }
  return false;
}
function rawSetMeta(data){
  data = data || {};
  if(qs('raw-tree-path')) qs('raw-tree-path').textContent = String(data.root || settingsState.rawRoot || '-');
  if(qs('raw-file-title')) qs('raw-file-title').textContent = String(data.name || ((data.rel_path && String(data.rel_path) !== '-') ? data.rel_path : '') || ((data.path && String(data.path) !== '-') ? data.path : '') || '未选择文件');
  if(qs('raw-file-path')) qs('raw-file-path').textContent = String(data.rel_path || data.path || '-');
  if(qs('raw-file-size')) qs('raw-file-size').textContent = data.size == null ? '-' : formatBytes(data.size);
  if(qs('raw-file-mtime')) qs('raw-file-mtime').textContent = data.mtime ? formatMtime(data.mtime) : '-';
}
function rawSetLocked(isLocked, message){
  var card = qs('raw-lock-card');
  var layout = qs('raw-layout');
  if(card) card.style.display = isLocked ? 'grid' : 'none';
  if(layout) layout.style.opacity = isLocked ? '0.55' : '1';
  var editor = qs('raw-editor');
  if(editor) editor.disabled = !!isLocked;
  ['btn-save-raw','btn-delete-raw','btn-load-raw'].forEach(function(id){
    var el = qs(id);
    if(el) el.disabled = !!isLocked && id !== 'btn-load-raw';
  });
  if(qs('raw-lock-copy') && message) qs('raw-lock-copy').textContent = String(message);
}
function rawRenderTreeNodes(nodes, selectedPath){
  var list = Array.isArray(nodes) ? nodes : [];
  if(!list.length) return '<div class="empty-state">暂无配置文件</div>';
  return list.map(function(node){
    node = node || {};
    var type = String(node.type || 'file');
    var name = enc(node.name || (type === 'dir' ? '目录' : '文件'));
    var rel = enc(node.rel_path || '');
    var path = enc(node.path || '');
    if(type === 'dir'){
      var openAttr = rawDirContainsSelected(node, selectedPath) ? ' open' : '';
      return '<details class="raw-dir"'+openAttr+'><summary title="'+rel+'">'+name+'</summary><div class="raw-dir-child">'+rawRenderTreeNodes(node.children || [], selectedPath)+'</div></details>';
    }
    var active = String(node.path || '') === String(selectedPath || '');
    return '<button class="raw-file-btn'+(active ? ' active' : '')+'" type="button" data-path="'+path+'" data-rel="'+rel+'"><span class="clip" title="'+path+'">'+name+'</span><span class="micro">'+enc(formatBytes(node.size))+'</span></button>';
  }).join('');
}
function rawRenderTree(data){
  data = data || {};
  settingsState.rawTree = data;
  settingsState.rawRoot = String(data.root || settingsState.rawRoot || '');
  if(qs('raw-tree')) qs('raw-tree').innerHTML = rawRenderTreeNodes(data.tree || [], rawActivePath());
  rawSetMeta({root:data.root || settingsState.rawRoot || '-', name:'未选择文件', rel_path:'', path:'', size:null, mtime:null});
}
function rawFirstFile(nodes){
  var list = Array.isArray(nodes) ? nodes : [];
  for(var i=0;i<list.length;i++){
    var item = list[i] || {};
    if(item.type === 'file' && item.path) return String(item.path);
    var child = rawFirstFile(item.children || []);
    if(child) return child;
  }
  return '';
}
function rawRefreshButtons(){
  var unlocked = !!settingsState.rawUnlocked;
  var hasPath = !!settingsState.rawSelectedPath;
  var treeReady = !!settingsState.rawTree;
  ['btn-save-raw','btn-delete-raw','btn-load-raw'].forEach(function(id){
    var el = qs(id);
    if(!el) return;
    if(id === 'btn-load-raw'){
      el.disabled = !unlocked;
    }else{
      el.disabled = !unlocked || !hasPath || !treeReady;
    }
  });
}
async function rawLoadFile(path){
  var filePath = String(path || settingsState.rawSelectedPath || '').trim();
  if(!filePath) throw new Error('请选择一个配置文件');
  const data = await getJson('/api/config/file?path=' + encodeURIComponent(filePath));
  settingsState.rawUnlocked = true;
  settingsState.rawLoaded = true;
  settingsState.rawSelectedPath = String(data.path || filePath);
  settingsState.rawSelectedRel = String(data.rel_path || '');
  rawRenderTree(settingsState.rawTree || data.tree || {});
  rawSetMeta(data);
  if(qs('raw-editor')) qs('raw-editor').value = String(data.text || '');
  rawSetLocked(false, '');
  rawRefreshButtons();
  setStatus('status-raw', '已读取: ' + String(data.rel_path || data.path || '-'), false);
  return data;
}
async function rawLoadTree(){
  const data = await getJson('/api/config/tree');
  settingsState.rawUnlocked = true;
  settingsState.rawRoot = String(data.root || '');
  settingsState.rawTree = data;
  rawRenderTree(data);
  rawSetLocked(false, '');
  rawRefreshButtons();
  return data;
}
async function loadRaw(){
  try{
    const treeData = await rawLoadTree();
    var target = String(settingsState.rawSelectedPath || '');
    if(!target){
      target = rawFirstFile(treeData.tree || []);
      settingsState.rawSelectedPath = target;
    }
    if(target){
      await rawLoadFile(target);
    }else{
      settingsState.rawLoaded = true;
      rawSetMeta({root: treeData.root || settingsState.rawRoot || '-', name:'未选择文件', rel_path:'-', path:'-', size:null, mtime:null});
      if(qs('raw-editor')) qs('raw-editor').value = '';
      rawRefreshButtons();
    }
  }catch(e){
    var msg = e && e.message ? e.message : String(e);
    if(msg.indexOf('unlock required') >= 0 || msg.indexOf('raw config unlock required') >= 0){
      settingsState.rawUnlocked = false;
      settingsState.rawLoaded = false;
      rawSetLocked(true, '需要先验证网页登录密码，才能查看和编辑配置文件。');
      rawRefreshButtons();
      openReauth('raw-unlock');
      setStatus('status-raw', msg, true);
      return;
    }
    throw e;
  }
}
async function saveRaw(){
  var selected = String(settingsState.rawSelectedPath || '').trim();
  if(!selected) throw new Error('请选择一个配置文件');
  const data = await postJson('/api/settings/raw/save', {path:selected, text:String(qs('raw-editor').value || '')});
  settingsState.rawTree = null;
  settingsState.rawLoaded = false;
  setStatus('status-raw', '保存成功: ' + String(data.saved_to || '-') + '\\n' + String(data.reload_msg || ''), false);
  showNotice('原始配置已保存', 'ok', 3200);
  await loadRaw().catch(function(){});
}
async function deleteRawFile(){
  var selected = String(settingsState.rawSelectedPath || '').trim();
  if(!selected) throw new Error('请选择一个配置文件');
  if(!confirm('确认删除以下文件？\\n' + selected)) return;
  const data = await postJson('/api/config/file/delete', {path:selected});
  settingsState.rawSelectedPath = '';
  settingsState.rawSelectedRel = '';
  settingsState.rawTree = null;
  setStatus('status-raw', '已删除: ' + String(data.deleted_path || '-') + '\\n' + String(data.backup_path || ''), false);
  showNotice('原始配置文件已删除', 'ok', 2600);
  await loadRaw().catch(function(){});
}
function renderPasskeyRows(items){
  var root = qs('passkey-list');
  if(!root) return;
  var arr = Array.isArray(items) ? items.slice() : [];
  if(!arr.length){
    root.innerHTML = '<div class="empty-state">暂无通行密钥</div>';
    return;
  }
  root.innerHTML = arr.map(function(item, idx){
    item = item || {};
    var id = String(item.id || '');
    var name = enc(item.name || ('通行密钥 ' + (idx + 1)));
    var created = item.created_ts ? formatMtime(item.created_ts) : '-';
    var used = item.last_used_ts ? formatMtime(item.last_used_ts) : '未使用';
    return '<div class="passkey-row" data-id="'+enc(id)+'">'
      + '<div class="passkey-meta"><div class="passkey-title">'+name+'</div>'
      + '<div class="passkey-sub">创建时间: '+enc(created)+' | 上次使用: '+enc(used)+'</div>'
      + '<div class="passkey-badges"><span class="passkey-badge">签名计数 '+enc(String(item.sign_count || 0))+'</span><span class="passkey-badge">'+(item.enabled === false ? '已停用' : '已启用')+'</span></div>'
      + '</div><button class="btn ghost warn passkey-delete" type="button">删除</button></div>';
  }).join('');
}
async function createPasskeyWithCreds(){
  if(!window.PublicKeyCredential || !navigator.credentials || !navigator.credentials.create){
    throw new Error('当前浏览器不支持通行密钥创建');
  }
  var user = String(qs('reauth-user').value || '').trim();
  var pass = String(qs('reauth-pass').value || '');
  if(!user || !pass) throw new Error('请输入网页登录账号和密码');
  var name = String((qs('cfg-passkey-name') && qs('cfg-passkey-name').value) || '').trim();
  const start = await postJson('/api/settings/passkey/start', {username:user, password:pass, name:name});
  if(!start.ok) throw new Error(start.error || '通行密钥创建失败');
  var pk = start.publicKey || {};
  var challenge = b64uToBytes(pk.challenge || start.challenge || start.challenge_token || '');
  var userId = b64uToBytes((pk.user && pk.user.id) || '');
  var createOptions = {
    publicKey: {
      challenge: challenge,
      rp: pk.rp || {name:start.realm || 'Light RID Scanner', id:start.rp_id || location.hostname},
      user: {
        id: userId,
        name: (pk.user && pk.user.name) || user,
        displayName: (pk.user && pk.user.displayName) || (name || user),
      },
      pubKeyCredParams: pk.pubKeyCredParams || [{type:'public-key', alg:-7}],
      timeout: pk.timeout || start.timeout_ms || 300000,
      attestation: pk.attestation || 'none',
      authenticatorSelection: pk.authenticatorSelection || {userVerification:'preferred', residentKey:'preferred'},
      excludeCredentials: (pk.excludeCredentials || []).map(function(item){
        return {type:'public-key', id:b64uToBytes(item.id || '')};
      }),
    }
  };
  var cred = await navigator.credentials.create(createOptions);
  if(!cred) throw new Error('未获取到通行密钥凭据');
  var response = cred.response || {};
  const finish = await postJson('/api/settings/passkey/finish', {
    challenge: start.challenge || start.challenge_token,
    id: cred.id || '',
    rawId: bytesToB64u(cred.rawId || new Uint8Array(0)),
    type: cred.type || 'public-key',
    response: {
      clientDataJSON: bytesToB64u(response.clientDataJSON || new Uint8Array(0)),
      attestationObject: bytesToB64u(response.attestationObject || new Uint8Array(0)),
      authenticatorData: bytesToB64u(response.authenticatorData || new Uint8Array(0)),
      signature: bytesToB64u(response.signature || new Uint8Array(0)),
      userHandle: response.userHandle ? bytesToB64u(response.userHandle) : '',
    },
    name: name,
    username: user,
    next: '/',
  });
  renderPasskeyRows(finish.passkeys || []);
  showNotice('通行密钥已添加', 'ok', 3200);
  if(qs('cfg-passkey-name')) qs('cfg-passkey-name').value = '';
  return finish;
}
async function deletePasskey(id){
  const data = await postJson('/api/settings/passkey/delete', {id:String(id || '')});
  renderPasskeyRows(data.passkeys || []);
  showNotice('通行密钥已删除', 'ok', 2600);
  return data;
}
function fmtSsoExpiry(item){
  item = item || {};
  var expiresAt = Number(item.expires_at || 0);
  if(!isFinite(expiresAt) || expiresAt <= 0) return '无限时间';
  var left = Math.max(0, expiresAt - Date.now() / 1000);
  if(left <= 0) return '已过期';
  if(left < 3600) return Math.max(1, Math.round(left / 60)) + ' 分钟';
  if(left < 86400) return Math.round(left / 3600) + ' 小时';
  return Math.round(left / 86400) + ' 天';
}
function renderLoginLinks(items){
  loginLinks = Array.isArray(items) ? items.slice() : [];
  var root = qs('login-link-list');
  if(!root) return;
  if(!loginLinks.length){
    root.innerHTML = '<div class="empty-state">暂无 SSO 登录链接。</div>';
    return;
  }
  root.innerHTML = loginLinks.map(function(item, idx){
    var name = enc(item.name || ('SSO 链接 ' + (idx + 1)));
    var check = enc(item.check || '');
    var status = String(item.status || (item.active === false ? 'expired' : 'active'));
    var stateLabel = enc(item.status_label || (status === 'active' ? '可用' : '不可用'));
    var expireLabel = enc(fmtSsoExpiry(item));
    var modeLabel = item.single_use ? '<span class="sso-link-badge">单次</span>' : '<span class="sso-link-badge">多次</span>';
    var bad = (status === 'active') ? '' : ' bad';
    return '<div class="list-row sso-link-row" data-check="'+check+'">'
      + '<div class="sso-link-meta"><div class="sso-link-title"><span>'+name+'</span>'
      + '<span class="sso-link-badge'+bad+'">'+stateLabel+'</span><span class="sso-link-badge">'+expireLabel+'</span>'+modeLabel+'</div>'
      + '<div class="micro">使用此链接可一键登录系统</div></div>'
      + '<button class="btn ghost warn login-link-row-delete" type="button">删除</button>'
      + '</div>';
  }).join('');
}
async function deleteLoginLink(check){
  const r = await fetch(apiUrl('/api/settings/login-link/delete'), {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify({check:String(check || '')})
  });
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP ' + r.status));
  renderLoginLinks(d.links || []);
  qs('login-link-state').textContent = '已删除校验码，对应 SSO 链接立即失效。';
  return d;
}
function collectLoginLinkOptions(){
  var mode = String((qs('login-link-expire-mode') && qs('login-link-expire-mode').value) || '86400');
  var body = {
    name: String(qs('login-link-name').value || '').trim(),
    next: '/',
    single_use: !!(qs('login-link-single-use') && qs('login-link-single-use').checked)
  };
  if(mode === 'never'){
    body.expires = 'never';
  }else if(mode === 'custom'){
    body.ttl_min = Math.max(1, Number((qs('login-link-ttl-min') && qs('login-link-ttl-min').value) || 1440));
  }else{
    body.ttl_sec = Math.max(60, Number(mode || 86400));
  }
  return body;
}
function setLoginLinkExpiryUi(){
  var mode = String((qs('login-link-expire-mode') && qs('login-link-expire-mode').value) || '86400');
  var custom = qs('login-link-ttl-min');
  var field = qs('login-link-custom-field');
  if(custom) custom.disabled = (mode !== 'custom');
  if(field) field.classList.toggle('hidden', mode !== 'custom');
}
async function createLoginLinkWithCreds(){
  var user = String(qs('reauth-user').value || '').trim();
  var pass = String(qs('reauth-pass').value || '');
  if(!user || !pass){
    setStatus('reauth-status', '账号和密码不完整。', true);
    return null;
  }
  var reqBody = collectLoginLinkOptions();
  reqBody.username = user;
  reqBody.password = pass;
  const r = await fetch(apiUrl('/api/settings/login-link/create'), {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify(reqBody)
  });
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false){
    throw new Error(d.error || ('HTTP ' + r.status));
  }
  var url = String(d.url || d.path || '');
  var expireText = d.expires_at ? ('有效期至 ' + fmtMetricTime(d.expires_at)) : '无限时间';
  qs('login-link-state').textContent = '校验码 ' + String(d.check || '-').slice(0, 10) + '... 已加入列表；' + expireText + (d.single_use ? '；单次登录。' : '。');
  renderLoginLinks(d.links || []);
  showOneTimeSecret('SSO 登录链接', url, '这个链接只在本次弹窗显示，关闭后只能删除记录再重新生成。');
  return d;
}
function fillIfaceOptions(items, selected){
  const sel = qs('cfg-iface');
  if(!sel) return;
  const opts = ['<option value="">未绑定</option>'];
  (Array.isArray(items)?items:[]).forEach(function(it){
    const name = String(it.name || '');
    if(!name) return;
    var kind = it.is_wireless ? ((it.mode ? String(it.mode) : 'wireless') + ' ' + (it.supports_5g ? '5G' : '2.4G')) : 'LAN';
    if(it.admin_up === false) kind += ' disabled';
    var model = it.model ? (' ' + String(it.model)) : '';
    opts.push('<option value="'+enc(name)+'">'+enc(name)+' ['+enc(kind + model)+']</option>');
  });
  sel.innerHTML = opts.join('');
  sel.value = selected || '';
}
function networkRoleOptions(selected){
  var roles = (settingsState.networkBindings && Array.isArray(settingsState.networkBindings.roles)) ? settingsState.networkBindings.roles : [
    {key:'none', label:'None'},
    {key:'scan', label:'扫描'},
    {key:'web', label:'网页服务'},
    {key:'ap_web', label:'AP热点网页服务'},
    {key:'disabled', label:'禁用'},
    {key:'idle', label:'闲置'}
  ];
  return roles.map(function(role){
    var key = String(role.key || 'none');
    return '<option value="'+enc(key)+'" '+(key===selected?'selected':'')+'>'+enc(role.label || key)+'</option>';
  }).join('');
}
function networkBindingRoleMap(){
  var out = {};
  var nb = settingsState.networkBindings || {};
  (Array.isArray(nb.items) ? nb.items : []).forEach(function(item){
    var iface = String((item && item.iface) || '');
    if(iface) out[iface] = String(item.role || 'none');
  });
  var selected = v('cfg-iface') || '';
  if(selected && !out[selected]) out[selected] = 'scan';
  return out;
}
function ensureNetworkUplinkControl(){
  if(qs('net-ap-uplink')) return qs('net-ap-uplink');
  var http = qs('net-ap-http');
  if(!http || !http.parentNode || !http.parentNode.parentNode) return null;
  var field = document.createElement('div');
  field.className = 'field';
  field.innerHTML = '<label>桥接出口</label><select id="net-ap-uplink"></select><div class="micro">选择可访问 Internet 的网卡，热点客户端将通过该网卡出网。</div>';
  http.parentNode.parentNode.appendChild(field);
  return qs('net-ap-uplink');
}
function fillNetworkUplinkOptions(ap){
  var sel = ensureNetworkUplinkControl();
  if(!sel) return;
  var current = String((ap && ap.uplink_iface) || '');
  var opts = ['<option value="">不共享 Internet</option>'];
  (Array.isArray(settingsState.interfaceItems) ? settingsState.interfaceItems : []).forEach(function(it){
    var name = String(it.name || '');
    if(!name) return;
    var kind = it.is_wireless ? '无线' : '有线';
    var ip = (Array.isArray(it.ipv4) && it.ipv4.length) ? (' | ' + it.ipv4.join(',')) : '';
    opts.push('<option value="'+enc(name)+'">'+enc(name + ' [' + kind + ip + ']')+'</option>');
  });
  sel.innerHTML = opts.join('');
  sel.value = current || '';
  sel.onchange = updateVisualDraftState;
}
function collectNetworkBindings(){
  var ap = (settingsState.networkBindings && settingsState.networkBindings.ap) ? Object.assign({}, settingsState.networkBindings.ap) : {};
  if(qs('net-ap-ssid')) ap.ssid = v('net-ap-ssid') || 'LightRID-HotSpot';
  if(qs('net-ap-password')) ap.password = v('net-ap-password');
  if(qs('net-ap-channel')) ap.channel = n('net-ap-channel') || 6;
  if(qs('net-ap-uplink')){
    ap.uplink_iface = v('net-ap-uplink');
    ap.internet_enabled = !!ap.uplink_iface;
  }
  ap.address = ap.address || '172.16.0.1';
  ap.cidr = ap.cidr || '172.16.0.1/24';
  ap.dhcp_start = ap.dhcp_start || '172.16.0.20';
  ap.dhcp_end = ap.dhcp_end || '172.16.0.240';
  ap.http_port = ap.http_port || 80;
  var rows = qsa('.network-bind-row');
  var items = rows.map(function(row){
    var iface = row.getAttribute('data-iface') || '';
    var roleSel = row.querySelector('.network-bind-role');
    return {iface:iface, role:String((roleSel && roleSel.value) || 'none')};
  }).filter(function(item){ return !!item.iface; });
  if(!items.length && settingsState.networkBindings && Array.isArray(settingsState.networkBindings.items)){
    items = settingsState.networkBindings.items.map(function(item){ return {iface:String(item.iface || ''), role:String(item.role || 'none')}; }).filter(function(item){ return !!item.iface; });
  }
  var selectedIface = v('cfg-iface') || '';
  if(selectedIface){
    var foundSelected = false;
    items.forEach(function(item){
      if(item.role === 'scan' && item.iface !== selectedIface) item.role = 'none';
      if(item.iface === selectedIface){ item.role = 'scan'; foundSelected = true; }
    });
    if(!foundSelected) items.push({iface:selectedIface, role:'scan'});
  }
  return {items:items, ap:ap};
}
function renderNetworkBindings(){
  var list = qs('network-bind-list');
  if(!list) return;
  var interfaces = Array.isArray(settingsState.interfaceItems) ? settingsState.interfaceItems : [];
  var roleMap = networkBindingRoleMap();
  var selected = v('cfg-iface') || '';
  if(!interfaces.length){
    list.innerHTML = '<div class="empty-state">未检测到网卡</div>';
  }else{
    list.innerHTML = interfaces.map(function(it){
      var name = String(it.name || '');
      var role = roleMap[name] || (name === selected ? 'scan' : String(it.detected_role || 'none'));
      var meta = [];
      if(it.model) meta.push('型号 ' + String(it.model));
      if(it.driver) meta.push('驱动 ' + String(it.driver));
      meta.push(it.is_wireless ? ('无线 ' + String(it.mode || '')) : '有线');
      if(it.admin_up === false) meta.push('已禁用');
      if(it.state) meta.push('状态 ' + String(it.state));
      if(Array.isArray(it.ipv4) && it.ipv4.length) meta.push(it.ipv4.join(', '));
      if(it.mac) meta.push(String(it.mac));
      return '<div class="list-row network-bind-row" data-iface="'+enc(name)+'">'
        + '<div class="model-map-row" style="grid-template-columns:minmax(120px,.35fr) minmax(0,1fr) minmax(180px,.35fr)">'
        + '<input value="'+enc(name)+'" disabled>'
        + '<input value="'+enc(meta.join(' | '))+'" disabled>'
        + '<select class="network-bind-role">'+networkRoleOptions(role)+'</select>'
        + '</div></div>';
    }).join('');
  }
  var ap = (settingsState.networkBindings && settingsState.networkBindings.ap) || {};
  if(qs('net-ap-ssid')) qs('net-ap-ssid').value = String(ap.ssid || 'LightRID-HotSpot');
  if(qs('net-ap-password')) qs('net-ap-password').value = String(ap.password || '');
  if(qs('net-ap-channel')) qs('net-ap-channel').value = String(ap.channel || 6);
  if(qs('net-ap-http')) qs('net-ap-http').value = String(ap.address || '172.16.0.1') + ':' + String(ap.http_port || 80);
  fillNetworkUplinkOptions(ap);
}
async function refreshNetworkBindings(){
  const data = await getJson('/api/network-bindings/status');
  settingsState.interfaceItems = Array.isArray(data.interfaces) ? data.interfaces : [];
  settingsState.networkBindings = data.bindings || settingsState.networkBindings || {items:[], ap:{}};
  fillIfaceOptions(settingsState.interfaceItems, data.selected_iface || v('cfg-iface'));
  renderNetworkBindings();
  setStatus('status-network-bind', '已扫描 ' + String(settingsState.interfaceItems.length) + ' 张网卡。', false);
  return data;
}
function openNetworkBindings(){
  if(qs('network-bind-modal')) qs('network-bind-modal').classList.add('show');
  renderNetworkBindings();
  refreshNetworkBindings().catch(function(e){ setStatus('status-network-bind', e.message || e, true); });
}
function closeNetworkBindings(){
  if(qs('network-bind-modal')) qs('network-bind-modal').classList.remove('show');
}
function saveNetworkBindingsToDraft(){
  var nb = collectNetworkBindings();
  var scan = (nb.items || []).filter(function(item){ return item.role === 'scan'; });
  if(scan.length > 1){
    setStatus('status-network-bind', '只能设置一张网卡为扫描。', true);
    return;
  }
  settingsState.networkBindings = Object.assign({}, settingsState.networkBindings || {}, nb);
  if(scan.length && qs('cfg-iface')) qs('cfg-iface').value = scan[0].iface;
  updateVisualDraftState();
  setStatus('status-network-bind', '网卡绑定已写入当前设置草稿，保存设置后生效。', false);
}
async function applyNetworkBindings(){
  if(settingsState.visualDirty){
    throw new Error('请先保存当前设置，再应用网卡绑定到系统。');
  }
  if(!confirm('将按已保存配置调整网卡状态、AP 地址、hostapd 和内置 DHCP。继续？')) return;
  const body = await privilegedBody({confirm:true}, '应用网卡绑定需要 root 权限；sudo 密码只用于本次请求，不会保存。');
  const data = await postJson('/api/network-bindings/apply', body);
  var lines = [];
  (Array.isArray(data.steps) ? data.steps : []).forEach(function(step){
    lines.push((step.ok ? 'OK ' : 'FAIL ') + String(step.label || '') + (step.output ? (' | ' + String(step.output)) : ''));
  });
  setStatus('status-network-bind', lines.join('\\n') || '已应用网卡绑定。', !data.ok);
  showNotice(data.ok ? '网卡绑定已应用。' : '部分网卡绑定步骤失败。', data.ok ? 'ok' : 'warn', 4200);
}
function renderHookRows(items){
  var root = qs('wecom-list');
  var arr = Array.isArray(items) ? items.slice() : [];
  if(!arr.length) arr = [{index:'', name:'默认通道', enabled:true, key_masked:''}];
  root.innerHTML = arr.map(function(item, idx){
    var index = (item.index == null) ? '' : String(item.index);
    var name = enc(item.name || ('通道 ' + (idx + 1)));
    var mask = enc(item.key_masked || '');
    return '<div class="list-row hook-row" data-index="'+enc(index)+'">'
      +'<div class="hook-layout">'
      +'<div class="field"><label>通道名称</label><input class="hook-name" type="text" value="'+name+'"></div>'
      +'<div class="field"><label>Key</label><input class="hook-key" type="password" value="" placeholder="'+(mask ? '留空即不修改' : '新的 Key')+'"></div>'
      +'<div class="field"><label>启用</label><input class="hook-enabled" type="checkbox" '+(item.enabled ? 'checked' : '')+'></div>'
      +'<div class="field"><label>&nbsp;</label><button class="btn ghost row-remove" type="button">移除</button></div>'
      +'</div></div>';
  }).join('');
}
function renderZoneRows(items){
  var root = qs('zone-list');
  var arr = Array.isArray(items) ? items.slice() : [];
  if(!arr.length){
    root.innerHTML = '<div class="empty-state">暂无报警区域</div>';
    return;
  }
  root.innerHTML = arr.map(function(item, idx){
    return '<div class="list-row zone-row">'
      +'<div class="zone-layout">'
      +'<div class="field"><label>区域名称</label><input class="zone-name" type="text" value="'+enc(item.name || ('报警区域 ' + (idx + 1)))+'"></div>'
      +'<div class="field"><label>启用</label><input class="zone-enabled" type="checkbox" '+(item.enabled ? 'checked' : '')+'></div>'
      +'<div class="field"><label>A 点纬度</label><input class="zone-lat1" type="number" step="0.000001" value="'+(item.lat1 == null ? '' : enc(item.lat1))+'"></div>'
      +'<div class="field"><label>A 点经度</label><input class="zone-lon1" type="number" step="0.000001" value="'+(item.lon1 == null ? '' : enc(item.lon1))+'"></div>'
      +'<div class="field"><label>B 点纬度</label><input class="zone-lat2" type="number" step="0.000001" value="'+(item.lat2 == null ? '' : enc(item.lat2))+'"></div>'
      +'<div class="field"><label>B 点经度</label><input class="zone-lon2" type="number" step="0.000001" value="'+(item.lon2 == null ? '' : enc(item.lon2))+'"></div>'
      +'<div class="field"><label>&nbsp;</label><button class="btn ghost row-remove" type="button">移除</button></div>'
      +'</div></div>';
  }).join('');
}
function collectHookRows(){
  return qsa('.hook-row').map(function(row){
    var keyInput = row.querySelector('.hook-key');
    var idx = row.getAttribute('data-index') || '';
    var rawKey = String((keyInput && keyInput.value) || '').trim();
    if(!rawKey && idx !== '') rawKey = '__KEEP__';
    if(!rawKey && idx === '') return null;
    return {
      index: (idx === '' ? null : Number(idx)),
      name: String((row.querySelector('.hook-name') || {}).value || '').trim() || '默认通道',
      enabled: !!((row.querySelector('.hook-enabled') || {}).checked),
      key: rawKey
    };
  }).filter(function(x){ return !!x; });
}
function collectZoneRows(){
  return qsa('.zone-row').map(function(row, idx){
    function rowVal(sel){ return String(((row.querySelector(sel) || {}).value) || '').trim(); }
    function rowNum(sel){ var s = rowVal(sel); if(!s) return null; var f = Number(s); return isFinite(f) ? f : null; }
    var name = rowVal('.zone-name') || ('报警区域 ' + (idx + 1));
    var zone = {
      name: name,
      enabled: !!((row.querySelector('.zone-enabled') || {}).checked),
      lat1: rowNum('.zone-lat1'),
      lon1: rowNum('.zone-lon1'),
      lat2: rowNum('.zone-lat2'),
      lon2: rowNum('.zone-lon2')
    };
    if(zone.lat1 == null && zone.lon1 == null && zone.lat2 == null && zone.lon2 == null && !zone.enabled){
      return null;
    }
    return zone;
  }).filter(function(x){ return !!x; });
}
function fmtApiTokenExpiry(item){
  return fmtSsoExpiry(item || {});
}
function renderApiTokenRows(items){
  var root = qs('api-token-list');
  if(!root) return;
  apiTokenRows = Array.isArray(items) ? items.slice() : [];
  if(!apiTokenRows.length){
    root.innerHTML = '<div class="empty-state">暂无 API Token。添加后才能启用外部 API。</div>';
    return;
  }
  root.innerHTML = apiTokenRows.map(function(item, idx){
    item = item || {};
    var id = String(item.id || '');
    var name = enc(item.name || ('API Token ' + (idx + 1)));
    var status = String(item.status || (item.active === false ? 'expired' : 'active'));
    var stateLabel = enc(item.status_label || (status === 'active' ? '可用' : '不可用'));
    var bad = (status === 'active' || status === 'new') ? '' : ' bad';
    return '<div class="api-token-row" data-id="'+enc(id)+'" data-status="'+enc(status)+'" data-status-label="'+stateLabel+'">'
      + '<div class="api-token-head">'
      + '<div class="api-token-name" title="'+name+'">'+name+'</div>'
      + '<div class="api-token-badges"><span class="api-token-badge'+bad+'">'+stateLabel+'</span><span class="api-token-badge">'+enc(fmtApiTokenExpiry(item))+'</span><span class="api-token-badge">'+(item.single_use ? '单次' : '多次')+'</span></div>'
      + '</div>'
      + '<div class="api-token-grid">'
      + '<div class="micro">Token 只在创建成功时显示一次，之后不能查看、复制或修改。</div>'
      + '<button class="btn ghost warn api-token-row-remove" type="button">删除</button>'
      + '</div>'
      + '</div>';
  }).join('');
}
function collectApiTokenCreateOptions(){
  var mode = String((qs('api-token-new-expire-mode') && qs('api-token-new-expire-mode').value) || '86400');
  var body = {
    name: String((qs('api-token-new-name') && qs('api-token-new-name').value) || '').trim(),
    single_use: !!(qs('api-token-new-single-use') && qs('api-token-new-single-use').checked)
  };
  if(mode === 'never') body.expires = 'never';
  else if(mode === 'custom') body.ttl_min = Math.max(1, Number((qs('api-token-new-ttl-min') && qs('api-token-new-ttl-min').value) || 1440));
  else body.ttl_sec = Math.max(60, Number(mode || 86400));
  return body;
}
function setApiTokenCreateExpiryUi(){
  var mode = String((qs('api-token-new-expire-mode') && qs('api-token-new-expire-mode').value) || '86400');
  var custom = qs('api-token-new-ttl-min');
  var field = qs('api-token-custom-field');
  if(custom) custom.disabled = (mode !== 'custom');
  if(field) field.classList.toggle('hidden', mode !== 'custom');
}
function updateApiWhitelistUi(effective){
  var block = qs('api-whitelist-block');
  var enabled = !!effective;
  if(block) block.classList.toggle('disabled-block', !enabled);
  ['cfg-api-whitelist-enabled','cfg-api-whitelist-mode','cfg-api-whitelist'].forEach(function(id){
    var el = qs(id);
    if(el) el.disabled = !enabled;
  });
}
async function createApiTokenWithCreds(){
  var user = String(qs('reauth-user').value || '').trim();
  var pass = String(qs('reauth-pass').value || '');
  if(!user || !pass){
    setStatus('reauth-status', '账号和密码不完整。', true);
    return null;
  }
  var reqBody = collectApiTokenCreateOptions();
  reqBody.username = user;
  reqBody.password = pass;
  const r = await fetch(apiUrl('/api/settings/api-token/create'), {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify(reqBody)
  });
  const d = await r.json().catch(()=>({}));
  if(authExpired(r, d)){ redirectLogin(); throw new Error('login required'); }
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP ' + r.status));
  renderApiTokenRows(d.tokens || []);
  updateApiWhitelistUi(true);
  showOneTimeSecret('API Token', String(d.token || ''), '这个 Token 只在本次弹窗显示，关闭后不能再次查看或复制。');
  if(qs('api-token-new-name')) qs('api-token-new-name').value = '';
  return d;
}
async function handleApiTokenListClick(ev){
  var row = ev.target && ev.target.closest ? ev.target.closest('.api-token-row') : null;
  if(!row) return;
  try{
    if(ev.target.closest('.api-token-row-remove')){
      var id = String(row.getAttribute('data-id') || '');
      if(!id) return;
      const d = await postJson('/api/settings/api-token/delete', {id:id});
      renderApiTokenRows(d.tokens || []);
      updateApiWhitelistUi(Array.isArray(d.tokens) && d.tokens.length > 0);
      showNotice('API Token 已删除。', 'ok', 2200);
      return;
    }
  }catch(e){
    showNotice(e.message || e, 'warn', 3600);
  }
}
function handleApiTokenListChange(_ev){}
function attachRowRemove(rootId, onEmptyFactory){
  var root = qs(rootId);
  if(!root) return;
  root.addEventListener('click', function(ev){
    var btn = ev.target && ev.target.closest ? ev.target.closest('.row-remove') : null;
    if(!btn) return;
    var row = btn.closest('.list-row');
    if(row && row.parentNode) row.parentNode.removeChild(row);
    if(!root.children.length && typeof onEmptyFactory === 'function') onEmptyFactory();
    updateVisualDraftState();
  });
}
async function useBrowserLocation(){
  if(!navigator.geolocation){ setStatus('status-visual', '当前浏览器不支持地理定位。', true); return; }
  if(!window.isSecureContext && !isLocalHostName(location.hostname || '')){
    setStatus('status-visual', '当前页面不是安全上下文，浏览器可能拒绝定位；HTTPS 或手动填写更稳定。', true);
  }
  navigator.geolocation.getCurrentPosition(function(pos){
    qs('cfg-base-lat').value = String(pos.coords.latitude || '');
    qs('cfg-base-lon').value = String(pos.coords.longitude || '');
    updateVisualDraftState();
    setStatus('status-visual', '已读取浏览器位置，等待测试或保存。', false);
  }, function(err){
    setStatus('status-visual', '定位失败: ' + (err && err.message ? err.message : err), true);
  }, {enableHighAccuracy:true, timeout:12000, maximumAge:0});
}
async function loadVisual(){
  const data = await getJson('/api/settings/view');
  const s = data.visual || {};
  const b = s.basic || {}, w = s.web || {}, nt = s.notify || {}, api = s.api || {}, auth = s.auth || {}, mu = s.model_update || {}, au = s.app_update || {}, mc = s.metrics || {};
  settingsState.interfaceItems = Array.isArray(data.interfaces) ? data.interfaces : [];
  settingsState.networkBindings = s.network_bindings || {items:[], ap:{}};
  fillIfaceOptions(settingsState.interfaceItems, b.iface || '');
  settingsState.visualLoaded = true;
  settingsState.channelUseDefault = !b.channel_custom;
  qs('cfg-channel').value = String(b.channel_effective == null ? 6 : b.channel_effective);
  setChannelUi(false);
  qs('cfg-time').value = String(b.time ?? '');
  qs('cfg-min-gap').value = String(b.min_gap ?? '');
  qs('cfg-lost-timeout').value = String(b.lost_timeout ?? 15);
  qs('cfg-rssi-delta').value = String(b.rssi_delta ?? '');
  qs('cfg-model-map').value = String(b.model_map || '');
  qs('cfg-model-update-enabled').checked = mu.enabled !== false;
  qs('cfg-app-update-enabled').checked = au.enabled !== false;
  qs('cfg-model-update-url').value = String(mu.url || '');
  renderAppUpdateState((au && au.state) || {});
  var must = (mu.state || {});
  qs('model-update-state').textContent = '已加载 ' + String(must.loaded_count || 0)
    + ' 条 | 上次成功 ' + (must.last_success_ts ? fmtMetricTime(must.last_success_ts) : '尚未成功')
    + (must.last_error ? (' | 最近错误: ' + String(must.last_error)) : '');
  qs('cfg-history-file').value = String(b.history_file || '');
  qs('cfg-heal').checked = !!b.auto_self_heal;
  qs('cfg-rssi-change').checked = !!b.change_on_rssi;
  qs('cfg-payload-change').checked = !!b.change_on_payload;
  qs('cfg-debug').checked = !!b.debug;
  qs('cfg-dwell2g').value = String(b.dwell_2g ?? '');
  qs('cfg-dwell5g').value = String(b.dwell_5g ?? '');
  qs('cfg-settle').value = String(b.settle ?? '');
  qs('cfg-hit-dwell').value = String(b.dwell_on_hit ?? '');
  qs('cfg-hit-cap').value = String(b.hit_cap ?? '');
  qs('cfg-hop').checked = !!b.hop;
  qs('cfg-hop5g').checked = !!b.hop_5g;
  qs('cfg-fast').checked = !!b.scan_wifi_fast;
  qs('cfg-base-name').value = String(w.base_name || '');
  qs('cfg-dji-url').value = String(w.dji_lookup_url || '');
  qs('cfg-base-lat').value = (w.base_lat == null) ? '' : String(w.base_lat);
  qs('cfg-base-lon').value = (w.base_lon == null) ? '' : String(w.base_lon);
  qs('cfg-base-zoom').value = String(w.base_zoom ?? '');
  qs('cfg-heading-ref').value = String(w.heading_ref_deg ?? '');
  qs('cfg-map-idle').value = String(w.map_auto_center_idle_sec ?? '');
  qs('cfg-web-access-enabled').checked = !!w.access_list_enabled;
  qs('cfg-web-access-mode').value = String(w.access_list_mode || 'allow');
  qs('cfg-web-access-list').value = Array.isArray(w.access_list) ? w.access_list.join('\\n') : '';
  renderZoneRows(Array.isArray(w.alarm_zones) ? w.alarm_zones : []);
  renderHostStats(data.host || {}, b);
  renderEulaState(data.eula || {});
  loadSystemServiceStatus().catch(function(e){ setStatus('status-system-service', e.message || e, true); });
  loadRuntimePanel().catch(function(){});
  loadMetrics().catch(function(){});
  qs('cfg-notify-enabled').checked = !!nt.enabled;
  qs('cfg-notify-reonline').checked = !!nt.notify_reonline;
  qs('cfg-reonline').value = String(nt.reonline_cooldown_sec ?? '');
  qs('cfg-send-timeout').value = String(nt.send_timeout_sec ?? '');
  renderHookRows(Array.isArray(nt.wecom_webhooks) ? nt.wecom_webhooks : []);
  qs('cfg-api-enabled').checked = !!api.enabled;
  renderApiTokenRows(Array.isArray(api.tokens) ? api.tokens : []);
  qs('cfg-api-whitelist-enabled').checked = !!api.whitelist_enabled;
  qs('cfg-api-whitelist-mode').value = String(api.whitelist_mode || 'allow');
  qs('cfg-api-whitelist').value = Array.isArray(api.whitelist) ? api.whitelist.join('\\n') : '';
  updateApiWhitelistUi(!!api.whitelist_effective);
  settingsState.authConfigured = !!auth.configured;
  qs('cfg-auth-enabled').checked = !!auth.enabled;
  qs('cfg-auth-method-password').checked = false;
  qs('cfg-auth-method-passkey').checked = false;
  (Array.isArray(auth.login_methods) && auth.login_methods.length ? auth.login_methods : ['password','passkey']).forEach(function(method){
    var id = method === 'password' ? 'cfg-auth-method-password' : (method === 'passkey' ? 'cfg-auth-method-passkey' : '');
    if(id && qs(id)) qs(id).checked = true;
  });
  qs('cfg-auth-user').value = '';
  qs('cfg-auth-user').placeholder = '留空即不修改';
  qs('cfg-auth-pass').value = '';
  qs('cfg-auth-pass').placeholder = '留空即不修改';
  qs('cfg-auth-realm').value = String(auth.realm || 'Light RID Scanner');
  qs('cfg-auth-ttl').value = String(auth.session_ttl_min || 30);
  if(qs('login-link-name')) qs('login-link-name').value = '';
  if(qs('login-link-expire-mode')) qs('login-link-expire-mode').value = '86400';
  if(qs('login-link-ttl-min')) qs('login-link-ttl-min').value = '1440';
  if(qs('login-link-single-use')) qs('login-link-single-use').checked = false;
  if(qs('api-token-new-expire-mode')) qs('api-token-new-expire-mode').value = '86400';
  if(qs('api-token-new-ttl-min')) qs('api-token-new-ttl-min').value = '1440';
  if(qs('api-token-new-single-use')) qs('api-token-new-single-use').checked = false;
  setLoginLinkExpiryUi();
  setApiTokenCreateExpiryUi();
  qs('btn-api-token-add').disabled = !(auth.enabled && auth.configured);
  renderLoginLinks(auth.sso_links || []);
  renderPasskeyRows(Array.isArray(auth.passkeys) ? auth.passkeys : []);
  if(qs('cfg-passkey-name')) qs('cfg-passkey-name').value = '';
  syncAuthMethodUi();
  if(qs('settings-config-path')) qs('settings-config-path').textContent = '设置文件: ' + String(data.path || '-');
  if(qs('settings-scan-data-path')) qs('settings-scan-data-path').textContent = '扫描数据文件: ' + String(b.history_file || '-');
  var rawAccess = data.raw_access || {};
  settingsState.rawUnlocked = !rawAccess.required || !!rawAccess.unlocked;
  settingsState.rawRoot = String(rawAccess.root || settingsState.rawRoot || '');
  settingsState.rawSelectedPath = String(data.path || settingsState.rawSelectedPath || '');
  rawSetLocked(!settingsState.rawUnlocked, settingsState.rawUnlocked ? '' : '需要先验证网页登录密码，才能查看和编辑配置文件。');
  rawRefreshButtons();
  qs('cfg-metrics-enabled').checked = !!mc.enabled;
  qs('cfg-metrics-retention').value = String(mc.retention_days || 7);
  qs('cfg-metrics-temp-source').value = String(mc.temperature_source || 'auto');
  var apiTokenCount = Array.isArray(api.tokens) ? api.tokens.length : 0;
  qs('secret-state').textContent = '通知通道 ' + String((nt.wecom_webhooks || []).length || 0)
    + ' | API Token ' + String(apiTokenCount) + ' 个'
    + ' | 外部 API ' + (api.enabled ? '开启' : '关闭')
    + ' | 登录 ' + (auth.enabled ? (auth.configured ? '开启' : '未完成') : '关闭');
  resetVisualDraftState();
  if(data.path) setStatus('status-visual', '配置文件: ' + data.path, false);
}
async function loadRawLegacyUnused(){
  return loadRaw();
}
async function saveVisual(){
  const payload = collectVisualPayload();
  const data = await postJson('/api/settings/visual/save', payload);
  var msg = '测试并保存成功: ' + String(data.saved_to || '-');
  if(data.backup_path) msg += '\\n备份: ' + String(data.backup_path);
  if(data.reload_msg) msg += '\\n' + String(data.reload_msg);
  setStatus('status-visual', msg, false);
  showNotice('配置已保存并生效。', 'ok', 3600);
  await loadVisual();
}
async function testVisual(){
  const payload = collectVisualPayload();
  const data = await postJson('/api/settings/visual/test', payload);
  var msg = '测试通过，运行配置已回滚。';
  if(data.reload_msg) msg += '\\n' + String(data.reload_msg);
  setStatus('status-visual', msg, false);
  showNotice('测试通过，当前运行配置已回滚。', 'ok', 3000);
}
async function saveRawLegacyUnused(){
  return saveRaw();
}
function bindShellActions(){
  on('btn-back', 'click', function(){ location.href='/'; });
  on('btn-logs', 'click', function(){ location.href='/logs'; });
  on('btn-logout', 'click', function(){ location.href='/logout'; });
  on('btn-theme', 'click', function(){ applyTheme(document.body.classList.contains('theme-light') ? 'dark' : 'light'); });
  on('btn-open-hw', 'click', function(){ location.href='/hardware-assistant'; });
  on('btn-diagnostic-export', 'click', async function(){
    var btn = qs('btn-diagnostic-export');
    try{
      if(btn) btn.disabled = true;
      await downloadQualityReport();
    }catch(e){
      setStatus('status-visual', '质量分析包导出失败: ' + (e.message || e), true);
      showNotice(e.message || e, 'warn', 4200);
    }finally{
      if(btn) btn.disabled = false;
    }
  });
  on('btn-refresh-host', 'click', function(){
    guarded(loadVisual, 'status-visual');
  });
  on('btn-refresh-runtime', 'click', function(){
    guarded(loadRuntimePanel, 'status-runtime', '运行数据已刷新。', 1800, 3600);
  });
  on('btn-reload-view', 'click', function(){
    guarded(loadVisual, 'status-visual', '设置已重新读取。', 2200);
  });
  qsa('.settings-jump [data-jump]').forEach(function(btn){
    btn.addEventListener('click', function(){
      var target = qs(btn.getAttribute('data-jump') || '');
      if(target && target.scrollIntoView) target.scrollIntoView({behavior:'smooth', block:'start'});
    });
  });
}
function bindModelEditorActions(){
  on('btn-model-map-open', 'click', function(){
    qs('model-map-modal').classList.add('show');
    loadModelEditor().catch(function(e){ if(qs('model-map-editor-state')) qs('model-map-editor-state').textContent = '识别库读取失败: ' + (e.message || e); });
  });
  on('btn-model-map-close', 'click', function(){ qs('model-map-modal').classList.remove('show'); });
  on('model-map-modal', 'click', function(ev){ if(ev.target === qs('model-map-modal')) qs('model-map-modal').classList.remove('show'); });
  on('btn-model-update-now', 'click', updateModelsNow);
  on('btn-app-update-check', 'click', checkAppVersionNow);
  on('btn-model-map-add', 'click', function(){ addModelMapRow('', ''); });
  on('btn-model-map-save', 'click', saveModelEditor);
  on('model-map-search', 'input', function(){ syncModelRowsFromInputs(); renderModelMapRows(); });
  on('model-map-list', 'input', function(ev){
    var t = ev.target;
    if(t && t.classList && t.classList.contains('model-prefix')){
      t.value = cleanModelPrefix(t.value);
    }
    syncModelRowsFromInputs();
  });
  on('model-map-list', 'click', function(ev){
    var btn = ev.target && ev.target.closest ? ev.target.closest('.model-row-delete') : null;
    if(!btn) return;
    var row = btn.closest('.model-map-row');
    var idx = row ? Number(row.getAttribute('data-index')) : -1;
    if(isFinite(idx) && idx >= 0){
      syncModelRowsFromInputs();
      modelMapRows.splice(idx, 1);
      renderModelMapRows();
    }
  });
}
function bindMetricActions(){
  on('cfg-metrics-enabled', 'change', function(){
    updateVisualDraftState();
    loadMetrics().catch(function(e){ if(qs('status-metrics')) qs('status-metrics').textContent = e.message || String(e); });
  });
  qsa('.metric-window').forEach(function(btn){
    btn.addEventListener('click', function(){ setMetricWindow(btn.getAttribute('data-window') || '12h'); });
  });
  on('metrics-zoom', 'input', function(){
    metricSetZoom(Number(qs('metrics-zoom').value || 1), 0.5);
  });
  qsa('.metric-spark').forEach(function(canvas){
    metricBindCanvasEvents(canvas);
  });
}
function bindDataTransferActions(){
  on('btn-export-settings-file', 'click', function(){
    guarded(exportSettingsFile, 'status-data-transfer', '设置文件已导出。', 2200, 3600);
  });
  on('btn-import-settings-file', 'click', function(){ pickFileInput('import-settings-file'); });
  on('import-settings-file', 'change', function(ev){
    var file = (ev && ev.target && ev.target.files && ev.target.files[0]) ? ev.target.files[0] : null;
    if(!file) return;
    guarded(function(){ return importSettingsFileFromFile(file); }, 'status-data-transfer', '', 0, 4200);
  });
  on('btn-export-scan-data', 'click', function(){
    guarded(exportScanDataFile, 'status-data-transfer', '扫描数据已导出。', 2200, 3600);
  });
  on('btn-import-scan-data', 'click', function(){ pickFileInput('import-scan-data-file'); });
  on('import-scan-data-file', 'change', function(ev){
    var file = (ev && ev.target && ev.target.files && ev.target.files[0]) ? ev.target.files[0] : null;
    if(!file) return;
    guarded(function(){ return importScanDataFileFromFile(file); }, 'status-data-transfer', '', 0, 4200);
  });
}
function bindEulaActions(){
  on('btn-eula-view', 'click', function(){ location.href = '/eula?next=/settings'; });
  on('btn-eula-revoke', 'click', revokeEulaAcceptance);
}
function bindCaptureActions(){
  on('btn-network-bindings', 'click', openNetworkBindings);
  on('btn-network-bind-refresh', 'click', function(){ guarded(refreshNetworkBindings, 'status-network-bind', '网卡列表已刷新。', 1800, 3600); });
  on('btn-network-bind-save', 'click', saveNetworkBindingsToDraft);
  on('btn-network-bind-apply', 'click', function(){ guarded(applyNetworkBindings, 'status-network-bind', '网卡绑定已应用。', 2600, 5200); });
  on('btn-network-bind-close', 'click', closeNetworkBindings);
  on('network-bind-modal', 'click', function(ev){ if(ev.target === qs('network-bind-modal')) closeNetworkBindings(); });
  on('network-bind-list', 'change', updateVisualDraftState);
  on('net-ap-ssid', 'input', updateVisualDraftState);
  on('net-ap-password', 'input', updateVisualDraftState);
  on('net-ap-channel', 'input', updateVisualDraftState);
  on('btn-channel-edit', 'click', function(){
    setChannelUi(!settingsState.channelEditing);
  });
  on('btn-channel-reset', 'click', function(){
    settingsState.channelUseDefault = true;
    qs('cfg-channel').value = '6';
    setChannelUi(false);
  });
  on('cfg-channel', 'input', function(){
    var val = Number(qs('cfg-channel').value || '');
    settingsState.channelUseDefault = !(isFinite(val) && val !== 6);
    setChannelUi(settingsState.channelEditing);
  });
}
async function handleLoginLinkListClick(ev){
  var row = ev.target && ev.target.closest ? ev.target.closest('.sso-link-row') : null;
  if(!row) return;
  var check = row.getAttribute('data-check') || '';
  try{
    if(ev.target.closest('.login-link-row-delete')){
      await deleteLoginLink(check);
      showNotice('SSO 校验码已删除。', 'ok', 2400);
      return;
    }
  }catch(e){
    showNotice(e.message || e, 'warn', 3600);
  }
}
async function confirmReauthAction(){
  try{
    var action = reauthAction || 'copy';
    if(action === 'login-link'){
      await createLoginLinkWithCreds();
      setStatus('status-visual', 'SSO 登录链接已生成，只在弹窗中显示一次。', false);
      showNotice('SSO 登录链接已生成。', 'ok', 2600);
    }else if(action === 'api-token-create'){
      await createApiTokenWithCreds();
      setStatus('status-visual', 'API Token 已生成，只在弹窗中显示一次。', false);
      showNotice('API Token 已生成。', 'ok', 2600);
    }else if(action === 'raw-unlock'){
      var user = String(qs('reauth-user').value || '').trim();
      var pass = String(qs('reauth-pass').value || '');
      if(!user || !pass) throw new Error('请输入网页登录账号和密码');
      const data = await postJson('/api/settings/raw/unlock', {username:user, password:pass});
      if(!data.ok) throw new Error(data.error || '原始配置解锁失败');
      settingsState.rawUnlocked = true;
      rawSetLocked(false, '');
      rawRefreshButtons();
      showNotice('原始配置已解锁', 'ok', 2600);
      await loadRaw().catch(function(){});
    }else if(action === 'passkey-create'){
      await createPasskeyWithCreds();
      if(qs('passkey-state')) qs('passkey-state').textContent = '通行密钥已添加，可直接用于网页登录。';
    }else{
      throw new Error('不支持的二次验证操作');
    }
    closeReauth();
  }catch(e){
    setStatus('reauth-status', e.message || e, true);
    showNotice(e.message || e, 'warn', 3600);
  }
}
function bindAccessActions(){
  on('btn-api-token-add', 'click', function(){ openReauth('api-token-create'); });
  on('api-token-list', 'click', handleApiTokenListClick);
  on('api-token-list', 'change', handleApiTokenListChange);
  on('btn-login-link-create', 'click', function(){ openReauth('login-link'); });
  on('btn-passkey-add', 'click', function(){ openReauth('passkey-create'); });
  on('cfg-auth-enabled', 'change', syncAuthMethodUi);
  ['cfg-auth-method-password','cfg-auth-method-passkey'].forEach(function(id){
    on(id, 'change', function(){
      ensureAuthLoginMethodSelection(id, true);
      syncAuthMethodUi();
    });
  });
  on('login-link-expire-mode', 'change', setLoginLinkExpiryUi);
  on('api-token-new-expire-mode', 'change', setApiTokenCreateExpiryUi);
  on('login-link-list', 'click', handleLoginLinkListClick);
  on('passkey-list', 'click', function(ev){
    var row = ev.target && ev.target.closest ? ev.target.closest('.passkey-row') : null;
    if(!row) return;
    var id = row.getAttribute('data-id') || '';
    var del = ev.target && ev.target.closest ? ev.target.closest('.passkey-delete') : null;
    if(!del) return;
    deletePasskey(id).catch(function(e){ showNotice(e.message || e, 'warn', 3600); });
  });
  on('btn-one-time-copy', 'click', function(){ copyTextPlain(oneTimeSecretValue).then(function(){ showNotice('已复制。', 'ok', 1800); }).catch(function(e){ showNotice(e.message || e, 'warn', 2600); }); });
  on('btn-one-time-close', 'click', closeOneTimeSecret);
  on('one-time-modal', 'click', function(ev){ if(ev.target === qs('one-time-modal')) closeOneTimeSecret(); });
  on('btn-reauth-cancel', 'click', function(){ closeReauth(); });
  on('reauth-modal', 'click', function(ev){ if(ev.target === qs('reauth-modal')) closeReauth(); });
  document.addEventListener('keydown', function(ev){ if(ev.key === 'Escape' && qs('reauth-modal').classList.contains('show')) closeReauth(); });
  on('btn-reauth-confirm', 'click', confirmReauthAction);
  on('btn-hook-add', 'click', function(){
    var rows = collectHookRows();
    rows.push({index:null, name:'新通道', enabled:true, key:''});
    renderHookRows(rows);
    updateVisualDraftState();
  });
}
function bindSystemServiceActions(){
  on('btn-service-refresh', 'click', function(){
    guarded(loadSystemServiceStatus, 'status-system-service', '服务状态已刷新。', 1800, 3600);
  });
  on('btn-service-register', 'click', registerSystemdServiceFromSettings);
  on('btn-iw-install', 'click', installIwFromSettings);
  on('btn-security-repair', 'click', repairRuntimeSecurityFromSettings);
  on('btn-elevate-cancel', 'click', function(){ closeElevate(null); });
  on('btn-elevate-confirm', 'click', function(){ closeElevate(qs('elevate-pass') ? qs('elevate-pass').value : ''); });
  on('elevate-pass', 'keydown', function(ev){
    if(ev.key === 'Enter'){
      ev.preventDefault();
      closeElevate(qs('elevate-pass') ? qs('elevate-pass').value : '');
    }
  });
  on('elevate-modal', 'click', function(ev){ if(ev.target === qs('elevate-modal')) closeElevate(null); });
}
function bindRawActions(){
  on('btn-load-raw', 'click', function(){
    guarded(loadRaw, 'status-raw', '原始配置已读取。', 2200);
  });
  on('btn-save-raw', 'click', function(){
    guarded(saveRaw, 'status-raw', '原始配置已保存。', 2600);
  });
  on('btn-delete-raw', 'click', function(){
    guarded(deleteRawFile, 'status-raw', '原始配置文件已删除。', 2600);
  });
  on('btn-raw-unlock', 'click', function(){ openReauth('raw-unlock'); });
  on('btn-raw-unlock-inline', 'click', function(){ openReauth('raw-unlock'); });
  on('raw-tree', 'click', function(ev){
    var btn = ev.target && ev.target.closest ? ev.target.closest('.raw-file-btn') : null;
    if(!btn) return;
    var path = btn.getAttribute('data-path') || '';
    if(!path) return;
    settingsState.rawSelectedPath = path;
    settingsState.rawSelectedRel = btn.getAttribute('data-rel') || '';
    rawRefreshButtons();
    guarded(function(){ return rawLoadFile(path); }, 'status-raw', '已切换配置文件。', 1800);
  });
}
function bindSaveActions(){
  on('btn-test-visual', 'click', async function(){
    try{
      setVisualActionBusy(true);
      await testVisual();
    }catch(e){
      setStatus('status-visual', e.message || e, true);
      showNotice(e.message || e, 'warn', 3800);
    }finally{
      setVisualActionBusy(false);
    }
  });
  on('btn-save-visual', 'click', async function(){
    try{
      setVisualActionBusy(true);
      await saveVisual();
    }catch(e){
      setStatus('status-visual', e.message || e, true);
      showNotice(e.message || e, 'warn', 3800);
    }finally{
      setVisualActionBusy(false);
    }
  });
  on('btn-save-visual-direct', 'click', async function(){
    try{
      setVisualActionBusy(true);
      await saveVisual();
    }catch(e){
      setStatus('status-visual', e.message || e, true);
      showNotice(e.message || e, 'warn', 3800);
    }finally{
      setVisualActionBusy(false);
    }
  });
}
function bindMapAndZoneActions(){
  on('btn-zone-add', 'click', function(){
    var rows = collectZoneRows();
    rows.push({name:'报警区域 ' + (rows.length + 1), enabled:false, lat1:null, lon1:null, lat2:null, lon2:null});
    renderZoneRows(rows);
    updateVisualDraftState();
  });
  on('btn-browser-loc', 'click', useBrowserLocation);
  on('btn-clear-base-loc', 'click', function(){
    qs('cfg-base-lat').value='';
    qs('cfg-base-lon').value='';
    updateVisualDraftState();
    setStatus('status-visual', '已清空基站坐标，等待测试或保存。', false);
  });
  attachRowRemove('zone-list', function(){ renderZoneRows([]); });
}
function bindBrowserPreferenceActions(){
  ['pref-new-firmware-parser'].forEach(function(id){
    on(id, 'change', saveBrowserPrefs);
  });
}
function bindViewportActions(){
  window.addEventListener('resize', function(){ syncSettingsViewport(); drawMetricsChart(); });
  if(window.visualViewport){
    try{
      window.visualViewport.addEventListener('resize', syncSettingsViewport);
      window.visualViewport.addEventListener('scroll', syncSettingsViewport);
    }catch(_e){}
  }
}
function initializeSettingsPage(){
  bindShellActions();
  bindCaptureActions();
  bindModelEditorActions();
  bindMetricActions();
  bindDataTransferActions();
  bindEulaActions();
  bindAccessCollapsibles();
  bindSettingsCardCollapsibles();
  bindAccessActions();
  bindSystemServiceActions();
  bindRawActions();
  bindSaveActions();
  bindMapAndZoneActions();
  bindBrowserPreferenceActions();
  bindViewportActions();
  attachRowRemove('wecom-list', function(){ renderHookRows([]); });
  applyTheme(loadTheme());
  applyTabs();
  bindVisualDraftTracking();
  syncSettingsViewport();
  loadBrowserPrefs();
  loadVisual().catch(function(e){ setStatus('status-visual', e.message || e, true); showNotice(e.message || e, 'warn', 3800); });
  window.setInterval(function(){ loadRuntimePanel().catch(function(){}); }, 2000);
  window.setInterval(function(){ loadMetrics().catch(function(){}); }, 2000);
}
initializeSettingsPage();
</script></body></html>"""

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
