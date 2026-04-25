
;

// -- WebSocket ------------------------------------------------
var ws, reconnTimer;
var lastLogsSeq = -1;
var lastApsSeq = -1;
var clearHistoryBusy = false;
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
var autoTrackSnSet = {};
var rowClickTimer = null;
var trackCache = {};
var trackLoading = {};
var prefRealtimeTrack = true;
var prefTrack2hOnly = false;
var COOKIE_TRACK_REALTIME = 'rid_realtime_track';
var COOKIE_TRACK_2H_ONLY = 'rid_track_2h_only';
var FREEZE_ON_HOME_KEY = 'rid_freeze_on_home_once';
var LIVE_TRACK_WINDOW_SEC = 300;
var AUTO_TRACK_OFFLINE_HIDE_SEC = LIVE_TRACK_WINDOW_SEC;
var TRACK_FILTER_WINDOW_SEC = 7200;
var replayState = {min:null,max:null,start:null,end:null,cursor:null,playing:false,speed:1,timer:null,userRange:false};
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
function cookieBool(name, defVal){
  var v = cookieGet(name);
  if(v == null || v === '') return !!defVal;
  v = String(v).toLowerCase();
  return (v === '1' || v === 'true' || v === 'on' || v === 'yes');
}
function loadTrackPrefs(){
  prefRealtimeTrack = cookieBool(COOKIE_TRACK_REALTIME, true);
  prefTrack2hOnly = cookieBool(COOKIE_TRACK_2H_ONLY, false);
  saveTrackPrefs();
}
function saveTrackPrefs(){
  cookieSet(COOKIE_TRACK_REALTIME, prefRealtimeTrack ? '1' : '0', 365);
  cookieSet(COOKIE_TRACK_2H_ONLY, prefTrack2hOnly ? '1' : '0', 365);
}
function syncTrackPrefsUi(){
  var rt = qs('opt-realtime-track');
  if(rt) rt.checked = !!prefRealtimeTrack;
  var f2h = qs('opt-track-2h');
  if(f2h) f2h.checked = !!prefTrack2hOnly;
}
function consumeFreezeOnHomeRequest(){
  try{
    homeFreezeAfterFirstRender = (localStorage.getItem(FREEZE_ON_HOME_KEY) === '1');
  }catch(_e){
    homeFreezeAfterFirstRender = false;
  }
}
function refreshAutoTrackSelection(rows){
  autoTrackSnSet = {};
  if(!prefRealtimeTrack) return;
  var arr = Array.isArray(rows) ? rows : [];
  for(var i=0;i<arr.length;i++){
    var e = arr[i] || {};
    var sn = String(e.sn || '');
    if(!sn || e.archived) continue;
    var age = Number(e.age || 0);
    if(!isFinite(age) || age < 0) age = 0;
    if(age >= AUTO_TRACK_OFFLINE_HIDE_SEC) continue;
    autoTrackSnSet[sn] = true;
  }
}
function effectiveTrackSnList(){
  var out = {};
  var sel = selectedSnList();
  for(var i=0;i<sel.length;i++){
    out[String(sel[i] || '')] = true;
  }
  if(prefRealtimeTrack){
    Object.keys(autoTrackSnSet).forEach(function(sn){
      if(sn) out[sn] = true;
    });
  }
  return Object.keys(out).filter(function(sn){ return !!sn; });
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
  if(page === 'history'){
    return historyVisibleSnList(rows);
  }
  return effectiveTrackSnList();
}
function isHistoryTrackVisible(sn){
  sn = String(sn || '');
  return !!sn && !historyHiddenSnSet[sn];
}
function isSnCheckedForCurrentPage(sn){
  return currentAppPage() === 'history' ? isHistoryTrackVisible(sn) : isSnSelected(sn);
}
function _trackTsSec(p){
  var ts = Number((p && p.ts) || 0);
  return (isFinite(ts) && ts > 0) ? ts : null;
}
function filterTrackForDisplay(track, page){
  var arr = Array.isArray(track) ? track.slice() : [];
  if(page === 'live'){
    var liveThreshold = (Date.now() / 1000) - LIVE_TRACK_WINDOW_SEC;
    arr = arr.filter(function(p){
      var ts = _trackTsSec(p);
      return ts == null ? true : (ts >= liveThreshold);
    });
  }else if(prefTrack2hOnly){
    var threshold = (Date.now() / 1000) - TRACK_FILTER_WINDOW_SEC;
    arr = arr.filter(function(p){
      var ts = _trackTsSec(p);
      return ts == null ? true : (ts >= threshold);
    });
  }
  if(page === 'history'){
    arr = filterTrackByReplay(arr);
  }
  return arr;
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
function buildInfoHtml(e){
  e = e || {};
  var html = '<div class="info-grid">';
  html += infoRowHtml('SN', String(e.sn || '-'));
  html += infoRowHtml('机型', String(e.model || 'N/A'));
  html += infoRowHtml('在线状态', e.lost ? '离线' : '在线');
  html += infoRowHtml('归档', e.archived ? '是' : '否');
  html += infoRowHtml('MAC', String(e.mac || '-'));
  html += infoRowHtml('SSID', String(e.ssid || '(hidden)'));
  html += infoRowHtml('来源', snSourceText(e));
  html += infoRowHtml('扫描类型', scanTypeText(e));
  html += infoRowHtml('扫描类型Key', String(e.scan_type_key || '-'));
  html += infoRowHtml('捕获类型', String(e.capture_type || '-'));
  html += infoRowHtml('捕获时间', String(e.capture_time || '-'));
  html += infoRowHtml('最后数据包', String(e.last_pkt_time || e.capture_time || '-'));
  html += infoRowHtml('ID类型', String(e.id_type || '-'));
  html += infoRowHtml('信号', e.rssi==null ? 'N/A' : (e.rssi + 'dBm'));
  html += infoRowHtml('信道', String(e.ch || '?') + (e.ch_assumed ? ' (assumed)' : ''));
  html += infoRowHtml('包数', String(e.pkts==null?0:e.pkts));
  html += infoRowHtml('纬度', fmt(e.lat,6,''));
  html += infoRowHtml('经度', fmt(e.lon,6,''));
  html += infoRowHtml('飞手纬度', fmt(e.pilot_lat,6,''));
  html += infoRowHtml('飞手经度', fmt(e.pilot_lon,6,''));
  html += infoRowHtml('飞手位置类型', String(e.pilot_loc_type_text || e.pilot_loc_type || '-'));
  html += infoRowHtml('高度', fmt(e.alt,1,'m'));
  html += infoRowHtml('速度', fmt(e.spd,2,'m/s'));
  html += infoRowHtml('垂直速度', fmt(e.vspd,2,'m/s'));
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
async function ensureTrackLoaded(sn, force){
  sn = String(sn || '');
  if(!sn) return;
  if(trackLoading[sn]) return;
  if(trackCache[sn] && !force) return;
  trackLoading[sn] = true;
  try{
    var data = await getJson('/api/tracks/get?sn=' + encodeURIComponent(sn));
    var tr = Array.isArray(data.track) ? data.track : [];
    trackCache[sn] = tr;
    if(isSnSelected(sn) || (prefRealtimeTrack && autoTrackSnSet[sn])){
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
function setSnSelected(sn, on){
  sn = String(sn || '');
  if(!sn) return;
  var e = latestDroneMap[sn] || null;
  var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
  if(on){
    selectedSnSet[sn] = true;
    if(mac) selectedMacSet[mac] = true;
  }else{
    delete selectedSnSet[sn];
    if(mac) delete selectedMacSet[mac];
  }
  if(on) ensureTrackLoaded(sn, false);
  syncTableSelectionUi();
  renderLiveCards(latestDroneRows);
  renderMapMiniList(latestDroneRows);
  refreshTrackMgrOptions(latestDroneRows);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function setHistorySnVisible(sn, on){
  sn = String(sn || '');
  if(!sn) return;
  if(on){
    delete historyHiddenSnSet[sn];
    ensureTrackLoaded(sn, false);
  }else{
    historyHiddenSnSet[sn] = true;
  }
  syncTableSelectionUi();
  renderMapMiniList(latestDroneRows);
  refreshReplayBounds(false);
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function setAllVisibleSelected(on){
  if(currentAppPage() === 'history'){
    var hRows = Array.isArray(latestDroneRows) ? latestDroneRows : [];
    hRows.forEach(function(e){
      var sn = String((e && e.sn) || '');
      if(!sn) return;
      if(on){
        delete historyHiddenSnSet[sn];
        ensureTrackLoaded(sn, false);
      }else{
        historyHiddenSnSet[sn] = true;
      }
    });
    syncTableSelectionUi();
    renderMapMiniList(latestDroneRows);
    refreshReplayBounds(false);
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
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
  return esc(v).replace(/\n/g,'&#10;');
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
  return ' class="'+cls+'"'+attrs+' style="--hl-alpha:'+a.toFixed(3)+'"';
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
      rssi: String(e.rssi == null ? '' : e.rssi),
      pkts: String(e.pkts == null ? '' : e.pkts),
      dir: String(e.dir || ''),
      last_seen: String(e.last_seen || ''),
      last_pkt_time: String(e.last_pkt_time || e.capture_time || ''),
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
function showBanner(text, kind, timeoutMs){
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
      var body = nowLabel + '  ' + sn + '\n' + String(e.model || 'N/A') + '  ' +
        (e.rssi == null ? 'N/A' : (e.rssi + 'dBm'));
      pushWebNotification(title, body, 'rid-'+sn+'-'+(isLost?'off':'on'));
      showBanner(title + '  ' + sn, isLost ? 'warn' : 'ok', 2600);
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
      html += '<option value="'+escAttr(name)+'">'+esc(lb)+'</option>';
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
  if(frozenPendingData){
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
  var selSig = selectedSnList().slice().sort().join('|');
  var sig = snSig + '::' + selSig + '::' + (show ? '1' : '0');
  if(sig === miniListRenderSig){
    return;
  }
  miniListRenderSig = sig;
  if(!rows.length){
    box.innerHTML = '<div class="mini-title">暂无飞机</div>';
    return;
  }
  var html = '<div class="mini-title">历史记录 · 选择飞机查看轨迹</div>';
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

  if(!qs('info-modal')){
    var modal = document.createElement('div');
    modal.id = 'info-modal';
    modal.className = 'info-modal';
    modal.innerHTML =
      '<div class="info-card" role="dialog" aria-modal="true" aria-label="详情信息">'+
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
  if(clearBtn && !qs('btn-theme')){
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
      '    <div class="adv-row">'+
      '      <label><input id="opt-realtime-track" type="checkbox"> 实时轨迹（在线自动展示，离线2分钟隐藏）</label>'+
      '    </div>'+
      '    <div class="adv-row">'+
      '      <label><input id="opt-track-2h" type="checkbox"> 自动筛选 2 小时内轨迹</label>'+
      '    </div>'+
      '    <div class="adv-note">轨迹偏好已保存到 Cookie</div>'+
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
      '    <textarea id="config-editor" class="cfg-editor" spellcheck="false" placeholder="在这里编辑 rid_config.json"></textarea>'+
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
      setApPanelCollapsed(false);
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
  if(qs('btn-theme')) qs('btn-theme').addEventListener('click', toggleTheme);
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
  if(qs('opt-realtime-track')) qs('opt-realtime-track').addEventListener('change', function(ev){
    prefRealtimeTrack = !!(ev && ev.target && ev.target.checked);
    saveTrackPrefs();
    refreshAutoTrackSelection(latestDroneRows);
    effectiveTrackSnList().forEach(function(sn){ ensureTrackLoaded(sn, false); });
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  });
  if(qs('opt-track-2h')) qs('opt-track-2h').addEventListener('change', function(ev){
    prefTrack2hOnly = !!(ev && ev.target && ev.target.checked);
    saveTrackPrefs();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  });
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
  updateNotifyButton();
  applySniffStatus(metaState);
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
    showBanner('历史已清空' + (typeof data.cleared==='number' ? ('（'+data.cleared+'架）') : ''), 'ok', 2600);
  }catch(e){
    showBanner('清空失败: ' + ((e && e.message) ? e.message : e), 'warn', 4200);
  }finally{
    if(btn){ btn.disabled = false; btn.textContent = '清空历史'; }
    clearHistoryBusy = false;
  }
}

async function deleteHistoryBySelect(){
  var sel = qs('track-sn-select');
  var st = qs('track-mgr-status');
  var sn = sel ? String(sel.value || '').trim() : '';
  if(!sn){
    if(st) st.textContent = '请先选择飞机';
    return;
  }
  if(!confirm('删除该飞机历史记录？\n' + sn)) return;
  if(st) st.textContent = '删除中...';
  try{
    var data = await postJson('/api/history/delete', {sn: sn});
    var e = latestDroneMap[sn] || null;
    var mac = String((e && (e.mac || e.src_mac)) || '').toLowerCase();
    delete selectedSnSet[sn];
    if(mac) delete selectedMacSet[mac];
    delete trackCache[sn];
    if(st) st.textContent = data.removed ? ('已删除: ' + sn) : ('未找到: ' + sn);
    showBanner('已删除历史: ' + sn, 'ok', 2400);
  }catch(e){
    if(st) st.textContent = '删除失败: ' + ((e && e.message) ? e.message : e);
    showBanner('删除失败', 'warn', 3200);
  }
}

async function clearTrackBySelect(){
  var sel = qs('track-sn-select');
  var st = qs('track-mgr-status');
  var sn = sel ? String(sel.value || '').trim() : '';
  if(!sn){
    if(st) st.textContent = '请先选择飞机';
    return;
  }
  if(!confirm('清空该飞机轨迹？\n' + sn)) return;
  if(st) st.textContent = '清空中...';
  try{
    var data = await postJson('/api/tracks/clear', {sn: sn});
    trackCache[sn] = [];
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
    var cls = 'live-card' + (selected ? ' selected' : '') + (e.lost ? ' lost' : '');
    var rssi = e.rssi == null ? 'N/A' : (String(e.rssi) + 'dBm');
    var model = String(e.model || 'N/A');
    var latlon = (e.lat == null || e.lon == null) ? 'N/A' : (fmt(e.lat,6,'') + ', ' + fmt(e.lon,6,''));
    var pilot = (e.pilot_lat == null || e.pilot_lon == null) ? 'N/A' : (fmt(e.pilot_lat,6,'') + ', ' + fmt(e.pilot_lon,6,''));
    var alt = fmt(e.alt,1,'m');
    var spd = fmt(e.spd,2,'m/s');
    var heading = String(e.dir || '-');
    var stateCls = e.lost ? 'lost' : 'live';
    var stateTxt = e.lost ? '5分钟内离线' : '在线';
    html += '<article class="'+cls+'" data-sn="'+escAttr(sn)+'">'
      + '<div class="live-card-top">'
      +   '<div class="live-card-title" title="'+esc(model)+'">'+esc(model)+'</div>'
      +   '<div class="live-card-actions">'
      +     '<label class="live-card-pick"><input class="sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+(selected?' checked':'')+'><span>选中</span></label>'
      +     '<span class="live-card-state '+stateCls+'">'+esc(stateTxt)+'</span>'
      +   '</div>'
      + '</div>'
      + '<div class="live-card-snrow"><span class="label">SN</span><span class="live-card-sntext" title="'+esc(sn)+'">'+esc(sn || '-')+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+escAttr(sn)+'" title="复制 SN">⧉</button></div>'
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
    if(uiFrozen){
      frozenPendingData = d;
      return;
    }
    onData(d);
  };
}
function setWsState(ok){
  qs('dot-ws').className = ok ? 'on' : '';
  qs('ws-status').textContent = ok ? '实时' : '重连中';
}

function onData(d){
  buildExtraUi();
  applyMeta((d && d.meta) || {});
  qs('cur-ts').textContent = d.ts;
  qs('cur-ch').textContent = d.ch;
  var list = Array.isArray(d.drones) ? d.drones : [];
  var live = list.filter(function(x){ return x && !x.lost; }).length;
  qs('n-live').textContent = live;
  qs('n-lost').textContent = list.length - live;
  syncFieldHighlights(list);
  handleDroneNotifications(list);
  latestDroneMap = {};
  latestDroneRows = list.slice();
  syncSelectedFromRows(latestDroneRows);
  refreshAutoTrackSelection(latestDroneRows);
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
      var cls = e.lost ? 'lost' : (sn.indexOf('MAC:')===0 ? 'mac' : 'live');
      if(selected) cls += ' selected';
      var snMeta = '<span class="sn-badge">'+esc(snSrc)+'</span><span class="sn-badge">'+esc(scanType)+'</span>';
      var modelCls = fieldCellAttrs(sn, 'model', '');
      var rssiCls = fieldCellAttrs(sn, 'rssi', '');
      var pktCls = fieldCellAttrs(sn, 'pkts', '');
      var dirCls = fieldCellAttrs(sn, 'dir', '');
      var ageCls = fieldCellAttrs(sn, 'age_text', 'mono');
      var lastSeenCls = fieldCellAttrs(sn, 'last_seen', 'mono');
      var lastPktCls = fieldCellAttrs(sn, 'last_pkt_time', 'mono');
      var checked = selected ? ' checked' : '';
      var chip = '<span class="track-color-chip" style="--track-color:'+escAttr(trackColorForSn(sn))+';'+(selected ? '' : 'display:none')+'" title="轨迹颜色"></span>';
      rows += '<tr class="'+cls+' data-row" data-sn="'+escAttr(sn)+'">'+
        '<td><div class="sel-wrap track-sel-wrap"><input class="sel-sn" type="checkbox" data-sn="'+escAttr(sn)+'"'+checked+'>'+chip+'</div></td>'+
        '<td class="idx-cell">'+(idx+1)+'</td>'+
        '<td><div class="sn-cell">'+snMeta+'<span class="mono">'+esc(sn)+'</span><button class="icon-btn copy-sn" type="button" data-sn="'+esc(sn)+'" title="复制SN">⧉</button></div></td>'+
        '<td'+modelCls+'>'+esc(e.model || 'N/A')+'</td>'+
        '<td'+rssiCls+'>'+fmt(e.rssi,0,'dBm')+'</td>'+
        '<td'+pktCls+'>'+esc(e.pkts==null?'0':e.pkts)+'</td>'+
        '<td'+dirCls+'>'+esc(e.dir || '-')+'</td>'+
        '<td'+ageCls+'>'+esc(e.age_text || fmtAge(e.age))+'</td>'+
        '<td'+lastSeenCls+'>'+esc(e.last_seen || '-')+'</td>'+
        '<td'+lastPktCls+'>'+esc(e.last_pkt_time || e.capture_time || '-')+'</td>'+
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
    if(e && Number(e.track_count || 0) !== Number((trackCache[sn] || []).length)){
      ensureTrackLoaded(sn, true);
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

var map = null, markers = {}, pilotMarkers = {}, trackLines = {}, twsLines = {}, baseMarker = null;
var motionState = {};
var COLORS = ['#58a6ff','#3fb950','#d29922','#d2a8ff','#79c0ff','#ff7b72'];
var TRACK_COLORS = ['#1f9dff','#12b886','#ff8f1f','#ff4d6d','#8b5cf6','#06b6d4','#84cc16','#eab308'];
var colorIdx = {};
var LIVE_RECENT_WINDOW_SEC = LIVE_TRACK_WINDOW_SEC;
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
    if(e.lost) return false;
    var age = Number(e.age || 0);
    if(!isFinite(age) || age < 0) age = 0;
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

function initMap(){
  if(map) return;
  map = L.map('map', {zoomControl:true, attributionControl:true, maxZoom:30});
  L.tileLayer('https://webrd0{s}.is.autonavi.com/appmaptile?lang=zh_cn&size=1&scale=1&style=8&x={x}&y={y}&z={z}',{
    subdomains:['1','2','3','4'],
    maxZoom:30,
    maxNativeZoom:18,
    attribution:'&copy; 高德地图'
  }).addTo(map);
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
  var card = qs('track-replay-card');
  if(card) return card;
  card = document.createElement('aside');
  card.id = 'track-replay-card';
  card.className = 'track-replay-card';
  card.innerHTML =
    '<div class="track-replay-head"><div><div class="track-replay-title">轨迹重放</div><div id="track-replay-count" class="track-replay-sub">-</div></div><button class="btn-mini" id="btn-replay-play" type="button">播放</button></div>'+
    '<div class="track-replay-time" id="track-replay-time">-</div>'+
    '<div class="track-replay-ranges">'+
    '  <input id="replay-range-start" type="range" min="0" max="1000" step="1" value="0" aria-label="重放开始时间">'+
    '  <input id="replay-range-end" type="range" min="0" max="1000" step="1" value="1000" aria-label="重放结束时间">'+
    '</div>'+
    '<div class="track-replay-controls">'+
    '  <button class="btn-mini" id="btn-replay-reset" type="button">全段</button>'+
    '  <label class="track-speed-label">速度<select id="replay-speed"><option value="0.5">0.5x</option><option value="1" selected>1x</option><option value="2">2x</option><option value="4">4x</option></select></label>'+
    '</div>'+
    '<div class="track-replay-status" id="track-replay-status">选择历史轨迹后可重放。</div>';
  panel.appendChild(card);
  var start = qs('replay-range-start');
  var end = qs('replay-range-end');
  if(start) start.addEventListener('input', onReplayRangeInput);
  if(end) end.addEventListener('input', onReplayRangeInput);
  var play = qs('btn-replay-play');
  if(play) play.addEventListener('click', function(){ setReplayPlaying(!replayState.playing); });
  var reset = qs('btn-replay-reset');
  if(reset) reset.addEventListener('click', resetReplayRange);
  var speed = qs('replay-speed');
  if(speed) speed.addEventListener('change', function(){ replayState.speed = Math.max(0.25, Number(speed.value || 1)); });
  return card;
}
function collectReplayBounds(){
  var minTs = null;
  var maxTs = null;
  displayTrackSnList('history', latestDroneRows).forEach(function(sn){
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    for(var i=0;i<tr.length;i++){
      var ts = _trackTsSec(tr[i]);
      if(ts == null) continue;
      if(minTs == null || ts < minTs) minTs = ts;
      if(maxTs == null || ts > maxTs) maxTs = ts;
    }
  });
  return {min:minTs, max:maxTs};
}
function refreshReplayBounds(keepRange){
  ensureTrackReplayCard();
  var b = collectReplayBounds();
  if(b.min == null || b.max == null || b.max <= b.min){
    stopReplayTimer();
    replayState.min = replayState.max = replayState.start = replayState.end = replayState.cursor = null;
    replayState.userRange = false;
    renderReplayCard();
    clearReplayMarkers();
    return;
  }
  var oldMin = replayState.min;
  var oldMax = replayState.max;
  replayState.min = b.min;
  replayState.max = b.max;
  if(!keepRange || !replayState.userRange || replayState.start == null || replayState.end == null || oldMin == null || oldMax == null){
    replayState.start = b.min;
    replayState.end = b.max;
    replayState.cursor = b.min;
  }else{
    replayState.start = Math.max(b.min, Math.min(b.max, Number(replayState.start)));
    replayState.end = Math.max(replayState.start, Math.min(b.max, Number(replayState.end)));
    replayState.cursor = Math.max(replayState.start, Math.min(replayState.end, Number(replayState.cursor || replayState.start)));
  }
  renderReplayCard();
}
function renderReplayCard(){
  var card = ensureTrackReplayCard();
  if(!card) return;
  var page = currentAppPage();
  card.style.display = (page === 'history') ? '' : 'none';
  var count = displayTrackSnList('history', latestDroneRows).length;
  var countEl = qs('track-replay-count');
  if(countEl) countEl.textContent = count ? ('显示 ' + count + ' 条轨迹') : '暂无轨迹';
  var startEl = qs('replay-range-start');
  var endEl = qs('replay-range-end');
  var hasRange = replayState.min != null && replayState.max != null && replayState.max > replayState.min;
  if(startEl) startEl.disabled = !hasRange;
  if(endEl) endEl.disabled = !hasRange;
  if(startEl && hasRange) startEl.value = String(replayTsToSlider(replayState.start));
  if(endEl && hasRange) endEl.value = String(replayTsToSlider(replayState.end));
  var play = qs('btn-replay-play');
  if(play){
    play.disabled = !hasRange;
    play.textContent = replayState.playing ? '暂停' : '播放';
  }
  var reset = qs('btn-replay-reset');
  if(reset) reset.disabled = !hasRange;
  var time = qs('track-replay-time');
  if(time){
    time.textContent = hasRange
      ? (fmtReplayTime(replayState.start) + ' 至 ' + fmtReplayTime(replayState.end))
      : '暂无可重放轨迹';
  }
  var status = qs('track-replay-status');
  if(status){
    if(!hasRange) status.textContent = count ? '轨迹正在加载或时间点不足。' : '历史记录默认显示全部轨迹。';
    else status.textContent = replayState.playing ? ('播放到 ' + fmtReplayTime(replayState.cursor)) : '拖动区间滑条筛选轨迹，点击播放开始重放。';
  }
}
function onReplayRangeInput(){
  if(replayState.min == null || replayState.max == null) return;
  var startEl = qs('replay-range-start');
  var endEl = qs('replay-range-end');
  var startTs = replaySliderToTs(startEl ? startEl.value : 0);
  var endTs = replaySliderToTs(endEl ? endEl.value : 1000);
  if(startTs == null || endTs == null) return;
  if(startTs > endTs){
    var tmp = startTs;
    startTs = endTs;
    endTs = tmp;
  }
  replayState.start = startTs;
  replayState.end = endTs;
  replayState.userRange = true;
  replayState.cursor = Math.max(startTs, Math.min(endTs, Number(replayState.cursor || startTs)));
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function resetReplayRange(){
  if(replayState.min == null || replayState.max == null) return;
  replayState.start = replayState.min;
  replayState.end = replayState.max;
  replayState.cursor = replayState.start;
  replayState.userRange = false;
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function stopReplayTimer(){
  if(replayState.timer){
    clearInterval(replayState.timer);
    replayState.timer = null;
  }
  replayState.playing = false;
}
function setReplayPlaying(on){
  if(!on){
    stopReplayTimer();
    renderReplayCard();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
    return;
  }
  if(replayState.start == null || replayState.end == null || replayState.end <= replayState.start) return;
  if(replayState.cursor == null || replayState.cursor >= replayState.end){
    replayState.cursor = replayState.start;
  }
  replayState.playing = true;
  if(replayState.timer) clearInterval(replayState.timer);
  replayState.timer = setInterval(function(){
    var span = Math.max(1, Number(replayState.end) - Number(replayState.start));
    var step = Math.max(1, span / 240) * Math.max(0.25, Number(replayState.speed || 1));
    replayState.cursor = Math.min(Number(replayState.end), Number(replayState.cursor || replayState.start) + step);
    if(replayState.cursor >= replayState.end){
      stopReplayTimer();
    }
    renderReplayCard();
    updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
  }, 250);
  renderReplayCard();
  updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
}
function replayWindowEnd(){
  if(replayState.playing && replayState.cursor != null) return replayState.cursor;
  return replayState.end;
}
function filterTrackByReplay(track){
  var arr = Array.isArray(track) ? track.slice() : [];
  if(currentAppPage() !== 'history') return arr;
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
  if(currentAppPage() !== 'history' || replayState.start == null || replayWindowEnd() == null){
    clearReplayMarkers();
    return;
  }
  var active = {};
  var end = Number(replayWindowEnd());
  var start = Number(replayState.start);
  displayTrackSnList('history', latestDroneRows).forEach(function(sn){
    var tr = Array.isArray(trackCache[sn]) ? trackCache[sn] : [];
    var point = null;
    for(var i=0;i<tr.length;i++){
      var p = tr[i] || {};
      var ts = _trackTsSec(p);
      if(ts == null || ts < start || ts > end) continue;
      point = p;
    }
    if(!point) return;
    var lat = Number(point.lat), lon = Number(point.lon);
    if(!isFinite(lat) || !isFinite(lon)) return;
    active[sn] = true;
    var pos = toMapLatLng(lat, lon);
    var col = trackColorForSn(sn);
    var popup = '<b>'+esc(sn)+'</b><br>重放位置<br>'+fmtReplayTime(point.ts);
    if(replayMarkers[sn]){
      replayMarkers[sn].setLatLng(pos).setStyle({color:'#fff', fillColor:col}).setPopupContent(popup);
    }else{
      replayMarkers[sn] = L.circleMarker(pos, {
        radius:7,
        color:'#fff',
        weight:2,
        fillColor:col,
        fillOpacity:0.96,
        opacity:0.95
      }).addTo(map).bindPopup(popup);
    }
  });
  Object.keys(replayMarkers).forEach(function(sn){
    if(!active[sn]){
      map.removeLayer(replayMarkers[sn]);
      delete replayMarkers[sn];
    }
  });
}

function droneIcon(color, lost, headingDeg, selected, indexNo){
  var op = lost ? 0.34 : 1.0;
  var rot = Number(headingDeg);
  if(!isFinite(rot)) rot = 0;
  var idx = Number(indexNo);
  if(!isFinite(idx) || idx <= 0) idx = 0;
  var idxTxt = idx > 99 ? '99+' : String(Math.round(idx));
  var glow = selected ? '0 0 8px rgba(255,255,255,.48)' : 'none';
  var lineOp = selected ? 0.96 : 0.68;
  var svg = '<svg xmlns="http://www.w3.org/2000/svg" width="68" height="68" viewBox="0 0 34 34">'
    +'<circle cx="17" cy="17" r="12.5" fill="'+color+'" fill-opacity="'+op+'" stroke="#fff" stroke-width="1.5"/>'
    +'<text x="17" y="19.7" text-anchor="middle" font-size="10.5" fill="#04131d" font-family="ui-monospace,Consolas" font-weight="700">'+esc(idxTxt)+'</text>'
    +'<line x1="17" y1="17" x2="17" y2="4.5" stroke="#fff" stroke-opacity="'+lineOp+'" stroke-width="'+(selected?2.3:1.6)+'"/>'
    +'<g transform="translate(17,17) rotate('+rot.toFixed(1)+') translate(-17,-17)" style="filter:'+glow+'">'
    +'<polygon points="17,6.4 20.4,16.4 17,14.8 13.6,16.4" fill="#ffffff" fill-opacity="'+(lost?0.68:0.98)+'"/>'
    +'<rect x="16.2" y="14.2" width="1.6" height="8.8" fill="#ffffff" fill-opacity="'+(lost?0.62:0.94)+'"/>'
    +'</g>'
    +'</svg>';
  return L.divIcon({
    html: svg, className:'', iconSize:[68,68], iconAnchor:[34,34], popupAnchor:[0,-30]
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
    mapHintTxt = '实时目标:' + recentRows.length + '  飞机:' + liveAir.length + '  飞手:' + livePilot.length + '  时窗:5分钟';
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
                   .setIcon(droneIcon(col, e.lost, heading, isSel, dispNo))
                   .setPopupContent(popup);
    } else {
      markers[sn] = L.marker(airPos, {icon: droneIcon(col, e.lost, heading, isSel, dispNo)})
        .addTo(map).bindPopup(popup);
      (function(snLocal){
        markers[snLocal].on('click', function(){
          if(currentAppPage() === 'history') setHistorySnVisible(snLocal, true);
          else setSnSelected(snLocal, true);
        });
      })(sn);
    }

    if(page === 'history' && isSel && isFinite(Number(heading))){
      var spd = Number(e.spd);
      var refSpd = (isFinite(spd) && spd > 0) ? spd : 8.0;
      var startOffset = 22;
      var refLen = Math.max(45, Math.min(260, refSpd * 10.0));
      var p1w = destinationPoint(latRaw, lonRaw, Number(heading), startOffset);
      var p2w = destinationPoint(latRaw, lonRaw, Number(heading), startOffset + refLen);
      var p1 = toMapLatLng(p1w.lat, p1w.lon);
      var p2 = toMapLatLng(p2w.lat, p2w.lon);
      var twsPts = [p1, p2];
      if(twsLines[sn]){
        twsLines[sn].setLatLngs(twsPts).setStyle({color:col, weight:2.1, opacity:0.95, dashArray:'3 5'});
      }else{
        twsLines[sn] = L.polyline(twsPts, {
          color:col,
          weight:2.1,
          opacity:0.95,
          dashArray:'3 5',
          lineCap:'round'
        }).addTo(map);
      }
      activeTws[sn] = true;
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
          else setSnSelected(snLocal, true);
        });
      })(sn);
    }
  });

  var activeTrack = {};
  var trackLatLngsAll = [];
  trackSn.forEach(function(sn){
    sn = String(sn || '');
    if(!sn) return;
    var tr = filterTrackForDisplay(Array.isArray(trackCache[sn]) ? trackCache[sn] : [], page);
    if(tr.length < 2){
      if(trackLines[sn]){
        map.removeLayer(trackLines[sn]);
        delete trackLines[sn];
      }
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
      if(trackLines[sn]){
        map.removeLayer(trackLines[sn]);
        delete trackLines[sn];
      }
      return;
    }
    activeTrack[sn] = true;
    var tColor = trackColorForSn(sn);
    if(trackLines[sn]){
      trackLines[sn].setLatLngs(latlngs);
      trackLines[sn].setStyle({color:tColor, weight:4, opacity:0.82});
    } else {
      trackLines[sn] = L.polyline(latlngs, {
        color:tColor,
        weight:4,
        opacity:0.82,
        lineJoin:'round'
      }).addTo(map);
    }
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
      map.removeLayer(trackLines[sn]); delete trackLines[sn];
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

;

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
    el.innerHTML = '<div class="zone-alarm-card"><div class="zone-alarm-title">区域告警</div><div id="zone-alarm-text" class="zone-alarm-text">检测到目标进入报警区域</div></div>';
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
    document.body.setAttribute('data-page', p);
    cookieSet(PAGE_COOKIE, p, 365);
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
      header.appendChild(nav);
    }
    var clearBtn = qs('btn-clear-history');
    if(clearBtn && !qs('btn-settings')){
      var btn = document.createElement('button');
      btn.id = 'btn-settings';
      btn.className = 'btn-mini header-link-btn';
      btn.type = 'button';
      btn.textContent = '设置';
      btn.addEventListener('click', function(){ location.href = '/settings'; });
      clearBtn.parentNode.insertBefore(btn, clearBtn);
    }
    if(clearBtn && !qs('btn-logs')){
      var logBtn = document.createElement('button');
      logBtn.id = 'btn-logs';
      logBtn.className = 'btn-mini header-link-btn';
      logBtn.type = 'button';
      logBtn.textContent = '日志';
      logBtn.addEventListener('click', function(){ location.href = '/logs'; });
      clearBtn.parentNode.insertBefore(logBtn, clearBtn);
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
        setSnSelected(sn, true);
        var e = latestDroneMap[sn];
        if(e) showInfoCard(buildInfoHtml(e), true);
        updateMap(Array.isArray(latestDroneRows) ? latestDroneRows : []);
        renderLiveCards(latestDroneRows);
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
      html += infoRowHtml(rows[i][0], rows[i][1]);
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
  function patchInfoCard(){
    buildInfoHtml = function(e){
      e = e || {};
      var base = [
        ['SN', String(e.sn || '-')],
        ['机型', String(e.model || 'N/A')],
        ['在线状态', e.lost ? '离线' : '在线'],
        ['来源', snSourceText(e)],
        ['扫描类型', scanTypeText(e)],
        ['MAC', String(e.mac || '-')],
        ['SSID', String(e.ssid || '(hidden)')],
        ['捕获类型', String(e.capture_type || '-')],
        ['捕获时间', String(e.capture_time || '-')],
        ['最后数据包', String(e.last_pkt_time || e.capture_time || '-')],
        ['信号', e.rssi==null ? 'N/A' : (e.rssi + 'dBm')],
        ['信道', String(e.ch || '?') + (e.ch_assumed ? ' (assumed)' : '')],
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
        ['高度', fmt(e.alt,1,'m')],
        ['速度', fmt(e.spd,2,'m/s')],
        ['垂直速度', fmt(e.vspd,2,'m/s')],
        ['方向', String(e.dir || '-')]
      ];
      var pilotPos = [
        ['飞手纬度', fmt(e.pilot_lat,6,'')],
        ['飞手经度', fmt(e.pilot_lon,6,'')],
        ['飞手位置类型', String(e.pilot_loc_type_text || e.pilot_loc_type || '-')]
      ];
      var html = '<div class="info-actions">'+
        '<button class="btn-mini export-track-btn" type="button" data-sn="'+escAttr(String(e.sn||''))+'">导出轨迹</button>'+
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
  function setZoneAlarm(rows){
    var overlay = ensureZoneOverlay();
    var groups = zoneHitGroups(rows);
    if(!groups.length){
      overlay.classList.remove('show');
      alarmLastSig = '';
      return;
    }
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
    qs('zone-alarm-text').textContent = '检测到目标进入自定义报警区域：' + lineText;
    overlay.classList.add('show');
    if(sig !== alarmLastSig){
      showBanner('区域告警：' + lineText, 'warn', 5200);
      if(webNotifyEnabled && window.Notification && Notification.permission === 'granted'){
        try{ new Notification('Light RID Scanner 区域告警', {body:lineText}); }catch(_e){}
      }
      alarmLastSig = sig;
    }
    if(alarmOverlayHideTimer) clearTimeout(alarmOverlayHideTimer);
    alarmOverlayHideTimer = setTimeout(function(){
      if(!zoneHitGroups(latestDroneRows).length){
        overlay.classList.remove('show');
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
    refreshReplayBounds(true);
    _origUpdateMap(drones);
    drawAlarmZones();
    setZoneAlarm(drones);
    renderReplayCard();
    updateReplayMarkers();
  };
  document.addEventListener('DOMContentLoaded', function(){
    patchInfoCard();
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
