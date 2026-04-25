
function qs(id){ return document.getElementById(id); }
function qsa(sel){ return Array.prototype.slice.call(document.querySelectorAll(sel) || []); }
function enc(v){ return String(v == null ? '' : v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function splitLines(text){
  var raw = String(text || '');
  if(raw.indexOf('\r') >= 0) raw = raw.split('\r').join('');
  return raw.split('\n');
}
function isLocalHostName(host){
  var h = String(host || '').toLowerCase();
  return h === 'localhost' || h === '127.0.0.1';
}
var apiTokenAction = '__KEEP__';
var apiTokenLastReveal = '';
var reauthAction = null;
var settingsState = {visualLoaded:false, rawLoaded:false, apiLoaded:false, channelUseDefault:true, channelEditing:false, visualInitial:null, visualDirty:false, dirtyCards:{}};
var COOKIE_TRACK_REALTIME = 'rid_realtime_track';
var COOKIE_TRACK_2H_ONLY = 'rid_track_2h_only';
var FREEZE_ON_HOME_KEY = 'rid_freeze_on_home_once';
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
async function getJson(url){
  const r = await fetch(apiUrl(url), {cache:'no-store', headers:pageHeaders()});
  const d = await r.json().catch(()=>({}));
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
}
async function postJson(url, body){
  const r = await fetch(apiUrl(url), {method:'POST', headers:pageHeaders({'Content-Type':'application/json'}), body:JSON.stringify(body||{})});
  const d = await r.json().catch(()=>({}));
  if(!r.ok || d.ok===false) throw new Error(d.error || ('HTTP '+r.status));
  return d;
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
  var rt = qs('pref-realtime-track');
  var f2h = qs('pref-track-2h');
  if(rt) rt.checked = cookieBool(COOKIE_TRACK_REALTIME, true);
  if(f2h) f2h.checked = cookieBool(COOKIE_TRACK_2H_ONLY, false);
}
function saveBrowserPrefs(){
  var rt = qs('pref-realtime-track');
  var f2h = qs('pref-track-2h');
  cookieSet(COOKIE_TRACK_REALTIME, (rt && rt.checked) ? '1' : '0', 365);
  cookieSet(COOKIE_TRACK_2H_ONLY, (f2h && f2h.checked) ? '1' : '0', 365);
  showNotice('页面偏好已保存到当前浏览器。', 'ok', 2200);
}
function notifySettingsButtonText(){
  if(!('Notification' in window)) return '网页通知(不支持)';
  if(Notification.permission === 'granted') return '网页通知(已开)';
  if(Notification.permission === 'denied') return '网页通知(已拒绝)';
  return '网页通知';
}
function updateHomeActionButtons(){
  var notifyBtn = qs('btn-settings-web-notify');
  if(notifyBtn){
    notifyBtn.textContent = notifySettingsButtonText();
    notifyBtn.disabled = !('Notification' in window) || Notification.permission === 'denied';
  }
}
async function requestSettingsWebNotify(){
  if(!('Notification' in window)){
    setStatus('status-home-actions', '当前浏览器不支持网页通知。', true);
    return;
  }
  try{
    if(Notification.permission !== 'granted'){
      await Notification.requestPermission();
    }
    updateHomeActionButtons();
    if(Notification.permission === 'granted'){
      try{ new Notification('Light RID Scanner 通知已启用', {body:'将推送飞机上下线事件'}); }catch(_e){}
      setStatus('status-home-actions', '网页通知已启用。', false);
      showNotice('网页通知已启用。', 'ok', 2400);
    }else{
      setStatus('status-home-actions', '网页通知未授权。', true);
      showNotice('网页通知未授权。', 'warn', 3200);
    }
  }catch(e){
    setStatus('status-home-actions', '网页通知申请失败: ' + (e.message || e), true);
  }
}
function freezeHomeOnReturn(){
  try{ localStorage.setItem(FREEZE_ON_HOME_KEY, '1'); }catch(_e){}
  location.href = '/';
}
async function clearHistoryFromSettings(){
  if(!confirm('清空历史无人机记录，并删除本地缓存文件？')) return;
  var btn = qs('btn-settings-clear-history');
  if(btn) btn.disabled = true;
  setStatus('status-home-actions', '清空历史中...', false);
  try{
    const data = await postJson('/api/history/clear', {});
    var msg = '历史已清空' + (typeof data.cleared === 'number' ? ('（' + data.cleared + '架）') : '') + '。';
    setStatus('status-home-actions', msg, false);
    showNotice(msg, 'ok', 2600);
    await loadRuntimePanel().catch(function(){});
  }catch(e){
    setStatus('status-home-actions', '清空失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 3800);
  }finally{
    if(btn) btn.disabled = false;
  }
}
async function ensureTabLoaded(tab){
  if(tab === 'raw' && !settingsState.rawLoaded){
    await loadRaw();
    settingsState.rawLoaded = true;
  }
  if(tab === 'api' && !settingsState.apiLoaded){
    await loadApiDocs();
    settingsState.apiLoaded = true;
  }
}
function activateTab(tab){
  qsa('.tab').forEach(function(btn){ btn.classList.toggle('active', btn.getAttribute('data-tab')===tab); });
  qsa('.panel').forEach(function(p){ p.classList.toggle('active', p.getAttribute('data-tab')===tab); });
  ensureTabLoaded(tab).catch(function(e){
    if(tab === 'raw') setStatus('status-raw', e.message || e, true);
    else if(tab === 'api') setStatus('status-api', e.message || e, true);
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
  if(sniff.state) meta.push('采集 ' + sniffLabel);
  if(sniff.msg) meta.push(String(sniff.msg));
  qs('host-meta').textContent = meta.length ? meta.join(' | ') : '-';
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
    log.value = lines.join('\n');
  }
  setStatus('status-runtime', 'AP ' + String((data.aps || []).length || 0) + '/' + String(data.aps_total || 0), false);
}
async function loadRuntimePanel(){
  const data = await getJson('/api/settings/runtime?limit=220');
  renderSettingsRuntime(data);
}
function collectVisualPayload(){
  return {
    basic: {
      iface: v('cfg-iface') || null,
      channel: settingsState.channelUseDefault ? null : n('cfg-channel'),
      channel_use_default: !!settingsState.channelUseDefault,
      time: n('cfg-time'),
      min_gap: n('cfg-min-gap'),
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
      token: (v('cfg-api-token-new') || ((apiTokenAction === '__CLEAR__') ? '__CLEAR__' : '__KEEP__')),
      whitelist_enabled: check('cfg-api-whitelist-enabled'),
      whitelist: splitLines(qs('cfg-api-whitelist').value || '')
    },
    auth: {
      enabled: check('cfg-auth-enabled'),
      realm: v('cfg-auth-realm'),
      username: v('cfg-auth-user') || '__KEEP__',
      password: String((qs('cfg-auth-pass') && qs('cfg-auth-pass').value) || '').trim() || '__KEEP__'
    }
  };
}
function visualPayloadSections(payload){
  payload = payload || {};
  return {
    capture: payload.basic || {},
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
      notify: payload.notify || {},
      api: payload.api || {},
      auth: payload.auth || {}
    }
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
  if(qs('draft-title')) qs('draft-title').textContent = settingsState.visualDirty ? '有未保存修改' : '当前没有未保存修改';
  if(qs('draft-meta')){
    var names = [];
    if(dirtyMap.capture) names.push('采集');
    if(dirtyMap.map) names.push('地图与基站');
    if(dirtyMap.zones) names.push('报警区域');
    if(dirtyMap.access) names.push('通知与访问控制');
    qs('draft-meta').textContent = settingsState.visualDirty
      ? ('已改动: ' + names.join('、') + '。先测试，再决定是否保存。')
      : '改过的卡片会高亮。测试只做预演，不会写入配置文件。';
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
    access: !sameJson(initialSections.access, currentSections.access)
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
    var t = ev.target;
    if(t && t.id === 'cfg-api-token-current') return;
    updateVisualDraftState();
  });
  root.addEventListener('change', function(){
    updateVisualDraftState();
  });
}
function setVisualActionBusy(busy){
  ['btn-test-visual','btn-save-visual','btn-reload-view'].forEach(function(id){
    var el = qs(id);
    if(!el) return;
    if(id === 'btn-test-visual' || id === 'btn-save-visual'){
      el.disabled = !!busy || (!settingsState.visualDirty);
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
    hint.textContent = settingsState.channelUseDefault
      ? '默认 CH6。'
      : '当前使用自定义信道。';
  }
}
function openReauth(action){
  reauthAction = action;
  qs('reauth-user').value = '';
  qs('reauth-pass').value = '';
  setStatus('reauth-status', '请输入网页登录账号和密码。', false);
  qs('reauth-modal').classList.add('show');
  window.setTimeout(function(){ try{ qs('reauth-user').focus(); }catch(_e){} }, 30);
}
function closeReauth(){
  reauthAction = null;
  qs('reauth-modal').classList.remove('show');
}
async function performTokenReauth(action){
  var user = String(qs('reauth-user').value || '').trim();
  var pass = String(qs('reauth-pass').value || '');
  if(!user || !pass){
    setStatus('reauth-status', '请输入完整账号和密码。', true);
    return;
  }
  const r = await fetch(apiUrl('/api/settings/api-token/reveal'), {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify({username:user, password:pass})
  });
  const d = await r.json().catch(()=>({}));
  if(!r.ok || d.ok===false){
    throw new Error(d.error || ('HTTP ' + r.status));
  }
  apiTokenLastReveal = String(d.token || '');
  qs('cfg-api-token-current').value = apiTokenLastReveal;
  qs('cfg-api-token-current').type = (action === 'reveal') ? 'text' : 'password';
  if(action === 'copy'){
    if(!apiTokenLastReveal) throw new Error('当前 Token 不可复制');
    await copyTextPlain(apiTokenLastReveal);
  }
}
function fillIfaceOptions(items, selected){
  const sel = qs('cfg-iface');
  if(!sel) return;
  const opts = ['<option value="">请选择默认网卡</option>'];
  (Array.isArray(items)?items:[]).forEach(function(it){
    const name = String(it.name || '');
    if(!name) return;
    opts.push('<option value="'+enc(name)+'">'+enc(name)+' ['+enc(String(it.mode||''))+'] '+(it.supports_5g ? '5G' : '2.4G')+'</option>');
  });
  sel.innerHTML = opts.join('');
  sel.value = selected || '';
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
      +'<div class="field"><label>Webhook Key</label><input class="hook-key" type="password" value="" placeholder="'+(mask || '输入新的 Key')+'"><div class="micro">当前值: '+(mask || '未设置')+'</div></div>'
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
    setStatus('status-visual', '当前页面不是安全上下文，部分浏览器会拒绝定位。若读取失败，请改用 HTTPS 或手动填写。', true);
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
  const b = s.basic || {}, w = s.web || {}, nt = s.notify || {}, api = s.api || {}, auth = s.auth || {};
  fillIfaceOptions(data.interfaces || [], b.iface || '');
  settingsState.visualLoaded = true;
  settingsState.channelUseDefault = !b.channel_custom;
  qs('cfg-channel').value = String(b.channel_effective == null ? 6 : b.channel_effective);
  setChannelUi(false);
  qs('cfg-time').value = String(b.time ?? '');
  qs('cfg-min-gap').value = String(b.min_gap ?? '');
  qs('cfg-rssi-delta').value = String(b.rssi_delta ?? '');
  qs('cfg-model-map').value = String(b.model_map || '');
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
  renderZoneRows(Array.isArray(w.alarm_zones) ? w.alarm_zones : []);
  renderHostStats(data.host || {}, b);
  loadRuntimePanel().catch(function(){});
  qs('cfg-notify-enabled').checked = !!nt.enabled;
  qs('cfg-notify-reonline').checked = !!nt.notify_reonline;
  qs('cfg-reonline').value = String(nt.reonline_cooldown_sec ?? '');
  qs('cfg-send-timeout').value = String(nt.send_timeout_sec ?? '');
  renderHookRows(Array.isArray(nt.wecom_webhooks) ? nt.wecom_webhooks : []);
  qs('cfg-api-enabled').checked = !!api.enabled;
  apiTokenAction = '__KEEP__';
  apiTokenLastReveal = '';
  qs('cfg-api-token-current').value = '';
  qs('cfg-api-token-current').type = 'password';
  qs('cfg-api-token-current').placeholder = api.token_masked || '未设置';
  qs('cfg-api-token-new').value = '';
  qs('cfg-api-token-new').placeholder = api.token_masked ? '留空则保持不变' : '请输入新的 Token';
  qs('cfg-api-whitelist-enabled').checked = !!api.whitelist_enabled;
  qs('cfg-api-whitelist').value = Array.isArray(api.whitelist) ? api.whitelist.join('\n') : '';
  qs('cfg-auth-enabled').checked = !!auth.enabled;
  qs('cfg-auth-user').value = '';
  qs('cfg-auth-user').placeholder = auth.username_masked || '留空则保持不变';
  qs('cfg-auth-pass').value = '';
  qs('cfg-auth-pass').placeholder = auth.password_masked || '留空则保持不变';
  qs('cfg-auth-realm').value = String(auth.realm || 'Light RID Scanner');
  qs('secret-state').textContent = '通知通道 ' + String((nt.wecom_webhooks || []).length || 0)
    + ' | Token ' + (api.token_masked || '未设置')
    + ' | 外部 API ' + (api.enabled ? '开启' : '关闭')
    + ' | 登录 ' + (auth.enabled ? (auth.configured ? '开启' : '未完成') : '关闭');
  resetVisualDraftState();
  if(data.path) setStatus('status-visual', '配置文件: ' + data.path, false);
}
async function loadRaw(){
  const data = await getJson('/api/config');
  settingsState.rawLoaded = true;
  qs('raw-editor').value = String(data.text || '');
  setStatus('status-raw', '已读取: ' + String(data.path || '-'), false);
}
async function saveVisual(){
  const payload = collectVisualPayload();
  const data = await postJson('/api/settings/visual/save', payload);
  var msg = '测试并保存成功: ' + String(data.saved_to || '-');
  if(data.backup_path) msg += '\n备份: ' + String(data.backup_path);
  if(data.reload_msg) msg += '\n' + String(data.reload_msg);
  setStatus('status-visual', msg, false);
  showNotice('配置已保存并生效。', 'ok', 3600);
  await loadVisual();
}
async function testVisual(){
  const payload = collectVisualPayload();
  const data = await postJson('/api/settings/visual/test', payload);
  var msg = '测试通过，运行配置已回滚。';
  if(data.reload_msg) msg += '\n' + String(data.reload_msg);
  setStatus('status-visual', msg, false);
  showNotice('测试通过，当前运行配置已回滚。', 'ok', 3000);
}
async function saveRaw(){
  const data = await postJson('/api/settings/raw/save', {text: String(qs('raw-editor').value || '')});
  setStatus('status-raw', '保存成功: ' + String(data.saved_to || '-') + '\n' + String(data.reload_msg || ''), false);
}
async function loadApiDocs(){
  const data = await getJson('/api/settings/api-docs').catch(function(){ return {api:{}, endpoints:[]}; });
  settingsState.apiLoaded = true;
  qs('api-docs').value = JSON.stringify(data, null, 2);
  setStatus('status-api', 'API 文档已生成。启用 Token 后可在 Header 中使用 X-API-Token 或 Authorization: Bearer。', false);
}
qs('btn-back').addEventListener('click', function(){ location.href='/'; });
qs('btn-logs').addEventListener('click', function(){ location.href='/logs'; });
qs('btn-theme').addEventListener('click', function(){ applyTheme(document.body.classList.contains('theme-light') ? 'dark' : 'light'); });
qs('btn-open-hw').addEventListener('click', function(){ location.href='/hardware-assistant'; });
qs('btn-diagnostic-export').addEventListener('click', async function(){
  try{
    qs('btn-diagnostic-export').disabled = true;
    await downloadQualityReport();
  }catch(e){
    setStatus('status-visual', '质量分析包导出失败: ' + (e.message || e), true);
    showNotice(e.message || e, 'warn', 4200);
  }finally{
    qs('btn-diagnostic-export').disabled = false;
  }
});
qs('btn-refresh-host').addEventListener('click', async function(){ try{ await loadVisual(); }catch(e){ setStatus('status-visual', e.message || e, true); showNotice(e.message || e, 'warn', 3800); } });
qs('btn-refresh-runtime').addEventListener('click', async function(){ try{ await loadRuntimePanel(); showNotice('运行数据已刷新。', 'ok', 1800); }catch(e){ setStatus('status-runtime', e.message || e, true); showNotice(e.message || e, 'warn', 3600); } });
qs('btn-reload-view').addEventListener('click', async function(){ try{ await loadVisual(); showNotice('设置已重新读取。', 'ok', 2200); }catch(e){ setStatus('status-visual', e.message || e, true); showNotice(e.message || e, 'warn', 3800); } });
qs('btn-home-freeze').addEventListener('click', freezeHomeOnReturn);
qs('btn-settings-web-notify').addEventListener('click', requestSettingsWebNotify);
qs('btn-settings-clear-history').addEventListener('click', clearHistoryFromSettings);
qs('btn-channel-edit').addEventListener('click', function(){
  setChannelUi(!settingsState.channelEditing);
});
qs('btn-channel-reset').addEventListener('click', function(){
  settingsState.channelUseDefault = true;
  qs('cfg-channel').value = '6';
  setChannelUi(false);
});
qs('cfg-channel').addEventListener('input', function(){
  var val = Number(qs('cfg-channel').value || '');
  settingsState.channelUseDefault = !(isFinite(val) && val !== 6);
  setChannelUi(settingsState.channelEditing);
});
qs('btn-api-token-clear').addEventListener('click', function(){
  apiTokenAction = '__CLEAR__';
  apiTokenLastReveal = '';
  qs('cfg-api-token-current').value = '';
  qs('cfg-api-token-current').type = 'password';
  qs('cfg-api-token-current').placeholder = '将于保存时清空';
  qs('cfg-api-token-new').value = '';
  updateVisualDraftState();
  setStatus('status-visual', '当前 API Token 已标记为清空，等待测试或保存。', false);
});
qs('btn-api-token-reveal').addEventListener('click', function(){ openReauth('reveal'); });
qs('btn-api-token-copy').addEventListener('click', function(){ openReauth('copy'); });
qs('btn-reauth-cancel').addEventListener('click', function(){ closeReauth(); });
qs('reauth-modal').addEventListener('click', function(ev){ if(ev.target === qs('reauth-modal')) closeReauth(); });
document.addEventListener('keydown', function(ev){ if(ev.key === 'Escape' && qs('reauth-modal').classList.contains('show')) closeReauth(); });
qs('btn-reauth-confirm').addEventListener('click', async function(){
  try{
    await performTokenReauth(reauthAction || 'copy');
    if(reauthAction === 'copy'){
      setStatus('status-visual', '当前 API Token 已复制到剪贴板。', false);
      showNotice('当前 API Token 已复制。', 'ok', 2400);
    }else{
      setStatus('status-visual', '当前 API Token 已通过再次验证并显示。', false);
      showNotice('当前 API Token 已显示。', 'ok', 2400);
    }
    closeReauth();
  }catch(e){
    setStatus('reauth-status', e.message || e, true);
    showNotice(e.message || e, 'warn', 3600);
  }
});
qs('btn-load-raw').addEventListener('click', async function(){ try{ await loadRaw(); showNotice('原始配置已读取。', 'ok', 2200); }catch(e){ setStatus('status-raw', e.message || e, true); showNotice(e.message || e, 'warn', 3800); } });
qs('btn-save-raw').addEventListener('click', async function(){ try{ await saveRaw(); showNotice('原始配置已保存。', 'ok', 2600); }catch(e){ setStatus('status-raw', e.message || e, true); showNotice(e.message || e, 'warn', 3800); } });
qs('btn-test-visual').addEventListener('click', async function(){
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
qs('btn-save-visual').addEventListener('click', async function(){
  try{
    setVisualActionBusy(true);
    await saveVisual();
    apiTokenAction = '__KEEP__';
    qs('cfg-api-token-new').value = '';
  }catch(e){
    setStatus('status-visual', e.message || e, true);
    showNotice(e.message || e, 'warn', 3800);
  }finally{
    setVisualActionBusy(false);
  }
});
qs('cfg-api-token-new').addEventListener('input', function(){
  if(String(qs('cfg-api-token-new').value || '').trim()){
    apiTokenAction = '__KEEP__';
    qs('cfg-api-token-current').placeholder = qs('cfg-api-token-current').placeholder || '已设置';
  }
  updateVisualDraftState();
});
qs('btn-hook-add').addEventListener('click', function(){
  var rows = collectHookRows();
  rows.push({index:null, name:'新通道', enabled:true, key:''});
  renderHookRows(rows);
  updateVisualDraftState();
});
qs('btn-zone-add').addEventListener('click', function(){
  var rows = collectZoneRows();
  rows.push({name:'报警区域 ' + (rows.length + 1), enabled:false, lat1:null, lon1:null, lat2:null, lon2:null});
  renderZoneRows(rows);
  updateVisualDraftState();
});
qs('btn-browser-loc').addEventListener('click', useBrowserLocation);
qs('btn-clear-base-loc').addEventListener('click', function(){ qs('cfg-base-lat').value=''; qs('cfg-base-lon').value=''; updateVisualDraftState(); setStatus('status-visual', '已清空基站坐标，等待测试或保存。', false); });
['pref-realtime-track','pref-track-2h'].forEach(function(id){
  var el = qs(id);
  if(el) el.addEventListener('change', saveBrowserPrefs);
});
attachRowRemove('wecom-list', function(){ renderHookRows([]); });
attachRowRemove('zone-list', function(){ renderZoneRows([]); });
applyTheme(loadTheme());
applyTabs();
bindVisualDraftTracking();
updateHomeActionButtons();
syncSettingsViewport();
loadBrowserPrefs();
window.addEventListener('resize', syncSettingsViewport);
if(window.visualViewport){
  try{
    window.visualViewport.addEventListener('resize', syncSettingsViewport);
    window.visualViewport.addEventListener('scroll', syncSettingsViewport);
  }catch(_e){}
}
loadVisual().catch(function(e){ setStatus('status-visual', e.message || e, true); showNotice(e.message || e, 'warn', 3800); });
