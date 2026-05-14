"""Station-styled viewer settings page."""

from __future__ import annotations

from viewer.ui_common import station_page


def build_settings_page() -> str:
    body = """
  <div class="settings-sticky-head">
    <div class="topbar">
      <div>
        <div class="title">Viewer 设置</div>
        <div class="sub">保留 Station 设置页的视觉结构，只显示 Viewer 主机、地图、登录和许可协议。</div>
      </div>
      <div class="actions">
        <button class="btn" id="btn-back" type="button">返回实时/历史</button>
        <button class="btn" id="btn-nodes" type="button">节点管理</button>
        <button class="btn ghost" id="btn-logout" type="button">登出</button>
        <button class="btn" id="btn-reload-view" type="button">刷新</button>
      </div>
    </div>
    <div class="draft-bar">
      <div class="draft-copy">
        <div class="draft-title" id="draft-title">当前没有未保存修改</div>
        <div class="draft-meta" id="draft-meta">地图和登录设置会写入 viewer/cfg.db；远程节点配置在“节点管理”页面维护。</div>
      </div>
      <div class="draft-actions">
        <button class="btn warn" id="btn-save-settings" type="button">保存设置</button>
      </div>
    </div>
    <div class="settings-jump" aria-label="设置分组导航">
      <button class="btn ghost" data-jump="settings-status" type="button">状态</button>
      <button class="btn ghost" data-jump="settings-map" type="button">地图</button>
      <button class="btn ghost" data-jump="settings-access" type="button">访问</button>
      <button class="btn ghost" data-jump="settings-eula" type="button">许可</button>
    </div>
  </div>
  <div class="panel active" data-tab="visual">
    <div class="visual-grid">
      <div class="stack">
        <div class="stack-label">Viewer 主机</div>
        <div class="card" id="settings-status">
          <div class="section-head">
            <div>
              <h2>主机状态</h2>
              <div class="section-copy">查看 Viewer 进程、配置库和聚合节点状态。</div>
            </div>
            <button class="btn ghost" id="btn-refresh-host" type="button">刷新状态</button>
          </div>
          <div id="host-stats" class="stats-grid" style="margin-top:14px"></div>
          <div id="host-meta" class="micro">-</div>
        </div>
        <div class="card" id="settings-map" data-card-key="map">
          <div class="section-head">
            <div>
              <h2>地图默认位置</h2>
              <div class="section-copy">没有任何可显示飞机时，实时/历史地图遵循这里的默认中心和缩放。</div>
            </div>
          </div>
          <div class="grid" style="margin-top:14px">
            <div class="field"><label>显示名称</label><input id="cfg-base-name" type="text"></div>
            <div class="field"><label>默认缩放</label><input id="cfg-base-zoom" type="number" min="3" max="30"></div>
            <div class="field"><label>默认纬度</label><input id="cfg-base-lat" type="number" step="0.000001"></div>
            <div class="field"><label>默认经度</label><input id="cfg-base-lon" type="number" step="0.000001"></div>
            <div class="field"><label>自动回中冷却(s)</label><input id="cfg-map-idle" type="number" min="5" max="600"></div>
            <div class="field"><label>参考航向(°)</label><input id="cfg-heading-ref" type="number" step="0.1"></div>
            <div class="field full">
              <label>定位</label>
              <div class="row-actions">
                <button class="btn" id="btn-browser-loc" type="button">读取浏览器位置</button>
                <button class="btn ghost" id="btn-clear-base-loc" type="button">清空默认坐标</button>
              </div>
              <div class="micro" id="base-geo-hint">浏览器定位能力由当前访问协议和浏览器权限决定。</div>
            </div>
          </div>
        </div>
      </div>
      <div class="stack">
        <div class="stack-label">访问与许可</div>
        <div class="card access-group" id="settings-access" data-card-key="access">
          <div class="section-head">
            <div>
              <h2>访问控制</h2>
              <div class="section-copy">Viewer 只保留账号密码登录和 SSO check 登录；不包含 PassKey、通知和远程 API Token 管理。</div>
            </div>
          </div>
          <div class="access-subgrid" style="margin-top:14px">
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">网页登录</div>
                  <div class="access-subcopy">控制设置页、节点管理页和聚合页面的网页登录会话。</div>
                </div>
              </div>
              <div class="grid">
                <div class="field"><label>网页登录账号</label><input id="cfg-auth-user" type="text"></div>
                <div class="field"><label>网页登录密码</label><input id="cfg-auth-pass" type="password" placeholder="留空不修改"></div>
              </div>
              <div class="checks">
                <label><input id="cfg-auth-enabled" type="checkbox"> 启用网页登录鉴权</label>
              </div>
            </div>
            <div class="access-subcard full">
              <div class="access-subhead">
                <div>
                  <div class="access-subtitle">SSO check 登录</div>
                  <div class="access-subcopy">Viewer 本机登录入口使用 /?check=...；子站 SSO 登录在节点管理页按节点生成。</div>
                </div>
              </div>
              <div class="grid">
                <div class="field full"><label>SSO check 密钥</label><input id="cfg-sso-check" type="password" placeholder="留空不修改，至少 12 位"></div>
              </div>
              <div class="checks">
                <label><input id="cfg-sso-enabled" type="checkbox"> 启用 SSO check 登录</label>
              </div>
              <div class="micro" id="secret-state">至少保留一种可用登录方式，避免锁定自己。</div>
            </div>
          </div>
          <div id="status-settings" class="status">-</div>
        </div>
        <div class="card" id="settings-eula">
          <div class="section-head">
            <div>
              <h2>许可协议</h2>
              <div class="section-copy">查看或撤回 Viewer 的 EULA 确认；撤回后会重新要求确认。</div>
            </div>
          </div>
          <div class="row-actions" style="margin-top:14px">
            <button class="btn" id="btn-eula-view" type="button">查看 EULA</button>
            <button class="btn warn" id="btn-eula-revoke" type="button">撤回同意</button>
          </div>
          <div id="status-eula" class="status">-</div>
        </div>
      </div>
    </div>
  </div>
"""
    script = r"""
function qs(id){ return document.getElementById(id); }
function qsa(sel){ return Array.prototype.slice.call(document.querySelectorAll(sel) || []); }
function enc(v){ return String(v == null ? '' : v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function pageHeaders(extra){ var h={'X-LightRID-Page':'1'}; if(extra) Object.assign(h, extra); return h; }
async function getJson(path){
  const r = await fetch(path, {cache:'no-store', headers:pageHeaders()});
  const d = await r.json().catch(()=>({}));
  if(r.status === 401){ location.href='/'; throw new Error('login required'); }
  if(!r.ok || d.ok === false) throw new Error(d.error || ('HTTP ' + r.status));
  return d;
}
async function postJson(path, body){
  const r = await fetch(path, {method:'POST', cache:'no-store', headers:pageHeaders({'Content-Type':'application/json'}), body:JSON.stringify(body || {})});
  const d = await r.json().catch(()=>({}));
  if(r.status === 401){ location.href='/'; throw new Error('login required'); }
  if(!r.ok || d.ok === false) throw new Error(d.error || ('HTTP ' + r.status));
  return d;
}
function setStatus(id, text, err){
  var el = qs(id); if(!el) return;
  el.textContent = text || '-';
  el.classList.toggle('err', !!err);
}
function fmtPct(v){ var n=Number(v); return isFinite(n) ? n.toFixed(1)+'%' : '—'; }
function fmtSec(v){
  var n=Number(v); if(!isFinite(n) || n < 0) return '—';
  if(n < 90) return Math.round(n) + ' 秒';
  if(n < 86400) return Math.floor(n/3600) + ' 小时 ' + Math.floor((n%3600)/60) + ' 分钟';
  return Math.floor(n/86400) + ' 天 ' + Math.floor((n%86400)/3600) + ' 小时';
}
function statCard(name, value, extra){
  return '<div class="stat-card"><div class="stat-name">'+enc(name)+'</div><div class="stat-value">'+enc(value)+'</div>'+(extra?'<div class="stat-extra">'+enc(extra)+'</div>':'')+'</div>';
}
function renderHost(host){
  host = host || {};
  var root = qs('host-stats');
  if(root){
    root.innerHTML = [
      statCard('主机', host.hostname || '—', host.platform || ''),
      statCard('CPU', fmtPct(host.cpu_percent), '核心 ' + String(host.cpu_count || '—')),
      statCard('内存', fmtPct(host.mem_percent), ((host.mem_used_mb || 0) && (host.mem_total_mb || 0)) ? (host.mem_used_mb + ' / ' + host.mem_total_mb + ' MB') : ''),
      statCard('运行时间', fmtSec(host.uptime_sec), 'Viewer ' + String(window.LIGHT_RID_VIEWER_VERSION || '')),
      statCard('节点', String(host.online_node_count || 0) + '/' + String(host.node_count || 0), '在线 / 已添加'),
      statCard('飞机', String(host.online_drone_count || 0) + '/' + String(host.drone_count || 0), '当前在线 / 聚合总数')
    ].join('');
  }
  if(qs('host-meta')) qs('host-meta').textContent = '配置库: ' + String(host.db_path || '-') + ' | 监听: ' + String(host.listen || '-');
}
function numberOrBlank(v){ return v == null || v === '' ? '' : String(v); }
async function loadSettings(){
  const data = await getJson('/api/settings');
  const a = data.auth || {}, m = data.map || {};
  qs('cfg-auth-enabled').checked = !!a.enabled;
  qs('cfg-auth-user').value = a.username || 'admin';
  qs('cfg-sso-enabled').checked = !!a.sso_enabled;
  qs('cfg-base-name').value = m.base_name || 'Node Center';
  qs('cfg-base-lat').value = numberOrBlank(m.base_lat);
  qs('cfg-base-lon').value = numberOrBlank(m.base_lon);
  qs('cfg-base-zoom').value = numberOrBlank(m.base_zoom || 5);
  qs('cfg-map-idle').value = numberOrBlank(m.map_auto_center_idle_sec || 20);
  qs('cfg-heading-ref').value = numberOrBlank(m.heading_ref_deg || 0);
  setStatus('status-settings', '密码 ' + (a.password_configured ? '已配置' : '未配置') + ' · SSO ' + (a.sso_configured ? '已配置' : '未配置'), false);
  renderHost(data.host || {});
  renderEula(data.eula || {});
}
function collectSettings(){
  return {
    auth: {
      enabled: qs('cfg-auth-enabled').checked,
      username: qs('cfg-auth-user').value,
      password: qs('cfg-auth-pass').value,
      sso_enabled: qs('cfg-sso-enabled').checked,
      sso_check: qs('cfg-sso-check').value
    },
    map: {
      base_name: qs('cfg-base-name').value,
      base_lat: qs('cfg-base-lat').value,
      base_lon: qs('cfg-base-lon').value,
      base_zoom: qs('cfg-base-zoom').value,
      map_auto_center_idle_sec: qs('cfg-map-idle').value,
      heading_ref_deg: qs('cfg-heading-ref').value
    }
  };
}
async function saveSettings(){
  setStatus('status-settings', '正在保存...', false);
  const data = await postJson('/api/settings/save', collectSettings());
  qs('cfg-auth-pass').value = '';
  qs('cfg-sso-check').value = '';
  renderHost(data.host || {});
  renderEula(data.eula || {});
  setStatus('status-settings', '已保存。密码 ' + (data.auth.password_configured ? '已配置' : '未配置') + ' · SSO ' + (data.auth.sso_configured ? '已配置' : '未配置'), false);
}
function renderEula(eula){
  setStatus('status-eula', (eula.accepted ? '当前已同意许可协议。' : '当前未同意许可协议。') + '\n状态文件: ' + String(eula.set_path || 'viewer/cfg.db'), !eula.accepted);
  if(qs('btn-eula-revoke')) qs('btn-eula-revoke').disabled = !eula.accepted;
}
async function revokeEula(){
  if(!confirm('撤回许可协议同意状态？')) return;
  const data = await postJson('/api/eula/revoke', {});
  renderEula(data);
  setTimeout(function(){ location.href='/eula?next=/settings'; }, 500);
}
function jumpTo(id){
  var el = qs(id); if(el) el.scrollIntoView({behavior:'smooth', block:'start'});
}
qs('btn-back').addEventListener('click', function(){ location.href='/'; });
qs('btn-nodes').addEventListener('click', function(){ location.href='/nodes'; });
qs('btn-logout').addEventListener('click', async function(){ try{ await postJson('/api/logout', {}); }finally{ location.href='/'; } });
qs('btn-reload-view').addEventListener('click', function(){ loadSettings().catch(function(e){ setStatus('status-settings', e.message || e, true); }); });
qs('btn-refresh-host').addEventListener('click', function(){ loadSettings().catch(function(e){ setStatus('host-meta', e.message || e, true); }); });
qs('btn-save-settings').addEventListener('click', function(){ saveSettings().catch(function(e){ setStatus('status-settings', e.message || e, true); }); });
qs('btn-browser-loc').addEventListener('click', function(){
  if(!navigator.geolocation){ setStatus('status-settings', '浏览器不支持定位。', true); return; }
  navigator.geolocation.getCurrentPosition(function(pos){
    qs('cfg-base-lat').value = String(pos.coords.latitude || '');
    qs('cfg-base-lon').value = String(pos.coords.longitude || '');
    setStatus('status-settings', '已读取浏览器位置，保存后生效。', false);
  }, function(err){ setStatus('status-settings', '定位失败: ' + (err && err.message ? err.message : err), true); }, {enableHighAccuracy:true, timeout:12000, maximumAge:0});
});
qs('btn-clear-base-loc').addEventListener('click', function(){ qs('cfg-base-lat').value=''; qs('cfg-base-lon').value=''; });
qs('btn-eula-view').addEventListener('click', function(){ location.href='/eula?next=/settings'; });
qs('btn-eula-revoke').addEventListener('click', function(){ revokeEula().catch(function(e){ setStatus('status-eula', e.message || e, true); }); });
qsa('[data-jump]').forEach(function(btn){ btn.addEventListener('click', function(){ jumpTo(btn.getAttribute('data-jump')); }); });
loadSettings().catch(function(e){ setStatus('status-settings', e.message || e, true); });
"""
    return station_page("Viewer 设置", body, script)
