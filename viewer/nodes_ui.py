"""Station-styled node manager page for the viewer."""

from __future__ import annotations

from viewer.ui_common import station_page


def build_nodes_page() -> str:
    body = """
  <div class="settings-sticky-head">
    <div class="topbar">
      <div>
        <div class="title">节点管理器</div>
        <div class="sub">添加 Station 节点、查看基础信息和负载/扫描数据，并对多个节点执行远程维护。</div>
      </div>
      <div class="actions">
        <button class="btn" id="btn-back" type="button">返回实时/历史</button>
        <button class="btn" id="btn-settings" type="button">Viewer 设置</button>
        <button class="btn ghost" id="btn-refresh" type="button">刷新</button>
      </div>
    </div>
  </div>
  <div class="visual-grid node-manager-grid">
    <div class="stack">
      <div class="stack-label">节点维护</div>
      <div class="card" id="node-editor">
        <div class="section-head">
          <div>
            <h2>添加 / 编辑节点</h2>
            <div class="section-copy">Viewer 只保存节点 API 地址和 Token；实时、历史、轨迹、负载数据每次从子站 API 拉取。</div>
          </div>
          <button class="btn" id="btn-clear-form" type="button">清空</button>
        </div>
        <div class="grid" style="margin-top:14px">
          <input id="node-id" type="hidden">
          <div class="field"><label>名称</label><input id="node-name" type="text" placeholder="例如 东门基站"></div>
          <div class="field"><label>API 地址</label><input id="node-url" type="text" placeholder="http://192.168.1.10:4600"></div>
          <div class="field"><label>Token</label><input id="node-token" type="password" placeholder="编辑时留空保留原 Token"></div>
          <div class="checks"><label><input id="node-enabled" type="checkbox" checked> 启用节点</label></div>
        </div>
        <div class="row-actions" style="margin-top:14px">
          <button class="btn" id="btn-test-node" type="button">测试连接</button>
          <button class="btn warn" id="btn-save-node" type="button">保存节点</button>
        </div>
        <div id="node-status" class="status">-</div>
      </div>
      <div class="card">
        <div class="section-head">
          <div>
            <h2>批量远程管理</h2>
            <div class="section-copy">对勾选节点执行远程维护。目前支持重启主程序和更新识别库。</div>
          </div>
        </div>
        <div class="row-actions" style="margin-top:14px">
          <button class="btn ghost" id="btn-select-all" type="button">全选</button>
          <button class="btn ghost" id="btn-select-online" type="button">选择在线</button>
          <button class="btn warn" id="btn-remote-restart" type="button">重启程序</button>
          <button class="btn" id="btn-remote-models" type="button">更新识别库</button>
        </div>
        <div id="bulk-status" class="status">-</div>
      </div>
      <div class="card">
        <div class="list-head">
          <div>
            <h2>节点基本信息</h2>
            <div class="section-copy">点击基本信息卡片在右侧查看完整信息；点击负载卡片显示详细负载曲线。</div>
          </div>
        </div>
        <div id="node-basic-list" class="list-wrap"></div>
      </div>
      <div class="card">
        <div class="list-head">
          <div>
            <h2>节点负载</h2>
            <div class="section-copy">显示当前健康状态和最近一次负载数据。</div>
          </div>
        </div>
        <div id="node-load-list" class="list-wrap"></div>
      </div>
      <div class="card">
        <div class="list-head">
          <div>
            <h2>扫描数据</h2>
            <div class="section-copy">每个节点共扫到 / 当前在线的飞机统计。</div>
          </div>
        </div>
        <div id="node-scan-list" class="list-wrap"></div>
      </div>
    </div>
    <div class="stack">
      <div class="stack-label">详情</div>
      <div class="card detail-card">
        <div class="section-head">
          <div>
            <h2 id="detail-title">节点详情</h2>
            <div class="section-copy" id="detail-copy">选择左侧卡片查看完整信息、负载图或远程登录入口。</div>
          </div>
        </div>
        <div class="row-actions" style="margin-top:14px">
          <button class="btn" id="btn-edit-selected" type="button" disabled>编辑</button>
          <button class="btn" id="btn-sso-selected" type="button" disabled>生成 SSO 登录</button>
          <button class="btn ghost" id="btn-open-sso" type="button" disabled>一键登录</button>
          <button class="btn warn" id="btn-delete-selected" type="button" disabled>删除</button>
        </div>
        <div id="detail-body" class="detail-body"></div>
        <canvas id="load-chart" class="node-load-chart"></canvas>
        <div id="detail-status" class="status">-</div>
      </div>
    </div>
  </div>
"""
    extra_css = """
.node-manager-grid{grid-template-columns:minmax(460px,1.06fr) minmax(420px,.94fr)}
.node-card{border:1px solid var(--border);border-radius:4px;background:var(--card2);padding:12px;display:grid;gap:9px;cursor:pointer}
.node-card:hover{border-color:var(--blue);background:color-mix(in srgb,var(--blue) 7%,var(--card2))}
.node-card.active{border-color:var(--blue);box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--blue) 22%,transparent)}
.node-card-head{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:9px;align-items:center}
.node-card-title{font:700 14px/1.2 var(--font-ui);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.node-card-meta{font:600 12px/1.45 var(--font-ui);color:var(--muted);word-break:break-word}
.node-pill{font:700 11px/1 var(--font-ui);border:1px solid var(--border);border-radius:4px;padding:4px 6px;color:var(--muted);white-space:nowrap}
.node-pill.ok{color:var(--green);border-color:color-mix(in srgb,var(--green) 45%,var(--border))}
.node-pill.err{color:#ff9b9b;border-color:color-mix(in srgb,#ff9b9b 45%,var(--border))}
.node-metrics{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px}
.node-metric{border:1px solid var(--border);border-radius:4px;background:var(--card);padding:8px;min-width:0}
.node-metric .k{font-size:11px;color:var(--muted)}
.node-metric .v{font:700 15px/1.2 var(--font-ui);margin-top:4px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.detail-card{position:sticky;top:12px}
.detail-body{margin-top:14px;display:grid;gap:8px}
.detail-row{display:grid;grid-template-columns:150px minmax(0,1fr);gap:10px;border-bottom:1px solid var(--border);padding:8px 0}
.detail-row .k{color:var(--muted);font-size:12px}
.detail-row .v{word-break:break-word;font:600 13px/1.45 var(--font-ui)}
.node-load-chart{display:none;width:100%;height:360px;margin-top:14px;border:1px solid var(--border);border-radius:4px;background:var(--card2)}
.node-load-chart.show{display:block}
@media (max-width:1200px){.node-manager-grid{grid-template-columns:1fr}.detail-card{position:relative;top:auto}}
"""
    script = r"""
function qs(id){ return document.getElementById(id); }
function qsa(sel){ return Array.prototype.slice.call(document.querySelectorAll(sel) || []); }
function enc(v){ return String(v == null ? '' : v).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;'); }
function pageHeaders(extra){ var h={'X-LightRID-Page':'1'}; if(extra) Object.assign(h, extra); return h; }
async function api(path, opts){
  const r = await fetch(path, Object.assign({cache:'no-store', headers:pageHeaders()}, opts || {}));
  const d = await r.json().catch(()=>({}));
  if(r.status === 401){ location.href='/'; throw new Error('login required'); }
  if(!r.ok || d.ok === false) throw new Error(d.error || ('HTTP ' + r.status));
  return d;
}
async function post(path, body){ return api(path, {method:'POST', headers:pageHeaders({'Content-Type':'application/json'}), body:JSON.stringify(body || {})}); }
function setStatus(id, text, err){ var el=qs(id); if(el){ el.textContent=text||'-'; el.classList.toggle('err', !!err); } }
function fmtPct(v){ var n=Number(v); return isFinite(n) ? n.toFixed(1)+'%' : '—'; }
function fmtTemp(v){ var n=Number(v); return isFinite(n) ? n.toFixed(1)+'°C' : '—'; }
function fmtMs(v){ var n=Number(v); return isFinite(n) ? Math.round(n)+'ms' : '—'; }
function fmtTime(ts){ var n=Number(ts); if(!isFinite(n) || n <= 0) return '—'; try{return new Date(n*1000).toLocaleString();}catch(_e){return String(ts);} }
var state = {nodes:[], records:[], selectedId:null, selectedSsoUrl:'', checkedIds:{}};
function nodeById(id){ return state.nodes.find(function(n){ return Number(n.id) === Number(id); }) || null; }
function recordById(id){ return state.records.find(function(n){ return Number(n.id) === Number(id); }) || null; }
function selectedIds(){ return qsa('.node-select:checked').map(function(x){ return Number(x.value || 0); }).filter(Boolean); }
function cardShell(n, kind, inner){
  var ok = !!n.ok;
  return '<div class="node-card '+(Number(state.selectedId)===Number(n.id)?'active':'')+'" data-id="'+enc(n.id)+'" data-kind="'+enc(kind)+'">'
    + '<div class="node-card-head"><input class="node-select" type="checkbox" value="'+enc(n.id)+'" '+(state.checkedIds[Number(n.id)]?'checked ':'')+(ok?'data-online="1"':'')+'>'
    + '<div class="node-card-title">'+enc(n.name || n.base_url || ('节点 '+n.id))+'</div>'
    + '<span class="node-pill '+(ok?'ok':'err')+'">'+(ok?'在线':'离线')+'</span></div>' + inner + '</div>';
}
function metricBox(k, v){ return '<div class="node-metric"><div class="k">'+enc(k)+'</div><div class="v">'+enc(v)+'</div></div>'; }
function renderLists(){
  var basic = qs('node-basic-list'), load = qs('node-load-list'), scan = qs('node-scan-list');
  if(!state.nodes.length){
    var empty = '<div class="empty-state">尚未添加节点。</div>';
    basic.innerHTML = empty; load.innerHTML = empty; scan.innerHTML = empty; return;
  }
  basic.innerHTML = state.nodes.map(function(n){
    var station = n.station || {}, service = n.service || {};
    return cardShell(n, 'basic',
      '<div class="node-card-meta">'+enc(n.base_url || '-')+'</div>'
      + '<div class="node-metrics">'
      + metricBox('延迟', fmtMs(n.latency_ms))
      + metricBox('基站', station.name || n.name || '—')
      + metricBox('采集', service.sniff_state || (n.enabled ? '—' : 'disabled'))
      + '</div>'
      + (n.error ? '<div class="node-card-meta">'+enc(String(n.error).slice(0,180))+'</div>' : '')
    );
  }).join('');
  load.innerHTML = state.nodes.map(function(n){
    var svc = n.service || {}, host = n.host || {};
    return cardShell(n, 'load',
      '<div class="node-metrics">'
      + metricBox('CPU', fmtPct(host.cpu_percent || svc.cpu_percent))
      + metricBox('内存', fmtPct(host.mem_percent || svc.mem_percent))
      + metricBox('温度', fmtTemp(host.temperature_c || svc.temperature_c))
      + '</div>'
      + '<div class="node-card-meta">负载 '+enc(host.load1 == null ? '—' : host.load1)+' / '+enc(host.load5 == null ? '—' : host.load5)+' / '+enc(host.load15 == null ? '—' : host.load15)+'</div>'
    );
  }).join('');
  scan.innerHTML = state.nodes.map(function(n){
    return cardShell(n, 'scan',
      '<div class="node-metrics">'
      + metricBox('共扫到', String(n.count || 0))
      + metricBox('当前在线', String(n.online_count || 0))
      + metricBox('状态码', n.status_code == null ? '—' : String(n.status_code))
      + '</div>'
      + '<div class="node-card-meta">更新时间 '+enc(fmtTime(n.fetched_at))+'</div>'
    );
  }).join('');
  updateSelectionButtons();
}
function detailRows(rows){
  return rows.map(function(r){ return '<div class="detail-row"><div class="k">'+enc(r[0])+'</div><div class="v">'+enc(r[1])+'</div></div>'; }).join('');
}
function showBasic(id){
  var n = nodeById(id) || {};
  var station = n.station || {}, svc = n.service || {}, rec = recordById(id) || {};
  state.selectedId = Number(id); state.selectedSsoUrl = '';
  qs('detail-title').textContent = n.name || '节点详情';
  qs('detail-copy').textContent = '完整基础信息';
  qs('load-chart').classList.remove('show');
  qs('detail-body').innerHTML = detailRows([
    ['名称', n.name || '—'], ['API 地址', n.base_url || '—'], ['启用', n.enabled ? '是' : '否'], ['在线', n.ok ? '是' : '否'],
    ['状态码', n.status_code == null ? '—' : n.status_code], ['延迟', fmtMs(n.latency_ms)], ['错误', n.error || '—'],
    ['基站名称', station.name || '—'], ['基站纬度', station.lat == null ? '—' : station.lat], ['基站经度', station.lon == null ? '—' : station.lon],
    ['采集状态', svc.sniff_state || '—'], ['采集消息', svc.sniff_msg || '—'], ['采集网卡', svc.sniff_iface || '—'],
    ['Token', rec.token_configured ? '已配置' : '未配置'], ['创建时间', fmtTime(rec.created_at)], ['更新时间', fmtTime(rec.updated_at)]
  ]);
  setStatus('detail-status', '-', false);
  renderLists();
}
async function showLoad(id){
  var n = nodeById(id) || {};
  state.selectedId = Number(id); state.selectedSsoUrl = '';
  qs('detail-title').textContent = (n.name || '节点') + ' 负载';
  qs('detail-copy').textContent = '最近负载曲线';
  qs('detail-body').innerHTML = detailRows([['API 地址', n.base_url || '—'], ['当前状态', n.ok ? '在线' : '离线'], ['扫描数据', String(n.online_count || 0) + '/' + String(n.count || 0)]]);
  setStatus('detail-status', '正在读取负载...', false);
  renderLists();
  try{
    const d = await api('/api/nodes/metrics?node_id=' + encodeURIComponent(id) + '&window=12h');
    drawChart(Array.isArray(d.items) ? d.items : []);
    setStatus('detail-status', d.items && d.items.length ? ('样本 ' + d.items.length) : '没有可用负载样本；请确认子站已启用节点负载记录。', !(d.items && d.items.length));
  }catch(e){
    drawChart([]);
    setStatus('detail-status', '负载读取失败: ' + (e.message || e), true);
  }
}
function showScan(id){
  var n = nodeById(id) || {};
  state.selectedId = Number(id); state.selectedSsoUrl = '';
  qs('detail-title').textContent = (n.name || '节点') + ' 扫描数据';
  qs('detail-copy').textContent = '当前聚合统计';
  qs('load-chart').classList.remove('show');
  qs('detail-body').innerHTML = detailRows([
    ['共扫到', n.count || 0], ['当前在线', n.online_count || 0], ['最后刷新', fmtTime(n.fetched_at)],
    ['采集状态', (n.service || {}).sniff_state || '—'], ['采集消息', (n.service || {}).sniff_msg || n.error || '—']
  ]);
  setStatus('detail-status', '-', false);
  renderLists();
}
function drawChart(items){
  var canvas = qs('load-chart'); canvas.classList.add('show');
  var ctx = canvas.getContext('2d'), rect = canvas.getBoundingClientRect(), dpr = window.devicePixelRatio || 1;
  var w = Math.max(320, Math.floor(rect.width || canvas.clientWidth || 640)), h = 360;
  canvas.width = Math.floor(w*dpr); canvas.height = Math.floor(h*dpr); canvas.style.height = h+'px';
  ctx.setTransform(dpr,0,0,dpr,0,0); ctx.clearRect(0,0,w,h);
  ctx.fillStyle = getComputedStyle(document.body).getPropertyValue('--card2') || '#252423'; ctx.fillRect(0,0,w,h);
  ctx.strokeStyle = getComputedStyle(document.body).getPropertyValue('--border') || '#3b3a39'; ctx.strokeRect(0.5,0.5,w-1,h-1);
  var rows = (items || []).filter(function(x){ return x && Number(x.ts || 0) > 0; });
  if(!rows.length){ ctx.fillStyle='#c8c6c4'; ctx.fillText('没有负载样本', 18, 30); return; }
  rows.sort(function(a,b){ return Number(a.ts||0)-Number(b.ts||0); });
  var minTs = Number(rows[0].ts), maxTs = Number(rows[rows.length-1].ts); if(maxTs <= minTs) maxTs = minTs + 1;
  var defs = [['cpu','#2899f5','CPU'],['mem','#92c353','内存'],['load','#c19c00','负载'],['temp','#f7630c','温度']];
  var pad = {l:42,r:16,t:20,b:28}, plotW = w-pad.l-pad.r, plotH = h-pad.t-pad.b;
  ctx.strokeStyle = 'rgba(200,198,196,.22)'; ctx.lineWidth = 1;
  for(var gy=0; gy<=4; gy++){ var y=pad.t+(plotH*gy/4); ctx.beginPath(); ctx.moveTo(pad.l,y); ctx.lineTo(w-pad.r,y); ctx.stroke(); }
  defs.forEach(function(def){
    var key=def[0], color=def[1], label=def[2], has=false;
    ctx.beginPath();
    rows.forEach(function(r){
      var v = Number(r[key]);
      if(!isFinite(v)) return;
      if(key === 'temp') v = Math.max(0, Math.min(100, v));
      else v = Math.max(0, Math.min(100, v));
      var x = pad.l + ((Number(r.ts)-minTs)/(maxTs-minTs))*plotW;
      var y = pad.t + (1 - v/100)*plotH;
      if(!has){ ctx.moveTo(x,y); has=true; } else ctx.lineTo(x,y);
    });
    ctx.strokeStyle = color; ctx.lineWidth = 2; ctx.stroke();
    ctx.fillStyle = color; ctx.fillText(label, pad.l + defs.indexOf(def)*68, 14);
  });
}
async function loadAll(){
  setStatus('bulk-status', '正在刷新...', false);
  const records = await api('/api/nodes');
  const agg = await api('/api/aggregate');
  state.records = records.items || [];
  state.nodes = agg.nodes || [];
  renderLists();
  if(state.selectedId && nodeById(state.selectedId)) showBasic(state.selectedId);
  setStatus('bulk-status', '节点 ' + String(agg.online_node_count || 0) + '/' + String(agg.node_count || 0) + ' 在线，飞机 ' + String(agg.online_drone_count || 0) + '/' + String(agg.drone_count || 0), false);
}
function clearForm(){ qs('node-id').value=''; qs('node-name').value=''; qs('node-url').value=''; qs('node-token').value=''; qs('node-enabled').checked=true; setStatus('node-status','-',false); }
async function saveNode(testOnly){
  var body = {id:Number(qs('node-id').value||0), name:qs('node-name').value, base_url:qs('node-url').value, token:qs('node-token').value, enabled:qs('node-enabled').checked};
  setStatus('node-status', testOnly ? '正在测试...' : '正在保存...', false);
  var d = await post(testOnly ? '/api/nodes/test' : '/api/nodes', body);
  if(testOnly){ var n=d.node||{}; setStatus('node-status', '测试完成：' + (n.ok ? '在线' : '离线') + (n.error ? ' · ' + n.error : ''), !n.ok); return; }
  clearForm(); await loadAll(); setStatus('node-status','已保存。',false);
}
function editSelected(){
  var rec = recordById(state.selectedId); if(!rec) return;
  qs('node-id').value = rec.id; qs('node-name').value = rec.name || ''; qs('node-url').value = rec.base_url || ''; qs('node-token').value = ''; qs('node-enabled').checked = !!rec.enabled;
  setStatus('node-status', '编辑模式：Token 留空会保留原值。', false);
  window.scrollTo({top:0, behavior:'smooth'});
}
async function deleteSelected(){
  if(!state.selectedId || !confirm('删除选中的节点？')) return;
  await post('/api/nodes/delete', {id:state.selectedId});
  state.selectedId = null; state.selectedSsoUrl = ''; qs('detail-body').innerHTML=''; qs('load-chart').classList.remove('show');
  await loadAll();
}
async function createSso(){
  if(!state.selectedId) return;
  setStatus('detail-status', '正在生成 SSO 登录链接...', false);
  var d = await post('/api/nodes/sso', {node_id:state.selectedId});
  state.selectedSsoUrl = d.url || '';
  qs('detail-body').innerHTML = detailRows([['SSO URL', state.selectedSsoUrl || '—'], ['节点', (nodeById(state.selectedId)||{}).name || state.selectedId], ['说明', '链接由子站 API 创建，按子站设置控制有效期和单次使用。']]);
  qs('btn-open-sso').disabled = !state.selectedSsoUrl;
  setStatus('detail-status', state.selectedSsoUrl ? '已生成，可点击一键登录。' : '子站没有返回 URL。', !state.selectedSsoUrl);
}
async function remoteOp(op){
  var ids = selectedIds();
  if(!ids.length && state.selectedId) ids = [state.selectedId];
  if(!ids.length){ setStatus('bulk-status','请先勾选节点或选择一个节点。',true); return; }
  if(op === 'restart' && !confirm('确认重启 ' + ids.length + ' 个节点的主程序？')) return;
  setStatus('bulk-status', '正在执行...', false);
  var d = await post('/api/nodes/remote', {node_ids:ids, operation:op});
  var rows = d.results || [];
  setStatus('bulk-status', rows.map(function(r){ return (r.name || r.id) + ': ' + (r.ok ? '完成' : ('失败 ' + (r.error || ''))); }).join('\n'), rows.some(function(r){ return !r.ok; }));
  setTimeout(loadAll, 1200);
}
function updateSelectionButtons(){
  var has = !!state.selectedId;
  qs('btn-edit-selected').disabled = !has;
  qs('btn-sso-selected').disabled = !has;
  qs('btn-delete-selected').disabled = !has;
  qs('btn-open-sso').disabled = !state.selectedSsoUrl;
}
document.addEventListener('click', function(ev){
  var cb = ev.target.closest('.node-select');
  if(cb){ state.checkedIds[Number(cb.value || 0)] = !!cb.checked; ev.stopPropagation(); return; }
  var card = ev.target.closest('.node-card');
  if(card){
    var id = Number(card.getAttribute('data-id') || 0), kind = card.getAttribute('data-kind') || 'basic';
    if(kind === 'load') showLoad(id); else if(kind === 'scan') showScan(id); else showBasic(id);
  }
});
qs('btn-back').onclick = function(){ location.href='/'; };
qs('btn-settings').onclick = function(){ location.href='/settings'; };
qs('btn-refresh').onclick = function(){ loadAll().catch(function(e){ setStatus('bulk-status', e.message || e, true); }); };
qs('btn-clear-form').onclick = clearForm;
qs('btn-test-node').onclick = function(){ saveNode(true).catch(function(e){ setStatus('node-status', e.message || e, true); }); };
qs('btn-save-node').onclick = function(){ saveNode(false).catch(function(e){ setStatus('node-status', e.message || e, true); }); };
qs('btn-edit-selected').onclick = editSelected;
qs('btn-delete-selected').onclick = function(){ deleteSelected().catch(function(e){ setStatus('detail-status', e.message || e, true); }); };
qs('btn-sso-selected').onclick = function(){ createSso().catch(function(e){ setStatus('detail-status', e.message || e, true); }); };
qs('btn-open-sso').onclick = function(){ if(state.selectedSsoUrl) window.open(state.selectedSsoUrl, '_blank', 'noopener'); };
qs('btn-select-all').onclick = function(){ qsa('.node-select').forEach(function(x){ x.checked = true; state.checkedIds[Number(x.value || 0)] = true; }); };
qs('btn-select-online').onclick = function(){ qsa('.node-select').forEach(function(x){ var on=x.getAttribute('data-online') === '1'; x.checked = on; state.checkedIds[Number(x.value || 0)] = on; }); };
qs('btn-remote-restart').onclick = function(){ remoteOp('restart').catch(function(e){ setStatus('bulk-status', e.message || e, true); }); };
qs('btn-remote-models').onclick = function(){ remoteOp('update_models').catch(function(e){ setStatus('bulk-status', e.message || e, true); }); };
loadAll().catch(function(e){ setStatus('bulk-status', e.message || e, true); });
"""
    return station_page("节点管理器", body, script, extra_css=extra_css)
