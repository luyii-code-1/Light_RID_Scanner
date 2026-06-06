"""Station-styled node manager page for the viewer."""

from __future__ import annotations

from viewer.paths import ASSETS_DIR
from viewer.ui_common import station_page


def _nodes_center_asset_url() -> str:
    asset_url = "/assets/vue/nodes-center.js"
    asset_path = ASSETS_DIR / "vue" / "nodes-center.js"
    try:
        st = asset_path.stat()
        return f"{asset_url}?v={int(st.st_mtime)}-{int(st.st_size)}"
    except OSError:
        return asset_url


def build_nodes_page() -> str:
    body = """
  <div class="settings-sticky-head">
    <div class="topbar node-topbar">
      <div class="node-hero">
        <div class="node-hero-icon">◎</div>
        <div>
          <div class="title">节点管理器</div>
          <div class="sub">管理远程节点</div>
        </div>
      </div>
      <div class="actions">
        <button class="btn" id="btn-back" type="button">返回实时/历史</button>
        <button class="btn" id="btn-settings" type="button">Viewer 设置</button>
        <button class="btn" id="btn-theme" type="button">浅色</button>
        <button class="btn ghost" id="btn-refresh" type="button">刷新</button>
      </div>
    </div>
  </div>
  <div class="visual-grid node-manager-grid">
    <div class="stack">
      <div class="stack-label">节点</div>
      <div class="card node-glass-card" id="node-editor">
        <div class="section-head">
          <div>
            <h2>添加 / 编辑节点</h2>
            <div class="section-copy">保存节点连接信息</div>
          </div>
          <button class="btn ghost" id="btn-clear-form" type="button">清空</button>
        </div>
        <div class="grid node-form-grid">
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
      <div class="card node-glass-card">
        <div class="section-head">
          <div>
            <h2>批量远程管理</h2>
            <div class="section-copy">对勾选节点执行远程操作</div>
          </div>
        </div>
        <div class="row-actions" style="margin-top:14px">
          <button class="btn ghost" id="btn-select-all" type="button">全选</button>
          <button class="btn ghost" id="btn-select-online" type="button">仅在线</button>
          <button class="btn warn" id="btn-remote-restart" type="button">重启程序</button>
          <button class="btn" id="btn-remote-models" type="button">更新识别库</button>
        </div>
        <div id="bulk-status" class="status">-</div>
      </div>
      <div class="card node-glass-card">
        <div class="list-head">
          <div>
            <h2>节点基本信息</h2>
            <div class="section-copy">点击节点查看详情</div>
          </div>
        </div>
        <div id="node-basic-list" class="list-wrap"></div>
      </div>
      <div class="card node-glass-card">
        <div class="list-head">
          <div>
            <h2>节点负载</h2>
            <div class="section-copy">节点负载趋势</div>
          </div>
        </div>
        <div id="node-load-list" class="list-wrap"></div>
      </div>
      <div class="card node-glass-card">
        <div class="list-head">
          <div>
            <h2>扫描数据</h2>
            <div class="section-copy">扫描统计</div>
          </div>
        </div>
        <div id="node-scan-list" class="list-wrap"></div>
      </div>
    </div>
    <div class="stack">
      <div class="stack-label">节点详情</div>
      <div class="card detail-card node-glass-card">
        <div class="section-head">
          <div>
            <h2 id="detail-title">节点详情</h2>
            <div class="section-copy" id="detail-copy">节点详情与负载</div>
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
.node-manager-grid{grid-template-columns:minmax(520px,1.08fr) minmax(420px,.92fr)}
.node-topbar{padding:14px 18px;border:1px solid color-mix(in srgb,var(--border) 92%,transparent);border-radius:22px;background:linear-gradient(180deg,color-mix(in srgb,var(--card) 96%,transparent),color-mix(in srgb,var(--card2) 94%,transparent));box-shadow:0 10px 28px rgba(0,0,0,.18)}
.node-hero{display:flex;align-items:center;gap:14px}
.node-hero-icon{width:40px;height:40px;border-radius:12px;display:grid;place-items:center;background:color-mix(in srgb,var(--blue) 12%,var(--card2));color:var(--blue);font:700 18px/1 var(--font-ui);box-shadow:inset 0 0 0 1px color-mix(in srgb,var(--blue) 18%,transparent)}
.node-glass-card{border-radius:22px;box-shadow:0 8px 24px rgba(0,0,0,.18);background:color-mix(in srgb,var(--card) 96%,transparent)}
.node-form-grid{margin-top:14px}
.list-wrap{display:grid;gap:10px}
.node-list-stack{display:grid;gap:12px}
.node-sort-row{display:grid;grid-template-columns:repeat(6,minmax(0,1fr));gap:8px}
.node-sort-btn{height:34px;border:1px solid color-mix(in srgb,var(--border) 92%,transparent);border-radius:10px;background:color-mix(in srgb,var(--card2) 92%,transparent);color:var(--muted);font:600 12px/1 var(--font-ui);cursor:pointer;transition:background-color 160ms ease,border-color 160ms ease,box-shadow 160ms ease,transform 160ms ease}
.node-sort-btn:hover{background:color-mix(in srgb,var(--blue) 7%,var(--card2));border-color:color-mix(in srgb,var(--blue) 20%,var(--border));transform:translateY(-1px)}
.node-sort-btn.active{color:var(--txt);border-color:color-mix(in srgb,var(--blue) 26%,var(--border));background:color-mix(in srgb,var(--blue) 10%,var(--card2))}
.node-sort-btn.sorted-asc::after,.node-sort-btn.sorted-desc::after{content:"";display:inline-block;width:8px;height:10px;margin-left:6px;vertical-align:-1px;background-repeat:no-repeat;background-position:center;background-size:8px 10px}
.node-sort-btn.sorted-asc::after{background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="8" height="10" viewBox="0 0 8 10"><path d="M4 1 7 4H1L4 1Z" fill="%236ea8ff"/></svg>')}
.node-sort-btn.sorted-desc::after{background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="8" height="10" viewBox="0 0 8 10"><path d="M4 9 1 6h6L4 9Z" fill="%236ea8ff"/></svg>')}
.node-card-list{display:grid;gap:10px}
.node-card{border:1px solid color-mix(in srgb,var(--border) 90%,transparent);border-radius:18px;background:color-mix(in srgb,var(--card2) 92%,transparent);padding:14px;display:grid;gap:10px;cursor:pointer;transition:background-color 160ms ease,border-color 160ms ease,box-shadow 160ms ease,transform 160ms ease}
.node-card:hover{border-color:color-mix(in srgb,var(--blue) 22%,var(--border));background:color-mix(in srgb,var(--blue) 6%,var(--card2));transform:translateY(-1px);box-shadow:0 10px 26px rgba(0,0,0,.22)}
.node-card.active{border-color:color-mix(in srgb,var(--blue) 34%,var(--border));background:color-mix(in srgb,var(--blue) 8%,var(--card2));box-shadow:inset 3px 0 0 var(--blue),0 10px 26px rgba(37,99,235,.12)}
.node-card-head{display:grid;grid-template-columns:auto minmax(0,1fr) auto;gap:10px;align-items:center}
.node-card-title{font:700 14px/1.25 var(--font-ui);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.node-card-meta{font:600 12px/1.45 var(--font-ui);color:var(--muted);word-break:break-word}
.node-pill{font:700 11px/1 var(--font-ui);border:1px solid color-mix(in srgb,var(--border) 88%,transparent);border-radius:9px;padding:5px 7px;color:var(--muted);white-space:nowrap;background:color-mix(in srgb,var(--card) 90%,transparent)}
.node-pill.ok{color:#58d191;border-color:rgba(34,197,94,.28);background:rgba(20,83,45,.34)}
.node-pill.err{color:#ffb272;border-color:rgba(245,158,11,.30);background:rgba(124,45,18,.32)}
.node-metrics{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:8px}
.node-metric{border:1px solid color-mix(in srgb,var(--border) 86%,transparent);border-radius:14px;background:color-mix(in srgb,var(--surface-tonal, #17283d) 72%,var(--card));padding:9px 10px;min-width:0}
.node-metric .k{font-size:11px;color:var(--muted)}
.node-metric .v{font:700 15px/1.2 var(--font-ui);margin-top:4px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.detail-card{position:sticky;top:12px}
.detail-body{margin-top:14px;display:grid;gap:8px}
.detail-row{display:grid;grid-template-columns:150px minmax(0,1fr);gap:10px;border-bottom:1px solid color-mix(in srgb,var(--border) 84%,transparent);padding:8px 0}
.detail-row .k{color:var(--muted);font-size:12px}
.detail-row .v{word-break:break-word;font:600 13px/1.45 var(--font-ui)}
.node-load-chart{display:none;width:100%;height:360px;margin-top:14px;border:1px solid color-mix(in srgb,var(--border) 84%,transparent);border-radius:18px;background:color-mix(in srgb,var(--card2) 96%,transparent)}
.node-load-chart.show{display:block}
body.theme-dark .node-topbar,
body.theme-dark .node-glass-card{background:color-mix(in srgb,var(--card) 96%,#08111d)}
body.theme-dark .node-metric{background:color-mix(in srgb,var(--surface-tonal, #12253b) 76%,var(--card))}
body.theme-light .node-topbar{box-shadow:0 10px 28px rgba(15,23,42,.08)}
body.theme-light .node-glass-card{box-shadow:0 8px 24px rgba(15,23,42,.08);background:color-mix(in srgb,var(--card) 96%,white)}
body.theme-light .node-sort-btn{background:color-mix(in srgb,var(--card2) 92%,white)}
body.theme-light .node-sort-btn.sorted-asc::after{background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="8" height="10" viewBox="0 0 8 10"><path d="M4 1 7 4H1L4 1Z" fill="%232563eb"/></svg>')}
body.theme-light .node-sort-btn.sorted-desc::after{background-image:url('data:image/svg+xml;utf8,<svg xmlns="http://www.w3.org/2000/svg" width="8" height="10" viewBox="0 0 8 10"><path d="M4 9 1 6h6L4 9Z" fill="%232563eb"/></svg>')}
body.theme-light .node-card{background:color-mix(in srgb,var(--card2) 92%,white)}
body.theme-light .node-card:hover{box-shadow:0 10px 26px rgba(15,23,42,.08)}
body.theme-light .node-pill{background:color-mix(in srgb,var(--card) 90%,white)}
body.theme-light .node-pill.ok{color:#0f8a49;border-color:rgba(22,163,74,.22);background:rgba(220,252,231,.9)}
body.theme-light .node-pill.err{color:#c2410c;border-color:rgba(245,158,11,.26);background:rgba(255,247,237,.94)}
body.theme-light .node-metric{background:color-mix(in srgb,var(--surface-tonal, #eaf2ff) 34%,white)}
body.theme-light .node-load-chart{background:color-mix(in srgb,var(--card2) 96%,white)}
@media (max-width:1200px){.node-manager-grid{grid-template-columns:1fr}.detail-card{position:relative;top:auto}}
@media (max-width:760px){.node-sort-row{grid-template-columns:repeat(2,minmax(0,1fr))}.node-metrics{grid-template-columns:1fr}.node-topbar{padding:12px 14px}}
"""
    script = r"""
function qs(id){ return document.getElementById(id); }
function qsa(sel){ return Array.prototype.slice.call(document.querySelectorAll(sel) || []); }
function pageHeaders(extra){ var h={'X-LightRID-Page':'1'}; if(extra) Object.assign(h, extra); return h; }
function loadTheme(){
  try{ var s = localStorage.getItem('rid_ui_theme'); if(s === 'dark' || s === 'light') return s; }catch(_e){}
  try{ if(window.matchMedia && window.matchMedia('(prefers-color-scheme: light)').matches) return 'light'; }catch(_e){}
  return 'dark';
}
function applyTheme(theme){
  var light = (theme === 'light');
  document.body.classList.toggle('theme-light', light);
  document.body.classList.toggle('theme-dark', !light);
  try{ localStorage.setItem('rid_ui_theme', light ? 'light' : 'dark'); }catch(_e){}
  if(qs('btn-theme')) qs('btn-theme').textContent = light ? '深色' : '浅色';
}
async function api(path, opts){
  const r = await fetch(path, Object.assign({cache:'no-store', headers:pageHeaders()}, opts || {}));
  const d = await r.json().catch(()=>({}));
  if(r.status === 401){ location.href='/'; throw new Error('login required'); }
  if(!r.ok || d.ok === false) throw new Error(d.error || ('HTTP ' + r.status));
  return d;
}
async function post(path, body){ return api(path, {method:'POST', headers:pageHeaders({'Content-Type':'application/json'}), body:JSON.stringify(body || {})}); }
function setStatus(id, text, err){ var el=qs(id); if(el){ el.textContent=text||'-'; el.classList.toggle('err', !!err); } }
function fmtMs(v){ var n=Number(v); return isFinite(n) ? Math.round(n)+'ms' : '—'; }
function fmtTime(ts){ var n=Number(ts); if(!isFinite(n) || n <= 0) return '—'; try{return new Date(n*1000).toLocaleString();}catch(_e){return String(ts);} }
var state = {nodes:[], records:[], selectedId:null, selectedSsoUrl:'', checkedIds:{}};
function nodeById(id){ return state.nodes.find(function(n){ return Number(n.id) === Number(id); }) || null; }
function recordById(id){ return state.records.find(function(n){ return Number(n.id) === Number(id); }) || null; }
function selectedIds(){ return Object.keys(state.checkedIds || {}).filter(function(key){ return !!state.checkedIds[key]; }).map(function(key){ return Number(key); }).filter(Boolean); }
function ssoCacheKey(node){
  node = node || {};
  return 'rid_viewer_node_sso_' + String(node.id || '') + '_' + String(node.base_url || '').replace(/[^A-Za-z0-9]+/g, '_');
}
function readCachedSso(node){
  try{
    var raw = localStorage.getItem(ssoCacheKey(node));
    if(!raw) return '';
    var item = JSON.parse(raw);
    var url = String((item && item.url) || '');
    var exp = Number((item && item.expires_at) || 0);
    if(exp && exp <= Date.now() / 1000){
      localStorage.removeItem(ssoCacheKey(node));
      return '';
    }
    return url;
  }catch(_e){ return ''; }
}
function writeCachedSso(node, payload){
  try{
    var url = String((payload && payload.url) || '');
    if(!url) return;
    localStorage.setItem(ssoCacheKey(node), JSON.stringify({url:url, expires_at:Number(payload.expires_at || 0), saved_at:Date.now()/1000}));
  }catch(_e){}
}
function detailRows(rows){
  return rows.map(function(r){ return '<div class="detail-row"><div class="k">'+String(r[0] || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')+'</div><div class="v">'+String(r[1] || '').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;')+'</div></div>'; }).join('');
}
function renderLists(){
  if(window.__RID_NODE_CENTER_BRIDGE__ && typeof window.__RID_NODE_CENTER_BRIDGE__.update === 'function'){
    window.__RID_NODE_CENTER_BRIDGE__.update({nodes:state.nodes, selectedId:state.selectedId, checkedIds:state.checkedIds});
  }
  updateSelectionButtons();
}
function showBasic(id){
  var n = nodeById(id) || {};
  var station = n.station || {}, svc = n.service || {}, rec = recordById(id) || {};
  state.selectedId = Number(id);
  state.selectedSsoUrl = readCachedSso(n);
  qs('detail-title').textContent = n.name || '节点详情';
  qs('detail-copy').textContent = '';
  qs('load-chart').classList.remove('show');
  qs('detail-body').innerHTML = detailRows([
    ['名称', n.name || '—'], ['API 地址', n.base_url || '—'], ['启用', n.enabled ? '是' : '否'], ['在线', n.ok ? '是' : '否'],
    ['状态码', n.status_code == null ? '—' : n.status_code], ['延迟', fmtMs(n.latency_ms)], ['错误', n.error || '—'],
    ['站点名称', station.name || '—'], ['站点纬度', station.lat == null ? '—' : station.lat], ['站点经度', station.lon == null ? '—' : station.lon],
    ['扫描状态', svc.sniff_state || '—'], ['扫描消息', svc.sniff_msg || '—'], ['网卡', svc.sniff_iface || '—'],
    ['Token', rec.token_configured ? '已配置' : '未配置'], ['创建时间', fmtTime(rec.created_at)], ['更新时间', fmtTime(rec.updated_at)]
  ]);
  setStatus('detail-status', state.selectedSsoUrl ? 'SSO 登录链接就绪' : '-', false);
  renderLists();
}
async function showLoad(id){
  var n = nodeById(id) || {};
  state.selectedId = Number(id);
  state.selectedSsoUrl = readCachedSso(n);
  qs('detail-title').textContent = (n.name || '节点') + ' 负载';
  qs('detail-copy').textContent = '12 小时负载曲线';
  qs('detail-body').innerHTML = detailRows([['API 地址', n.base_url || '—'], ['当前状态', n.ok ? '在线' : '离线'], ['扫描数据', String(n.online_count || 0) + '/' + String(n.count || 0)]]);
  setStatus('detail-status', '正在读取负载数据...', false);
  renderLists();
  try{
    const d = await withViewerPageLoading((n.name || '节点') + ' 负载数据', '正在读取数据', function(){
      return api('/api/nodes/metrics?node_id=' + encodeURIComponent(id) + '&window=12h');
    });
    drawChart(Array.isArray(d.items) ? d.items : []);
    setStatus('detail-status', d.items && d.items.length ? ('已加载 ' + d.items.length + ' 条样本') : (d.error || '无负载数据'), !(d.items && d.items.length));
  }catch(e){
    drawChart([]);
    setStatus('detail-status', '负载读取失败: ' + (e.message || e), true);
  }
}
function showScan(id){
  var n = nodeById(id) || {};
  state.selectedId = Number(id);
  state.selectedSsoUrl = readCachedSso(n);
  qs('detail-title').textContent = (n.name || '节点') + ' 扫描数据';
  qs('detail-copy').textContent = '聚合统计';
  qs('load-chart').classList.remove('show');
  qs('detail-body').innerHTML = detailRows([
    ['累计扫描', n.count || 0], ['当前在线', n.online_count || 0], ['最后刷新', fmtTime(n.fetched_at)],
    ['扫描状态', (n.service || {}).sniff_state || '—'], ['扫描消息', (n.service || {}).sniff_msg || n.error || '—']
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
  ctx.fillStyle = getComputedStyle(document.body).getPropertyValue('--card2') || '#f4f8ff'; ctx.fillRect(0,0,w,h);
  ctx.strokeStyle = getComputedStyle(document.body).getPropertyValue('--border') || '#dbe6f4'; ctx.strokeRect(0.5,0.5,w-1,h-1);
  var rows = (items || []).filter(function(x){ return x && Number(x.ts || 0) > 0; });
  if(!rows.length){ ctx.fillStyle='#64748b'; ctx.font='600 13px Inter'; ctx.fillText('没有负载样本', 18, 30); return; }
  rows.sort(function(a,b){ return Number(a.ts||0)-Number(b.ts||0); });
  var minTs = Number(rows[0].ts), maxTs = Number(rows[rows.length-1].ts); if(maxTs <= minTs) maxTs = minTs + 1;
  var defs = [['cpu','#2563eb','CPU'],['mem','#16a34a','内存'],['load','#f59e0b','负载'],['temp','#f97316','温度']];
  var pad = {l:42,r:16,t:20,b:28}, plotW = w-pad.l-pad.r, plotH = h-pad.t-pad.b;
  ctx.strokeStyle = 'rgba(100,116,139,.18)'; ctx.lineWidth = 1;
  for(var gy=0; gy<=4; gy++){ var y=pad.t+(plotH*gy/4); ctx.beginPath(); ctx.moveTo(pad.l,y); ctx.lineTo(w-pad.r,y); ctx.stroke(); }
  defs.forEach(function(def, idx){
    var key=def[0], color=def[1], label=def[2], has=false;
    ctx.beginPath();
    rows.forEach(function(r){
      var v = Number(r[key]);
      if(!isFinite(v)) return;
      v = Math.max(0, Math.min(100, v));
      var x = pad.l + ((Number(r.ts)-minTs)/(maxTs-minTs))*plotW;
      var y = pad.t + (1 - v/100)*plotH;
      if(!has){ ctx.moveTo(x,y); has=true; } else ctx.lineTo(x,y);
    });
    ctx.strokeStyle = color; ctx.lineWidth = 2; ctx.stroke();
    ctx.fillStyle = color; ctx.font='700 12px Inter'; ctx.fillText(label, pad.l + idx*68, 14);
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
  setStatus('bulk-status', '在线节点 ' + String(agg.online_node_count || 0) + '/' + String(agg.node_count || 0) + '，在线无人机 ' + String(agg.online_drone_count || 0) + '/' + String(agg.drone_count || 0), false);
}
function normalizeNodeRootInput(raw){
  var value = String(raw || '').trim();
  if(!value) throw new Error('API address is required');
  if(/\s/.test(value)) throw new Error('API address must not contain whitespace');
  if(!/^[a-z][a-z0-9+.-]*:\/\//i.test(value)) value = 'http://' + value;
  var url;
  try{ url = new URL(value); }catch(_e){ throw new Error('API address must be an http(s) URL root'); }
  if(url.protocol !== 'http:' && url.protocol !== 'https:') throw new Error('API address must be http(s)');
  if(url.username || url.password || (url.pathname && url.pathname !== '/') || url.search || url.hash){
    throw new Error('Only the URL root is allowed, for example http://192.168.1.10:4600');
  }
  return url.origin;
}
function collectNodeBody(){
  var root = normalizeNodeRootInput(qs('node-url').value);
  qs('node-url').value = root;
  return {id:Number(qs('node-id').value||0), name:qs('node-name').value, base_url:root, token:qs('node-token').value, enabled:qs('node-enabled').checked};
}
function clearForm(){ qs('node-id').value=''; qs('node-name').value=''; qs('node-url').value=''; qs('node-token').value=''; qs('node-enabled').checked=true; setStatus('node-status','-',false); }
async function saveNode(testOnly){
  var body = collectNodeBody();
  setStatus('node-status', testOnly ? '正在测试...' : '正在保存...', false);
  var d = await post(testOnly ? '/api/nodes/test' : '/api/nodes', body);
  if(testOnly){ var n=d.node||{}; setStatus('node-status', n.ok ? '连接正常' : ('连接失败' + (n.error ? '：' + n.error : '')), !n.ok); return; }
  clearForm(); await loadAll(); setStatus('node-status','已保存。',false);
}
function editSelected(){
  var rec = recordById(state.selectedId); if(!rec) return;
  qs('node-id').value = rec.id; qs('node-name').value = rec.name || ''; qs('node-url').value = rec.base_url || ''; qs('node-token').value = ''; qs('node-enabled').checked = !!rec.enabled;
  setStatus('node-status', '留空则保留原 Token', false);
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
  var node = nodeById(state.selectedId) || {};
  var cached = readCachedSso(node);
  if(cached){
    state.selectedSsoUrl = cached;
    qs('detail-body').innerHTML = detailRows([['SSO URL', state.selectedSsoUrl], ['节点', node.name || state.selectedId]]);
    qs('btn-open-sso').disabled = false;
    setStatus('detail-status', '已缓存', false);
    return;
  }
  setStatus('detail-status', '正在生成 SSO 登录链接...', false);
  var d = await post('/api/nodes/sso', {node_id:state.selectedId});
  state.selectedSsoUrl = d.url || '';
  writeCachedSso(node, d);
  qs('detail-body').innerHTML = detailRows([['SSO URL', state.selectedSsoUrl || '—'], ['节点', (nodeById(state.selectedId)||{}).name || state.selectedId]]);
  qs('btn-open-sso').disabled = !state.selectedSsoUrl;
  setStatus('detail-status', state.selectedSsoUrl ? '已生成' : '无可用链接', !state.selectedSsoUrl);
}
async function remoteOp(op){
  var ids = selectedIds();
  if(!ids.length && state.selectedId) ids = [state.selectedId];
  if(!ids.length){ setStatus('bulk-status','请先勾选节点，或先选中一个节点。',true); return; }
  if(op === 'restart' && !confirm('确认重启 ' + ids.length + ' 个节点的主程序？')) return;
  setStatus('bulk-status', '正在执行...', false);
  var d = await post('/api/nodes/remote', {node_ids:ids, operation:op});
  var rows = d.results || [];
  setStatus('bulk-status', rows.map(function(r){ return (r.name || r.id) + '：' + (r.ok ? '已完成' : ('失败，' + (r.error || ''))); }).join('\n'), rows.some(function(r){ return !r.ok; }));
  setTimeout(loadAll, 1200);
}
function updateSelectionButtons(){
  var has = !!state.selectedId;
  qs('btn-edit-selected').disabled = !has;
  qs('btn-sso-selected').disabled = !has;
  qs('btn-delete-selected').disabled = !has;
  qs('btn-open-sso').disabled = !state.selectedSsoUrl;
}
window.__RID_NODE_CENTER_ACTIONS__ = {
  showBasic: showBasic,
  showLoad: showLoad,
  showScan: showScan,
  onChecked: function(id, checked){ state.checkedIds[Number(id || 0)] = !!checked; }
};
qs('btn-back').onclick = function(){ location.href='/'; };
qs('btn-settings').onclick = function(){ location.href='/settings'; };
qs('btn-theme').onclick = function(){ applyTheme(document.body.classList.contains('theme-light') ? 'dark' : 'light'); };
qs('btn-refresh').onclick = function(){ withViewerPageLoading('Viewer 节点列表', '正在读取数据', loadAll).catch(function(e){ setStatus('bulk-status', e.message || e, true); }); };
qs('btn-clear-form').onclick = clearForm;
qs('btn-test-node').onclick = function(){ saveNode(true).catch(function(e){ setStatus('node-status', e.message || e, true); }); };
qs('btn-save-node').onclick = function(){ saveNode(false).catch(function(e){ setStatus('node-status', e.message || e, true); }); };
qs('btn-edit-selected').onclick = editSelected;
qs('btn-delete-selected').onclick = function(){ deleteSelected().catch(function(e){ setStatus('detail-status', e.message || e, true); }); };
qs('btn-sso-selected').onclick = function(){ createSso().catch(function(e){ setStatus('detail-status', e.message || e, true); }); };
qs('btn-open-sso').onclick = function(){ if(state.selectedSsoUrl) window.open(state.selectedSsoUrl, '_blank', 'noopener'); };
qs('btn-select-all').onclick = function(){ (state.nodes || []).forEach(function(n){ state.checkedIds[Number(n.id || 0)] = true; }); renderLists(); };
qs('btn-select-online').onclick = function(){ (state.nodes || []).forEach(function(n){ state.checkedIds[Number(n.id || 0)] = !!n.ok; }); renderLists(); };
qs('btn-remote-restart').onclick = function(){ remoteOp('restart').catch(function(e){ setStatus('bulk-status', e.message || e, true); }); };
qs('btn-remote-models').onclick = function(){ remoteOp('update_models').catch(function(e){ setStatus('bulk-status', e.message || e, true); }); };
applyTheme(loadTheme());
if(window.__RID_NODE_CENTER_BRIDGE__ && typeof window.__RID_NODE_CENTER_BRIDGE__.mount === 'function'){ window.__RID_NODE_CENTER_BRIDGE__.mount(); }
withViewerPageLoading('Viewer 节点列表', '正在读取数据', loadAll).catch(function(e){ setStatus('bulk-status', e.message || e, true); });
"""
    return station_page(
        "节点管理器",
        body,
        script,
        extra_css=extra_css,
        extra_scripts=(_nodes_center_asset_url(),),
    )
