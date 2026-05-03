
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
      'Please add this RID model mapping to rid_models.json.'
    ].join('\\n');
    return 'https://github.com/luyii-code-1/Light_RID_Scanner/issues/new?title='
      + encodeURIComponent(title) + '&body=' + encodeURIComponent(body);
  }
  function modelPrEditUrl(){
    return 'https://github.com/luyii-code-1/Light_RID_Scanner/edit/main/rid_models.json';
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
    qs('zone-alarm-text').textContent = '检测到目标进入自定义报警区域：' + lineText;
    overlay.classList.add('show');
    if(sig !== alarmLastSig){
      showBanner('区域告警：' + lineText, 'warn', 5200, {persist:false});
      if(webNotifyEnabled && window.Notification && Notification.permission === 'granted'){
        try{ new Notification('Light RID Scanner 区域告警', {body:lineText}); }catch(_e){}
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


const nextPath = __EXPR__;
const form = document.getElementById('login-form');
const statusEl = document.getElementById('status');
const passkeyBtn = document.getElementById('btn-passkey-login');
function pageHeaders(extra){
  var h = {'X-LightRID-Page':'1'};
  if(extra) Object.keys(extra).forEach(function(k){ h[k] = extra[k]; });
  return h;
}
function setStatus(text, err){
  if(!statusEl) return;
  statusEl.textContent = text || '';
  statusEl.classList.toggle('err', !!err);
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
  return btoa(bin).replace(/\+/g,'-').replace(/\//g,'_').replace(/=+$/,'');
}
async function loginWithPasskey(){
  if(!window.PublicKeyCredential || !navigator.credentials || !navigator.credentials.get){
      throw new Error('当前浏览器不支持通行密钥登录');
  }
  setStatus('正在准备通行密钥登录...', false);
  const startR = await fetch('/api/passkey/login/start', {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:'{}'
  });
  const start = await startR.json().catch(() => ({}));
  if(!startR.ok || start.ok === false) throw new Error(start.error || ('HTTP ' + startR.status));
  const pk = start.publicKey || {};
  const allowCredentials = Array.isArray(pk.allowCredentials) ? pk.allowCredentials : [];
  const cred = await navigator.credentials.get({
    publicKey: {
      challenge: b64uToBytes(pk.challenge || start.challenge || ''),
      rpId: pk.rpId || pk.rp_id || location.hostname,
      timeout: pk.timeout || start.timeout_ms || 300000,
      userVerification: pk.userVerification || 'preferred',
      allowCredentials: allowCredentials.map(function(item){ return {type:'public-key', id:b64uToBytes(item.id || '')}; })
    }
  });
  if(!cred) throw new Error('未获取到通行密钥凭据');
  const response = cred.response || {};
  const finishR = await fetch('/api/passkey/login/finish', {
    method:'POST',
    headers:pageHeaders({'Content-Type':'application/json'}),
    body:JSON.stringify({
      challenge: start.challenge || start.challenge_token || '',
      id: cred.id || '',
      rawId: bytesToB64u(cred.rawId || new Uint8Array(0)),
      type: cred.type || 'public-key',
      response: {
        clientDataJSON: bytesToB64u(response.clientDataJSON || new Uint8Array(0)),
        authenticatorData: bytesToB64u(response.authenticatorData || new Uint8Array(0)),
        signature: bytesToB64u(response.signature || new Uint8Array(0)),
        userHandle: response.userHandle ? bytesToB64u(response.userHandle) : ''
      },
      next: nextPath || '/'
    })
  });
  const finish = await finishR.json().catch(() => ({}));
  if(!finishR.ok || finish.ok === false) throw new Error(finish.error || ('HTTP ' + finishR.status));
  location.href = nextPath || finish.next || '/';
}
if(form){
  form.addEventListener('submit', async function(ev){
    ev.preventDefault();
    const btn = document.getElementById('submit');
    btn.disabled = true;
    setStatus('正在验证...', false);
    try{
      const r = await fetch('/login', {
        method:'POST',
        headers:{'Content-Type':'application/json'},
        body:JSON.stringify({username:document.getElementById('user').value || '', password:document.getElementById('password').value || ''})
      });
      const d = await r.json().catch(() => ({}));
      if(!r.ok || d.ok === false) throw new Error(d.error || '登录失败');
      location.href = nextPath || d.next || '/';
    }catch(e){
      setStatus(e.message || String(e), true);
    }finally{
      btn.disabled = false;
    }
  });
}
if(passkeyBtn){
  passkeyBtn.addEventListener('click', async function(){
    passkeyBtn.disabled = true;
    try{
      await loginWithPasskey();
    }catch(e){
      setStatus(e.message || String(e), true);
    }finally{
      passkeyBtn.disabled = false;
    }
  });
}