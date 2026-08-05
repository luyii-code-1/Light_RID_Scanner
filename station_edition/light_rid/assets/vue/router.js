(() => {
  const $ = id => document.getElementById(id);
  const headers = extra => Object.assign({"X-LightRID-Page":"1"}, extra || {});
  let state = null;
  let transactionTimer = null;

  function currentPageUrl() {
    const url = new URL(location.href);
    url.search = "";
    url.hash = "";
    return url.href;
  }

  function setMessage(text, error) {
    $("message").textContent = text || "";
    $("message").style.color = error ? "var(--red)" : "var(--muted)";
  }
  function redirectIfExpired(response, data) {
    if (response.status === 401 || (data && data.auth_expired)) {
      location.href = "/login?next=/router";
      return true;
    }
    return false;
  }
  async function request(path, options) {
    const response = await fetch(path, Object.assign({cache:"no-store", headers:headers()}, options || {}));
    const data = await response.json().catch(() => ({}));
    if (redirectIfExpired(response, data)) throw new Error("登录已过期");
    if (!response.ok || data.ok === false) {
      const detail = Array.isArray(data.errors) ? "\n" + data.errors.join("\n") : "";
      throw new Error((data.error || `HTTP ${response.status}`) + detail);
    }
    return data;
  }
  function post(path, body) {
    return request(path, {method:"POST", headers:headers({"Content-Type":"application/json"}), body:JSON.stringify(body || {})});
  }
  function value(id, fallback="") { return String($(id).value == null ? fallback : $(id).value).trim(); }
  function checked(id) { return !!$(id).checked; }
  function number(id, fallback=0) { const n = Number(value(id)); return Number.isFinite(n) ? n : fallback; }
  function splitWords(id) { return value(id).split(/[\s,]+/).filter(Boolean); }
  function setValue(id, value) { $(id).value = value == null ? "" : String(value); }
  function setChecked(id, value) { $(id).checked = !!value; }
  function activeMode() { const item = document.querySelector('input[name="mode"]:checked'); return item ? item.value : "wired"; }

  function updateConditionals() {
    const protocol = value("wan-protocol", "dhcp");
    document.querySelectorAll(".conditional").forEach(el => el.classList.toggle("hidden", !el.classList.contains(protocol)));
    const wired = activeMode() === "wired";
    $("wan-card").style.opacity = wired ? "1" : ".55";
    $("repeater-card").style.opacity = wired ? ".55" : "1";
    $("ap-channel").disabled = !wired;
  }

  function renderStatus(data) {
    const config = data.config || {};
    const runtime = data.runtime || {};
    $("luci-link").href = data.luci_url || "/cgi-bin/luci";
    $("status-mode").textContent = config.mode === "repeater" ? "5GHz 无线中继" : "有线 WAN";
    const uplink = config.mode === "repeater" ? runtime.wwan : runtime.wan;
    const up = !!(uplink && uplink.up);
    $("status-wan").innerHTML = `<span class="dot ${up ? "up" : ""}"></span>${up ? "已连接" : "未连接"}`;
    $("status-lan").textContent = ((runtime.lan || {}).addresses || [config.lan && config.lan.ipaddr || "—"])[0] || "—";
    const ipv6 = ((runtime.wan6 || {}).addresses6 || []);
    $("status-ipv6").textContent = ipv6.length ? "已连接" : "未连接";
    $("ipv6-detail").textContent = ipv6.length ? ipv6.join(" · ") : "WAN6 当前没有可用 IPv6 地址。";
  }

  function fill(config) {
    document.querySelector(`input[name="mode"][value="${config.mode || "wired"}"]`).checked = true;
    const wan = config.wan || {}, lan = config.lan || {}, ap = config.ap || {}, rep = config.repeater || {}, guest = config.guest || {};
    setValue("wan-protocol", wan.protocol || "dhcp"); setValue("wan-ip", wan.ipaddr); setValue("wan-mask", wan.netmask); setValue("wan-gateway", wan.gateway); setValue("wan-dns", (wan.dns || []).join(" ")); setValue("pppoe-user", wan.username); setValue("pppoe-pass", "");
    setValue("lan-ip", lan.ipaddr); setValue("lan-mask", lan.netmask); setValue("lan-start", lan.dhcp_start); setValue("lan-limit", lan.dhcp_limit); setValue("lan-lease", lan.lease_time); setValue("lan-dns", (lan.dns || []).join(" ")); setChecked("lan-dhcp", lan.dhcp_enabled);
    setValue("ap-ssid", ap.ssid); setValue("ap-pass", ""); setValue("ap-channel", ap.channel === "auto" ? 36 : ap.channel); setValue("ap-htmode", ap.htmode); setValue("ap-power", ap.txpower); setChecked("ap-enabled", ap.enabled);
    setValue("repeater-ssid", rep.ssid); setValue("repeater-bssid", rep.bssid); setValue("repeater-encryption", rep.encryption || "psk2"); setValue("repeater-pass", "");
    setValue("guest-ssid", guest.ssid); setValue("guest-pass", ""); setValue("guest-ip", guest.ipaddr); setValue("guest-mask", guest.netmask); setValue("guest-start", guest.dhcp_start); setValue("guest-limit", guest.dhcp_limit); setValue("guest-lease", guest.lease_time); setChecked("guest-enabled", guest.enabled);
    setChecked("remote-enabled", !!(config.remote_management || {}).enabled);
    renderForwards(config.port_forwards || []);
    updateConditionals();
  }

  function forwardRow(item={}) {
    const row = document.createElement("div"); row.className = "forward"; row.dataset.id = item.id || String(Date.now());
    row.innerHTML = `<div class="field"><label>名称</label><input class="pf-name" maxlength="48"></div><div class="field"><label>协议</label><select class="pf-proto"><option value="tcp">TCP</option><option value="udp">UDP</option><option value="tcp udp">TCP+UDP</option></select></div><div class="field"><label>外部端口</label><input class="pf-external" type="number" min="1" max="65535"></div><div class="field"><label>内部地址</label><input class="pf-ip"></div><div class="field"><label>内部端口</label><input class="pf-internal" type="number" min="1" max="65535"></div><div class="field"><label>来源 CIDR（可选）</label><input class="pf-source"></div><button class="btn danger remove" type="button">删除</button>`;
    row.querySelector(".pf-name").value = item.name || ""; row.querySelector(".pf-proto").value = item.protocol || "tcp"; row.querySelector(".pf-external").value = item.external_port || ""; row.querySelector(".pf-ip").value = item.internal_ip || ""; row.querySelector(".pf-internal").value = item.internal_port || ""; row.querySelector(".pf-source").value = item.source_ip || "";
    row.querySelector(".remove").onclick = () => { row.remove(); renderEmptyForwards(); };
    return row;
  }
  function renderEmptyForwards() { if (!$("forward-list").children.length) $("forward-list").innerHTML = '<div class="empty">尚未创建端口转发规则。</div>'; }
  function renderForwards(items) { $("forward-list").innerHTML = ""; items.forEach(item => $("forward-list").appendChild(forwardRow(item))); renderEmptyForwards(); }
  function addForward() { const empty = $("forward-list").querySelector(".empty"); if (empty) empty.remove(); $("forward-list").appendChild(forwardRow({})); }
  function collectForwards() {
    return Array.from($("forward-list").querySelectorAll(".forward")).map(row => ({id:row.dataset.id, name:row.querySelector(".pf-name").value, enabled:true, protocol:row.querySelector(".pf-proto").value, external_port:Number(row.querySelector(".pf-external").value), internal_ip:row.querySelector(".pf-ip").value, internal_port:Number(row.querySelector(".pf-internal").value), source_ip:row.querySelector(".pf-source").value}));
  }
  function collect() {
    return {
      mode:activeMode(),
      wan:{protocol:value("wan-protocol"), ipaddr:value("wan-ip"), netmask:value("wan-mask"), gateway:value("wan-gateway"), dns:splitWords("wan-dns"), username:value("pppoe-user"), password:$("pppoe-pass").value},
      lan:{ipaddr:value("lan-ip"), netmask:value("lan-mask"), dhcp_enabled:checked("lan-dhcp"), dhcp_start:number("lan-start"), dhcp_limit:number("lan-limit"), lease_time:value("lan-lease"), dns:splitWords("lan-dns")},
      ap:{enabled:checked("ap-enabled"), ssid:value("ap-ssid"), password:$("ap-pass").value, channel:number("ap-channel",36), htmode:value("ap-htmode"), txpower:number("ap-power",20)},
      repeater:{ssid:value("repeater-ssid"), bssid:value("repeater-bssid"), encryption:value("repeater-encryption"), password:$("repeater-pass").value},
      guest:{enabled:checked("guest-enabled"), ssid:value("guest-ssid"), password:$("guest-pass").value, ipaddr:value("guest-ip"), netmask:value("guest-mask"), dhcp_start:number("guest-start"), dhcp_limit:number("guest-limit"), lease_time:value("guest-lease")},
      port_forwards:collectForwards(), remote_management:{enabled:checked("remote-enabled")}
    };
  }

  function showTransaction(tx) {
    clearInterval(transactionTimer); transactionTimer = null;
    if (!tx || !tx.pending) { $("transaction").classList.remove("show"); return; }
    $("transaction").classList.add("show"); $("confirm").disabled = tx.phase !== "applied";
    const render = () => { const remaining = Math.max(0, Math.ceil(Number(tx.deadline || 0) - Date.now()/1000)); const phase = tx.phase === "applied" ? "已应用" : "正在应用"; $("transaction-copy").textContent = `${phase} · 剩余 ${remaining} 秒。确认页面：${currentPageUrl()}`; if (!remaining) clearInterval(transactionTimer); };
    render(); transactionTimer = setInterval(render, 1000); $("confirm").dataset.id = tx.id; $("rollback").dataset.id = tx.id;
  }
  async function load() {
    try {
      const data = await request("/api/router/status"); state = data; const supported = !!(data.capabilities || {}).supported;
      $("unsupported").classList.toggle("show", !supported); if (!supported) $("unsupported-text").textContent = `当前环境不受支持：${(data.capabilities || {}).board || "unknown"}`;
      $("router-form").style.opacity = supported ? "1" : ".45"; $("apply").disabled = !supported; $("validate").disabled = !supported; $("factory-reset").disabled = !supported;
      if (supported) { fill(data.config || {}); renderStatus(data); }
      showTransaction(data.transaction); setMessage(supported ? "配置已加载。密码字段留空表示保持原值。" : "只能在 GL-AR750S OpenWrt 上管理路由。", !supported);
    } catch (error) { setMessage(error.message, true); }
  }
  async function validate() { try { setMessage("正在检查配置…"); await post("/api/router/validate", collect()); setMessage("配置检查通过。尚未写入设备。"); } catch (error) { setMessage(error.message, true); } }
  async function apply() {
    if (!confirm("应用网络配置后，必须在 60 秒内确认。继续吗？")) return;
    try { setMessage("正在备份并应用 OpenWrt 配置，请勿断电…"); const data = await post("/api/router/apply", collect()); showTransaction(data.transaction); setMessage("配置正在应用，请在当前访问地址点击“保留设置”。"); const url = currentPageUrl(); setTimeout(() => { location.assign(url); }, 5000); } catch (error) { setMessage(error.message, true); }
  }
  async function confirmTx() { try { const data = await post("/api/router/confirm", {id:$("confirm").dataset.id}); showTransaction(null); setMessage("网络配置已确认保留。"); await load(); } catch (error) { setMessage(error.message, true); } }
  async function rollbackTx() { try { await post("/api/router/rollback", {id:$("rollback").dataset.id}); showTransaction(null); setMessage("已恢复变更前配置，正在重新连接…"); setTimeout(load, 4000); } catch (error) { setMessage(error.message, true); } }
  async function scan() { try { $("scan").disabled = true; $("scan-list").innerHTML = '<div class="empty">正在扫描 5GHz 网络…</div>'; const data = await post("/api/router/wifi/scan", {}); $("scan-list").innerHTML = ""; (data.items || []).forEach(item => { const row = document.createElement("div"); row.className="scan-item"; row.innerHTML=`<div><div class="scan-main"></div><div class="scan-meta"></div></div><button class="btn" type="button">选择</button>`; row.querySelector(".scan-main").textContent=item.ssid; row.querySelector(".scan-meta").textContent=`${item.bssid} · 信道 ${item.channel} · ${item.signal == null ? "—" : item.signal + " dBm"} · ${item.encryption}`; row.querySelector("button").onclick=()=>{setValue("repeater-ssid",item.ssid);setValue("repeater-bssid",item.bssid);setValue("repeater-encryption",item.encryption);}; $("scan-list").appendChild(row); }); if (!(data.items || []).length) $("scan-list").innerHTML='<div class="empty">没有发现 5GHz 网络。</div>'; } catch(error) { $("scan-list").innerHTML=`<div class="empty"></div>`; $("scan-list").firstChild.textContent=error.message; } finally { $("scan").disabled=false; } }
  async function resetOriginal() { try { $("reset-dialog").close(); setMessage("正在恢复安装前网络配置…"); await post("/api/router/reset-network", {confirm:"RESTORE"}); setMessage("原厂网络配置已恢复，当前连接可能中断。"); } catch(error) { setMessage(error.message,true); } }

  $("wan-protocol").addEventListener("change", updateConditionals); document.querySelectorAll('input[name="mode"]').forEach(el => el.addEventListener("change", updateConditionals));
  $("add-forward").onclick=addForward; $("scan").onclick=scan; $("validate").onclick=validate; $("apply").onclick=apply; $("confirm").onclick=confirmTx; $("rollback").onclick=rollbackTx;
  $("factory-reset").onclick=()=>$("reset-dialog").showModal(); $("reset-cancel").onclick=()=>$("reset-dialog").close(); $("reset-confirm").onclick=resetOriginal;
  load();
})();
