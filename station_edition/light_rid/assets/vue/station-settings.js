(() => {
  // frontend/src/station-settings.js
  function qs(id) {
    return document.getElementById(id);
  }
  function qsa(sel) {
    return Array.prototype.slice.call(document.querySelectorAll(sel) || []);
  }
  function enc(v2) {
    return String(v2 == null ? "" : v2).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  }
  function splitLines(text) {
    var raw = String(text || "");
    if (raw.indexOf("\r") >= 0) raw = raw.split("\r").join("");
    return raw.split("\n");
  }
  function isLocalHostName(host) {
    var h = String(host || "").toLowerCase();
    return h === "localhost" || h === "127.0.0.1";
  }
  var apiTokenRows = [];
  var oneTimeSecretValue = "";
  var reauthAction = null;
  var elevateResolve = null;
  var lastSystemServiceStatus = null;
  var loginLinks = [];
  var modelMapRows = [];
  var modelMapPath = "";
  var settingsState = { visualLoaded: false, rawLoaded: false, rawUnlocked: false, rawRoot: "", rawTree: null, rawSelectedPath: "", rawSelectedRel: "", channelUseDefault: true, channelEditing: false, visualInitial: null, visualDirty: false, dirtyCards: {}, authConfigured: false, networkBindings: null, interfaceItems: [] };
  var metricsState = { window: "12h", zoom: 1, panSec: 0, hover: null, drag: null, chartMeta: {}, items: [] };
  var visualCheckboxSaveTimer = null;
  var SETTINGS_DRAFT_SECTIONS = [
    { key: "capture", label: "采集" },
    { key: "map", label: "地图与基站" },
    { key: "zones", label: "报警区域" },
    { key: "access", label: "通知与访问控制" },
    { key: "metrics", label: "节点负载" }
  ];
  var COOKIE_TRACK_REALTIME = "rid_realtime_track";
  var COOKIE_TRACK_2H_ONLY = "rid_track_2h_only";
  var NEW_FIRMWARE_PARSE_KEY = "rid_new_firmware_parse_enabled";
  function on(id, type, handler) {
    var el = qs(id);
    if (el) el.addEventListener(type, handler);
    return el;
  }
  function bindAccessCollapsibles() {
    qsa(".access-subcard.collapsible > .access-subhead").forEach(function(head) {
      head.setAttribute("role", "button");
      head.setAttribute("tabindex", "0");
      function toggle() {
        var card = head.closest(".access-subcard");
        if (card) card.classList.toggle("collapsed");
      }
      head.addEventListener("click", toggle);
      head.addEventListener("keydown", function(ev) {
        if (ev.key === "Enter" || ev.key === " ") {
          ev.preventDefault();
          toggle();
        }
      });
    });
  }
  function bindSettingsCardCollapsibles() {
    qsa(".card.settings-collapsible > .section-head").forEach(function(head) {
      head.setAttribute("role", "button");
      head.setAttribute("tabindex", "0");
      function toggle() {
        var card = head.closest(".card.settings-collapsible");
        if (card) card.classList.toggle("collapsed");
      }
      head.addEventListener("click", function(ev) {
        var t = ev.target;
        if (t && t.closest && t.closest("button,input,label,a,select,textarea")) return;
        toggle();
      });
      head.addEventListener("keydown", function(ev) {
        if (ev.key === "Enter" || ev.key === " ") {
          ev.preventDefault();
          toggle();
        }
      });
    });
  }
  async function guarded(action, statusId, okText, okMs, warnMs) {
    try {
      await action();
      if (okText) showNotice(okText, "ok", okMs || 2200);
    } catch (e) {
      if (statusId) setStatus(statusId, e.message || e, true);
      showNotice(e.message || e, "warn", warnMs || 3800);
    }
  }
  var settingsLoadingStartedAt = 0;
  var settingsLoadingTimer = null;
  function settingsLoadingState(target) {
    if (!settingsLoadingStartedAt) settingsLoadingStartedAt = Date.now();
    var elapsed = Math.floor((Date.now() - settingsLoadingStartedAt) / 1e3);
    var name = String(target || "设置数据");
    return {
      target: name,
      detail: "正在处理 " + name,
      status: "已等待 " + elapsed + "s，完成后会自动刷新状态"
    };
  }
  function showSettingsPageLoading(target, title) {
    settingsLoadingStartedAt = Date.now();
    var host = qs("rid-loading-overlay");
    if (!host) {
      host = document.createElement("div");
      host.id = "rid-loading-overlay";
      host.className = "rid-loading-overlay";
      host.innerHTML = '<div class="rid-loading-shell"><div class="rid-loading-box"><div class="rid-loading-head"><div class="rid-loading-spinner"></div><div class="rid-loading-copy-wrap"><div class="rid-loading-title"></div><div class="rid-loading-copy"></div></div></div><div class="rid-loading-meta"><div class="rid-loading-meta-line"><span class="rid-loading-meta-label">当前目标</span><span class="rid-loading-meta-value" data-role="target"></span></div><div class="rid-loading-meta-line"><span class="rid-loading-meta-label">详细状态</span><span class="rid-loading-meta-value" data-role="status"></span></div></div></div></div>';
      document.body.appendChild(host);
    }
    var titleEl = host.querySelector(".rid-loading-title");
    var copyEl = host.querySelector(".rid-loading-copy");
    var targetEl = host.querySelector('[data-role="target"]');
    var statusEl = host.querySelector('[data-role="status"]');
    function tick() {
      var state = settingsLoadingState(target);
      if (titleEl) titleEl.textContent = String(title || "正在处理设置");
      if (copyEl) copyEl.textContent = state.detail;
      if (targetEl) targetEl.textContent = state.target;
      if (statusEl) statusEl.textContent = state.status;
    }
    tick();
    host.classList.add("show");
    document.body.classList.add("rid-loading-active");
    if (settingsLoadingTimer) clearInterval(settingsLoadingTimer);
    settingsLoadingTimer = setInterval(tick, 1e3);
  }
  function hideSettingsPageLoading() {
    var host = qs("rid-loading-overlay");
    if (host) host.classList.remove("show");
    document.body.classList.remove("rid-loading-active");
    if (settingsLoadingTimer) {
      clearInterval(settingsLoadingTimer);
      settingsLoadingTimer = null;
    }
  }
  async function withSettingsPageLoading(target, title, fn) {
    showSettingsPageLoading(target, title);
    try {
      return await fn();
    } finally {
      hideSettingsPageLoading();
    }
  }
  function syncSettingsViewport() {
    var vp = window.visualViewport;
    var vh = Math.max(320, Math.round(vp && vp.height ? vp.height : window.innerHeight || 0));
    document.documentElement.style.setProperty("--app-vh", vh + "px");
  }
  function cookieDelete(name) {
    var key = String(name || "").trim();
    if (!key) return;
    var secure = location.protocol === "https:" ? "; Secure" : "";
    document.cookie = key + "=; Max-Age=0; Path=/; SameSite=Lax" + secure;
  }
  function setStatus(id, text, err) {
    var el = qs(id);
    if (!el) return;
    el.textContent = String(text || "-");
    el.classList.toggle("err", !!err);
  }
  function showNotice(text, kind, timeoutMs) {
    var host = qs("settings-toast-stack");
    if (!host) return;
    var node = document.createElement("div");
    var tone = kind === "warn" || kind === "error" ? "warn" : "ok";
    node.className = "toast " + tone;
    node.innerHTML = '<div class="toast-title">' + (tone === "warn" ? "请留意" : "已完成") + '</div><div class="toast-text">' + enc(String(text || "")) + "</div>";
    host.appendChild(node);
    requestAnimationFrame(function() {
      node.classList.add("show");
    });
    var ttl = Math.max(1800, Number(timeoutMs || 3200));
    window.setTimeout(function() {
      node.classList.remove("show");
      window.setTimeout(function() {
        if (node.parentNode) node.parentNode.removeChild(node);
      }, 220);
    }, ttl);
  }
  function apiUrl(url) {
    try {
      return new URL(String(url || ""), window.location.origin).toString();
    } catch (_e) {
      return String(url || "");
    }
  }
  function pageHeaders(extra) {
    var headers = { "X-LightRID-Page": "1" };
    if (extra && typeof extra === "object") {
      Object.keys(extra).forEach(function(k) {
        headers[k] = extra[k];
      });
    }
    return headers;
  }
  var authRedirecting = false;
  function authExpired(r, d) {
    var err = String(d && d.error || "");
    return r && r.status === 401 && (!!(d && d.auth_expired) || err === "login required" || err === "auth required");
  }
  function redirectLogin() {
    if (authRedirecting) return;
    authRedirecting = true;
    location.href = "/login?next=/";
  }
  async function copyTextPlain(text) {
    var raw = String(text || "");
    if (!raw) throw new Error("没有可复制的内容");
    if (navigator.clipboard && navigator.clipboard.writeText) {
      try {
        await navigator.clipboard.writeText(raw);
        return;
      } catch (_e) {
      }
    }
    var ta = document.createElement("textarea");
    ta.value = raw;
    ta.style.position = "fixed";
    ta.style.opacity = "0";
    ta.style.pointerEvents = "none";
    document.body.appendChild(ta);
    ta.focus();
    ta.select();
    try {
      if (!document.execCommand("copy")) throw new Error("copy failed");
    } finally {
      if (ta.parentNode) ta.parentNode.removeChild(ta);
    }
  }
  function parseFilenameFromDisposition(headerValue) {
    var cd = String(headerValue || "");
    var marker = "filename=";
    var pos = cd.toLowerCase().indexOf(marker);
    if (pos < 0) return "";
    var raw = cd.slice(pos + marker.length).trim();
    if (raw.charAt(0) === '"') {
      var end = raw.indexOf('"', 1);
      raw = end > 0 ? raw.slice(1, end) : raw.slice(1);
    } else {
      var semi = raw.indexOf(";");
      if (semi >= 0) raw = raw.slice(0, semi);
    }
    return raw.trim();
  }
  async function downloadQualityReport() {
    showNotice("正在生成质量分析包...", "ok", 2200);
    const r = await fetch(apiUrl("/api/tools/diagnostic.zip"), { cache: "no-store", headers: pageHeaders() });
    if (!r.ok) {
      var errText = "";
      try {
        var errJson = await r.json();
        if (authExpired(r, errJson)) {
          redirectLogin();
          throw new Error("login required");
        }
        errText = errJson.error || "";
      } catch (_e) {
        try {
          errText = await r.text();
        } catch (_e2) {
        }
      }
      throw new Error(errText || "HTTP " + r.status);
    }
    const blob = await r.blob();
    if (!blob || Number(blob.size || 0) < 128) {
      throw new Error("质量分析包为空，请稍后重试或查看服务日志");
    }
    var filename = parseFilenameFromDisposition(r.headers.get("Content-Disposition")) || "light-rid-quality.zip";
    var url = URL.createObjectURL(blob);
    var a = document.createElement("a");
    a.href = url;
    a.download = filename;
    document.body.appendChild(a);
    a.click();
    window.setTimeout(function() {
      URL.revokeObjectURL(url);
      if (a.parentNode) a.parentNode.removeChild(a);
    }, 15e3);
    showNotice("质量分析包已生成。", "ok", 3200);
  }
  function transferStamp() {
    var d = /* @__PURE__ */ new Date();
    function pad(n2) {
      return String(n2).padStart(2, "0");
    }
    return String(d.getFullYear()) + pad(d.getMonth() + 1) + pad(d.getDate()) + "_" + pad(d.getHours()) + pad(d.getMinutes()) + pad(d.getSeconds());
  }
  function formatBytes(bytes) {
    var n2 = Number(bytes || 0);
    if (!isFinite(n2) || n2 < 0) return "-";
    var units = ["B", "KB", "MB", "GB"];
    var idx = 0;
    while (n2 >= 1024 && idx < units.length - 1) {
      n2 = n2 / 1024;
      idx += 1;
    }
    var dec = idx === 0 ? 0 : n2 >= 100 ? 1 : 2;
    return n2.toFixed(dec) + " " + units[idx];
  }
  function scanDataFileLabel(info) {
    info = info && typeof info === "object" ? info : {};
    if (info.error) return "读取失败：" + String(info.error);
    if (!info.exists) return "文件不存在，或还没生成";
    var text = formatBytes(info.size);
    if (info.mtime) {
      try {
        text += "，" + new Date(Number(info.mtime) * 1e3).toLocaleString();
      } catch (_e) {
      }
    }
    return text;
  }
  function renderScanDataFileInfo(info) {
    var el = qs("settings-scan-data-size");
    if (!el) return;
    el.textContent = "历史数据大小: " + scanDataFileLabel(info || {});
  }
  function downloadBlobFile(name, blob) {
    var fileName = String(name || "download.bin").trim() || "download.bin";
    var data = blob instanceof Blob ? blob : new Blob([blob == null ? "" : blob], { type: "application/octet-stream" });
    var url = URL.createObjectURL(data);
    var a = document.createElement("a");
    a.href = url;
    a.download = fileName;
    document.body.appendChild(a);
    a.click();
    window.setTimeout(function() {
      URL.revokeObjectURL(url);
      if (a.parentNode) a.parentNode.removeChild(a);
    }, 15e3);
  }
  function downloadJsonObject(name, data) {
    var text = JSON.stringify(data == null ? {} : data, null, 2) + "\n";
    downloadBlobFile(name, new Blob([text], { type: "application/json;charset=utf-8" }));
  }
  function pickFileInput(id) {
    var input = qs(id);
    if (!input) return;
    input.value = "";
    input.click();
  }
  function readJsonFile(file) {
    return new Promise(function(resolve, reject) {
      if (!file) {
        reject(new Error("未选择文件"));
        return;
      }
      var fr = new FileReader();
      fr.onload = function() {
        try {
          resolve(JSON.parse(String(fr.result || "")));
        } catch (e) {
          reject(new Error("JSON 解析失败: " + (e && e.message ? e.message : e)));
        }
      };
      fr.onerror = function() {
        reject(new Error("文件读取失败"));
      };
      fr.readAsText(file, "utf-8");
    });
  }
  async function exportSettingsFile() {
    setStatus("status-data-transfer", "正在导出设置文件...", false);
    var data = await getJson("/api/settings/export/settings");
    downloadJsonObject("rid_settings_" + transferStamp() + ".json", data);
    setStatus("status-data-transfer", "设置文件已导出到 " + String(data.config_path || "-"), false);
    showNotice("设置文件已导出。", "ok", 2600);
  }
  async function exportScanDataFile() {
    setStatus("status-data-transfer", "正在导出扫描数据...", false);
    var data = await getJson("/api/settings/export/scan-data");
    downloadJsonObject("rid_scan_data_" + transferStamp() + ".json", data);
    renderScanDataFileInfo(data.data_file_info || null);
    setStatus("status-data-transfer", "扫描数据已导出，共 " + Number(data.count || 0) + " 条", false);
    showNotice("扫描数据已导出。", "ok", 2600);
  }
  async function importSettingsFileFromFile(file) {
    setStatus("status-data-transfer", "正在导入设置文件...", false);
    var payload = await readJsonFile(file);
    var data = await postJson("/api/settings/import/settings", { payload });
    var msg = "设置文件已导入到 " + String(data.saved_to || "-");
    if (data.backup_path) msg += "\n备份文件 " + String(data.backup_path);
    if (data.reload_msg) msg += "\n" + String(data.reload_msg);
    setStatus("status-data-transfer", msg, false);
    showNotice("设置文件已导入并生效。", "ok", 3200);
    await loadVisual();
  }
  async function importScanDataFileFromFile(file) {
    var payload = await readJsonFile(file);
    var merge = window.confirm("选择扫描数据导入方式：\n确定 = 合并到现有数据\n取消 = 覆盖现有数据");
    var mode = merge ? "merge" : "replace";
    setStatus("status-data-transfer", "正在导入扫描数据（" + (mode === "merge" ? "合并模式" : "覆盖模式") + "）...", false);
    var data = await postJson("/api/settings/import/scan-data", { mode, payload });
    var parts = [];
    if (data.mode === "replace") parts.push("已清空旧数据 " + Number(data.replaced || 0) + " 条");
    parts.push("新增 " + Number(data.added || 0));
    parts.push("更新 " + Number(data.updated || 0));
    parts.push("跳过 " + Number(data.skipped || 0));
    parts.push("当前共 " + Number(data.count || 0) + " 条");
    renderScanDataFileInfo(data.data_file_info || null);
    setStatus("status-data-transfer", "扫描数据导入完成。" + parts.join("，"), false);
    showNotice("扫描数据导入完成。", "ok", 3200);
  }
  async function getJson(url) {
    const r = await fetch(apiUrl(url), { cache: "no-store", headers: pageHeaders() });
    const d = await r.json().catch(() => ({}));
    if (authExpired(r, d)) {
      redirectLogin();
      throw new Error("login required");
    }
    if (!r.ok || d.ok === false) throw new Error(d.error || "HTTP " + r.status);
    return d;
  }
  async function postJson(url, body) {
    const r = await fetch(apiUrl(url), { method: "POST", headers: pageHeaders({ "Content-Type": "application/json" }), body: JSON.stringify(body || {}) });
    const d = await r.json().catch(() => ({}));
    if (authExpired(r, d)) {
      redirectLogin();
      throw new Error("login required");
    }
    if (!r.ok || d.ok === false) throw new Error(d.error || "HTTP " + r.status);
    return d;
  }
  async function reidentifyRecentHistoryPackets() {
    setStatus("status-data-transfer", "正在重新识别所有飞机最近保存的 100 个数据包...", false);
    var data = await postJson("/api/settings/history/reidentify-recent", { limit: 100 });
    var msg = "历史包批量识别完成。飞机 " + Number(data.updated_aircraft || 0) + "/" + Number(data.aircraft_count || 0) + "，数据包 " + Number(data.decoded || 0) + "/" + Number(data.packet_count || 0);
    var extra = [];
    if (Number(data.migrated || 0) > 0) extra.push("SN迁移 " + Number(data.migrated || 0));
    if (Number(data.skipped || 0) > 0) extra.push("跳过 " + Number(data.skipped || 0));
    if (Number(data.failed || 0) > 0) extra.push("失败 " + Number(data.failed || 0));
    if (extra.length) msg += "（" + extra.join("，") + "）";
    setStatus("status-data-transfer", msg, false);
    showNotice("最近 100 个历史包已重新识别。", "ok", 3600);
  }
  function closeElevate(value) {
    var modal = qs("elevate-modal");
    var pass = qs("elevate-pass");
    var resolver = elevateResolve;
    elevateResolve = null;
    if (pass) pass.value = "";
    if (modal) modal.classList.remove("show");
    if (resolver) resolver(value);
  }
  function requestElevationPassword(message) {
    if (lastSystemServiceStatus && lastSystemServiceStatus.running_as_root) return Promise.resolve("");
    return new Promise(function(resolve) {
      elevateResolve = resolve;
      if (qs("elevate-copy")) qs("elevate-copy").textContent = String(message || "此操作需要 root 权限；sudo 密码只用于本次请求，不会保存。");
      if (qs("elevate-status")) setStatus("elevate-status", "密码只用于这次操作，不会写入配置文件或浏览器存储。", false);
      if (qs("elevate-modal")) qs("elevate-modal").classList.add("show");
      window.setTimeout(function() {
        if (qs("elevate-pass")) qs("elevate-pass").focus();
      }, 40);
    });
  }
  async function privilegedBody(base, message) {
    var body = Object.assign({}, base || {});
    if (lastSystemServiceStatus && lastSystemServiceStatus.running_as_root) return body;
    var pwd = await requestElevationPassword(message);
    if (pwd == null) throw new Error("已取消提权");
    body.sudo_password = String(pwd || "");
    return body;
  }
  function v(id) {
    return String(qs(id) && qs(id).value || "").trim();
  }
  function n(id) {
    var x = v(id);
    if (!x) return null;
    var f = Number(x);
    return isFinite(f) ? f : null;
  }
  function check(id) {
    return !!(qs(id) && qs(id).checked);
  }
  function cloneJson(obj) {
    return JSON.parse(JSON.stringify(obj == null ? null : obj));
  }
  function sameJson(a, b) {
    return JSON.stringify(a == null ? null : a) === JSON.stringify(b == null ? null : b);
  }
  function loadTheme() {
    try {
      var s = localStorage.getItem("rid_ui_theme");
      if (s === "dark" || s === "light") return s;
    } catch (_e) {
    }
    if (window.matchMedia && window.matchMedia("(prefers-color-scheme: light)").matches) return "light";
    return "dark";
  }
  function applyTheme(theme) {
    var light = theme === "light";
    document.body.classList.toggle("theme-light", light);
    document.body.classList.toggle("theme-dark", !light);
    try {
      localStorage.setItem("rid_ui_theme", light ? "light" : "dark");
    } catch (_e) {
    }
    qs("btn-theme").textContent = light ? "深色" : "浅色";
  }
  function loadBrowserPrefs() {
    var newFw = qs("pref-new-firmware-parser");
    cookieDelete(COOKIE_TRACK_REALTIME);
    cookieDelete(COOKIE_TRACK_2H_ONLY);
    if (newFw) {
      try {
        newFw.checked = localStorage.getItem(NEW_FIRMWARE_PARSE_KEY) !== "0";
      } catch (_e) {
        newFw.checked = true;
      }
    }
  }
  function saveBrowserPrefs() {
    var newFw = qs("pref-new-firmware-parser");
    cookieDelete(COOKIE_TRACK_REALTIME);
    cookieDelete(COOKIE_TRACK_2H_ONLY);
    if (newFw) {
      try {
        localStorage.setItem(NEW_FIRMWARE_PARSE_KEY, newFw.checked ? "1" : "0");
      } catch (_e) {
      }
    }
    showNotice("页面偏好已保存到当前浏览器。", "ok", 2200);
  }
  function renderEulaState(eula) {
    eula = eula || {};
    var status = qs("status-eula");
    var revokeBtn = qs("btn-eula-revoke");
    if (status) {
      status.textContent = (eula.accepted ? "已同意许可协议。" : "还没有同意许可协议。") + "\n状态文件 " + String(eula.set_path || "EULA.set") + "\n协议来源 " + String(eula.source_url || "");
      status.classList.toggle("err", !eula.accepted);
    }
    if (revokeBtn) revokeBtn.disabled = !eula.accepted;
  }
  async function revokeEulaAcceptance() {
    if (!confirm("撤回后会立刻回到许可协议确认页。确定继续吗？")) return;
    var btn = qs("btn-eula-revoke");
    if (btn) btn.disabled = true;
    setStatus("status-eula", "正在撤回许可协议同意状态...", false);
    try {
      const data = await postJson("/api/eula/revoke", {});
      setStatus("status-eula", "已撤回同意，即将跳转到 EULA 页面。\n状态文件 " + String(data.set_path || ""), true);
      showNotice("已撤回 EULA 同意状态。", "warn", 2600);
      window.setTimeout(function() {
        location.href = "/eula?next=/settings";
      }, 700);
    } catch (e) {
      setStatus("status-eula", "撤回失败：" + (e.message || e), true);
      showNotice(e.message || e, "warn", 3600);
      if (btn) btn.disabled = false;
    }
  }
  async function ensureTabLoaded(tab) {
    if (tab === "raw" && !settingsState.rawLoaded) {
      await loadRaw();
      settingsState.rawLoaded = true;
    }
  }
  function activateTab(tab) {
    qsa(".tab").forEach(function(btn) {
      btn.classList.toggle("active", btn.getAttribute("data-tab") === tab);
    });
    qsa(".panel").forEach(function(p) {
      p.classList.toggle("active", p.getAttribute("data-tab") === tab);
    });
    ensureTabLoaded(tab).catch(function(e) {
      if (tab === "raw") setStatus("status-raw", e.message || e, true);
    });
  }
  function applyTabs() {
    qsa(".tab").forEach(function(btn) {
      btn.addEventListener("click", function() {
        activateTab(btn.getAttribute("data-tab") || "visual");
      });
    });
  }
  function fmtPct(v2) {
    return v2 == null || !isFinite(v2) ? "—" : Number(v2).toFixed(1) + "%";
  }
  function fmtMb(used, total) {
    if (used == null || total == null || !isFinite(used) || !isFinite(total)) return "—";
    return String(used) + " / " + String(total) + " MB";
  }
  function fmtSecShort(sec) {
    sec = Number(sec);
    if (!isFinite(sec) || sec < 0) return "—";
    if (sec < 60) return Math.round(sec) + "s";
    if (sec < 3600) return Math.round(sec / 60) + "m";
    if (sec < 86400) return Math.round(sec / 3600) + "h";
    return Math.round(sec / 86400) + "d";
  }
  function checkedAuthLoginMethods() {
    var out = [];
    if (check("cfg-auth-method-password")) out.push("password");
    if (check("cfg-auth-method-passkey")) out.push("passkey");
    return out;
  }
  function ensureAuthLoginMethodSelection(preferredId, noisy) {
    var methods = checkedAuthLoginMethods();
    if (methods.length) return methods;
    var fallbackId = preferredId || "cfg-auth-method-password";
    if (qs(fallbackId)) qs(fallbackId).checked = true;
    methods = checkedAuthLoginMethods();
    if (noisy) {
      if (qs("auth-method-state")) qs("auth-method-state").textContent = "至少保留一种网页登录方式。账号密码仍用于设置页二次确认。";
      showNotice("至少保留一种网页登录方式。", "warn", 2400);
    }
    return methods;
  }
  function syncAuthMethodUi() {
    var methods = ensureAuthLoginMethodSelection("", false);
    var authEnabled = check("cfg-auth-enabled");
    var authConfigured = !!settingsState.authConfigured;
    var allowPassword = methods.indexOf("password") >= 0;
    var allowPasskey = methods.indexOf("passkey") >= 0;
    if (qs("auth-method-state")) {
      var labels = [];
      if (allowPassword) labels.push("账号密码");
      if (allowPasskey) labels.push("PassKey");
      qs("auth-method-state").textContent = "当前可用方式：" + (labels.join(" / ") || "未选择") + "。至少保留一种网页登录方式。账号密码仍用于二次确认和 PassKey 注册。";
    }
    if (qs("passkey-state")) {
      if (!authEnabled || !authConfigured) {
        qs("passkey-state").textContent = "先配好网页登录账号和密码，再来这里登记通行密钥。";
      } else if (!allowPasskey) {
        qs("passkey-state").textContent = "PassKey 登录当前已关闭；已登记的密钥会保留，但暂时不会生效。";
      } else {
        qs("passkey-state").textContent = "已登记的通行密钥可以直接登录网页。";
      }
    }
    if (qs("login-link-state")) {
      if (!authEnabled || !authConfigured) {
        qs("login-link-state").textContent = "填好网页登录账号和密码后，就可以生成 SSO 链接。";
      } else {
        qs("login-link-state").textContent = "命中有效 SSO 链接时，会优先于密码和 PassKey 登录。";
      }
    }
    if (qs("btn-login-link-create")) qs("btn-login-link-create").disabled = !(authEnabled && authConfigured);
    if (qs("btn-passkey-add")) qs("btn-passkey-add").disabled = !(authEnabled && authConfigured && allowPasskey);
  }
  function renderHostStats(host, basic) {
    var root = qs("host-stats");
    if (!root) return;
    host = host || {};
    basic = basic || {};
    var sniff = host.sniff_state || {};
    var sniffLabel = sniff.state === "ok" ? "正常" : sniff.state === "warn" ? "等待数据" : sniff.state === "error" ? "异常" : "—";
    var localIps = Array.isArray(host.local_ips) && host.local_ips.length ? host.local_ips.map(function(ip) {
      ip = String(ip || "");
      return '<div class="ip-line"><span class="ip-text" title="' + enc(ip) + '">' + enc(ip) + '</span><span class="ip-len">' + ip.length + "</span></div>";
    }).join("") : "—";
    var items = [
      ["主机", host.hostname || "—"],
      ["本机 IP", localIps, "ip-lines"],
      ["CPU", fmtPct(host.cpu_percent)],
      ["内存", fmtPct(host.mem_percent)],
      ["内存容量", fmtMb(host.mem_used_mb, host.mem_total_mb)],
      ["温度", host.temperature_c == null ? "—" : Number(host.temperature_c).toFixed(1) + "°C"],
      ["当前网卡", host.active_iface || basic.iface || "未绑定"],
      ["当前信道", String(host.current_channel || basic.channel_effective || 6)]
    ];
    root.innerHTML = items.map(function(row) {
      var cls = row[2] ? "v " + row[2] : "v";
      var val = row[2] ? String(row[1]) : enc(row[1]);
      return '<div class="stat"><div class="k">' + enc(row[0]) + '</div><div class="' + cls + '">' + val + "</div></div>";
    }).join("");
    var meta = [];
    if (host.cpu_count) meta.push("核心 " + String(host.cpu_count));
    if (Array.isArray(host.ifaces) && host.ifaces.length) meta.push("网卡 " + host.ifaces.map(function(x) {
      return String(x.name || "");
    }).filter(Boolean).join(", "));
    if (host.load1 != null) meta.push("负载 " + String(host.load1) + "/" + String(host.load5) + "/" + String(host.load15));
    if (host.uptime_sec != null) meta.push("运行 " + fmtSecShort(host.uptime_sec));
    if (host.temperature_source_label) meta.push("温度源 " + String(host.temperature_source_label));
    if (sniff.state) meta.push("采集 " + sniffLabel);
    if (sniff.msg) meta.push(String(sniff.msg));
    qs("host-meta").textContent = meta.length ? meta.join(" | ") : "-";
  }
  function renderSystemServiceStatus(data) {
    data = data || {};
    lastSystemServiceStatus = data;
    var iw = data.iw || {};
    var wirelessToolsMissing = !iw.available || !iw.hostapd_available;
    var sec = data.security || {};
    var lines = [];
    if (data.supported) {
      if (data.registered && data.unit_matches === false) lines.push("当前服务文件和本页生成的启动参数不一致，可点“注册/更新服务”修正。");
      if (data.running_as_root) lines.push("安全提醒：当前网页服务仍在用 root 运行，建议一键修复为 rid 专用账号。");
      if (data.registered && !data.service_uses_dedicated_user) lines.push("安全提醒：当前服务文件还没有声明 rid 专用账号。");
    } else {
      lines.push("systemd 不可用" + (data.reason ? "，" + String(data.reason) : ""));
      if (data.manual_hint) lines.push(String(data.manual_hint));
    }
    if (iw.message && wirelessToolsMissing) lines.push(String(iw.message));
    if (iw.manual_hint && wirelessToolsMissing) lines.push(String(iw.manual_hint));
    if (data.last_error) lines.push("状态读取失败：" + String(data.last_error));
    var securityWarn = !!(data.running_as_root || data.registered && !data.service_uses_dedicated_user || !data.dedicated_user_exists);
    setStatus("status-system-service", lines.join("\n") || "-", wirelessToolsMissing || !!data.supported && securityWarn);
    renderRuntimeSecurityAlert(data, sec);
    var regBtn = qs("btn-service-register");
    if (regBtn) regBtn.disabled = !data.supported || !data.can_elevate || !data.dedicated_user_exists;
    var iwBtn = qs("btn-iw-install");
    if (iwBtn) iwBtn.disabled = !!iw.available && !!iw.hostapd_available || !iw.can_install;
    var repairBtn = qs("btn-security-repair");
    if (repairBtn) repairBtn.disabled = !data.supported || !data.can_elevate;
  }
  function renderRuntimeSecurityAlert(data, sec) {
    var box = qs("runtime-security-alert");
    if (!box) return;
    data = data || {};
    sec = sec || data.security || {};
    var runningRoot = !!(data.running_as_root || sec.running_as_root);
    var serviceOk = !!data.service_uses_dedicated_user && !!data.dedicated_user_exists;
    box.classList.add("show");
    box.classList.toggle("warn", runningRoot || !serviceOk);
    box.classList.toggle("ok", !runningRoot && serviceOk);
    if (qs("runtime-security-title")) {
      qs("runtime-security-title").textContent = runningRoot ? "当前处于 root 权限" : serviceOk ? "运行权限正常" : "专用账号未完成";
    }
    if (qs("runtime-security-copy")) {
      if (runningRoot) {
        qs("runtime-security-copy").textContent = "当前网页服务和采集进程还在用 root 运行，风险较高。点“一键修复”后，会创建或确认 rid 账号，并把 systemd 服务切到 rid 账号运行。";
      } else if (sec && sec.risk === "missing-capabilities") {
        qs("runtime-security-copy").textContent = "当前进程不是 root，但缺少采集所需的网络能力。执行“一键修复”后，会让 systemd 以 rid 账号和所需能力启动服务。";
      } else if (!serviceOk) {
        qs("runtime-security-copy").textContent = "当前进程不是 root，但 systemd 服务还没确认切到 rid 专用账号。需要 root 或临时 sudo 提权来完成修复。";
      } else {
        qs("runtime-security-copy").textContent = "当前服务已经使用 rid 专用账号，采集所需网络能力也已由 systemd 提供。";
      }
    }
  }
  async function loadSystemServiceStatus() {
    const data = await getJson("/api/settings/systemd/status");
    renderSystemServiceStatus(data);
    return data;
  }
  async function registerSystemdServiceFromSettings() {
    if (!confirm("将写入 /etc/systemd/system/light-rid-scanner.service，并启用开机自启。继续吗？")) return;
    var btn = qs("btn-service-register");
    try {
      if (btn) btn.disabled = true;
      setStatus("status-system-service", "正在注册 systemd 服务...", false);
      const body = await privilegedBody({ confirm: true }, "注册/更新 systemd 服务需要 root 权限。请输入 sudo 密码；密码只用于本次请求，不会保存。");
      const data = await postJson("/api/settings/systemd/register", body);
      renderSystemServiceStatus(data && data.status || {});
      showNotice(data.message || "systemd 服务已注册。", "ok", 3600);
    } catch (e) {
      setStatus("status-system-service", "注册失败: " + (e.message || e), true);
      showNotice(e.message || e, "warn", 4200);
    } finally {
      await loadSystemServiceStatus().catch(function() {
      });
    }
  }
  async function installIwFromSettings() {
    if (!confirm("将执行 apt-get update，并安装 iw 与 hostapd。继续？")) return;
    var btn = qs("btn-iw-install");
    try {
      if (btn) btn.disabled = true;
      setStatus("status-system-service", "正在安装无线工具...", false);
      const body = await privilegedBody({ confirm: true }, "安装 iw 和 hostapd 需要 root 权限；密码只用于本次操作。");
      const data = await postJson("/api/settings/iw/install", body);
      if (data.status) renderSystemServiceStatus(data.status);
      showNotice(data.message || "无线工具安装完成。", "ok", 3600);
    } catch (e) {
      setStatus("status-system-service", "无线工具安装失败: " + (e.message || e) + "\n请手动执行: sudo apt-get update && sudo apt-get install -y iw hostapd", true);
      showNotice(e.message || e, "warn", 4600);
    } finally {
      await loadSystemServiceStatus().catch(function() {
      });
    }
  }
  function refreshSystemServiceAfterRestart(delaySec) {
    var delayMs = Math.max(5e3, Number(delaySec || 3) * 1e3 + 4e3);
    var attempts = 0;
    function tick() {
      attempts += 1;
      loadSystemServiceStatus().then(function() {
        setStatus("status-system-service", "服务已自动重启，运行状态已刷新。", false);
        showNotice("服务已自动重启，当前状态已刷新。", "ok", 3600);
      }).catch(function() {
        if (attempts < 8) {
          setTimeout(tick, 2e3);
        } else {
          setStatus("status-system-service", "服务正在重启。如果状态没有恢复，请稍后手动刷新页面。", true);
          showNotice("服务正在重启。如果页面未恢复，请稍后手动刷新。", "warn", 5200);
        }
      });
    }
    setTimeout(tick, delayMs);
  }
  async function repairRuntimeSecurityFromSettings() {
    if (!confirm("将创建或确认 rid 专用账号，授予配置与缓存写权限，把 systemd 服务改为 rid 账号运行，并在完成后自动重启服务。继续吗？")) return;
    var btn = qs("btn-security-repair");
    var restartScheduled = false;
    var restartDelay = 3;
    try {
      if (btn) btn.disabled = true;
      setStatus("status-system-service", "正在修复运行权限...", false);
      const body = await privilegedBody({ confirm: true }, "一键修复需要 root 权限。请输入 sudo 密码；密码只用于创建账号、授权文件和写入 systemd 服务，本系统不会保存。");
      const data = await postJson("/api/settings/security/repair", body);
      restartScheduled = !!(data && data.restart_scheduled);
      restartDelay = Number(data && data.restart_delay_sec || restartDelay);
      renderSystemServiceStatus(data && data.status || {});
      if (restartScheduled) {
        setStatus("status-system-service", "修复完成，服务将在几秒后自动重启；页面可能短暂断开。", false);
        showNotice(data.message || "运行权限已修复，服务即将自动重启。", "ok", 8200);
        refreshSystemServiceAfterRestart(restartDelay);
      } else {
        showNotice(data.message || "运行权限已修复。", "ok", 5200);
      }
    } catch (e) {
      setStatus("status-system-service", "修复失败: " + (e.message || e), true);
      showNotice(e.message || e, "warn", 5200);
    } finally {
      if (!restartScheduled) {
        await loadSystemServiceStatus().catch(function() {
        });
      }
    }
  }
  function renderSettingsRuntime(data) {
    data = data || {};
    var apRoot = qs("settings-ap-list");
    if (apRoot) {
      var aps = Array.isArray(data.aps) ? data.aps.slice(0, 40) : [];
      if (!aps.length) {
        apRoot.innerHTML = '<div class="empty-state">暂无 AP 数据</div>';
      } else {
        apRoot.innerHTML = '<div class="settings-ap-scroll">' + aps.map(function(a, idx) {
          var mac = String(a.mac || "-");
          var ssid = String(a.ssid || "(hidden)");
          var vendor = String(a.vendor || "未知");
          var rssi = a.rssi == null ? "N/A" : String(a.rssi) + "dBm";
          return '<div class="list-row"><div class="settings-ap-row-grid"><div class="micro">#' + (idx + 1) + '</div><div class="clip" title="' + enc(ssid) + '"><b>' + enc(ssid) + '</b><div class="micro clip" title="' + enc(vendor) + '">' + enc(vendor) + '</div></div><div class="micro clip" title="' + enc(mac) + '">' + enc(mac) + "</div><div>" + enc(rssi) + "</div></div></div>";
        }).join("") + "</div>";
      }
    }
    var log = qs("settings-runtime-log");
    if (log) {
      var lines = [];
      if (Array.isArray(data.ap_logs) && data.ap_logs.length) lines = lines.concat(["[AP]"], data.ap_logs);
      if (Array.isArray(data.event_logs) && data.event_logs.length) lines = lines.concat(["", "[EVENT]"], data.event_logs);
      if (Array.isArray(data.scan_logs) && data.scan_logs.length) lines = lines.concat(["", "[SCAN]"], data.scan_logs);
      log.value = lines.join("\n");
    }
    setStatus("status-runtime", "AP " + String((data.aps || []).length || 0) + "/" + String(data.aps_total || 0), false);
    if (data.metrics && Array.isArray(data.metrics.items)) {
      metricsState.items = data.metrics.items;
      drawMetricsChart();
    }
  }
  async function loadRuntimePanel() {
    const data = await getJson("/api/settings/runtime?limit=220");
    renderSettingsRuntime(data);
  }
  function metricWindowSec() {
    if (metricsState.window === "7d") return 7 * 86400;
    if (metricsState.window === "24h") return 24 * 3600;
    return 12 * 3600;
  }
  function fmtMetricTime(ts) {
    var d = new Date(Number(ts || 0) * 1e3);
    if (!isFinite(d.getTime())) return "-";
    return d.toLocaleString();
  }
  function metricNumber(v2) {
    var n2 = Number(v2);
    return isFinite(n2) ? n2 : null;
  }
  function metricRowsSorted() {
    var arr = Array.isArray(metricsState.items) ? metricsState.items.slice() : [];
    arr.sort(function(a, b) {
      return Number(a.ts || 0) - Number(b.ts || 0);
    });
    return arr;
  }
  function metricZoomFactor() {
    var z = Math.max(1, Math.min(100, Number(metricsState.zoom || 1)));
    return Math.pow(24, (z - 1) / 99);
  }
  function metricCurrentRange(rows) {
    var arr = Array.isArray(rows) ? rows : metricRowsSorted();
    var base = metricWindowSec();
    var span = Math.max(1800, base / metricZoomFactor());
    var latest = arr.length ? Number(arr[arr.length - 1].ts || Date.now() / 1e3) : Date.now() / 1e3;
    var first = arr.length ? Number(arr[0].ts || latest) : latest - base;
    var maxPan = Math.max(0, latest - first - span);
    metricsState.panSec = Math.max(0, Math.min(maxPan, Number(metricsState.panSec || 0)));
    var end = latest - Number(metricsState.panSec || 0);
    var start = end - span;
    return { start, end, span, latest, first, maxPan };
  }
  function metricDefs(rows) {
    var apMax = (Array.isArray(rows) ? rows : []).reduce(function(m, x) {
      return Math.max(m, Number(x.ap || 0));
    }, 1);
    return [
      { key: "cpu", label: "CPU", color: "#2899f5", fmt: function(v2) {
        return fmtPct(v2);
      }, axis: function(v2) {
        return Math.round(v2) + "%";
      }, max: 100 },
      { key: "mem", label: "内存", color: "#92c353", fmt: function(v2) {
        return fmtPct(v2);
      }, axis: function(v2) {
        return Math.round(v2) + "%";
      }, max: 100 },
      { key: "temp", label: "温度", color: "#f7630c", fmt: function(v2) {
        return v2 == null ? "—" : Number(v2).toFixed(1) + "°C";
      }, axis: function(v2) {
        return Math.round(v2) + "°";
      }, max: 100 },
      { key: "load", label: "负载", color: "#c19c00", fmt: function(v2) {
        return fmtPct(v2);
      }, axis: function(v2) {
        return Math.round(v2) + "%";
      }, max: 100 },
      { key: "ap", label: "AP数", color: "#8764b8", fmt: function(v2) {
        return v2 == null ? "—" : String(Math.round(Number(v2)));
      }, axis: function(v2) {
        return String(Math.round(v2));
      }, max: Math.max(1, apMax) }
    ];
  }
  function metricTooltipFor(canvas, key) {
    var wrap = canvas ? canvas.parentElement : null;
    if (!wrap) return null;
    var tip = wrap.querySelector(".metric-chart-tip");
    if (!tip) {
      tip = document.createElement("div");
      tip.className = "metric-chart-tip";
      tip.setAttribute("data-metric", key || "");
      wrap.appendChild(tip);
    }
    return tip;
  }
  function metricNearestPoint(rows, key, ts) {
    var best = null, bestDiff = Infinity;
    (Array.isArray(rows) ? rows : []).forEach(function(p) {
      var value = metricNumber(p && p[key]);
      if (value == null) return;
      var pt = Number(p.ts || 0);
      var diff = Math.abs(pt - ts);
      if (diff < bestDiff) {
        bestDiff = diff;
        best = { row: p, ts: pt, value };
      }
    });
    return best;
  }
  function metricSyncZoomControl() {
    var z = Math.max(1, Math.min(100, Number(metricsState.zoom || 1)));
    metricsState.zoom = z;
    var input = qs("metrics-zoom");
    var label = qs("metrics-zoom-value");
    if (input) input.value = String(z);
    if (label) label.textContent = Math.round(metricZoomFactor() * 10) / 10 + "x";
  }
  function metricSetZoom(nextZoom, focusRatio) {
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
  function metricPanByPixels(canvas, dx) {
    var key = canvas && canvas.getAttribute("data-metric");
    var meta = key ? metricsState.chartMeta[key] : null;
    if (!meta || !meta.range) return;
    var plotW = Math.max(1, meta.width - meta.pad.l - meta.pad.r);
    metricsState.panSec = Number(metricsState.panSec || 0) + Number(dx || 0) / plotW * meta.range.span;
    metricCurrentRange(metricRowsSorted());
    drawMetricsChart();
  }
  function metricPointerRatio(canvas, ev) {
    var rect = canvas.getBoundingClientRect();
    if (!rect.width) return 0.5;
    return Math.max(0, Math.min(1, (Number(ev.clientX || 0) - rect.left) / rect.width));
  }
  function metricUpdateHoverFromEvent(canvas, ev) {
    if (!canvas) return;
    metricsState.hover = { key: canvas.getAttribute("data-metric") || "", ratio: metricPointerRatio(canvas, ev) };
    drawMetricsChart();
  }
  function metricClearHover() {
    metricsState.hover = null;
    drawMetricsChart();
  }
  function metricBindCanvasEvents(canvas) {
    if (!canvas || canvas.__metricBound) return;
    canvas.__metricBound = true;
    canvas.addEventListener("wheel", function(ev) {
      ev.preventDefault();
      var step = ev.deltaY < 0 ? 6 : -6;
      metricSetZoom(Number(metricsState.zoom || 1) + step, metricPointerRatio(canvas, ev));
    }, { passive: false });
    canvas.addEventListener("pointerdown", function(ev) {
      if (ev.button != null && ev.button !== 0) return;
      metricsState.drag = { key: canvas.getAttribute("data-metric") || "", lastX: Number(ev.clientX || 0), moved: false };
      var wrap = canvas.parentElement;
      if (wrap) wrap.classList.add("dragging");
      try {
        canvas.setPointerCapture(ev.pointerId);
      } catch (_e) {
      }
      ev.preventDefault();
    });
    canvas.addEventListener("pointermove", function(ev) {
      if (metricsState.drag && metricsState.drag.key === (canvas.getAttribute("data-metric") || "")) {
        var x = Number(ev.clientX || 0);
        var dx = x - Number(metricsState.drag.lastX || x);
        if (Math.abs(dx) >= 1) {
          metricsState.drag.lastX = x;
          metricsState.drag.moved = true;
          metricPanByPixels(canvas, dx);
        }
        ev.preventDefault();
        return;
      }
      metricUpdateHoverFromEvent(canvas, ev);
    });
    function endDrag(ev) {
      var wasDrag = metricsState.drag && metricsState.drag.key === (canvas.getAttribute("data-metric") || "");
      metricsState.drag = null;
      var wrap = canvas.parentElement;
      if (wrap) wrap.classList.remove("dragging");
      try {
        canvas.releasePointerCapture(ev.pointerId);
      } catch (_e) {
      }
      if (wasDrag) metricUpdateHoverFromEvent(canvas, ev);
    }
    canvas.addEventListener("pointerup", endDrag);
    canvas.addEventListener("pointercancel", endDrag);
    canvas.addEventListener("pointerleave", function() {
      if (metricsState.drag) return;
      metricClearHover();
    });
    canvas.addEventListener("dblclick", function() {
      metricsState.zoom = 1;
      metricsState.panSec = 0;
      metricSyncZoomControl();
      metricClearHover();
    });
  }
  function drawMetricsChart() {
    var allRows = metricRowsSorted();
    var range = metricCurrentRange(allRows);
    var rows = allRows.filter(function(x) {
      return Number(x.ts || 0) >= range.start && Number(x.ts || 0) <= range.end;
    });
    var defs = metricDefs(rows);
    metricsState.chartMeta = {};
    defs.forEach(function(def) {
      drawMetricSpark(def, rows, range);
    });
    var last = rows[rows.length - 1] || {};
    var status = qs("status-metrics");
    if (status) {
      var panText = Number(metricsState.panSec || 0) > 1 ? " | 视图偏移 " + Math.round(Number(metricsState.panSec || 0) / 60) + " 分钟" : "";
      status.textContent = rows.length ? "样本 " + rows.length + " | 最新 CPU " + fmtPct(last.cpu) + " / 内存 " + fmtPct(last.mem) + " / 温度 " + (last.temp == null ? "—" : Number(last.temp).toFixed(1) + "°C") + " / AP " + String(last.ap == null ? "—" : last.ap) + " | 视图 " + Math.round(metricZoomFactor() * 10) / 10 + "x" + panText : "暂无负载数据";
    }
  }
  function drawMetricSpark(def, rows, range) {
    var canvas = document.querySelector('.metric-spark[data-metric="' + def.key + '"]');
    var valueEl = qs("metric-value-" + def.key);
    var tip = canvas ? metricTooltipFor(canvas, def.key) : null;
    if (!canvas) return;
    var box = canvas.getBoundingClientRect();
    var dpr = window.devicePixelRatio || 1;
    var cssW = Math.max(260, box.width || (canvas.parentElement ? canvas.parentElement.clientWidth : 0) || 300);
    var cssH = Math.max(110, box.height || (canvas.parentElement ? canvas.parentElement.clientHeight : 0) || 136);
    var w = Math.round(cssW * dpr);
    var h = Math.round(cssH * dpr);
    if (canvas.width !== w) canvas.width = w;
    if (canvas.height !== h) canvas.height = h;
    var ctx = canvas.getContext("2d");
    ctx.clearRect(0, 0, w, h);
    var styles = getComputedStyle(document.body);
    var border = (styles.getPropertyValue("--border") || "#444").trim();
    var muted = (styles.getPropertyValue("--muted") || "#888").trim();
    var txt = (styles.getPropertyValue("--txt") || "#fff").trim();
    var pad = { l: 42, r: 12, t: 10, b: 24 };
    var padPx = { l: pad.l * dpr, r: pad.r * dpr, t: pad.t * dpr, b: pad.b * dpr };
    var plotW = Math.max(1, w - padPx.l - padPx.r);
    var plotH = Math.max(1, h - padPx.t - padPx.b);
    var start = range ? Number(range.start || 0) : 0;
    var end = range ? Number(range.end || start + 1) : 1;
    if (end <= start) end = start + 1;
    metricsState.chartMeta[def.key] = { width: cssW, height: cssH, pad, range: { start, end, span: end - start }, rows, def };
    if (tip) tip.style.display = "none";
    ctx.strokeStyle = border;
    ctx.lineWidth = 1 * dpr;
    ctx.font = String(10 * dpr) + "px sans-serif";
    ctx.fillStyle = muted;
    ctx.textBaseline = "middle";
    ctx.beginPath();
    for (var gi = 0; gi <= 4; gi++) {
      var gy = padPx.t + plotH * gi / 4;
      ctx.moveTo(padPx.l, gy);
      ctx.lineTo(w - padPx.r, gy);
      var gv = Math.max(0, Number(def.max || 100)) * (1 - gi / 4);
      ctx.fillText(def.axis ? def.axis(gv) : String(Math.round(gv)), 4 * dpr, gy);
    }
    for (var vi = 0; vi <= 4; vi++) {
      var gx = padPx.l + plotW * vi / 4;
      ctx.moveTo(gx, padPx.t);
      ctx.lineTo(gx, h - padPx.b);
    }
    ctx.stroke();
    if (!rows.length) {
      if (valueEl) valueEl.textContent = "—";
      ctx.fillStyle = muted;
      ctx.font = String(12 * dpr) + "px sans-serif";
      ctx.fillText("暂无数据", padPx.l + 4 * dpr, h / 2);
      return;
    }
    function rawValue(p) {
      return metricNumber(p[def.key]);
    }
    var lastVal = null;
    for (var li = rows.length - 1; li >= 0; li--) {
      lastVal = rawValue(rows[li]);
      if (lastVal != null) break;
    }
    if (valueEl) valueEl.textContent = def.fmt(lastVal);
    function xFor(ts) {
      return padPx.l + (Number(ts || start) - start) / (end - start) * plotW;
    }
    function yFor(v2) {
      var maxV = Math.max(1, Number(def.max || 100));
      var n2 = Math.max(0, Math.min(maxV, Number(v2 || 0)));
      return padPx.t + (1 - n2 / maxV) * plotH;
    }
    var drawn = false;
    var firstPt = null, lastPt = null;
    ctx.beginPath();
    rows.forEach(function(p) {
      var raw = rawValue(p);
      if (raw == null) return;
      var x = xFor(p.ts), y = yFor(raw);
      if (!drawn) {
        ctx.moveTo(x, y);
        firstPt = { x, y };
        drawn = true;
      } else ctx.lineTo(x, y);
      lastPt = { x, y };
    });
    if (drawn) {
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
      rows.forEach(function(p) {
        var raw = rawValue(p);
        if (raw == null) return;
        var x = xFor(p.ts), y = yFor(raw);
        if (!drawn) {
          ctx.moveTo(x, y);
          drawn = true;
        } else ctx.lineTo(x, y);
      });
      ctx.strokeStyle = def.color;
      ctx.lineWidth = 2 * dpr;
      ctx.stroke();
    }
    ctx.fillStyle = muted;
    ctx.textBaseline = "alphabetic";
    ctx.font = String(10 * dpr) + "px sans-serif";
    ctx.fillText(fmtMetricTime(start).replace(/^[0-9]{4}[/]/, ""), padPx.l, h - 6 * dpr);
    var endLabel = fmtMetricTime(end).replace(/^[0-9]{4}[/]/, "");
    var endW = ctx.measureText(endLabel).width;
    ctx.fillText(endLabel, Math.max(padPx.l, w - padPx.r - endW), h - 6 * dpr);
    if (metricsState.hover && metricsState.hover.key === def.key) {
      var ratio = Math.max(0, Math.min(1, Number(metricsState.hover.ratio || 0)));
      var targetTs = start + (end - start) * ratio;
      var hit = metricNearestPoint(rows, def.key, targetTs);
      if (hit) {
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
        if (tip) {
          var cssX = hx / dpr, cssY = hy / dpr;
          tip.classList.toggle("below", cssY < 52);
          tip.style.left = Math.max(74, Math.min(cssW - 74, cssX)) + "px";
          tip.style.top = Math.max(18, Math.min(cssH - 18, cssY)) + "px";
          tip.textContent = def.label + "  " + def.fmt(hit.value) + "\n" + fmtMetricTime(hit.ts);
          tip.style.display = "block";
        }
      }
    }
  }
  async function loadMetrics() {
    if (!check("cfg-metrics-enabled")) {
      metricsState.items = [];
      drawMetricsChart();
      if (qs("status-metrics")) qs("status-metrics").textContent = "节点负载记录已关闭；开启并保存后开始采样。";
      return;
    }
    const data = await getJson("/api/settings/metrics?window=" + encodeURIComponent(metricsState.window || "12h"));
    metricsState.items = Array.isArray(data.items) ? data.items : [];
    if (data.enabled === false) {
      metricsState.items = [];
      drawMetricsChart();
      if (qs("status-metrics")) qs("status-metrics").textContent = "节点负载记录已关闭；开启并保存后开始采样。";
      return;
    }
    if (qs("status-metrics") && data.store_path) {
      qs("status-metrics").textContent = "数据文件: " + String(data.store_path);
    }
    drawMetricsChart();
  }
  function setMetricWindow(win) {
    metricsState.window = win === "7d" || win === "24h" ? win : "12h";
    metricsState.panSec = 0;
    metricsState.hover = null;
    qsa(".metric-window").forEach(function(btn) {
      btn.classList.toggle("active", btn.getAttribute("data-window") === metricsState.window);
    });
    loadMetrics().catch(function(e) {
      if (qs("status-metrics")) qs("status-metrics").textContent = e.message || String(e);
    });
  }
  async function updateModelsNow() {
    var btn = qs("btn-model-update-now");
    try {
      if (btn) btn.disabled = true;
      if (qs("model-update-state")) qs("model-update-state").textContent = "正在更新识别库...";
      const data = await postJson("/api/settings/models/update", { url: v("cfg-model-update-url") });
      if (qs("model-update-state")) qs("model-update-state").textContent = data.message || "识别库已更新。";
      showNotice(data.message || "识别库已更新。", "ok", 3e3);
      await loadVisual();
    } catch (e) {
      if (qs("model-update-state")) qs("model-update-state").textContent = "更新失败: " + (e.message || e);
      showNotice(e.message || e, "warn", 4200);
    } finally {
      if (btn) btn.disabled = false;
    }
  }
  function renderAppUpdateState(state) {
    var el = qs("app-update-state");
    if (!el) return;
    state = state || {};
    var currentTag = String(state.current_tag || "").trim();
    var latestTag = String(state.latest_tag || "").trim();
    var currentCommit = state.current_short || (state.current_commit ? String(state.current_commit).slice(0, 12) : "");
    var latestCommit = state.latest_short || (state.latest_commit ? String(state.latest_commit).slice(0, 12) : "");
    var lines = ["当前 Tag: " + (currentTag || "未知")];
    lines.push("最新 Tag: " + (latestTag || "尚未检查"));
    lines.push("当前 commit: " + (currentCommit || "未知"));
    if (latestCommit) lines.push("Release commit: " + latestCommit);
    if (state.target_arch) lines.push("架构: " + String(state.target_arch));
    if (state.running) lines.push("正在检查版本...");
    else if (state.installing) lines.push("更新状态: " + String(state.install_message || state.install_status || "进行中"));
    else if (state.last_error) lines.push("检查/更新失败: " + String(state.last_error));
    else if (state.checked) lines.push(state.update_available ? "发现新版本，可直接执行自动更新。" : "当前已是检查到的最新版本。");
    else lines.push("启用后会检查 GitHub Release，并在满足条件时执行自动更新。");
    if (state.install_supported === false && state.support_reason) lines.push("当前环境: " + String(state.support_reason));
    if (state.asset_name) lines.push("匹配资产: " + String(state.asset_name));
    el.textContent = lines.join(" | ");
    if (qs("btn-app-update-start")) {
      qs("btn-app-update-start").disabled = !!state.running || !!state.installing || !state.update_available || state.install_supported === false;
    }
    if (state.completion_notice && state.completion_notice.text) {
      showNotice(String(state.completion_notice.text), "ok", 5200);
    }
  }
  async function checkAppVersionNow() {
    var btn = qs("btn-app-update-check");
    try {
      if (btn) btn.disabled = true;
      renderAppUpdateState({ running: true });
      const data = await postJson("/api/settings/app-update/check", {});
      renderAppUpdateState(data && data.state || {});
      showNotice(data && data.state && data.state.update_available ? "发现新版本，请手动更新。" : "版本检查完成。", "ok", 3e3);
    } catch (e) {
      showNotice(e.message || e, "warn", 4200);
    } finally {
      if (btn) btn.disabled = false;
    }
  }
  function pollAppUpdateAfterRestart() {
    var attempts = 0;
    function tick() {
      attempts += 1;
      getJson("/api/settings/view").then(function(data) {
        var state = (((data || {}).visual || {}).app_update || {}).state || {};
        renderAppUpdateState(state);
        if (state.completion_notice && state.completion_notice.text) {
          setStatus("status-visual", String(state.completion_notice.text), false);
          return;
        }
        if (attempts < 25) {
          setTimeout(tick, 2e3);
        }
      }).catch(function() {
        if (attempts < 25) setTimeout(tick, 2e3);
      });
    }
    setTimeout(tick, 7e3);
  }
  async function startAppUpdateNow() {
    if (!confirm("将下载最新 GitHub Release 的当前架构资产，并自动停止服务、备份旧文件、替换新文件后重新启动。继续吗？")) return;
    var btn = qs("btn-app-update-start");
    try {
      if (btn) btn.disabled = true;
      setStatus("status-visual", "正在准备自动更新...", false);
      renderAppUpdateState({ installing: true, install_status: "preparing" });
      const body = await privilegedBody({ confirm: true }, "自动更新需要停止/启动 systemd 并替换已安装文件。请输入 sudo 密码；密码只用于本次更新，不会保存。");
      const data = await postJson("/api/settings/app-update/start", body);
      renderAppUpdateState(data && data.state || {});
      setStatus("status-visual", data && data.message || "更新进程已启动，服务将短暂重启。", false);
      showNotice(data && data.message || "更新进程已启动。", "ok", 4200);
      if (data && data.restart_expected) pollAppUpdateAfterRestart();
    } catch (e) {
      setStatus("status-visual", "自动更新失败: " + (e.message || e), true);
      showNotice(e.message || e, "warn", 4800);
    } finally {
      if (btn) btn.disabled = false;
    }
  }
  function cleanModelPrefix(prefix) {
    return String(prefix == null ? "" : prefix).toUpperCase().replace(/[^0-9A-Z]/g, "").slice(0, 32);
  }
  function syncModelRowsFromInputs() {
    qsa("#model-map-list .model-map-row").forEach(function(row) {
      var idx = Number(row.getAttribute("data-index"));
      if (!isFinite(idx) || !modelMapRows[idx]) return;
      var p = row.querySelector(".model-prefix");
      var m = row.querySelector(".model-name");
      modelMapRows[idx].prefix = cleanModelPrefix(p ? p.value : "");
      modelMapRows[idx].model = String(m && m.value || "").trim();
      if (p) p.value = modelMapRows[idx].prefix;
    });
  }
  function filteredModelRows() {
    var q = String(qs("model-map-search") && qs("model-map-search").value || "").trim().toLowerCase();
    return modelMapRows.map(function(row, idx) {
      return { idx, prefix: String(row.prefix || ""), model: String(row.model || "") };
    }).filter(function(row) {
      if (!q) return true;
      return row.prefix.toLowerCase().indexOf(q) >= 0 || row.model.toLowerCase().indexOf(q) >= 0;
    });
  }
  function renderModelMapRows() {
    var root = qs("model-map-list");
    if (!root) return;
    var rows = filteredModelRows();
    if (!rows.length) {
      root.innerHTML = '<div class="model-map-empty">暂无匹配条目。</div>';
    } else {
      root.innerHTML = rows.map(function(row) {
        return '<div class="model-map-row" data-index="' + row.idx + '"><input class="model-prefix" value="' + enc(row.prefix) + '" maxlength="32" spellcheck="false" placeholder="前缀"><input class="model-name" value="' + enc(row.model) + '" spellcheck="false" placeholder="机型名称"><button class="btn warn model-row-delete" type="button">删除</button></div>';
      }).join("");
    }
    var state = qs("model-map-editor-state");
    if (state) {
      var suffix = modelMapPath ? " | " + modelMapPath : "";
      state.textContent = "当前 " + String(modelMapRows.length) + " 条，保存后会立即刷新实时与历史机型。" + suffix;
    }
  }
  function collectModelMapRows() {
    syncModelRowsFromInputs();
    var seen = {};
    var out = [];
    modelMapRows.forEach(function(row) {
      var prefix = cleanModelPrefix(row && row.prefix);
      var model = String(row && row.model || "").trim();
      if (!prefix && !model) return;
      if (!prefix || !model) return;
      seen[prefix] = model;
    });
    Object.keys(seen).sort().forEach(function(prefix) {
      out.push({ prefix, model: seen[prefix] });
    });
    return out;
  }
  function addModelMapRow(prefix, model) {
    syncModelRowsFromInputs();
    modelMapRows.unshift({ prefix: cleanModelPrefix(prefix), model: String(model || "").trim() });
    if (qs("model-map-search")) qs("model-map-search").value = "";
    renderModelMapRows();
    var first = document.querySelector("#model-map-list .model-map-row input");
    if (first) first.focus();
  }
  async function loadModelEditor() {
    const data = await getJson("/api/settings/models/list");
    modelMapRows = (Array.isArray(data.items) ? data.items : []).map(function(row) {
      return { prefix: cleanModelPrefix(row && row.prefix), model: String(row && row.model || "").trim() };
    });
    modelMapPath = String(data.path || "");
    renderModelMapRows();
    if (data.warning && qs("model-map-editor-state")) {
      qs("model-map-editor-state").textContent = String(data.warning);
    }
  }
  async function saveModelEditor() {
    var btn = qs("btn-model-map-save");
    try {
      if (btn) btn.disabled = true;
      var items = collectModelMapRows();
      const data = await postJson("/api/settings/models/save", { items });
      modelMapRows = (Array.isArray(data.items) ? data.items : items).map(function(row) {
        return { prefix: cleanModelPrefix(row && row.prefix), model: String(row && row.model || "").trim() };
      });
      modelMapPath = String(data.path || modelMapPath || "");
      renderModelMapRows();
      if (qs("model-update-state") && data.state) {
        qs("model-update-state").textContent = "已加载 " + String(data.state && data.state.loaded_count || modelMapRows.length) + " 条";
      }
      showNotice(data.message || "识别库已保存。", "ok", 2600);
    } catch (e) {
      showNotice(e.message || e, "warn", 4200);
      if (qs("model-map-editor-state")) qs("model-map-editor-state").textContent = "保存失败: " + (e.message || e);
    } finally {
      if (btn) btn.disabled = false;
    }
  }
  function collectVisualPayload() {
    return {
      basic: {
        iface: v("cfg-iface") || null,
        channel: settingsState.channelUseDefault ? null : n("cfg-channel"),
        channel_use_default: !!settingsState.channelUseDefault,
        time: n("cfg-time"),
        min_gap: n("cfg-min-gap"),
        lost_timeout: n("cfg-lost-timeout"),
        rssi_delta: n("cfg-rssi-delta"),
        model_map: v("cfg-model-map"),
        history_file: v("cfg-history-file"),
        auto_self_heal: check("cfg-heal"),
        change_on_rssi: check("cfg-rssi-change"),
        change_on_payload: check("cfg-payload-change"),
        debug: check("cfg-debug"),
        dwell_2g: n("cfg-dwell2g"),
        dwell_5g: n("cfg-dwell5g"),
        settle: n("cfg-settle"),
        dwell_on_hit: n("cfg-hit-dwell"),
        hit_cap: n("cfg-hit-cap"),
        hop: check("cfg-hop"),
        hop_5g: check("cfg-hop5g"),
        scan_wifi_fast: check("cfg-fast"),
        no_tui: true
      },
      web: {
        dji_lookup_url: v("cfg-dji-url"),
        base_name: v("cfg-base-name"),
        base_lat: n("cfg-base-lat"),
        base_lon: n("cfg-base-lon"),
        base_zoom: n("cfg-base-zoom"),
        heading_ref_deg: n("cfg-heading-ref"),
        map_auto_center_idle_sec: n("cfg-map-idle"),
        access_list_enabled: check("cfg-web-access-enabled"),
        access_list_mode: v("cfg-web-access-mode") || "allow",
        access_list: splitLines(qs("cfg-web-access-list").value || ""),
        alarm_zones: collectZoneRows()
      },
      notify: {
        enabled: check("cfg-notify-enabled"),
        notify_reonline: check("cfg-notify-reonline"),
        reonline_cooldown_sec: n("cfg-reonline"),
        send_timeout_sec: n("cfg-send-timeout"),
        wecom_webhooks: collectHookRows()
      },
      api: {
        enabled: check("cfg-api-enabled"),
        whitelist_enabled: check("cfg-api-whitelist-enabled"),
        whitelist_mode: v("cfg-api-whitelist-mode") || "allow",
        whitelist: splitLines(qs("cfg-api-whitelist").value || "")
      },
      auth: {
        enabled: check("cfg-auth-enabled"),
        realm: v("cfg-auth-realm"),
        session_ttl_min: n("cfg-auth-ttl"),
        login_methods: ensureAuthLoginMethodSelection("", false),
        username: v("cfg-auth-user") || "__KEEP__",
        password: String(qs("cfg-auth-pass") && qs("cfg-auth-pass").value || "").trim() || "__KEEP__"
      },
      model_update: {
        enabled: check("cfg-model-update-enabled"),
        url: v("cfg-model-update-url")
      },
      app_update: {
        enabled: check("cfg-app-update-enabled")
      },
      metrics: {
        enabled: check("cfg-metrics-enabled"),
        retention_days: n("cfg-metrics-retention"),
        temperature_source: v("cfg-metrics-temp-source") || "auto"
      },
      network_bindings: collectNetworkBindings()
    };
  }
  function mergeCheckboxValues(base, current) {
    if (typeof current === "boolean") return current;
    if (Array.isArray(base) || Array.isArray(current)) {
      var baseArr = Array.isArray(base) ? base : [];
      var curArr = Array.isArray(current) ? current : [];
      return baseArr.map(function(item, idx) {
        return mergeCheckboxValues(item, curArr[idx]);
      });
    }
    if (base && typeof base === "object") {
      var out = cloneJson(base);
      if (current && typeof current === "object") {
        Object.keys(current).forEach(function(key) {
          if (Object.prototype.hasOwnProperty.call(out, key)) {
            out[key] = mergeCheckboxValues(out[key], current[key]);
          }
        });
      }
      return out;
    }
    return base;
  }
  function collectCheckboxOnlyVisualPayload() {
    var base = settingsState.visualInitial ? cloneJson(settingsState.visualInitial) : collectVisualPayload();
    var current = collectVisualPayload();
    return mergeCheckboxValues(base, current);
  }
  function visualPayloadSections(payload) {
    payload = payload || {};
    return {
      capture: Object.assign({}, payload.basic || {}, { model_update: payload.model_update || {}, app_update: payload.app_update || {}, network_bindings: payload.network_bindings || {} }),
      map: {
        dji_lookup_url: (payload.web || {}).dji_lookup_url,
        base_name: (payload.web || {}).base_name,
        base_lat: (payload.web || {}).base_lat,
        base_lon: (payload.web || {}).base_lon,
        base_zoom: (payload.web || {}).base_zoom,
        heading_ref_deg: (payload.web || {}).heading_ref_deg,
        map_auto_center_idle_sec: (payload.web || {}).map_auto_center_idle_sec
      },
      zones: { alarm_zones: (payload.web || {}).alarm_zones || [] },
      access: {
        web_access: {
          access_list_enabled: (payload.web || {}).access_list_enabled,
          access_list_mode: (payload.web || {}).access_list_mode,
          access_list: (payload.web || {}).access_list || []
        },
        notify: payload.notify || {},
        api: payload.api || {},
        auth: payload.auth || {}
      },
      metrics: payload.metrics || {}
    };
  }
  function setDraftUi(dirtyMap) {
    dirtyMap = dirtyMap || {};
    settingsState.dirtyCards = dirtyMap;
    settingsState.visualDirty = Object.keys(dirtyMap).some(function(k) {
      return !!dirtyMap[k];
    });
    qsa(".card[data-card-key]").forEach(function(card) {
      var key = card.getAttribute("data-card-key") || "";
      card.classList.toggle("dirty", !!dirtyMap[key]);
    });
    if (qs("btn-test-visual")) qs("btn-test-visual").disabled = !settingsState.visualDirty;
    if (qs("btn-save-visual")) qs("btn-save-visual").disabled = !settingsState.visualDirty;
    if (qs("draft-title")) qs("draft-title").textContent = settingsState.visualDirty ? "有未保存修改" : "当前没有未保存修改";
    if (qs("draft-meta")) {
      var names = SETTINGS_DRAFT_SECTIONS.filter(function(item) {
        return !!dirtyMap[item.key];
      }).map(function(item) {
        return item.label;
      });
      qs("draft-meta").textContent = settingsState.visualDirty ? "已改动: " + names.join("、") + "。复选框会立即保存，输入内容需点击保存。" : "当前没有未保存修改。";
    }
  }
  function updateVisualDraftState() {
    if (!settingsState.visualLoaded || !settingsState.visualInitial) return;
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
  function resetVisualDraftState() {
    settingsState.visualInitial = cloneJson(collectVisualPayload());
    setDraftUi({});
  }
  function bindVisualDraftTracking() {
    var root = document.querySelector('.panel[data-tab="visual"]');
    if (!root || root.getAttribute("data-dirty-bind") === "1") return;
    root.setAttribute("data-dirty-bind", "1");
    root.addEventListener("input", function(ev) {
      updateVisualDraftState();
    });
    root.addEventListener("change", function(ev) {
      updateVisualDraftState();
      var target = ev && ev.target;
      if (target && String(target.type || "").toLowerCase() === "checkbox") {
        scheduleVisualCheckboxSave();
      }
    });
  }
  function scheduleVisualCheckboxSave() {
    if (!settingsState.visualLoaded) return;
    if (visualCheckboxSaveTimer) clearTimeout(visualCheckboxSaveTimer);
    visualCheckboxSaveTimer = window.setTimeout(async function() {
      visualCheckboxSaveTimer = null;
      try {
        setVisualActionBusy(true);
        setStatus("status-visual", "正在保存勾选项...", false);
        await saveVisual({ auto: true, checkboxOnly: true });
      } catch (e) {
        setStatus("status-visual", e.message || e, true);
        showNotice(e.message || e, "warn", 3800);
      } finally {
        setVisualActionBusy(false);
      }
    }, 160);
  }
  function setVisualActionBusy(busy) {
    ["btn-test-visual", "btn-save-visual", "btn-save-visual-direct", "btn-reload-view"].forEach(function(id) {
      var el = qs(id);
      if (!el) return;
      if (id === "btn-test-visual" || id === "btn-save-visual") {
        el.disabled = !!busy || !settingsState.visualDirty;
      } else {
        el.disabled = !!busy;
      }
    });
  }
  function setChannelUi(editing) {
    settingsState.channelEditing = !!editing;
    var input = qs("cfg-channel");
    var editBtn = qs("btn-channel-edit");
    var resetBtn = qs("btn-channel-reset");
    var hint = qs("channel-hint");
    if (input) input.disabled = !editing;
    if (editBtn) editBtn.textContent = editing ? "锁定" : "编辑";
    if (resetBtn) resetBtn.style.display = settingsState.channelUseDefault ? "none" : "";
    if (hint) {
      hint.textContent = "";
      hint.style.display = "none";
    }
  }
  function openReauth(action) {
    reauthAction = action;
    qs("reauth-user").value = "";
    qs("reauth-pass").value = "";
    setStatus("reauth-status", "二次验证使用网页登录账号和密码。", false);
    qs("reauth-modal").classList.add("show");
    window.setTimeout(function() {
      try {
        qs("reauth-user").focus();
      } catch (_e) {
      }
    }, 30);
  }
  function closeReauth() {
    reauthAction = null;
    qs("reauth-modal").classList.remove("show");
  }
  function showOneTimeSecret(title, secret, note) {
    oneTimeSecretValue = String(secret || "");
    qs("one-time-title").textContent = String(title || "只显示一次");
    qs("one-time-note").textContent = String(note || "关闭后不能再次查看或复制。");
    qs("one-time-secret").textContent = oneTimeSecretValue;
    qs("one-time-modal").classList.add("show");
  }
  function closeOneTimeSecret() {
    oneTimeSecretValue = "";
    qs("one-time-secret").textContent = "";
    qs("one-time-modal").classList.remove("show");
  }
  function b64uToBytes(text) {
    var raw = String(text || "").replace(/-/g, "+").replace(/_/g, "/");
    while (raw.length % 4) raw += "=";
    if (!raw) return new Uint8Array(0);
    var bin = atob(raw);
    var out = new Uint8Array(bin.length);
    for (var i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
    return out;
  }
  function bytesToB64u(bytes) {
    var view = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes || []);
    var bin = "";
    for (var i = 0; i < view.length; i++) bin += String.fromCharCode(view[i]);
    return btoa(bin).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
  }
  function formatMtime(ts) {
    var d = new Date(Number(ts || 0) * 1e3);
    return isFinite(d.getTime()) ? d.toLocaleString() : "-";
  }
  function rawActivePath() {
    return String(settingsState.rawSelectedPath || "");
  }
  function rawDirContainsSelected(node, selectedPath) {
    var selected = String(selectedPath || "");
    if (!selected || !node) return false;
    var base = String(node.path || "");
    if (base && selected.indexOf(base + "\\") === 0) return true;
    if (base && selected.indexOf(base + "/") === 0) return true;
    var children = Array.isArray(node.children) ? node.children : [];
    for (var i = 0; i < children.length; i++) {
      var child = children[i] || {};
      if (child.type === "file" && String(child.path || "") === selected) return true;
      if (child.type === "dir" && rawDirContainsSelected(child, selected)) return true;
    }
    return false;
  }
  function rawSetMeta(data) {
    data = data || {};
    if (qs("raw-tree-path")) qs("raw-tree-path").textContent = String(data.root || settingsState.rawRoot || "-");
    if (qs("raw-file-title")) qs("raw-file-title").textContent = String(data.name || (data.rel_path && String(data.rel_path) !== "-" ? data.rel_path : "") || (data.path && String(data.path) !== "-" ? data.path : "") || "未选择文件");
    if (qs("raw-file-path")) qs("raw-file-path").textContent = String(data.rel_path || data.path || "-");
    if (qs("raw-file-size")) qs("raw-file-size").textContent = data.size == null ? "-" : formatBytes(data.size);
    if (qs("raw-file-mtime")) qs("raw-file-mtime").textContent = data.mtime ? formatMtime(data.mtime) : "-";
  }
  function rawSetLocked(isLocked, message) {
    var card = qs("raw-lock-card");
    var layout = qs("raw-layout");
    if (card) card.style.display = isLocked ? "grid" : "none";
    if (layout) layout.style.opacity = isLocked ? "0.55" : "1";
    var editor = qs("raw-editor");
    if (editor) editor.disabled = !!isLocked;
    ["btn-save-raw", "btn-delete-raw", "btn-load-raw"].forEach(function(id) {
      var el = qs(id);
      if (el) el.disabled = !!isLocked && id !== "btn-load-raw";
    });
    if (qs("raw-lock-copy") && message) qs("raw-lock-copy").textContent = String(message);
  }
  function rawRenderTreeNodes(nodes, selectedPath) {
    var list = Array.isArray(nodes) ? nodes : [];
    if (!list.length) return '<div class="empty-state">暂无配置文件</div>';
    return list.map(function(node) {
      node = node || {};
      var type = String(node.type || "file");
      var name = enc(node.name || (type === "dir" ? "目录" : "文件"));
      var rel = enc(node.rel_path || "");
      var path = enc(node.path || "");
      if (type === "dir") {
        var openAttr = rawDirContainsSelected(node, selectedPath) ? " open" : "";
        return '<details class="raw-dir"' + openAttr + '><summary title="' + rel + '">' + name + '</summary><div class="raw-dir-child">' + rawRenderTreeNodes(node.children || [], selectedPath) + "</div></details>";
      }
      var active = String(node.path || "") === String(selectedPath || "");
      return '<button class="raw-file-btn' + (active ? " active" : "") + '" type="button" data-path="' + path + '" data-rel="' + rel + '"><span class="clip" title="' + path + '">' + name + '</span><span class="micro">' + enc(formatBytes(node.size)) + "</span></button>";
    }).join("");
  }
  function rawRenderTree(data) {
    data = data || {};
    settingsState.rawTree = data;
    settingsState.rawRoot = String(data.root || settingsState.rawRoot || "");
    if (qs("raw-tree")) qs("raw-tree").innerHTML = rawRenderTreeNodes(data.tree || [], rawActivePath());
    rawSetMeta({ root: data.root || settingsState.rawRoot || "-", name: "未选择文件", rel_path: "", path: "", size: null, mtime: null });
  }
  function rawFirstFile(nodes) {
    var list = Array.isArray(nodes) ? nodes : [];
    for (var i = 0; i < list.length; i++) {
      var item = list[i] || {};
      if (item.type === "file" && item.path) return String(item.path);
      var child = rawFirstFile(item.children || []);
      if (child) return child;
    }
    return "";
  }
  function rawRefreshButtons() {
    var unlocked = !!settingsState.rawUnlocked;
    var hasPath = !!settingsState.rawSelectedPath;
    var treeReady = !!settingsState.rawTree;
    ["btn-save-raw", "btn-delete-raw", "btn-load-raw"].forEach(function(id) {
      var el = qs(id);
      if (!el) return;
      if (id === "btn-load-raw") {
        el.disabled = !unlocked;
      } else {
        el.disabled = !unlocked || !hasPath || !treeReady;
      }
    });
  }
  async function rawLoadFile(path) {
    var filePath = String(path || settingsState.rawSelectedPath || "").trim();
    if (!filePath) throw new Error("请选择一个配置文件");
    const data = await getJson("/api/config/file?path=" + encodeURIComponent(filePath));
    settingsState.rawUnlocked = true;
    settingsState.rawLoaded = true;
    settingsState.rawSelectedPath = String(data.path || filePath);
    settingsState.rawSelectedRel = String(data.rel_path || "");
    rawRenderTree(settingsState.rawTree || data.tree || {});
    rawSetMeta(data);
    if (qs("raw-editor")) qs("raw-editor").value = String(data.text || "");
    rawSetLocked(false, "");
    rawRefreshButtons();
    setStatus("status-raw", "已读取: " + String(data.rel_path || data.path || "-"), false);
    return data;
  }
  async function rawLoadTree() {
    const data = await getJson("/api/config/tree");
    settingsState.rawUnlocked = true;
    settingsState.rawRoot = String(data.root || "");
    settingsState.rawTree = data;
    rawRenderTree(data);
    rawSetLocked(false, "");
    rawRefreshButtons();
    return data;
  }
  async function loadRaw() {
    try {
      const treeData = await rawLoadTree();
      var target = String(settingsState.rawSelectedPath || "");
      if (!target) {
        target = rawFirstFile(treeData.tree || []);
        settingsState.rawSelectedPath = target;
      }
      if (target) {
        await rawLoadFile(target);
      } else {
        settingsState.rawLoaded = true;
        rawSetMeta({ root: treeData.root || settingsState.rawRoot || "-", name: "未选择文件", rel_path: "-", path: "-", size: null, mtime: null });
        if (qs("raw-editor")) qs("raw-editor").value = "";
        rawRefreshButtons();
      }
    } catch (e) {
      var msg = e && e.message ? e.message : String(e);
      if (msg.indexOf("unlock required") >= 0 || msg.indexOf("raw config unlock required") >= 0) {
        settingsState.rawUnlocked = false;
        settingsState.rawLoaded = false;
        rawSetLocked(true, "需要先验证网页登录密码，才能查看和编辑配置文件。");
        rawRefreshButtons();
        openReauth("raw-unlock");
        setStatus("status-raw", msg, true);
        return;
      }
      throw e;
    }
  }
  async function saveRaw() {
    var selected = String(settingsState.rawSelectedPath || "").trim();
    if (!selected) throw new Error("请选择一个配置文件");
    const data = await postJson("/api/settings/raw/save", { path: selected, text: String(qs("raw-editor").value || "") });
    settingsState.rawTree = null;
    settingsState.rawLoaded = false;
    setStatus("status-raw", "保存成功: " + String(data.saved_to || "-") + "\n" + String(data.reload_msg || ""), false);
    showNotice("原始配置已保存", "ok", 3200);
    await loadRaw().catch(function() {
    });
  }
  async function deleteRawFile() {
    var selected = String(settingsState.rawSelectedPath || "").trim();
    if (!selected) throw new Error("请选择一个配置文件");
    if (!confirm("确认删除以下文件？\n" + selected)) return;
    const data = await postJson("/api/config/file/delete", { path: selected });
    settingsState.rawSelectedPath = "";
    settingsState.rawSelectedRel = "";
    settingsState.rawTree = null;
    setStatus("status-raw", "已删除: " + String(data.deleted_path || "-") + "\n" + String(data.backup_path || ""), false);
    showNotice("原始配置文件已删除", "ok", 2600);
    await loadRaw().catch(function() {
    });
  }
  function renderPasskeyRows(items) {
    var root = qs("passkey-list");
    if (!root) return;
    var arr = Array.isArray(items) ? items.slice() : [];
    if (!arr.length) {
      root.innerHTML = '<div class="empty-state">暂无通行密钥</div>';
      return;
    }
    root.innerHTML = arr.map(function(item, idx) {
      item = item || {};
      var id = String(item.id || "");
      var name = enc(item.name || "通行密钥 " + (idx + 1));
      var created = item.created_ts ? formatMtime(item.created_ts) : "-";
      var used = item.last_used_ts ? formatMtime(item.last_used_ts) : "未使用";
      return '<div class="passkey-row" data-id="' + enc(id) + '"><div class="passkey-meta"><div class="passkey-title">' + name + '</div><div class="passkey-sub">创建时间: ' + enc(created) + " | 上次使用: " + enc(used) + '</div><div class="passkey-badges"><span class="passkey-badge">签名计数 ' + enc(String(item.sign_count || 0)) + '</span><span class="passkey-badge">' + (item.enabled === false ? "已停用" : "已启用") + '</span></div></div><button class="btn ghost warn passkey-delete" type="button">删除</button></div>';
    }).join("");
  }
  async function createPasskeyWithCreds() {
    if (!window.PublicKeyCredential || !navigator.credentials || !navigator.credentials.create) {
      throw new Error("当前浏览器不支持通行密钥创建");
    }
    var user = String(qs("reauth-user").value || "").trim();
    var pass = String(qs("reauth-pass").value || "");
    if (!user || !pass) throw new Error("请输入网页登录账号和密码");
    var name = String(qs("cfg-passkey-name") && qs("cfg-passkey-name").value || "").trim();
    const start = await postJson("/api/settings/passkey/start", { username: user, password: pass, name });
    if (!start.ok) throw new Error(start.error || "通行密钥创建失败");
    var pk = start.publicKey || {};
    var challenge = b64uToBytes(pk.challenge || start.challenge || start.challenge_token || "");
    var userId = b64uToBytes(pk.user && pk.user.id || "");
    var createOptions = {
      publicKey: {
        challenge,
        rp: pk.rp || { name: start.realm || "Light RID Scanner", id: start.rp_id || location.hostname },
        user: {
          id: userId,
          name: pk.user && pk.user.name || user,
          displayName: pk.user && pk.user.displayName || (name || user)
        },
        pubKeyCredParams: pk.pubKeyCredParams || [{ type: "public-key", alg: -7 }],
        timeout: pk.timeout || start.timeout_ms || 3e5,
        attestation: pk.attestation || "none",
        authenticatorSelection: pk.authenticatorSelection || { userVerification: "preferred", residentKey: "preferred" },
        excludeCredentials: (pk.excludeCredentials || []).map(function(item) {
          return { type: "public-key", id: b64uToBytes(item.id || "") };
        })
      }
    };
    var cred = await navigator.credentials.create(createOptions);
    if (!cred) throw new Error("未获取到通行密钥凭据");
    var response = cred.response || {};
    const finish = await postJson("/api/settings/passkey/finish", {
      challenge: start.challenge || start.challenge_token,
      id: cred.id || "",
      rawId: bytesToB64u(cred.rawId || new Uint8Array(0)),
      type: cred.type || "public-key",
      response: {
        clientDataJSON: bytesToB64u(response.clientDataJSON || new Uint8Array(0)),
        attestationObject: bytesToB64u(response.attestationObject || new Uint8Array(0)),
        authenticatorData: bytesToB64u(response.authenticatorData || new Uint8Array(0)),
        signature: bytesToB64u(response.signature || new Uint8Array(0)),
        userHandle: response.userHandle ? bytesToB64u(response.userHandle) : ""
      },
      name,
      username: user,
      next: "/"
    });
    renderPasskeyRows(finish.passkeys || []);
    showNotice("通行密钥已添加", "ok", 3200);
    if (qs("cfg-passkey-name")) qs("cfg-passkey-name").value = "";
    return finish;
  }
  async function deletePasskey(id) {
    const data = await postJson("/api/settings/passkey/delete", { id: String(id || "") });
    renderPasskeyRows(data.passkeys || []);
    showNotice("通行密钥已删除", "ok", 2600);
    return data;
  }
  function fmtSsoExpiry(item) {
    item = item || {};
    var expiresAt = Number(item.expires_at || 0);
    if (!isFinite(expiresAt) || expiresAt <= 0) return "无限时间";
    var left = Math.max(0, expiresAt - Date.now() / 1e3);
    if (left <= 0) return "已过期";
    if (left < 3600) return Math.max(1, Math.round(left / 60)) + " 分钟";
    if (left < 86400) return Math.round(left / 3600) + " 小时";
    return Math.round(left / 86400) + " 天";
  }
  function renderLoginLinks(items) {
    loginLinks = Array.isArray(items) ? items.slice() : [];
    var root = qs("login-link-list");
    if (!root) return;
    if (!loginLinks.length) {
      root.innerHTML = '<div class="empty-state">暂无 SSO 登录链接。</div>';
      return;
    }
    root.innerHTML = loginLinks.map(function(item, idx) {
      var name = enc(item.name || "SSO 链接 " + (idx + 1));
      var check2 = enc(item.check || "");
      var status = String(item.status || (item.active === false ? "expired" : "active"));
      var stateLabel = enc(item.status_label || (status === "active" ? "可用" : "不可用"));
      var expireLabel = enc(fmtSsoExpiry(item));
      var modeLabel = item.single_use ? '<span class="sso-link-badge">单次</span>' : '<span class="sso-link-badge">多次</span>';
      var bad = status === "active" ? "" : " bad";
      return '<div class="list-row sso-link-row" data-check="' + check2 + '"><div class="sso-link-meta"><div class="sso-link-title"><span>' + name + '</span><span class="sso-link-badge' + bad + '">' + stateLabel + '</span><span class="sso-link-badge">' + expireLabel + "</span>" + modeLabel + '</div><div class="micro">使用此链接可一键登录系统</div></div><button class="btn ghost warn login-link-row-delete" type="button">删除</button></div>';
    }).join("");
  }
  async function deleteLoginLink(check2) {
    const r = await fetch(apiUrl("/api/settings/login-link/delete"), {
      method: "POST",
      headers: pageHeaders({ "Content-Type": "application/json" }),
      body: JSON.stringify({ check: String(check2 || "") })
    });
    const d = await r.json().catch(() => ({}));
    if (authExpired(r, d)) {
      redirectLogin();
      throw new Error("login required");
    }
    if (!r.ok || d.ok === false) throw new Error(d.error || "HTTP " + r.status);
    renderLoginLinks(d.links || []);
    qs("login-link-state").textContent = "已删除校验码，对应 SSO 链接立即失效。";
    return d;
  }
  function collectLoginLinkOptions() {
    var mode = String(qs("login-link-expire-mode") && qs("login-link-expire-mode").value || "86400");
    var body = {
      name: String(qs("login-link-name").value || "").trim(),
      next: "/",
      single_use: !!(qs("login-link-single-use") && qs("login-link-single-use").checked)
    };
    if (mode === "never") {
      body.expires = "never";
    } else if (mode === "custom") {
      body.ttl_min = Math.max(1, Number(qs("login-link-ttl-min") && qs("login-link-ttl-min").value || 1440));
    } else {
      body.ttl_sec = Math.max(60, Number(mode || 86400));
    }
    return body;
  }
  function setLoginLinkExpiryUi() {
    var mode = String(qs("login-link-expire-mode") && qs("login-link-expire-mode").value || "86400");
    var custom = qs("login-link-ttl-min");
    var field = qs("login-link-custom-field");
    if (custom) custom.disabled = mode !== "custom";
    if (field) field.classList.toggle("hidden", mode !== "custom");
  }
  async function createLoginLinkWithCreds() {
    var user = String(qs("reauth-user").value || "").trim();
    var pass = String(qs("reauth-pass").value || "");
    if (!user || !pass) {
      setStatus("reauth-status", "账号和密码不完整。", true);
      return null;
    }
    var reqBody = collectLoginLinkOptions();
    reqBody.username = user;
    reqBody.password = pass;
    const r = await fetch(apiUrl("/api/settings/login-link/create"), {
      method: "POST",
      headers: pageHeaders({ "Content-Type": "application/json" }),
      body: JSON.stringify(reqBody)
    });
    const d = await r.json().catch(() => ({}));
    if (authExpired(r, d)) {
      redirectLogin();
      throw new Error("login required");
    }
    if (!r.ok || d.ok === false) {
      throw new Error(d.error || "HTTP " + r.status);
    }
    var url = String(d.url || d.path || "");
    var expireText = d.expires_at ? "有效期至 " + fmtMetricTime(d.expires_at) : "无限时间";
    qs("login-link-state").textContent = "校验码 " + String(d.check || "-").slice(0, 10) + "... 已加入列表；" + expireText + (d.single_use ? "；单次登录。" : "。");
    renderLoginLinks(d.links || []);
    showOneTimeSecret("SSO 登录链接", url, "这个链接只在本次弹窗显示，关闭后只能删除记录再重新生成。");
    return d;
  }
  function fillIfaceOptions(items, selected) {
    const sel = qs("cfg-iface");
    if (!sel) return;
    const opts = ['<option value="">未绑定</option>'];
    (Array.isArray(items) ? items : []).forEach(function(it) {
      const name = String(it.name || "");
      if (!name) return;
      var kind = it.is_wireless ? (it.mode ? String(it.mode) : "wireless") + " " + (it.supports_5g ? "5G" : "2.4G") : "LAN";
      if (it.admin_up === false) kind += " disabled";
      var model = it.model ? " " + String(it.model) : "";
      opts.push('<option value="' + enc(name) + '">' + enc(name) + " [" + enc(kind + model) + "]</option>");
    });
    sel.innerHTML = opts.join("");
    sel.value = selected || "";
  }
  function networkRoleOptions(selected) {
    var roles = settingsState.networkBindings && Array.isArray(settingsState.networkBindings.roles) ? settingsState.networkBindings.roles : [
      { key: "none", label: "None" },
      { key: "scan", label: "扫描" },
      { key: "web", label: "网页服务" },
      { key: "ap_web", label: "AP热点网页服务" },
      { key: "disabled", label: "禁用" },
      { key: "idle", label: "闲置" }
    ];
    return roles.map(function(role) {
      var key = String(role.key || "none");
      return '<option value="' + enc(key) + '" ' + (key === selected ? "selected" : "") + ">" + enc(role.label || key) + "</option>";
    }).join("");
  }
  function networkBindingRoleMap() {
    var out = {};
    var nb = settingsState.networkBindings || {};
    (Array.isArray(nb.items) ? nb.items : []).forEach(function(item) {
      var iface = String(item && item.iface || "");
      if (iface) out[iface] = String(item.role || "none");
    });
    var selected = v("cfg-iface") || "";
    if (selected && !out[selected]) out[selected] = "scan";
    return out;
  }
  function ensureNetworkUplinkControl() {
    if (qs("net-ap-uplink")) return qs("net-ap-uplink");
    var http = qs("net-ap-http");
    if (!http || !http.parentNode || !http.parentNode.parentNode) return null;
    var field = document.createElement("div");
    field.className = "field";
    field.innerHTML = '<label>桥接出口</label><select id="net-ap-uplink"></select><div class="micro">选择可访问 Internet 的网卡，热点客户端将通过该网卡出网。</div>';
    http.parentNode.parentNode.appendChild(field);
    return qs("net-ap-uplink");
  }
  function fillNetworkUplinkOptions(ap) {
    var sel = ensureNetworkUplinkControl();
    if (!sel) return;
    var current = String(ap && ap.uplink_iface || "");
    var opts = ['<option value="">不共享 Internet</option>'];
    (Array.isArray(settingsState.interfaceItems) ? settingsState.interfaceItems : []).forEach(function(it) {
      var name = String(it.name || "");
      if (!name) return;
      var kind = it.is_wireless ? "无线" : "有线";
      var ip = Array.isArray(it.ipv4) && it.ipv4.length ? " | " + it.ipv4.join(",") : "";
      opts.push('<option value="' + enc(name) + '">' + enc(name + " [" + kind + ip + "]") + "</option>");
    });
    sel.innerHTML = opts.join("");
    sel.value = current || "";
    sel.onchange = updateVisualDraftState;
  }
  function collectNetworkBindings() {
    var ap = settingsState.networkBindings && settingsState.networkBindings.ap ? Object.assign({}, settingsState.networkBindings.ap) : {};
    if (qs("net-ap-ssid")) ap.ssid = v("net-ap-ssid") || "LightRID-HotSpot";
    if (qs("net-ap-password")) ap.password = v("net-ap-password");
    if (qs("net-ap-channel")) ap.channel = n("net-ap-channel") || 6;
    if (qs("net-ap-uplink")) {
      ap.uplink_iface = v("net-ap-uplink");
      ap.internet_enabled = !!ap.uplink_iface;
    }
    ap.address = ap.address || "172.16.0.1";
    ap.cidr = ap.cidr || "172.16.0.1/24";
    ap.dhcp_start = ap.dhcp_start || "172.16.0.20";
    ap.dhcp_end = ap.dhcp_end || "172.16.0.240";
    ap.http_port = ap.http_port || 80;
    var rows = qsa(".network-bind-row");
    var items = rows.map(function(row) {
      var iface = row.getAttribute("data-iface") || "";
      var roleSel = row.querySelector(".network-bind-role");
      return { iface, role: String(roleSel && roleSel.value || "none") };
    }).filter(function(item) {
      return !!item.iface;
    });
    if (!items.length && settingsState.networkBindings && Array.isArray(settingsState.networkBindings.items)) {
      items = settingsState.networkBindings.items.map(function(item) {
        return { iface: String(item.iface || ""), role: String(item.role || "none") };
      }).filter(function(item) {
        return !!item.iface;
      });
    }
    var selectedIface = v("cfg-iface") || "";
    if (selectedIface) {
      var foundSelected = false;
      items.forEach(function(item) {
        if (item.role === "scan" && item.iface !== selectedIface) item.role = "none";
        if (item.iface === selectedIface) {
          item.role = "scan";
          foundSelected = true;
        }
      });
      if (!foundSelected) items.push({ iface: selectedIface, role: "scan" });
    }
    return { items, ap };
  }
  function renderNetworkBindings() {
    var list = qs("network-bind-list");
    if (!list) return;
    var interfaces = Array.isArray(settingsState.interfaceItems) ? settingsState.interfaceItems : [];
    var roleMap = networkBindingRoleMap();
    var selected = v("cfg-iface") || "";
    if (!interfaces.length) {
      list.innerHTML = '<div class="empty-state">未检测到网卡</div>';
    } else {
      list.innerHTML = interfaces.map(function(it) {
        var name = String(it.name || "");
        var role = roleMap[name] || (name === selected ? "scan" : String(it.detected_role || "none"));
        var meta = [];
        if (it.model) meta.push("型号 " + String(it.model));
        if (it.driver) meta.push("驱动 " + String(it.driver));
        meta.push(it.is_wireless ? "无线 " + String(it.mode || "") : "有线");
        if (it.admin_up === false) meta.push("已禁用");
        if (it.state) meta.push("状态 " + String(it.state));
        if (Array.isArray(it.ipv4) && it.ipv4.length) meta.push(it.ipv4.join(", "));
        if (it.mac) meta.push(String(it.mac));
        return '<div class="list-row network-bind-row" data-iface="' + enc(name) + '"><div class="model-map-row" style="grid-template-columns:minmax(120px,.35fr) minmax(0,1fr) minmax(180px,.35fr)"><input value="' + enc(name) + '" disabled><input value="' + enc(meta.join(" | ")) + '" disabled><select class="network-bind-role">' + networkRoleOptions(role) + "</select></div></div>";
      }).join("");
    }
    var ap = settingsState.networkBindings && settingsState.networkBindings.ap || {};
    if (qs("net-ap-ssid")) qs("net-ap-ssid").value = String(ap.ssid || "LightRID-HotSpot");
    if (qs("net-ap-password")) qs("net-ap-password").value = String(ap.password || "");
    if (qs("net-ap-channel")) qs("net-ap-channel").value = String(ap.channel || 6);
    if (qs("net-ap-http")) qs("net-ap-http").value = String(ap.address || "172.16.0.1") + ":" + String(ap.http_port || 80);
    fillNetworkUplinkOptions(ap);
  }
  async function refreshNetworkBindings() {
    const data = await getJson("/api/network-bindings/status");
    settingsState.interfaceItems = Array.isArray(data.interfaces) ? data.interfaces : [];
    settingsState.networkBindings = data.bindings || settingsState.networkBindings || { items: [], ap: {} };
    fillIfaceOptions(settingsState.interfaceItems, data.selected_iface || v("cfg-iface"));
    renderNetworkBindings();
    setStatus("status-network-bind", "已扫描 " + String(settingsState.interfaceItems.length) + " 张网卡。", false);
    return data;
  }
  function saveNetworkBindingsToDraft() {
    var nb = collectNetworkBindings();
    var scan = (nb.items || []).filter(function(item) {
      return item.role === "scan";
    });
    if (scan.length > 1) {
      setStatus("status-network-bind", "只能设置一张网卡为扫描。", true);
      return;
    }
    settingsState.networkBindings = Object.assign({}, settingsState.networkBindings || {}, nb);
    if (scan.length && qs("cfg-iface")) qs("cfg-iface").value = scan[0].iface;
    updateVisualDraftState();
    setStatus("status-network-bind", "网卡绑定已写入当前设置草稿，保存设置后生效。", false);
  }
  async function applyNetworkBindings() {
    if (settingsState.visualDirty) {
      throw new Error("请先保存当前设置，再应用网卡绑定到系统。");
    }
    if (!confirm("将按已保存配置调整网卡状态、AP 地址、hostapd 和内置 DHCP。继续？")) return;
    const body = await privilegedBody({ confirm: true }, "应用网卡绑定需要 root 权限；sudo 密码只用于本次请求，不会保存。");
    const data = await postJson("/api/network-bindings/apply", body);
    var lines = [];
    (Array.isArray(data.steps) ? data.steps : []).forEach(function(step) {
      lines.push((step.ok ? "OK " : "FAIL ") + String(step.label || "") + (step.output ? " | " + String(step.output) : ""));
    });
    setStatus("status-network-bind", lines.join("\n") || "已应用网卡绑定。", !data.ok);
    showNotice(data.ok ? "网卡绑定已应用。" : "部分网卡绑定步骤失败。", data.ok ? "ok" : "warn", 4200);
  }
  function renderHookRows(items) {
    var root = qs("wecom-list");
    var arr = Array.isArray(items) ? items.slice() : [];
    if (!arr.length) arr = [{ index: "", name: "默认通道", enabled: true, key_masked: "" }];
    root.innerHTML = arr.map(function(item, idx) {
      var index = item.index == null ? "" : String(item.index);
      var name = enc(item.name || "通道 " + (idx + 1));
      var mask = enc(item.key_masked || "");
      return '<div class="list-row hook-row" data-index="' + enc(index) + '"><div class="hook-layout"><div class="field"><label>通道名称</label><input class="hook-name" type="text" value="' + name + '"></div><div class="field"><label>Key</label><input class="hook-key" type="password" value="" placeholder="' + (mask ? "留空即不修改" : "新的 Key") + '"></div><div class="field"><label>启用</label><input class="hook-enabled" type="checkbox" ' + (item.enabled ? "checked" : "") + '></div><div class="field"><label>&nbsp;</label><button class="btn ghost row-remove" type="button">移除</button></div></div></div>';
    }).join("");
  }
  function renderZoneRows(items) {
    var root = qs("zone-list");
    var arr = Array.isArray(items) ? items.slice() : [];
    if (!arr.length) {
      root.innerHTML = '<div class="empty-state">暂无报警区域</div>';
      return;
    }
    root.innerHTML = arr.map(function(item, idx) {
      return '<div class="list-row zone-row"><div class="zone-layout"><div class="field"><label>区域名称</label><input class="zone-name" type="text" value="' + enc(item.name || "报警区域 " + (idx + 1)) + '"></div><div class="field"><label>启用</label><input class="zone-enabled" type="checkbox" ' + (item.enabled ? "checked" : "") + '></div><div class="field"><label>A 点纬度</label><input class="zone-lat1" type="number" step="0.000001" value="' + (item.lat1 == null ? "" : enc(item.lat1)) + '"></div><div class="field"><label>A 点经度</label><input class="zone-lon1" type="number" step="0.000001" value="' + (item.lon1 == null ? "" : enc(item.lon1)) + '"></div><div class="field"><label>B 点纬度</label><input class="zone-lat2" type="number" step="0.000001" value="' + (item.lat2 == null ? "" : enc(item.lat2)) + '"></div><div class="field"><label>B 点经度</label><input class="zone-lon2" type="number" step="0.000001" value="' + (item.lon2 == null ? "" : enc(item.lon2)) + '"></div><div class="field"><label>&nbsp;</label><button class="btn ghost row-remove" type="button">移除</button></div></div></div>';
    }).join("");
  }
  function collectHookRows() {
    return qsa(".hook-row").map(function(row) {
      var keyInput = row.querySelector(".hook-key");
      var idx = row.getAttribute("data-index") || "";
      var rawKey = String(keyInput && keyInput.value || "").trim();
      if (!rawKey && idx !== "") rawKey = "__KEEP__";
      if (!rawKey && idx === "") return null;
      return {
        index: idx === "" ? null : Number(idx),
        name: String((row.querySelector(".hook-name") || {}).value || "").trim() || "默认通道",
        enabled: !!(row.querySelector(".hook-enabled") || {}).checked,
        key: rawKey
      };
    }).filter(function(x) {
      return !!x;
    });
  }
  function collectZoneRows() {
    return qsa(".zone-row").map(function(row, idx) {
      function rowVal(sel) {
        return String((row.querySelector(sel) || {}).value || "").trim();
      }
      function rowNum(sel) {
        var s = rowVal(sel);
        if (!s) return null;
        var f = Number(s);
        return isFinite(f) ? f : null;
      }
      var name = rowVal(".zone-name") || "报警区域 " + (idx + 1);
      var zone = {
        name,
        enabled: !!(row.querySelector(".zone-enabled") || {}).checked,
        lat1: rowNum(".zone-lat1"),
        lon1: rowNum(".zone-lon1"),
        lat2: rowNum(".zone-lat2"),
        lon2: rowNum(".zone-lon2")
      };
      if (zone.lat1 == null && zone.lon1 == null && zone.lat2 == null && zone.lon2 == null && !zone.enabled) {
        return null;
      }
      return zone;
    }).filter(function(x) {
      return !!x;
    });
  }
  function fmtApiTokenExpiry(item) {
    return fmtSsoExpiry(item || {});
  }
  function renderApiTokenRows(items) {
    var root = qs("api-token-list");
    if (!root) return;
    apiTokenRows = Array.isArray(items) ? items.slice() : [];
    if (!apiTokenRows.length) {
      root.innerHTML = '<div class="empty-state">暂无 API Token。添加后才能启用外部 API。</div>';
      return;
    }
    root.innerHTML = apiTokenRows.map(function(item, idx) {
      item = item || {};
      var id = String(item.id || "");
      var name = enc(item.name || "API Token " + (idx + 1));
      var status = String(item.status || (item.active === false ? "expired" : "active"));
      var stateLabel = enc(item.status_label || (status === "active" ? "可用" : "不可用"));
      var bad = status === "active" || status === "new" ? "" : " bad";
      return '<div class="api-token-row" data-id="' + enc(id) + '" data-status="' + enc(status) + '" data-status-label="' + stateLabel + '"><div class="api-token-head"><div class="api-token-name" title="' + name + '">' + name + '</div><div class="api-token-badges"><span class="api-token-badge' + bad + '">' + stateLabel + '</span><span class="api-token-badge">' + enc(fmtApiTokenExpiry(item)) + '</span><span class="api-token-badge">' + (item.single_use ? "单次" : "多次") + '</span></div></div><div class="api-token-grid"><div class="micro">Token 只会在创建成功时显示一次，之后不能再查看、复制或修改。</div><button class="btn ghost warn api-token-row-remove" type="button">删除</button></div></div>';
    }).join("");
  }
  function collectApiTokenCreateOptions() {
    var mode = String(qs("api-token-new-expire-mode") && qs("api-token-new-expire-mode").value || "86400");
    var body = {
      name: String(qs("api-token-new-name") && qs("api-token-new-name").value || "").trim(),
      single_use: !!(qs("api-token-new-single-use") && qs("api-token-new-single-use").checked)
    };
    if (mode === "never") body.expires = "never";
    else if (mode === "custom") body.ttl_min = Math.max(1, Number(qs("api-token-new-ttl-min") && qs("api-token-new-ttl-min").value || 1440));
    else body.ttl_sec = Math.max(60, Number(mode || 86400));
    return body;
  }
  function setApiTokenCreateExpiryUi() {
    var mode = String(qs("api-token-new-expire-mode") && qs("api-token-new-expire-mode").value || "86400");
    var custom = qs("api-token-new-ttl-min");
    var field = qs("api-token-custom-field");
    if (custom) custom.disabled = mode !== "custom";
    if (field) field.classList.toggle("hidden", mode !== "custom");
  }
  function updateApiWhitelistUi(effective) {
    var block = qs("api-whitelist-block");
    var enabled = !!effective;
    if (block) block.classList.toggle("disabled-block", !enabled);
    ["cfg-api-whitelist-enabled", "cfg-api-whitelist-mode", "cfg-api-whitelist"].forEach(function(id) {
      var el = qs(id);
      if (el) el.disabled = !enabled;
    });
  }
  async function createApiTokenWithCreds() {
    var user = String(qs("reauth-user").value || "").trim();
    var pass = String(qs("reauth-pass").value || "");
    if (!user || !pass) {
      setStatus("reauth-status", "账号和密码不完整。", true);
      return null;
    }
    var reqBody = collectApiTokenCreateOptions();
    reqBody.username = user;
    reqBody.password = pass;
    const r = await fetch(apiUrl("/api/settings/api-token/create"), {
      method: "POST",
      headers: pageHeaders({ "Content-Type": "application/json" }),
      body: JSON.stringify(reqBody)
    });
    const d = await r.json().catch(() => ({}));
    if (authExpired(r, d)) {
      redirectLogin();
      throw new Error("login required");
    }
    if (!r.ok || d.ok === false) throw new Error(d.error || "HTTP " + r.status);
    renderApiTokenRows(d.tokens || []);
    updateApiWhitelistUi(true);
    showOneTimeSecret("API Token", String(d.token || ""), "这个 Token 只在本次弹窗显示，关闭后不能再次查看或复制。");
    if (qs("api-token-new-name")) qs("api-token-new-name").value = "";
    return d;
  }
  async function handleApiTokenListClick(ev) {
    var row = ev.target && ev.target.closest ? ev.target.closest(".api-token-row") : null;
    if (!row) return;
    try {
      if (ev.target.closest(".api-token-row-remove")) {
        var id = String(row.getAttribute("data-id") || "");
        if (!id) return;
        const d = await postJson("/api/settings/api-token/delete", { id });
        renderApiTokenRows(d.tokens || []);
        updateApiWhitelistUi(Array.isArray(d.tokens) && d.tokens.length > 0);
        showNotice("API Token 已删除。", "ok", 2200);
        return;
      }
    } catch (e) {
      showNotice(e.message || e, "warn", 3600);
    }
  }
  function handleApiTokenListChange(_ev) {
  }
  function attachRowRemove(rootId, onEmptyFactory) {
    var root = qs(rootId);
    if (!root) return;
    root.addEventListener("click", function(ev) {
      var btn = ev.target && ev.target.closest ? ev.target.closest(".row-remove") : null;
      if (!btn) return;
      var row = btn.closest(".list-row");
      if (row && row.parentNode) row.parentNode.removeChild(row);
      if (!root.children.length && typeof onEmptyFactory === "function") onEmptyFactory();
      updateVisualDraftState();
    });
  }
  async function useBrowserLocation() {
    if (!navigator.geolocation) {
      setStatus("status-visual", "当前浏览器不支持地理定位。", true);
      return;
    }
    if (!window.isSecureContext && !isLocalHostName(location.hostname || "")) {
      setStatus("status-visual", "当前页面不是安全上下文，浏览器可能拒绝定位；HTTPS 或手动填写更稳定。", true);
    }
    navigator.geolocation.getCurrentPosition(function(pos) {
      qs("cfg-base-lat").value = String(pos.coords.latitude || "");
      qs("cfg-base-lon").value = String(pos.coords.longitude || "");
      updateVisualDraftState();
      setStatus("status-visual", "已读取浏览器位置，等待测试或保存。", false);
    }, function(err) {
      setStatus("status-visual", "定位失败: " + (err && err.message ? err.message : err), true);
    }, { enableHighAccuracy: true, timeout: 12e3, maximumAge: 0 });
  }
  async function loadVisual() {
    const data = await getJson("/api/settings/view");
    const s = data.visual || {};
    const b = s.basic || {}, w = s.web || {}, nt = s.notify || {}, api = s.api || {}, auth = s.auth || {}, mu = s.model_update || {}, au = s.app_update || {}, mc = s.metrics || {};
    settingsState.interfaceItems = Array.isArray(data.interfaces) ? data.interfaces : [];
    settingsState.networkBindings = s.network_bindings || { items: [], ap: {} };
    fillIfaceOptions(settingsState.interfaceItems, b.iface || "");
    settingsState.visualLoaded = true;
    settingsState.channelUseDefault = !b.channel_custom;
    qs("cfg-channel").value = String(b.channel_effective == null ? 6 : b.channel_effective);
    setChannelUi(false);
    qs("cfg-time").value = String(b.time ?? "");
    qs("cfg-min-gap").value = String(b.min_gap ?? "");
    qs("cfg-lost-timeout").value = String(b.lost_timeout ?? 15);
    qs("cfg-rssi-delta").value = String(b.rssi_delta ?? "");
    qs("cfg-model-map").value = String(b.model_map || "");
    qs("cfg-model-update-enabled").checked = mu.enabled !== false;
    qs("cfg-app-update-enabled").checked = au.enabled !== false;
    qs("cfg-model-update-url").value = String(mu.url || "");
    renderAppUpdateState(au && au.state || {});
    var must = mu.state || {};
    qs("model-update-state").textContent = "已加载 " + String(must.loaded_count || 0) + " 条 | 上次成功 " + (must.last_success_ts ? fmtMetricTime(must.last_success_ts) : "尚未成功") + (must.last_error ? " | 最近错误: " + String(must.last_error) : "");
    qs("cfg-history-file").value = String(b.history_file || "");
    qs("cfg-heal").checked = !!b.auto_self_heal;
    qs("cfg-rssi-change").checked = !!b.change_on_rssi;
    qs("cfg-payload-change").checked = !!b.change_on_payload;
    qs("cfg-debug").checked = !!b.debug;
    qs("cfg-dwell2g").value = String(b.dwell_2g ?? "");
    qs("cfg-dwell5g").value = String(b.dwell_5g ?? "");
    qs("cfg-settle").value = String(b.settle ?? "");
    qs("cfg-hit-dwell").value = String(b.dwell_on_hit ?? "");
    qs("cfg-hit-cap").value = String(b.hit_cap ?? "");
    qs("cfg-hop").checked = !!b.hop;
    qs("cfg-hop5g").checked = !!b.hop_5g;
    qs("cfg-fast").checked = !!b.scan_wifi_fast;
    qs("cfg-base-name").value = String(w.base_name || "");
    qs("cfg-dji-url").value = String(w.dji_lookup_url || "");
    qs("cfg-base-lat").value = w.base_lat == null ? "" : String(w.base_lat);
    qs("cfg-base-lon").value = w.base_lon == null ? "" : String(w.base_lon);
    qs("cfg-base-zoom").value = String(w.base_zoom ?? "");
    qs("cfg-heading-ref").value = String(w.heading_ref_deg ?? "");
    qs("cfg-map-idle").value = String(w.map_auto_center_idle_sec ?? "");
    qs("cfg-web-access-enabled").checked = !!w.access_list_enabled;
    qs("cfg-web-access-mode").value = String(w.access_list_mode || "allow");
    qs("cfg-web-access-list").value = Array.isArray(w.access_list) ? w.access_list.join("\n") : "";
    renderZoneRows(Array.isArray(w.alarm_zones) ? w.alarm_zones : []);
    renderHostStats(data.host || {}, b);
    renderEulaState(data.eula || {});
    loadSystemServiceStatus().catch(function(e) {
      setStatus("status-system-service", e.message || e, true);
    });
    loadRuntimePanel().catch(function() {
    });
    loadMetrics().catch(function() {
    });
    qs("cfg-notify-enabled").checked = !!nt.enabled;
    qs("cfg-notify-reonline").checked = !!nt.notify_reonline;
    qs("cfg-reonline").value = String(nt.reonline_cooldown_sec ?? "");
    qs("cfg-send-timeout").value = String(nt.send_timeout_sec ?? "");
    renderHookRows(Array.isArray(nt.wecom_webhooks) ? nt.wecom_webhooks : []);
    qs("cfg-api-enabled").checked = !!api.enabled;
    renderApiTokenRows(Array.isArray(api.tokens) ? api.tokens : []);
    qs("cfg-api-whitelist-enabled").checked = !!api.whitelist_enabled;
    qs("cfg-api-whitelist-mode").value = String(api.whitelist_mode || "allow");
    qs("cfg-api-whitelist").value = Array.isArray(api.whitelist) ? api.whitelist.join("\n") : "";
    updateApiWhitelistUi(!!api.whitelist_effective);
    settingsState.authConfigured = !!auth.configured;
    qs("cfg-auth-enabled").checked = !!auth.enabled;
    qs("cfg-auth-method-password").checked = false;
    qs("cfg-auth-method-passkey").checked = false;
    (Array.isArray(auth.login_methods) && auth.login_methods.length ? auth.login_methods : ["password", "passkey"]).forEach(function(method) {
      var id = method === "password" ? "cfg-auth-method-password" : method === "passkey" ? "cfg-auth-method-passkey" : "";
      if (id && qs(id)) qs(id).checked = true;
    });
    qs("cfg-auth-user").value = "";
    qs("cfg-auth-user").placeholder = "留空即不修改";
    qs("cfg-auth-pass").value = "";
    qs("cfg-auth-pass").placeholder = "留空即不修改";
    qs("cfg-auth-realm").value = String(auth.realm || "Light RID Scanner");
    qs("cfg-auth-ttl").value = String(auth.session_ttl_min || 30);
    if (qs("login-link-name")) qs("login-link-name").value = "";
    if (qs("login-link-expire-mode")) qs("login-link-expire-mode").value = "86400";
    if (qs("login-link-ttl-min")) qs("login-link-ttl-min").value = "1440";
    if (qs("login-link-single-use")) qs("login-link-single-use").checked = false;
    if (qs("api-token-new-expire-mode")) qs("api-token-new-expire-mode").value = "86400";
    if (qs("api-token-new-ttl-min")) qs("api-token-new-ttl-min").value = "1440";
    if (qs("api-token-new-single-use")) qs("api-token-new-single-use").checked = false;
    setLoginLinkExpiryUi();
    setApiTokenCreateExpiryUi();
    qs("btn-api-token-add").disabled = !(auth.enabled && auth.configured);
    renderLoginLinks(auth.sso_links || []);
    renderPasskeyRows(Array.isArray(auth.passkeys) ? auth.passkeys : []);
    if (qs("cfg-passkey-name")) qs("cfg-passkey-name").value = "";
    syncAuthMethodUi();
    if (qs("settings-config-path")) qs("settings-config-path").textContent = "设置文件: " + String(data.path || "-");
    if (qs("settings-scan-data-path")) qs("settings-scan-data-path").textContent = "扫描数据文件: " + String(b.history_file || "-");
    renderScanDataFileInfo(data.scan_data_file || null);
    var rawAccess = data.raw_access || {};
    settingsState.rawUnlocked = !rawAccess.required || !!rawAccess.unlocked;
    settingsState.rawRoot = String(rawAccess.root || settingsState.rawRoot || "");
    settingsState.rawSelectedPath = String(data.path || settingsState.rawSelectedPath || "");
    rawSetLocked(!settingsState.rawUnlocked, settingsState.rawUnlocked ? "" : "需要先验证网页登录密码，才能查看和编辑配置文件。");
    rawRefreshButtons();
    qs("cfg-metrics-enabled").checked = !!mc.enabled;
    qs("cfg-metrics-retention").value = String(mc.retention_days || 7);
    qs("cfg-metrics-temp-source").value = String(mc.temperature_source || "auto");
    var apiTokenCount = Array.isArray(api.tokens) ? api.tokens.length : 0;
    qs("secret-state").textContent = "通知通道 " + String((nt.wecom_webhooks || []).length || 0) + " | API Token " + String(apiTokenCount) + " 个 | 外部 API " + (api.enabled ? "开启" : "关闭") + " | 登录 " + (auth.enabled ? auth.configured ? "开启" : "未完成" : "关闭");
    resetVisualDraftState();
    if (data.path) setStatus("status-visual", "配置文件: " + data.path, false);
  }
  async function saveVisual(opts) {
    opts = opts && typeof opts === "object" ? opts : {};
    const payload = opts.checkboxOnly ? collectCheckboxOnlyVisualPayload() : collectVisualPayload();
    const data = await postJson("/api/settings/visual/save", payload);
    var msg = (opts.auto ? "勾选项已保存: " : "保存成功: ") + String(data.saved_to || "-");
    if (data.backup_path) msg += "\n备份: " + String(data.backup_path);
    if (data.reload_msg) msg += "\n" + String(data.reload_msg);
    setStatus("status-visual", msg, false);
    showNotice(opts.auto ? "勾选项已保存。" : "配置已保存并生效。", "ok", opts.auto ? 2200 : 3e3);
    if (opts.auto) {
      settingsState.visualInitial = cloneJson(payload);
      updateVisualDraftState();
    } else {
      await loadVisual();
    }
  }
  async function testVisual() {
    const payload = collectVisualPayload();
    const data = await postJson("/api/settings/visual/test", payload);
    var msg = "测试通过，运行配置已回滚。";
    if (data.reload_msg) msg += "\n" + String(data.reload_msg);
    setStatus("status-visual", msg, false);
    showNotice("测试通过，当前运行配置已回滚。", "ok", 3e3);
  }
  function bindShellActions() {
    on("btn-back", "click", function() {
      location.href = "/";
    });
    on("btn-logs", "click", function() {
      location.href = "/logs";
    });
    on("btn-logout", "click", function() {
      location.href = "/logout";
    });
    on("btn-theme", "click", function() {
      applyTheme(document.body.classList.contains("theme-light") ? "dark" : "light");
    });
    on("btn-open-hw", "click", function() {
      location.href = "/hardware-assistant";
    });
    on("btn-diagnostic-export", "click", async function() {
      var btn = qs("btn-diagnostic-export");
      try {
        if (btn) btn.disabled = true;
        await downloadQualityReport();
      } catch (e) {
        setStatus("status-visual", "质量分析包导出失败: " + (e.message || e), true);
        showNotice(e.message || e, "warn", 4200);
      } finally {
        if (btn) btn.disabled = false;
      }
    });
    on("btn-refresh-host", "click", function() {
      withSettingsPageLoading("Station 设置", "正在读取设置", function() {
        return guarded(loadVisual, "status-visual");
      });
    });
    on("btn-refresh-runtime", "click", function() {
      withSettingsPageLoading("运行数据", "正在读取运行状态", function() {
        return guarded(loadRuntimePanel, "status-runtime", "运行数据已刷新。", 1800, 3600);
      });
    });
    on("btn-reload-view", "click", function() {
      withSettingsPageLoading("Station 设置", "正在读取设置", function() {
        return guarded(loadVisual, "status-visual", "设置已重新读取。", 2200);
      });
    });
    qsa(".settings-jump [data-jump]").forEach(function(btn) {
      btn.addEventListener("click", function() {
        var target = qs(btn.getAttribute("data-jump") || "");
        if (target && target.scrollIntoView) target.scrollIntoView({ behavior: "smooth", block: "start" });
      });
    });
  }
  function bindModelEditorActions() {
    on("btn-model-map-open", "click", function() {
      qs("model-map-modal").classList.add("show");
      loadModelEditor().catch(function(e) {
        if (qs("model-map-editor-state")) qs("model-map-editor-state").textContent = "识别库读取失败: " + (e.message || e);
      });
    });
    on("btn-model-map-close", "click", function() {
      qs("model-map-modal").classList.remove("show");
    });
    on("model-map-modal", "click", function(ev) {
      if (ev.target === qs("model-map-modal")) qs("model-map-modal").classList.remove("show");
    });
    on("btn-model-update-now", "click", updateModelsNow);
    on("btn-app-update-check", "click", checkAppVersionNow);
    on("btn-app-update-start", "click", startAppUpdateNow);
    on("btn-model-map-add", "click", function() {
      addModelMapRow("", "");
    });
    on("btn-model-map-save", "click", saveModelEditor);
    on("model-map-search", "input", function() {
      syncModelRowsFromInputs();
      renderModelMapRows();
    });
    on("model-map-list", "input", function(ev) {
      var t = ev.target;
      if (t && t.classList && t.classList.contains("model-prefix")) {
        t.value = cleanModelPrefix(t.value);
      }
      syncModelRowsFromInputs();
    });
    on("model-map-list", "click", function(ev) {
      var btn = ev.target && ev.target.closest ? ev.target.closest(".model-row-delete") : null;
      if (!btn) return;
      var row = btn.closest(".model-map-row");
      var idx = row ? Number(row.getAttribute("data-index")) : -1;
      if (isFinite(idx) && idx >= 0) {
        syncModelRowsFromInputs();
        modelMapRows.splice(idx, 1);
        renderModelMapRows();
      }
    });
  }
  function bindMetricActions() {
    on("cfg-metrics-enabled", "change", function() {
      updateVisualDraftState();
      loadMetrics().catch(function(e) {
        if (qs("status-metrics")) qs("status-metrics").textContent = e.message || String(e);
      });
    });
    qsa(".metric-window").forEach(function(btn) {
      btn.addEventListener("click", function() {
        setMetricWindow(btn.getAttribute("data-window") || "12h");
      });
    });
    on("metrics-zoom", "input", function() {
      metricSetZoom(Number(qs("metrics-zoom").value || 1), 0.5);
    });
    qsa(".metric-spark").forEach(function(canvas) {
      metricBindCanvasEvents(canvas);
    });
  }
  function bindDataTransferActions() {
    on("btn-export-settings-file", "click", function() {
      withSettingsPageLoading("设置文件", "正在导出设置文件", function() {
        return guarded(exportSettingsFile, "status-data-transfer", "设置文件已导出。", 2200, 3600);
      });
    });
    on("btn-import-settings-file", "click", function() {
      pickFileInput("import-settings-file");
    });
    on("import-settings-file", "change", function(ev) {
      var file = ev && ev.target && ev.target.files && ev.target.files[0] ? ev.target.files[0] : null;
      if (!file) return;
      withSettingsPageLoading("设置文件", "正在导入设置文件", function() {
        return guarded(function() {
          return importSettingsFileFromFile(file);
        }, "status-data-transfer", "", 0, 4200);
      });
    });
    on("btn-export-scan-data", "click", function() {
      withSettingsPageLoading("扫描数据", "正在导出扫描数据", function() {
        return guarded(exportScanDataFile, "status-data-transfer", "扫描数据已导出。", 2200, 3600);
      });
    });
    on("btn-import-scan-data", "click", function() {
      pickFileInput("import-scan-data-file");
    });
    on("import-scan-data-file", "change", function(ev) {
      var file = ev && ev.target && ev.target.files && ev.target.files[0] ? ev.target.files[0] : null;
      if (!file) return;
      withSettingsPageLoading("扫描数据", "正在导入扫描数据", function() {
        return guarded(function() {
          return importScanDataFileFromFile(file);
        }, "status-data-transfer", "", 0, 4200);
      });
    });
    on("btn-reidentify-recent-history", "click", function() {
      withSettingsPageLoading("历史包识别", "正在识别所有飞机近100包", function() {
        return guarded(reidentifyRecentHistoryPackets, "status-data-transfer", "所有飞机近100个存储包已识别。", 2400, 5200);
      });
    });
  }
  function bindEulaActions() {
    on("btn-eula-view", "click", function() {
      location.href = "/eula?next=/settings";
    });
    on("btn-eula-revoke", "click", revokeEulaAcceptance);
  }
  function bindCaptureActions() {
    on("btn-network-bind-refresh", "click", function() {
      withSettingsPageLoading("网卡绑定", "正在扫描网卡", function() {
        return guarded(refreshNetworkBindings, "status-network-bind", "网卡列表已刷新。", 1800, 3600);
      });
    });
    on("btn-network-bind-save", "click", saveNetworkBindingsToDraft);
    on("btn-network-bind-apply", "click", function() {
      withSettingsPageLoading("网卡绑定", "正在应用网卡绑定", function() {
        return guarded(applyNetworkBindings, "status-network-bind", "网卡绑定已应用。", 2600, 5200);
      });
    });
    on("network-bind-module", "toggle", function() {
      var host = qs("network-bind-module");
      if (host && host.open) {
        withSettingsPageLoading("网卡绑定", "正在扫描网卡", refreshNetworkBindings).catch(function(e) {
          setStatus("status-network-bind", e.message || e, true);
        });
      }
    });
    on("network-bind-list", "change", updateVisualDraftState);
    on("net-ap-ssid", "input", updateVisualDraftState);
    on("net-ap-password", "input", updateVisualDraftState);
    on("net-ap-channel", "input", updateVisualDraftState);
    on("btn-channel-edit", "click", function() {
      setChannelUi(!settingsState.channelEditing);
    });
    on("btn-channel-reset", "click", function() {
      settingsState.channelUseDefault = true;
      qs("cfg-channel").value = "6";
      setChannelUi(false);
    });
    on("cfg-channel", "input", function() {
      var val = Number(qs("cfg-channel").value || "");
      settingsState.channelUseDefault = !(isFinite(val) && val !== 6);
      setChannelUi(settingsState.channelEditing);
    });
  }
  async function handleLoginLinkListClick(ev) {
    var row = ev.target && ev.target.closest ? ev.target.closest(".sso-link-row") : null;
    if (!row) return;
    var check2 = row.getAttribute("data-check") || "";
    try {
      if (ev.target.closest(".login-link-row-delete")) {
        await deleteLoginLink(check2);
        showNotice("SSO 校验码已删除。", "ok", 2400);
        return;
      }
    } catch (e) {
      showNotice(e.message || e, "warn", 3600);
    }
  }
  async function confirmReauthAction() {
    try {
      var action = reauthAction || "copy";
      if (action === "login-link") {
        await createLoginLinkWithCreds();
        setStatus("status-visual", "SSO 登录链接已生成，只会在弹窗里显示一次。", false);
        showNotice("SSO 登录链接已生成。", "ok", 2600);
      } else if (action === "api-token-create") {
        await createApiTokenWithCreds();
        setStatus("status-visual", "API Token 已生成，只会在弹窗里显示一次。", false);
        showNotice("API Token 已生成。", "ok", 2600);
      } else if (action === "raw-unlock") {
        var user = String(qs("reauth-user").value || "").trim();
        var pass = String(qs("reauth-pass").value || "");
        if (!user || !pass) throw new Error("请输入网页登录账号和密码");
        const data = await postJson("/api/settings/raw/unlock", { username: user, password: pass });
        if (!data.ok) throw new Error(data.error || "原始配置解锁失败");
        settingsState.rawUnlocked = true;
        rawSetLocked(false, "");
        rawRefreshButtons();
        showNotice("原始配置已解锁。", "ok", 2600);
        await loadRaw().catch(function() {
        });
      } else if (action === "passkey-create") {
        await createPasskeyWithCreds();
        if (qs("passkey-state")) qs("passkey-state").textContent = "通行密钥已添加，可直接用于网页登录。";
      } else {
        throw new Error("不支持的二次验证操作");
      }
      closeReauth();
    } catch (e) {
      setStatus("reauth-status", e.message || e, true);
      showNotice(e.message || e, "warn", 3600);
    }
  }
  function bindAccessActions() {
    on("btn-api-token-add", "click", function() {
      openReauth("api-token-create");
    });
    on("api-token-list", "click", handleApiTokenListClick);
    on("api-token-list", "change", handleApiTokenListChange);
    on("btn-login-link-create", "click", function() {
      openReauth("login-link");
    });
    on("btn-passkey-add", "click", function() {
      openReauth("passkey-create");
    });
    on("cfg-auth-enabled", "change", syncAuthMethodUi);
    ["cfg-auth-method-password", "cfg-auth-method-passkey"].forEach(function(id) {
      on(id, "change", function() {
        ensureAuthLoginMethodSelection(id, true);
        syncAuthMethodUi();
      });
    });
    on("login-link-expire-mode", "change", setLoginLinkExpiryUi);
    on("api-token-new-expire-mode", "change", setApiTokenCreateExpiryUi);
    on("login-link-list", "click", handleLoginLinkListClick);
    on("passkey-list", "click", function(ev) {
      var row = ev.target && ev.target.closest ? ev.target.closest(".passkey-row") : null;
      if (!row) return;
      var id = row.getAttribute("data-id") || "";
      var del = ev.target && ev.target.closest ? ev.target.closest(".passkey-delete") : null;
      if (!del) return;
      deletePasskey(id).catch(function(e) {
        showNotice(e.message || e, "warn", 3600);
      });
    });
    on("btn-one-time-copy", "click", function() {
      copyTextPlain(oneTimeSecretValue).then(function() {
        showNotice("已复制。", "ok", 1800);
      }).catch(function(e) {
        showNotice(e.message || e, "warn", 2600);
      });
    });
    on("btn-one-time-close", "click", closeOneTimeSecret);
    on("one-time-modal", "click", function(ev) {
      if (ev.target === qs("one-time-modal")) closeOneTimeSecret();
    });
    on("btn-reauth-cancel", "click", function() {
      closeReauth();
    });
    on("reauth-modal", "click", function(ev) {
      if (ev.target === qs("reauth-modal")) closeReauth();
    });
    document.addEventListener("keydown", function(ev) {
      if (ev.key === "Escape" && qs("reauth-modal").classList.contains("show")) closeReauth();
    });
    on("btn-reauth-confirm", "click", confirmReauthAction);
    on("btn-hook-add", "click", function() {
      var rows = collectHookRows();
      rows.push({ index: null, name: "新通道", enabled: true, key: "" });
      renderHookRows(rows);
      updateVisualDraftState();
    });
  }
  function bindSystemServiceActions() {
    on("btn-service-refresh", "click", function() {
      withSettingsPageLoading("systemd 服务", "正在读取服务状态", function() {
        return guarded(loadSystemServiceStatus, "status-system-service", "服务状态已刷新。", 1800, 3600);
      });
    });
    on("btn-service-register", "click", registerSystemdServiceFromSettings);
    on("btn-iw-install", "click", installIwFromSettings);
    on("btn-security-repair", "click", repairRuntimeSecurityFromSettings);
    on("btn-elevate-cancel", "click", function() {
      closeElevate(null);
    });
    on("btn-elevate-confirm", "click", function() {
      closeElevate(qs("elevate-pass") ? qs("elevate-pass").value : "");
    });
    on("elevate-pass", "keydown", function(ev) {
      if (ev.key === "Enter") {
        ev.preventDefault();
        closeElevate(qs("elevate-pass") ? qs("elevate-pass").value : "");
      }
    });
    on("elevate-modal", "click", function(ev) {
      if (ev.target === qs("elevate-modal")) closeElevate(null);
    });
  }
  function bindRawActions() {
    on("btn-load-raw", "click", function() {
      withSettingsPageLoading("原始配置", "正在读取原始配置", function() {
        return guarded(loadRaw, "status-raw", "原始配置已读取。", 2200);
      });
    });
    on("btn-save-raw", "click", function() {
      withSettingsPageLoading("原始配置", "正在保存原始配置", function() {
        return guarded(saveRaw, "status-raw", "原始配置已保存。", 2600);
      });
    });
    on("btn-delete-raw", "click", function() {
      withSettingsPageLoading("原始配置", "正在删除原始配置文件", function() {
        return guarded(deleteRawFile, "status-raw", "原始配置文件已删除。", 2600);
      });
    });
    on("btn-raw-unlock", "click", function() {
      openReauth("raw-unlock");
    });
    on("btn-raw-unlock-inline", "click", function() {
      openReauth("raw-unlock");
    });
    on("raw-tree", "click", function(ev) {
      var btn = ev.target && ev.target.closest ? ev.target.closest(".raw-file-btn") : null;
      if (!btn) return;
      var path = btn.getAttribute("data-path") || "";
      if (!path) return;
      settingsState.rawSelectedPath = path;
      settingsState.rawSelectedRel = btn.getAttribute("data-rel") || "";
      rawRefreshButtons();
      withSettingsPageLoading("原始配置", "正在切换配置文件", function() {
        return guarded(function() {
          return rawLoadFile(path);
        }, "status-raw", "已切换配置文件。", 1800);
      });
    });
  }
  function bindSaveActions() {
    on("btn-test-visual", "click", async function() {
      try {
        showSettingsPageLoading("当前配置", "正在测试当前配置");
        setVisualActionBusy(true);
        await testVisual();
      } catch (e) {
        setStatus("status-visual", e.message || e, true);
        showNotice(e.message || e, "warn", 3800);
      } finally {
        hideSettingsPageLoading();
        setVisualActionBusy(false);
      }
    });
    on("btn-save-visual", "click", async function() {
      try {
        showSettingsPageLoading("当前配置", "正在保存设置");
        setVisualActionBusy(true);
        await saveVisual();
      } catch (e) {
        setStatus("status-visual", e.message || e, true);
        showNotice(e.message || e, "warn", 3800);
      } finally {
        hideSettingsPageLoading();
        setVisualActionBusy(false);
      }
    });
    on("btn-save-visual-direct", "click", async function() {
      try {
        showSettingsPageLoading("当前配置", "正在保存设置");
        setVisualActionBusy(true);
        await saveVisual();
      } catch (e) {
        setStatus("status-visual", e.message || e, true);
        showNotice(e.message || e, "warn", 3800);
      } finally {
        hideSettingsPageLoading();
        setVisualActionBusy(false);
      }
    });
  }
  function bindMapAndZoneActions() {
    on("btn-zone-add", "click", function() {
      var rows = collectZoneRows();
      rows.push({ name: "报警区域 " + (rows.length + 1), enabled: false, lat1: null, lon1: null, lat2: null, lon2: null });
      renderZoneRows(rows);
      updateVisualDraftState();
    });
    on("btn-browser-loc", "click", useBrowserLocation);
    on("btn-clear-base-loc", "click", function() {
      qs("cfg-base-lat").value = "";
      qs("cfg-base-lon").value = "";
      updateVisualDraftState();
      setStatus("status-visual", "已清空基站坐标，等待测试或保存。", false);
    });
    attachRowRemove("zone-list", function() {
      renderZoneRows([]);
    });
  }
  function bindBrowserPreferenceActions() {
    ["pref-new-firmware-parser"].forEach(function(id) {
      on(id, "change", saveBrowserPrefs);
    });
  }
  function bindViewportActions() {
    window.addEventListener("resize", function() {
      syncSettingsViewport();
      drawMetricsChart();
    });
    if (window.visualViewport) {
      try {
        window.visualViewport.addEventListener("resize", syncSettingsViewport);
        window.visualViewport.addEventListener("scroll", syncSettingsViewport);
      } catch (_e) {
      }
    }
  }
  function initializeSettingsPage() {
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
    attachRowRemove("wecom-list", function() {
      renderHookRows([]);
    });
    applyTheme(loadTheme());
    applyTabs();
    bindVisualDraftTracking();
    syncSettingsViewport();
    loadBrowserPrefs();
    withSettingsPageLoading("Station 设置", "正在读取设置", async function() {
      await loadVisual();
      await refreshNetworkBindings().catch(function(e) {
        setStatus("status-network-bind", e.message || e, true);
      });
    }).catch(function(e) {
      setStatus("status-visual", e.message || e, true);
      showNotice(e.message || e, "warn", 3800);
    });
    window.setInterval(function() {
      loadRuntimePanel().catch(function() {
      });
    }, 2e3);
    window.setInterval(function() {
      loadMetrics().catch(function() {
      });
    }, 2e3);
  }
  initializeSettingsPage();
})();
