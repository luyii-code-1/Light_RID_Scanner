import { createApp, computed, h, reactive } from "vue";

function apiHeaders(extra) {
  const base = { "X-LightRID-Page": "1" };
  return Object.assign(base, extra || {});
}

async function getJson(path) {
  const response = await fetch(path, { cache: "no-store", headers: apiHeaders() });
  const data = await response.json().catch(() => ({}));
  if (response.status === 401) {
    location.href = "/";
    throw new Error("login required");
  }
  if (!response.ok || data.ok === false) {
    throw new Error(data.error || `HTTP ${response.status}`);
  }
  return data;
}

async function postJson(path, body) {
  const response = await fetch(path, {
    method: "POST",
    cache: "no-store",
    headers: apiHeaders({ "Content-Type": "application/json" }),
    body: JSON.stringify(body || {}),
  });
  const data = await response.json().catch(() => ({}));
  if (response.status === 401) {
    location.href = "/";
    throw new Error("login required");
  }
  if (!response.ok || data.ok === false) {
    throw new Error(data.error || `HTTP ${response.status}`);
  }
  return data;
}

function withLoading(target, title, fn) {
  if (typeof window.withViewerPageLoading === "function") {
    return window.withViewerPageLoading(target, title, fn);
  }
  return fn();
}

function deepClone(value) {
  return JSON.parse(JSON.stringify(value));
}

function sameJson(left, right) {
  try {
    return JSON.stringify(left) === JSON.stringify(right);
  } catch (_error) {
    return false;
  }
}

function numText(value, fallback = "") {
  return value == null || value === "" ? fallback : String(value);
}

function fmtPct(value) {
  const out = Number(value);
  return Number.isFinite(out) ? `${out.toFixed(1)}%` : "—";
}

function fmtSec(value) {
  const out = Number(value);
  if (!Number.isFinite(out) || out < 0) {
    return "—";
  }
  if (out < 90) {
    return `${Math.round(out)} 秒`;
  }
  if (out < 86400) {
    return `${Math.floor(out / 3600)} 小时 ${Math.floor((out % 3600) / 60)} 分钟`;
  }
  return `${Math.floor(out / 86400)} 天 ${Math.floor((out % 86400) / 3600)} 小时`;
}

function themeFromStorage() {
  try {
    const stored = localStorage.getItem("rid_ui_theme");
    if (stored === "dark" || stored === "light") {
      return stored;
    }
  } catch (_error) {
    // ignore
  }
  try {
    if (window.matchMedia && window.matchMedia("(prefers-color-scheme: light)").matches) {
      return "light";
    }
  } catch (_error) {
    // ignore
  }
  return "dark";
}

function applyTheme(theme) {
  const light = theme === "light";
  document.body.classList.toggle("theme-light", light);
  document.body.classList.toggle("theme-dark", !light);
  try {
    localStorage.setItem("rid_ui_theme", light ? "light" : "dark");
  } catch (_error) {
    // ignore
  }
}

const defaultDraft = {
  auth: {
    enabled: false,
    username: "admin",
    password: "",
    sso_enabled: false,
    sso_check: "",
    password_configured: false,
    sso_configured: false,
  },
  map: {
    base_name: "Node Center",
    base_lat: "",
    base_lon: "",
    base_zoom: 5,
    map_auto_center_idle_sec: 20,
    heading_ref_deg: 0,
  },
  aggregate: {
    cache_ttl_hours: 24,
  },
  notify: {
    enabled: false,
    node_status_enabled: true,
    wecom_key: "",
    wecom_configured: false,
  },
  host: {},
  eula: {},
};

const state = reactive({
  theme: themeFromStorage(),
  draft: deepClone(defaultDraft),
  initial: deepClone(defaultDraft),
  aggregateMeta: null,
  statuses: {
    settings: "-",
    notify: "-",
    eula: "-",
    aggregate: "-",
  },
});

function buildPayload(options = {}) {
  const checkboxOnly = !!options.checkboxOnly;
  const initial = state.initial || defaultDraft;
  return {
    auth: {
      enabled: !!state.draft.auth.enabled,
      username: checkboxOnly ? initial.auth.username : state.draft.auth.username,
      password: checkboxOnly ? "" : state.draft.auth.password,
      sso_enabled: !!state.draft.auth.sso_enabled,
      sso_check: checkboxOnly ? "" : state.draft.auth.sso_check,
    },
    map: {
      base_name: checkboxOnly ? initial.map.base_name : state.draft.map.base_name,
      base_lat: checkboxOnly ? initial.map.base_lat : state.draft.map.base_lat,
      base_lon: checkboxOnly ? initial.map.base_lon : state.draft.map.base_lon,
      base_zoom: checkboxOnly ? initial.map.base_zoom : state.draft.map.base_zoom,
      map_auto_center_idle_sec: checkboxOnly ? initial.map.map_auto_center_idle_sec : state.draft.map.map_auto_center_idle_sec,
      heading_ref_deg: checkboxOnly ? initial.map.heading_ref_deg : state.draft.map.heading_ref_deg,
    },
    aggregate: {
      cache_ttl_hours: checkboxOnly ? initial.aggregate.cache_ttl_hours : state.draft.aggregate.cache_ttl_hours,
    },
    notify: {
      enabled: !!state.draft.notify.enabled,
      node_status_enabled: !!state.draft.notify.node_status_enabled,
      wecom_key: checkboxOnly ? "" : state.draft.notify.wecom_key,
    },
  };
}

function applySettingsData(data, options = {}) {
  const auth = data.auth || {};
  const map = data.map || {};
  const aggregate = data.aggregate || {};
  const notify = data.notify || {};
  state.draft.auth.enabled = !!auth.enabled;
  state.draft.auth.username = auth.username || "admin";
  state.draft.auth.password = "";
  state.draft.auth.sso_enabled = !!auth.sso_enabled;
  state.draft.auth.sso_check = "";
  state.draft.auth.password_configured = !!auth.password_configured;
  state.draft.auth.sso_configured = !!auth.sso_configured;
  state.draft.map.base_name = map.base_name || "Node Center";
  state.draft.map.base_lat = numText(map.base_lat);
  state.draft.map.base_lon = numText(map.base_lon);
  state.draft.map.base_zoom = numText(map.base_zoom || 5, "5");
  state.draft.map.map_auto_center_idle_sec = numText(map.map_auto_center_idle_sec || 20, "20");
  state.draft.map.heading_ref_deg = numText(map.heading_ref_deg || 0, "0");
  state.draft.aggregate.cache_ttl_hours = numText(aggregate.cache_ttl_hours || 24, "24");
  state.draft.notify.enabled = !!notify.enabled;
  state.draft.notify.node_status_enabled = notify.node_status_enabled !== false;
  state.draft.notify.wecom_key = "";
  state.draft.notify.wecom_configured = !!notify.wecom_configured;
  state.draft.host = data.host || {};
  state.draft.eula = data.eula || {};
  if (data.aggregate) {
    state.aggregateMeta = data.aggregate;
  }
  if (!options.checkboxOnly) {
    state.initial = deepClone({
      auth: {
        enabled: state.draft.auth.enabled,
        username: state.draft.auth.username,
        password: "",
        sso_enabled: state.draft.auth.sso_enabled,
        sso_check: "",
        password_configured: state.draft.auth.password_configured,
        sso_configured: state.draft.auth.sso_configured,
      },
      map: {
        base_name: state.draft.map.base_name,
        base_lat: state.draft.map.base_lat,
        base_lon: state.draft.map.base_lon,
        base_zoom: state.draft.map.base_zoom,
        map_auto_center_idle_sec: state.draft.map.map_auto_center_idle_sec,
        heading_ref_deg: state.draft.map.heading_ref_deg,
      },
      aggregate: {
        cache_ttl_hours: state.draft.aggregate.cache_ttl_hours,
      },
      notify: {
        enabled: state.draft.notify.enabled,
        node_status_enabled: state.draft.notify.node_status_enabled,
        wecom_key: "",
        wecom_configured: state.draft.notify.wecom_configured,
      },
      host: state.draft.host,
      eula: state.draft.eula,
    });
  }
  state.statuses.notify = `企业微信 ${state.draft.notify.wecom_configured ? "已配置" : "未配置"}`;
  state.statuses.eula = `${state.draft.eula.accepted ? "已同意许可协议。" : "还没有同意许可协议。"}\n状态文件 ${String(state.draft.eula.set_path || "viewer/cfg.db")}`;
  state.statuses.settings = `密码：${state.draft.auth.password_configured ? "已配置" : "未配置"}\nSSO：${state.draft.auth.sso_configured ? "已配置" : "未配置"}`;
}

async function loadSettings() {
  const data = await getJson("/api/settings");
  applySettingsData(data);
}

async function saveSettings(options = {}) {
  const data = await postJson("/api/settings/save", buildPayload(options));
  applySettingsData(data, options);
  state.statuses.settings = `${options.checkboxOnly ? "勾选项已保存。" : "设置已保存。"}\n密码：${data.auth.password_configured ? "已配置" : "未配置"}\nSSO：${data.auth.sso_configured ? "已配置" : "未配置"}`;
}

async function loadAggregate(force) {
  state.statuses.aggregate = force ? "正在重新聚合..." : "正在读取聚合缓存...";
  const data = force
    ? await postJson("/api/history/aggregate", { force: true })
    : await getJson("/api/history/aggregate");
  state.aggregateMeta = data;
  state.statuses.aggregate = aggregateMetaText.value;
}

async function clearAggregate() {
  const data = await postJson("/api/history/aggregate/clear", {});
  state.statuses.aggregate = `已清空 ${String(data.cleared || 0)} 条缓存`;
}

async function testNotify() {
  state.statuses.notify = "正在发送测试通知...";
  const data = await postJson("/api/settings/notify/test", {});
  state.statuses.notify = data.message || "测试通知已发送。";
}

async function revokeEula() {
  if (!confirm("确认撤回许可协议同意状态？")) {
    return;
  }
  const data = await postJson("/api/eula/revoke", {});
  state.draft.eula = data || {};
  state.statuses.eula = `${state.draft.eula.accepted ? "已同意许可协议。" : "还没有同意许可协议。"}\n状态文件 ${String(state.draft.eula.set_path || "viewer/cfg.db")}`;
  setTimeout(() => {
    location.href = "/eula?next=/settings";
  }, 500);
}

async function logout() {
  try {
    await postJson("/api/logout", {});
  } finally {
    location.href = "/";
  }
}

const aggregateMetaText = computed(() => {
  const data = state.aggregateMeta || {};
  let text = `缓存 ${data.cached ? "命中" : "已更新"}，飞机 ${String(data.count || 0)} 架，原始记录 ${String(data.raw_count || 0)} 条，聚合结果 ${String(data.aggregate_count || 0)} 条，TTL ${String(data.cache_ttl_hours || state.draft.aggregate.cache_ttl_hours || 24)} 小时`;
  if (data.generated_at) {
    try {
      text += ` | 生成 ${new Date(Number(data.generated_at) * 1000).toLocaleString()}`;
    } catch (_error) {
      // ignore
    }
  }
  return text;
});

const dirty = computed(() =>
  !sameJson(state.initial, {
    auth: {
      enabled: state.draft.auth.enabled,
      username: state.draft.auth.username,
      password: "",
      sso_enabled: state.draft.auth.sso_enabled,
      sso_check: "",
      password_configured: state.draft.auth.password_configured,
      sso_configured: state.draft.auth.sso_configured,
    },
    map: {
      base_name: state.draft.map.base_name,
      base_lat: state.draft.map.base_lat,
      base_lon: state.draft.map.base_lon,
      base_zoom: state.draft.map.base_zoom,
      map_auto_center_idle_sec: state.draft.map.map_auto_center_idle_sec,
      heading_ref_deg: state.draft.map.heading_ref_deg,
    },
    aggregate: {
      cache_ttl_hours: state.draft.aggregate.cache_ttl_hours,
    },
    notify: {
      enabled: state.draft.notify.enabled,
      node_status_enabled: state.draft.notify.node_status_enabled,
      wecom_key: "",
      wecom_configured: state.draft.notify.wecom_configured,
    },
    host: state.draft.host,
    eula: state.draft.eula,
  }),
);

function statCard(name, value, extra) {
  return h("div", { class: "stat-card" }, [
    h("div", { class: "stat-name" }, name),
    h("div", { class: "stat-value" }, value),
    extra ? h("div", { class: "stat-extra" }, extra) : null,
  ]);
}

function textField(label, value, onInput, attrs = {}) {
  return h("div", { class: `field${attrs.full ? " full" : ""}` }, [
    h("label", label),
    h("input", {
      type: attrs.type || "text",
      placeholder: attrs.placeholder || "",
      min: attrs.min,
      max: attrs.max,
      step: attrs.step,
      value,
      onInput: (event) => onInput(event.target.value),
    }),
  ]);
}

function checkboxField(id, label, checked, onChange) {
  return h("label", { key: id }, [
    h("input", {
      type: "checkbox",
      checked,
      onChange: async (event) => {
        onChange(event.target.checked);
        try {
          await withLoading("Viewer 设置", "正在保存勾选项", () => saveSettings({ checkboxOnly: true }));
        } catch (error) {
          state.statuses.settings = error.message || String(error);
        }
      },
    }),
    ` ${label}`,
  ]);
}

const App = {
  setup() {
    function jumpTo(id) {
      const target = document.getElementById(id);
      if (target && target.scrollIntoView) {
        target.scrollIntoView({ behavior: "smooth", block: "start" });
      }
    }

    async function browserLocation() {
      if (!navigator.geolocation) {
        state.statuses.settings = "浏览器不支持定位。";
        return;
      }
      navigator.geolocation.getCurrentPosition(
        (position) => {
          state.draft.map.base_lat = String(position.coords.latitude || "");
          state.draft.map.base_lon = String(position.coords.longitude || "");
          state.statuses.settings = "已读取当前浏览器位置，保存后生效。";
        },
        (error) => {
          state.statuses.settings = `定位失败: ${error && error.message ? error.message : error}`;
        },
        { enableHighAccuracy: true, timeout: 12000, maximumAge: 0 },
      );
    }

    function clearBaseLocation() {
      state.draft.map.base_lat = "";
      state.draft.map.base_lon = "";
    }

    function toggleTheme() {
      state.theme = state.theme === "light" ? "dark" : "light";
      applyTheme(state.theme);
    }

    return {
      state,
      dirty,
      aggregateMetaText,
      jumpTo,
      browserLocation,
      clearBaseLocation,
      toggleTheme,
      saveSettings,
      loadSettings,
      loadAggregate,
      clearAggregate,
      testNotify,
      revokeEula,
      logout,
    };
  },
  render() {
    const host = this.state.draft.host || {};
    const eula = this.state.draft.eula || {};
    return h("div", { class: "viewer-settings-root" }, [
      h("div", { class: "settings-sticky-head" }, [
        h("div", { class: "topbar" }, [
          h("div", [
            h("div", { class: "title" }, "Viewer 设置"),
            h("div", { class: "sub" }, "查看和维护 Viewer 的主机、地图、聚合、登录和通知设置。"),
          ]),
          h("div", { class: "actions" }, [
            h("button", { class: "btn", type: "button", onClick: () => (location.href = "/") }, "返回实时/历史"),
            h("button", { class: "btn", type: "button", onClick: () => (location.href = "/nodes") }, "节点管理"),
            h("button", { class: "btn ghost", type: "button", onClick: this.logout }, "退出"),
            h("button", { class: "btn", type: "button", onClick: this.toggleTheme }, this.state.theme === "light" ? "深色" : "浅色"),
            h(
              "button",
              {
                class: "btn",
                type: "button",
                onClick: async () => {
                  try {
                    await withLoading("Viewer 设置", "正在读取数据", () => this.loadSettings());
                  } catch (error) {
                    this.state.statuses.settings = error.message || String(error);
                  }
                },
              },
              "刷新",
            ),
          ]),
        ]),
        h("div", { class: "draft-bar" }, [
          h("div", { class: "draft-copy" }, [
            h("div", { class: "draft-title" }, this.dirty ? "有未保存的改动" : "没有未保存的改动"),
            h("div", { class: "draft-meta" }, this.dirty ? "勾选项会立即保存，文本和数值改动需要点保存。" : "这些设置会写入 viewer/cfg.db。"),
          ]),
          h("div", { class: "draft-actions" }, [
            h(
              "button",
              {
                class: "btn warn",
                type: "button",
                onClick: async () => {
                  try {
                    await withLoading("Viewer 设置", "正在保存设置", () => this.saveSettings());
                  } catch (error) {
                    this.state.statuses.settings = error.message || String(error);
                  }
                },
              },
              "保存设置",
            ),
          ]),
        ]),
        h("div", { class: "settings-jump", "aria-label": "设置分组导航" }, [
          ["settings-status", "状态"],
          ["settings-map", "地图"],
          ["settings-aggregate", "聚合"],
          ["settings-access", "访问"],
          ["settings-notify", "通知"],
          ["settings-eula", "许可"],
        ].map(([id, label]) =>
          h(
            "button",
            {
              key: id,
              class: "btn ghost",
              type: "button",
              onClick: () => this.jumpTo(id),
            },
            label,
          ),
        )),
      ]),
      h("div", { class: "panel active", "data-tab": "visual" }, [
        h("div", { class: "visual-grid" }, [
          h("div", { class: "stack" }, [
            h("div", { class: "stack-label" }, "Viewer 主机"),
            h("div", { class: "card", id: "settings-status" }, [
              h("div", { class: "section-head" }, [
                h("div", [h("h2", "主机状态"), h("div", { class: "section-copy" }, "查看 Viewer 进程、本地配置库和当前聚合状态。")]),
                h(
                  "button",
                  {
                    class: "btn ghost",
                    type: "button",
                    onClick: async () => {
                      try {
                        await withLoading("Viewer 主机状态", "正在读取数据", () => this.loadSettings());
                      } catch (error) {
                        this.state.statuses.settings = error.message || String(error);
                      }
                    },
                  },
                  "刷新状态",
                ),
              ]),
              h("div", { class: "stats-grid", style: "margin-top:14px" }, [
                statCard("主机", host.hostname || "—", host.platform || ""),
                statCard("CPU", fmtPct(host.cpu_percent), `核心 ${String(host.cpu_count || "—")}`),
                statCard(
                  "内存",
                  fmtPct(host.mem_percent),
                  host.mem_used_mb && host.mem_total_mb ? `${host.mem_used_mb} / ${host.mem_total_mb} MB` : "",
                ),
                statCard("运行时间", fmtSec(host.uptime_sec), `Viewer ${String(window.LIGHT_RID_VIEWER_VERSION || "")}`),
                statCard("节点", `${String(host.online_node_count || 0)}/${String(host.node_count || 0)}`, "在线 / 已添加"),
                statCard("飞机", `${String(host.online_drone_count || 0)}/${String(host.drone_count || 0)}`, "当前在线 / 聚合总数"),
              ]),
              h("div", { class: "micro" }, `配置库 ${String(host.db_path || "-")}，监听地址 ${String(host.listen || "-")}`),
            ]),
            h("div", { class: "card", id: "settings-map" }, [
              h("div", { class: "section-head" }, [h("div", [h("h2", "地图默认位置"), h("div", { class: "section-copy" }, "实时和历史页没有可显示飞机时，会回到这里的中心点和缩放级别。")])]),
              h("div", { class: "grid", style: "margin-top:14px" }, [
                textField("显示名称", this.state.draft.map.base_name, (value) => (this.state.draft.map.base_name = value)),
                textField("默认缩放", this.state.draft.map.base_zoom, (value) => (this.state.draft.map.base_zoom = value), { type: "number", min: 3, max: 30 }),
                textField("默认纬度", this.state.draft.map.base_lat, (value) => (this.state.draft.map.base_lat = value), { type: "number", step: "0.000001" }),
                textField("默认经度", this.state.draft.map.base_lon, (value) => (this.state.draft.map.base_lon = value), { type: "number", step: "0.000001" }),
                textField("自动回中冷却(s)", this.state.draft.map.map_auto_center_idle_sec, (value) => (this.state.draft.map.map_auto_center_idle_sec = value), { type: "number", min: 5, max: 600 }),
                textField("参考航向(°)", this.state.draft.map.heading_ref_deg, (value) => (this.state.draft.map.heading_ref_deg = value), { type: "number", step: "0.1" }),
                h("div", { class: "field full" }, [
                  h("label", "定位"),
                  h("div", { class: "row-actions" }, [
                    h("button", { class: "btn", type: "button", onClick: this.browserLocation }, "使用当前浏览器位置"),
                    h("button", { class: "btn ghost", type: "button", onClick: this.clearBaseLocation }, "清空默认坐标"),
                  ]),
                  h("div", { class: "micro" }, "能否定位取决于当前访问方式和浏览器授权。"),
                ]),
              ]),
            ]),
            h("div", { class: "card", id: "settings-aggregate" }, [
              h("div", { class: "section-head" }, [h("div", [h("h2", "历史聚合"), h("div", { class: "section-copy" }, "按 SN 合并各子站的历史和轨迹，并把结果缓存到 viewer/cfg.db。")])]),
              h("div", { class: "grid", style: "margin-top:14px" }, [
                textField("聚合缓存有效期(小时)", this.state.draft.aggregate.cache_ttl_hours, (value) => (this.state.draft.aggregate.cache_ttl_hours = value), { type: "number", min: 1, max: 168 }),
                h("div", { class: "field full" }, [
                  h("label", "手动维护"),
                  h("div", { class: "row-actions" }, [
                    h("button", { class: "btn", type: "button", onClick: async () => withLoading("历史聚合数据", "正在读取数据", () => this.loadAggregate(true)) }, "立即聚合"),
                    h("button", { class: "btn ghost", type: "button", onClick: async () => withLoading("历史聚合缓存", "正在读取数据", () => this.loadAggregate(false)) }, "查看缓存"),
                    h("button", { class: "btn warn", type: "button", onClick: async () => withLoading("历史聚合缓存", "正在清空缓存", this.clearAggregate) }, "清空缓存"),
                  ]),
                  h("div", { class: "micro" }, this.aggregateMetaText),
                ]),
              ]),
            ]),
          ]),
          h("div", { class: "stack" }, [
            h("div", { class: "stack-label" }, "访问与许可"),
            h("div", { class: "card access-group", id: "settings-access" }, [
              h("div", { class: "section-head" }, [h("div", [h("h2", "访问控制"), h("div", { class: "section-copy" }, "管理 Viewer 的网页登录和 SSO 快捷入口。")])]),
              h("div", { class: "access-subgrid", style: "margin-top:14px" }, [
                h("div", { class: "access-subcard full" }, [
                  h("div", { class: "access-subhead" }, [h("div", [h("div", { class: "access-subtitle" }, "网页登录"), h("div", { class: "access-subcopy" }, "用于设置页、节点页和聚合页的账号密码登录。")])]),
                  h("div", { class: "grid" }, [
                    textField("网页登录账号", this.state.draft.auth.username, (value) => (this.state.draft.auth.username = value)),
                    textField("网页登录密码", this.state.draft.auth.password, (value) => (this.state.draft.auth.password = value), { type: "password", placeholder: "留空即不修改" }),
                  ]),
                  h("div", { class: "checks" }, [checkboxField("auth-enabled", "启用网页登录", this.state.draft.auth.enabled, (checked) => (this.state.draft.auth.enabled = checked))]),
                ]),
                h("div", { class: "access-subcard full" }, [
                  h("div", { class: "access-subhead" }, [h("div", [h("div", { class: "access-subtitle" }, "SSO check 登录"), h("div", { class: "access-subcopy" }, "本机快捷登录入口，地址格式为 /?check=...。")])]),
                  h("div", { class: "grid" }, [
                    textField("SSO check 密钥", this.state.draft.auth.sso_check, (value) => (this.state.draft.auth.sso_check = value), { type: "password", placeholder: "留空即不修改，至少 12 位", full: true }),
                  ]),
                  h("div", { class: "checks" }, [checkboxField("sso-enabled", "启用 SSO check 登录", this.state.draft.auth.sso_enabled, (checked) => (this.state.draft.auth.sso_enabled = checked))]),
                  h("div", { class: "micro" }, "至少保留一种登录方式，免得把自己锁在外面。"),
                ]),
              ]),
              h("div", { class: `status${this.state.statuses.settings ? "" : ""}` }, this.state.statuses.settings),
            ]),
            h("div", { class: "card access-group", id: "settings-notify" }, [
              h("div", { class: "section-head" }, [h("div", [h("h2", "企业微信通知"), h("div", { class: "section-copy" }, "子站上下线变化时，可以发企业微信机器人通知。")])]),
              h("div", { class: "grid", style: "margin-top:14px" }, [
                textField("企业微信机器人 Key 或完整 Webhook URL", this.state.draft.notify.wecom_key, (value) => (this.state.draft.notify.wecom_key = value), { type: "password", placeholder: "留空即不修改", full: true }),
              ]),
              h("div", { class: "checks" }, [
                checkboxField("notify-enabled", "启用企业微信通知", this.state.draft.notify.enabled, (checked) => (this.state.draft.notify.enabled = checked)),
                checkboxField("notify-node-status", "子站在线/离线变化通知", this.state.draft.notify.node_status_enabled, (checked) => (this.state.draft.notify.node_status_enabled = checked)),
              ]),
              h("div", { class: "row-actions", style: "margin-top:14px" }, [
                h("button", { class: "btn ghost", type: "button", onClick: async () => withLoading("企业微信通知", "正在发送测试通知", this.testNotify) }, "测试通知"),
              ]),
              h("div", { class: "status" }, this.state.statuses.notify),
            ]),
            h("div", { class: "card", id: "settings-eula" }, [
              h("div", { class: "section-head" }, [h("div", [h("h2", "许可协议"), h("div", { class: "section-copy" }, "查看当前 EULA 状态，或撤回已同意的记录。")])]),
              h("div", { class: "row-actions", style: "margin-top:14px" }, [
                h("button", { class: "btn", type: "button", onClick: () => (location.href = "/eula?next=/settings") }, "查看 EULA"),
                h("button", { class: "btn warn", type: "button", disabled: !eula.accepted, onClick: async () => withLoading("许可协议", "正在撤回许可状态", this.revokeEula) }, "撤回同意"),
              ]),
              h("div", { class: "status" }, this.state.statuses.eula),
            ]),
          ]),
        ]),
      ]),
    ]);
  },
};

applyTheme(state.theme);

const root = document.getElementById("viewer-settings-root");
if (root) {
  createApp(App).mount(root);
  withLoading("Viewer 设置", "正在读取数据", loadSettings).catch((error) => {
    state.statuses.settings = error.message || String(error);
  });
}
