import { createApp, computed, h, reactive } from "vue";

const state = reactive({
  nodes: [],
  selectedId: null,
  checkedIds: {},
  sections: {
    basic: { field: "name", dir: "asc" },
    load: { field: "cpu", dir: "desc" },
    scan: { field: "online_count", dir: "desc" },
  },
});

const storagePrefix = "rid_node_center_sort_";

function safeText(value, fallback = "—") {
  if (value == null || value === "") {
    return fallback;
  }
  return String(value);
}

function numValue(value, fallback = Number.NEGATIVE_INFINITY) {
  const out = Number(value);
  return Number.isFinite(out) ? out : fallback;
}

function fmtPct(value) {
  const out = Number(value);
  return Number.isFinite(out) ? `${out.toFixed(1)}%` : "—";
}

function fmtTemp(value) {
  const out = Number(value);
  return Number.isFinite(out) ? `${out.toFixed(1)}°C` : "—";
}

function fmtMs(value) {
  const out = Number(value);
  return Number.isFinite(out) ? `${Math.round(out)}ms` : "—";
}

function fmtTime(value) {
  const out = Number(value);
  if (!Number.isFinite(out) || out <= 0) {
    return "—";
  }
  try {
    return new Date(out * 1000).toLocaleString();
  } catch (_error) {
    return String(value);
  }
}

function sectionColumns(kind) {
  if (kind === "load") {
    return [
      { key: "name", label: "节点" },
      { key: "ok", label: "状态" },
      { key: "cpu", label: "CPU" },
      { key: "mem", label: "内存" },
      { key: "temp", label: "温度" },
      { key: "load1", label: "负载" },
    ];
  }
  if (kind === "scan") {
    return [
      { key: "name", label: "节点" },
      { key: "ok", label: "状态" },
      { key: "count", label: "累计" },
      { key: "online_count", label: "在线" },
      { key: "status_code", label: "状态码" },
      { key: "fetched_at", label: "刷新时间" },
    ];
  }
  return [
    { key: "name", label: "节点" },
    { key: "ok", label: "状态" },
    { key: "latency_ms", label: "延迟" },
    { key: "station", label: "站点" },
    { key: "sniff_state", label: "采集" },
    { key: "base_url", label: "地址" },
  ];
}

function compareBy(kind, field, left, right) {
  if (field === "name") {
    return safeText(left.name || left.base_url, "").localeCompare(safeText(right.name || right.base_url, ""));
  }
  if (field === "base_url") {
    return safeText(left.base_url, "").localeCompare(safeText(right.base_url, ""));
  }
  if (field === "ok") {
    return numValue(left.ok ? 1 : 0, 0) - numValue(right.ok ? 1 : 0, 0);
  }
  if (kind === "basic" && field === "station") {
    return safeText((left.station || {}).name, "").localeCompare(safeText((right.station || {}).name, ""));
  }
  if (kind === "basic" && field === "sniff_state") {
    return safeText((left.service || {}).sniff_state, "").localeCompare(safeText((right.service || {}).sniff_state, ""));
  }
  if (kind === "load" && field === "cpu") {
    return numValue((left.host || {}).cpu_percent ?? (left.service || {}).cpu_percent) - numValue((right.host || {}).cpu_percent ?? (right.service || {}).cpu_percent);
  }
  if (kind === "load" && field === "mem") {
    return numValue((left.host || {}).mem_percent ?? (left.service || {}).mem_percent) - numValue((right.host || {}).mem_percent ?? (right.service || {}).mem_percent);
  }
  if (kind === "load" && field === "temp") {
    return numValue((left.host || {}).temperature_c ?? (left.service || {}).temperature_c) - numValue((right.host || {}).temperature_c ?? (right.service || {}).temperature_c);
  }
  if (kind === "load" && field === "load1") {
    return numValue((left.host || {}).load1) - numValue((right.host || {}).load1);
  }
  return numValue(left[field]) - numValue(right[field]);
}

function readStoredSort(kind) {
  try {
    const raw = localStorage.getItem(storagePrefix + kind);
    if (!raw) return null;
    const parsed = JSON.parse(raw);
    if (!parsed || !parsed.field) return null;
    return { field: String(parsed.field), dir: parsed.dir === "asc" ? "asc" : "desc" };
  } catch (_error) {
    return null;
  }
}

function writeStoredSort(kind) {
  try {
    localStorage.setItem(storagePrefix + kind, JSON.stringify(state.sections[kind]));
  } catch (_error) {
    // ignore
  }
}

function action(name, ...args) {
  const host = window.__RID_NODE_CENTER_ACTIONS__ || {};
  const fn = host[name];
  if (typeof fn === "function") {
    return fn(...args);
  }
  return undefined;
}

const NodeSection = {
  props: {
    kind: { type: String, required: true },
  },
  setup(props) {
    const rows = computed(() => {
      const sortState = state.sections[props.kind];
      const list = Array.isArray(state.nodes) ? state.nodes.slice() : [];
      list.sort((left, right) => {
        const cmp = compareBy(props.kind, sortState.field, left, right);
        if (cmp === 0) {
          return safeText(left.name || left.base_url, "").localeCompare(safeText(right.name || right.base_url, ""));
        }
        return sortState.dir === "asc" ? cmp : -cmp;
      });
      return list;
    });

    function sortClass(field) {
      const sortState = state.sections[props.kind];
      if (sortState.field !== field) {
        return "node-sort-btn";
      }
      return `node-sort-btn active ${sortState.dir === "asc" ? "sorted-asc" : "sorted-desc"}`;
    }

    function setSort(field) {
      const sortState = state.sections[props.kind];
      if (sortState.field === field) {
        sortState.dir = sortState.dir === "asc" ? "desc" : "asc";
      } else {
        sortState.field = field;
        sortState.dir = field === "name" ? "asc" : "desc";
      }
      writeStoredSort(props.kind);
    }

    function toggleChecked(node, checked) {
      state.checkedIds[Number(node.id || 0)] = !!checked;
      action("onChecked", Number(node.id || 0), !!checked);
    }

    function openDetail(node) {
      const name = props.kind === "load" ? "showLoad" : props.kind === "scan" ? "showScan" : "showBasic";
      action(name, Number(node.id || 0));
    }

    return {
      rows,
      sortClass,
      setSort,
      toggleChecked,
      openDetail,
      columns: computed(() => sectionColumns(props.kind)),
    };
  },
  render() {
    if (!this.rows.length) {
      return h("div", { class: "empty-state" }, "还没有添加节点。");
    }
    return h("div", { class: "node-list-stack" }, [
      h(
        "div",
        { class: "node-sort-row" },
        this.columns.map((column) =>
          h(
            "button",
            {
              key: column.key,
              type: "button",
              class: this.sortClass(column.key),
              onClick: () => this.setSort(column.key),
            },
            column.label,
          ),
        ),
      ),
      h(
        "div",
        { class: "node-card-list" },
        this.rows.map((node) => {
          const station = node.station || {};
          const service = node.service || {};
          const host = node.host || {};
          const nodeId = Number(node.id || 0);
          const active = Number(state.selectedId || 0) === nodeId;
          const checked = !!state.checkedIds[nodeId];
          const statusText = node.ok ? "在线" : "离线";
          const statusClass = node.ok ? "ok" : "err";
          let metrics = [];
          let meta = safeText(node.base_url, "—");
          if (this.kind === "load") {
            metrics = [
              { k: "CPU", v: fmtPct(host.cpu_percent ?? service.cpu_percent) },
              { k: "内存", v: fmtPct(host.mem_percent ?? service.mem_percent) },
              { k: "温度", v: fmtTemp(host.temperature_c ?? service.temperature_c) },
            ];
            meta = `负载 ${safeText(host.load1, "—")} / ${safeText(host.load5, "—")} / ${safeText(host.load15, "—")}`;
          } else if (this.kind === "scan") {
            metrics = [
              { k: "累计", v: safeText(node.count, "0") },
              { k: "在线", v: safeText(node.online_count, "0") },
              { k: "状态码", v: safeText(node.status_code, "—") },
            ];
            meta = `最近刷新 ${fmtTime(node.fetched_at)}`;
          } else {
            metrics = [
              { k: "延迟", v: fmtMs(node.latency_ms) },
              { k: "站点", v: safeText(station.name || node.name, "—") },
              { k: "采集", v: safeText(service.sniff_state || (node.enabled ? "—" : "disabled"), "—") },
            ];
            if (node.error) {
              meta = String(node.error).slice(0, 180);
            }
          }
          return h(
            "article",
            {
              key: `${this.kind}:${nodeId}`,
              class: ["node-card", active ? "active" : "", node.ok ? "" : "offline"],
              onClick: () => this.openDetail(node),
            },
            [
              h("div", { class: "node-card-head" }, [
                h("input", {
                  class: "node-select",
                  type: "checkbox",
                  checked,
                  "data-online": node.ok ? "1" : "0",
                  onClick: (event) => event.stopPropagation(),
                  onChange: (event) => this.toggleChecked(node, event.target.checked),
                }),
                h("div", { class: "node-card-title", title: safeText(node.name || node.base_url, "节点") }, safeText(node.name || node.base_url, "节点")),
                h("span", { class: ["node-pill", statusClass] }, statusText),
              ]),
              h("div", { class: "node-card-meta mono" }, safeText(node.base_url, "—")),
              h(
                "div",
                { class: "node-metrics" },
                metrics.map((metric) =>
                  h("div", { key: metric.k, class: "node-metric" }, [
                    h("div", { class: "k" }, metric.k),
                    h("div", { class: "v" }, metric.v),
                  ]),
                ),
              ),
              h("div", { class: "node-card-meta" }, meta),
            ],
          );
        }),
      ),
    ]);
  },
};

function mountSection(id, kind) {
  const target = document.getElementById(id);
  if (!target || target.getAttribute("data-vue-mounted") === "1") {
    return;
  }
  createApp({
    render() {
      return h(NodeSection, { kind });
    },
  }).mount(target);
  target.setAttribute("data-vue-mounted", "1");
}

function mountAll() {
  mountSection("node-basic-list", "basic");
  mountSection("node-load-list", "load");
  mountSection("node-scan-list", "scan");
}

function installBridge() {
  if (window.__RID_NODE_CENTER_BRIDGE__) {
    return;
  }
  ["basic", "load", "scan"].forEach((kind) => {
    const stored = readStoredSort(kind);
    if (stored) {
      state.sections[kind] = stored;
    }
  });
  window.__RID_NODE_CENTER_BRIDGE__ = {
    mount() {
      mountAll();
    },
    update(payload) {
      mountAll();
      const next = payload || {};
      state.nodes = Array.isArray(next.nodes) ? next.nodes.slice() : [];
      state.selectedId = next.selectedId == null ? null : Number(next.selectedId);
      state.checkedIds = { ...(next.checkedIds || {}) };
    },
  };
}

installBridge();
