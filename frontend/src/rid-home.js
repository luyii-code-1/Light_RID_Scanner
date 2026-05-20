import {
  createApp,
  computed,
  nextTick,
  reactive,
} from "vue/dist/vue.esm-bundler.js";

const appState = reactive({
  mounted: false,
  loading: false,
  page: "live",
  tableRows: [],
  liveRows: [],
});

function fn(name, fallback) {
  const value = window[name];
  return typeof value === "function" ? value : fallback;
}

function currentPage() {
  return String(fn("currentAppPage", () => "live")() || "live");
}

function normalizeRows(rows) {
  return Array.isArray(rows) ? rows.map((row) => row || {}) : [];
}

function fmtFallback(value, digits, unit) {
  if (value == null || Number.isNaN(Number(value))) {
    return "N/A";
  }
  return `${Number(value).toFixed(digits)}${unit}`;
}

function updateSummary(rows) {
  const list = normalizeRows(rows);
  const live = list.filter((row) => row && !row.lost).length;
  const totalEl = document.getElementById("n-total");
  const liveEl = document.getElementById("n-live");
  const lostEl = document.getElementById("n-lost");
  if (totalEl) totalEl.textContent = String(list.length);
  if (liveEl) liveEl.textContent = String(live);
  if (lostEl) lostEl.textContent = String(list.length - live);
}

function updateLatestDroneMap(rows) {
  const next = {};
  normalizeRows(rows).forEach((row) => {
    const sn = String((row && row.sn) || "");
    if (sn) {
      next[sn] = row;
    }
  });
  window.latestDroneMap = next;
}

function updateLiveCount(rows) {
  const countEl = document.getElementById("live-card-count");
  if (countEl) {
    const liveRecentRows = fn("liveRecentRows", (items) => normalizeRows(items));
    countEl.textContent = String(normalizeRows(liveRecentRows(rows)).length);
  }
}

function updateTableRows(rows) {
  const normalized = normalizeRows(rows);
  appState.page = currentPage();
  appState.tableRows = normalized;
  updateSummary(normalized);
  updateLatestDroneMap(normalized);
}

function updateLiveRows(rows) {
  const normalized = normalizeRows(rows);
  appState.liveRows = normalized;
  updateLiveCount(normalized);
}

function afterTableRender(rows) {
  const list = normalizeRows(rows);
  nextTick(() => {
    fn("syncTableSelectionUi", () => {})();
    fn("refreshTrackMgrOptions", () => {})(list);
    fn("refreshActiveInfoCard", () => {})(list);
  });
  fn("renderMapMiniList", () => {})(list);
}

const TableBodyRoot = {
  setup() {
    const rows = computed(() => appState.tableRows);
    const page = computed(() => appState.page);
    const fmt = fn("fmt", fmtFallback);
    const fmtAge = fn("fmtAge", (age) => (age == null ? "N/A" : String(age)));
    const uasIdText = fn("uasIdText", (row) => String((row && row.uas_id) || "N/A"));
    const scanTypeText = fn("scanTypeText", () => "N/A");
    const snSourceText = fn("snSourceText", () => "N/A");
    const firmwareTypeText = fn("firmwareTypeText", () => "N/A");
    const firmwareTypeKey = fn("firmwareTypeKey", () => "unknown");
    const trackColorForSn = fn("trackColorForSn", () => "#2899f5");
    const isSnSelected = fn("isSnSelected", () => false);
    const isHistoryTrackVisible = fn("isHistoryTrackVisible", () => false);
    const fieldCellAttrs = fn("fieldCellAttrs", () => "");
    const highlightAlpha = fn("highlightAlpha", () => 0);

    function selected(row) {
      const sn = String((row && row.sn) || "");
      return page.value === "history" ? !!isHistoryTrackVisible(sn) : !!isSnSelected(sn);
    }

    function rowClasses(row) {
      const sn = String((row && row.sn) || "");
      return {
        "data-row": true,
        mac: sn.startsWith("MAC:"),
        live: !row.lost && !sn.startsWith("MAC:"),
        lost: !!row.lost,
        selected: selected(row),
        "alarm-zone": !!(window.zoneAlarmSnSet && window.zoneAlarmSnSet[sn]),
      };
    }

    function snBadges(row) {
      return [
        { text: snSourceText(row), className: "sn-badge" },
        { text: scanTypeText(row), className: "sn-badge" },
        {
          text: firmwareTypeText(row),
          className: `sn-badge firmware-${firmwareTypeKey(row)}`,
        },
        ...(window.zoneAlarmSnSet && window.zoneAlarmSnSet[String((row && row.sn) || "")]
          ? [{ text: "报警", className: "sn-badge alarm" }]
          : []),
      ];
    }

    function cellClass(sn, field, extraClass = "") {
      const classes = String(extraClass || "")
        .split(/\s+/)
        .filter(Boolean);
      const attrText = String(fieldCellAttrs(sn, field, extraClass) || "");
      if (/\bhl\b/.test(attrText)) {
        classes.push("hl");
      }
      return classes.join(" ");
    }

    function cellStyle(sn, field) {
      const alpha = Number(highlightAlpha(sn, field) || 0);
      return alpha > 0
        ? { "--hl-alpha": String(Math.max(0, Math.min(1, alpha))) }
        : undefined;
    }

    function trackChipStyle(sn, isSelected) {
      return {
        "--track-color": String(trackColorForSn(sn) || "#2899f5"),
        display: isSelected ? "" : "none",
      };
    }

    return {
      rows,
      fmt,
      fmtAge,
      uasIdText,
      selected,
      rowClasses,
      snBadges,
      cellClass,
      cellStyle,
      trackChipStyle,
    };
  },
  template: `
    <template v-if="rows.length">
      <tr
        v-for="(row, idx) in rows"
        :key="String(row.sn || '') + ':' + idx"
        :class="rowClasses(row)"
        :data-sn="String(row.sn || '')"
      >
        <td>
          <div class="sel-wrap track-sel-wrap">
            <input
              class="sel-sn"
              type="checkbox"
              :data-sn="String(row.sn || '')"
              :checked="selected(row)"
            >
            <span
              class="track-color-chip"
              :style="trackChipStyle(String(row.sn || ''), selected(row))"
              title="轨迹颜色"
            ></span>
          </div>
        </td>
        <td class="idx-cell">{{ idx + 1 }}</td>
        <td>
          <div class="sn-cell">
            <span
              v-for="badge in snBadges(row)"
              :key="badge.className + ':' + badge.text"
              :class="badge.className"
            >{{ badge.text }}</span>
            <span class="mono">{{ String(row.sn || '') }}</span>
            <button class="icon-btn copy-sn" type="button" :data-sn="String(row.sn || '')" title="复制SN">⧉</button>
          </div>
        </td>
        <td
          :class="cellClass(String(row.sn || ''), 'model')"
          :style="cellStyle(String(row.sn || ''), 'model')"
          :data-hl-sn="String(row.sn || '')"
          data-hl-field="model"
        >{{ String(row.model || 'N/A') }}</td>
        <td
          :class="cellClass(String(row.sn || ''), 'rssi')"
          :style="cellStyle(String(row.sn || ''), 'rssi')"
          :data-hl-sn="String(row.sn || '')"
          data-hl-field="rssi"
        >{{ fmt(row.rssi, 0, 'dBm') }}</td>
        <td
          :class="cellClass(String(row.sn || ''), 'pkts')"
          :style="cellStyle(String(row.sn || ''), 'pkts')"
          :data-hl-sn="String(row.sn || '')"
          data-hl-field="pkts"
        >{{ row.pkts == null ? '0' : String(row.pkts) }}</td>
        <td
          :class="cellClass(String(row.sn || ''), 'dir')"
          :style="cellStyle(String(row.sn || ''), 'dir')"
          :data-hl-sn="String(row.sn || '')"
          data-hl-field="dir"
        >{{ String(row.dir || '-') }}</td>
        <td
          :class="cellClass(String(row.sn || ''), 'age_text', 'mono')"
          :style="cellStyle(String(row.sn || ''), 'age_text')"
          :data-hl-sn="String(row.sn || '')"
          data-hl-field="age_text"
        >{{ String(row.age_text || fmtAge(row.age)) }}</td>
        <td
          :class="cellClass(String(row.sn || ''), 'last_seen', 'mono')"
          :style="cellStyle(String(row.sn || ''), 'last_seen')"
          :data-hl-sn="String(row.sn || '')"
          data-hl-field="last_seen"
        >{{ String(row.last_seen || '-') }}</td>
        <td
          :class="cellClass(String(row.sn || ''), 'uas_id', 'mono')"
          :style="cellStyle(String(row.sn || ''), 'uas_id')"
          :data-hl-sn="String(row.sn || '')"
          data-hl-field="uas_id"
        >{{ uasIdText(row) }}</td>
      </tr>
    </template>
    <tr v-else>
      <td colspan="10" class="empty">暂无数据</td>
    </tr>
  `,
};

const LiveCardsRoot = {
  setup() {
    const sourceRows = computed(() => appState.liveRows);
    const liveRecentRows = fn("liveRecentRows", (rows) => normalizeRows(rows));
    const coordText = fn("coordText", (lat, lon) => (lat == null || lon == null ? "N/A" : `${lat}, ${lon}`));
    const homeAuxCoordText = fn("homeAuxCoordText", () => "N/A");
    const firmwareTypeText = fn("firmwareTypeText", () => "N/A");
    const uasIdText = fn("uasIdText", (row) => String((row && row.uas_id) || "N/A"));
    const isSnSelected = fn("isSnSelected", () => false);
    const fmt = fn("fmt", fmtFallback);
    const fmtAge = fn("fmtAge", (age) => (age == null ? "N/A" : String(age)));

    const rows = computed(() => {
      const list = normalizeRows(liveRecentRows(sourceRows.value));
      return list.sort((left, right) => {
        const leftLost = !!(left && left.lost);
        const rightLost = !!(right && right.lost);
        if (leftLost !== rightLost) {
          return leftLost ? 1 : -1;
        }
        const leftRssi = left && left.rssi != null ? Number(left.rssi) : -9999;
        const rightRssi = right && right.rssi != null ? Number(right.rssi) : -9999;
        return rightRssi - leftRssi;
      });
    });

    function rowClasses(row) {
      const sn = String((row && row.sn) || "");
      return {
        "live-card": true,
        selected: !!isSnSelected(sn),
        lost: !!row.lost,
        "alarm-zone": !!(window.zoneAlarmSnSet && window.zoneAlarmSnSet[sn]),
      };
    }

    function hasAlarm(row) {
      const sn = String((row && row.sn) || "");
      return !!(window.zoneAlarmSnSet && window.zoneAlarmSnSet[sn]);
    }

    function stateClass(row) {
      return row && row.lost ? "lost" : "live";
    }

    function stateText(row) {
      return row && row.lost ? "2分钟内离线" : "在线";
    }

    return {
      rows,
      rowClasses,
      hasAlarm,
      stateClass,
      stateText,
      coordText,
      homeAuxCoordText,
      firmwareTypeText,
      uasIdText,
      fmt,
      fmtAge,
      isSnSelected,
    };
  },
  template: `
    <template v-if="rows.length">
      <article
        v-for="(row, idx) in rows"
        :key="String(row.sn || '') + ':' + idx"
        :class="rowClasses(row)"
        :data-sn="String(row.sn || '')"
      >
        <div class="live-card-top">
          <div class="live-card-title" :title="String(row.model || 'N/A')">{{ String(row.model || 'N/A') }}</div>
          <div class="live-card-actions">
            <label class="live-card-pick">
              <input class="sel-sn" type="checkbox" :data-sn="String(row.sn || '')" :checked="isSnSelected(String(row.sn || ''))">
              <span>选中</span>
            </label>
            <span v-if="hasAlarm(row)" class="live-card-state alarm">区域告警</span>
            <span class="live-card-state firmware">{{ firmwareTypeText(row) }}</span>
            <span class="live-card-state" :class="stateClass(row)">{{ stateText(row) }}</span>
          </div>
        </div>
        <div class="live-card-snrow">
          <span class="label">SN</span>
          <span class="live-card-sntext" :title="String(row.sn || '')">{{ String(row.sn || '-') }}</span>
          <button class="icon-btn copy-sn" type="button" :data-sn="String(row.sn || '')" title="复制 SN">⧉</button>
        </div>
        <div class="live-card-snrow live-card-uasrow">
          <span class="label">UAS ID</span>
          <span class="live-card-sntext" :title="uasIdText(row)">{{ uasIdText(row) }}</span>
          <span></span>
        </div>
        <div v-if="row.discovered_base_text" class="viewer-base-label" :title="String(row.discovered_base_text)">{{ String(row.discovered_base_text) }}</div>
        <div class="live-card-grid">
          <div class="live-card-item"><div class="k">经纬度</div><div class="v">{{ row.lat == null || row.lon == null ? 'N/A' : (fmt(row.lat, 6, '') + ', ' + fmt(row.lon, 6, '')) }}</div></div>
          <div class="live-card-item"><div class="k">高度</div><div class="v">{{ fmt(row.alt, 1, 'm') }}</div></div>
          <div class="live-card-item"><div class="k">速度</div><div class="v">{{ fmt(row.spd, 2, 'm/s') }}</div></div>
          <div class="live-card-item"><div class="k">航向</div><div class="v">{{ String(row.dir || '-') }}</div></div>
          <div class="live-card-item"><div class="k">遥控站位置</div><div class="v">{{ coordText(row.pilot_lat, row.pilot_lon, 6) }}</div></div>
          <div class="live-card-item"><div class="k">Aux/Home</div><div class="v">{{ homeAuxCoordText(row) }}</div></div>
          <div class="live-card-item"><div class="k">信号 / 更新</div><div class="v">{{ (row.rssi == null ? 'N/A' : (String(row.rssi) + 'dBm')) + ' / ' + String(row.age_text || fmtAge(row.age)) }}</div></div>
        </div>
        <div class="live-card-foot">
          <span>最后数据包 {{ String(row.last_pkt_time || row.capture_time || '-') }}</span>
          <span>#{{ idx + 1 }}</span>
        </div>
      </article>
    </template>
    <div v-else class="ap-empty">暂无实时目标</div>
  `,
  methods: {
    window() {
      return window;
    },
  },
};

const legacyFns = {
  renderDroneTable: typeof window.renderDroneTable === "function" ? window.renderDroneTable : null,
  renderLiveCards: typeof window.renderLiveCards === "function" ? window.renderLiveCards : null,
  onData: typeof window.onData === "function" ? window.onData : null,
};

function mountApps() {
  if (appState.mounted) {
    return true;
  }
  const tbody = document.getElementById("tbody");
  const liveCards = document.getElementById("live-card-list");
  if (!tbody || !liveCards) {
    return false;
  }
  createApp(TableBodyRoot).mount(tbody);
  createApp(LiveCardsRoot).mount(liveCards);
  appState.mounted = true;
  document.body.setAttribute("data-rid-vue-home", "1");
  return true;
}

function renderDroneTableBridge(rows) {
  if (appState.loading && legacyFns.renderDroneTable) {
    legacyFns.renderDroneTable(rows);
    return;
  }
  if (!mountApps()) {
    if (legacyFns.renderDroneTable) {
      legacyFns.renderDroneTable(rows);
    }
    return;
  }
  updateTableRows(rows);
  updateLiveRows(rows);
  afterTableRender(rows);
}

function renderLiveCardsBridge(rows) {
  if (appState.loading && legacyFns.renderLiveCards) {
    legacyFns.renderLiveCards(rows);
    return;
  }
  if (!mountApps()) {
    if (legacyFns.renderLiveCards) {
      legacyFns.renderLiveCards(rows);
    }
    return;
  }
  updateLiveRows(rows);
}

function installBridge() {
  if (window.__RID_HOME_VUE_BRIDGE__) {
    return;
  }

  if (legacyFns.onData) {
    window.onData = function onDataBridge(payload) {
      appState.loading = !!(payload && payload.meta && payload.meta.viewer_loading);
      return legacyFns.onData(payload);
    };
  }

  window.renderDroneTable = renderDroneTableBridge;
  window.renderLiveCards = renderLiveCardsBridge;
  window.__RID_HOME_VUE_BRIDGE__ = {
    updateTableRows,
    updateLiveRows,
    mountApps,
  };
}

installBridge();
