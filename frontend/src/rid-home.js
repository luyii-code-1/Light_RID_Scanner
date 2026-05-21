import {
  createApp,
  computed,
  Fragment,
  h,
  nextTick,
  reactive,
} from "vue";

const appState = reactive({
  mounted: false,
  page: "live",
  loading: false,
  tableRows: [],
  liveRows: [],
});

const tableColumns = [
  { key: "index", label: "#", className: "sortable", sortable: true },
  { key: "sn", label: "SN", className: "sortable", sortable: true },
  { key: "model", label: "机型", className: "sortable", sortable: true },
  { key: "rssi", label: "信号", className: "sortable", sortable: true },
  { key: "pkts", label: "包", className: "sortable", sortable: true },
  { key: "dir", label: "方向", className: "sortable", sortable: true },
  { key: "age", label: "数据更新", className: "sortable", sortable: true },
  { key: "last_seen", label: "末次发现", className: "sortable", sortable: true },
  { key: "uas_id", label: "UAS ID", className: "sortable", sortable: true },
];

function fn(name, fallback) {
  const value = window[name];
  return typeof value === "function" ? value : fallback;
}

function qs(id) {
  return document.getElementById(id);
}

function normalizeRows(rows) {
  return Array.isArray(rows) ? rows.map((row) => row || {}) : [];
}

function currentPage() {
  return String(fn("currentAppPage", () => "live")() || "live");
}

function asText(value, fallback = "") {
  if (value == null || value === "") {
    return fallback;
  }
  return String(value);
}

function dataAttr(value) {
  return String(value || "");
}

function fmtFallback(value, digits, unit) {
  if (value == null || Number.isNaN(Number(value))) {
    return "N/A";
  }
  return `${Number(value).toFixed(digits)}${unit}`;
}

function stopEvent(event) {
  if (!event) {
    return;
  }
  if (typeof event.preventDefault === "function") {
    event.preventDefault();
  }
  if (typeof event.stopPropagation === "function") {
    event.stopPropagation();
  }
}

function updateSummary(rows) {
  const list = normalizeRows(rows);
  const live = list.filter((row) => row && !row.lost).length;
  const totalEl = qs("n-total");
  const liveEl = qs("n-live");
  const lostEl = qs("n-lost");
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
  const countEl = qs("live-card-count");
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
    fn("applyTableSortUi", () => {})();
  });
  fn("renderMapMiniList", () => {})(list);
}

function tableCell(sn, field, text, extraClass, cellClass, cellStyle) {
  return h(
    "td",
    {
      class: cellClass(sn, field, extraClass),
      style: cellStyle(sn, field),
      "data-hl-sn": sn,
      "data-hl-field": field,
    },
    text,
  );
}

const TableRoot = {
  setup() {
    const rows = computed(() => {
      const sortRows = fn("sortedDroneRows", (items) => normalizeRows(items));
      return normalizeRows(sortRows(appState.tableRows));
    });
    const page = computed(() => appState.page);
    const fmt = fn("fmt", fmtFallback);
    const fmtAge = fn("fmtAge", (age) => (age == null ? "N/A" : String(age)));
    const uasIdText = fn("uasIdText", (row) => String((row && row.uas_id) || "N/A"));
    const scanTypeText = fn("scanTypeText", () => "N/A");
    const snSourceText = fn("snSourceText", () => "N/A");
    const firmwareTypeText = fn("firmwareTypeText", () => "N/A");
    const firmwareTypeKey = fn("firmwareTypeKey", () => "unknown");
    const trackColorForSn = fn("trackColorForSn", () => "#2563eb");
    const isSnSelected = fn("isSnSelected", () => false);
    const isHistoryTrackVisible = fn("isHistoryTrackVisible", () => false);
    const fieldCellAttrs = fn("fieldCellAttrs", () => "");
    const highlightAlpha = fn("highlightAlpha", () => 0);
    const getTableSortState = fn("getTableSortState", () => ({ field: "", dir: "asc" }));
    const setTableSort = fn("setTableSort", () => {});
    const setAllVisibleSelected = fn("setAllVisibleSelected", () => {});
    const setHistorySnVisible = fn("setHistorySnVisible", () => {});
    const setSnSelected = fn("setSnSelected", () => {});
    const focusHistoryAircraft = fn("focusHistoryAircraft", () => {});
    const showDroneInfoCard = fn("showDroneInfoCard", () => {});
    const hideInfoCard = fn("hideInfoCard", () => {});
    const copySn = fn("copySn", () => {});
    let rowClickTimer = null;

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
      const out = [
        { text: snSourceText(row), className: "sn-badge" },
        { text: scanTypeText(row), className: "sn-badge" },
        {
          text: firmwareTypeText(row),
          className: `sn-badge firmware-${firmwareTypeKey(row)}`,
        },
      ];
      const sn = String((row && row.sn) || "");
      if (window.zoneAlarmSnSet && window.zoneAlarmSnSet[sn]) {
        out.push({ text: "报警", className: "sn-badge alarm" });
      }
      return out.filter((item) => item.text && item.text !== "N/A");
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
        "--track-color": String(trackColorForSn(sn) || "#2563eb"),
        display: isSelected ? "" : "none",
      };
    }

    function sortClass(field) {
      const state = getTableSortState() || {};
      if (String(state.field || "") !== String(field || "")) {
        return "sortable";
      }
      return `sortable sorted-${state.dir === "desc" ? "desc" : "asc"}`;
    }

    function allSelected() {
      if (!rows.value.length) {
        return false;
      }
      return rows.value.every((row) => selected(row));
    }

    function someSelected() {
      return rows.value.some((row) => selected(row));
    }

    function toggleAll(event) {
      setAllVisibleSelected(!!(event && event.target && event.target.checked));
    }

    function toggleRow(row, checked) {
      const sn = String((row && row.sn) || "");
      if (!sn) {
        return;
      }
      if (page.value === "history") {
        setHistorySnVisible(sn, !!checked);
      } else {
        setSnSelected(sn, !!checked);
      }
    }

    function onRowClick(row) {
      const sn = String((row && row.sn) || "");
      if (!sn) {
        return;
      }
      if (rowClickTimer) {
        clearTimeout(rowClickTimer);
        rowClickTimer = null;
      }
      rowClickTimer = setTimeout(() => {
        rowClickTimer = null;
        if (page.value === "history") {
          focusHistoryAircraft(sn);
          return;
        }
        const item = (window.latestDroneMap || {})[sn];
        if (item) {
          showDroneInfoCard(item);
        }
      }, 220);
    }

    function onRowDblClick(row, event) {
      stopEvent(event);
      const sn = String((row && row.sn) || "");
      if (!sn) {
        return;
      }
      if (rowClickTimer) {
        clearTimeout(rowClickTimer);
        rowClickTimer = null;
      }
      setSnSelected(sn, true);
      hideInfoCard();
    }

    function onCopyClick(sn, event) {
      stopEvent(event);
      copySn(sn);
    }

    function onHeaderClick(field, event) {
      stopEvent(event);
      setTableSort(field);
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
      sortClass,
      allSelected,
      someSelected,
      toggleAll,
      toggleRow,
      onRowClick,
      onRowDblClick,
      onCopyClick,
      onHeaderClick,
    };
  },
  render() {
      return h("table", { id: "dtable" }, [
      h(
        "thead",
        h("tr", [
          h("th", [
            h("div", { class: "sel-wrap" }, [
              h("input", {
                id: "sel-all",
                class: "sel-sn",
                type: "checkbox",
                title: "全选",
                checked: this.allSelected(),
                indeterminate: !this.allSelected() && this.someSelected(),
                onChange: this.toggleAll,
              }),
            ]),
          ]),
          ...tableColumns.map((column) =>
            h(
              "th",
              {
                key: column.key,
                class: this.sortClass(column.key),
                "data-sort": column.key,
                onClick: (event) => this.onHeaderClick(column.key, event),
              },
              column.label,
            ),
          ),
        ]),
      ),
      h(
        "tbody",
        { id: "tbody" },
        this.rows.length
          ? this.rows.map((row, idx) => {
              const sn = dataAttr(row && row.sn);
              const isSelected = this.selected(row);
              return h(
                "tr",
                {
                    key: sn || `row-${idx}`,
                  class: this.rowClasses(row),
                  "data-sn": sn,
                  onClick: () => this.onRowClick(row),
                  onDblclick: (event) => this.onRowDblClick(row, event),
                },
                [
                  h("td", [
                    h("div", { class: "sel-wrap track-sel-wrap" }, [
                      h("input", {
                        class: "sel-sn",
                        type: "checkbox",
                        "data-sn": sn,
                        checked: isSelected,
                        onClick: stopEvent,
                        onChange: (event) => this.toggleRow(row, event.target.checked),
                      }),
                      h("span", {
                        class: "track-color-chip",
                        style: this.trackChipStyle(sn, isSelected),
                        title: "轨迹颜色",
                      }),
                    ]),
                  ]),
                  h("td", { class: "idx-cell" }, String(idx + 1)),
                  h("td", [
                    h("div", { class: "sn-cell" }, [
                      ...this.snBadges(row).map((badge) =>
                        h(
                          "span",
                          {
                            key: `${badge.className}:${badge.text}`,
                            class: badge.className,
                          },
                          badge.text,
                        ),
                      ),
                      h("span", { class: "mono" }, sn),
                      h(
                        "button",
                        {
                          class: "icon-btn copy-sn",
                          type: "button",
                          "data-sn": sn,
                          title: "复制 SN",
                          onClick: (event) => this.onCopyClick(sn, event),
                        },
                        "⧉",
                      ),
                    ]),
                  ]),
                  tableCell(sn, "model", asText(row && row.model, "N/A"), "", this.cellClass, this.cellStyle),
                  tableCell(sn, "rssi", this.fmt(row && row.rssi, 0, "dBm"), "", this.cellClass, this.cellStyle),
                  tableCell(
                    sn,
                    "pkts",
                    row && row.pkts == null ? "0" : String(row.pkts),
                    "mono",
                    this.cellClass,
                    this.cellStyle,
                  ),
                  tableCell(sn, "dir", asText(row && row.dir, "-"), "", this.cellClass, this.cellStyle),
                  tableCell(
                    sn,
                    "age_text",
                    asText(row && row.age_text, this.fmtAge(row && row.age)),
                    "mono",
                    this.cellClass,
                    this.cellStyle,
                  ),
                  tableCell(
                    sn,
                    "last_seen",
                    asText(row && row.last_seen, "-"),
                    "mono",
                    this.cellClass,
                    this.cellStyle,
                  ),
                  tableCell(sn, "uas_id", this.uasIdText(row), "mono", this.cellClass, this.cellStyle),
                ],
              );
            })
          : [h("tr", { key: "empty" }, [h("td", { colspan: "10", class: "empty" }, "暂无数据")])],
      ),
    ]);
  },
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

    function onCopyClick(sn, event) {
      stopEvent(event);
      fn("copySn", () => {})(sn);
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
      onCopyClick,
    };
  },
  render() {
    if (!this.rows.length) {
      return h("div", { class: "ap-empty" }, "暂无实时目标");
    }
    return h(
      Fragment,
      this.rows.map((row, idx) => {
        const sn = dataAttr(row && row.sn);
        const title = asText(row && row.model, "N/A");
        const latlon =
          row && row.lat != null && row.lon != null
            ? `${this.fmt(row.lat, 6, "")}, ${this.fmt(row.lon, 6, "")}`
            : "N/A";
        const rssiText = row && row.rssi == null ? "N/A" : `${String(row && row.rssi)}dBm`;
        const updateText = asText(row && row.age_text, this.fmtAge(row && row.age));
        const footText = asText(row && (row.last_pkt_time || row.capture_time), "-");
        return h(
          "article",
          {
            key: sn || `card-${idx}`,
            class: this.rowClasses(row),
            "data-sn": sn,
          },
          [
            h("div", { class: "live-card-top" }, [
              h("div", { class: "live-card-title", title }, title),
              h("div", { class: "live-card-actions" }, [
                h("label", { class: "live-card-pick" }, [
                  h("input", {
                    class: "sel-sn",
                    type: "checkbox",
                    "data-sn": sn,
                    checked: this.isSnSelected(sn),
                  }),
                  h("span", "选中"),
                ]),
                ...(this.hasAlarm(row) ? [h("span", { class: "live-card-state alarm" }, "区域报警")] : []),
                h("span", { class: "live-card-state firmware" }, this.firmwareTypeText(row)),
                h("span", { class: ["live-card-state", this.stateClass(row)] }, this.stateText(row)),
              ]),
            ]),
            h("div", { class: "live-card-snrow" }, [
              h("span", { class: "label" }, "SN"),
              h("span", { class: "live-card-sntext", title: asText(row && row.sn, "") }, asText(row && row.sn, "-")),
              h(
                "button",
                {
                  class: "icon-btn copy-sn",
                  type: "button",
                  "data-sn": sn,
                  title: "复制 SN",
                  onClick: (event) => this.onCopyClick(sn, event),
                },
                "⧉",
              ),
            ]),
            h("div", { class: "live-card-snrow live-card-uasrow" }, [
              h("span", { class: "label" }, "UAS ID"),
              h("span", { class: "live-card-sntext", title: this.uasIdText(row) }, this.uasIdText(row)),
              h("span"),
            ]),
            ...(row && row.discovered_base_text
              ? [
                  h(
                    "div",
                    {
                      class: "viewer-base-label",
                      title: String(row.discovered_base_text),
                    },
                    String(row.discovered_base_text),
                  ),
                ]
              : []),
            h("div", { class: "live-card-grid" }, [
              h("div", { class: "live-card-item" }, [h("div", { class: "k" }, "经纬度"), h("div", { class: "v" }, latlon)]),
              h("div", { class: "live-card-item" }, [h("div", { class: "k" }, "高度"), h("div", { class: "v" }, this.fmt(row && row.alt, 1, "m"))]),
              h("div", { class: "live-card-item" }, [h("div", { class: "k" }, "速度"), h("div", { class: "v" }, this.fmt(row && row.spd, 2, "m/s"))]),
              h("div", { class: "live-card-item" }, [h("div", { class: "k" }, "航向"), h("div", { class: "v" }, asText(row && row.dir, "-"))]),
              h("div", { class: "live-card-item" }, [h("div", { class: "k" }, "遥控站位置"), h("div", { class: "v" }, this.coordText(row && row.pilot_lat, row && row.pilot_lon, 6))]),
              h("div", { class: "live-card-item" }, [h("div", { class: "k" }, "Aux/Home"), h("div", { class: "v" }, this.homeAuxCoordText(row))]),
              h("div", { class: "live-card-item" }, [h("div", { class: "k" }, "信号 / 更新"), h("div", { class: "v" }, `${rssiText} / ${updateText}`)]),
            ]),
            h("div", { class: "live-card-foot" }, [
              h("span", `最后数据包 ${footText}`),
              h("span", `#${idx + 1}`),
            ]),
          ],
        );
      }),
    );
  },
};

const legacyFns = {
  onData: typeof window.onData === "function" ? window.onData : null,
  renderDroneTable: typeof window.renderDroneTable === "function" ? window.renderDroneTable : null,
  renderLiveCards: typeof window.renderLiveCards === "function" ? window.renderLiveCards : null,
};

function mountTableApp() {
  const wrap = document.querySelector(".tbl-wrap");
  if (!wrap) {
    return false;
  }
  let root = document.getElementById("rid-vue-table-root");
  if (!root) {
    wrap.innerHTML = '<div id="rid-vue-table-root"></div>';
    root = document.getElementById("rid-vue-table-root");
  }
  if (!root || root.getAttribute("data-vue-mounted") === "1") {
    return !!root;
  }
  createApp(TableRoot).mount(root);
  root.setAttribute("data-vue-mounted", "1");
  return true;
}

function mountLiveCardsApp() {
  const liveCards = qs("live-card-list");
  if (!liveCards || liveCards.getAttribute("data-vue-mounted") === "1") {
    return !!liveCards;
  }
  createApp(LiveCardsRoot).mount(liveCards);
  liveCards.setAttribute("data-vue-mounted", "1");
  return true;
}

function mountApps() {
  if (appState.mounted) {
    return true;
  }
  const mountedTable = mountTableApp();
  const mountedCards = mountLiveCardsApp();
  if (!mountedTable && !mountedCards) {
    return false;
  }
  appState.mounted = true;
  document.body.setAttribute("data-rid-vue-home", "1");
  return true;
}

function renderDroneTableBridge(rows) {
  if (!mountApps()) {
    if (legacyFns.renderDroneTable) {
      return legacyFns.renderDroneTable(rows);
    }
    return;
  }
  updateTableRows(rows);
  updateLiveRows(rows);
  afterTableRender(rows);
}

function renderLiveCardsBridge(rows) {
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
