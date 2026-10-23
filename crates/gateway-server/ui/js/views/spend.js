// Spend logs: one filter row scoping everything below it, totals, spend per
// day, per key and per model group, and the logs themselves.

import { api } from "../api.js";
import { barChart, chartCard, columnChart } from "../charts.js";
import { busy, errorBox, field, h, icon, infoBox, mount } from "../dom.js";
import * as fmt from "../format.js";
import { pageHead, spendLogTable } from "./common.js";

const RANGES = [
  { id: "1d", label: "24 hours", days: 1 },
  { id: "7d", label: "7 days", days: 7 },
  { id: "30d", label: "30 days", days: 30 },
  { id: "all", label: "All", days: null },
];
const TOP = 8;
const SHOWN_LOGS = 200;

/** Spend per category, largest first, with the tail folded into "Other". */
function rank(logs, keyOf, labelOf) {
  const sums = new Map();
  for (const l of logs) {
    const k = keyOf(l);
    const cur = sums.get(k) ?? { key: k, label: labelOf(l), value: 0, count: 0 };
    cur.value += l.spend;
    cur.count += 1;
    sums.set(k, cur);
  }
  const sorted = [...sums.values()].sort((a, b) => b.value - a.value || b.count - a.count);
  if (sorted.length <= TOP) return sorted;
  const rest = sorted.slice(TOP - 1);
  return [...sorted.slice(0, TOP - 1), { key: null, label: `Other (${rest.length})`, value: rest.reduce((s, d) => s + d.value, 0), count: rest.reduce((s, d) => s + d.count, 0) }];
}

const dayStart = (d) => new Date(d.getFullYear(), d.getMonth(), d.getDate());

/** Spend per local calendar day, every day in the range present (zero if idle). */
function perDay(logs, days) {
  const today = dayStart(new Date());
  let first;
  if (days) first = new Date(today.getFullYear(), today.getMonth(), today.getDate() - (days - 1));
  else if (logs.length) first = dayStart(new Date(Math.min(...logs.map((l) => l.endTime)) * 1000));
  else return [];
  // At most 90 columns; older days are still in the totals and the table.
  const earliest = new Date(today.getFullYear(), today.getMonth(), today.getDate() - 89);
  if (first < earliest) first = earliest;
  const buckets = [];
  for (let d = new Date(first); d <= today; d = new Date(d.getFullYear(), d.getMonth(), d.getDate() + 1)) {
    buckets.push({ start: d.getTime(), label: fmt.day(d), value: 0, count: 0 });
  }
  for (const l of logs) {
    const t = dayStart(new Date(l.endTime * 1000)).getTime();
    const b = buckets.find((x) => x.start === t);
    if (b) {
      b.value += l.spend;
      b.count += 1;
    }
  }
  return buckets;
}

function readState() {
  const q = new URLSearchParams(location.search);
  return {
    range: RANGES.some((r) => r.id === q.get("range")) ? q.get("range") : "7d",
    api_key: q.get("api_key") ?? "",
    team_id: q.get("team_id") ?? "",
    model: q.get("model") ?? "",
    status: q.get("status") ?? "",
    limit: q.get("limit") ?? "1000",
  };
}

function writeState(state) {
  const q = new URLSearchParams();
  for (const [k, v] of Object.entries(state)) if (v) q.set(k, v);
  history.replaceState(null, "", `${location.pathname}?${q}`);
}

function select(label, options, value, onChange) {
  const el = h("select", null, options.map(([v, text]) => h("option", { value: v, selected: v === value }, text)));
  el.addEventListener("change", () => onChange(el.value));
  return field(label, el);
}

export function spendView(main) {
  const state = readState();
  const refresh = h("button", { type: "button", class: "small" }, icon("refresh"), "Refresh");
  const filters = h("div", { class: "filters", role: "search", "aria-label": "Filter spend logs" });
  const body = h("div", { class: "stack" }, h("p", { class: "placeholder" }, "Loading…"));
  mount(main, pageHead("Spend", "Settled calls, newest first. The filters scope every number, chart and row below.", refresh), filters, body);

  let options = { keys: [], teams: [], models: [] };

  const set = (patch) => {
    Object.assign(state, patch);
    writeState(state);
    drawFilters();
    load();
  };

  function drawFilters() {
    const ranges = h("div", { class: "field range" },
      h("span", { class: "field-label", id: "range-label" }, "Time range"),
      h("div", { class: "segmented", role: "group", "aria-labelledby": "range-label" },
        RANGES.map((r) => h("button", { type: "button", "aria-pressed": String(state.range === r.id), onclick: () => set({ range: r.id }) }, r.label))));
    mount(filters,
      ranges,
      select("Key", [["", "All keys"], ["0", "Master key"], ...options.keys.map((k) => [k, `Key #${k}`])], state.api_key, (v) => set({ api_key: v })),
      select("Team", [["", "All teams"], ...options.teams.map((t) => [t, `Team #${t}`])], state.team_id, (v) => set({ team_id: v })),
      select("Model group", [["", "All models"], ...options.models.map((m) => [m, m])], state.model, (v) => set({ model: v })),
      select("Status", [["", "Any status"], ["success", "Success"], ["failure", "Failed"], ["expired", "Expired"]], state.status, (v) => set({ status: v })),
      select("Logs", [["100", "Latest 100"], ["1000", "Latest 1,000"], ["10000", "Latest 10,000"]], state.limit, (v) => set({ limit: v })));
  }

  async function loadOptions() {
    const [keys, teams, models] = await Promise.allSettled([api("/key/list"), api("/team/list"), api("/model/info")]);
    options = {
      keys: (keys.value?.keys ?? []).map((k) => k.token_id).sort((a, b) => a - b),
      teams: (teams.value ?? []).map((t) => t.team_id).sort((a, b) => a - b),
      models: [...new Set((models.value?.data ?? []).map((m) => m.model_name).filter(Boolean))].sort(),
    };
    drawFilters();
  }

  async function load() {
    const range = RANGES.find((r) => r.id === state.range);
    const query = {
      limit: state.limit,
      api_key: state.api_key,
      team_id: state.team_id,
      model: state.model,
      status: state.status,
      start_date: range.days ? String(Math.floor(Date.now() / 1000) - range.days * 86400) : "",
    };
    try {
      const logs = await busy(body, () => api("/spend/logs", { query }));
      draw(logs, range);
    } catch (err) {
      mount(body, err.status === 404 ? infoBox(err.message) : errorBox(err));
    }
  }

  function draw(logs, range) {
    const total = logs.reduce((s, l) => s + l.spend, 0);
    const tokens = logs.reduce((s, l) => s + l.total_tokens, 0);
    const failed = logs.filter((l) => l.status !== "success").length;
    const capped = logs.length >= Number(state.limit);
    const days = perDay(logs, range.days);
    const byKey = rank(logs, (l) => l.api_key, (l) => (l.api_key === "0" ? "Master key" : `Key #${l.api_key}`));
    const byModel = rank(logs, (l) => l.model_group ?? String(l.model_group_id), (l) => l.model_group ?? `group ${l.model_group_id}`);
    const tile = (label, value, note) => h("div", { class: "tile" }, h("div", { class: "label" }, label), h("div", { class: "value" }, value), note && h("div", { class: "note" }, note));
    mount(body,
      capped && infoBox(`Showing the latest ${fmt.int(logs.length)} matching logs; older ones are not counted. Raise "Logs" or narrow the filters to see more.`),
      h("div", { class: "tiles" },
        tile("Spend", fmt.usd(total), range.days ? `last ${range.label}` : "all time"),
        tile("Calls", fmt.int(logs.length)),
        tile("Tokens", fmt.compact(tokens), `${fmt.int(tokens)} in and out`),
        tile("Failed or expired", fmt.int(failed), logs.length ? `${Math.round((failed / logs.length) * 100)}% of calls` : null)),
      chartCard("Spend per day", days, () => columnChart(days, { format: fmt.usd, tick: fmt.usdTick, title: "Spend per day" }), { format: fmt.usd, labelHeader: "Day", hint: "local time" }),
      h("div", { class: "grid two" },
        chartCard("Spend per key", byKey, () => barChart(byKey, { format: fmt.usd, title: "Spend per key", onSelect: (d) => d.key !== null && set({ api_key: d.key }) }), { format: fmt.usd, labelHeader: "Key", hint: "select a bar to filter" }),
        chartCard("Spend per model group", byModel, () => barChart(byModel, { format: fmt.usd, title: "Spend per model group", onSelect: (d) => d.key !== null && options.models.includes(d.key) && set({ model: d.key }) }), { format: fmt.usd, labelHeader: "Model group", hint: "select a bar to filter" })),
      h("section", { class: "card", "aria-labelledby": "logs-h" },
        h("div", { class: "card-head" }, h("h2", { id: "logs-h" }, "Spend logs"), logs.length > SHOWN_LOGS && h("span", { class: "hint" }, `first ${SHOWN_LOGS} of ${fmt.int(logs.length)}`)),
        spendLogTable(logs.slice(0, SHOWN_LOGS), { empty: "No spend logs match these filters." })));
  }

  refresh.addEventListener("click", () => {
    loadOptions();
    load();
  });
  drawFilters();
  loadOptions();
  load();
}
