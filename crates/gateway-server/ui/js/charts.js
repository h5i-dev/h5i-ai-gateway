// Charts as inline SVG. One series per chart (one colour, --series-1), thin
// marks with 4px rounded data ends, hairline grid, a value label only on the
// extreme, a hover/focus tooltip on every mark, and a table view of the same
// numbers. Charts redraw at their container's width.

import { h, s, mount, table } from "./dom.js";

const tooltip = () => document.getElementById("tooltip");

function showTip(evt, value, label) {
  const t = tooltip();
  mount(t, h("strong", null, value), h("span", null, label));
  t.hidden = false;
  const r = evt.currentTarget.getBoundingClientRect();
  const x = evt.clientX ?? r.left + r.width / 2;
  const y = evt.clientY ?? r.top;
  const w = t.offsetWidth;
  t.style.left = `${Math.min(Math.max(8, x - w / 2), window.innerWidth - w - 8)}px`;
  t.style.top = `${Math.max(8, y - t.offsetHeight - 12)}px`;
}
const hideTip = () => (tooltip().hidden = true);

/** Tick step: 1, 2 or 5 times a power of ten, about `count` ticks up to `max`. */
function ticks(max, count = 4) {
  if (!(max > 0)) return [0, 1];
  const raw = max / count;
  const p = 10 ** Math.floor(Math.log10(raw));
  const e = raw / p;
  const step = (e >= 7.5 ? 10 : e >= 3.5 ? 5 : e >= 1.5 ? 2 : 1) * p;
  const out = [];
  for (let v = 0; v <= max + step * 0.999; v += step) out.push(Number(v.toPrecision(12)));
  return out;
}

/** A column (or bar) with a 4px rounded data end and a square base. */
function column(x, y, w, hgt) {
  const r = Math.min(4, w / 2, hgt);
  return `M${x},${y + hgt}V${y + r}Q${x},${y} ${x + r},${y}H${x + w - r}Q${x + w},${y} ${x + w},${y + r}V${y + hgt}Z`;
}
function bar(x, y, w, hgt) {
  const r = Math.min(4, hgt / 2, w);
  return `M${x},${y}H${x + w - r}Q${x + w},${y} ${x + w},${y + r}V${y + hgt - r}Q${x + w},${y + hgt} ${x + w - r},${y + hgt}H${x}Z`;
}

function measure(text, size = 12) {
  return text.length * size * 0.58;
}

function datum(attrs, label, valueText, onActivate) {
  const g = s("g", { class: "datum", tabindex: 0, role: "img", "aria-label": `${label}: ${valueText}`, ...attrs });
  g.addEventListener("pointermove", (e) => showTip(e, valueText, label));
  g.addEventListener("pointerleave", hideTip);
  g.addEventListener("focus", (e) => showTip(e, valueText, label));
  g.addEventListener("blur", hideTip);
  if (onActivate) {
    g.style.cursor = "pointer";
    g.addEventListener("click", onActivate);
    g.addEventListener("keydown", (e) => (e.key === "Enter" || e.key === " ") && (e.preventDefault(), onActivate()));
  }
  return g;
}

/** Redraw `draw(width)` into `el` whenever its width changes. */
function responsive(el, draw) {
  let last = 0;
  const ro = new ResizeObserver(() => {
    const w = Math.round(el.clientWidth);
    if (w && w !== last) {
      last = w;
      mount(el, draw(w));
    }
  });
  ro.observe(el);
  return el;
}

/**
 * Vertical columns over an ordered axis (days). data: [{label, value}].
 * `format` formats values, `tick` formats axis ticks.
 */
export function columnChart(data, { format, tick, title, height = 220 }) {
  const el = h("div", { class: "chart", role: "group", "aria-label": title });
  return responsive(el, (width) => {
    const max = Math.max(0, ...data.map((d) => d.value));
    const ys = ticks(max);
    const top = ys[ys.length - 1] || 1;
    const left = Math.max(...ys.map((v) => measure(tick(v), 11))) + 12;
    const pad = { t: 22, r: 8, b: 26, l: left };
    const pw = width - pad.l - pad.r;
    const ph = height - pad.t - pad.b;
    const band = pw / Math.max(1, data.length);
    const w = Math.max(2, Math.min(24, band - 2));
    const y = (v) => pad.t + ph - (v / top) * ph;
    const svg = s("svg", { viewBox: `0 0 ${width} ${height}`, width, height, "aria-hidden": "false" });
    for (const v of ys) {
      svg.append(s("line", { class: v === 0 ? "baseline" : "gridline", x1: pad.l, x2: width - pad.r, y1: y(v), y2: y(v) }));
      svg.append(s("text", { class: "tick", x: pad.l - 8, y: y(v) + 4, "text-anchor": "end" }, tick(v)));
    }
    // Label every k-th column so x labels never collide.
    const widest = Math.max(...data.map((d) => measure(d.label, 11)), 1);
    const every = Math.max(1, Math.ceil((widest + 8) / band));
    const peak = data.reduce((best, d, i) => (d.value > (data[best]?.value ?? -1) ? i : best), 0);
    data.forEach((d, i) => {
      const cx = pad.l + band * i + band / 2;
      const hgt = Math.max(0, y(0) - y(d.value));
      const g = datum({}, d.label, format(d.value));
      g.append(s("rect", { class: "hit", x: pad.l + band * i, y: pad.t, width: band, height: ph }));
      if (hgt > 0) g.append(s("path", { class: "mark", d: column(cx - w / 2, y(d.value), w, hgt) }));
      svg.append(g);
      if (i % every === 0 || i === data.length - 1) {
        if (i === data.length - 1 && i % every !== 0 && (i % every) * band < widest) return;
        svg.append(s("text", { class: "tick", x: cx, y: height - 8, "text-anchor": "middle" }, d.label));
      }
    });
    if (max > 0) {
      const cx = pad.l + band * peak + band / 2;
      const anchor = cx < pad.l + 40 ? "start" : cx > width - 40 ? "end" : "middle";
      svg.append(s("text", { class: "value", x: cx, y: y(data[peak].value) - 6, "text-anchor": anchor }, format(data[peak].value)));
    }
    return svg;
  });
}

/**
 * Horizontal bars over categories, largest first. data: [{label, value}].
 * `onSelect(d)`, if given, makes each bar a control (e.g. filter by it).
 */
export function barChart(data, { format, title, onSelect }) {
  const el = h("div", { class: "chart", role: "group", "aria-label": title });
  return responsive(el, (width) => {
    const row = 30;
    const barH = 18;
    const max = Math.max(0, ...data.map((d) => d.value)) || 1;
    const labelW = Math.min(width * 0.38, Math.max(...data.map((d) => measure(d.label)), 40) + 12);
    const valueW = Math.max(...data.map((d) => measure(format(d.value)))) + 12;
    const pw = Math.max(20, width - labelW - valueW);
    const height = data.length * row + 4;
    const svg = s("svg", { viewBox: `0 0 ${width} ${height}`, width, height });
    svg.append(s("line", { class: "baseline", x1: labelW, x2: labelW, y1: 0, y2: height }));
    data.forEach((d, i) => {
      const y = i * row + (row - barH) / 2;
      const w = (d.value / max) * pw;
      const g = datum({}, d.label, format(d.value), onSelect && (() => onSelect(d)));
      g.append(s("rect", { class: "hit", x: 0, y: i * row, width, height: row }));
      const shown = d.label.length > 28 ? d.label.slice(0, 27) + "…" : d.label;
      g.append(s("text", { class: "label", x: labelW - 8, y: y + barH / 2 + 4, "text-anchor": "end" }, shown));
      if (w > 0) g.append(s("path", { class: "mark", d: bar(labelW + 1, y, Math.max(w, 2), barH) }));
      // Value at the bar's tip: every bar here is a ranked category, few in number.
      g.append(s("text", { class: i === 0 ? "value" : "tick", x: labelW + 1 + Math.max(w, 2) + 6, y: y + barH / 2 + 4 }, format(d.value)));
      svg.append(g);
    });
    return svg;
  });
}

/**
 * A chart card with a table view of the same numbers. `columns` are table
 * columns over `data` ({label, value}).
 */
export function chartCard(title, data, chart, { format, labelHeader = "Category", hint, empty = "No spend in this range." }) {
  const body = h("div");
  const toggle = h("button", { type: "button", class: "small ghost", "aria-pressed": "false" }, "Table");
  const head = h("div", { class: "card-head" }, h("h2", null, title), hint && h("span", { class: "hint" }, hint), data.length ? toggle : null);
  const showChart = () => mount(body, chart());
  const showTable = () =>
    mount(body, table([{ label: labelHeader, cell: (d) => d.label }, { label: "Spend", num: true, cell: (d) => format(d.value) }, ...(data[0]?.count !== undefined ? [{ label: "Requests", num: true, cell: (d) => d.count }] : [])], data, { caption: title }));
  toggle.addEventListener("click", () => {
    const on = toggle.getAttribute("aria-pressed") !== "true";
    toggle.setAttribute("aria-pressed", String(on));
    toggle.textContent = on ? "Chart" : "Table";
    on ? showTable() : showChart();
  });
  if (data.length) showChart();
  else mount(body, h("p", { class: "empty" }, empty));
  return h("section", { class: "card", "aria-label": title }, head, body);
}

/** Spend against a budget: the fill turns warning at 80% and critical at 100%. */
export function meter(spend, budget, format) {
  const text = h("span", { class: "text" }, h("strong", null, format(spend)), budget === null || budget === undefined ? " · no budget" : ` of ${format(budget)}`);
  if (budget === null || budget === undefined) return h("div", { class: "meter" }, text);
  const ratio = budget > 0 ? spend / budget : spend > 0 ? 1 : 0;
  const pct = Math.min(100, Math.round(ratio * 100));
  const fill = h("div", { class: "fill" });
  fill.style.width = `${pct}%`;
  return h("div", { class: ["meter", ratio >= 1 ? "critical" : ratio >= 0.8 && "warning"] },
    h("div", { class: "bar", role: "meter", "aria-valuemin": 0, "aria-valuemax": 100, "aria-valuenow": pct, "aria-label": `${pct}% of budget used` }, fill),
    text);
}
