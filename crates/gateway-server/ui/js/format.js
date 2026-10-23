// Number, money and time formatting, in the browser's locale. Every
// formatter degrades to plain text where a browser lacks part of Intl.

function numberFormat(options) {
  try {
    const f = new Intl.NumberFormat(undefined, options);
    f.format(1);
    return (v) => f.format(v);
  } catch {
    const digits = options.maximumFractionDigits ?? 0;
    return (v) => Number(v).toFixed(digits);
  }
}

const intFmt = numberFormat({ maximumFractionDigits: 0 });
const compactFmt = numberFormat({ notation: "compact", maximumFractionDigits: 1 });
const moneyFmts = new Map();

/** Dollars, with enough digits that small LLM charges do not read as $0.00. */
export function usd(v) {
  if (v === null || v === undefined) return "—";
  const n = Number(v);
  const abs = Math.abs(n);
  const digits = abs === 0 || abs >= 0.01 ? 2 : Math.min(10, Math.max(4, 3 - Math.floor(Math.log10(abs))));
  if (!moneyFmts.has(digits)) moneyFmts.set(digits, numberFormat({ minimumFractionDigits: 2, maximumFractionDigits: digits }));
  return `${n < 0 ? "-" : ""}$${moneyFmts.get(digits)(abs)}`;
}

/** Compact dollars for axis ticks: $0, $0.5, $1.2K. */
export function usdTick(v) {
  if (v === 0) return "$0";
  if (Math.abs(v) >= 1000) return "$" + compactFmt(v);
  return "$" + Number(v.toPrecision(3)).toString();
}

export const int = (v) => (v === null || v === undefined ? "—" : intFmt(v));
export const compact = (v) => compactFmt(v);

/** "1 key", "3 keys". */
export const plural = (n, noun) => `${intFmt(n)} ${noun}${n === 1 ? "" : "s"}`;

/** A limit: null means none. */
export const limit = (v, unit = "") => (v === null || v === undefined ? "∞" : `${intFmt(v)}${unit}`);

/** Dollars per million tokens, from a per-token price. */
export const perMillion = (perToken) => usd(Number(perToken) * 1e6);

function dateFormat(options) {
  try {
    const f = new Intl.DateTimeFormat(undefined, options);
    f.format(new Date());
    return (d) => f.format(d);
  } catch {
    return (d) => d.toLocaleString();
  }
}

const dateTime = dateFormat({ dateStyle: "medium", timeStyle: "short" });
const timeOnly = dateFormat({ hour: "2-digit", minute: "2-digit", second: "2-digit" });
const dayFmt = dateFormat({ month: "short", day: "numeric" });

export const when = (secs) => (secs ? dateTime(new Date(secs * 1000)) : "—");
export const clock = (secs) => timeOnly(new Date(secs * 1000));
export const day = (date) => dayFmt(date);

let rtf = null;
try {
  rtf = new Intl.RelativeTimeFormat(undefined, { numeric: "auto" });
} catch {
  // Fall back to English below.
}

/** "in 3 days", "5 minutes ago". */
export function relative(secs) {
  if (!secs) return "—";
  const diff = secs - Date.now() / 1000;
  const abs = Math.abs(diff);
  let [unit, size] = ["second", 1];
  for (const [u, s] of [["day", 86400], ["hour", 3600], ["minute", 60]]) {
    if (abs >= s) {
      [unit, size] = [u, s];
      break;
    }
  }
  const n = Math.round(diff / size);
  if (rtf) return rtf.format(n, unit);
  const words = `${Math.abs(n)} ${unit}${Math.abs(n) === 1 ? "" : "s"}`;
  return n >= 0 ? `in ${words}` : `${words} ago`;
}

/** "86400s" → "1d"; LiteLLM-style durations for display and form fields. */
export function duration(v) {
  if (!v) return "";
  const secs = parseInt(v, 10);
  if (Number.isNaN(secs)) return v;
  for (const [unit, size] of [["d", 86400], ["h", 3600], ["m", 60]]) {
    if (secs % size === 0 && secs >= size) return `${secs / size}${unit}`;
  }
  return `${secs}s`;
}

export const ms = (v) => (v === null || v === undefined ? "—" : v < 1000 ? `${Math.round(v)} ms` : `${(v / 1000).toFixed(2)} s`);
