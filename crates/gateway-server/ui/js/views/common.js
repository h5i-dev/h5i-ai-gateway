// Pieces several pages share.

import { h, status, table } from "../dom.js";
import * as fmt from "../format.js";

export function pageHead(title, sub, ...actions) {
  return h("header", { class: "page-head" }, h("h1", null, title), ...actions, sub && h("p", { class: "sub" }, sub));
}

const now = () => Date.now() / 1000;

/** A key's state, with the reason it cannot be used if there is one. */
export function keyStatus(k) {
  if (k.blocked) return status("critical", "Blocked");
  if (k.expires !== null && k.expires <= now()) return status("critical", "Expired");
  if (k.max_budget !== null && k.spend + k.reserved_spend >= k.max_budget) return status("serious", "Budget used");
  return status("good", "Active");
}

export function teamStatus(t) {
  if (t.blocked) return status("critical", "Blocked");
  if (t.max_budget !== null && t.spend + t.reserved_spend >= t.max_budget) return status("serious", "Budget used");
  return status("good", "Active");
}

/** The models a key or team may call: chips, or "All models". */
export function modelChips(models) {
  if (!models || !models.length) return h("span", { class: "chip" }, "All models");
  return h("div", { class: "chips" }, models.map((m) => h("span", { class: "chip" }, m)));
}

/**
 * A set of model checkboxes with an "All models" switch.
 * `value()` is [] for all models (what the API takes to mean every model).
 */
export function modelPicker(available, selected = []) {
  const all = h("input", { type: "checkbox", checked: selected.length === 0 });
  const names = [...new Set([...available, ...selected])].sort();
  const boxes = names.map((m) => ({ m, box: h("input", { type: "checkbox", value: m, checked: selected.includes(m) }) }));
  const list = h("div", { class: "model-picks", role: "group", "aria-label": "Models" },
    boxes.length ? boxes.map(({ m, box }) => h("label", { class: "check" }, box, m)) : h("span", { class: "help" }, "No models configured."));
  const sync = () => {
    list.setAttribute("aria-disabled", String(all.checked));
    for (const { box } of boxes) box.toggleAttribute("disabled", all.checked);
  };
  all.addEventListener("change", sync);
  sync();
  const el = h("fieldset", { class: "field wide" },
    h("legend", { class: "visually-hidden" }, "Models"),
    h("label", { class: "check" }, all, "All models (including ones added later)"),
    list);
  return {
    el,
    value: () => (all.checked ? [] : boxes.filter(({ box }) => box.checked).map(({ m }) => m)),
  };
}

/** A number input's value: null when empty (no limit). */
export function numberOrNull(input) {
  const v = input.value.trim();
  if (v === "") return null;
  const n = Number(v);
  if (!Number.isFinite(n) || n < 0) throw Object.assign(new Error(`${input.dataset.name || "A field"} must be a non-negative number.`), { type: "invalid_input" });
  return n;
}

/** Duration fields take LiteLLM's forms: 30s, 15m, 12h, 30d, 2w, 1mo. */
export function durationOrNull(input) {
  const v = input.value.trim();
  if (v === "") return null;
  if (!/^\d+\s*(s|m|h|d|w|mo)$/.test(v)) throw Object.assign(new Error(`${input.dataset.name || "Duration"} must look like 30s, 15m, 12h, 30d, 2w or 1mo.`), { type: "invalid_input" });
  return v.replace(/\s+/g, "");
}

export const keyLabel = (id) => (id === "0" || id === 0 ? "master key" : `#${id}`);

export function logStatus(l) {
  if (l.status === "success") return status("good", "Success");
  if (l.status === "expired") return status("warning", "Expired");
  return status("critical", l.retryable_failure ? "Failed (retried)" : "Failed");
}

/** Spend logs as a table, newest first. */
export function spendLogTable(logs, { caption, empty } = {}) {
  return table(
    [
      { label: "Time", class: "nowrap", cell: (l) => fmt.when(l.endTime) },
      { label: "Key", class: "nowrap", cell: (l) => keyLabel(l.api_key) },
      { label: "Team", cell: (l) => (l.team_id ? `#${l.team_id}` : "—") },
      { label: "Model", cell: (l) => h("span", null, l.model_group ?? `group ${l.model_group_id}`, l.model && h("span", { class: "sub" }, l.model)) },
      { label: "Tokens in / out", num: true, cell: (l) => `${fmt.int(l.prompt_tokens)} / ${fmt.int(l.completion_tokens)}` },
      { label: "Spend", num: true, cell: (l) => fmt.usd(l.spend) },
      { label: "Status", cell: logStatus },
    ],
    logs,
    { caption, empty: empty ?? "No spend logs yet. Calls appear here once they settle." },
  );
}
