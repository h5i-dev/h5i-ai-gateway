// Virtual keys: list, create (the key is shown once), edit, block, reset
// spend and delete.

import { api, post } from "../api.js";
import { meter } from "../charts.js";
import { busy, confirm, copyButton, dialog, errorBox, field, h, icon, mount, table, toast } from "../dom.js";
import * as fmt from "../format.js";
import { durationOrNull, keyStatus, modelChips, modelPicker, numberOrNull, pageHead } from "./common.js";

function numberInput(name, value, step = "1") {
  return h("input", { type: "number", min: "0", step, inputmode: "decimal", placeholder: "No limit", value: value ?? "", "data-name": name });
}

/** The key form, for creating (no `key`) or editing. Resolves with the API's answer, or undefined. */
function keyForm({ key, models, teams }) {
  const editing = Boolean(key);
  return dialog(editing ? `Edit key #${key.token_id}` : "Create a virtual key", (close, heading) => {
    const picker = modelPicker(models, key?.models ?? []);
    const budget = numberInput("Max budget", key?.max_budget, "any");
    const budgetDuration = h("input", { type: "text", placeholder: "Never resets", value: fmt.duration(key?.budget_duration), "data-name": "Budget period" });
    const rpm = numberInput("RPM limit", key?.rpm_limit);
    const tpm = numberInput("TPM limit", key?.tpm_limit);
    const parallel = numberInput("Max parallel requests", key?.max_parallel_requests);
    const duration = h("input", { type: "text", placeholder: editing ? "Keep current expiry" : "Never expires", "data-name": "Valid for" });
    const team = h("select", null, h("option", { value: "" }, "No team"), teams.map((t) => h("option", { value: t.team_id }, `Team #${t.team_id}`)));
    const admin = h("input", { type: "checkbox" });
    const errors = h("div");
    const submit = h("button", { type: "submit", class: "primary" }, editing ? "Save changes" : "Create key");
    const form = h("form", { method: "dialog", novalidate: true },
      heading,
      errors,
      h("div", { class: "form-grid" },
        picker.el,
        field("Max budget (USD)", budget, "Spend plus reserved calls may not exceed it."),
        field("Budget period", budgetDuration, "Spend resets every period: 1d, 7d, 1mo…"),
        field("RPM limit", rpm, "Requests per minute"),
        field("TPM limit", tpm, "Tokens per minute"),
        field("Max parallel requests", parallel),
        field(editing ? "Extend validity" : "Valid for", duration, editing ? "From now: 30d, 12h… Empty keeps the expiry." : "30d, 12h… Empty for no expiry."),
        !editing && field("Team", team, "Team budgets and model lists apply as well."),
        !editing && h("label", { class: "check wide" }, admin, "Admin key (proxy_admin): may manage keys, teams and spend")),
      h("div", { class: "dialog-actions" }, h("button", { type: "button", onclick: () => close() }, "Cancel"), submit));
    form.addEventListener("submit", async (e) => {
      e.preventDefault();
      mount(errors);
      submit.disabled = true;
      try {
        const body = {
          models: picker.value(),
          max_budget: numberOrNull(budget),
          rpm_limit: numberOrNull(rpm),
          tpm_limit: numberOrNull(tpm),
          max_parallel_requests: numberOrNull(parallel),
        };
        const period = durationOrNull(budgetDuration);
        const valid = durationOrNull(duration);
        if (period) body.budget_duration = period;
        else if (editing && key.budget_duration) body.budget_duration = "0s";
        if (valid) body.duration = valid;
        let result;
        if (editing) {
          result = await post("/key/update", { key: key.token_id, ...body });
        } else {
          for (const k of ["max_budget", "rpm_limit", "tpm_limit", "max_parallel_requests"]) if (body[k] === null) delete body[k];
          if (team.value) body.team_id = team.value;
          if (admin.checked) body.user_role = "proxy_admin";
          result = await post("/key/generate", body);
        }
        close(result);
      } catch (err) {
        mount(errors, errorBox(err));
        submit.disabled = false;
      }
    });
    return form;
  });
}

function showNewKey(result) {
  return dialog("Your new key", (close, heading) =>
    h("div", { class: "dialog-body" },
      heading,
      h("div", { class: "alert info", role: "note" }, h("div", null, "Copy this key now. It is not stored and cannot be shown again; if it is lost, delete it and create another.")),
      h("div", { class: "secret" }, h("code", null, result.key), copyButton(result.key)),
      h("dl", { class: "kv" }, h("dt", null, "Key id"), h("dd", null, `#${result.token_id}`), h("dt", null, "Expires"), h("dd", null, result.expires ? fmt.when(result.expires) : "Never")),
      h("div", { class: "dialog-actions" }, h("button", { type: "button", class: "primary", onclick: () => close() }, "Done"))));
}

export function keysView(main) {
  const search = h("input", { type: "search", placeholder: "Filter by id, team, model or role", "aria-label": "Filter keys" });
  const create = h("button", { type: "button", class: "primary" }, "Create key");
  const refresh = h("button", { type: "button", class: "small" }, icon("refresh"), "Refresh");
  const errors = h("div", { "aria-live": "polite" });
  const body = h("div", null, h("p", { class: "placeholder" }, "Loading…"));
  mount(main, pageHead("Virtual keys", "Each key has its own budget, rate limits and model list; a team's limits apply on top.", refresh, create), errors, h("div", { class: "filters" }, h("div", { class: "field search" }, search)), body);

  let keys = [];
  let models = [];
  let teams = [];

  const act = async (fn, done) => {
    mount(errors);
    try {
      await fn();
      if (done) toast(done);
      await reload();
    } catch (err) {
      mount(errors, errorBox(err));
    }
  };

  function draw() {
    const q = search.value.trim().toLowerCase();
    const rows = keys.filter((k) => !q || [k.token_id, k.team_id && `team ${k.team_id}`, k.user_role, ...(k.models.length ? k.models : ["all models"])].some((v) => v && String(v).toLowerCase().includes(q)));
    mount(body, table(
      [
        { label: "Key", cell: (k) => h("span", null, h("strong", null, `#${k.token_id}`), h("span", { class: "sub" }, k.user_role === "proxy_admin" ? "admin" : "user")) },
        { label: "Team", cell: (k) => (k.team_id ? `#${k.team_id}` : "—") },
        { label: "Models", cell: (k) => modelChips(k.models) },
        { label: "Spend / budget", cell: (k) => h("div", null, meter(k.spend, k.max_budget, fmt.usd), k.reserved_spend > 0 && h("span", { class: "sub" }, `${fmt.usd(k.reserved_spend)} reserved`), k.budget_duration && h("span", { class: "sub" }, `resets every ${fmt.duration(k.budget_duration)}, next ${fmt.relative(k.budget_reset_at)}`)) },
        { label: "RPM / TPM / parallel", num: true, cell: (k) => `${fmt.limit(k.rpm_limit)} / ${fmt.limit(k.tpm_limit)} / ${fmt.limit(k.max_parallel_requests)}` },
        { label: "Expires", cell: (k) => (k.expires ? h("span", { title: fmt.when(k.expires) }, fmt.relative(k.expires)) : "Never") },
        { label: "Status", cell: keyStatus },
        {
          label: h("span", { class: "visually-hidden" }, "Actions"),
          class: "actions",
          cell: (k) => h("span", null,
            h("button", { type: "button", class: "small ghost", "aria-label": `Edit key #${k.token_id}`, onclick: async () => (await keyForm({ key: k, models, teams })) && (toast(`Key #${k.token_id} updated`), reload()) }, "Edit"),
            h("button", { type: "button", class: "small ghost", "aria-label": `${k.blocked ? "Unblock" : "Block"} key #${k.token_id}`, onclick: () => act(() => post(k.blocked ? "/key/unblock" : "/key/block", { key: k.token_id }), `Key #${k.token_id} ${k.blocked ? "unblocked" : "blocked"}`) }, k.blocked ? "Unblock" : "Block"),
            h("button", { type: "button", class: "small ghost", "aria-label": `Reset spend of key #${k.token_id}`, onclick: async () => (await confirm(`Reset the spend of key #${k.token_id}?`, `Its spend (${fmt.usd(k.spend)}) goes back to zero. Spend logs are kept.`, "Reset spend")) && act(() => post("/key/reset_spend", { key: k.token_id }), "Spend reset") }, "Reset spend"),
            h("button", { type: "button", class: "small ghost danger", "aria-label": `Delete key #${k.token_id}`, onclick: async () => (await confirm(`Delete key #${k.token_id}?`, "Clients using it will be refused at once. This cannot be undone.")) && act(() => post("/key/delete", { keys: [k.token_id] }), `Key #${k.token_id} deleted`) }, "Delete")),
        },
      ],
      rows,
      { caption: q ? `${rows.length} of ${fmt.plural(keys.length, "key")}` : fmt.plural(keys.length, "key"), empty: keys.length ? "No key matches the filter." : "No virtual keys yet. Create one to give a client access." },
    ));
  }

  async function reload() {
    await busy(body, async () => {
      const [k, m, t] = await Promise.all([api("/key/list"), api("/v1/models"), api("/team/list")]);
      keys = k.keys.sort((a, b) => Number(b.token_id) - Number(a.token_id));
      models = m.data.map((d) => d.id);
      teams = t;
      draw();
      mount(errors);
    });
  }

  search.addEventListener("input", draw);
  refresh.addEventListener("click", () => act(async () => {}));
  create.addEventListener("click", async () => {
    const result = await keyForm({ models, teams });
    if (result) {
      await showNewKey(result);
      reload();
    }
  });
  reload().catch((err) => mount(body, errorBox(err)));
}
