// Teams: shared budgets, rate limits and model lists over their keys.

import { api, post } from "../api.js";
import { meter } from "../charts.js";
import { busy, confirm, dialog, errorBox, field, h, icon, mount, table, toast } from "../dom.js";
import * as fmt from "../format.js";
import { durationOrNull, modelChips, modelPicker, numberOrNull, pageHead, teamStatus } from "./common.js";

function numberInput(name, value, step = "1") {
  return h("input", { type: "number", min: "0", step, inputmode: "decimal", placeholder: "No limit", value: value ?? "", "data-name": name });
}

function teamForm({ team, models }) {
  const editing = Boolean(team);
  return dialog(editing ? `Edit team #${team.team_id}` : "Create a team", (close, heading) => {
    const picker = modelPicker(models, team?.models ?? []);
    const budget = numberInput("Max budget", team?.max_budget, "any");
    const budgetDuration = h("input", { type: "text", placeholder: "Never resets", value: fmt.duration(team?.budget_duration), "data-name": "Budget period" });
    const rpm = numberInput("RPM limit", team?.rpm_limit);
    const tpm = numberInput("TPM limit", team?.tpm_limit);
    const errors = h("div");
    const submit = h("button", { type: "submit", class: "primary" }, editing ? "Save changes" : "Create team");
    const form = h("form", { method: "dialog", novalidate: true },
      heading,
      errors,
      h("div", { class: "form-grid" },
        picker.el,
        field("Max budget (USD)", budget, "Shared by every key of the team."),
        field("Budget period", budgetDuration, "Spend resets every period: 1d, 7d, 1mo…"),
        field("RPM limit", rpm, "Requests per minute, all keys together"),
        field("TPM limit", tpm, "Tokens per minute, all keys together")),
      h("div", { class: "dialog-actions" }, h("button", { type: "button", onclick: () => close() }, "Cancel"), submit));
    form.addEventListener("submit", async (e) => {
      e.preventDefault();
      mount(errors);
      submit.disabled = true;
      try {
        const body = { models: picker.value(), max_budget: numberOrNull(budget), rpm_limit: numberOrNull(rpm), tpm_limit: numberOrNull(tpm) };
        const period = durationOrNull(budgetDuration);
        if (period) body.budget_duration = period;
        else if (editing && team.budget_duration) body.budget_duration = "0s";
        let result;
        if (editing) {
          result = await post("/team/update", { team_id: team.team_id, ...body });
        } else {
          for (const k of ["max_budget", "rpm_limit", "tpm_limit"]) if (body[k] === null) delete body[k];
          result = await post("/team/new", body);
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

export function teamsView(main) {
  const create = h("button", { type: "button", class: "primary" }, "Create team");
  const refresh = h("button", { type: "button", class: "small" }, icon("refresh"), "Refresh");
  const errors = h("div", { "aria-live": "polite" });
  const body = h("div", null, h("p", { class: "placeholder" }, "Loading…"));
  mount(main, pageHead("Teams", "A key in a team must fit both its own limits and the team's. A team with keys cannot be deleted.", refresh, create), errors, body);

  let teams = [];
  let models = [];
  let keyCount = new Map();

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
    mount(body, table(
      [
        { label: "Team", cell: (t) => h("strong", null, `#${t.team_id}`) },
        { label: "Keys", num: true, cell: (t) => fmt.int(keyCount.get(t.team_id) ?? 0) },
        { label: "Models", cell: (t) => modelChips(t.models) },
        { label: "Spend / budget", cell: (t) => h("div", null, meter(t.spend, t.max_budget, fmt.usd), t.reserved_spend > 0 && h("span", { class: "sub" }, `${fmt.usd(t.reserved_spend)} reserved`), t.budget_duration && h("span", { class: "sub" }, `resets every ${fmt.duration(t.budget_duration)}, next ${fmt.relative(t.budget_reset_at)}`)) },
        { label: "RPM / TPM", num: true, cell: (t) => `${fmt.limit(t.rpm_limit)} / ${fmt.limit(t.tpm_limit)}` },
        { label: "Status", cell: teamStatus },
        {
          label: h("span", { class: "visually-hidden" }, "Actions"),
          class: "actions",
          cell: (t) => h("span", null,
            h("button", { type: "button", class: "small ghost", "aria-label": `Edit team #${t.team_id}`, onclick: async () => (await teamForm({ team: t, models })) && (toast(`Team #${t.team_id} updated`), reload()) }, "Edit"),
            h("button", { type: "button", class: "small ghost", "aria-label": `${t.blocked ? "Unblock" : "Block"} team #${t.team_id}`, onclick: () => act(() => post(t.blocked ? "/team/unblock" : "/team/block", { team_id: t.team_id }), `Team #${t.team_id} ${t.blocked ? "unblocked" : "blocked"}`) }, t.blocked ? "Unblock" : "Block"),
            h("button", { type: "button", class: "small ghost danger", "aria-label": `Delete team #${t.team_id}`, onclick: async () => (await confirm(`Delete team #${t.team_id}?`, "Only a team without keys can be deleted. This cannot be undone.")) && act(() => post("/team/delete", { team_ids: [t.team_id] }), `Team #${t.team_id} deleted`) }, "Delete")),
        },
      ],
      teams,
      { caption: fmt.plural(teams.length, "team"), empty: "No teams yet. A team shares one budget and model list across its keys." },
    ));
  }

  async function reload() {
    await busy(body, async () => {
      const [t, m, k] = await Promise.all([api("/team/list"), api("/v1/models"), api("/key/list")]);
      teams = t.sort((a, b) => Number(b.team_id) - Number(a.team_id));
      models = m.data.map((d) => d.id);
      keyCount = new Map();
      for (const key of k.keys) if (key.team_id) keyCount.set(key.team_id, (keyCount.get(key.team_id) ?? 0) + 1);
      draw();
      mount(errors);
    });
  }

  refresh.addEventListener("click", () => act(async () => {}));
  create.addEventListener("click", async () => {
    const result = await teamForm({ models });
    if (result) {
      toast(`Team #${result.team_id} created`);
      reload();
    }
  });
  reload().catch((err) => mount(body, errorBox(err)));
}
