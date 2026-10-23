// Global spend, the deployments and their health, and the latest calls.

import { api } from "../api.js";
import { busy, errorBox, h, icon, infoBox, mount, status, table } from "../dom.js";
import * as fmt from "../format.js";
import { pageHead, spendLogTable } from "./common.js";

const REFRESH_MS = 15000;

function tile(label, value, note, hero) {
  return h("div", { class: ["tile", hero && "hero"] }, h("div", { class: "label" }, label), h("div", { class: "value" }, value), note && h("div", { class: "note" }, note));
}

function health(info) {
  if (!info.enabled) return status("warning", "Disabled");
  if (info.cooling_down) return status("critical", `Cooling down until ${fmt.clock(info.cooldown_until)}`);
  return status("good", "Healthy");
}

function modelsTable(models) {
  const rows = [...models].sort((a, b) => (a.model_name ?? "").localeCompare(b.model_name ?? "") || (a.model_info.order ?? 0) - (b.model_info.order ?? 0));
  return table(
    [
      { label: "Model group", cell: (m) => h("strong", null, m.model_name ?? "—") },
      { label: "Deployment", cell: (m) => h("span", null, h("code", null, m.litellm_params?.model ?? "—"), h("span", { class: "sub" }, m.litellm_params?.api_base ?? `id ${m.model_info.id}`)) },
      { label: "Order", num: true, cell: (m) => (m.model_info.order >= 4294967295 ? "—" : m.model_info.order) },
      { label: "Input / 1M tok", num: true, cell: (m) => fmt.perMillion(m.model_info.input_cost_per_token) },
      { label: "Output / 1M tok", num: true, cell: (m) => fmt.perMillion(m.model_info.output_cost_per_token) },
      { label: "RPM / TPM", num: true, cell: (m) => `${fmt.limit(m.model_info.rpm)} / ${fmt.limit(m.model_info.tpm)}` },
      { label: "Health", cell: (m) => health(m.model_info) },
    ],
    rows,
    { caption: "Deployments are tried by order, then the least busy. Credentials are never shown.", empty: "No deployments configured." },
  );
}

export function dashboardView(main, { onCleanup }) {
  const refresh = h("button", { type: "button", class: "small" }, icon("refresh"), "Refresh");
  const body = h("div", { class: "stack" }, h("p", { class: "placeholder" }, "Loading…"));
  mount(main, pageHead("Dashboard", "Spend across every key, the configured deployments, and the latest calls. Refreshes every 15 seconds.", refresh), body);

  async function load() {
    const [global, models, keys, teams, logs] = await Promise.allSettled([
      api("/global/spend"),
      api("/model/info"),
      api("/key/list"),
      api("/team/list"),
      api("/spend/logs", { query: { limit: 10 } }),
    ]);
    const firstError = [global, models, keys, teams].find((r) => r.status === "rejected");
    const g = global.value ?? {};
    const nodes = [];
    if (firstError) nodes.push(errorBox(firstError.reason));
    const keyList = keys.value?.keys ?? [];
    const blocked = keyList.filter((k) => k.blocked).length;
    const deps = models.value?.data ?? [];
    const cooling = deps.filter((d) => d.model_info.cooling_down).length;
    nodes.push(
      h("div", { class: "tiles" },
        tile("Total spend", fmt.usd(g.spend), "charged to virtual keys", true),
        tile("Reserved spend", fmt.usd(g.reserved_spend), "held by calls in flight"),
        tile("In-flight calls", fmt.int(g.in_flight), "admitted, not yet settled"),
        tile("Virtual keys", fmt.int(keyList.length), blocked ? `${blocked} blocked` : "none blocked"),
        tile("Teams", fmt.int(teams.value?.length ?? 0)),
        tile("Deployments", fmt.int(deps.length), cooling ? `${cooling} cooling down` : "all healthy")),
    );
    nodes.push(h("section", { class: "card", "aria-labelledby": "models-h" }, h("div", { class: "card-head" }, h("h2", { id: "models-h" }, "Models and deployments")), modelsTable(deps)));
    const recent = h("section", { class: "card", "aria-labelledby": "recent-h" },
      h("div", { class: "card-head" }, h("h2", { id: "recent-h" }, "Recent calls"), h("a", { href: "/ui/spend", "data-link": "" }, "All spend logs →")));
    if (logs.status === "fulfilled") recent.append(spendLogTable(logs.value));
    else recent.append(logs.reason.status === 404 ? infoBox(logs.reason.message) : errorBox(logs.reason));
    nodes.push(recent);
    mount(body, ...nodes);
  }

  const run = () => busy(body, load).catch((e) => mount(body, errorBox(e)));
  refresh.addEventListener("click", run);
  run();
  const timer = setInterval(() => document.visibilityState === "visible" && run(), REFRESH_MS);
  onCleanup(() => clearInterval(timer));
}
