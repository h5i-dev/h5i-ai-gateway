// What a key that is not an admin may see: its own limits and spend, and
// the models it can call.

import { api } from "../api.js";
import { meter } from "../charts.js";
import { busy, errorBox, h, icon, mount } from "../dom.js";
import * as fmt from "../format.js";
import { keyStatus, modelChips, pageHead } from "./common.js";

export function accountView(main) {
  const refresh = h("button", { type: "button", class: "small" }, icon("refresh"), "Refresh");
  const body = h("div", { class: "grid two" }, h("p", { class: "placeholder" }, "Loading…"));
  mount(main, pageHead("My key", "Your key's limits and spend. Ask an administrator to change them.", refresh), body);

  const row = (k, v) => [h("dt", null, k), h("dd", null, v)];

  async function load() {
    const [info, models] = await Promise.all([api("/key/info"), api("/v1/models")]);
    const k = info.info;
    mount(body,
      h("section", { class: "card", "aria-labelledby": "key-h" },
        h("div", { class: "card-head" }, h("h2", { id: "key-h" }, `Key #${k.token_id}`), keyStatus(k)),
        h("dl", { class: "kv" },
          row("Spend", meter(k.spend, k.max_budget, fmt.usd)),
          row("Reserved", fmt.usd(k.reserved_spend)),
          row("Budget period", k.budget_duration ? `every ${fmt.duration(k.budget_duration)}, next reset ${fmt.relative(k.budget_reset_at)}` : "never resets"),
          row("Requests per minute", fmt.limit(k.rpm_limit)),
          row("Tokens per minute", fmt.limit(k.tpm_limit)),
          row("Parallel requests", fmt.limit(k.max_parallel_requests)),
          row("Team", k.team_id ? `#${k.team_id}` : "none"),
          row("Expires", k.expires ? `${fmt.when(k.expires)} (${fmt.relative(k.expires)})` : "never"),
          row("Allowed models", modelChips(k.models)))),
      h("section", { class: "card", "aria-labelledby": "models-h" },
        h("div", { class: "card-head" }, h("h2", { id: "models-h" }, "Models you can call"), h("a", { href: "/ui/playground", "data-link": "" }, "Try one →")),
        models.data.length
          ? h("ul", { class: "chips" }, models.data.map((m) => h("li", { class: "chip" }, m.id)))
          : h("p", { class: "empty" }, "This key may not call any configured model.")));
  }

  const run = () => busy(body, load).catch((err) => mount(body, errorBox(err)));
  refresh.addEventListener("click", run);
  run();
}
