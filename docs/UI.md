# Admin UI

Open `http://localhost:4000/ui` and sign in with the master key or a virtual
key. The console is plain HTML, CSS and JavaScript modules in
`crates/gateway-server/ui/`, embedded in the binary: no build step, and
nothing is loaded from anywhere but the gateway, so it works offline. It
has no privileges of its own: the key you sign in with (kept in the tab's
`sessionStorage`) goes in `Authorization` on every management call, and the
kernel decides what it may see and do.

- **Dashboard**: global spend, reserved spend and in-flight calls; every
  deployment with its prices, limits, order and health (cooling down or not);
  the latest calls.
- **Keys**: list with spend against budget, create (the new key is shown
  once, with a copy button), edit models, budget, budget period, RPM/TPM,
  parallel limit and validity, block and unblock, reset spend, delete.
- **Teams**: the same for teams, with their key counts.
- **Spend**: `/spend/logs` filtered by time range, key, team, model group
  and status, with totals and spend per day, per key and per model group
  (each chart has a table view; selecting a bar filters by it).
- **Playground**: chat with any model the key may call, streaming or not,
  with latency, time to first token, tokens, the deployment and
  `x-litellm-response-cost`.

A key that is not an admin sees only its own limits and spend, the models it
may call, and the playground. Light and dark themes follow the system or a
toggle. `/ui/assets/{version}/…` URLs carry a hash of the assets and are cached
for a year; `/ui` and the console's own routes (`/ui/keys`, …) are never cached.

| Dashboard | Spend (dark) | Playground |
|---|---|---|
| ![Dashboard](ui/dashboard.png) | ![Spend](ui/spend-dark.png) | ![Playground](ui/playground.png) |
