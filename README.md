# h5i-ai-gateway

An OpenAI-compatible LLM gateway: a Rust port of the
[LiteLLM proxy](https://github.com/BerriAI/litellm), built on
[h5i-app](https://crates.io/crates/h5i-app) 0.1.3 so that its control plane
(virtual keys, teams, model access, budgets, rate limits, routing, cooldowns
and spend accounting) is a pure Rust kernel extracted to Lean 4 and proven
against a specification.

```
client ──HTTP──▶ gateway-server (shell, trusted)
                   │  Admit ─────────▶ gateway-kernel (extracted to Lean, proven)
                   │  call provider ─▶ gateway-providers (OpenAI, Azure, Anthropic, Gemini, …)
                   │  Settle ────────▶ gateway-kernel ──▶ PostgreSQL rows + spend log (outbox)
```

## Layout

| Path | What it is |
|---|---|
| `kernel/` | `gateway-kernel`: every decision the gateway makes, in the Rust subset Aeneas translates |
| `proofs/` | Lean 4: `Spec.lean` (the specification to review) and the proofs about the extracted kernel |
| `crates/gateway-providers/` | provider adapters: OpenAI-compatible types, translation to each provider, streaming, pricing |
| `crates/gateway-server/` | `h5i-gateway`: the axum server, LiteLLM config, management API, PostgreSQL store, spend logs |
| `examples/config.yaml` | a LiteLLM-style configuration |
| `h5i-app.toml` | what `h5i app extract/check/prove/mutate` work on |

## How a request is decided

A completion is two kernel commands around one provider call.

1. **`Admit`** checks, in one SERIALIZABLE transaction, that the virtual key
   exists and is neither blocked nor expired, that its team (if any) is not
   blocked, that key and team may call the model, that the key's and team's
   RPM/TPM windows and the key's parallel-request limit have room, picks a
   deployment (lowest `order`, then least busy, then lowest id, among those
   that are enabled, not cooling down, not yet tried for this request, and
   under their own RPM/TPM), and **reserves the call's worst-case cost**
   (prompt estimate + `max_tokens` at the deployment's prices) against the
   key's and the team's budgets, on top of what they already spent and
   reserved.
2. The shell calls the provider outside any transaction.
3. **`Settle`** replaces the reservation with the cost of the tokens the
   provider reported, at the prices quoted at admission, charges key and
   team, counts the tokens, counts a retryable failure against the
   deployment (cooling it down after `allowed_fails` per minute), and emits
   a spend log. The store writes the spend log to h5i's outbox in the same
   transaction, so a log exists exactly when its charge commits.

On a retryable failure the shell admits again excluding the deployments
already tried (`num_retries`), then moves on to the configured `fallbacks`.
Reservations whose calls never settle are released by `Expire` after the
reservation TTL.

## What is proven

`proofs/Spec.lean` is the file to review: it restates the policy on lists and
natural numbers (prices, `Within`, `AdmitByKey`, `Best`, `IsAdmin`,
`KeyMayWrite`, `Inv`, `Honest`). The theorems are about the Rust code as
Aeneas translates it; `h5i app prove` extracts the kernel, builds the proofs
and gates them (no `sorry`, `native_decide` or axioms beyond `propext`,
`Classical.choice`, `Quot.sound`).

| Theorem | Statement |
|---|---|
| `Theorems.admit_sound` | an admitted call by a key satisfies the whole policy `AdmitByKey`: the key exists, is unblocked and unexpired; its team exists and is unblocked; key and team may call the model; key and team RPM/TPM and the key's parallel limit have room; the deployment is `Best` (eligible and preferred by no eligible one); the reserved amount is the worst-case `price`; and it fits within key and team budgets on top of spend (after any budget-period reset) and outstanding reservations |
| `Theorems.admit_complete` | conversely, every call the policy allows is admitted, on exactly that deployment, reserving exactly that amount (in reachable states, while ids remain) |
| `Theorems.budget_never_exceeded` | in every state reached by honest steps, every key's and team's spend plus outstanding reservations stays within its budget, however requests interleave. Honest excludes exactly two steps that can overrun a budget: a provider reporting more tokens than the call reserved, and an admin lowering a budget below what is spent |
| `Theorems.key_confined` | a key that is not an admin never changes any key's or team's limits, blocks, grants or roles; it writes only its own key's and team's spend, its own new reservations, usage counters, the id counter, deployment health and spend logs |
| `Theorems.authorized` | the same as a universal `H5iAppLib.WritesAuthorized` theorem over every actor, state and command |
| `Theorems.manage_needs_admin` | every management command succeeds only for the master key or an active admin key |
| `Theorems.reachable_inv` | every reachable state has unique ids per table, fresh ids, and teams for all keys' team references |
| `Theorems.settle_logged`, `emit_origin` | a settlement emits exactly one spend log, for its reservation, with the cost it charged; every spend log comes from a settlement or (at cost 0) an expiry |
| `Helpers.route_spec` | routing returns an eligible deployment no eligible deployment is preferred to, or none exactly when none is eligible |
| `Helpers.cost_spec`, … | each helper (saturating cost, budget check, windows, lookups, budget resets, cooldowns) agrees with its specification |
| `Commands.transition_total` | the kernel never panics, overflows or indexes out of bounds (for inputs whose vectors fit in memory) |
| `Apply.apply_spec`, `Storage.pg_stored`, `Storage.db_inv` | committing a write set computes `Spec.applyAll`, and PostgreSQL holds and loads back exactly that state (h5i-app's store theorem) |
| `ReadOnly.sound` | `Dump`, `KeyInfo`, `TeamInfo` and `ListModels` never write, so they may run without a write transaction |
| `Scenarios.*` | concrete runs of the extracted code: routing by priority, exclusion and cooldown, budgets counting reservations, rate-limit windows, settlement charging the actual cost once, refusals |

`h5i app mutate` injects twelve bugs listed in `h5i-app.toml` (budget
ignoring reservations, off-by-one rate limits, expiry, parallel and cooldown
thresholds, ignored cooldowns, ignored model grants, inverted routing,
charging the reservation instead of the cost, letting any key settle any
reservation, late budget resets); each must break a proof.

### What is trusted

The h5i-app framework's trusted base (`docs/app/TRUST.md` in h5i): the
engine runs each command in a SERIALIZABLE transaction, the tools (Charon,
Aeneas, Lean, rustc) and PostgreSQL. Beyond that, the shell in
`crates/gateway-server` and `crates/gateway-providers`:

- **Authentication.** The master key comparison and the HMAC verification of
  virtual keys (`h5i-app-token` parsing is itself verified) decide the
  `Principal`. The kernel trusts `master` and the key id it is given.
- **The clock.** Budgets, windows, expiry and cooldowns use the engine's
  clock (PostgreSQL's, monotonic per tenant).
- **Token counts.** Admission reserves an *estimate* of the prompt plus
  `max_tokens`; the gateway sets `max_tokens` when the client does not, so a
  provider that honours it stays within the reservation. Settlement charges
  what the provider reports. The budget theorem's honesty assumption is
  exactly that reported usage does not exceed the reservation. A provider
  that reports more (an underestimated prompt) is still charged in full, so
  spend can then pass the budget (this case is not covered by a theorem);
  the next admission sees the overrun and is refused.
- **Provider translation** (`gateway-providers`), the configuration loader,
  and the JSON decoding of requests. Every theorem holds for all commands,
  so a wrong decoding can only produce a command the caller could have sent.
- **Spend log delivery** from the outbox is at least once; a sink must drop
  repeats by the `Idempotency-Key` header.
- **Unsettled calls.** If the database is unreachable when a call settles,
  the reservation is released uncharged when it expires (logged as an error).

## Running

```sh
cargo build --release -p gateway-server
export LITELLM_MASTER_KEY=sk-1234 OPENAI_API_KEY=...
./target/release/h5i-gateway --config examples/config.yaml --port 4000   # target dir: see .cargo/config.toml

# a virtual key with a budget and a rate limit
curl -s localhost:4000/key/generate -H "Authorization: Bearer $LITELLM_MASTER_KEY" \
  -H 'content-type: application/json' -d '{"models":["gpt-4o"],"max_budget":10,"rpm_limit":60,"duration":"30d"}'

# any OpenAI SDK pointed at http://localhost:4000 works
curl -s localhost:4000/v1/chat/completions -H "Authorization: Bearer sk-v1...." \
  -H 'content-type: application/json' -d '{"model":"gpt-4o","messages":[{"role":"user","content":"Hello"}]}'
```

With `general_settings.database_url` (or `DATABASE_URL`) state lives in
PostgreSQL (schema `h5i_gateway`) and survives restarts; spend logs are
queued in h5i's outbox and delivered to `general_settings.spend_logs`
(`log`, or a webhook URL), and `/spend/logs` reads them back. Without a
database the gateway keeps its state in memory.

## Compatibility with LiteLLM

**Implemented:** the `config.yaml` format (`model_list` with `litellm_params`
and `model_info`, `os.environ/` secrets, `router_settings.num_retries`,
`allowed_fails`, `cooldown_time`, `timeout`, `fallbacks`,
`model_group_alias`, `general_settings.master_key`/`database_url`,
`environment_variables`); `/v1/chat/completions` (streaming included),
`/v1/embeddings`, `/v1/models`, Azure-style
`/openai/deployments/{model}/chat/completions`; virtual keys
(`/key/generate|update|delete|block|unblock|info|list|reset_spend`) with
`models`, `max_budget`, `budget_duration`, `rpm_limit`, `tpm_limit`,
`max_parallel_requests`, `duration`, `team_id`, `user_role: proxy_admin`;
teams (`/team/new|update|delete|block|unblock|info|list`) with shared budgets,
limits and model lists; `/model/info`, `/spend/logs`, `/global/spend`,
`/health/liveliness|readiness`; the `x-litellm-*` response headers; keys in
`Authorization`, `x-api-key`, `api-key` or `x-goog-api-key`; `mock_response`.
Providers: OpenAI and OpenAI-compatible (Azure, Groq, DeepSeek, Mistral,
Together, Fireworks, OpenRouter, xAI, Perplexity, DeepInfra, Cerebras, NVIDIA
NIM, SambaNova, vLLM, Ollama, LM Studio), Anthropic and Gemini (AI Studio),
with LiteLLM's price table vendored.

**Different by design:** budgets are enforced with reservations, so
concurrent requests cannot overspend (LiteLLM checks spend after the fact);
rate limits use fixed one-minute windows; routing is priority (`order`),
then least busy, then id (LiteLLM's `routing_strategy` setting is accepted
but not used); deployments come from the configuration file (no
`/model/new`); key, team and user ids are numbers; prompt-cache token prices
are not discounted.

**Not implemented:** Bedrock, Vertex AI and the other non-OpenAI-compatible
providers; `/v1/completions`, `/v1/messages`, images, audio, files, batches
and the Responses API; guardrails, caching, callbacks other than the spend
log webhook, SSO and the admin UI; users, organizations and budgets per
customer or per model.

## Tests

```sh
cargo test --workspace                                   # kernel, providers, server (in-memory)
docker run -d -p 127.0.0.1:55432:5432 -e POSTGRES_USER=h5i -e POSTGRES_PASSWORD=h5i postgres:17
H5I_APP_TEST_DATABASE_URL=postgres://h5i:h5i@127.0.0.1:55432/h5i cargo test -p gateway-server --test postgres
h5i app prove     # extract the kernel, build and gate the proofs
h5i app mutate    # every listed bug must break a proof
h5i app lint
```

The PostgreSQL tests run random commands through the PostgreSQL engine and
the in-memory executor and require identical replies, identical final
state and exactly the committed spend logs in the outbox, and fire 32
concurrent admissions at one budget to check that exactly the affordable
ones get through.

## License

Apache-2.0. `crates/gateway-providers/data/model_prices_and_context_window.json`
is from LiteLLM (MIT).
