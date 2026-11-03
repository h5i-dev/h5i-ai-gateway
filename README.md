# h5i-ai-gateway

An OpenAI-compatible LLM gateway: a Rust port of the
[LiteLLM proxy](https://github.com/BerriAI/litellm) on
[h5i-app](https://crates.io/crates/h5i-app-core) 0.1.3. Virtual keys, teams,
budgets, rate limits, routing and spend are decided by a pure Rust kernel
that is extracted to Lean 4 and proven. HTTP, provider calls and the
configuration file are ordinary Rust around it.

## Run

```bash
export LITELLM_MASTER_KEY=sk-1234 OPENAI_API_KEY=...
cargo run --release -p gateway-server -- --config examples/config.yaml --port 4000
```

`--config` takes a LiteLLM `config.yaml`. Without a database the gateway
keeps its state in memory. To keep keys, budgets and spend across restarts,
set `general_settings.database_url` (or `DATABASE_URL`) to PostgreSQL:

```bash
docker run -d -p 127.0.0.1:55432:5432 -e POSTGRES_USER=h5i -e POSTGRES_PASSWORD=h5i postgres:17
export DATABASE_URL=postgres://h5i:h5i@127.0.0.1:55432/h5i
```

## Deploy on Vercel

The whole gateway runs as one Rust function (`api/gateway.rs`, after
Vercel's [Rust Axum template](https://vercel.com/templates/other/rust-axum));
`vercel.json` routes every path to it.

```bash
vercel link
vercel env add LITELLM_MASTER_KEY
vercel env add OPENAI_API_KEY
vercel env add DATABASE_URL      # PostgreSQL, e.g. Neon; strongly recommended
vercel deploy --prod
```

The models come from `vercel/config.yaml`, built into the function; set
`LITELLM_CONFIG_YAML` to a whole `config.yaml` to replace it without a
rebuild. Without `DATABASE_URL`, keys and spend live in one function
instance's memory: they are lost on a cold start and not shared between
instances.

## Use

Create a virtual key, then call any model it may use with an OpenAI SDK or
curl:

```bash
curl -s localhost:4000/key/generate -H "Authorization: Bearer $LITELLM_MASTER_KEY" \
  -H 'content-type: application/json' \
  -d '{"models":["gpt-4o"],"max_budget":10,"rpm_limit":60,"duration":"30d"}'

curl -s localhost:4000/v1/chat/completions -H "Authorization: Bearer sk-v1...." \
  -H 'content-type: application/json' \
  -d '{"model":"gpt-4o","messages":[{"role":"user","content":"Hello"}]}'
```

The admin console is at <http://localhost:4000/ui> ([UI notes](docs/UI.md)).

Supported: chat, embeddings, Anthropic's `/v1/messages`, OpenAI's
`/v1/responses`, images and audio; OpenAI and its compatible providers,
Azure, Anthropic, Gemini, Bedrock and Vertex AI; keys, teams, budgets, rate
limits, fallbacks, guardrails and caching. Details and differences from
LiteLLM are in the [compatibility notes](docs/COMPATIBILITY.md).

## How it decides

Each call is two kernel commands around the provider call. `Admit` checks the
key, its team, model access and rate limits, picks a deployment, and reserves
the call's worst-case cost against the key's and team's budgets. `Settle`
charges the actual cost and writes a spend log. With PostgreSQL both run in
SERIALIZABLE transactions, so concurrent requests cannot overspend a budget.
See the [design notes](docs/DESIGN.md).

## Verification

```bash
cargo test --workspace
h5i app prove
h5i app mutate
h5i app lint
h5i test --target http://127.0.0.1:4000   # attack flows in .h5i-tests/, against a running gateway
```

Proof extraction needs Charon, Aeneas, and Lean 4.31.0 (`h5i app doctor`).
The PostgreSQL and Redis tests run when `H5I_APP_TEST_DATABASE_URL` and
`H5I_GATEWAY_TEST_REDIS_URL` are set ([test commands](docs/PROOFS.md#tests)).

`.h5i-tests/` holds security regression tests: the kernel's authorization
properties as HTTP attacks, and ports of the Nuclei templates for LiteLLM's
own CVEs ([how to run them](.h5i-tests/README.md)). CI runs them, and the
workspace tests, on every pull request.

Lean proves, among other things, that an admitted call satisfies the whole
admission policy and every allowed call is admitted, that no key or team
spends past its budget, and that a key without admin rights cannot change
any limits. The proofs assume a provider never reports more tokens than the
call reserved; HTTP, authentication, the clock and provider translation are
trusted. See the [proof notes](docs/PROOFS.md).

## Performance

Against LiteLLM's Python proxy, same mock upstream, gateway on 8 CPUs, 64
connections, upstream answering immediately (2026-10-23):

| Scenario | h5i-gateway | LiteLLM 1.106.2 |
|---|---:|---:|
| Chat, no database | 33,200 req/s | 801 req/s |
| Streaming | 11,208 req/s | 277 req/s |
| Chat with PostgreSQL and a virtual key | 1,389 req/s | 480 req/s |
| Memory | 68 MB | 4.4 GB |

The PostgreSQL row uses a database on the host network. The two do different
work there: h5i-gateway commits every reservation and charge in a
transaction, and LiteLLM writes spend in batches every 60 s. Reproduce with
`bench/run.sh`; see the [benchmark report](bench/README.md).

## Code

- `kernel/`: the gateway's decisions; `proofs/`: generated Lean and theorems.
- `crates/gateway-server/`: HTTP, config, management API, PostgreSQL, admin UI.
- `crates/gateway-providers/`: provider adapters, streaming, pricing.
- `crates/gateway-bench/` and `bench/`: the benchmark.

## License

Apache-2.0. `crates/gateway-providers/data/model_prices_and_context_window.json`
is from LiteLLM (MIT). `crates/gateway-providers/tests/fixtures/eventstream/`
is from `aws-smithy-eventstream` (Apache-2.0).
