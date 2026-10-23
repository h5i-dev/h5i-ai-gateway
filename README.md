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
                   │  call provider ─▶ gateway-providers (OpenAI, Azure, Anthropic, Gemini, Bedrock, Vertex AI, …)
                   │  Settle ────────▶ gateway-kernel ──▶ PostgreSQL rows + spend log (outbox)
```

## Layout

| Path | What it is |
|---|---|
| `kernel/` | `gateway-kernel`: every decision the gateway makes, in the Rust subset Aeneas translates |
| `proofs/` | Lean 4: `Spec.lean` (the specification to review) and the proofs about the extracted kernel |
| `crates/gateway-providers/` | provider adapters: OpenAI-compatible types, translation to each provider, streaming, pricing |
| `crates/gateway-server/` | `h5i-gateway`: the axum server, LiteLLM config, management API, PostgreSQL store, spend logs |
| `crates/gateway-server/ui/` | the admin console served at `/ui` (HTML, CSS, JavaScript modules; embedded in the binary) |
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
`KeyMayWrite`, `Inv`, `Honest`, and for the master key's group commit
`Batch`: `RunItems`, `BatchHonest`, `Keyed`, `Equiv`). The theorems are about the Rust code as
Aeneas translates it; `h5i app prove` extracts the kernel, builds the proofs
and gates them (no `sorry`, `native_decide` or axioms beyond `propext`,
`Classical.choice`, `Quot.sound`).

| Theorem | Statement |
|---|---|
| `Theorems.admit_sound` | an admitted call by a key satisfies the whole policy `AdmitByKey`: the key exists, is unblocked and unexpired; its team exists and is unblocked; key and team may call the model; key and team RPM/TPM and the key's parallel limit have room; the deployment is `Best` (eligible and preferred by no eligible one); the reserved amount is the worst-case `price`; and it fits within key and team budgets on top of spend (after any budget-period reset) and outstanding reservations |
| `Theorems.admit_complete` | conversely, every call the policy allows is admitted, on exactly that deployment, reserving exactly that amount (in reachable states, while ids remain) |
| `Theorems.budget_never_exceeded` | in every state reached by honest steps, every key's and team's spend plus outstanding reservations stays within its budget, however requests interleave. Honest excludes exactly two steps that can overrun a budget: a provider reporting more tokens than the call reserved, and an admin lowering a budget below what is spent. In a `Batch`, honesty (`BatchHonest`) asks it of every `Settle` item at the state in which that item runs (after the earlier items) |
| `Theorems.key_confined` | a key that is not an admin never changes any key's or team's limits, blocks, grants or roles; it writes only its own key's and team's spend, its own new reservations, usage counters, the id counter, deployment health and spend logs |
| `Theorems.authorized` | the same as a universal `H5iAppLib.WritesAuthorized` theorem over every actor, state and command |
| `Theorems.manage_needs_admin` | every management command succeeds only for the master key or an active admin key |
| `Theorems.reachable_inv` | every reachable state has unique ids per table, fresh ids, and teams for all keys' team references (`reachable_keyed`: every table, usage and grants included, has unique keys) |
| `Theorems.settle_logged`, `emit_origin` | a settlement emits exactly one spend log, for its reservation, with the cost it charged; every spend log comes from a settlement, (at cost 0) an expiry, or a batch's `Settle` item `i` that succeeded, for its reservation, with the cost of outcome `i` |
| `Theorems.batch_sequential` | a successful `Batch` (master key only) is exactly the sequential run of its items (`Spec.RunItems`): each item, as its own key, on the state the earlier successful items left, was refused (writing nothing) or succeeded with the outcome it reports; the batch commits `compactL` of the items' writes in order, which sends the same spend logs in the same order and, with unique keys per table, reaches the same rows up to their order in each table (`compact_equiv`, `Spec.Equiv`) |
| `Theorems.batch_complete`, `batch_admit_sound` | conversely, a master-key batch that fits in memory succeeds with exactly the run of its items; every `Admitted` outcome satisfies `AdmitByKey` (or `Best` for the master key) at the state its item ran in |
| `Helpers.route_spec` | routing returns an eligible deployment no eligible deployment is preferred to, or none exactly when none is eligible |
| `Helpers.cost_spec`, … | each helper (saturating cost, budget check, windows, lookups, budget resets, cooldowns) agrees with its specification |
| `Commands.transition_total` | the kernel never panics, overflows or indexes out of bounds (for inputs whose vectors fit in memory; for a batch, the snapshot's rows plus 8 per item fit in a vector) |
| `Apply.apply_spec`, `Storage.pg_stored`, `Storage.db_inv` | committing a write set computes `Spec.applyAll`, and PostgreSQL holds and loads back exactly that state (h5i-app's store theorem) |
| `ReadOnly.sound` | `Dump`, `KeyInfo`, `TeamInfo` and `ListModels` never write, so they may run without a write transaction |
| `Scenarios.*` | concrete runs of the extracted code: routing by priority, exclusion and cooldown, budgets counting reservations, rate-limit windows, settlement charging the actual cost once, refusals, a batch whose second admission is refused only because of the first one's reservation |

`h5i app mutate` injects fourteen bugs listed in `h5i-app.toml` (budget
ignoring reservations, off-by-one rate limits, expiry, parallel and cooldown
thresholds, ignored cooldowns, ignored model grants, inverted routing,
charging the reservation instead of the cost, letting any key settle any
reservation, late budget resets, batch items running on the original
state, compaction merging spend logs); each must break a proof.

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
  the next admission sees the overrun and is refused. Media deployments
  are priced per image, second of audio or character instead of per token
  (see *Images and audio* below); their reservations are upper bounds
  except where a provider reports more image tokens, or a longer duration,
  than the header or estimate allowed for.
- **Provider translation** (`gateway-providers`), the configuration loader,
  and the JSON decoding of requests. Every theorem holds for all commands,
  so a wrong decoding can only produce a command the caller could have sent.
- **Spend log delivery** from the outbox is at least once; a sink must drop
  repeats by the `Idempotency-Key` header.
- **Unsettled calls.** If the database is unreachable when a call settles,
  the reservation is released uncharged when it expires (logged as an error).
- **Guardrails** (`guardrails.rs`) and **the response cache** (`cache.rs`)
  are shell code outside the proofs. They decide nothing the kernel
  decides: a guardrail can only refuse a request or rewrite its content,
  and a cache hit still goes through `Admit` and `Settle` (at zero tokens),
  so access, blocks, rate limits and budgets hold for it as for any call.
  What is trusted is that they inspect and rewrite content correctly (a
  regex that misses a secret lets it through), and that a cached response
  is the one the provider gave for the same key material. Cached responses
  are shared across keys, as in LiteLLM.

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
database the gateway keeps its state in memory, and `/spend/logs` reads the
last 10,000 spend logs from memory.

## Admin UI

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
| ![Dashboard](docs/ui/dashboard.png) | ![Spend](docs/ui/spend-dark.png) | ![Playground](docs/ui/playground.png) |

## Compatibility with LiteLLM

**Implemented:** the `config.yaml` format (`model_list` with `litellm_params`
and `model_info`, `os.environ/` secrets, `router_settings.num_retries`,
`allowed_fails`, `cooldown_time`, `timeout`, `fallbacks`,
`model_group_alias`, `general_settings.master_key`/`database_url`,
`environment_variables`); `/v1/chat/completions` (streaming included),
`/v1/embeddings`, `/v1/models`, Azure-style
`/openai/deployments/{model}/chat/completions`; Anthropic's Messages API
and OpenAI's Responses API, bridged to chat completions for every provider
(see below); images and audio (below); virtual keys
(`/key/generate|update|delete|block|unblock|info|list|reset_spend`) with
`models`, `max_budget`, `budget_duration`, `rpm_limit`, `tpm_limit`,
`max_parallel_requests`, `duration`, `team_id`, `user_role: proxy_admin`;
teams (`/team/new|update|delete|block|unblock|info|list`) with shared budgets,
limits and model lists; `/model/info`, `/spend/logs` (filters `api_key`,
`team_id`, `model`, `status`, `start_date`, `end_date`, `limit`),
`/global/spend`, `/health/liveliness|readiness`; an admin UI at `/ui`; the
`x-litellm-*` response headers; keys in
`Authorization`, `x-api-key`, `api-key` or `x-goog-api-key`; `mock_response`.
Guardrails (the `guardrails:` list, `mode: pre_call|during_call|post_call`,
`default_on`, per-request `guardrails` / `metadata.guardrails`, the
`x-litellm-applied-guardrails` header; a block is a 400 of type
`guardrail_violation` naming the guardrail): `litellm_content_filter`
(`blocked_words`, regex and prebuilt `patterns` with `BLOCK`/`MASK`:
e-mail, phone, credit cards with a Luhn check, US SSN, IPv4/IPv6, AWS keys,
GitHub/Slack/OpenAI-style tokens, generic API keys, URLs), `presidio`
(analyzer and anonymizer APIs, `pii_entities_config`, score thresholds,
`output_parse_pii`, streaming included), `openai_moderation`, `lakera_v2`
(`block` or `monitor`) and `generic_guardrail_api` (`BLOCKED`, `NONE`,
`GUARDRAIL_INTERVENED` with rewritten texts, `extra_body` per request,
`unreachable_fallback`, `fail_on_error`). Caching (`litellm_settings.cache`
and `cache_params`: `type: local|redis`, `host`/`port`/`password`/`url`,
`ttl`, `namespace`, `max_size_in_memory`, `mode: default_off`,
`supported_call_types`) of chat completions (including the Messages and
Responses APIs, which run on the chat path) and embeddings, per-request
`cache: {no-cache, no-store, ttl, s-maxage, namespace, use-cache}`, a cached
chat replayed as a stream when `stream: true`, and the `x-litellm-cache-key`
and `x-litellm-cache-hit` headers.
Providers: OpenAI and OpenAI-compatible (Azure, Groq, DeepSeek, Mistral,
Together, Fireworks, OpenRouter, xAI, Perplexity, DeepInfra, Cerebras, NVIDIA
NIM, SambaNova, vLLM, Ollama, LM Studio), Anthropic, Gemini (AI Studio),
Amazon Bedrock (`bedrock/`: Converse and ConverseStream for every chat model,
including `bedrock/converse/`, region paths, cross-region inference profiles
such as `us.anthropic...` and ARNs; Titan and Cohere embeddings; SigV4 with
`aws_access_key_id`/`aws_secret_access_key`/`aws_session_token`/
`aws_region_name` or the `AWS_*` variables, or Bedrock API keys via
`api_key`/`AWS_BEARER_TOKEN_BEDROCK`; `aws_bedrock_runtime_endpoint`) and
Google Vertex AI (`vertex_ai/`: Gemini, Claude via `rawPredict` /
`streamRawPredict`, text embeddings; service-account or authorized-user
`vertex_credentials` / `GOOGLE_APPLICATION_CREDENTIALS` exchanged for cached
OAuth2 tokens, an access token in `api_key`, or the GCE metadata server;
`vertex_project`, `vertex_location` including `global`), with LiteLLM's price
table vendored.

**Different by design:** budgets are enforced with reservations, so
concurrent requests cannot overspend (LiteLLM checks spend after the fact);
rate limits use fixed one-minute windows; routing is priority (`order`),
then least busy, then id (LiteLLM's `routing_strategy` setting is accepted
but not used); deployments come from the configuration file (no
`/model/new`); key, team and user ids are numbers; prompt-cache token prices
are not discounted. A cache hit is admitted by the kernel and settled at
zero tokens (so it counts against RPM and needs model access, but costs
nothing). `post_call` guardrails on a stream run once on the accumulated
text when the upstream ends: the text has already been sent, so a block
ends the stream with an error event and `MASK` rewrites are not applied to
streams. `during_call` and `post_call` blocks come after the provider call,
which is charged. Guardrails apply to chat (and so to the APIs built on it)
and `pre_call` to embedding inputs.

**Anthropic Messages API** (`POST /v1/messages`, `/anthropic/v1/messages`,
`/v1/messages/count_tokens`), as LiteLLM's `/v1/messages`: the request is
translated to a chat completion, so any provider serves it and keys,
budgets, rate limits, routing, retries, fallbacks and spend work as for
`/v1/chat/completions`. Supported: `system` as a string or text blocks;
text, `image` (base64 or URL), `document` (base64, plain text, file id)
blocks; `tool_use`/`tool_result`; `tools` (custom tools; server tools such
as `web_search_20250305` pass through to Anthropic only); `tool_choice`
including `disable_parallel_tool_use`; `stop_sequences`, `temperature`,
`top_p`, `top_k`, `metadata.user_id`, `thinking` (forwarded to Anthropic
deployments; mapped to `reasoning_effort` for others), `cache_control`
(kept for Anthropic deployments, dropped for others), `stream`. Responses,
SSE events (`message_start`, `ping`, `content_block_start/delta/stop` with
`text_delta`, `thinking_delta`, `input_json_delta`, `message_delta` with
`stop_reason` and usage, `message_stop`, `error`) and errors
(`{"type": "error", "error": {...}}`) are in Anthropic's shape. Keys may be
sent as `x-api-key`. `count_tokens` returns the gateway's prompt estimate
(no tokenizer) and charges nothing. Not supported: `signature_delta` and
thinking signatures in streamed answers, citations, and server tools on
non-Anthropic deployments.

**OpenAI Responses API** (`POST /v1/responses`, `GET` and
`DELETE /v1/responses/{id}`), bridged to chat completions like LiteLLM's
responses-to-chat bridge: `input` as a string or items (messages with
`input_text`/`input_image`/`input_file`/`input_audio` parts, `function_call`,
`function_call_output`; `reasoning` items are dropped), `instructions`,
function `tools`, `tool_choice`, `max_output_tokens`, `temperature`,
`top_p`, `text.format` (`json_schema`, `json_object`), `reasoning.effort`,
`parallel_tool_calls`, `stream` (`response.created`, `response.in_progress`,
`response.output_item.added/done`, `response.content_part.added/done`,
`response.output_text.delta/done`, `response.function_call_arguments.delta/done`,
`response.reasoning_summary_*`, `response.completed`/`response.incomplete`,
`error`/`response.failed`, all with `sequence_number`s), `store` and
`previous_response_id`. Output items are `message` (`output_text`),
`function_call` and `reasoning` (as summary text). **Stored responses are
kept in memory** in the gateway process (lost on restart, not shared between
replicas), at most `H5I_RESPONSES_STORE_SIZE` of them (default 1000, least
recently used evicted), each visible only to the key that created it. Not
supported: hosted tools (web/file search, computer use, code interpreter,
MCP), `background`, `item_reference` inputs, `input_file.file_url`,
`/v1/responses/{id}/input_items`, conversations, and
`/v1/responses/{id}/cancel`.

**Not implemented:** the other non-OpenAI-compatible providers; Bedrock
InvokeModel chat (`bedrock/invoke/` is served through Converse), AWS
role/profile/web-identity credentials and the instance-metadata chain, Nova
and TwelveLabs embeddings, media given to Bedrock as `http(s)` URLs (send
base64 or `s3://`); Vertex AI workload-identity federation
(`external_account`), partner models other than Claude, Model Garden
endpoints; `/v1/completions`, files and batches; the other
guardrail integrations (Bedrock, Aporia, Azure, …), content filter
`categories` and `blocked_words_file`, LiteLLM's older
`litellm_settings.guardrails` format, and semantic, S3, disk and
Redis-cluster caches; callbacks other than the spend log webhook, and SSO;
users, organizations and budgets per customer or per model.

### Images and audio

| Endpoint | Providers |
|---|---|
| `POST /v1/images/generations` (`prompt, n, size, quality, style, response_format, background, output_format, user`, other fields passed through) | OpenAI (dall-e-2/3, gpt-image-*), Azure OpenAI, OpenAI-compatible providers that serve the endpoint (xAI, Together, …), Gemini AI Studio (Imagen via `:predict`; `gemini-*-image` via `:generateContent`) |
| `POST /v1/images/edits` (multipart `image`/`image[]`, `mask`, `prompt`, `n`, `size`, …) | OpenAI, Azure OpenAI, OpenAI-compatible |
| `POST /v1/audio/transcriptions`, `/v1/audio/translations` (multipart `file, model, language, prompt, response_format, temperature, timestamp_granularities[]`, …) | OpenAI (whisper-1, gpt-4o-transcribe, …), Azure OpenAI, Groq and other OpenAI-compatible servers; `text`/`srt`/`vtt` pass through with the upstream's content type |
| `POST /v1/audio/speech` (`model, input, voice, response_format, speed, instructions`) | OpenAI, Azure OpenAI, OpenAI-compatible; the audio is streamed back with its content type |

Each is also served without `/v1` and as Azure's
`/openai/deployments/{model}/...`; uploads are limited to 64 MiB;
`mock_response` (request field, form field or `litellm_params`) answers
offline (`n` copies of the given image URL, the given transcript, or a
short silent WAV) and honours LiteLLM's error triggers. A deployment serves
a media endpoint when its mode (`model_info.mode`, else LiteLLM's table,
else implied by its own media prices) matches; a chat deployment is
refused.

**Units and prices.** The kernel charges `prompt_units * input_cost +
completion_units * output_cost`, so a media deployment's prices are per
media unit, taken from LiteLLM's table or the deployment's own
`litellm_params`/`model_info` (`output_cost_per_image`,
`input_cost_per_image`, `input_cost_per_pixel`,
`output_cost_per_image_token`, `input_cost_per_image_token`,
`input_cost_per_second`, `output_cost_per_second`,
`input_cost_per_character`, `input_cost_per_audio_token`,
`input_cost_per_token`, `output_cost_per_token`); the module docs of
`crates/gateway-server/src/media/pricing.rs` give the details.

- *Per-image models* (DALL-E, Imagen): a completion unit is a thousandth
  of the deployment's most expensive size/quality variant
  (`hd/1024-x-1792/dall-e-3`, Azure's per-pixel prices, or a flat
  `output_cost_per_image`); an image costing `p` is `ceil(p / unit)` units.
  Admission reserves `n` images at the dearest variant the request's `size`
  and `quality` allow (every variant for `auto`; DALL-E 3 defaults to
  standard 1024x1024); settlement counts the images returned at the variant
  generated. Rounding overcharges by under 0.1% of the top price per image.
  OpenAI's DALL-E prices, no longer in the vendored table, are built in.
- *Token-priced image models* (gpt-image, Gemini image models): completion
  units are output image tokens, prompt units text tokens. The reported
  usage is charged (input image tokens and output text/thinking tokens
  converted at their price ratios); without usage, the table's per-image
  variant price. The reservation is the prompt's UTF-8 length, 8,000 image
  tokens per uploaded image, and per output image the larger of the
  variant price in tokens and OpenAI's token counts for the size and
  quality (Gemini: 1,400, or 2,600 above 2K, plus 2,048 text tokens).
- *Transcription*: a prompt unit is a second of audio at the per-second
  price (`output_cost_per_second` if set, else `input_cost_per_second`, as
  LiteLLM). The reservation is the upload's duration read from its
  container (WAV, FLAC, MP4/M4A, Ogg, MP3 Xing/VBRI headers; for other MP3s
  the format's lowest bitrate, and for unknown formats 6 kbps, as bounds);
  settlement uses the provider's reported duration (`duration`,
  `usage.seconds`), else the container's, else the last subtitle cue,
  rounded up to whole seconds. Models reporting token usage
  (gpt-4o-transcribe) are charged it, converted to seconds-units, with
  output tokens as completion units.
- *Speech*: a prompt unit is an input character at
  `input_cost_per_character`; the cost is known before the call, so the
  reservation is exact. Token-priced TTS (gpt-4o-mini-tts) is charged its
  estimated input tokens (characters / 4), like LiteLLM.

Media units also count towards TPM limits. A model group should hold one
kind of deployment; a mixed group reserves the largest of each
deployment's own reservation. Not implemented: streamed transcriptions
(`stream: true`), Gemini image edits, Gemini/Vertex speech and
transcription, image variations, and pricing of the audio output of
token-priced TTS models.

## Tests

```sh
cargo test --workspace                                   # kernel, providers, server (in-memory)
docker run -d -p 127.0.0.1:55432:5432 -e POSTGRES_USER=h5i -e POSTGRES_PASSWORD=h5i postgres:17
H5I_APP_TEST_DATABASE_URL=postgres://h5i:h5i@127.0.0.1:55432/h5i cargo test -p gateway-server --test postgres
docker run -d --rm -p 127.0.0.1:56379:6379 redis:7
H5I_GATEWAY_TEST_REDIS_URL=redis://127.0.0.1:56379/ cargo test -p gateway-server --test guardrails_cache redis
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
is from LiteLLM (MIT). `crates/gateway-providers/tests/fixtures/eventstream/`
is from `aws-smithy-eventstream` (Apache-2.0).
