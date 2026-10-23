# Proofs

What the Lean proofs in `proofs/` establish about the kernel, and what they leave to trusted code.

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
| `Frame.frame` | the read plans load enough: for every principal, snapshot and command with a plan, `transition` on `Snapshot.load plan s` (what the server loads) gives exactly the result, writes and reply or refusal, it gives on the whole tenant `s`. For `Admit`, `Settle`, `Expire`, `KeyInfo`, `TeamInfo` and `ListModels` this holds unconditionally (`frame_cmd`). For `Batch` (`batch_frame`) it needs that `s` keeps `Spec.Inv` (a new reservation's id is fresh) and fits in memory (`Commands.Fits`, as for `transition_total`); the proof follows the sequential run of the items: each runs on a state that differs from `s` only by earlier items' writes, every row an item writes is one the plan keeps (the reservation an admission inserts carries the item's key and team, the key and team rows it updates are the item key's), so each item runs on a slice of the full run's state and gives the same result |
| `Plan.reads_abs`, `Frame.load_for_sound` | the extracted `read_plan` computes the plans `Frame.frame` is about (`Plan.readsA`); end to end, rows holding what each read of the plan returns decode (`Schema.decode_load`) to a snapshot on which `transition` gives the same result as on `s` |
| `Scenarios.*` | concrete runs of the extracted code: routing by priority, exclusion and cooldown, budgets counting reservations, rate-limit windows, settlement charging the actual cost once, refusals, a batch whose second admission is refused only because of the first one's reservation |

`h5i app mutate` injects sixteen bugs listed in `h5i-app.toml` (budget
ignoring reservations, off-by-one rate limits, expiry, parallel and cooldown
thresholds, ignored cooldowns, ignored model grants, inverted routing,
charging the reservation instead of the cost, letting any key settle any
reservation, late budget resets, batch items running on the original
state, compaction merging spend logs, and a read plan that looks for the
reservations of a key's team in the wrong column or drops them, which would
let a team overspend); each must break a proof. The wrong-column plan is
rejected by the frame theorem itself: the plan's Lean form follows the
column constant, so `Plan.reads_abs` still holds and `Frame.frame` fails.

## What is trusted

The h5i-app framework's trusted base (`docs/app/TRUST.md` in h5i): the
engine runs each command in a SERIALIZABLE transaction, the tools (Charon,
Aeneas, Lean, rustc) and PostgreSQL. Beyond that, the shell in
`crates/gateway-server` and `crates/gateway-providers`:

- **Authentication:** the master key comparison and the HMAC verification of
  virtual keys (`h5i-app-token` parsing is itself verified) decide the
  `Principal`. The kernel trusts `master` and the key id it is given.
- **The clock:** budgets, windows, expiry and cooldowns use the engine's
  clock (PostgreSQL's, monotonic per tenant).
- **Token counts:** admission reserves an *estimate* of the prompt plus
  `max_tokens`; the gateway sets `max_tokens` when the client does not, so a
  provider that honours it stays within the reservation. Settlement charges
  what the provider reports. The budget theorem's honesty assumption is
  exactly that reported usage does not exceed the reservation. A provider
  that reports more (an underestimated prompt) is still charged in full, so
  spend can then pass the budget (this case is not covered by a theorem);
  the next admission sees the overrun and is refused. Media deployments
  are priced per image, second of audio or character instead of per token
  (see [Images and audio](COMPATIBILITY.md#images-and-audio)); their reservations are upper bounds
  except where a provider reports more image tokens, or a longer duration,
  than the header or estimate allowed for.
- **Provider translation** (`gateway-providers`), the configuration loader,
  and the JSON decoding of requests. Every theorem holds for all commands,
  so a wrong decoding can only produce a command the caller could have sent.
- **Spend log delivery** from the outbox is at least once; a sink must drop
  repeats by the `Idempotency-Key` header.
- **Read plans:** PostgreSQL returns, for each read of a plan, the rows
  `H5iAppLib.Query.Read.rows` says, in key order: h5i-app's
  `compile_read` is differential-tested against that definition (in both
  SQL modes; the gateway uses `ReadSqlMode::ScalarWhenUnique`), not proved.
  The frame theorem is stated on `Snapshot.load`, the snapshot those rows
  decode to.
- **Unsettled calls:** if the database is unreachable when a call settles,
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
ones get through. One of them does so in a tenant of 40 teams and 400 keys,
with batches whose items settle reservations admitted earlier in the same
batch: the PostgreSQL engine loads only what `read_plan` names, the
in-memory executor runs every command on the whole tenant.
