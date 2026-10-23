# Benchmark: h5i-gateway vs LiteLLM

This compares h5i-gateway with LiteLLM's Python proxy (latest PyPI release),
and with LiteLLM's work-in-progress Rust gateway where it can serve the same
requests. All three run against the same mock OpenAI-compatible upstream, take
the same requests, and are pinned to the same 8 CPUs. Everything lives in
`bench/` and `crates/gateway-bench`. One command reruns it all (see
[Reproducing](#reproducing)).

## Headline

Gateway on 8 logical CPUs, 64 concurrent keep-alive connections, upstream
answering immediately (profile `lat0`, so these numbers are gateway overhead
alone). Full tables are in [`results/tables.md`](results/tables.md).

| scenario (c=64, lat0) | direct upstream | h5i-gateway | LiteLLM Python 1.106.2 | LiteLLM Rust (WIP) |
|---|---|---|---|---|
| chat, master key: req/s | 215K | 33.2K | 801 | 38.1K |
| chat: p50 / p99 ms | 0.29 / 0.60 | 1.91 / 3.08 | 44.4 / 346 | 1.66 / 2.81 |
| chat: CPU per request | - | 194 us | 9.6 ms | 193 us |
| streaming chat: req/s | 35.0K | 11.2K | 277 | not supported (501) |
| embeddings (1536-d): req/s | 269K | 17.2K | 572 | not supported (501) |
| PostgreSQL + virtual key, Docker port forwarding: req/s | - | 851 | 488 | no database support |
| PostgreSQL + virtual key, host network: req/s | - | 1,389 | 480 | - |
| the same at c=256: req/s (p50 ms) | - | 2,125 (115) | 507 (456) | - |
| PostgreSQL, tenant holding 10,000 keys: req/s | - | 1,229 | 440 | - |
| memory (PSS, all processes) | - | 68 MB | 4.4 GB (8 workers) | 23 MB |

With a realistic upstream (profile `real`: 50 ms to the first byte, streams of
20 chunks 10 ms apart), at 256 connections:

| scenario (real, c=256) | direct | h5i-gateway | LiteLLM Python | LiteLLM Rust |
|---|---|---|---|---|
| chat: req/s (p50 ms) | 4,957 (51.6) | 4,887 (52.3) | 657 (184) | 4,920 (52.0) |
| streaming chat: req/s (p50 ms) | 936 (275) | 930 (276) | 238 (776) | - |
| embeddings: req/s (p50 ms) | 4,961 (51.5) | 4,785 (53.3) | 442 (599) | - |
| PostgreSQL + key, host network: req/s (p50 ms) | - | 1,206 (210) | 449 (354) | - |

In short:

- Without a database, h5i-gateway adds about 0.4 ms at low load and uses about
  194 us of CPU per chat completion: about 50 times less CPU than LiteLLM's
  Python proxy and 60 times less memory. LiteLLM's Rust gateway performs about
  the same as h5i on the one scenario it serves (non-streaming chat).
- With PostgreSQL, h5i-gateway is 1.7 to 4.2 times faster than LiteLLM from 64
  connections up, while doing more database work per request (see
  [Discussion](#discussion)). Behind Docker's port forwarding it is slightly
  slower at 1 and 16 connections (71 against 80, 424 against 463 req/s); on
  the host network it is faster at every concurrency (132 against 80 at one
  connection).
- With a 50 ms upstream, h5i-gateway's chat, streaming and embeddings stay
  within about 2 ms of calling the upstream directly at every concurrency.
  LiteLLM saturates at 657 chat, 442 embeddings and 238 streaming req/s.

![throughput, lat0](results/throughput-lat0.svg)

### Since the previous run

The first version of this benchmark (h5i at commit `ab08e49`) measured
h5i-gateway's PostgreSQL mode at a flat 70 to 77 req/s and its streaming at
41 ms per stream. Four changes since then account for the difference:

| change | effect in that change's own measurement |
|---|---|
| `TCP_NODELAY` on accepted sockets | streaming 1.55K → 11.6K req/s at c=64 (each SSE write no longer waits for a delayed ACK) |
| group commit: the shell queues `Admit` and `Settle` per tenant and commits them as one kernel `Batch` | PostgreSQL 70 → 282 req/s at c=64 |
| compaction of a batch's writes (one write per row) and one outbox row per commit | 282 → 877 req/s at c=64 (Docker port forwarding) |
| per-command read plans instead of whole-tenant loads | tenant of 10,000 keys: 336 → about 1,260 req/s |

`proofs/Theorems.lean` proves that a batch is exactly the sequential run of
its items (`batch_sequential`), that compaction reaches the same rows
(`compact_equiv`), and `proofs/Frame.lean` that each planned command gives on
its partial load the result it gives on the whole tenant (`frame`). Each
request still gets the answer it would get if its command were committed on
its own, in some order of the tenant's requests; the changes reduce the
number of transactions and the rows each one reads.

The no-database chat path became about 15% slower over the same period
(40.1K → 33.2K req/s at c=64, 180 → 194 us of CPU per request), as guardrail
selection and the response cache's checks joined it.

## What was compared

| system | version | how it ran |
|---|---|---|
| direct upstream | `mock-upstream` | the load generator calls the mock directly: the harness's own ceiling |
| h5i-gateway | commit `4003a66`, `cargo build --release` | `h5i-gateway --config <cfg>`, `RUST_LOG=warn`, Tokio multi-threaded (8 workers via the CPU mask), group commit up to 256 items |
| LiteLLM Python | `litellm[proxy]==1.106.2` (PyPI, latest at the time), Python 3.12.3, uvicorn 0.54.0, uvloop 0.23.0, prisma 0.15.0 | `litellm --config <cfg> --num_workers 8` (uvicorn with uvloop, LiteLLM's default on Linux) |
| LiteLLM Rust | `litellm-rust/` at BerriAI/litellm `f2118fc7` | `cargo build --release -p litellm-gateway` with its own workspace and profile (fat LTO); `LITELLM_CONFIG=<cfg>` |

LiteLLM ran with its documented production settings
([docs.litellm.ai/docs/proxy/prod](https://docs.litellm.ai/docs/proxy/prod)):
`LITELLM_MODE=PRODUCTION`, `LITELLM_LOG=ERROR`, `set_verbose: false`,
`json_logs: true`, `request_timeout: 600`, `routing_strategy: simple-shuffle`,
`proxy_batch_write_at: 60`, `database_connection_pool_limit: 10`,
`disable_error_logs: true`, and as many workers as CPUs. Access logs are off
at that log level. h5i-gateway logs only warnings. The configs are generated
by `driver.py` (`litellm_style_config`): one chat deployment
(`openai/gpt-4o-mini`) and one embedding deployment
(`openai/text-embedding-3-small`), both pointing at the mock.

LiteLLM's Rust gateway builds, starts and serves `/v1/chat/completions`
non-streaming against an OpenAI-compatible upstream, so it's included for
that scenario only. It was left out of the others for these reasons (from
its source at that commit):

- Provider: its chat route accepts only `anthropic`, `bedrock` and
  `openai_like` (`inference-chat/src/common_utils.rs`). `openai/...` returns
  `400 invalid provider: openai`, so its config uses `openai_like/gpt-4o-mini`.
- Streaming: `"stream": true` returns `501`. The base chat transformation
  answers `Unsupported("streaming")` (`llms/src/base_llm/chat/transformation.rs`).
- Embeddings: `/v1/embeddings` is routed to `request::unsupported` (`501`).
- Database: none. There is no database or virtual keys, and its README lists
  spend accounting as unimplemented. Only the master key authenticates.

### Machine

AMD EPYC 7502 (2 x 32 cores, SMT on, 128 logical CPUs, 2 NUMA nodes), 252 GB
RAM, Linux 6.8.0, rustc 1.98.1, Docker 29.9.2, `postgres:17`
(`sha256:d74eeac9…`). The machine is shared with other users. The 1-minute
load average was 1 to 9 during the run, most of it the benchmark itself.
Each point records the busy CPUs outside the benchmark's CPU sets (`other
load` in the tables): at most 1.2 CPUs.

### CPU pinning

| process group | logical CPUs |
|---|---|
| gateway under test (all its processes/threads) | 64-71 |
| load generator | 72-79 |
| mock upstream | 80-87 |
| PostgreSQL (`docker --cpuset-cpus`) | 88-95 |

All four sets are on NUMA node 0. Each set holds 8 hardware threads on 8
distinct physical cores. Their SMT siblings (0-31) were not reserved; see
[Caveats](#caveats). Override the sets with `BENCH_CPUS_{GATEWAY,LOADGEN,UPSTREAM,DB}`.

## Method

The mock upstream (`crates/gateway-bench/src/bin/mock_upstream.rs`) is axum on
Tokio with 8 workers and `TCP_NODELAY`. It returns OpenAI-shaped responses
(ids, `system_fingerprint`, `usage` with token details). Chat completions
carry about 120 completion tokens (1.3 KB response bodies; a whole stream is
7.3 KB). Streams send a role chunk, 20 content chunks, a finish chunk, a usage
chunk (when `stream_options.include_usage`) and `[DONE]`. Embeddings are 1536
floats (19 KB per response). Two profiles:
- `lat0`: latency 0 ms, 20 chunks with no delay between them.
- `real`: latency 50 ms before the response or the first chunk, then 20
  chunks 10 ms apart (a stream lasts about 275 ms).

The load generator (`crates/gateway-bench/src/bin/loadgen.rs`) is a
closed-loop client: N workers, each with its own HTTP/1.1 keep-alive
connection (hyper, `TCP_NODELAY`), sending back to back. An open-loop
`--rate` mode, which measures latency from the scheduled send time, exists
but wasn't used for the tables. Each point runs 5 s of warmup and then a 10 s
measured window. Only requests that complete inside the window count.

What is recorded per point:
- latency and time to first body byte (streams) in HDR histograms with 1 us
  resolution and 3 significant digits;
- throughput, and errors by status. An error is a non-200 response or a body
  that is not complete: no `[DONE]` for streams, no closing `}` otherwise.
  Every point in the tables had 0 errors.

On a separate OS thread, it also samples from /proc the gateway's process
tree (all LiteLLM workers included), the mock, and PostgreSQL:
- CPU time (utime+stime) over the window;
- the peak of the summed RSS, every 100 ms;
- the summed PSS at the end. PSS splits pages shared between LiteLLM's forked
  workers, so the PSS column is the fair memory figure. The RSS column
  double-counts shared pages.

Requests are the same for every system:
- chat: a system and a user message (about 560 characters), `max_tokens: 256`,
  `temperature: 0.2`;
- streaming: the same request with `stream: true` and
  `stream_options.include_usage`;
- embeddings: one string of about 140 characters.

Scenarios, for each profile, at 1, 16, 64 and 256 connections:
- `chat`, `stream` and `embeddings`: master key, no database.
- `db`: chat with PostgreSQL and a virtual key, the gateway reaching
  PostgreSQL through Docker's port forwarding (docker-proxy, a userspace hop
  per round trip). The key is created with `/key/generate`: models
  `[gpt-4o-mini]`, `max_budget` 1,000,000, `rpm_limit` 1e9, `tpm_limit` 1e12,
  30 days. Each system gets a fresh database in a `postgres:17` container on
  port 19300, with tmpfs data, `max_connections=500` and
  `shared_buffers=1GB`. LiteLLM runs its Prisma migrations at startup;
  h5i-gateway installs its schema. One call with the key is made before
  measuring, so LiteLLM's key cache is warm.
- `dbhost`: the same with PostgreSQL on the host network (loopback, as with a
  database on the same host or a nearby one).
- `dbbig`: as `dbhost`, after creating 10,000 more keys in the tenant
  (`/key/generate`, 32 at a time).
- `dbtenants` (h5i only): four h5i-gateway processes, each the master of its
  own tenant (`general_settings.org_id` 1 to 4), sharing one database and the
  gateway's 8 CPUs. Each load generator drives one of them with a quarter of
  the connections (so the "1" point is 4 connections). Throughput is the sum,
  latency percentiles the worst tenant's. LiteLLM has no tenants in this
  sense: its organizations share one database without per-tenant
  transactions.

The direct upstream has no database variant; the database scenarios compare
against direct chat.

## Results

Every number in the tables and charts below comes from
[`results/tables.md`](results/tables.md), generated from the raw JSON in
`results/raw/<profile>/<system>-<scenario>-c<N>.json`. The
`*-<scenario>-keyinfo.json` files hold `/key/info` for the benchmark key after
the run. The charts use log scales for throughput and latency. Hover a point
in a browser for its values.

### Gateway overhead (profile `lat0`)

![throughput lat0](results/throughput-lat0.svg)
![p50 lat0](results/latency-p50-lat0.svg)
![p99 lat0](results/latency-p99-lat0.svg)

Chat, master key, no database:

| c | direct req/s | h5i req/s (p50, p99 ms) | LiteLLM req/s (p50, p99 ms) | LiteLLM Rust req/s (p50, p99 ms) |
|---|---|---|---|---|
| 1 | 11.3K | 2,183 (0.45, 0.53) | 120 (8.3, 8.8) | 2,459 (0.40, 0.47) |
| 16 | 195K | 33.5K (0.47, 0.68) | 742 (19.7, 46.4) | 35.7K (0.44, 0.63) |
| 64 | 215K | 33.2K (1.91, 3.08) | 801 (44.4, 346) | 38.1K (1.66, 2.81) |
| 256 | 254K | 29.1K (8.59, 17.6) | 837 (233, 1,290) | 43.1K (5.56, 13.6) |

Streaming chat:

| c | direct req/s (p50) | h5i req/s (p50) | LiteLLM req/s (p50) |
|---|---|---|---|
| 1 | 2,349 (0.4) | 875 (1.2) | 38 (25.8) |
| 16 | 31.0K (0.5) | 10.1K (1.6) | 285 (55.6) |
| 64 | 35.0K (1.7) | 11.2K (5.6) | 277 (196) |
| 256 | 39.7K (6.4) | 11.4K (21.0) | 286 (713) |

Embeddings (1536 dimensions):

| c | direct req/s | h5i req/s (p50 ms) | LiteLLM req/s (p50 ms) |
|---|---|---|---|
| 1 | 9.5K | 1,115 (0.9) | 79 (12.6) |
| 16 | 220K | 17.1K (0.9) | 540 (29.3) |
| 64 | 269K | 17.2K (3.7) | 572 (90.2) |
| 256 | 281K | 17.2K (14.4) | 584 (180) |

PostgreSQL + virtual key, chat, req/s (p50 ms):

| c | h5i, port forwarding | LiteLLM, port forwarding | h5i, host network | LiteLLM, host network | h5i, 10,000 keys | LiteLLM, 10,000 keys |
|---|---|---|---|---|---|---|
| 1 | 71 (14.1) | 80 (11.9) | 132 (7.3) | 80 (11.6) | 122 (7.8) | 78 (11.8) |
| 16 | 424 (37.7) | 463 (31.5) | 662 (24.1) | 419 (32.2) | 662 (24.0) | 422 (33.5) |
| 64 | 851 (75.1) | 488 (95.7) | 1,389 (46.3) | 480 (57.9) | 1,229 (49.6) | 440 (63.1) |
| 256 | 1,152 (213) | 525 (372) | 2,125 (115) | 507 (456) | 1,306 (194) | 510 (477) |

Four tenants on one database (h5i, host network):

| connections | req/s (worst tenant's p50 ms) | per tenant |
|---|---|---|
| 4 | 419 (8.6) | - |
| 16 | 815 (17.9) | - |
| 64 | 1,766 (21.1) | - |
| 256 | 1,458 (43.9) | - |

A repeat of the last two points shortly after the full run gave 2,912 req/s
at 64 connections (731, 741, 704 and 736 per tenant) and 2,517 at 256 (890,
718, 416 and 493). During the 256-connection repeat PostgreSQL recorded about
70 rolled-back transactions per second against about 1,400 commits, and
none at 64. See [Discussion](#discussion).

### Realistic upstream (profile `real`)

![throughput real](results/throughput-real.svg)
![p50 real](results/latency-p50-real.svg)
![p99 real](results/latency-p99-real.svg)

With 50 ms of upstream latency, the two Rust gateways track the direct
baseline without a database: at c=256, 4.9K chat req/s against 4.96K direct,
930 streams/s against 936, and h5i's embeddings 4.8K against 4.96K, adding at
most 1.8 ms at the median. LiteLLM adds 17 ms at c=1 and 130 to 550 ms at
c=256, where it saturates at 657 chat req/s, 238 streams/s and 442
embeddings/s.

PostgreSQL + virtual key, chat, req/s (p50 ms):

| c | h5i, port forwarding | LiteLLM, port forwarding | h5i, host network | LiteLLM, host network | h5i, 10,000 keys | LiteLLM, 10,000 keys | h5i, 4 tenants |
|---|---|---|---|---|---|---|---|
| 1 (4 for tenants) | 15 (67.3) | 13 (75.6) | 17 (59.5) | 13 (75.5) | 16 (60.8) | 13 (76.0) | 67 (59.5) |
| 16 | 191 (85.0) | 201 (77.2) | 229 (70.8) | 195 (78.8) | 213 (76.4) | 192 (82.0) | 264 (60.4) |
| 64 | 524 (124) | 372 (92.9) | 630 (102) | 378 (102) | 595 (109) | 374 (141) | 636 (73.9) |
| 256 | 797 (321) | 499 (483) | 1,206 (210) | 449 (354) | 1,154 (223) | 496 (435) | 904 (170) |

### CPU and memory

![cpu chat](results/cpu-per-request-chat-lat0.svg)
![cpu db](results/cpu-per-request-db-lat0.svg)
![memory](results/memory-pss.svg)

CPU per request at c=64 (lat0), counting all gateway processes, user +
system:

| scenario | h5i | LiteLLM Rust | LiteLLM Python |
|---|---|---|---|
| chat | 194 us | 193 us | 9.6 ms |
| streaming | 686 us | - | 26.7 ms |
| embeddings | 433 us | - | 14.0 ms |
| PostgreSQL + key, port forwarding | 629 us | - | 16.1 ms |
| PostgreSQL + key, host network | 608 us | - | 16.2 ms |

PostgreSQL's own CPU during the database points was 0.38 CPUs for h5i at
851 req/s (port forwarding) and 0.68 CPUs at 1,389 req/s (host network),
against 0.29 to 0.35 CPUs for LiteLLM at 480 to 490 req/s.

Memory (PSS summed over processes, lat0): h5i 53 to 109 MB without a database
and 28 to 88 MB with one, depending on concurrency and response size; LiteLLM
Rust 13 to 50 MB; LiteLLM Python 4.2 to 5.1 GB for its 8 workers without a
database and 4.5 to 6.0 GB with one.

## Discussion

### Without a database

An h5i request costs about 194 us of CPU. That covers parsing the body,
authenticating, running the kernel's `Admit` and `Settle` in memory, building
the upstream request, and re-serializing the response, all in compiled code
on one Tokio runtime. LiteLLM spends about 8.3 ms of CPU per chat request
even at c=1 (one worker busy for the whole request): Python/FastAPI request
handling plus LiteLLM's pre- and post-call machinery (parameter mapping, cost
calculation, logging objects, callbacks). Eight workers cap it at about 800
chat req/s on 8 CPUs; beyond that, requests queue and p99 grows past a second
at c=256. Embeddings show the same gap: h5i parses and re-serializes the
19 KB response for about 430 us, LiteLLM takes about 14 ms building Python
objects for 1536 floats. The memory gap (about 70 MB against 4.4 GB) comes
from LiteLLM loading its whole package into each of 8 forked workers.

LiteLLM's Rust gateway is h5i's peer on raw overhead: within 1% of h5i's CPU
per request at c=64, and faster at c=256 (43.1K against 29.1K req/s). It is a
smaller program today (no streaming, embeddings, keys or spend).

### With PostgreSQL

Each h5i request is two kernel commands, `Admit` (reserve the worst-case
cost) and `Settle` (charge the actual cost, write the spend log to the
outbox), each in a SERIALIZABLE transaction that h5i-app's engine runs under
a tenant-wide advisory lock. The shell's batcher keeps one queue per tenant:
requests that arrive while a transaction is in flight are committed together
in the next one, as one kernel `Batch`. A batch writes each row once (a
batch of admissions by one key updates its key and usage rows once) and puts
all its spend logs in one outbox row, and each command loads only the rows
its read plan names.

The cost that remains is round trips. At c=64 the gateway used 0.5 to 0.8
CPUs and PostgreSQL 0.4 to 0.7 CPUs, so neither was CPU-bound. A batch costs
a fixed set of statements (lock, clock, the planned reads, commit) plus about
one statement per admitted request (its reservation) and one per settled
request (deleting the reservation). The `dbhost` columns run 1.5 to 1.8 times
faster than the `db` columns because Docker's port forwarding adds a
userspace hop to every one of those round trips.
At one connection there is nothing to batch, so a request costs two full
transactions; that is the one point where h5i is behind LiteLLM (71 against
80 req/s with port forwarding).

LiteLLM needs no database work on the hot path. It authenticates from an
in-memory key cache and checks budgets against cached spend, enforces rate
limits in each worker's memory without Redis, and writes accumulated spend in
batches every `proxy_batch_write_at` = 60 s. Its database CPU stays at about
0.3 CPUs whatever the load; its own CPU is the limit (7 to 8 of its 8 CPUs).

The two modes do different work. h5i-gateway's PostgreSQL mode guarantees,
and proves, that concurrent requests cannot overspend a budget, because
budgets are reserved and checked inside a serializable transaction; that a
spend log exists exactly when its charge commits; and that rate limits hold
across every instance sharing the database. LiteLLM's numbers come with
weaker semantics:
- a budget can be overrun by whatever is in flight or not yet flushed (up to
  60 s of spend);
- without Redis, per-key RPM/TPM limits are enforced per worker, so the
  effective limit is 8 times the configured one here;
- spend reaches the database only after the batch interval. Right after the
  runs, `/key/info` for LiteLLM's benchmark key reported spend 0.0; h5i's
  reported every request's charge (`results/raw/*/*-keyinfo.json`).

### Large tenants

Before read plans, every transaction loaded every row of the tenant, and a
tenant with 10,000 keys ran at about 336 req/s at c=64. With them, `dbbig`
runs at 1,229 req/s against 1,389 for a one-key tenant (lat0, c=64), and at
1,154 against 1,206 with the 50 ms upstream at c=256. LiteLLM is unaffected
by the number of keys (440 against 480 req/s).

### Several tenants

Tenants have separate locks and queues, so their transactions can run in
parallel. Four tenants reached 1,766 req/s in the full run and 2,912 in a
repeat at 64 connections, against 1,389 for one tenant with all 64; at 256
connections both runs were lower than at 64 (1,458 and 2,517) and the
tenants were uneven. The repeat saw rolled-back transactions only at 256
connections. The likely cause is SERIALIZABLE conflicts between tenants'
transactions on shared tables and index pages, which h5i-app's engine retries
(its retries are not counted per point, so this is not confirmed). The four
gateway processes also shared the gateway's 8 CPUs. The `dbtenants` numbers
are therefore the least settled in this report; the full run and the repeat
differ by 65% at 64 connections.

### Caveats

- Loopback only: the load generator, the gateways, the mock and PostgreSQL
  share one machine. A network between gateway and database would cost h5i
  more than LiteLLM, since every batch is several round trips and LiteLLM's
  hot path has none.
- Shared machine: the CPU sets are disjoint and on distinct physical cores,
  but their SMT siblings and the rest of the machine were open to other
  users' jobs. Outside load stayed under 1.2 busy CPUs per point.
- The direct baseline is limited by the 8-CPU load generator and mock: about
  250K req/s non-streaming, 40K streams/s. h5i's and LiteLLM Rust's 30K to
  43K req/s are their own limits, not the harness's.
- LiteLLM Python might do better with other servers (`--run_gunicorn`,
  `--run_granian`), more workers than CPUs, or Redis. This benchmark uses its
  default uvicorn+uvloop server with one worker per CPU, as its production
  guide recommends for a single VM.
- 10 s windows: LiteLLM's tails (p99, max) and the multi-tenant points vary
  between runs. Rerun with `--duration 30` for tighter numbers.
- The 4-tenant scenario runs four gateway processes on the CPUs one gateway
  gets elsewhere, and its lowest point is 4 connections, not 1.

## Reproducing

```sh
bench/run.sh                       # everything: builds, installs, runs, renders (about 1 h)
bench/run.sh --profiles lat0 --systems direct,h5i --scenarios chat --concurrency 64 --duration 5
python3 bench/report.py bench/results   # re-render tables and charts from raw JSON
```

`run.sh` is idempotent: rerunning rebuilds what changed and overwrites the
results. It does the following:
1. builds `h5i-gateway`, `mock-upstream` and `loadgen` in release mode
   in Cargo's target directory (`$CARGO_TARGET_DIR`, by default `target/`);
2. builds LiteLLM's Rust gateway. It uses `$LITELLM_RUST_DIR`, or otherwise
   sparse-clones BerriAI/litellm at `f2118fc7`, into
   `<target>/bench/litellm-rust-target`;
3. installs `litellm[proxy]` (or `$LITELLM_VERSION`), `prisma` and `uvloop`
   into `<target>/bench/venv`, and runs `prisma generate` for LiteLLM's
   schema. The first run downloads Node and the Prisma engines;
4. records `results/environment.json`;
5. runs `driver.py`, which starts and stops every process and the
   PostgreSQL container itself;
6. runs `report.py`.

Logs go to `<target>/bench/logs` (set `BENCH_SCRATCH` to move the scratch
directory). `driver.py --resume` skips points whose
JSON already exists. Delete a noisy point's file and rerun with `--resume` to
redo just that point. `driver.py` waits before a point while the 1-minute
load average is above `--max-load` (default 64). `BENCH_BIG_KEYS` (default
10,000) and `BENCH_TENANTS` (default 4) size the `dbbig` and `dbtenants`
scenarios.

Runtime: about an hour for 184 points: 15 s per point plus process startup
(LiteLLM about 30 s per start), and about 6 min to create the 10,000 keys in
h5i's tenant per profile (15 s in LiteLLM's). The first `run.sh` also spends
about 5 min building LiteLLM's Rust gateway (fat LTO), about 1 min on the h5i
builds, and 1 to 2 min installing LiteLLM.

Requirements: Linux with `taskset`, Docker (with the `postgres:17` image or
network to pull it), Rust, Python 3.10+, `git`, and network access for PyPI,
Prisma and GitHub on the first run.

## Files

| path | what |
|---|---|
| `bench/run.sh` | the one command |
| `bench/driver.py` | runs every point: process groups, pinning, PostgreSQL, virtual keys, large and multiple tenants |
| `bench/report.py` | tables and SVG charts from raw JSON |
| `bench/setup-litellm.sh` | LiteLLM venv and Prisma client |
| `bench/results/` | `raw/` JSON per point, `tables.md`, `environment.json`, charts |
| `crates/gateway-bench/` | `mock-upstream` and `loadgen` |
