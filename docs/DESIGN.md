# Design

How h5i-gateway decides a request, and what each transaction reads.

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

## What a transaction reads

A command loads only the rows it can look at, not the whole tenant. The
kernel's `read_plan` names them as one declarative read per table
(`h5i_app_sql::Read`), and `GatewayStore::load_for` loads exactly those
(`schema_load_plan`):

| Command | Rows loaded (besides the settings and every deployment) |
|---|---|
| `Admit` | the caller's key, its team, the model by name, the key's and team's grants, the usage counters of the key, the team and every deployment, the reservations of the key and of its team (they feed the budget and parallel checks) |
| `Settle`, `Expire` | the reservation, its key and team and their counters, the caller's key (is it an admin?), every deployment's counter |
| `KeyInfo` | the caller's key and the key asked about, its grants and reservations |
| `TeamInfo` | the caller's key, the team asked about, its grants and reservations |
| `ListModels` | the caller's key, its team and their grants, every model |
| `Batch` | the union over its items: each key, reservation and model named once |
| management, `Dump` | everything |

Each arm of a plan's predicates fixes a key (a sub-read of "the team of key
`k`" is a scalar sub-query), so PostgreSQL answers it from an index: the cost
of a request no longer grows with the number of keys in the tenant. A batch
of 256 items by one key reads that key once.

Chat completions with one virtual key at concurrency 64 (mock upstream,
PostgreSQL 17 on host networking, group commit on), in a tenant holding
1, ~1,000 and ~10,000 keys, two runs each:

| Keys in the tenant | 1 | ~1,000 | ~10,000 |
|---|---|---|---|
| whole-tenant loads | 1,672 / 1,656 req/s | 1,248 / 1,240 | 336 / 336 |
| read plans | 1,520 / 1,504 req/s | 1,120 / 1,304 | 1,280 / 1,248 |
| read plans, `plan_cache_mode = force_generic_plan` | 1,520 req/s | 1,400 | — |

A plan's queries are larger than `SELECT ... WHERE tenant_id = $1`: a
batch that settles `n` reservations has an arm per reservation in the keys,
teams and usage reads. In a very small tenant that costs about 9%;
PostgreSQL also re-plans these statements (custom plans) on each new
connection, which is what makes the ~1,000-key runs vary. Setting
`plan_cache_mode = force_generic_plan` for the gateway's database role
(`ALTER ROLE ... SET plan_cache_mode = force_generic_plan`) avoids that.
