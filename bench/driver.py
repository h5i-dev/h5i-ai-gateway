#!/usr/bin/env python3
"""Benchmark driver: runs every (profile, system, scenario, concurrency) point.

Started by bench/run.sh, which builds the tools and installs LiteLLM first.
Standard library only. Each point writes one JSON file under
bench/results/raw/<profile>/<system>-<scenario>-c<N>.json.

Process groups are pinned to disjoint CPU sets with taskset (PostgreSQL with
docker --cpuset-cpus); see CORES below.
"""

import argparse
import json
import os
import signal
import subprocess
import sys
import time
import urllib.error
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# Disjoint CPU sets (the benchmark machine has 128 cores).
CORES = {
    "gateway": os.environ.get("BENCH_CPUS_GATEWAY", "64-71"),
    "loadgen": os.environ.get("BENCH_CPUS_LOADGEN", "72-79"),
    "upstream": os.environ.get("BENCH_CPUS_UPSTREAM", "80-87"),
    "db": os.environ.get("BENCH_CPUS_DB", "88-95"),
}
GATEWAY_CORES = 8

UPSTREAM_PORT = 19100
GATEWAY_PORT = 19200
PG_PORT = 19300
PG_CONTAINER = "h5i-bench-pg"
PG_IMAGE = "postgres:17"
MASTER_KEY = "sk-bench-master-0123456789"
CHAT_MODEL = "gpt-4o-mini"
EMBED_MODEL = "text-embedding-3-small"

# Mock upstream settings per profile.
PROFILES = {
    # Pure gateway overhead: the upstream answers immediately.
    "lat0": {"latency-ms": 0, "stream-chunks": 20, "chunk-delay-ms": 0},
    # A realistic provider: 50 ms to the first byte, 20 chunks 10 ms apart.
    "real": {"latency-ms": 50, "stream-chunks": 20, "chunk-delay-ms": 10},
}
SCENARIO_PATH = {
    "chat": "/v1/chat/completions",
    "stream": "/v1/chat/completions",
    "embeddings": "/v1/embeddings",
    "db": "/v1/chat/completions",
    "dbhost": "/v1/chat/completions",
}


def log(msg):
    print(f"[{time.strftime('%H:%M:%S')}] {msg}", flush=True)


def http(method, url, body=None, key=None, timeout=10):
    data = json.dumps(body).encode() if body is not None else None
    req = urllib.request.Request(url, data=data, method=method)
    req.add_header("content-type", "application/json")
    if key:
        req.add_header("authorization", f"Bearer {key}")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.status, r.read()
    except urllib.error.HTTPError as e:
        return e.code, e.read()


class Proc:
    """A process group pinned to a CPU set, logging to a file."""

    def __init__(self, name, argv, cores, logdir, env=None):
        self.name = name
        self.logfile = os.path.join(logdir, f"{name}.log")
        self.out = open(self.logfile, "ab")
        self.out.write(f"\n==== {time.ctime()} {' '.join(argv)}\n".encode())
        self.out.flush()
        full_env = dict(os.environ)
        full_env.update(env or {})
        self.p = subprocess.Popen(
            ["taskset", "-c", cores] + argv,
            stdout=self.out,
            stderr=subprocess.STDOUT,
            env=full_env,
            start_new_session=True,
        )
        self.pid = self.p.pid  # taskset execs the program: same pid

    def alive(self):
        return self.p.poll() is None

    def stop(self):
        if self.p.poll() is None:
            try:
                os.killpg(self.p.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                self.p.wait(timeout=20)
            except subprocess.TimeoutExpired:
                os.killpg(self.p.pid, signal.SIGKILL)
                self.p.wait()
        self.out.close()


def wait_ready(proc, url, key, body, timeout=240):
    """Poll with a real request until it returns 200."""
    deadline = time.time() + timeout
    last = None
    while time.time() < deadline:
        if not proc.alive():
            raise RuntimeError(f"{proc.name} exited (see {proc.logfile})")
        try:
            status, data = http("POST", url, body, key, timeout=5)
            if status == 200:
                return
            last = f"{status} {data[:300]!r}"
        except Exception as e:  # connection refused while starting
            last = repr(e)
        time.sleep(0.5)
    raise RuntimeError(f"{proc.name} not ready after {timeout}s: {last}")


# ---------------------------------------------------------------- systems


def upstream_base():
    return f"http://127.0.0.1:{UPSTREAM_PORT}/v1"


def litellm_style_config(db_url=None, production=True, provider="openai"):
    """A LiteLLM config.yaml, understood by all three gateways."""
    lines = [
        "model_list:",
        f"  - model_name: {CHAT_MODEL}",
        "    litellm_params:",
        f"      model: {provider}/{CHAT_MODEL}",
        f"      api_base: {upstream_base()}",
        "      api_key: sk-mock-upstream",
        f"  - model_name: {EMBED_MODEL}",
        "    litellm_params:",
        f"      model: {provider}/{EMBED_MODEL}",
        f"      api_base: {upstream_base()}",
        "      api_key: sk-mock-upstream",
    ]
    if production:
        # LiteLLM's documented production settings (docs.litellm.ai/docs/proxy/prod).
        lines += [
            "litellm_settings:",
            "  request_timeout: 600",
            "  set_verbose: false",
            "  json_logs: true",
            "router_settings:",
            "  routing_strategy: simple-shuffle",
        ]
    lines += ["general_settings:", f"  master_key: {MASTER_KEY}"]
    if production:
        lines += [
            "  proxy_batch_write_at: 60",
            "  database_connection_pool_limit: 10",
            "  disable_error_logs: true",
        ]
    if db_url:
        lines.append(f"  database_url: {db_url}")
    return "\n".join(lines) + "\n"


def start_system(system, args, db_url=None):
    """Returns the Proc of the gateway under test (None for direct)."""
    if system == "direct":
        return None
    cfg = os.path.join(args.scratch, f"config-{system}.yaml")
    port = str(GATEWAY_PORT)
    if system == "h5i":
        with open(cfg, "w") as f:
            f.write(litellm_style_config(db_url, production=False))
        env = {"RUST_LOG": "warn"}
        argv = [args.h5i_bin, "--config", cfg, "--host", "127.0.0.1", "--port", port]
    elif system == "litellm":
        with open(cfg, "w") as f:
            f.write(litellm_style_config(db_url, production=True))
        env = {
            "LITELLM_MODE": "PRODUCTION",
            "LITELLM_LOG": "ERROR",
            "LITELLM_MASTER_KEY": MASTER_KEY,
            "LITELLM_SALT_KEY": "sk-bench-salt-0123456789",
            "NO_DOCKER": "1",
            "DISABLE_ADMIN_UI": "True",
            "PRISMA_BINARY_CACHE_DIR": os.path.join(args.scratch, "prisma-cache"),
            "XDG_CACHE_HOME": os.path.join(args.scratch, "xdg-cache"),
            "HOME": os.path.join(args.scratch, "home"),
        }
        os.makedirs(env["HOME"], exist_ok=True)
        if db_url:
            env["DATABASE_URL"] = db_url
        argv = [
            os.path.join(args.venv, "bin", "litellm"),
            "--config", cfg, "--host", "127.0.0.1", "--port", port,
            "--num_workers", str(GATEWAY_CORES),
        ]
    elif system == "litellm-rust":
        with open(cfg, "w") as f:
            # Its chat route serves only anthropic, bedrock and openai_like.
            f.write(litellm_style_config(None, production=False, provider="openai_like"))
        env = {"LITELLM_CONFIG": cfg, "HOST": "127.0.0.1", "PORT": port, "RUST_LOG": "warn"}
        argv = [args.litellm_rust_bin]
    else:
        raise ValueError(system)
    proc = Proc(system, argv, CORES["gateway"], args.logdir, env)
    body = {"model": CHAT_MODEL, "messages": [{"role": "user", "content": "ping"}], "max_tokens": 8}
    try:
        wait_ready(proc, f"http://127.0.0.1:{port}/v1/chat/completions", MASTER_KEY, body)
    except BaseException:
        proc.stop()
        raise
    return proc


def make_virtual_key(system):
    """A key with a budget and rate limits far above what the run uses."""
    body = {
        "models": [CHAT_MODEL],
        "max_budget": 1000000,
        "rpm_limit": 1000000000,
        "tpm_limit": 1000000000000,
        "duration": "30d",
    }
    status, data = http("POST", f"http://127.0.0.1:{GATEWAY_PORT}/key/generate", body, MASTER_KEY, 60)
    if status != 200:
        raise RuntimeError(f"{system} /key/generate: {status} {data[:500]!r}")
    return json.loads(data)["key"]


# ---------------------------------------------------------------- postgres


PG_PSQL_PORT = "5432"


def docker(*a, check=True, capture=False):
    return subprocess.run(["docker", *a], check=check, capture_output=capture, text=True)


# Database scenarios and how the gateway reaches PostgreSQL: through Docker's
# port forwarding (docker-proxy, a userspace hop per round trip) or on the
# host network (loopback, as with a database on the same host or LAN).
DB_SCENARIOS = {"db": "forward", "dbhost": "host"}


def start_postgres(network="forward"):
    docker("rm", "-f", PG_CONTAINER, check=False, capture=True)
    net = ["--network", "host"] if network == "host" else ["-p", f"127.0.0.1:{PG_PORT}:5432"]
    port = ["-c", f"port={PG_PORT}", "-c", "listen_addresses=127.0.0.1"] if network == "host" else []
    docker(
        "run", "--rm", "-d", "--name", PG_CONTAINER,
        "--cpuset-cpus", CORES["db"],
        *net,
        "--tmpfs", "/var/lib/postgresql/data:rw,size=8g",
        "--shm-size", "1g",
        "-e", "POSTGRES_USER=bench", "-e", "POSTGRES_PASSWORD=bench", "-e", "POSTGRES_DB=bench",
        PG_IMAGE, "-c", "max_connections=500", "-c", "shared_buffers=1GB", *port,
        capture=True,
    )
    global PG_PSQL_PORT
    PG_PSQL_PORT = str(PG_PORT) if network == "host" else "5432"
    for _ in range(120):
        r = docker("exec", PG_CONTAINER, "pg_isready", "-U", "bench", "-h", "127.0.0.1",
                   "-p", PG_PSQL_PORT, check=False, capture=True)
        if r.returncode == 0:
            # The entrypoint restarts the server once after initdb.
            time.sleep(2)
            r = docker("exec", PG_CONTAINER, "pg_isready", "-U", "bench", "-h", "127.0.0.1",
                       "-p", PG_PSQL_PORT, check=False, capture=True)
            if r.returncode == 0:
                return
        time.sleep(1)
    raise RuntimeError("postgres did not start")


def postgres_pid():
    r = docker("inspect", "-f", "{{.State.Pid}}", PG_CONTAINER, capture=True)
    return int(r.stdout.strip())


def fresh_database(name):
    psql = ["exec", PG_CONTAINER, "psql", "-U", "bench", "-d", "bench", "-h", "127.0.0.1", "-p", PG_PSQL_PORT,
            "-v", "ON_ERROR_STOP=1", "-c"]
    docker(*psql, f"DROP DATABASE IF EXISTS {name} WITH (FORCE)", capture=True)
    docker(*psql, f"CREATE DATABASE {name}", capture=True)
    return f"postgresql://bench:bench@127.0.0.1:{PG_PORT}/{name}"


def stop_postgres():
    docker("rm", "-f", PG_CONTAINER, check=False, capture=True)


# ---------------------------------------------------------------- points


def wait_quiet(max_load, max_wait=300):
    load = os.getloadavg()[0]
    waited = 0
    while load > max_load and waited < max_wait:
        log(f"  load {load:.1f} > {max_load}: waiting")
        time.sleep(15)
        waited += 15
        load = os.getloadavg()[0]
    return load


def cpu_busy():
    """(busy, total) jiffies per CPU from /proc/stat."""
    out = {}
    with open("/proc/stat") as f:
        for line in f:
            if line.startswith("cpu") and line[3].isdigit():
                name, *v = line.split()
                v = [int(x) for x in v]
                idle = v[3] + v[4]
                out[int(name[3:])] = (sum(v[:8]) - idle, sum(v[:8]))
    return out


def parse_cpus(spec):
    cpus = set()
    for part in spec.split(","):
        a, _, b = part.partition("-")
        cpus.update(range(int(a), int(b or a) + 1))
    return cpus


def busy_cores(before, after, cpus=None):
    busy = total = 0
    for c, (b1, t1) in after.items():
        if cpus is None or c in cpus:
            b0, t0 = before.get(c, (b1, t1))
            busy += b1 - b0
            total += t1 - t0
    n = len(after) if cpus is None else len(cpus)
    return round(busy / total * n, 2) if total else 0.0


def run_point(args, profile, system, scenario, conc, key, watch):
    out_dir = os.path.join(args.out, "raw", profile)
    os.makedirs(out_dir, exist_ok=True)
    out = os.path.join(out_dir, f"{system}-{scenario}-c{conc}.json")
    if args.resume and os.path.exists(out):
        log(f"  skip {out} (exists)")
        return
    base = (f"http://127.0.0.1:{UPSTREAM_PORT}" if system == "direct"
            else f"http://127.0.0.1:{GATEWAY_PORT}")
    load_before = wait_quiet(args.max_load)
    argv = [
        "taskset", "-c", CORES["loadgen"], args.loadgen_bin,
        "--url", base + SCENARIO_PATH[scenario],
        "--scenario", "chat" if scenario in DB_SCENARIOS else scenario,
        "--key", key,
        "--concurrency", str(conc),
        "--duration", str(args.duration),
        "--warmup", str(args.warmup),
        "--label", f"{profile}/{system}/{scenario}",
        "--out", out,
    ]
    for name, pid in watch.items():
        argv += ["--watch", f"{name}={pid}"]
    stat0 = cpu_busy()
    r = subprocess.run(argv, capture_output=True, text=True)
    stat1 = cpu_busy()
    print("  " + r.stderr.strip().replace("\n", "\n  "), flush=True)
    if r.returncode != 0 or not os.path.exists(out):
        raise RuntimeError(f"loadgen failed: {r.stderr}")
    with open(out) as f:
        res = json.load(f)
    res.update({
        "system": system,
        "profile": profile,
        "profile_settings": PROFILES[profile],
        "bench_scenario": scenario,
        "loadavg_before": round(load_before, 2),
        "loadavg_after": round(os.getloadavg()[0], 2),
        "cores": CORES,
        # Busy CPUs (whole run incl. warmup) on the whole machine, and on the
        # CPUs not given to the benchmark (other users of the machine).
        "machine_busy_cores": busy_cores(stat0, stat1),
        "other_cpus_busy_cores": busy_cores(
            stat0, stat1, set(stat1) - set().union(*(parse_cpus(c) for c in CORES.values()))),
    })
    with open(out, "w") as f:
        json.dump(res, f, indent=2)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--systems", default="direct,h5i,litellm,litellm-rust")
    ap.add_argument("--profiles", default="lat0,real")
    ap.add_argument("--scenarios", default="chat,stream,embeddings,db,dbhost")
    ap.add_argument("--concurrency", default="1,16,64,256")
    ap.add_argument("--db-concurrency", default="1,16,64,256")
    ap.add_argument("--duration", type=float, default=10)
    ap.add_argument("--warmup", type=float, default=5)
    ap.add_argument("--max-load", type=float, default=64.0,
                    help="wait before a point while the 1-min load average exceeds this")
    ap.add_argument("--resume", action="store_true", help="skip points whose JSON exists")
    ap.add_argument("--out", default=os.path.join(HERE, "results"))
    ap.add_argument("--scratch", default=os.environ.get("BENCH_SCRATCH", "/dev/shm/h5i-bench"))
    ap.add_argument("--target", default=os.environ.get("CARGO_TARGET_DIR", "/dev/shm/h5i-gw-target-bench"))
    ap.add_argument("--litellm-rust-bin",
                    help="default: <scratch>/litellm-rust-target/release/litellm-gateway")
    ap.add_argument("--h5i-bin", help="h5i-gateway binary (default: <target>/release/h5i-gateway)")
    args = ap.parse_args()
    args.litellm_rust_bin = args.litellm_rust_bin or os.path.join(
        args.scratch, "litellm-rust-target", "release", "litellm-gateway")
    args.h5i_bin = args.h5i_bin or os.path.join(args.target, "release", "h5i-gateway")
    args.loadgen_bin = os.path.join(args.target, "release", "loadgen")
    args.mock_bin = os.path.join(args.target, "release", "mock-upstream")
    args.venv = os.path.join(args.scratch, "venv")
    args.logdir = os.path.join(args.scratch, "logs")
    os.makedirs(args.logdir, exist_ok=True)

    systems = args.systems.split(",")
    for name, binary in (("litellm-rust", args.litellm_rust_bin),):
        if name in systems and not os.path.exists(binary):
            log(f"{name} binary {binary} missing: skipping it")
            systems.remove(name)
    scenarios = args.scenarios.split(",")
    concs = [int(c) for c in args.concurrency.split(",")]
    db_concs = [int(c) for c in args.db_concurrency.split(",")]
    # What each system supports (see bench/README.md).
    supports = {
        "direct": {"chat", "stream", "embeddings"},
        "h5i": {"chat", "stream", "embeddings", "db", "dbhost"},
        "litellm": {"chat", "stream", "embeddings", "db", "dbhost"},
        # Chat only: streaming and /v1/embeddings return 501, and no database support.
        "litellm-rust": {"chat"},
    }

    procs = []
    pg_started = False

    def cleanup(*_):
        for p in procs:
            p.stop()
        if pg_started:
            stop_postgres()

    signal.signal(signal.SIGTERM, lambda *_: (cleanup(), sys.exit(1)))
    t0 = time.time()
    try:
        for profile in args.profiles.split(","):
            settings = PROFILES[profile]
            mock_argv = [args.mock_bin, "--port", str(UPSTREAM_PORT)]
            for k, v in settings.items():
                mock_argv += [f"--{k}", str(v)]
            mock = Proc(f"mock-upstream-{profile}", mock_argv, CORES["upstream"], args.logdir)
            procs.append(mock)
            wait_ready(mock, f"http://127.0.0.1:{UPSTREAM_PORT}/v1/chat/completions", None,
                       {"model": CHAT_MODEL, "messages": [{"role": "user", "content": "ping"}]})
            log(f"profile {profile}: mock upstream {settings}")

            nodb = [s for s in scenarios if s not in DB_SCENARIOS]
            for system in systems:
                todo = [s for s in nodb if s in supports[system]]
                if not todo:
                    continue
                log(f"{profile}/{system}: starting (no database)")
                gw = start_system(system, args)
                if gw:
                    procs.append(gw)
                watch = {"gateway": gw.pid} if gw else {}
                watch["upstream"] = mock.pid
                key = MASTER_KEY if gw else "sk-mock-upstream"
                for scenario in todo:
                    for c in concs:
                        run_point(args, profile, system, scenario, c, key, watch)
                if gw:
                    gw.stop()
                    procs.remove(gw)

            for db_scenario, network in DB_SCENARIOS.items():
                db_systems = [s for s in systems if db_scenario in supports[s] and s != "direct"]
                if db_scenario not in scenarios or not db_systems:
                    continue
                start_postgres(network)
                pg_started = True
                for system in db_systems:
                    name = f"bench_{system.replace('-', '_')}_{profile}_{db_scenario}"
                    url = fresh_database(name)
                    log(f"{profile}/{system}: starting with PostgreSQL ({name})")
                    gw = start_system(system, args, db_url=url)
                    procs.append(gw)
                    key = make_virtual_key(system)
                    # A first call with the virtual key (LiteLLM caches the key after it).
                    body = {"model": CHAT_MODEL, "messages": [{"role": "user", "content": "ping"}],
                            "max_tokens": 8}
                    status, data = http("POST", f"http://127.0.0.1:{GATEWAY_PORT}/v1/chat/completions",
                                        body, key, 30)
                    if status != 200:
                        raise RuntimeError(f"{system} virtual key call: {status} {data[:300]!r}")
                    watch = {"gateway": gw.pid, "upstream": mock.pid, "db": postgres_pid()}
                    for c in db_concs:
                        run_point(args, profile, system, db_scenario, c, key, watch)
                    # What the gateway recorded for the key (LiteLLM writes spend in batches).
                    status, data = http("GET", f"http://127.0.0.1:{GATEWAY_PORT}/key/info?key={key}",
                                        None, MASTER_KEY, 30)
                    info = os.path.join(args.out, "raw", profile, f"{system}-{db_scenario}-keyinfo.json")
                    with open(info, "w") as f:
                        json.dump({"status": status, "body": data.decode(errors="replace")}, f, indent=2)
                    gw.stop()
                    procs.remove(gw)
            mock.stop()
            procs.remove(mock)
    finally:
        cleanup()
    log(f"done in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
