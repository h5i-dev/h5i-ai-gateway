#!/usr/bin/env bash
# Runs the whole benchmark end to end: builds the tools and gateways, installs
# LiteLLM, runs every point (bench/driver.py), and renders tables and charts
# (bench/report.py). Idempotent: rerunning rebuilds what changed and
# overwrites the results. Arguments are passed to driver.py, e.g.
#   bench/run.sh --profiles lat0 --systems direct,h5i --duration 5
# Environment: BENCH_SCRATCH (default /dev/shm/h5i-bench), CARGO_TARGET_DIR
# (default /dev/shm/h5i-gw-target-bench), LITELLM_RUST_DIR, LITELLM_VERSION,
# BENCH_CPUS_{GATEWAY,LOADGEN,UPSTREAM,DB}.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
SCRATCH=${BENCH_SCRATCH:-/dev/shm/h5i-bench}
export BENCH_SCRATCH=$SCRATCH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-/dev/shm/h5i-gw-target-bench}
LITELLM_COMMIT=f2118fc7670ba3fa736d9b8f4deef9077a45a720
LITELLM_RUST_DIR=${LITELLM_RUST_DIR:-/dev/shm/h5i-gw/litellm/litellm-rust}
RESULTS=$ROOT/bench/results
mkdir -p "$SCRATCH/logs" "$RESULTS"
for tool in cargo docker taskset python3 git patch; do
  command -v "$tool" >/dev/null || { echo "missing $tool" >&2; exit 1; }
done

echo "== building h5i-gateway and the bench tools (release)"
cargo build --release --manifest-path "$ROOT/Cargo.toml" -p gateway-server -p gateway-bench

echo "== building h5i-gateway with bench/patches/h5i-tcp-nodelay.patch"
rm -rf "$SCRATCH/h5i-nodelay" && mkdir -p "$SCRATCH/h5i-nodelay"
git -C "$ROOT" archive HEAD | tar -x -C "$SCRATCH/h5i-nodelay"
if patch -s -p1 -d "$SCRATCH/h5i-nodelay" --dry-run <"$ROOT/bench/patches/h5i-tcp-nodelay.patch" >/dev/null 2>&1; then
  patch -s -p1 -d "$SCRATCH/h5i-nodelay" <"$ROOT/bench/patches/h5i-tcp-nodelay.patch"
  CARGO_TARGET_DIR=$SCRATCH/nodelay-target cargo build --release \
    --manifest-path "$SCRATCH/h5i-nodelay/Cargo.toml" -p gateway-server
else
  echo "   patch does not apply (already fixed?): skipping h5i-nodelay"
  rm -f "$SCRATCH/nodelay-target/release/h5i-gateway"
fi

echo "== building LiteLLM's Rust gateway ($LITELLM_COMMIT)"
if [ ! -f "$LITELLM_RUST_DIR/Cargo.toml" ]; then
  LITELLM_RUST_DIR=$SCRATCH/litellm-src/litellm-rust
  if [ ! -f "$LITELLM_RUST_DIR/Cargo.toml" ]; then
    rm -rf "$SCRATCH/litellm-src"
    git clone -q --filter=blob:none --no-checkout https://github.com/BerriAI/litellm "$SCRATCH/litellm-src"
    git -C "$SCRATCH/litellm-src" sparse-checkout set litellm-rust
    git -C "$SCRATCH/litellm-src" checkout -q "$LITELLM_COMMIT"
  fi
fi
CARGO_TARGET_DIR=$SCRATCH/litellm-rust-target cargo build --release \
  --manifest-path "$LITELLM_RUST_DIR/Cargo.toml" -p litellm-gateway \
  || echo "   litellm-gateway failed to build: it will be skipped"

echo "== installing LiteLLM (Python)"
bash "$ROOT/bench/setup-litellm.sh"

echo "== PostgreSQL image"
docker image inspect postgres:17 >/dev/null 2>&1 || docker pull -q postgres:17

echo "== recording the environment"
python3 - "$RESULTS/environment.json" "$ROOT" "$SCRATCH" <<'EOF'
import json, os, platform, subprocess, sys
out, root, scratch = sys.argv[1:]
def sh(*cmd):
    try:
        return subprocess.run(cmd, capture_output=True, text=True, check=True).stdout.strip()
    except Exception as e:
        return f"unavailable: {e}"
cpu = next((l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name")), "?")
mem = next((l.split()[1] for l in open("/proc/meminfo") if l.startswith("MemTotal")), "0")
env = {
    "cpu": cpu,
    "logical_cpus": os.cpu_count(),
    "memory_gb": round(int(mem) / 1024 / 1024),
    "kernel": platform.release(),
    "rustc": sh("rustc", "--version"),
    "python": sh(os.path.join(scratch, "venv/bin/python"), "--version"),
    "litellm": sh(os.path.join(scratch, "venv/bin/python"), "-c",
                  "import importlib.metadata as m; print(m.version('litellm'))"),
    "litellm_rust_commit": "f2118fc7670ba3fa736d9b8f4deef9077a45a720",
    "h5i_gateway_commit": sh("git", "-C", root, "rev-parse", "HEAD"),
    "postgres": sh("docker", "image", "inspect", "-f", "{{index .RepoDigests 0}}", "postgres:17"),
    "loadavg_at_start": os.getloadavg(),
}
json.dump(env, open(out, "w"), indent=2)
print(json.dumps(env, indent=2))
EOF

echo "== running the benchmark"
start=$(date +%s)
python3 "$ROOT/bench/driver.py" --out "$RESULTS" "$@"
echo "== benchmark took $(( $(date +%s) - start )) s"

echo "== rendering tables and charts"
python3 "$ROOT/bench/report.py" "$RESULTS"
