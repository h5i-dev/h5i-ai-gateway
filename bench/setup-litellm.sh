#!/usr/bin/env bash
# Installs the LiteLLM proxy (latest PyPI release, or $LITELLM_VERSION) into a
# venv under $BENCH_SCRATCH and generates its Prisma client (needed with
# DATABASE_URL; the first run downloads Node and the Prisma engines).
set -euo pipefail
SCRATCH=${BENCH_SCRATCH:-$(cd "$(dirname "$0")/.." && pwd)/target/bench}
VENV=$SCRATCH/venv
SPEC="litellm[proxy]${LITELLM_VERSION:+==$LITELLM_VERSION}"
mkdir -p "$SCRATCH/home"
# Keep Prisma's and pip's caches in scratch, as the driver does when it runs LiteLLM.
export HOME=$SCRATCH/home XDG_CACHE_HOME=$SCRATCH/xdg-cache PRISMA_BINARY_CACHE_DIR=$SCRATCH/prisma-cache
[ -x "$VENV/bin/python" ] || python3 -m venv "$VENV"
if ! "$VENV/bin/python" -c 'import litellm.proxy.proxy_server' 2>/dev/null; then
  "$VENV/bin/python" -m pip install -q --upgrade pip
  "$VENV/bin/python" -m pip install -q "$SPEC" prisma uvloop
fi
SITE=$("$VENV/bin/python" -c 'import litellm, os; print(os.path.dirname(litellm.__file__))')
if ! "$VENV/bin/python" -c 'from prisma import Prisma' 2>/dev/null; then
  PATH=$VENV/bin:$PATH "$VENV/bin/prisma" generate --schema "$SITE/proxy/schema.prisma" >/dev/null
fi
"$VENV/bin/python" -m pip show litellm | sed -n 2p
