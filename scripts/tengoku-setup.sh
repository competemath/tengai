#!/usr/bin/env bash
# Put Tengoku at the commit in tengoku.pin, with its compiled cache, in .tengoku (where lakefile.toml finds it).
#
#   scripts/tengoku-setup.sh            # clone/fetch Tengoku, check out the pin, unpack the cache, replay-build Tengoku.All
#   scripts/tengoku-setup.sh --latest   # first move the pin to the commit of the newest published cache
#
# Nothing of Tengoku is compiled here: the cache is Tengoku's own (scripts/cache.sh get, attested when `gh` is logged in) and the
# replay build only confirms it covers the tree. On a laptop this is several GB; the CI job and the drip workflow run it on a runner.
set -euo pipefail
cd "$(dirname "$0")/.."

REPO="https://github.com/competemath/tengoku"
POINTER="$REPO/releases/download/cache-latest/cache-latest.json"

if [ "${1:-}" = "--latest" ]; then
  json="$(curl --proto '=https' --tlsv1.2 -fsSL "$POINTER")"
  commit="$(python3 -c 'import json, sys; print(json.loads(sys.argv[1])["commit"])' "$json")"
  [[ "$commit" =~ ^[0-9a-f]{40}$ ]] || { echo "the published cache pointer names no commit" >&2; exit 1; }
  printf '%s\n' "$commit" > tengoku.pin
  echo "tengoku.pin -> $commit"
fi

pin="$(tr -d '[:space:]' < tengoku.pin)"
[[ "$pin" =~ ^[0-9a-f]{40}$ ]] || { echo "tengoku.pin must hold a full 40-character commit" >&2; exit 1; }

if [ ! -d .tengoku/.git ]; then
  git clone -q --filter=blob:none "$REPO" .tengoku
fi
git -C .tengoku fetch -q origin
git -C .tengoku checkout -q -f "$pin"

export TENGOKU_VERIFY="${TENGOKU_VERIFY:-warn}"
(
  cd .tengoku
  scripts/cache.sh get "$pin" 2>&1 | tail -5
  # replay only: if the cache does not cover the pinned tree this fails instead of compiling hours of mathematics
  lake build --no-build Tengoku.All 2>&1 | tail -3
)
echo "Tengoku is at $pin"
