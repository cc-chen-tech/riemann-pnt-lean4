#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

cd "$ROOT"

printf '%s\n' "[verify-baseline] lake build"
lake build

printf '%s\n' "[verify-baseline] scanning for sorry/admit/axiom"
if rg -n "^[[:space:]]*(sorry|admit|axiom)\b|:= by[[:space:]]*(sorry|admit)\b|\bby[[:space:]]+(sorry|admit)\b" \
  --glob '*.lean' \
  --glob '!vendor/**' \
  --glob '!.lake/**' \
  --glob '!.worktrees/**'; then
  echo "[verify-baseline] unexpected placeholder found"
  exit 1
fi

printf '%s\n' "[verify-baseline] checking target inventory consistency"
python3 scripts/check-targets-consistent.py

printf '%s\n' "[verify-baseline] checking chain-gap bookkeeping"
python3 scripts/check-chain-gaps.py

printf '%s\n' "[verify-baseline] enforcing theorem axiom allowlist"
python3 scripts/check_axiom_allowlist.py

printf '%s\n' "[verify-baseline] scanning worktrees for target-set mismatches (informational)"
if ! python3 scripts/scan-worktrees-targets.py; then
  echo "[verify-baseline] warning: worktree target sets differ; inspect output before merging"
fi

printf '%s\n' "[verify-baseline] target inventory and build are consistent"
