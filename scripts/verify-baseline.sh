#!/usr/bin/env bash

set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"

cd "$ROOT"

printf '%s\n' "[verify-baseline] lake build"
lake build

printf '%s\n' "[verify-baseline] scanning for sorry/admit/axiom"
if rg -n "\bsorry\b|\badmit\b|\baxiom\b" *.lean; then
  echo "[verify-baseline] unexpected placeholder found"
  exit 1
fi

printf '%s\n' "[verify-baseline] checking target inventory consistency"
python3 scripts/check-targets-consistent.py

printf '%s\n' "[verify-baseline] target inventory and build are consistent"
