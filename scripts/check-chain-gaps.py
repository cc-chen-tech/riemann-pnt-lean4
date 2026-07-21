#!/usr/bin/env python3
"""Validate the unresolved target/chain bookkeeping.

This script is intentionally strict: the repository currently tracks exactly four
main unresolved mathematical chains, and each unresolved `def ... : Prop`
target must be assigned to one of them.
"""

from __future__ import annotations

from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]
STATUS_PATH = ROOT / "docs" / "current-target-status.json"

EXPECTED_CHAINS = {
    "Quantitative zero-free region",
    "Explicit formula",
    "RH error equivalence",
    "Quantitative critical-line extensions",
    "de Bruijn-Newman constant",
}


def main() -> None:
    if not STATUS_PATH.exists():
        print(f"missing status file: {STATUS_PATH}")
        sys.exit(1)

    data = json.loads(STATUS_PATH.read_text(encoding="utf-8"))

    chain_summary = [item["name"] for item in data.get("chain_summary", [])]
    chain_inventory = data.get("chain_inventory", {})
    remaining = data.get("remaining_prop_targets", {})

    missing = [c for c in chain_summary if c not in EXPECTED_CHAINS]
    if missing:
        print(f"unexpected chain names in chain_summary: {missing}")
        sys.exit(1)

    if set(chain_summary) != EXPECTED_CHAINS:
        print("chain_summary does not match expected chain set")
        print(f"got: {sorted(chain_summary)}")
        print(f"exp: {sorted(EXPECTED_CHAINS)}")
        sys.exit(1)

    # Flatten unresolved target names from the remaining Prop declaration list.
    targets: set[str] = set()
    for items in remaining.values():
        for item in items:
            targets.add(item["name"])

    # Ensure every chain inventory entry is one of the tracked unresolved targets.
    covered: set[str] = set()
    for chain in chain_inventory:
        if chain not in EXPECTED_CHAINS:
            print(f"unexpected chain in chain_inventory: {chain}")
            sys.exit(1)
        for t in chain_inventory[chain]:
            if t not in targets:
                print(
                    f"chain_inventory references unknown target {chain}: {t}"
                )
                sys.exit(1)
            if t in covered:
                print(f"target appears in multiple chains: {t}")
                sys.exit(1)
            covered.add(t)

    if covered != targets:
        print("chain_inventory does not cover exactly all targets")
        print(f"missing: {sorted(targets - covered)}")
        print(f"extra: {sorted(covered - targets)}")
        sys.exit(1)

    print(f"chain-gap check passed: {len(targets)} targets in {len(EXPECTED_CHAINS)} chains")


if __name__ == "__main__":
    main()
