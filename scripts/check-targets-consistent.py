#!/usr/bin/env python3
"""Fail if unresolved `def ... : Prop` count changes unexpectedly.

This script is intended as a local CI guard: it recomputes Prop targets from
all top-level Lean files and compares against the canonical `docs` status file.

It is not a proof checker; it only validates that the repository's explicit
"target statements" remain a single controlled set.
"""

from __future__ import annotations

from pathlib import Path
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
STATUS_PATH = ROOT / "docs" / "current-target-status.json"

def scan_targets() -> set[str]:
    pat = re.compile(r"^def\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(.*\))?\s*:\s*Prop\s*:=" )
    names: set[str] = set()
    for path in sorted(ROOT.glob("*.lean")):
        for line in path.read_text(encoding="utf-8").splitlines():
            m = pat.match(line.strip())
            if m:
                names.add(m.group(1))
    return names


def load_status() -> set[str]:
    try:
        data = json.loads(STATUS_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return set()
    remaining = data.get("remaining_prop_targets", {})
    out: set[str] = set()
    for entries in remaining.values():
        for item in entries:
            out.add(item["name"])
    return out


def main() -> None:
    scanned = scan_targets()
    status = load_status()
    if not status:
        print(f"warning: unable to load status file {STATUS_PATH}")
    if scanned != status:
        only_in_scan = sorted(scanned - status)
        only_in_status = sorted(status - scanned)
        if only_in_scan:
            print("Targets in Lean files but not in status:")
            for x in only_in_scan:
                print(f"  + {x}")
        if only_in_status:
            print("Targets in status file but not in Lean files:")
            for x in only_in_status:
                print(f"  - {x}")
        print(f"scan={len(scanned)} status={len(status)}")
        sys.exit(1)
    print(f"target inventory consistent: {len(scanned)} targets")


if __name__ == "__main__":
    main()
