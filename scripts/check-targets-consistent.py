#!/usr/bin/env python3
"""Fail if project-local `def ... : Prop` bookkeeping changes unexpectedly.

This script is intended as a local CI guard: it recursively scans project Lean
files, requires every Prop-valued definition to be classified, and compares the
mathematical target set against the canonical `docs` status file.

It is not a proof checker; it only validates that the repository's explicit
"target statements" and interface placeholders remain controlled.
"""

from __future__ import annotations

from pathlib import Path
import json
import sys

from target_inventory import ROOT, scan_prop_defs

ROOT = Path(__file__).resolve().parents[1]
STATUS_PATH = ROOT / "docs" / "current-target-status.json"


def scan_targets() -> set[str]:
    return {
        record.qualified_name
        for record in scan_prop_defs(ROOT)
        if record.category == "mathematical_target"
    }


def load_status() -> set[str]:
    try:
        data = json.loads(STATUS_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return set()
    remaining = data.get("remaining_prop_targets", {})
    out: set[str] = set()
    for namespace, entries in remaining.items():
        for item in entries:
            if "qualified_name" in item:
                out.add(item["qualified_name"])
            else:
                out.add(f"{namespace}.{item['name']}")
    return out


def main() -> None:
    records = scan_prop_defs(ROOT)
    unclassified = [r for r in records if r.category == "unclassified"]
    if unclassified:
        print("Unclassified Prop definitions in Lean files:")
        for r in unclassified:
            rel = r.file.relative_to(ROOT)
            print(f"  ! {rel}:{r.line_no}:{r.qualified_name}  |  {r.signature}")
        print("Classify these as mathematical targets, route interfaces, or reusable predicates.")
        sys.exit(1)

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

    route_interfaces = [r for r in records if r.category == "route_interface"]
    reusable_predicates = [r for r in records if r.category == "reusable_predicate"]
    true_interfaces = [r for r in route_interfaces if r.body_is_true]
    print(
        "target inventory consistent: "
        f"{len(scanned)} mathematical targets, "
        f"{len(route_interfaces)} route interfaces "
        f"({len(true_interfaces)} body=True), "
        f"{len(reusable_predicates)} reusable predicates"
    )


if __name__ == "__main__":
    main()
