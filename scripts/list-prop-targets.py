#!/usr/bin/env python3
"""Print project-local Lean `def ... : Prop` declarations by category.

Usage:
  python3 scripts/list-prop-targets.py
  # emits mathematical targets, route interfaces, reusable predicates, and
  # unclassified Prop definitions.
"""

from __future__ import annotations

from target_inventory import ROOT, scan_prop_defs


def _print_group(title: str, records) -> None:
    print(title)
    for r in records:
        rel = r.file.relative_to(ROOT)
        true_tag = " body=True" if r.body_is_true else ""
        chain = f" chain={r.chain}" if r.chain else ""
        print(f"{rel}:{r.line_no}:{r.qualified_name}{true_tag}{chain}  |  {r.signature}")
    print(f"TOTAL {title}: {len(records)}")
    print()


records = scan_prop_defs()
groups = {
    "mathematical_target": [r for r in records if r.category == "mathematical_target"],
    "route_interface": [r for r in records if r.category == "route_interface"],
    "reusable_predicate": [r for r in records if r.category == "reusable_predicate"],
    "unclassified": [r for r in records if r.category == "unclassified"],
}

print("Prop declarations in project Lean sources:")
for name in ["mathematical_target", "route_interface", "reusable_predicate", "unclassified"]:
    _print_group(name, groups[name])

print(f"TOTAL scanned Prop defs: {len(records)}")
