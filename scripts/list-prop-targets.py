#!/usr/bin/env python3
"""Print unresolved Lean target declarations of form `def ... : Prop :=`.

Usage:
  python3 scripts/list-prop-targets.py
  # emits each declaration name and a total count.
"""

from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
pat = re.compile(
    r"^def\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(.*\))?\s*:\s*Prop\s*:="
)

# `def ... : Prop` is also useful for reusable predicates.  These are not
# unresolved theorem targets and should not be counted as remaining proof gaps.
NON_TARGET_PROP_PREDICATES = {
    "weightedIntegralOf_tail_dominates",
}

entries = []
for path in sorted(root.glob("*.lean")):
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        m = pat.match(line.strip())
        if m and m.group(1) not in NON_TARGET_PROP_PREDICATES:
            entries.append((path.name, i, m.group(1), line.strip()))

print("Unresolved Prop declarations in Lean sources:")
for file, line_no, name, source in entries:
    print(f"{file}:{line_no}:{name}  |  {source}")
print(f"TOTAL: {len(entries)}")
