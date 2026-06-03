#!/usr/bin/env python3
"""Scan the main checkout and nearby Codex worktrees for unresolved `def ... : Prop` names.

The goal is to quickly detect whether another worktree has solved or introduced
target declarations that differ from the authoritative main checkout set.
"""

from __future__ import annotations

from pathlib import Path
from subprocess import check_output
import re
import sys


ROOT = Path(__file__).resolve().parents[1]
WORKTREE_ROOT = Path.home() / ".config" / "superpowers" / "worktrees" / "riemann-pnt-lean4"

PAT = re.compile(r"^def\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(.*\))?\s*:\s*Prop\s*:=")


def scan_targets(path: Path) -> set[str]:
    """Collect top-level unresolved `def ... : Prop` declarations in `.lean` files."""
    targets: set[str] = set()
    for file in sorted(path.glob("*.lean")):
        try:
            lines = file.read_text(encoding="utf-8").splitlines()
        except OSError:
            continue
        for line in lines:
            m = PAT.match(line.strip())
            if m:
                targets.add(m.group(1))
    return targets


def scan_worktree(path: Path) -> tuple[set[str], str]:
    """Collect target declarations for a worktree path."""
    if not path.exists():
        return set(), str(path)
    return scan_targets(path), str(path)


def branch_name(path: Path) -> str:
    """Best-effort branch name for display (falls back to path name)."""
    try:
        out = check_output(["git", "-C", str(path), "rev-parse", "--abbrev-ref", "HEAD"], text=True)
        return out.strip()
    except Exception:
        return path.name


def main() -> int:
    base_targets = scan_targets(ROOT)
    print(f"[scan] base checkout: {ROOT} ({len(base_targets)} targets)")

    if not WORKTREE_ROOT.exists():
        print(f"[scan] worktree root missing: {WORKTREE_ROOT}")
        return 0

    had_diff = False
    for wt in sorted(p for p in WORKTREE_ROOT.iterdir() if p.is_dir()):
        wt_targets, wt_path = scan_worktree(wt)
        if wt_targets == base_targets:
            print(f"[scan] {wt.name}: same target set ({len(wt_targets)}) [{branch_name(wt)}]")
            continue

        had_diff = True
        print(f"[scan] {wt.name}: target mismatch [{branch_name(wt)}]")
        extra = sorted(wt_targets - base_targets)
        missing = sorted(base_targets - wt_targets)
        if extra:
            print("  + only here:")
            for t in extra:
                print(f"    + {t}")
        if missing:
            print("  - only base:")
            for t in missing:
                print(f"    - {t}")

    if had_diff:
        print("[scan] mismatches found; no automatic merge performed")
        return 1

    print("[scan] all scanned worktrees match target declarations")
    return 0


if __name__ == "__main__":
    sys.exit(main())
