#!/usr/bin/env python3
"""Regenerate docs/current-target-status.json from current Lean `def ... : Prop` targets."""

from __future__ import annotations

from pathlib import Path
from datetime import datetime
import json
import re

ROOT = Path(__file__).resolve().parents[1]
STATUS_PATH = ROOT / "docs" / "current-target-status.json"

# Match declarations like:
#   def foo : Prop :=
#   def foo (x : α) : Prop :=
PROP_DEF_RE = re.compile(
    r"^def\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:\(.*\))?\s*:\s*Prop\s*:="
)

# Manual chain map used by the remaining-work dashboard.
CHAIN_SUMMARY = [
    {
        "name": "Quantitative zero-free region",
        "target": "classical_zero_free_region",
        "status": "not proved in Lean",
        "next_step": "supply high-height zero-free/derivative estimates and keep compact patching lemmas already formalized",
    },
    {
        "name": "Explicit formula",
        "target": "explicit_formula_von_mangoldt",
        "status": "not proved in Lean",
        "next_step": "finish Perron-to-residue finite-height chain, then pass from contour sum to truncated/ψ0 limit",
    },
    {
        "name": "RH error equivalence",
        "target": "rh_iff_optimal_error",
        "status": "not proved in Lean",
        "next_step": "bridge explicit formula through RH-scale psi/theta error and convert to prime-counting Li error",
    },
    {
        "name": "Hardy theorem",
        "target": "hardy_theorem_target",
        "status": "not proved in Lean",
        "next_step": "prove Hardy signed moment asymptotics and tail-dominance then derive unbounded zeros",
    },
]


# Target-specific chain assignments for machine-readable dashboards.
TARGET_CHAIN_MAP = {
    "classical_zero_free_region": "Quantitative zero-free region",
    "vinogradov_korobov_zero_free_region": "Quantitative zero-free region",
    "PNTForm1": "RH error equivalence",
    "PNTForm2": "RH error equivalence",
    "PNTForm3": "RH error equivalence",
    "RH_PsiErrorBound": "RH error equivalence",
    "RH_ThetaErrorBound": "RH error equivalence",
    "RH_PrimeCountingLiErrorBound": "RH error equivalence",
    "RH_ErrorBound": "RH error equivalence",
    "rh_iff_optimal_error": "RH error equivalence",
    "explicit_formula_von_mangoldt": "Explicit formula",
    "integral_asymptotic_target": "Hardy theorem",
    "hardy_two_signed_moments_target": "Hardy theorem",
    "weightedIntegralOf_tail_dominates": "Hardy theorem",
    "hardy_theorem_target": "Hardy theorem",
    "hardy_zeros_unbounded_target": "Hardy theorem",
    "hardy_zeros_abs_unbounded_target": "Hardy theorem",
    "hardy_littlewood_lower_bound_target": "Hardy theorem",
    "selberg_zero_proportion_target": "Hardy theorem",
    "gamma_asymptotic_half_plus_it_target": "Hardy theorem",
    "theta_asymptotic_target": "Hardy theorem",
    "approximate_functional_equation_target": "Hardy theorem",
    "conrey_40_percent_zeros_on_critical_line_target": "Hardy theorem",
}


def _chain_of(target: str) -> str:
    """Assign a chain name to a target for dashboarding."""
    return TARGET_CHAIN_MAP.get(target, "Uncategorized")


def scan_targets() -> dict[str, list[str]]:
    """Return remaining target declarations grouped by source file basename."""
    remaining: dict[str, list[str]] = {}

    for path in sorted(ROOT.glob("*.lean")):
        file_targets: list[str] = []
        for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            m = PROP_DEF_RE.match(line.strip())
            if not m:
                continue
            file_targets.append(m.group(1))
        if file_targets:
            remaining[path.name] = file_targets

    return remaining


def load_previous_shapes() -> dict[str, str]:
    """Load existing target shapes so we do not overwrite handcrafted metadata."""
    if not STATUS_PATH.exists():
        return {}
    data = json.loads(STATUS_PATH.read_text(encoding="utf-8"))
    out: dict[str, str] = {}
    for entries in data.get("remaining_prop_targets", {}).values():
        for item in entries:
            out[item["name"]] = item.get("shape", "<unknown>")
    return out


def build_status(remaining: dict[str, list[str]]) -> dict[str, object]:
    all_count = sum(len(v) for v in remaining.values())
    previous_shapes = load_previous_shapes()

    # Keep the file keys short and namespace-like for readability.
    grouped: dict[str, list[dict[str, object]]] = {}
    for file, entries in remaining.items():
        file_key = file.removesuffix(".lean")
        grouped[file_key] = [
            {
                "name": item,
                "shape": previous_shapes.get(item, "<unknown>"),
                "depends_on": [],
            }
            for item in entries
        ]

    return {
        "timestamp": datetime.now().strftime("%Y-%m-%d"),
        "status": "not-yet-complete",
        "completed_without_sorry": True,
        "remaining_prop_targets": grouped,
        "chain_summary": CHAIN_SUMMARY,
        "chain_inventory": {
            chain: [
                item["name"]
                for file_targets in grouped.values()
                for item in file_targets
                if _chain_of(item["name"]) == chain
            ]
            for chain in sorted(set(_chain_of(item["name"]) for file_targets in grouped.values() for item in file_targets))
        },
        "all_prop_defs_count": all_count,
    }


def main() -> None:
    status = build_status(scan_targets())
    STATUS_PATH.write_text(json.dumps(status, ensure_ascii=False, indent=2) + "\n")
    print(f"wrote {STATUS_PATH.relative_to(ROOT)}")
    print(f"TOTAL: {status['all_prop_defs_count']}")


if __name__ == "__main__":
    main()
