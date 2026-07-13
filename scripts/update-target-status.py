#!/usr/bin/env python3
"""Regenerate docs/current-target-status.json from the Lean Prop inventory."""

from __future__ import annotations

from datetime import datetime
import json

from target_inventory import ROOT, MATH_TARGETS, scan_prop_defs


STATUS_PATH = ROOT / "docs" / "current-target-status.json"

CHAIN_SUMMARY = [
    {
        "name": "Quantitative zero-free region",
        "target": "vinogradov_korobov_zero_free_region",
        "status": "classical c/log region proved; stronger Vinogradov-Korobov target remains",
        "next_step": "develop exponential-sum estimates for the stronger Vinogradov-Korobov width",
    },
    {
        "name": "Explicit formula",
        "target": "explicit_formula_von_mangoldt",
        "status": "not proved in Lean",
        "next_step": "cover bounded gaps by the proved fixed-window weighted estimate and formalize floor/ceiling interpolation from the cofinal psi0 limit to all truncation heights",
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
        "next_step": "prove Hardy signed moment asymptotics; the main signed-moment bridge no longer needs tail-dominance",
    },
]


def load_previous_shapes() -> dict[str, str]:
    """Load existing target shapes so we do not overwrite handcrafted metadata."""
    if not STATUS_PATH.exists():
        return {}
    data = json.loads(STATUS_PATH.read_text(encoding="utf-8"))
    out: dict[str, str] = {}
    for entries in data.get("remaining_prop_targets", {}).values():
        for item in entries:
            if "qualified_name" in item:
                out[item["qualified_name"]] = item.get("shape", "<unknown>")
            out[item["name"]] = item.get("shape", "<unknown>")
    return out


def _namespace_of(qualified_name: str) -> str:
    if "." not in qualified_name:
        return "Global"
    return qualified_name.rsplit(".", 1)[0]


def build_status() -> dict[str, object]:
    records = scan_prop_defs(ROOT)
    math_targets = [r for r in records if r.category == "mathematical_target"]
    route_interfaces = [r for r in records if r.category == "route_interface"]
    reusable_predicates = [r for r in records if r.category == "reusable_predicate"]
    unclassified = [r for r in records if r.category == "unclassified"]
    previous_shapes = load_previous_shapes()

    grouped: dict[str, list[dict[str, object]]] = {}
    for record in math_targets:
        namespace = _namespace_of(record.qualified_name)
        grouped.setdefault(namespace, []).append(
            {
                "name": record.name,
                "qualified_name": record.qualified_name,
                "file": str(record.file.relative_to(ROOT)),
                "line": record.line_no,
                "shape": previous_shapes.get(
                    record.qualified_name,
                    previous_shapes.get(record.name, "<unknown>"),
                ),
                "depends_on": [],
            }
        )

    return {
        "timestamp": datetime.now().strftime("%Y-%m-%d"),
        "status": "not-yet-complete",
        "completed_without_sorry": True,
        "remaining_prop_targets": grouped,
        "route_interface_targets": [
            {
                "name": r.name,
                "qualified_name": r.qualified_name,
                "file": str(r.file.relative_to(ROOT)),
                "line": r.line_no,
                "chain": r.chain,
                "body": "True" if r.body_is_true else "real_statement",
            }
            for r in route_interfaces
        ],
        "reusable_predicates": [
            {
                "name": r.name,
                "qualified_name": r.qualified_name,
                "file": str(r.file.relative_to(ROOT)),
                "line": r.line_no,
            }
            for r in reusable_predicates
        ],
        "unclassified_prop_defs": [
            {
                "name": r.name,
                "qualified_name": r.qualified_name,
                "file": str(r.file.relative_to(ROOT)),
                "line": r.line_no,
            }
            for r in unclassified
        ],
        "chain_summary": CHAIN_SUMMARY,
        "chain_inventory": {
            chain: [
                r.name
                for r in math_targets
                if MATH_TARGETS[r.qualified_name] == chain
            ]
            for chain in sorted(set(MATH_TARGETS[r.qualified_name] for r in math_targets))
        },
        "mathematical_target_count": len(math_targets),
        "route_interface_count": len(route_interfaces),
        "route_interface_true_body_count": len([r for r in route_interfaces if r.body_is_true]),
        "reusable_predicate_count": len(reusable_predicates),
        "unclassified_prop_def_count": len(unclassified),
        "all_scanned_prop_defs_count": len(records),
    }


def main() -> None:
    status = build_status()
    STATUS_PATH.write_text(json.dumps(status, ensure_ascii=False, indent=2) + "\n")
    print(f"wrote {STATUS_PATH.relative_to(ROOT)}")
    print(
        "TOTAL: "
        f"{status['mathematical_target_count']} mathematical targets, "
        f"{status['route_interface_count']} route interfaces, "
        f"{status['reusable_predicate_count']} reusable predicates, "
        f"{status['unclassified_prop_def_count']} unclassified"
    )


if __name__ == "__main__":
    main()
