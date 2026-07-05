#!/usr/bin/env python3
"""Shared scanner for Lean `def ... : Prop` declarations.

The scanner is intentionally conservative: every project-local Prop-valued
definition must be classified as one of:

* mathematical target: a real unresolved proof goal;
* route interface: an intermediate API/roadmap predicate, often body `True`;
* reusable predicate: a normal predicate used by proved lemmas.

This prevents subdirectory interface placeholders from being hidden by a
top-level-only target count.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
IGNORED_DIRS = {".git", ".lake", ".worktrees", "vendor"}

DEF_START_RE = re.compile(
    r"^(?:noncomputable\s+)?def\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
NAMESPACE_RE = re.compile(r"^namespace\s+(.+)$")
END_RE = re.compile(r"^end(?:\s+(.+))?$")
PROP_SIGNATURE_RE = re.compile(r":\s*Prop\b.*:=")
TRUE_BODY_RE = re.compile(r":=\s*True\b")


MATH_TARGETS = {
    "ZeroFreeRegion.classical_zero_free_region": "Quantitative zero-free region",
    "vinogradov_korobov_zero_free_region": "Quantitative zero-free region",
    "PrimeNumberTheorem.PNTForm1": "RH error equivalence",
    "PrimeNumberTheorem.PNTForm2": "RH error equivalence",
    "PrimeNumberTheorem.PNTForm3": "RH error equivalence",
    "PrimeNumberTheorem.RH_PsiErrorBound": "RH error equivalence",
    "PrimeNumberTheorem.RH_ThetaErrorBound": "RH error equivalence",
    "PrimeNumberTheorem.RH_PrimeCountingLiErrorBound": "RH error equivalence",
    "PrimeNumberTheorem.RH_ErrorBound": "RH error equivalence",
    "PrimeNumberTheorem.rh_iff_optimal_error": "RH error equivalence",
    "PrimeNumberTheorem.explicit_formula_von_mangoldt": "Explicit formula",
    "HardyTheorem.integral_asymptotic_target": "Hardy theorem",
    "HardyTheorem.hardy_two_signed_moments_target": "Hardy theorem",
    "HardyTheorem.hardy_theorem_target": "Hardy theorem",
    "HardyTheorem.hardy_zeros_unbounded_target": "Hardy theorem",
    "HardyTheorem.hardy_zeros_abs_unbounded_target": "Hardy theorem",
    "HardyTheorem.hardy_littlewood_lower_bound_target": "Hardy theorem",
    "HardyTheorem.selberg_zero_proportion_target": "Hardy theorem",
    "HardyTheorem.Details.gamma_asymptotic_half_plus_it_target": "Hardy theorem",
    "HardyTheorem.Details.theta_asymptotic_target": "Hardy theorem",
    "HardyTheorem.Details.approximate_functional_equation_target": "Hardy theorem",
    "KnownResults.conrey_40_percent_zeros_on_critical_line_target": "Hardy theorem",
}

ROUTE_INTERFACES = {
    "PrimeNumberTheorem.ExplicitFormulaConversePowerTarget": "Explicit formula",
    "PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedTarget": "Explicit formula",
    "PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedConverseRoute": "Explicit formula",
    "MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum": "Explicit formula",
    "HardyTheorem.AFE.zeta_critical_afe_target": "Hardy theorem",
    "RiemannExplorer.Conrey40.conrey_40_percent_zeros_on_critical_line_target": "Hardy theorem",
}

REUSABLE_PREDICATES = {
    "HardyTheorem.weightedIntegralOf_tail_dominates",
    "PrimeNumberTheorem.ExplicitFormulaAux.goodHeight",
}


@dataclass(frozen=True)
class PropDef:
    file: Path
    line_no: int
    name: str
    qualified_name: str
    signature: str
    body_is_true: bool
    category: str
    chain: str | None


def _project_lean_files(root: Path) -> list[Path]:
    out: list[Path] = []
    for path in root.rglob("*.lean"):
        if any(part in IGNORED_DIRS for part in path.relative_to(root).parts):
            continue
        out.append(path)
    return sorted(out)


def _strip_comments(lines: list[str]) -> list[tuple[int, str]]:
    """Remove Lean line comments and block comments for declaration scanning."""
    out: list[tuple[int, str]] = []
    depth = 0
    for line_no, line in enumerate(lines, start=1):
        i = 0
        kept = ""
        while i < len(line):
            if depth > 0:
                end = line.find("-/", i)
                if end == -1:
                    i = len(line)
                else:
                    depth -= 1
                    i = end + 2
                continue

            line_comment = line.find("--", i)
            block_comment = line.find("/-", i)
            if line_comment != -1 and (block_comment == -1 or line_comment < block_comment):
                kept += line[i:line_comment]
                break
            if block_comment != -1:
                kept += line[i:block_comment]
                depth += 1
                i = block_comment + 2
                continue
            kept += line[i:]
            break
        out.append((line_no, kept))
    return out


def _classify(qualified_name: str) -> tuple[str, str | None]:
    if qualified_name in MATH_TARGETS:
        return "mathematical_target", MATH_TARGETS[qualified_name]
    if qualified_name in ROUTE_INTERFACES:
        return "route_interface", ROUTE_INTERFACES[qualified_name]
    if qualified_name in REUSABLE_PREDICATES:
        return "reusable_predicate", None
    return "unclassified", None


def _body_is_true(normalized_signature: str, stripped_lines: list[tuple[int, str]], idx: int) -> bool:
    if TRUE_BODY_RE.search(normalized_signature):
        return True
    if not normalized_signature.endswith(":="):
        return False
    for _, line in stripped_lines[idx + 1:]:
        stripped = line.strip()
        if not stripped:
            continue
        return stripped == "True" or stripped.startswith("True ")
    return False


def scan_prop_defs(root: Path = ROOT) -> list[PropDef]:
    records: list[PropDef] = []
    for path in _project_lean_files(root):
        try:
            stripped_lines = _strip_comments(path.read_text(encoding="utf-8").splitlines())
        except OSError:
            continue

        namespace_stack: list[str] = []
        pending: tuple[int, str, str] | None = None

        for idx, (line_no, line) in enumerate(stripped_lines):
            stripped = line.strip()
            if not stripped:
                continue

            ns = NAMESPACE_RE.match(stripped)
            if pending is None and ns:
                namespace_stack.extend(ns.group(1).split("."))
                continue

            end = END_RE.match(stripped)
            if pending is None and end:
                if namespace_stack:
                    namespace_stack.pop()
                continue

            if pending is None:
                m = DEF_START_RE.match(stripped)
                if not m:
                    continue
                pending = (line_no, m.group(1), stripped)
            else:
                start_line, name, acc = pending
                pending = (start_line, name, f"{acc} {stripped}")

            start_line, name, acc = pending
            if ":=" not in acc:
                continue

            normalized = " ".join(acc.split())
            if PROP_SIGNATURE_RE.search(normalized):
                qualified = ".".join([*namespace_stack, name])
                category, chain = _classify(qualified)
                records.append(
                    PropDef(
                        file=path,
                        line_no=start_line,
                        name=name,
                        qualified_name=qualified,
                        signature=normalized,
                        body_is_true=_body_is_true(normalized, stripped_lines, idx),
                        category=category,
                        chain=chain,
                    )
                )
            pending = None

    return records


def mathematical_targets(root: Path = ROOT) -> list[PropDef]:
    return [r for r in scan_prop_defs(root) if r.category == "mathematical_target"]


def route_interfaces(root: Path = ROOT) -> list[PropDef]:
    return [r for r in scan_prop_defs(root) if r.category == "route_interface"]


def reusable_predicates(root: Path = ROOT) -> list[PropDef]:
    return [r for r in scan_prop_defs(root) if r.category == "reusable_predicate"]


def unclassified_prop_defs(root: Path = ROOT) -> list[PropDef]:
    return [r for r in scan_prop_defs(root) if r.category == "unclassified"]
