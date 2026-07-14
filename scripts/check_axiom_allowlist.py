#!/usr/bin/env python3

import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Set


ROOT = Path(__file__).resolve().parents[1]
AUDIT_FILE = ROOT / "Test" / "MultiplicityAxiomAudit.lean"

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
EXPECTED_DECLARATIONS = {
    "PrimeNumberTheorem.analyticOrderNatAt_riemannZeta_one_sub_of_nontrivialZero",
    "PrimeNumberTheorem.norm_multiplicity_zero_contribution_le_div_height",
    "PrimeNumberTheorem.sum_analyticOrderNatAt_riemannZeta_le_finsum_divisor_closedBall",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_localZeroMultiplicity_le_log_bound",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_cofinal_explicitFormulaApproxWithMultiplicity_tendsto",
    "PrimeNumberTheorem.ExplicitFormulaResidues.explicit_formula_von_mangoldt_proved",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_card_nontrivialZerosFinset_le_mul_log",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq",
}

REPORT_RE = re.compile(
    r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",
    flags=re.MULTILINE,
)


def parse_axiom_report(output: str) -> Dict[str, Set[str]]:
    reports: Dict[str, Set[str]] = {}
    for declaration, raw_axioms in REPORT_RE.findall(output):
        axioms = {
            axiom.strip()
            for axiom in raw_axioms.replace("\n", " ").split(",")
            if axiom.strip()
        }
        reports[declaration] = axioms
    return reports


def validate_axioms(
    reports: Dict[str, Set[str]],
    *,
    expected_declarations: Iterable[str],
    allowed_axioms: Set[str],
) -> List[str]:
    expected = set(expected_declarations)
    errors = [
        f"missing axiom report for {declaration}"
        for declaration in sorted(expected - reports.keys())
    ]
    for declaration in sorted(expected & reports.keys()):
        unexpected = reports[declaration] - allowed_axioms
        if unexpected:
            errors.append(
                f"{declaration} uses unexpected axioms: {', '.join(sorted(unexpected))}"
            )
    return errors


def main() -> int:
    completed = subprocess.run(
        ["lake", "env", "lean", str(AUDIT_FILE)],
        cwd=ROOT,
        text=True,
        capture_output=True,
    )
    output = completed.stdout + completed.stderr
    if completed.returncode != 0:
        sys.stderr.write(output)
        return completed.returncode

    reports = parse_axiom_report(output)
    errors = validate_axioms(
        reports,
        expected_declarations=EXPECTED_DECLARATIONS,
        allowed_axioms=ALLOWED_AXIOMS,
    )
    if errors:
        for error in errors:
            print(f"[axiom-allowlist] {error}", file=sys.stderr)
        return 1

    print(
        "[axiom-allowlist] checked "
        f"{len(EXPECTED_DECLARATIONS)} declarations; only standard axioms are used"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
