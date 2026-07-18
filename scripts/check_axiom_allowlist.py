#!/usr/bin/env python3

import re
import subprocess
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Set


ROOT = Path(__file__).resolve().parents[1]

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
    "PrimeNumberTheorem.ExplicitFormulaAux.norm_finiteNontrivialZeroSumWithMultiplicity_le_sqrt_mul_globalReciprocal_of_RH",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_sqrt_mul_log_sq_of_RH",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_nontrivialZero_re_le_one_sub_div_log_truncation",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq",
    "PrimeNumberTheorem.ExplicitFormulaAux.exists_nat_abs_chebyshevPsi0_sub_id_le_exp_sqrt_log",
    "PrimeNumberTheorem.ExplicitFormulaAux.chebyshevPsi0_sub_id_nat_isLittleO",
    "PrimeNumberTheorem.chebyshevPsi_sub_id_nat_isLittleO",
    "PrimeNumberTheorem.PNTForm3_proved",
    "PrimeNumberTheorem.pnt_forms_proved",
    "RiemannPNT.API.pnt_forms_proved",
    "PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log",
    "RiemannPNT.API.exists_abs_chebyshevPsi_sub_id_le_exp_neg_sqrt_log",
    "PrimeNumberTheorem.exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log",
    "RiemannPNT.API.exists_abs_primeCounting_sub_logIntegral_le_exp_neg_sqrt_log",
    "ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion",
    "ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_le_log_sq_on_inner_zeroFreeRegion",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_horizontal_inner_explicitFormulaContour_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_explicitFormulaApproxWithMultiplicity_sub_le_log_div_of_le_add_three",
    "PrimeNumberTheorem.exists_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le_div",
    "PrimeNumberTheorem.exists_uniform_nat_norm_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.vonMangoldtLSeriesNorm_le_two_div_mul_one_add_two_div",
    "PrimeNumberTheorem.exists_uniform_nat_norm_movingRight_truncated_neg_logDeriv_firstOrderPerron_sub_chebyshevPsi0_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_movingRight_horizontal_complete_explicitFormulaContour_difference_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_movingRight_firstOrderContourRemainder_le_horizontal_add_left",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_movingRight_truncatedExplicitFormula_sub_chebyshevPsi0_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_truncatedExplicitFormula_sub_contourRemainder_sub_chebyshevPsi0_le_div",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_integral_farLeft_explicit_le_log_div",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_norm_integral_farLeft_explicit_le_log_div",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_goodHeight_Icc_norm_firstOrderContourRemainder_le_horizontal_add_left",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_firstOrderContourRemainder_le_horizontal_add_left",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_goodHeight_Icc_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_horizontal_add_left",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_truncatedExplicitFormula_sub_chebyshevPsi0_le",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_nat_goodHeight_pow_five_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_log_nat_sq",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_nat_goodHeight_pow_five_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_nat_sq",
    "PrimeNumberTheorem.ExplicitFormulaResidues.tendsto_oddVerticalExplicitBound_atTop",
    "PrimeNumberTheorem.ExplicitFormulaAux.norm_finiteTrivialZeroSum_residues_sub_logTerm_le_geometric",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_goodHeight_Icc_exists_truncation_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_log_sq_div",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_goodHeight_Icc_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div",
    "PrimeNumberTheorem.deriv_riemannZeta_zero_div_riemannZeta_zero",
    "PrimeNumberTheorem.ExplicitFormulaTruncated.explicitFormulaTruncatedTarget_proved",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_nat_abs_chebyshevPsi0_sub_id_le_sqrt_mul_log_sq_of_RH",
    "PrimeNumberTheorem.ExplicitFormulaResidues.exists_nat_abs_chebyshevPsi_sub_id_le_sqrt_mul_log_sq_of_RH",
    "PrimeNumberTheorem.ExplicitFormulaResidues.RH_PsiErrorBound_of_RiemannHypothesis",
    "PrimeNumberTheorem.ExplicitFormulaResidues.RH_ThetaErrorBound_of_RiemannHypothesis",
    "PrimeNumberTheorem.ExplicitFormulaResidues.RH_PrimeCountingLiErrorBound_of_RiemannHypothesis",
    "PrimeNumberTheorem.ExplicitFormulaResidues.RH_ErrorBound_of_RiemannHypothesis",
    "PrimeNumberTheorem.ExplicitFormulaResidues.riemannHypothesis_iff_RH_PsiErrorBound",
    "PrimeNumberTheorem.logIntegral_mul_log_sub_integral_div_eq_sub_two",
    "PrimeNumberTheorem.chebyshevTheta_sub_id_eq_primeCountingLi_error",
    "PrimeNumberTheorem.RH_ThetaErrorBound_of_RH_PrimeCountingLiErrorBound",
    "PrimeNumberTheorem.riemannHypothesis_of_RH_PrimeCountingLiErrorBound",
    "PrimeNumberTheorem.rh_iff_optimal_error_proved",
    "RiemannPNT.API.RH_PsiErrorBound_of_riemannHypothesis",
    "RiemannPNT.API.RH_PrimeCountingLiErrorBound_of_riemannHypothesis",
    "RiemannPNT.API.riemannHypothesis_iff_RH_PsiErrorBound",
    "HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_phase_le_of_monotone_deriv",
    "HardyTheorem.OscillatoryIntegral.norm_integral_rpow_smul_cexp_fourierMellinPhase_le",
    "HardyTheorem.intervalIntegral_centeredFloorError_cpow_eq_bernoulliTwo",
    "HardyTheorem.exists_norm_intervalIntegral_periodizedBernoulli_two_mellin_le",
    "HardyTheorem.exists_norm_intervalIntegral_periodizedBernoulli_two_cpow_le",
    "HardyTheorem.exists_norm_integral_Ioi_periodizedBernoulli_two_cpow_le",
    "HardyTheorem.integral_Ioi_centeredFloorError_cpow_eq_bernoulliTwo",
    "HardyTheorem.exists_norm_mul_integral_Ioi_floorError_cpow_le",
    "HardyTheorem.exists_riemannZeta_first_approximation",
    "HardyTheorem.criticalLineZetaFirstApprox",
    "HardyTheorem.exists_integral_norm_riemannZeta_critical_line_ge_mul",
    "HardyTheorem.exists_abs_integral_hardyZ_le_rpow_three_quarters",
    "HardyTheorem.hardyZ_zero_set_not_isBounded",
    "HardyTheorem.hardy_zeros_unbounded_target_proved",
    "HardyTheorem.hardy_theorem_target_proved",
    "RiemannPNT.API.hardy_zeros_unbounded_target_proved",
    "HardyTheorem.norm_integral_inv_nat_cpow_criticalLine_le",
    "HardyTheorem.norm_integral_criticalLineDirichletTail_le",
    "HardyTheorem.norm_integral_criticalLineDirichletTail_cutoff_le",
    "HardyTheorem.norm_integral_criticalLineDirichletTail_cutoff_isLittleO",
    "ZeroFreeRegion.riemannZeta_eq_pole_add_floorError_integral_of_pos_re",
    "ZeroFreeRegion.riemannZeta_eq_dirichletPolynomial_add_pole_add_floorErrorTail",
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
        ["lake", "build", "Test.MultiplicityAxiomAudit"],
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
