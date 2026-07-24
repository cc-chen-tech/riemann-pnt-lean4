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
    "RiemannPNT.API.hardy_theorem_target_proved",
    "RiemannPNT.API.zeroCountOnCriticalLine_eq_distinct_ncard",
    "HardyTheorem.norm_integral_inv_nat_cpow_criticalLine_le",
    "HardyTheorem.norm_integral_criticalLineDirichletTail_le",
    "HardyTheorem.norm_integral_criticalLineDirichletTail_cutoff_le",
    "HardyTheorem.norm_integral_criticalLineDirichletTail_cutoff_isLittleO",
    "ZeroFreeRegion.riemannZeta_eq_pole_add_floorError_integral_of_pos_re",
    "ZeroFreeRegion.riemannZeta_eq_dirichletPolynomial_add_pole_add_floorErrorTail",
    "MathlibAux.intervalIntegral_mul_cexp_linear_eq_integration_by_parts",
    "MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_oscillatory",
    "MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_trivial",
    "MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_min",
    "HardyTheorem.hardyPhaseLinearizedSum_eq_commonPhase_mul_negLogPolynomial",
    "HardyTheorem.normSq_hardyPhaseLinearizedSum_eq_negLogPolynomial",
    "HardyTheorem.hardyPhaseNegLogPolynomial_eq_conj_positive",
    "HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le_min",
    "HardyTheorem.norm_deriv_hardyPhaseWindowCoeff_le_trivial",
    "HardyTheorem.sum_inv_nat_central_annulus_le",
    "HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_central_annulus_le",
    "HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_far_low_le",
    "HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_far_high_le",
    "HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_full_le",
    "HardyTheorem.sum_normSq_deriv_hardyPhaseWindowCoeff_full_le_mul",
    "MathlibAux.norm_integral_timeDependentLogOffDiagonal_le_of_measurable",
    "MathlibAux.integral_normSq_timeDependentLogPolynomial_le_of_measurable",
    "MathlibAux.continuousOn_timeDependentLogPolynomial",
    "HardyTheorem.integral_normSq_hardyPhaseLinearizedSum_le",
    "HardyTheorem.integral_normSq_hardyPhaseLinearizedSum_le_dyadic_mul",
    "HardyTheorem.exists_integral_normSq_hardyPhaseLinearizedSum_le_mul",
    "HardyTheorem.HasNegToPosLocalSignChangeAt.eq_zero",
    "HardyTheorem.card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_signChanges",
    "HardyTheorem.card_le_criticalLineOddZeroCount_of_pairwiseDisjoint_hardyZ_signChanges",
    "HardyTheorem.continuous_selbergMollifier_criticalLine",
    "HardyTheorem.selbergMoebiusWeight_mem_Icc",
    "HardyTheorem.abs_selbergMoebiusCoeff_le_one",
    "HardyTheorem.continuous_selbergMoebiusMollifiedHardyZ",
    "HardyTheorem.hasLocalSignChangeAt_hardyZ_of_mollified",
    "HardyTheorem.odd_analyticOrderNatAt_riemannZeta_of_mollified_localSignChange",
    "HardyTheorem.odd_analyticOrderNatAt_riemannZeta_of_selbergMoebius_localSignChange",
    "HardyTheorem.selbergMoebiusMollifier_criticalLine_eq_logExponentialPolynomial",
    "HardyTheorem.sum_normSq_selbergMoebiusCriticalLineCoeff_le",
    "HardyTheorem.integral_normSq_selbergMoebiusMollifier_le",
    "HardyTheorem.sum_normSq_selbergMoebiusCriticalLineCoeff_le_one_add_log",
    "HardyTheorem.integral_normSq_selbergMoebiusMollifier_le_one_add_log",
    "HardyTheorem.criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_convolutionSum",
    "HardyTheorem.abs_selbergMollifiedDirichletCoeff_le_card_divisorsAntidiagonal",
    "HardyTheorem.selbergMollifiedDirichletCoeff_eq_vonMangoldt_div_log",
    "HardyTheorem.sum_normSq_selbergMollifiedCriticalLineCoeff_le_one_add_log",
    "MathlibAux.integral_fourthMoment_logExponentialPolynomial_le",
    "MathlibAux.volume_slidingWindowMass_ge_le",
    "MathlibAux.volume_slidingWindowMass_gt_le",
    "MathlibAux.paleyZygmund_measure_lower_bound",
    "MathlibAux.paleyZygmund_smallMass_measure_upper_bound",
    "MathlibAux.paleyZygmund_sq_measure_lower_bound",
    "HardyTheorem.exists_hardyZ_localSignChange_of_selbergGoodStart",
    "HardyTheorem.selberg_odd_zero_proportion_target_of_mollified_good_window_bounds",
    "HardyTheorem.volume_selbergExcessiveSignedMassStarts_inter_Icc_le",
    "HardyTheorem.exists_integral_sq_selbergMoebiusMollifiedHardyZ_le",
    "HardyTheorem.exists_selbergMoebiusMollifiedZetaFirstApprox",
    "HardyTheorem.exists_selbergMoebiusAbsShortIntegral_ge_sub_shortDirichlet_coarse",
    "HardyTheorem.conj_selbergMoebiusMollifier_criticalLine_eq_neg",
    "HardyTheorem.criticalLineDirichletPolynomial_mul_mollifier_mul_conj_eq_exponentialPolynomial",
    "HardyTheorem.selbergMollifiedTripleFrequency_eq_iff_key_eq",
    "HardyTheorem.selbergMollifiedTriplePolynomial_eq_collectedPolynomial",
    "HardyTheorem.selbergMollifiedHardyPhasePolynomial_eq_collectedPolynomial",
    "HardyTheorem.selbergSqrtZetaEulerFactor_sq",
    "HardyTheorem.selbergSqrtZetaCoeff_mul_self",
    "HardyTheorem.selbergShortTaperedSqrtZeta_sq_mul_zeta_apply_prime",
    "HardyTheorem.selbergShortTaperedSqrtZeta_sq_mul_zeta_apply_prime_pow",
    "HardyTheorem.selbergShortTaperedSqrtZeta_collected_apply_of_le",
    "HardyTheorem.sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_fifteen_fourths",
    "HardyTheorem.sum_normSq_sliding_selbergSqrtZetaLowRangeDirichletCoeff_le",
    "HardyTheorem.sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_highRange",
    "HardyTheorem.integral_normSq_selbergSqrtZetaMollifiedShortDirichletPolynomial_le_gapSum",
    "HardyTheorem.exp_I_thetaModel_mul_criticalLinePolynomial_mul_mollifier_mul_conj_eq_collectedPhasePolynomial",
    "HardyTheorem.selbergMollifiedTripleKey_eq_one_iff",
    "HardyTheorem.selbergMollifiedTripleCollectedCoeff_one_eq_constantPairs",
    "HardyTheorem.selbergMollifiedTripleCollectedPolynomial_sub_constant_eq",
    "HardyTheorem.integral_normSq_selbergMollifiedTripleNonconstantShortIntegral_le",
    "MathlibAux.slidingExponentialPolynomialIntegral_eq",
    "MathlibAux.integral_normSq_slidingExponentialPolynomialIntegral_le",
    "MathlibAux.intervalIntegral_lagIntegral_add",
    "MathlibAux.abs_lagIntegral_le_of_forall_norm_le",
    "MathlibAux.norm_slidingExponentialCoefficient_le_min",
    "MathlibAux.sum_normSq_fiber_le_mul_sum_normSq",
    "MathlibAux.integral_normSq_negLogExponentialPolynomial_le_dyadic",
    "HardyTheorem.volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_of_shortDirichletL2",
    "HardyTheorem.criticalLineDirichletPolynomial_mul_mollifier_sq_eq_exponentialPolynomial",
    "HardyTheorem.selbergMollifiedShortDirichletPolynomial_eq_integral_expansion",
    "HardyTheorem.selbergShortDirichletTriplePolynomial_eq_collectedPolynomial",
    "HardyTheorem.selbergShortDirichletCollectedFrequency_injective_on_support",
    "HardyTheorem.selbergShortDirichletCollectedPolynomial_sub_one_eq",
    "HardyTheorem.selbergShortDirichletCollectedCoeff_eq_convolution",
    "HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_convolutionMajorant",
    "HardyTheorem.selbergShortDirichletCollectedCoeff_eq_zero_of_topRange",
    "HardyTheorem.sum_normSq_sliding_selbergShortDirichletCollectedCoeff_eq_effectiveSupport",
    "HardyTheorem.selbergShortCollectedDirichletConvolution_eq_lowRange",
    "HardyTheorem.norm_selbergShortDirichletCollectedCoeff_le_two_div_sqrt",
    "HardyTheorem.sum_normSq_sliding_selbergShortDirichletCollectedCoeff_lowRange_le_log",
    "HardyTheorem.sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_highRange",
    "HardyTheorem.sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_pairFiberHighRange",
    "HardyTheorem.sum_normSq_sliding_selbergShortDirichletCollectedCoeff_le_lowRange_add_pairFiberMinHighRange",
    "HardyTheorem.selbergShortDirichletCollectedPolynomial_sub_one_eq_effectiveSupport",
    "HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_dyadic",
    "HardyTheorem.integral_normSq_selbergShortDirichletCollectedPolynomial_sub_one_le_effectiveDyadic",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_le_pairFiberEnergy",
    "HardyTheorem.normSq_finset_sum_mul_le_sum_normSq_mul_sum_normSq",
    "HardyTheorem.normSq_selbergShortDirichletCollectedCoeff_le_weightedPairEnergy",
    "HardyTheorem.selbergShortDirichletTriples_eq_completeRangePairs_image",
    "HardyTheorem.selbergShortCollectedDirichletConvolution_eq_completeRange",
    "HardyTheorem.Icc_one_filter_dvd_eq_image_mul",
    "HardyTheorem.selbergShortLcmHarmonicKernel_one_eq_inv_mul_harmonic",
    "HardyTheorem.natCast_lcm_inv_eq_gcd_mul_inv_mul_inv",
    "HardyTheorem.natCast_gcd_eq_sum_totient_commonDivisors",
    "HardyTheorem.selbergShortDoubleMoebiusCoeff_eq_zero_of_pred_sq_lt",
    "HardyTheorem.sum_selbergShortDoubleMoebiusCoeff_eq_effectiveSupport",
    "HardyTheorem.sum_double_selbergShortDoubleMoebiusCoeff_eq_effectiveSupport",
    "MathlibAux.sum_reciprocal_lcm_quadratic_eq_totient_squares",
    "HardyTheorem.selbergShortDoubleMoebius_reciprocalLcmQuadratic_eq_totientSquares",
    "HardyTheorem.selbergShortDoubleMoebius_reciprocalLcmQuadratic_nonneg",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_effectiveDoubleLcmHarmonic",
    "HardyTheorem.sum_lcmHarmonic_quadratic_eq_divisorSquares",
    "HardyTheorem.sum_lcmHarmonic_quadratic_nonneg",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_divisorSquares",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_highRange_eq_sharpSupport",
    "HardyTheorem.selbergShortDoubleMoebiusCoeff_eq_convolution_sq",
    "HardyTheorem.selbergShortDoubleMoebiusDivisorSum_eq_zetaConvolution",
    "HardyTheorem.selbergShortCollectedDirichletConvolution_eq_primeCoefficient",
    "HardyTheorem.selbergShortDirichletCollectedCoeff_eq_primeCoefficient",
    "HardyTheorem.selbergShortCollectedDirichletConvolution_prime_le_neg_half",
    "HardyTheorem.sum_completeRangePairWeight_mul_kernel_eq_collected",
    "HardyTheorem.sum_completeRangeQuadrupleWeight_mul_kernel_eq_doubleCollected",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_eq_lcmKernel",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_lcmHarmonic",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_nonconstantRange_eq_lcmHarmonic_sub_one",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_doubleLcmHarmonic",
    "HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_nonconstantRange_eq_doubleLcmHarmonic_sub_one",
    "HardyTheorem.selbergMollifiedShortDirichletPolynomial_eq_slidingCollected",
    "HardyTheorem.integral_normSq_selbergMollifiedShortDirichletPolynomial_le_gapSum",
    "HardyTheorem.integral_normSq_selbergMollifiedShortDirichletPolynomial_le_energy",
    "HardyTheorem.volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_gapSum",
    "HardyTheorem.exists_volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_gapSum",
    "HardyTheorem.hardy_littlewood_lower_bound_target_proved",
    "HardyTheorem.hardy_littlewood_odd_lower_bound_target_proved",
    "RiemannPNT.API.hardyLittlewoodOddLowerBound_proved",
    "HardyTheorem.criticalLineOddZeroCount_two_mul_lower_bound_of_good_window_measure",
    "HardyTheorem.selberg_odd_zero_proportion_target_of_log_good_window_measure",
    "PrimeNumberTheorem.RiemannVonMangoldt.exists_eventually_riemannZeroCount_ge_selbergScale",
    "PrimeNumberTheorem.RiemannVonMangoldt.isNontrivialZero_criticalLineReflection",
    "PrimeNumberTheorem.RiemannVonMangoldt.analyticOrderNatAt_riemannZeta_conj_of_nontrivialZero",
    "PrimeNumberTheorem.RiemannVonMangoldt.analyticOrderNatAt_riemannZeta_criticalLineReflection_of_nontrivialZero",
    "PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount_eq_positiveCriticalLine_add_two_mul_zeroDensityCount",
    "PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount_add_halfMultiplicity_eq_criticalLine_add_two_mul_zeroDensityCount",
    "PrimeNumberTheorem.RiemannVonMangoldt.riemannZeroCount_eq_criticalLine_add_two_mul_zeroDensityCount",
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
