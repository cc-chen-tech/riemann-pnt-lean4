# Unproved Target Statements and Missing Chains

This file is the authoritative classification of `def ... : Prop` statements
(as of `2026-07-15`) in this Lean checkout.  It separates genuinely unproved
mathematical targets from reusable predicates that already have theorem-level
proofs.

## How to Read This Inventory

This file measures **internal proof progress** only.  It answers questions like:

- which Lean declarations are still roadmap targets;
- which verified declarations currently anchor each missing chain;
- which analytic inputs would let a target be promoted to a proved theorem.

It does **not** answer the external SOTA question.  A smaller target count does
not imply that this repository is close to proving RH or a prime error with a
power saving below exponent `2/3`.  The ordinary PNT status instead rests on the checked declarations
`PNTForm1_proved`, `PNTForm2_proved`, and `PNTForm3_proved`.  External academic
positioning must be checked separately against Isabelle/HOL PNT, HOL Light PNT, Lean
`PrimeNumberTheoremAnd`, Mathlib's zeta/L-function infrastructure, and current
Lean repositories at the time of submission.

The safe project positioning is:

```text
Lean 4 formalization of de la Vallee Poussin 3-4-1/Jensen machinery,
the classical c/log zero-free region, and an ordinary PNT derivation
```

## Target count

- `HardyTheorem` namespace: 7
- `HardyTheorem.Details` namespace: 3
- `PrimeNumberTheorem` namespace: 7
- `KnownResults` namespace: 1
- `ZeroFreeRegion` namespace: 0
- global namespace: 1

Total: **19**.

For the chain accounting:

- Quantitative zero-free region chain: 1
- Explicit formula chain: 0 (the principal-value target is proved; the separate
  quantitative truncated-error statement remains a route interface)
- RH/prime-counting error chain: 7
- Hardy theorem chain: 11 (7 in `HardyTheorem`, 3 in `HardyTheorem.Details`,
  1 in `KnownResults`)

## Chain 1: Quantitative zero-free region

### Target declarations

- `vinogradov_korobov_zero_free_region`

### Current verified anchor theorems

- `ZeroFreeRegion.log_deriv_zeta_re_series`
- `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`
- `ZeroFreeRegion.residue_bounds`
- `ZeroFreeRegion.classical_zero_free_region_compact`
- `ZeroFreeRegion.classical_zero_free_region_proved`
- `ZeroFreeRegion.log_deriv_zeta_pos_real`
- `ZeroFreeRegion.log_deriv_zeta_antitone`
- `ZeroFreeRegion.compact_patch_classical_zero_free_region_at_three`
- `ZeroFreeRegion.classical_zero_free_region_high_height`
- `ZeroFreeRegion.classical_zero_free_region_iff_high_height`
- `ZeroFreeRegion.classical_zero_free_region_iff_high_height_at_three`
- `ZeroFreeRegion.vinogradov_korobov_high_height_classical_zero_free_region`
- `ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov`

### Missing mathlib/analytic infrastructure

1. Vinogradov-Korobov exponential-sum estimates;
2. the corresponding stronger zeta growth and logarithmic-derivative bounds;
3. assembly of those bounds into the `2/3`-power logarithmic zero-free width.

---

## Chain 2: Explicit formula

### Unproved target declarations

None.  `PrimeNumberTheorem.explicit_formula_von_mangoldt` remains a reusable
predicate, but `ExplicitFormulaResidues.explicit_formula_von_mangoldt_proved`
discharges it for every `x >= 2`.

### Current verified anchor theorems

- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`
- `PrimeNumberTheorem.zero_contribution`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`
- `PrimeNumberTheorem.vonMangoldt_eq_mathlib`

The following declarations are legacy unweighted compatibility bridges. They
remain useful bookkeeping references but do not prove or unfold the current
multiplicity-aware target:

- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_error_tendsto_zero`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_error_isLittleO_one`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_re_im_tendsto`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_re_im_error_tendsto_zero`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_unweighted_iff_re_im_error_isLittleO_one`

### Completed principal-value chain

1. `norm_explicitFormulaApproxWithMultiplicity_sub_le_two_localWindows` covers
   each bounded gap by two fixed-width multiplicity-weighted windows;
2. the proof uses `floor ((t - 5) / 2)` to associate every sufficiently large
   real height with a selected cofinal height;
3. `explicit_formula_von_mangoldt_proved` combines those estimates with the
   cofinal `psi0` limit and closes the all-height symmetric principal-value
   predicate.  The quantitative truncated-error route remains separate.

---

## Chain 3: RH ⇔ prime-counting error

### Remaining target declarations

- `PrimeNumberTheorem.RH_PsiErrorBound`
- `PrimeNumberTheorem.RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound`

### Current verified anchor theorems

- `PrimeNumberTheorem.PNTForm3_proved`
- `PrimeNumberTheorem.PNTForm2_proved`
- `PrimeNumberTheorem.PNTForm1_proved`
- `PrimeNumberTheorem.pnt_forms_proved`
- `PrimeNumberTheorem.pnt_forms_equivalent`
- `PrimeNumberTheorem.PNTForm1_iff_PNTForm2`
- `PrimeNumberTheorem.PNTForm2_iff_PNTForm1`
- `PrimeNumberTheorem.PNTForm2_iff_PNTForm3`
- `PrimeNumberTheorem.PNTForm3_iff_PNTForm2`
- `PrimeNumberTheorem.PNTForm1_iff_PNTForm3`
- `PrimeNumberTheorem.PNTForm3_iff_PNTForm1`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`
- `PrimeNumberTheorem.primeCounting_eq_mathlib`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`
- `PrimeNumberTheorem.RH_PsiErrorBound_iff_RH_ThetaErrorBound`
- `PrimeNumberTheorem.theta_error_div_log_isBigO_sqrt_mul_log`
- `PrimeNumberTheorem.theta_error_integral_isBigO_sqrt_mul_log`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PsiErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals`
- `PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound`
- `PrimeNumberTheorem.rh_iff_pointwise_error_iff`
- `PrimeNumberTheorem.rh_iff_optimal_error_of_pointwise_implications`
- `PrimeNumberTheorem.RH_ErrorBound_of_rh_iff_optimal_error`
- `PrimeNumberTheorem.RiemannHypothesis_of_rh_iff_pointwise_error`
- `PrimeNumberTheorem.primeCounting_logIntegral_finite_interval_bound`
- `PrimeNumberTheorem.psiPowerErrorBound_of_RH_PsiErrorBound_of_half_lt`
- `ZeroFreeRegion.nontrivial_zero_re_le_half_of_RH_PsiErrorBound`
- `ZeroFreeRegion.half_le_nontrivial_zero_re_of_RH_PsiErrorBound`
- `ZeroFreeRegion.riemannHypothesis_of_RH_PsiErrorBound`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_PsiErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_ThetaErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_PrimeCountingLiErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.RH_ErrorBound_of_RiemannHypothesis`
- `PrimeNumberTheorem.ExplicitFormulaResidues.riemannHypothesis_iff_RH_PsiErrorBound`
- `PrimeNumberTheorem.logIntegral_mul_log_sub_integral_div_eq_sub_two`
- `PrimeNumberTheorem.chebyshevTheta_sub_id_eq_primeCountingLi_error`
- `PrimeNumberTheorem.RH_ThetaErrorBound_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_PsiErrorBound_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.riemannHypothesis_of_RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.rh_iff_optimal_error_proved`

### Current boundary

The implication chain is complete in both directions:

```text
RH -> RH_PsiErrorBound -> RH_ThetaErrorBound -> RH_PrimeCountingLiErrorBound
RH_PrimeCountingLiErrorBound -> RH_ThetaErrorBound -> RH_PsiErrorBound -> RH
```

Thus `rh_iff_optimal_error` is a proved reusable predicate.  This is an
equivalence theorem, not an unconditional proof of RH or any equivalent error
predicate; those individual propositions remain mathematical targets.

---

## Chain 4: Hardy theorem

### Target declarations

- `HardyTheorem.integral_asymptotic_target`
- `HardyTheorem.hardy_two_signed_moments_target`
- `HardyTheorem.hardy_theorem_target`
- `HardyTheorem.hardy_zeros_unbounded_target`
- `HardyTheorem.hardy_zeros_abs_unbounded_target`
- `HardyTheorem.hardy_littlewood_lower_bound_target`
- `HardyTheorem.selberg_zero_proportion_target`
- `HardyTheorem.Details.gamma_asymptotic_half_plus_it_target`
- `HardyTheorem.Details.theta_asymptotic_target`
- `HardyTheorem.Details.approximate_functional_equation_target`
- `KnownResults.conrey_40_percent_zeros_on_critical_line_target`

### Current verified anchor theorems

- `HardyTheorem.hardyZ_zero_iff_zeta_zero`
- `HardyTheorem.hardyZ_eventually_const_sign_of_finite_zeros`
- `HardyTheorem.weightedIntegralOf_neg`
- `HardyTheorem.hardy_two_signed_moments_target_iff_integral_asymptotic_one_two`
- `HardyTheorem.hardy_theorem_target_of_two_signed_moments`
- `HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two`
- `HardyTheorem.exists_zero_on_critical_line_of_hardy_theorem_target`
- `HardyTheorem.exists_zero_on_critical_line_of_two_signed_moments`
- `HardyTheorem.exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `HardyTheorem.hardy_theorem_target_of_two_signed_moments_and_tail_dominance`
- `HardyTheorem.hardyZ_continuous`
- `HardyTheorem.critical_line_zeta_zero_neg_height`
- `HardyTheorem.hardy_theorem_target_iff_abs_unbounded_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded_of_neg_symm`
- `HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded`
- `HardyTheorem.hardy_theorem_target_iff_unbounded_of_bounded_strips`
- `HardyTheorem.exists_zero_on_critical_line_of_unbounded`
- `HardyTheorem.exists_zero_on_critical_line_of_abs_unbounded`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_two_signed_moments_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `PrimeNumberTheorem.hardy_theorem_target_iff_unbounded`
- `PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_two_signed_moments`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_two_signed_moments`
- `PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.hardy_theorem_target_of_two_signed_moments`
- `PrimeNumberTheorem.hardy_theorem_target_of_integral_asymptotic_one_two`
- `HardyTheorem.hardy_theorem_target_of_hardy_littlewood_lower_bound`
- `HardyTheorem.hardy_theorem_target_of_selberg_zero_proportion`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion`
- `PrimeNumberTheorem.hardy_zeros_unbounded_of_conrey_40_percent_target`
- `PrimeNumberTheorem.infinitely_many_zeros_on_critical_line_of_two_signed_moments`
- `PrimeNumberTheorem.infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_two_signed_moments`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_selberg_zero_proportion`
- `PrimeNumberTheorem.exists_zero_on_critical_line_of_conrey_40_percent_target`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips`
- `HardyTheorem.hardy_zeros_abs_unbounded_of_selberg_zero_proportion_of_bounded_strips`
- `HardyTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion_of_bounded_strips`
- `RiemannExplorer.hardy_theorem_target_of_conrey_target`
- `RiemannExplorer.hardy_theorem_target_of_two_signed_moments`
- `RiemannExplorer.hardy_theorem_target_of_integral_asymptotic_one_two`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_selberg_zero_proportion`
- `RiemannExplorer.infinitely_many_zeros_on_critical_line_of_conrey_target`
- `RiemannExplorer.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `RiemannExplorer.exists_zero_on_critical_line_of_selberg_zero_proportion`

### Missing mathlib/analytic infrastructure

1. corrected asymptotic signed moment formulas with sign-normalized leading terms;
2. Riemann–Siegel/AFE and `Γ`-factor asymptotics consistent with the chosen phase;
3. unbounded-height conclusion extracted from the signed-moment target using
   bounded-height zero finiteness.

---

## Non-target declarations to avoid confusion

- `HardyTheorem.weightedIntegralOf_tail_dominates` is a reusable predicate
  used as a hypothesis in conditional tail-dominance bridges, not an
  unconditional theorem target.
- `KnownResults.conrey_40_percent_zeros_on_critical_line_target`
  is the upper-level Conrey target form.  The submodule declaration
  `RiemannExplorer.Conrey40.conrey_40_percent_zeros_on_critical_line_target`
  is only a route-interface alias to this target.
- `MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum` is a route
  interface with a real statement body.  It marks the missing rectangle
  contour/residue theorem and is not counted as a mathematical target.
- `PrimeNumberTheorem.ExplicitFormulaAux.goodHeight` is a reusable contour
  height predicate, not a proof target.
- `PrimeNumberTheorem.explicit_formula_von_mangoldt` is a reusable theorem
  predicate, proved by
  `ExplicitFormulaResidues.explicit_formula_von_mangoldt_proved`; only the
  separate quantitative truncated-error route remains open.

All of the above is meant to be consumed as a roadmap, not a claim of completion.
