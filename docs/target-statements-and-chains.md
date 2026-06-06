# Unproved Target Statements and Missing Chains

This file is the authoritative checklist of the remaining `def ... : Prop`
statements (as of `2026-06-03`) in this Lean checkout.

All entries are intentionally **not** exported as theorems.  They are explicit
`Prop` targets used as roadmap checkpoints.

## Target count

- `HardyTheorem` namespace: 10
- `PrimeNumberTheorem` namespace: 9
- `ZeroFreeRegion` namespace: 2
- `RiemannExplorer` namespace: 1

Total: **22**.

For the chain accounting:

- Quantitative zero-free region chain: 2
- Explicit formula chain: 1
- RH/prime-counting error chain: 8
- Hardy theorem chain: 11 (10 in `HardyTheorem`, 1 in `RiemannExplorer`)

## Chain 1: Quantitative zero-free region

### Target declarations

- `ZeroFreeRegion.classical_zero_free_region`
- `ZeroFreeRegion.vinogradov_korobov_zero_free_region`

### Current verified anchor theorems

- `ZeroFreeRegion.log_deriv_zeta_re_series`
- `ZeroFreeRegion.log_deriv_zeta_nonneg_combination`
- `ZeroFreeRegion.residue_bounds`
- `ZeroFreeRegion.classical_zero_free_region_compact`
- `ZeroFreeRegion.log_deriv_zeta_pos_real`
- `ZeroFreeRegion.log_deriv_zeta_antitone`
- `ZeroFreeRegion.compact_patch_classical_zero_free_region_at_three`
- `ZeroFreeRegion.classical_zero_free_region_high_height`
- `ZeroFreeRegion.classical_zero_free_region_iff_high_height`
- `ZeroFreeRegion.classical_zero_free_region_iff_high_height_at_three`
- `ZeroFreeRegion.vinogradov_korobov_high_height_classical_zero_free_region`
- `ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov`

### Missing mathlib/analytic infrastructure

1. zeta-specific log-derivative growth bound near `Re(s)=1` for bounded-height
   high strips;
2. Borel–Carathéodory or equivalent zero-repulsion machinery;
3. explicit control of the pole-side term (`-zeta'/zeta` near `1`) and
   the `σ+2it` regular part;
4. real-variable bridge from a quantitative strip at large height to the bounded-
   height compact strip.

---

## Chain 2: Explicit formula

### Target declarations

- `PrimeNumberTheorem.explicit_formula_von_mangoldt`

### Current verified anchor theorems

- `PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height`
- `PrimeNumberTheorem.zero_contribution`
- `PrimeNumberTheorem.chebyshevPsi_eq_mathlib`
- `PrimeNumberTheorem.vonMangoldt_eq_mathlib`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_error_tendsto_zero`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_error_isLittleO_one`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_tendsto`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero`
- `PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_error_isLittleO_one`

### Missing mathlib/analytic infrastructure

1. Perron's formula / contour-integral identity in a form usable for
   von Mangoldt sums;
2. residue-theorem-level contour argument for:
   - pole at `s=1`,
   - pole at `s=0`,
   - nontrivial zeros with multiplicity,
   - trivial-zero contribution;
3. corrected summation convention (truncated/symmetric principal value / midpoint
   `psi0`) and explicit edge-error estimates.

---

## Chain 3: RH ⇔ prime-counting error

### Target declarations

- `PrimeNumberTheorem.PNTForm1`
- `PrimeNumberTheorem.PNTForm2`
- `PrimeNumberTheorem.PNTForm3`
- `PrimeNumberTheorem.RH_PsiErrorBound`
- `PrimeNumberTheorem.RH_ThetaErrorBound`
- `PrimeNumberTheorem.RH_PrimeCountingLiErrorBound`
- `PrimeNumberTheorem.RH_ErrorBound`
- `PrimeNumberTheorem.rh_iff_optimal_error`

### Current verified anchor theorems

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

### Missing mathlib/analytic infrastructure

1. a usable explicit-formula endpoint from Chain 2 with quantified error terms,
   including truncation parameter handling;
2. zero-counting and reciprocal-zero sum control (e.g. `N(T)` and `sum 1/|rho|`)
   for converting explicit-formula sums to `sqrt(x) log^2 x`-type bounds;
3. upstream proof of `RH_PsiErrorBound` / `RH_ThetaErrorBound`; the forward
   `Chebyshev` to `primeCounting` bridge under RH-quality errors is already
   proved by `RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound`;
4. reverse implication machinery (error bounds on `pi`/`Li` imply RH in
   the required direction).

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
- `HardyTheorem.gamma_asymptotic_half_plus_it_target`
- `HardyTheorem.theta_asymptotic_target`
- `HardyTheorem.approximate_functional_equation_target`
- `RiemannExplorer.conrey_40_percent_zeros_on_critical_line_target`

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
- `RiemannExplorer.conrey_40_percent_zeros_on_critical_line_target`
  appears as a downstream target form and is kept intentionally in
  `RiemannExplorer`.

All of the above is meant to be consumed as a roadmap, not a claim of completion.
