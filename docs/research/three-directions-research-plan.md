# Three Directions Research Notes

These notes track concrete Lean progress along three zero-free/PNT/RH-adjacent
routes.  The old repo-local worktree has been merged into `main` and removed;
the goal remains to add verified interfaces and small lemmas without overstating
any unresolved analytic theorem.

## Baseline

- Former worktree: `/Users/luicy/AI/Riemann/.worktrees/riemann-three-directions-research`
- Branch snapshot: `research/three-directions`, now aligned with `main`
- Current base before final worktree recovery:
  `a330c51 feat(zero-free): add log-scale weak-shift obstruction`
- Research work already carried into `main` covers:
  - signed BTY detector/Borel facades;
  - center-one and general-center zero-pair bridges;
  - explicit-formula tail bridges from eventual/no-new-zero and global-height inputs;
  - a zeta polynomial-growth handoff to the classical high-height
    `log |t|` scale;
  - compact-band positive lower bounds for `zeta` and a patching handoff from
    those proved compact bounds plus a future high-height lower bound to the
    full `verticalRegion 1 2 H` lower-bound input.
- Rule: do not present route interfaces or `def ... : Prop` targets as proved
  mathematics.

## Direction 1: BTY detector and Borel bounds

Verified assets now include:

- the BTY degree-16 trigonometric detector;
- the automatic finite Dirichlet-series identity
  `log_deriv_zeta_finset_series_identity`, so the detector `hseries` input is
  no longer a manual hypothesis in the automatic detector route;
- the pointwise BTY detector nonnegativity theorem
  `btyDetectorPolynomial_nonneg`;
- the simplified uniform BTY penalty
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound_simplified`;
- finite-family norm-bound facades
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_norm_bound`
  and
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_vertical_log_bound`;
- the global-vertical-to-finite-BTY handoff
  `btyDetector_uniform_vertical_log_bound_of_global_log_abs_add_three_bound`
  and the composed lower bound
  `log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound`;
- the automatic BTY finite-height comparison
  `btyDetector_log_abs_mul_add_three_le_log_seventeen_mul_abs_add_three`
  and its no-manual-`hlog` lower-bound wrapper
  `log_deriv_zeta_bty_detector_one_lower_bound_of_global_vertical_log_abs_add_three_bound_auto`;
- the mixed center/nonzero coefficient evaluation
  `btyDetectorCoeff_mixed_center_sum`, giving the exact noncentral coefficient
  sum `4431901 / 2485395`;
- the named vertical-bound BTY handoff
  `log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound`,
  which controls all nonzero BTY detector frequencies from
  `LogDerivVerticalLogBound` and leaves only the real-axis `k=0` term as a
  separate upper-bound input;
- the fixed-margin center-term closure
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound`,
  which removes that `k=0` input when `1 + epsilon <= sigma`;
- the fixed-margin closure
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_one_add_le`, which
  uses the existing `Re(s) >= 1 + epsilon` vertical `logDeriv` estimate;
- the bidirectional conversion between the named `logDeriv zeta` and
  `-logDeriv zeta` vertical norm-bound interfaces:
  `logDerivVerticalLogBound_of_negLogDerivVerticalLogBound` and
  `negLogDerivVerticalLogBound_of_logDerivVerticalLogBound`;
- the unsigned simplified Borel facade
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family_simplified`;
- the signed simplified Borel facade added on this branch:
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_signed_right_shift_borel_family_simplified`;
- the finite-family right-shifted Borel quotient bridges:
  `re_neg_deriv_div_riemannZeta_finset_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `re_neg_deriv_div_riemannZeta_finset_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`;
- the finite detector/Borel-family bridges:
  `log_deriv_zeta_finset_single_lower_bound_auto_of_right_shift_borel_family`
  and
  `log_deriv_zeta_finset_single_lower_bound_auto_of_signed_right_shift_borel_family`;
- the uniform BTY finite-family Borel bridges:
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family`
  and
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_signed_right_shift_borel_family`;
- the named-interface constructors from future high-height `B * log |t|`
  estimates:
  `logDerivVerticalLogBound_of_high_height_log_abs_bound`,
  `negLogDerivVerticalLogBound_of_high_height_log_abs_bound`, and
  `reNegDerivDivVerticalLogBound_of_high_height_log_abs_bound`;
- the direct affine-high-height-to-BTY fixed-margin bridges:
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_affine_log_abs_add_three_bound_high_height`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_affine_log_abs_add_three_bound_high_height_simplified`;
- the corresponding multiplicative `C * log(|t|+3)` BTY bridges:
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_log_abs_add_three_bound_high_height`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_log_abs_add_three_bound_high_height_simplified`;
- the signed `-logDeriv` versions of the same direct BTY bridges, for both
  affine and multiplicative `log(|t|+3)` high-height inputs:
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_affine_log_abs_add_three_bound_high_height`;
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_affine_log_abs_add_three_bound_high_height_simplified`;
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_log_abs_add_three_bound_high_height`;
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_log_abs_add_three_bound_high_height_simplified`;
- the exact-scale norm and signed-norm fixed-margin BTY handoffs:
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_logDeriv_bound`;
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_logDeriv_bound_simplified`;
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_negLogDeriv_bound`;
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_negLogDeriv_bound_simplified`;
- signed-vertical final assembly wrappers:
  `classical_zero_free_region_of_LogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`;
  `classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`;
  `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_NegLogDerivVerticalLogBound`;
  `classical_zero_free_region_of_exists_MultiplicityLogDerivRegularPartLogBound_and_exists_NegLogDerivVerticalLogBound`.
- direct real-part shifted-pair packaging:
  `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_high_height_log_abs_bounds`
  combines separate future high-height estimates at `sigma + it` and
  `sigma + 2it` into the shared pair shape consumed by the 3-4-1 route.
- direct final assemblies from an existential regular-part estimate plus a
  future high-height `B * log |t|` estimate in the `logDeriv`, `-logDeriv`, or
  `Re(-ζ'/ζ)` convention:
  `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_logDeriv_bound`;
  `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_negLogDeriv_bound`;
  `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_reNegDerivDiv_bound`,
  together with their multiplicity-aware analogues.
- the exact-scale real-part version of the same BTY bridge:
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound_simplified`;
- the polynomial-growth-to-`log |t|` zeta handoff:
  `log_norm_riemannZeta_sigma_it_le_affine_log_abs_of_polynomial_growth`.
- cutoff-normalization wrappers for both classical and Vinogradov-Korobov
  high-height zero-free-region targets:
  `classical_zero_free_region_high_height_mono_cutoff`;
  `classical_zero_free_region_high_height_mono_cutoff_re_im`;
  `classical_zero_free_region_high_height_exists_mono_cutoff`;
  `classical_zero_free_region_high_height_exists_mono_cutoff_re_im`;
  `vinogradov_korobov_zero_free_region_high_height_mono_cutoff`;
  `vinogradov_korobov_zero_free_region_high_height_mono_cutoff_re_im`;
  `vinogradov_korobov_zero_free_region_high_height_exists_mono_cutoff`;
  `vinogradov_korobov_zero_free_region_high_height_exists_mono_cutoff_re_im`.
- explicit-formula support normalizers:
  `PrimeNumberTheorem.ExplicitFormulaAux.goodHeight_iff_no_zero_at_height`;
  `PrimeNumberTheorem.ExplicitFormulaAux.not_goodHeight_iff_exists_zero_at_height`;
  `PrimeNumberTheorem.ExplicitFormulaAux.nontrivial_zero_mem_self_height`;
  `PrimeNumberTheorem.ExplicitFormulaAux.zeroMultiplicity_eq_one_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.zeroMultiplicity_eq_zero_of_not_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.mem_finiteTrivialZeroSum_iff`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_im_eq_zero_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_re_lt_zero_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_re_le_neg_two_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_ne_zero_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_abs_im_eq_zero_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_not_isNontrivialZero_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_two_le_norm_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_inv_norm_le_half_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.norm_trivial_zero_contribution_le_half_rpow_re`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_rpow_re_le_rpow_neg_two_of_mem`;
  `PrimeNumberTheorem.ExplicitFormulaAux.norm_trivial_zero_contribution_le_half_rpow_neg_two`;
  `PrimeNumberTheorem.ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_half_sum_rpow_re`;
  `PrimeNumberTheorem.ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_card_mul_half_rpow_neg_two`;
  `PrimeNumberTheorem.ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_floor_mul_half_rpow_neg_two`;
  `PrimeNumberTheorem.ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_height_mul_half_rpow_neg_two`;
  `PrimeNumberTheorem.ExplicitFormulaAux.finiteTrivialZeroSum_card_le`.

Next useful step:

```lean
logDeriv_riemannZeta_vertical_log_bound
```

The formerly separate `hseries` step is now closed in Lean.  The next bridge is
not the finite-support bookkeeping anymore: the new named handoff reduces the
nonzero BTY frequencies to the single future bound
`LogDerivVerticalLogBound`, and the fixed-margin variant discharges the center
term when `1 + epsilon <= sigma`.  What remains for the boundary-scale route is
the actual zeta-specific high-height estimate
`‖logDeriv ζ(σ + i u)‖ <= B log |u|` on `1 <= σ <= 2`.
The new polynomial-growth handoff removes one piece of height bookkeeping once
a usable zeta polynomial-growth input is available, but it does not prove that
input or a log-derivative estimate.  The fixed-margin closure is useful
infrastructure, not the classical shrinking-width estimate at
`sigma = 1 + a / log |t|`.

The lower-bound side now has the companion bridge
`exists_norm_riemannZeta_pos_lower_bound_on_verticalRegion_of_compact_band_and_high_height`:
the compact positive-height band is discharged by the proved nonvanishing plus
compactness theorem, while the remaining assumption is exactly the future
high-height lower bound for `T <= |Im z|`.  This narrows the derivative-growth
route to two real analytic inputs on the full strip: an upper bound for `ζ'`
and a positive lower bound for `ζ` at high height.

## Direction 2: Stechkin/Heath-Brown pair positivity

Verified assets now include:

- center-one zero-pair bridges over `nontrivialZerosFinset`;
- a general-center finite paired-sum bridge over full and new-zero finsets;
- paired-sum and paired-average bridges over full and new-zero finsets:
  `nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive`;
  `nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive`;
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive`;
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive`.
- center-one paired-sum and paired-average convenience wrappers:
  `nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one`;
  `nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one`;
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one`;
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive_one`.
- pointwise critical-strip positivity suppliers:
  `laplacePairPositive_one_of_re_nonnegative_on_critical_strip`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip`,
  `nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip`,
  and the corresponding new-zero `sdiff` sum/average wrappers.
- generic finite nonnegative kernel-combination closure:
  `weightedKernelCombo`,
  `laplacePairPositive_weightedKernelCombo`, and the corresponding full/new-zero
  sum, average, paired-sum, and paired-average nonnegativity wrappers.
- a concrete resolvent/Laplace prototype kernel
  `resolventLaplaceKernel a z = ((a : Complex) + z)⁻¹`, with right-half-plane
  real-part positivity, center-one pair positivity, and finite-zero/new-zero
  sum, average, paired-sum, and paired-average nonnegativity wrappers for every
  `a >= 0`.
- a center-reflected symmetric resolvent/Laplace kernel
  `symmetricResolventLaplaceKernel a center z = (a + z)⁻¹ + (a + center - z)⁻¹`,
  and finite combinations `symmetricResolventLaplaceKernelCombo`, with
  centered-strip positivity, center-one pair positivity, and full/new-zero
  finite-zero sum, average, paired-sum, and paired-average nonnegativity
  wrappers whenever the shifts and weights are nonnegative.
- a signed/damped detector-kernel interface
  `dampedKernel κ F G = F - κ • G`, with pair-positivity supplied by a
  concrete inequality `κ * pair(G) <= pair(F)` on the strip, plus the
  pair-nonnegative dominated input `0 <= pair(G) <= pair(F)` together with
  `κ <= 1`.  The damped interface is connected to full finite-zero and new-zero
  `sdiff` sums, averages, paired-sums, and paired-averages over
  `nontrivialZerosFinset`.
- finite nonnegative combinations of damped detector kernels:
  `laplacePairPositive_weightedDampedKernelCombo_of_pair_le`,
  `laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le`, and the
  corresponding full/new-zero sum, average, paired-sum, and paired-average
  wrappers.  This gives a direct Lean surface for multi-term signed detector
  assemblies once each summand's Stechkin-style pair inequality is available.
- finite weighted self-damped resolvent/Laplace combinations:
  `laplacePairPositive_one_weightedSelfDampedResolventLaplaceKernelCombo`
  and the corresponding full/new-zero sum, average, paired-sum, and
  paired-average nonnegativity wrappers whenever all weights and shifts are
  nonnegative and each damping coefficient is at most one.
- finite weighted self-damped affine resolvent/Laplace combinations:
  `laplacePairPositive_one_weightedSelfDampedAffineResolventLaplaceKernelCombo`
  and
  `weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip`,
  and the corresponding full/new-zero sum, average, paired-sum, and
  paired-average nonnegativity wrappers whenever all weights, affine parameters,
  and damping coefficients satisfy the same nonnegativity/`<= 1` hypotheses.
- finite nonnegative combinations of those prototype kernels,
  `resolventLaplaceKernelCombo`, with the same right-half-plane positivity,
  pair-positivity, and finite-zero/new-zero sum, average, paired-sum, and
  paired-average nonnegativity wrappers.
- affine resolvent/Laplace prototype kernels
  `affineResolventLaplaceKernel a b c z = (a + (b + c * z))⁻¹` and finite
  combinations `affineResolventLaplaceKernelCombo`, with right-half-plane
  positivity, center-one pair positivity, and full/new-zero sum, average,
  paired-sum, and paired-average nonnegativity wrappers for both single-kernel
  and finite-combination forms whenever the weights and affine parameters are
  nonnegative.

Important boundary:

The general-center paired average is not an unpaired real-part average.  Turning
it into an unpaired sum needs a proof that the chosen center-pair map preserves
the relevant zero set.  For zeta this is available at center `1`, via
`rho -> 1 - rho`, not for an arbitrary center.

The generic weighted-combination closure, resolvent/Laplace prototype,
symmetric resolvent/Laplace prototype, damped signed-kernel interface,
weighted damped-kernel combination interface, and affine resolvent/Laplace
prototype are real concrete suppliers for the finite-zero pairing API.  The
combination wrappers match detectors built by summing positive elementary
kernels; the damped interfaces additionally match Stechkin-style subtraction
terms, including finite nonnegative sums of such signed terms and concrete
weighted self-damped resolvent/Laplace combinations and weighted self-damped
affine resolvent/Laplace combinations. They are still not the full
Stechkin/Heath-Brown kernel used in the latest zero-free-region arguments. The
next useful step is to formalize a nontrivial detector kernel from that
literature and prove the concrete pair inequality needed by
`laplacePairPositive_dampedKernel_of_pair_le`, use the split
`laplacePairPositive_dampedKernel_of_pair_nonneg_le` input when it matches the
detector, or prove either
`LaplacePairPositive F 1` or the stronger pointwise critical-strip positivity
certificate for it.

## Direction 3: explicit formula / PNT error bridge

Verified assets now include:

- the public vertical-line and power-error route predicates:
  `NoZerosOnVerticalLine`, `PsiPowerErrorBelowTwoThirds`,
  `PsiPowerErrorBelowLine`,
  `NoZerosOnVerticalLineOneThirdOfStrongPNTError`, and
  `ExplicitFormulaConversePowerTarget`;
- input constructors for power-scale `ψ` error hypotheses:
  `psiPowerErrorBound_of_eventual_abs_bound`,
  `psiPowerErrorBound_of_pointwise`,
  `psiPowerErrorBelowLine_of_eventual_abs_bound`,
  `psiPowerErrorBelowLine_of_pointwise`,
  `psiPowerErrorBelowLine_of_power_saving`,
  `psiPowerErrorBelowTwoThirds_of_eventual_abs_bound`, and
  `psiPowerErrorBelowTwoThirds_of_pointwise`, and
  `psiPowerErrorBelowTwoThirds_of_power_saving`.  These let a future analytic
  estimate of the form `|ψ(x)-x| <= C*x^theta` or
  `ψ(x)-x = O(x^(beta-delta))` feed the route predicates directly.
- the `1/3`/`2/3` reflection equivalence
  `exists_nontrivial_zero_on_one_third_iff_two_thirds`;
- direct conditional bridges from RH, a zero-free right half-plane
  `Re(s) >= 2/3`, a concrete `psi` power error below `2/3`, or the general
  explicit-formula converse target to no zeros on `Re(s)=1/3`;
- direct `Re(s)=2/3` wrappers for the concrete `psi` power-error route and for
  `ExplicitFormulaConversePowerTarget (2/3)`, plus concrete below-`2/3`
  wrappers for both the direct and reflected line conclusions;
- direct conditional `O(x^(2/3-delta))` wrappers:
  `no_zeros_on_one_third_of_explicit_formula_converse_power_saving` and
  `no_zeros_on_two_thirds_of_explicit_formula_converse_power_saving`;
- general `O(x^(beta-delta))` direct/reflected wrappers and contrapositives,
  including same-line and reflected-line zeta-zero inputs:
  `no_zeros_on_vertical_line_of_psi_power_error_bound_sub_delta_bridge`,
  `no_zeros_on_reflected_line_of_psi_power_error_bound_sub_delta_bridge`,
  `not_psi_power_error_bound_sub_delta_of_exists_zero_on_line_bridge`, and
  `not_psi_power_error_bound_sub_delta_of_exists_zero_on_reflected_line_bridge`;
- existence-form versions of the general `psi`-error and explicit-formula
  converse bridges:
  `not_exists_nontrivial_zero_on_line_of_psi_power_error_bridge`;
  `not_exists_nontrivial_zero_on_reflected_line_of_psi_power_error_bridge`;
  `not_exists_nontrivial_zero_on_line_of_explicit_formula_converse_power_bound_sub_delta`;
  `not_exists_nontrivial_zero_on_reflected_line_of_explicit_formula_converse_power_bound_sub_delta`.
  These expose the same conditional route directly as
  `¬ ∃ s, IsNontrivialZero s ∧ s.re = ...`, matching the way the
  `Re(s)=1/3` / reflected-line question is usually discussed.
- finite explicit-formula truncation increment identities;
- exact finite-height truncation identities:
  `finiteNontrivialZeroSum_eq_add_new_zeros`,
  `finiteNontrivialZeroSum_sub_eq_new_zeros`,
  `explicitFormulaApprox_eq_sub_new_zeros`,
  `explicitFormulaApprox_sub_eq_new_zeros`,
  `explicitFormulaApprox_add_new_zeros`, and the corresponding empty-tail,
  congruence, and global-height stability wrappers;
- basic eventual-stability entrypoints
  `explicit_formula_von_mangoldt_of_eventually_eq` and
  `explicit_formula_von_mangoldt_of_eventually_exact`, which let a future
  contour/Perron construction enter through eventual equality with the
  corrected truncation, or through eventual exact equality with `ψ₀(x)`;
- new-zero norm/count tail bounds under RH;
- eventual-no-new-zero tail convergence;
- direct non-RH contribution-tail bridges:
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_tendsto_zero`;
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_norm_tendsto_zero`;
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_sum_norm_tendsto_zero`;
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_sum_norm_isLittleO_one`;
  `explicit_formula_von_mangoldt_of_base_and_eventually_new_zero_contribution_sum_norm_le`;
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_sum_norm_isBigO_tendsto_zero`;
  `explicit_formula_von_mangoldt_of_base_and_eventually_new_zero_contribution_norm_le`;
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_norm_isBigO_tendsto_zero`;
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_norm_isLittleO_one`;
  `explicit_formula_von_mangoldt_of_base_and_eventually_no_new_zeros_via_contribution_tail`;
- composed bridges:
  `explicit_formula_von_mangoldt_of_RH_base_and_eventually_no_new_zeros_via_sum_tail`;
  `explicit_formula_von_mangoldt_of_RH_base_and_eventually_no_new_zeros_via_card_tail`.
- global-height-bound-to-tail bridges:
  `nontrivialZerosFinset_eventually_sdiff_eq_empty_of_global_height_bound`;
  `new_zero_inv_norm_tail_tendsto_zero_of_global_height_bound`;
  `new_zero_card_tail_tendsto_zero_of_global_height_bound`;
  `explicit_formula_von_mangoldt_of_RH_base_and_global_height_bound_via_sum_tail`;
  `explicit_formula_von_mangoldt_of_RH_base_and_global_height_bound_via_card_tail`.
- truncated explicit-formula converse facades:
  `psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route`;
  `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`;
  `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_below_two_thirds`;
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route`;
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_below_two_thirds`;
  `no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_mono_error`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`;
  `not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving`;
  `not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`;
  `not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_mono_error`;
  `not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`;
  `not_exists_nontrivial_zero_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`;
  `not_exists_nontrivial_zero_on_one_third_of_truncated_explicit_formula_converse_route_saving`.
  These now live in the core `ExplicitFormulaTruncated` module as well as the
  public `RiemannPNT.API.ExplicitFormulaTruncated` namespace; the route
  conversion, direct `O(x^(beta-delta))` zero-exclusion wrappers, and
  monotone-error zero-exclusion wrappers are also exposed as top-level
  `RiemannPNT.API` theorems, including the existence-form variants.  The
  monotone wrappers let a `psi` power saving below a smaller boundary feed a
  larger-boundary truncated route, yielding direct and reflected zero
  exclusion at that larger boundary.
- explicit-formula auxiliary normalizers:
  `ExplicitFormulaAux.chebyshevPsi0`;
  `ExplicitFormulaAux.jumpVonMangoldt`;
  `ExplicitFormulaAux.zeroMultiplicity`;
  `ExplicitFormulaAux.goodHeight_iff_no_zero_at_height`;
  `ExplicitFormulaAux.not_goodHeight_iff_exists_zero_at_height`;
  `ExplicitFormulaAux.finiteNontrivialZeroSum`;
  `ExplicitFormulaAux.finiteTrivialZeroSum`;
  `ExplicitFormulaAux.nontrivial_zero_mem_self_height`;
  `ExplicitFormulaAux.zeroMultiplicity_eq_one_of_mem`;
  `ExplicitFormulaAux.zeroMultiplicity_eq_zero_of_not_mem`;
  `ExplicitFormulaAux.mem_finiteTrivialZeroSum_iff`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_im_eq_zero_of_mem`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_re_lt_zero_of_mem`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_re_le_neg_two_of_mem`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_ne_zero_of_mem`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_abs_im_eq_zero_of_mem`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_not_isNontrivialZero_of_mem`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_two_le_norm_of_mem`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_inv_norm_le_half_of_mem`;
  `ExplicitFormulaAux.norm_trivial_zero_contribution_le_half_rpow_re`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_rpow_re_le_rpow_neg_two_of_mem`;
  `ExplicitFormulaAux.norm_trivial_zero_contribution_le_half_rpow_neg_two`;
  `ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_half_sum_rpow_re`;
  `ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_card_mul_half_rpow_neg_two`;
  `ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_floor_mul_half_rpow_neg_two`;
  `ExplicitFormulaAux.norm_finiteTrivialZeroSum_contribution_le_height_mul_half_rpow_neg_two`;
  `ExplicitFormulaAux.finiteTrivialZeroSum_card_le`;
  `ExplicitFormulaAux.chebyshevPsi0_eq_chebyshevPsi_off_primePowers`;
  `ExplicitFormulaAux.jumpVonMangoldt_eq_vonMangoldt_of_primePower`.
- the monotonic `ψ`-error bridges `psiPowerErrorBelowLine_mono` and
  `psiPowerErrorBelowLine_of_below_two_thirds_of_two_thirds_le`, which let a
  stronger below-line error input feed any weaker boundary, including the
  concrete `theta < 2/3` input at any `beta >= 2/3`.
- monotone-error explicit-formula converse wrappers:
  `no_zeros_on_vertical_line_of_psi_power_error_bridge_mono_error`;
  `no_zeros_on_reflected_line_of_psi_power_error_bridge_mono_error`;
  `no_zeros_on_vertical_line_of_psi_power_error_below_two_thirds_mono_bridge`;
  `no_zeros_on_reflected_line_of_psi_power_error_below_two_thirds_mono_bridge`;
  `no_zeros_on_vertical_line_of_explicit_formula_converse_power_mono_error`;
  `no_zeros_on_reflected_line_of_explicit_formula_converse_power_mono_error`;
  `no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_saving`;
  `no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_mono_error`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`;
  `not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving`;
  `not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`;
  `not_exists_nontrivial_zero_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`;
  `not_exists_nontrivial_zero_on_one_third_of_truncated_explicit_formula_converse_route_saving`.
- critical-strip zero-line/existence normalizers:
  `not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line`;
  `no_zeros_on_vertical_line_of_not_exists_nontrivial_zero_on_line`;
  `no_zeros_on_vertical_line_iff_not_exists_nontrivial_zero_on_line`.
- route-interface conversion bridges:
  `psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power`;
  `explicitFormulaConversePowerTarget_of_psiPowerErrorBelowLineExcludesZerosRightOf`.

Important boundary:

These theorems still assume the base explicit-formula identity at a stable
truncation.  The global-height variants are route interfaces, not realistic
unconditional inputs for zeta zeros.  They do not prove Perron's formula,
contour shifting, or the converse/oscillation theorem turning
`psi(x) - x = O(x^(beta - delta))` into zero exclusion.  The current Lean value
is that both sides of the formal path are now explicit and smoke-checked: a
future `|ψ(x)-x| <= C*x^theta` estimate can enter as a route predicate, and any
future converse input at `beta = 2/3` then feeds the claimed `Re(s)=1/3`
exclusion.  The general contrapositive wrappers make the same dependency
usable in the opposite direction: a hypothetical zeta zero on `Re(s)=beta`, on
the reflected line, or to the right of the boundary is incompatible with a
concrete `O(x^(beta-delta))` error once the corresponding converse route is
assumed.

## Hard Gaps

- No classical zero-free region `Re(s) >= 1 - c / log |t|` is proved here.
- No Perron formula or contour-shift explicit formula is proved here.
- No explicit-formula converse / oscillation theorem is proved here.
- No result here proves RH or an unconditional zero-free vertical line.
