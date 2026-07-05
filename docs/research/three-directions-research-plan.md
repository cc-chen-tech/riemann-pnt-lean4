# Three Directions Research Worktree

This worktree tracks concrete Lean progress along three zero-free/PNT/RH-adjacent
routes.  The branch is based on current `main`; the goal is to add verified
interfaces and small lemmas without overstating any unresolved analytic theorem.

## Baseline

- Worktree: `/Users/luicy/AI/Riemann/.worktrees/riemann-three-directions-research`
- Branch: `research/three-directions`
- Current base: `0946b01 feat(zero-free): lift zeta growth handoff to circle averages`
- Research work on this branch currently covers:
  - signed BTY detector/Borel facades;
  - center-one and general-center zero-pair bridges;
  - explicit-formula tail bridges from eventual/no-new-zero and global-height inputs;
  - a zeta polynomial-growth handoff to the classical high-height
    `log |t|` scale.
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
- the polynomial-growth-to-`log |t|` zeta handoff:
  `log_norm_riemannZeta_sigma_it_le_affine_log_abs_of_polynomial_growth`.

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

## Direction 2: Stechkin/Heath-Brown pair positivity

Verified assets now include:

- center-one zero-pair bridges over `nontrivialZerosFinset`;
- a general-center finite paired-sum bridge over full and new-zero finsets;
- paired-average bridges over full and new-zero finsets:
  `nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive`;
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_laplace_pair_positive`.
- center-one paired-average convenience wrappers:
  `nontrivialZerosFinset_pair_average_nonnegative_of_laplace_pair_positive_one`;
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

The generic weighted-combination closure, resolvent/Laplace prototype, and
affine resolvent/Laplace prototype are real concrete suppliers for the
finite-zero pairing API, and the combination wrappers match the algebraic shape
of detectors built by summing positive elementary kernels. They are still not
the full Stechkin/Heath-Brown kernel used in the latest zero-free-region
arguments. The next useful step is to formalize a nontrivial detector kernel
from that literature and prove either
`LaplacePairPositive F 1` or the stronger pointwise critical-strip positivity
certificate for it.

## Direction 3: explicit formula / PNT error bridge

Verified assets now include:

- the public vertical-line and power-error route predicates:
  `NoZerosOnVerticalLine`, `PsiPowerErrorBelowTwoThirds`,
  `PsiPowerErrorBelowLine`, and `ExplicitFormulaConversePowerTarget`;
- the `1/3`/`2/3` reflection equivalence
  `exists_nontrivial_zero_on_one_third_iff_two_thirds`;
- direct conditional bridges from RH, a zero-free right half-plane
  `Re(s) >= 2/3`, a concrete `psi` power error below `2/3`, or the general
  explicit-formula converse target to no zeros on `Re(s)=1/3`;
- direct `Re(s)=2/3` wrappers for the concrete `psi` power-error route and for
  `ExplicitFormulaConversePowerTarget (2/3)`, plus concrete below-`2/3`
  wrappers for both the direct and reflected line conclusions;
- finite explicit-formula truncation increment identities;
- new-zero norm/count tail bounds under RH;
- eventual-no-new-zero tail convergence;
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
  `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`;
  `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_below_two_thirds`;
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route`;
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds`;
  `no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`.
- route-interface conversion bridges:
  `psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power`;
  `explicitFormulaConversePowerTarget_of_psiPowerErrorBelowLineExcludesZerosRightOf`.

Important boundary:

These theorems still assume the base explicit-formula identity at a stable
truncation.  The global-height variants are route interfaces, not realistic
unconditional inputs for zeta zeros.  They do not prove Perron's formula,
contour shifting, or the converse/oscillation theorem turning
`psi(x) - x = O(x^(beta - delta))` into zero exclusion.  The current Lean value
is that the formal path from any such future input at `beta = 2/3` to the
claimed `Re(s)=1/3` exclusion is now explicit and smoke-checked.

## Hard Gaps

- No classical zero-free region `Re(s) >= 1 - c / log |t|` is proved here.
- No Perron formula or contour-shift explicit formula is proved here.
- No explicit-formula converse / oscillation theorem is proved here.
- No result here proves RH or an unconditional zero-free vertical line.
