# Formal Theorem Inventory

This inventory separates proved Lean declarations from target statements.  It is
intended for reviewers and for future work planning.

Current verified baseline:

```bash
./scripts/verify-baseline.sh
python3 -m pytest
```

At the time of writing, `lake build` succeeds, the recursive placeholder scan
has no project Lean-source matches, the scanner classifies every project
`def ... : Prop`, the mathematical target inventory is stable at 22
declarations, and the Python experiment tests pass.

## Proved Project-Local Results

### `ZeroFreeRegion.lean`

Core verified declarations:

- `trig_identity_nonneg`
  proves `3 + 4 cos theta + cos (2 theta) >= 0`.
- `log_deriv_zeta_re_series`
  extracts the real-part Dirichlet series for `-zeta'/zeta`.
- `log_deriv_zeta_nonneg_combination`
  proves the full 3-4-1 logarithmic-derivative nonnegativity combination.
- `classical_zero_free_region_compact`
  proves a nonconstructive positive-width zero-free strip for each bounded
  height.
- `residue_bounds`
  proves `1 < (sigma - 1) * Re(zeta(sigma)) <= sigma` for `sigma > 1`.
- `log_deriv_zeta_pos_real`
  proves positivity of the real-axis logarithmic derivative expression.
- `log_deriv_zeta_antitone`
  proves the real-axis antitone property of the logarithmic derivative series.

Supporting declarations include:

- `zeta_no_zeros_on_line_one`
- `riemannZeta_pos_of_real_gt_one`
- `log_riemannZeta_dirichlet_series`
- `riemannZeta_re_eq_tsum_real`
- `summable_one_div_rpow`
- `riemannZeta_re_gt_one`
- `riemannZeta_gt_one_div_sub`
- `riemannZeta_re_le_sigma_div_sub`
- `log_deriv_zeta_real_eq_series`
- `sigmaOf_log_gt_one`
  proves the standard high-height choice `1 + a / log |t|` is greater than
  `1` when `a > 0`.
- `sigmaOf_log_le_two`
  proves this choice is at most `2` when `a <= log 2`.
- `sigmaOf_log_sub_pos`
  proves this choice stays to the right of any `β < 1`.
- `sigmaOf_log_le_one_add`
  connects this choice to local right-neighborhood hypotheses `σ <= 1 + d`.
- `three_four_one_sigmaOf_log_margin`
  proves the pure real-variable negativity margin for the standard choice
  `σ = 1 + a / log |t|`.
- `exists_sigmaOf_log_margin_constants`
  chooses positive constants `a,c` satisfying the standard smallness
  constraints and `3*C/a + K < 4/(a+c)` when `1 < C < 4/3`.
- `exists_sigmaOf_log_margin_constants_for_shift_bounds`
  specializes the constant choice to nonnegative shifted-estimate coefficients
  `Czero,Ctwo`, producing the exact margin
  `3*C/a + 4*Czero + Ctwo < 4/(a+c)`.
- `exists_sigmaOf_log_margin_constants_same_const`
  specializes the same constant selection to one nonnegative coefficient `B`,
  producing `3*C/a + 5*B < 4/(a+c)`.

Private technical lemma:

- `natCast_cpow_neg_re`
  computes `Re ((n : C)^(-s))` for positive natural `n`.

### `ZeroFreeRegion/MeromorphicAux.lean`

Core verified declarations:

- `meromorphicAt_riemannZeta_of_ne_one`
  proves zeta is meromorphic away from the pole at `1`.
- `meromorphicAt_riemannZeta_one`
  proves zeta is meromorphic at the pole by a local regular-plus-pole
  decomposition.
- `meromorphicOn_riemannZeta_closedBall`
  proves zeta is meromorphic on every closed ball.
- `eventuallyEq_riemannZeta_simplePoleAtOne`
  gives the local simple-pole normal form for zeta.
- `eventually_ne_zero_riemannZeta_nhdsNE_one`
  proves zeta is eventually nonzero in the punctured neighborhood of `1`.
- `eventuallyEq_inv_riemannZeta_simpleZeroAtOne`
  identifies the local reciprocal of zeta with the analytic simple-zero model.
- `analyticAt_riemannZetaReciprocalModelAtOne`
  proves the reciprocal local model is analytic at `1`.
- `deriv_riemannZetaReciprocalModelAtOne_one`
  proves the reciprocal local model has derivative `1` at `1`.
- `meromorphicOrderAt_riemannZeta_one`
  proves `meromorphicOrderAt riemannZeta 1 = -1`.
- `divisor_riemannZeta_pole_one`
  records the divisor value of zeta at its pole on meromorphic domains.
- `tendsto_mul_logDeriv_inv_riemannZeta_simpleZeroAtOne`
  proves `(s - 1) * logDeriv (fun z => (riemannZeta z)^-1) s -> 1`.
- `eventuallyEq_logDeriv_inv_riemannZeta`
  proves `logDeriv (1 / zeta) = -logDeriv zeta` in a punctured neighborhood.
- `tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne`
  proves `(s - 1) * logDeriv riemannZeta s -> -1` at the punctured
  neighborhood of `1`.
- `eventually_norm_mul_logDeriv_riemannZeta_le_two`
  proves the normalized logarithmic derivative is eventually bounded by `2`
  near the pole.
- `eventually_norm_mul_logDeriv_riemannZeta_lt_const`
  proves the normalized logarithmic derivative is eventually bounded by any
  real constant `C > 1`.
- `eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one`
  proves the local pole-order bound
  `norm (logDeriv riemannZeta s) <= 2 / norm (s - 1)` eventually near `1`.
- `eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one`
  proves the flexible local pole-order bound
  `norm (logDeriv riemannZeta s) < C / norm (s - 1)` for every `C > 1`.
- `logDeriv_riemannZeta_eq_deriv_div`,
  `neg_logDeriv_riemannZeta_eq_neg_deriv_div`,
  `neg_deriv_div_riemannZeta_eq_neg_logDeriv`,
  `logDeriv_riemannZeta_re_eq_deriv_div_re`,
  `neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re`,
  `neg_deriv_div_riemannZeta_re_eq_neg_logDeriv_re`,
  `norm_logDeriv_riemannZeta_eq_norm_deriv_div`, and
  `norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv`
  bridge Mathlib's `logDeriv ζ` notation with the quotient notation
  `ζ'/ζ` and `-ζ'/ζ` used by the 3-4-1 estimates.
- `eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
  rewrites the eventual local pole-order bound in explicit quotient notation
  `deriv riemannZeta s / riemannZeta s`.
- `eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  rewrites the flexible eventual pole-order bound in explicit quotient
  notation for every `C > 1`.
- `eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
  rewrites the eventual local pole-order bound for the signed quotient
  `-deriv riemannZeta s / riemannZeta s`.
- `eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  rewrites the flexible eventual pole-order bound for the signed quotient
  for every `C > 1`.
- `log_norm_neg_logDeriv_riemannZeta_eq`
  proves pointwise that the logarithmic norm is unchanged by replacing
  `logDeriv riemannZeta` with `-logDeriv riemannZeta`.
- `circleAverage_log_norm_neg_logDeriv_riemannZeta_eq`
  lifts the same `norm_neg` conversion to the Jensen left-side circle average.
- `eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
  bounds the real part of the signed quotient by
  `2 / norm (s - 1)` eventually near `1`.
- `eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  gives the corresponding eventual real-part bound with any constant
  `C > 1`.
- `eventually_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  gives the one-sided eventual real-part upper bound with any constant
  `C > 1`.
- `exists_punctured_ball_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one`
  packages that local pole-order bound as an explicit punctured-ball
  neighborhood around `1`.
- `exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one`
  packages the same local pole-order bound on a smaller closed punctured ball
  around `1`.
- `exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
  rewrites the closed punctured-ball local bound in explicit quotient notation
  `deriv riemannZeta s / riemannZeta s`.
- `exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  gives the flexible closed punctured-ball quotient bound for
  `deriv riemannZeta s / riemannZeta s`.
- `exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
  rewrites the same local bound for the signed quotient
  `-deriv riemannZeta s / riemannZeta s`.
- `exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  gives the flexible closed punctured-ball quotient bound for the signed
  quotient.
- `exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
  bounds the real part of the signed quotient on a closed punctured ball
  around `1`.
- `exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  gives the corresponding closed punctured-ball real-part bound with any
  constant `C > 1`.
- `exists_punctured_closedBall_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
  gives the one-sided closed punctured-ball real-part upper bound with any
  constant `C > 1`.
- `exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one`
  specializes the concrete signed-quotient norm bound to real-axis parameters
  with constant `2`.
- `exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one`
  gives the corresponding concrete real-axis real-part bound.
- `exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one`
  gives the corresponding concrete real-axis one-sided upper bound.
- `exists_rightNeighborhood_hreal_two_div_sub_one`
  packages the concrete real-axis bound in the exact `hreal` shape used by
  the 3-4-1 high-height assembly.
- `exists_sigmaOf_log_hreal_two_div_sub_one`
  specializes the concrete `hreal` package to the standard high-height choice
  `sigmaOf t = 1 + a / log |t|`.
- `exists_sigmaOf_log_hreal_two_mul_log_div`
  normalizes that concrete specialization into the vertical-height estimate
  `Re(-zeta'/zeta)(1 + a / log |t|) <= 2 * log |t| / a`.
- `exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one`
  specializes the local signed-quotient norm bound to real-axis parameters
  `1 < sigma <= 1 + d`, replacing `norm ((sigma : C) - 1)` by `sigma - 1`.
- `exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one`
  specializes the local real-part bound to real-axis parameters
  `1 < sigma <= 1 + d`, replacing `norm ((sigma : C) - 1)` by `sigma - 1`.
- `exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one`
  gives the corresponding real-axis one-sided upper bound without the absolute
  value.
- `exists_rightNeighborhood_hreal_const_div_sub_one`
  packages the flexible real-axis bound in the exact `hreal` shape used by the
  3-4-1 high-height assembly.
- `exists_sigmaOf_log_hreal_const_div_sub_one`
  specializes the flexible `hreal` package to the standard high-height choice
  `sigmaOf t = 1 + a / log |t|`.
- `exists_sigmaOf_log_hreal_const_mul_log_div`
  normalizes the flexible specialization into the vertical-height estimate
  `Re(-zeta'/zeta)(1 + a / log |t|) <= C * log |t| / a`.
- `exists_sigmaOf_log_two_t_norm_bound_const_mul_log_div`
  controls the `sigma + 2it` point by the half-plane L-series triangle
  inequality, with the unavoidable absolute-convergence scale
  `<= C * log |t| / a`.
- `exists_sigmaOf_log_two_t_bound_const_mul_log_div`
  converts the same weak `sigma + 2it` norm estimate into the real-part shape
  used by the third term of the 3-4-1 inequality.
- `sigmaOf_log_weak_two_t_margin_impossible`
  proves that this weak `1/a` scale cannot satisfy the standard 3-4-1 constant
  margin when the real-axis and `sigma + 2it` coefficients are both at least
  one.
- `no_sigmaOf_log_margin_constants_with_weak_two_t`
  packages the same obstruction as nonexistence of positive constants `a,c`
  satisfying the standard weak-margin inequality.
- `exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds`
  packages the standard `sigma(t) = 1 + a / log |t|` choice into the verified
  3-4-1 high-height contradiction and compact bounded-height patch.
- `exists_sigmaOf_log_classical_zero_free_region_of_shift_bounds`
  specializes that closure theorem to the usual shifted estimates
  `-1/(sigma-beta) + Czero log |t|` and `Ctwo log |t|`.
- `classical_zero_free_region_of_sigma_log_shift_estimates`
  combines local pole control, constant selection, standard `sigma`, 3-4-1,
  and compact patching, leaving exactly the two shifted estimates as analytic
  inputs.
- `classical_zero_free_region_of_sigma_log_shift_estimates_nonneg_constants`
  is the same closure with individual nonnegative shifted coefficients
  `Czero,Ctwo` instead of the bundled `0 <= 4*Czero + Ctwo`.
- `classical_zero_free_region_of_exists_sigma_log_shift_estimates_nonneg_constants`
  packages the general nonnegative shifted-estimate interface as one
  existential analytic input with some `1 < C < 4/3`.
- `classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths`
  fixes the real-axis coefficient to `5/4`, removing the abstract
  `1 < C < 4/3` hypotheses from the caller-facing closure.
- `classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths_nonneg_constants`
  combines the fixed `5/4` real-axis coefficient with the individual
  nonnegative shifted-coefficient interface.
- `classical_zero_free_region_of_exists_sigma_log_shift_estimates_five_fourths_nonneg_constants`
  packages that fixed `5/4` nonnegative interface as one existential analytic
  input.
- `classical_zero_free_region_of_sigma_log_shift_estimates_same_const`
  uses one nonnegative logarithmic coefficient for both shifted estimates.
- `classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const_high_height`
  packages the same-constant shifted estimates as one existential high-height
  analytic input; the existing compact patch closes the bounded-height range.
- `classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two`
  fixes the height cutoff in that same-constant closure to `2`, matching the
  target statement.
- `classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const`
  packages the remaining quantitative zero-free-region input as existence of
  one nonnegative logarithmic coefficient for both shifted estimates.
- `classical_zero_free_region_of_regular_part_bound_and_two_t_bound`
  converts the expected Borel-Caratheodory/Jensen regular-part estimate
  `Re(-zeta'/zeta)(s)+1/(Re(s)-Re(rho)) <= B log |Im(s)|`, together with the
  `sigma+2it` shifted estimate, into the classical zero-free-region target.
- `classical_zero_free_region_of_exists_regular_part_bound_and_two_t_bound`
  packages those two remaining analytic estimates under one nonnegative
  logarithmic coefficient.
- `inv_sub_same_im_re`
  rewrites `Re((s-rho)^{-1})` as `1/(Re(s)-Re(rho))` when `s` and `rho`
  have the same imaginary part, converting the complex principal part into
  the real singular term used by the zero-free-region contradiction.
- `classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound`
  replaces the regular-part real estimate by the norm estimate
  `||-zeta'/zeta(s)+(s-rho)^{-1}|| <= B log |Im(s)|`, together with the
  `sigma+2it` shifted estimate.
- `classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound`
  packages that norm-bound regular-part input under one nonnegative
  logarithmic coefficient.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound`
  is the same norm-bound closure in Mathlib's natural `-logDeriv zeta`
  notation, rewriting through the verified quotient bridge.
- `classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_two_t_bound`
  packages the `-logDeriv zeta` norm-bound input under one nonnegative
  logarithmic coefficient.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds`
  allows separate nonnegative logarithmic coefficients for the regular-part
  norm estimate and the `sigma+2it` estimate, merging them by `max`.
- `classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bounds`
  packages the same two-coefficient analytic input existentially.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds`
  lets both remaining analytic inputs be supplied as norm estimates in
  `-logDeriv zeta` notation, converting the `sigma+2it` norm estimate to a
  real-part estimate by `Re(z) <= ||z||`.
- `classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds`
  packages the fully norm-bound two-coefficient input existentially.
- `log_abs_two_mul_le_two_log_abs`
  proves `log |2t| <= 2 log |t|` for `|t| >= 2`, converting vertical estimates
  at height `2t` to the logarithmic scale used in the zero-free-region target.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
  reduces the `sigma+2it` input to a general vertical-strip norm estimate
  `||-logDeriv zeta(z)|| <= B log |Im(z)|` on `1 <= Re(z) <= 2`.
- `classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
  packages the regular-part norm estimate and vertical-strip log-derivative
  norm estimate existentially.
- `classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
  is the same highest-level closure in the natural local-zero convention
  `||logDeriv zeta(s) - (s-rho)^{-1}|| <= B log |Im(s)|`, converting signs by
  `||-x|| = ||x||`.
- `classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
  packages that positive-log-derivative convention existentially.
- `classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  is the high-height version of the same positive-log-derivative closure: the
  two zeta-specific estimates only need to hold for `T0 <= |Im|`, with
  `T0 >= 2`, and the bounded-height gap is filled by the compact patch.
- `classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  packages the high-height positive-log-derivative convention existentially.
- `classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height`
  converts high-height estimates of the natural form
  `A + B * log |Im|` into the multiplicative logarithmic interface, using
  `1 <= log |Im|` above height `3`.
- `classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height`
  packages the affine-log high-height interface existentially.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height`
  is the coordinate form of the affine-log closure, with the regular-part
  estimate stated for `sigma + i t` and same-height zero candidates
  `beta + i t`.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_bounds_high_height`
  packages the coordinate affine-log interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height`
  is the signed coordinate form of the same affine-log closure in
  `-logDeriv zeta` notation.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height`
  packages the signed coordinate affine-log interface existentially.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  specializes the coordinate interface to the common single-constant estimate
  `C * (1 + log |t|)` for both the regular-part and vertical log-derivative
  bounds.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  packages that single-constant coordinate interface existentially.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
  allows separate constants in the `C * (1 + log |t|)` estimate shape.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
  packages that two-constant Big-O shaped interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  accepts the same single-constant `C * (1 + log |t|)` interface in the
  signed `-logDeriv zeta` convention.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  packages that signed single-constant interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
  accepts separate signed `Cregular * (1 + log |t|)` and
  `Cvertical * (1 + log |t|)` bounds.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
  packages that signed two-constant Big-O shaped interface existentially.
- `log_abs_add_three_le_two_log_abs`
  proves `log(|t| + 3) <= 2 log |t|` for `|t| >= 3`.
- `norm_sigma_add_I_mul_le_abs_add_two`
  proves `||sigma + it|| <= |t| + 2` on `1 <= sigma <= 2`.
- `log_norm_sigma_add_I_mul_add_three_le_two_log_abs`
  proves `log(||sigma + it|| + 3) <= 2 log |t|` for
  `1 <= sigma <= 2` and `|t| >= 5`.
- `log_norm_add_three_le_two_log_abs_im`
  is the corresponding complex-variable comparison in terms of
  `s.re` and `s.im`.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
  specializes the coordinate interface to estimates stated as
  `C * log(|t| + 3)` for both remaining zeta-specific bounds.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
  packages the `log(|t| + 3)` coordinate interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
  accepts the same single-constant safe-height logarithmic interface in the
  signed `-logDeriv zeta` convention.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
  packages that signed single-constant safe-height logarithmic interface
  existentially.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
  allows separate `Cregular * log(|t| + 3)` and
  `Cvertical * log(|t| + 3)` bounds.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
  packages that two-constant safe-height logarithmic interface
  existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
  accepts the same two-constant safe-height logarithmic interface in the
  signed `-logDeriv zeta` convention.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
  packages that signed safe-height logarithmic interface existentially.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  accepts separate constants in estimates stated with the full complex
  height `log(||sigma + it|| + 3)`.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  packages that full-height logarithmic interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  accepts the same coordinate full-height estimates in the signed
  `-logDeriv zeta` convention.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  packages that signed coordinate full-height interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
  specializes that signed coordinate full-height interface to one shared
  constant for both remaining estimates.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
  packages the shared-constant signed coordinate full-height interface
  existentially.
- `classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  accepts complex-variable regular-part and vertical-strip estimates
  stated with `log(||s|| + 3)` and `log(||z|| + 3)`.
- `classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  packages that complex-variable full-height logarithmic interface
  existentially.
- `classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
  specializes the complex-variable full-height logarithmic interface to
  one shared constant.
- `classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
  packages the shared-constant complex-variable full-height interface
  existentially.
- `classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
  accepts affine full-height estimates `A + B log(||s|| + 3)` and
  `A + B log(||z|| + 3)` directly in complex variables.
- `classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
  packages that affine full-height logarithmic interface existentially.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
  accepts the same affine full-height estimates in the signed
  `-logDeriv zeta` convention.
- `classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
  packages that signed affine full-height interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
  accepts signed coordinate affine full-height estimates with additive
  constants.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
  packages that signed coordinate affine full-height interface existentially.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  accepts signed multiplicative full-height estimates with separate regular
  part and vertical-strip constants.
- `classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  packages that signed multiplicative full-height interface existentially.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
  specializes the signed complex-variable full-height interface to one
  shared constant.
- `classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
  packages the shared-constant signed complex-variable full-height interface
  existentially.
- `meromorphicAt_logDeriv_riemannZeta_one`
  proves the logarithmic derivative is meromorphic at the pole.
- `meromorphicAt_neg_logDeriv_riemannZeta_one`
  proves the signed logarithmic derivative is meromorphic at the pole.
- `meromorphicOn_logDeriv_riemannZeta_closedBall`
  proves the logarithmic derivative is meromorphic on every closed ball.
- `meromorphicOn_neg_logDeriv_riemannZeta_closedBall`
  proves the signed logarithmic derivative is meromorphic on every closed
  ball.
- `borelCaratheodory_zero_centered`
  translates Mathlib's vanishing-at-zero Borel-Caratheodory theorem to disks
  centered at arbitrary `c`.
- `borelCaratheodory_centered`
  translates Mathlib's general Borel-Caratheodory theorem to disks centered at
  arbitrary `c`.
- `borelCaratheodory_sub_centered`
  bounds `||f z - f c||` from a real-part bound on the centered function
  `f - f(c)`.
- `jensen_circleAverage_log_norm_riemannZeta_closedBall`
  specializes Mathlib's Jensen formula to `riemannZeta` on closed balls.
- `jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall`
  specializes Mathlib's Jensen formula to `logDeriv riemannZeta` on closed
  balls.
- `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall`
  specializes Mathlib's Jensen formula to `-logDeriv riemannZeta` on closed
  balls.
- `closedBall_re_bounds` and `ball_re_bounds`
  bound real coordinates of points in complex disks by center plus/minus
  radius.
- `closedBall_abs_im_ge_of_add_le` and `ball_abs_im_ge_of_add_le`
  transfer a high imaginary-height bound from the disk center to every point in
  the disk.
- `closedBall_sigma_it_re_bounds`, `ball_sigma_it_re_bounds`,
  `closedBall_sigma_it_abs_im_ge_of_add_le`, and
  `ball_sigma_it_abs_im_ge_of_add_le`
  specialize the same disk geometry to centers written as `sigma + I*t`.
- `closedBall_sigma_it_re_mem_Icc`, `ball_sigma_it_re_mem_Icc`,
  `closedBall_sigma_it_mem_verticalRegion`, and
  `ball_sigma_it_mem_verticalRegion`
  package those center-specialized estimates as real-strip membership and
  simultaneous real-strip/high-height membership.
- `closedBall_sigma_it_subset_verticalRegion` and
  `ball_sigma_it_subset_verticalRegion`
  upgrade the same facts to set inclusions for entire local disks.
- `verticalRegion`, `mem_verticalRegion`,
  `mapsTo_add_closedBall_zero_sigma_it_verticalRegion`, and
  `mapsTo_add_ball_zero_sigma_it_verticalRegion`
  name the vertical target set and prove that zero-centered disks translate
  into it under the same margin hypotheses.
- `differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion` and
  `meromorphicOn_closedBall_sigma_it_of_meromorphicOn_verticalRegion`
  restrict vertical-region regularity to the local disks used by
  Borel-Caratheodory and Jensen.
- `borelCaratheodory_centered_verticalRegion` and
  `borelCaratheodory_sub_centered_verticalRegion`
  combine the centered Borel-Caratheodory wrappers with the local disk
  geometry, using ambient `verticalRegion` hypotheses directly.
- `borelCaratheodory_centered_half_radius_bound`
  turns the centered Borel-Caratheodory rational factors into the constant
  bound `||f z|| <= 2 M + 3 ||f c||` on the half-radius subdisk.
- `borelCaratheodory_sub_centered_half_radius_bound`
  gives the matching oscillation form `||f z - f c|| <= 2 M` on the
  half-radius subdisk.
- `borelCaratheodory_centered_verticalRegion_half_radius_bound` and
  `borelCaratheodory_sub_centered_verticalRegion_half_radius_bound`
  combine the same half-radius estimates with the ambient `verticalRegion`
  disk geometry.
- `borelCaratheodory_riemannZeta_verticalRegion` and
  `borelCaratheodory_sub_riemannZeta_verticalRegion`
  specialize the same Borel wrappers to ζ and centered ζ, leaving only
  ambient real-part bounds as future analytic inputs.
- `mapsTo_riemannZeta_verticalRegion_of_re_le`,
  `mapsTo_sub_riemannZeta_verticalRegion_of_re_le`,
  `borelCaratheodory_riemannZeta_verticalRegion_of_re_le`, and
  `borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le`
  provide the pointwise-estimate interface for those ζ bounds, so future
  growth estimates can be stated as ordinary
  `∀ z ∈ verticalRegion, Re(...) ≤ M` hypotheses.
- `borelCaratheodory_riemannZeta_verticalRegion_half_radius_bound`,
  `borelCaratheodory_sub_riemannZeta_verticalRegion_half_radius_bound`,
  `borelCaratheodory_riemannZeta_verticalRegion_of_re_le_half_radius`, and
  `borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le_half_radius`
  give the denominator-free half-radius variants for ζ itself.
- `borelCaratheodory_logDeriv_riemannZeta_verticalRegion` and
  `borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion`
  specialize the same local Borel geometry to `logDeriv ζ`, while keeping the
  remaining differentiability and real-part bounds explicit.
- `mapsTo_logDeriv_riemannZeta_verticalRegion_of_re_le`,
  `mapsTo_sub_logDeriv_riemannZeta_verticalRegion_of_re_le`,
  `borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_re_le`, and
  `borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_re_le`
  let future height estimates enter this layer as ordinary pointwise
  `∀ z ∈ verticalRegion, Re(...) ≤ M` hypotheses rather than prepackaged
  `Set.MapsTo` assumptions.
- `differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re`
  proves the missing differentiability hypothesis automatically on
  positive-height right half-strips, using ζ nonvanishing on `Re(s) >= 1`.
- `borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`
  and
  `borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`
  are the same `logDeriv ζ` Borel interfaces with that differentiability
  hypothesis discharged; the only remaining Borel input is a pointwise
  real-part height bound.
- `borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`
  and
  `borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`
  are the positive `logDeriv ζ` half-radius versions, matching the local
  regular-part sign convention.
- `borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
  normalize those positive half-radius Borel outputs to affine
  `A + B log(||sigma+it|| + 3)` bounds.
- `differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re`,
  `borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`,
  and
  `borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`
  repeat this Borel regularity layer in the signed `-logDeriv ζ` convention
  used by the 3-4-1 inequality.
- `borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`
  combines the signed right-half-strip Borel wrapper with the half-radius
  constant bound, eliminating the denominator terms in the common local-disk
  application.
- `borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`
  is the signed oscillation half-radius version used for centered
  regular-part control of `-ζ'/ζ`.
- `borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
  normalize the signed half-radius Borel outputs to affine
  `A + B log(||sigma+it|| + 3)` bounds.
- `jensen_circleAverage_log_norm_verticalRegion`
  combines Jensen's formula with the same closed-disk geometry and ambient
  vertical-region meromorphicity.
- `one_not_mem_verticalRegion_of_pos_height`,
  `ne_one_of_mem_verticalRegion_of_pos_height`, and
  `differentiableOn_riemannZeta_verticalRegion_of_pos_height`
  prove that positive-height vertical regions avoid ζ's pole and therefore
  support ζ differentiability.
- `meromorphicOn_riemannZeta_verticalRegion`,
  `meromorphicOn_logDeriv_riemannZeta_verticalRegion`,
  `meromorphicOn_neg_logDeriv_riemannZeta_verticalRegion`,
  `jensen_circleAverage_log_norm_riemannZeta_verticalRegion`, and
  `jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion`,
  `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion`
  specialize the ambient vertical-region meromorphic/Jensen interfaces to ζ
  and both logarithmic-derivative sign conventions.

### `PrimeNumberTheorem.lean`

Core verified declarations:

- `logIntegral_asymptotic`
  proves the asymptotic relation needed for `Li(x) ~ x / log x`.
- `pnt_forms_equivalent`
  proves equivalence of the project-local `PNTForm1`, `PNTForm2`, and
  `PNTForm3`.
- `nontrivial_zero_symmetric`
  proves symmetry of nontrivial zeros under `rho -> 1 - rho`.
- `nontrivial_zero_symmetric'`
  packages the symmetry as preservation of `IsNontrivialZero`.
- `riemannZeta_ne_zero_of_re_le_zero`
  excludes nontrivial zeros in `Re(s) <= 0`, except for the trivial zero
  locations.
- `nontrivial_zero_in_critical_strip`
  derives `0 < Re(s) < 1` for nontrivial zeros.
- `finite_nontrivial_zeros_bounded_height`
  proves finiteness of nontrivial zeros with bounded imaginary part.
- `rh_iff_nontrivial_zeros_on_line`
  identifies the local RH statement with the condition that every nontrivial
  zero has real part `1/2`.
- `rh_statement_iff_mathlib`
  relates the local RH statement to Mathlib's `RiemannHypothesis`.
- `riemannZeta_pole_simple`
  proves `(s - 1)^2 zeta(s) -> 0` at the punctured neighborhood of `1`.
- `rh_zero_symmetric_self_consistent`
  records the compatibility of RH with zero symmetry.
- `zero_contribution`
  rewrites the oscillatory contribution of a zero.
- `PNTForm2_iff_PNTForm1`, `PNTForm3_iff_PNTForm2`, and
  `PNTForm3_iff_PNTForm1`
  package reverse orientations of the already-proved PNT-form equivalences.

Supporting declarations include:

- `primeCounting_eq_mathlib`
- `vonMangoldt_eq_mathlib`
- `chebyshevPsi_eq_mathlib`
- `logIntegral_integration_by_parts`
- `logIntegral_nonneg`
- `logIntegral_pos`
- `riemannZeta_not_frequently_zero_nhdsNE_of_ne_one`
- `RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound`
- `rh_iff_optimal_error_of_pointwise_implications`
- `RH_ErrorBound_of_rh_iff_optimal_error`
- `RiemannHypothesis_of_rh_iff_pointwise_error`
- `explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero`
- `explicit_formula_von_mangoldt_iff_re_im_error_isLittleO_one`
- `hardy_zeros_abs_unbounded_of_two_signed_moments`
- `hardy_zeros_unbounded_of_two_signed_moments`
- `hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two`
- `hardy_zeros_unbounded_of_integral_asymptotic_one_two`
- `hardy_theorem_target_of_two_signed_moments`
- `hardy_theorem_target_of_integral_asymptotic_one_two`
- `infinitely_many_zeros_on_critical_line_of_two_signed_moments`
- `infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two`
- `infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `exists_zero_on_critical_line_of_two_signed_moments`
- `exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `exists_zero_on_critical_line_of_selberg_zero_proportion`
- `exists_zero_on_critical_line_of_conrey_40_percent_target`

### `HardyTheorem.lean`

Core verified declarations:

- `completedRiemannZeta_conj_eq_of_one_lt_re`
- `completedRiemannZeta₀_conj_eq`
- `completedRiemannZeta_critical_line_real`
- `Gammaℝ_re_im_arg`
- `hardyZ_zero_implies_zeta_zero`
- `hardyZ_zero_iff_zeta_zero`
- `hardyZ_continuous`
- `hardyZ_eventually_const_sign_of_finite_zeros`
- `weightedIntegralOf_neg`
- `hardy_two_signed_moments_target_iff_integral_asymptotic_one_two`
- `hardy_theorem_target_of_two_signed_moments`
- `hardy_theorem_target_of_integral_asymptotic_one_two`
- `exists_zero_on_critical_line_of_hardy_theorem_target`
- `exists_zero_on_critical_line_of_two_signed_moments`
- `exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `hardy_theorem_target_iff_abs_unbounded_of_bounded_strips`
- `hardy_theorem_target_iff_unbounded_of_bounded_strips`
- `hardy_zeros_abs_unbounded_of_two_signed_moments_of_bounded_strips`
- `exists_zero_on_critical_line_of_unbounded`
- `exists_zero_on_critical_line_of_abs_unbounded`
- `hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips`
- `hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `hardy_zeros_unbounded_iff_abs_unbounded`

These prove the local Hardy-Z setup and the equivalence between zeros of
`hardyZ` and zeros of `zeta` on the critical line, plus conditional bridges
from the signed-moment targets to Hardy's infinite and unbounded-height zero
interfaces.  They do not prove Hardy's theorem unconditionally; the moment
estimates needed for Hardy's theorem remain targets.

### `GammaResidue.lean`

Core verified declarations:

- `gamma_residue_at_zero`
- `gamma_residue_at_neg_natural`
- `residue_at_zero_eq_one`
- `residue_at_minus_one_eq_minus_one`
- `residue_at_minus_two_eq_half`

The general theorem proves the residue of `Gamma` at nonpositive integers:

```text
Res(Gamma, -n) = (-1)^n / n!
```

### `EulerAndLfunctions.lean`

This file contains wrappers around existing Mathlib results:

- `EulerProduct.euler_product`
- `EulerProduct.euler_product_inv`
- `ZetaValues.zeta_two`
- `ZetaValues.zeta_zero`
- `ZetaValues.zeta_pos_real`
- `ZetaValues.zeta_ne_zero`
- `DirichletNonvanishing.lseries_ne_zero`
- `DirichletNonvanishing.lfunction_ne_zero`

These are useful for the project API but should not be presented as new
mathematical theorems.

### `RiemannExplorer.lean`

This file provides project-level definitions and wrappers:

- `RiemannHypothesis.riemannZetaSeries`
- `RiemannHypothesis.euler_product`
- `RiemannHypothesis.zeta_pole_at_one`
- `RiemannHypothesis.functional_equation`
- `RiemannHypothesis.riemannHypothesis_iff_zeros_on_critical_line`
- `KnownResults.zeta_no_zeros_on_one_line`
- `KnownResults.zeta_no_zeros_on_zero_line`
- `KnownResults.infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound`
- `KnownResults.hardy_theorem_target_of_two_signed_moments`
- `KnownResults.hardy_theorem_target_of_integral_asymptotic_one_two`
- `KnownResults.exists_zero_on_critical_line_of_two_signed_moments`
- `KnownResults.exists_zero_on_critical_line_of_integral_asymptotic_one_two`
- `KnownResults.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound`
- `KnownResults.exists_zero_on_critical_line_of_selberg_zero_proportion`

It also records exploratory strategy strings.  Those strings are explanatory
metadata, not proof results.

## Target Statements, Not Proved Theorems

The following declarations are intentionally `def ... : Prop` targets.  They
are not exported as theorems and should not be cited as proved.

As of `2026-06-08`, there are **22** mathematical target declarations:

- `HardyTheorem` namespace: **7**
- `HardyTheorem.Details` namespace: **3**
- `PrimeNumberTheorem` namespace: **9**
- `KnownResults` namespace: **1**
- `ZeroFreeRegion` namespace: **1**
- global namespace: **1** (`vinogradov_korobov_zero_free_region`)

### `ZeroFreeRegion.lean`

- `classical_zero_free_region`
  target: a uniform zero-free region
  `Re(s) >= 1 - c / log |Im(s)|`.
- `vinogradov_korobov_zero_free_region`
  target: the stronger Vinogradov-Korobov zero-free region.  This declaration
  currently lives in the global namespace even though it is in
  `ZeroFreeRegion.lean`.

### `PrimeNumberTheorem.lean`

- `rh_iff_optimal_error`
  target: equivalence between RH and a prime-counting error term.
- `explicit_formula_von_mangoldt`
  target: a von Mangoldt explicit formula in midpoint/truncated-limit form,
  using `chebyshevPsi0` and `finiteNontrivialZeroSum`.
- `PNTForm1`, `PNTForm2`, `PNTForm3`
  local PNT-format targets:
  `pi(x) ~ x / log x`, `pi(x) ~ Li(x)`, and `psi(x) ~ x`. These are
  intentionally target placeholders because the bridge to a full analytic proof
  runs through explicit-formula machinery.

### `HardyTheorem.lean`

- `integral_asymptotic_target`
- `hardy_two_signed_moments_target`
- `hardy_theorem_target`
- `hardy_zeros_unbounded_target`
- `hardy_zeros_abs_unbounded_target`
- `hardy_littlewood_lower_bound_target`
- `selberg_zero_proportion_target`

### `HardyTheorem.Details`

- `gamma_asymptotic_half_plus_it_target`
- `theta_asymptotic_target`
- `approximate_functional_equation_target`

These replace earlier overstrong or false theorem statements.  In particular,
eventual positivity of a function is not by itself enough to imply eventual
positivity of its integral from `0` to `T`; an additional tail-dominance
hypothesis is needed.  The weighted-integral positivity/negativity bridge and
the finite-zero contradiction under signed-moment and tail-dominance hypotheses
are now proved lemmas, not target statements.

### `KnownResults` in `RiemannExplorer.lean`

- `conrey_40_percent_zeros_on_critical_line_target`
  target: a positive-proportion statement on critical-line zeros, expressed as
  a target alias for `HardyTheorem.selberg_zero_proportion_target`.

## Route Interfaces and Reusable Predicates

The recursive Prop scanner also tracks route interfaces and ordinary predicates
so they are not hidden inside subdirectories or mistaken for proved theorems.

Route interfaces:

- `HardyTheorem.AFE.zeta_critical_afe_target`
  real-statement AFE interface for the Hardy chain.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedTarget`
  real-statement truncated explicit-formula interface.
- `RiemannExplorer.Conrey40.conrey_40_percent_zeros_on_critical_line_target`
  alias interface to `KnownResults.conrey_40_percent_zeros_on_critical_line_target`.
- `MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum`
  real-statement interface for missing rectangle contour/residue infrastructure.

Reusable predicates:

- `HardyTheorem.weightedIntegralOf_tail_dominates`
- `PrimeNumberTheorem.ExplicitFormulaAux.goodHeight`

Current status in `HardyTheorem.lean` target list:

- `hardy_zeros_abs_unbounded_target` is a monotone reformulation of
  `hardy_zeros_unbounded_target`.
- `hardy_littlewood_lower_bound_target` is available as a derived output if
  `selberg_zero_proportion_target` is available.

Detailed dependency maps for the four unfinished analytic chains are collected
under `docs/missing-chains-index.md`.

## Dependency Boundary

The project uses substantial Mathlib infrastructure, including:

- `riemannZeta` and its Euler product;
- the functional equation and nonvanishing on `Re(s) >= 1`;
- `riemannZeta_residue_one`;
- von Mangoldt L-series identities;
- zeta asymptotics around the harmonic-series expansion;
- compactness and analytic continuation APIs.

The project-local novelty is the assembly and formal proof of the intermediate
zeta-function infrastructure listed above, especially the real-part
logarithmic-derivative series, the 3-4-1 combination, compact zero-free strip,
and residue-scale inequalities.

## Missing Chains for a Complete Analytic PNT

To turn the current framework into a full de la Vallee Poussin proof with error
term, the following chains remain:

1. **Quantitative zero-free region.**
   Need zeta growth and logarithmic-derivative estimates, likely through
   Hadamard factorization or Borel-Caratheodory, to upgrade the compact strip to
   `c / log |t|`.
2. **Explicit formula.**
   Need Perron's formula, contour integration, residue calculus, edge estimates,
   and a correct truncated/principal-value zero sum.
3. **RH error equivalence.**
   Need zero-counting estimates, explicit formula bounds under RH, and partial
   summation from Chebyshev functions to prime counting.
4. **Hardy theorem.**
   Need corrected moment asymptotics for Hardy's Z-function and supporting
   special-function asymptotics.
