# Zero-Free Region Chain

This note audits the remaining Lean work needed to turn the current
zero-free-region infrastructure into the target
`ZeroFreeRegion.classical_zero_free_region : Prop`.

Current Lean status: `ZeroFreeRegion.lean` checks with
`lake env lean -R . ZeroFreeRegion.lean`.  The quantitative target is still a
`def ... : Prop`, not a proved theorem.

## Verified Starting Points

The following declarations are available in the current checkout:

```lean
ZeroFreeRegion.log_deriv_zeta_re_series
  (s : ℂ) (hs : 1 < s.re) :
  (-deriv riemannZeta s / riemannZeta s).re =
    ∑' n : ℕ, Λ n * Real.cos (s.im * Real.log n) / (n : ℝ) ^ s.re

ZeroFreeRegion.log_deriv_zeta_nonneg_combination
  (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
  3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
    + 4 * (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
    + (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re ≥ 0

ZeroFreeRegion.norm_logDeriv_riemannZeta_le_real_neg_deriv_div
  (s : ℂ) (hs : 1 < s.re) :
  ‖logDeriv riemannZeta s‖ ≤
    (-deriv riemannZeta (s.re : ℂ) /
      riemannZeta (s.re : ℂ)).re

ZeroFreeRegion.residue_bounds
  (σ : ℝ) (hσ : 1 < σ) :
  1 < (σ - 1) * (riemannZeta (σ : ℂ)).re ∧
    (σ - 1) * (riemannZeta (σ : ℂ)).re ≤ σ

ZeroFreeRegion.classical_zero_free_region_compact
  (T : ℝ) (_hT : T ≥ 2) :
  ∃ d > 0, ∀ s : ℂ, |s.im| ≤ T → s.re ≥ 1 - d →
    riemannZeta s ≠ 0
```

`residue_bounds` confirms the normalization of the pole at `1`, but it is not
yet a logarithmic-derivative estimate.  The missing quantitative step is the
standard de la Vallee Poussin contradiction:

1. assume a zero `ρ = β + i t` near `Re(s) = 1`;
2. evaluate the 3-4-1 inequality at `σ = 1 + η`;
3. bound the real-axis and `σ + 2it` terms by `O(log |t|)`, while the
   `σ + it` term contributes `-1 / (σ - β) + O(log |t|)`;
4. choose `η` and the final constant `c` small enough to contradict
   nonnegativity.

The `σ + 2it` term now has a proved half-plane reduction:
`norm_logDeriv_riemannZeta_le_real_neg_deriv_div` bounds it by the real-axis
value at the same real part whenever `σ > 1`. The remaining work is therefore
to turn the real-axis value at `σ = 1 + a / log |t|` into the required
`O(log |t|)` bound and to prove the local zero-candidate regular-part estimate.

## Verified Conditional Assembly

The low-risk Lean assembly around the 3-4-1 inequality and the bounded-height
patch is already proved in `ZeroFreeRegion.lean`.  These declarations do not
prove the missing analytic estimates; they make the exact remaining inputs
explicit.

```lean
ZeroFreeRegion.three_four_one_zero_free_high_height_of_log_deriv_bounds
ZeroFreeRegion.compact_patch_classical_zero_free_region
ZeroFreeRegion.classical_zero_free_region_of_log_deriv_bounds
ZeroFreeRegion.compact_patch_classical_zero_free_region_of_width
ZeroFreeRegion.compact_patch_classical_zero_free_region_of_width_re_im
ZeroFreeRegion.classical_zero_free_region_iff_high_height
ZeroFreeRegion.classical_zero_free_region_iff_high_height_re_im
ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov
ZeroFreeRegion.classical_width_le_vinogradov_korobov_width
```

Consequences:

- A high-height `c / log |t|` zero-free estimate now closes the full
  `classical_zero_free_region` target by `compact_patch_classical_zero_free_region`.
- A high-height coordinate estimate in variables `(β, t)` also closes the target
  via `compact_patch_classical_zero_free_region_re_im`.
- A Vinogradov-Korobov-width estimate, if supplied, now implies the classical
  zero-free-region target by the proved real-variable width comparison.

The remaining work for the classical zero-free region is therefore not the
algebraic 3-4-1 contradiction or bounded-height patching; it is the
zeta-specific logarithmic-derivative estimates described below.

The standard real-variable choice
`sigmaOf t = 1 + a / Real.log |t|` now has its elementary side conditions
proved:

- `ZeroFreeRegion.sigmaOf_log_gt_one`
  proves `1 < sigmaOf t` above height `2` when `a > 0`.
- `ZeroFreeRegion.sigmaOf_log_le_two`
  proves `sigmaOf t <= 2` above height `2` when `a <= log 2`.
- `ZeroFreeRegion.sigmaOf_log_sub_pos`
  proves `0 < sigmaOf t - beta` for every `beta < 1`.
- `ZeroFreeRegion.sigmaOf_log_le_one_add`
  proves `sigmaOf t <= 1 + d` from `a <= d log 2`, letting local
  right-neighborhood estimates feed the high-height assembly.
- `ZeroFreeRegion.closedBall_re_bounds` / `ZeroFreeRegion.ball_re_bounds` and
  `ZeroFreeRegion.closedBall_abs_im_ge_of_add_le` /
  `ZeroFreeRegion.ball_abs_im_ge_of_add_le`
  provide the disk geometry needed to transfer vertical-strip real-coordinate
  and high-height hypotheses onto Borel-Caratheodory/Jensen disks.
  The corresponding `sigma + I*t` specializations are
  `ZeroFreeRegion.closedBall_sigma_it_re_bounds`,
  `ZeroFreeRegion.ball_sigma_it_re_bounds`,
  `ZeroFreeRegion.closedBall_sigma_it_abs_im_ge_of_add_le`, and
  `ZeroFreeRegion.ball_sigma_it_abs_im_ge_of_add_le`; the combined wrappers
  `ZeroFreeRegion.closedBall_sigma_it_re_mem_Icc`,
  `ZeroFreeRegion.ball_sigma_it_re_mem_Icc`,
  `ZeroFreeRegion.closedBall_sigma_it_mem_verticalRegion`, and
  `ZeroFreeRegion.ball_sigma_it_mem_verticalRegion` package the same facts as
  direct real-strip and vertical-region membership statements, and
  `ZeroFreeRegion.closedBall_sigma_it_subset_verticalRegion` /
  `ZeroFreeRegion.ball_sigma_it_subset_verticalRegion` lift them to inclusion
  statements for whole local disks.  The `ZeroFreeRegion.verticalRegion`
  abbreviation names this set, and
  `ZeroFreeRegion.mapsTo_add_closedBall_zero_sigma_it_verticalRegion` /
  `ZeroFreeRegion.mapsTo_add_ball_zero_sigma_it_verticalRegion` supply the
  translated zero-centered disk shape used by the centered
  Borel-Caratheodory wrappers.  Finally,
  `ZeroFreeRegion.differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion`
  and
  `ZeroFreeRegion.meromorphicOn_closedBall_sigma_it_of_meromorphicOn_verticalRegion`
  restrict vertical-region regularity to the local disks required by
  Borel-Caratheodory and Jensen.  The combined
  `ZeroFreeRegion.borelCaratheodory_centered_verticalRegion` and
  `ZeroFreeRegion.borelCaratheodory_sub_centered_verticalRegion` wrappers are
  the direct Borel entry points for later zeta/log-derivative growth estimates;
  `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion` and
  `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion`
  specialize this interface to ζ itself.  Their pointwise variants
  `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion_of_re_le`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le`
  accept zeta growth estimates directly as
  `∀ z ∈ verticalRegion, Re(...) ≤ M` hypotheses, with
  `ZeroFreeRegion.mapsTo_riemannZeta_verticalRegion_of_re_le` and
  `ZeroFreeRegion.mapsTo_sub_riemannZeta_verticalRegion_of_re_le`
  supplying the `Set.MapsTo` conversion.  The corresponding half-radius
  wrappers
  `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion_half_radius_bound`,
  `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion_half_radius_bound`,
  `ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion_of_re_le_half_radius`,
  and
  `ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le_half_radius`
  remove the Borel denominator factors for ζ growth estimates.
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion` and
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion`
  provide the conditional `logDeriv ζ` versions with differentiability and
  real-part bounds left as explicit analytic inputs.  The pointwise variants
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_re_le`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_re_le`
  accept future height estimates directly in the usual form
  `∀ z ∈ verticalRegion, Re(...) ≤ M`, with
  `ZeroFreeRegion.mapsTo_logDeriv_riemannZeta_verticalRegion_of_re_le` and
  `ZeroFreeRegion.mapsTo_sub_logDeriv_riemannZeta_verticalRegion_of_re_le`
  supplying the `Set.MapsTo` conversion.  On positive-height right half-strips,
  `ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_verticalRegion_of_one_le_re`
  now discharges the differentiability hypothesis from
  `riemannZeta_ne_zero_of_one_le_re`; the wrappers
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`
  therefore leave only the real-part height estimate as the Borel input.  The
  signed wrappers
  `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re`,
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`,
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`
  provide the same interface in the `-logDeriv ζ` convention used by the
  3-4-1 inequality.  The general half-radius wrappers
  `ZeroFreeRegion.borelCaratheodory_centered_half_radius_bound` and
  `ZeroFreeRegion.borelCaratheodory_sub_centered_half_radius_bound`, plus the
  ambient vertical-region forms
  `ZeroFreeRegion.borelCaratheodory_centered_verticalRegion_half_radius_bound`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_centered_verticalRegion_half_radius_bound`,
  convert the Borel disk-denominator terms into the fixed half-radius bounds
  `2M + 3||f(c)||` and `2M`.  The positive `logDeriv ζ` specializations
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`,
  together with the signed specializations
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`,
  expose those fixed half-radius bounds in both logarithmic-derivative sign
  conventions;
  `ZeroFreeRegion.jensen_circleAverage_log_norm_verticalRegion` is the matching
  Jensen entry point for zero-count and divisor estimates.
- The zeta-specific regularity layer now includes
  `ZeroFreeRegion.differentiableOn_riemannZeta_verticalRegion_of_pos_height`,
  `ZeroFreeRegion.meromorphicOn_riemannZeta_verticalRegion`,
  `ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_verticalRegion`, and the
  right-half-strip differentiability theorem for `logDeriv ζ`, plus
  Jensen specializations for ζ and `logDeriv ζ` on `sigma + I*t` disks:
  `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_verticalRegion`
  and
  `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion`.

## Mathlib API Check

The local Mathlib already contains more relevant complex-analysis API than the
comments in `ZeroFreeRegion.lean` suggest:

- `Complex.borelCaratheodory` and `Complex.borelCaratheodory_zero` exist in
  `Mathlib.Analysis.Complex.BorelCaratheodory`.
  The project now also proves the centered wrappers
  `ZeroFreeRegion.borelCaratheodory_centered` and
  `ZeroFreeRegion.borelCaratheodory_zero_centered`, so future zeta estimates
  can work directly on disks centered at `1+it` or nearby shifted points.
  The oscillation wrapper `ZeroFreeRegion.borelCaratheodory_sub_centered`
  also packages the common centered-function use case `f - f(c)`.
- `MeromorphicOn.circleAverage_log_norm` exists in
  `Mathlib.Analysis.Complex.JensenFormula`; this is the local Jensen formula
  over closed balls for meromorphic functions.  The project now specializes it
  to `riemannZeta` and `logDeriv riemannZeta` as
  `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_closedBall` and
  `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall`.
- `Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'` and
  related declarations exist in `Mathlib.Analysis.Complex.Hadamard`.
- `PowerSeries.exists_isWeierstrassFactorization` exists, but this is
  Weierstrass preparation for formal power series over complete local rings.
  It is not a global Hadamard product/factorization theorem for entire
  functions of finite order.

I did not find a Mathlib theorem that directly states the global Hadamard
factorization/product for finite-order entire functions or a ready-made
classical zeta zero-free region.

Useful checked names:

```lean
#check Complex.borelCaratheodory
#check ZeroFreeRegion.borelCaratheodory_centered
#check ZeroFreeRegion.borelCaratheodory_zero_centered
#check ZeroFreeRegion.borelCaratheodory_sub_centered
#check MeromorphicOn.circleAverage_log_norm
#check ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_closedBall
#check ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall
#check Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
#check PowerSeries.exists_isWeierstrassFactorization
#check riemannZeta_residue_one
#check differentiableAt_riemannZeta
#check riemannZeta_ne_zero_of_one_le_re
#check ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
```

## Minimal Missing Lemmas

The following is the smallest useful Lean decomposition I see.  The names are
suggestions; statements should be adjusted when implementation starts.

### 1. Zeta Meromorphicity on Closed Balls

Mathematical statement:
`ζ` is meromorphic on every closed ball, with only a simple pole at `1`.

Suggested Lean statement:

```lean
lemma meromorphicOn_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn riemannZeta (Metric.closedBall c R)

lemma riemannZeta_divisor_pole_one
    (U : Set ℂ) (hU : 1 ∈ U) :
    (MeromorphicOn.divisor riemannZeta U) 1 = -1
```

Mathlib status:
`differentiableAt_riemannZeta`, `riemannZeta_residue_one`, and the completed
zeta API are enough for the local meromorphicity step.  This project now proves
`ZeroFreeRegion.meromorphicAt_riemannZeta_one` and
`ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall`.

Difficulty:
This block is now done, including
`ZeroFreeRegion.meromorphicOrderAt_riemannZeta_one` and
`ZeroFreeRegion.divisor_riemannZeta_pole_one`.  The logarithmic derivative is
also connected to this API by
`ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_closedBall`; the local
denominator condition is recorded as
`ZeroFreeRegion.eventually_ne_zero_riemannZeta_nhdsNE_one`.  The local
principal-part behavior is now also proved as
`ZeroFreeRegion.tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne`, namely
`(s - 1) * logDeriv riemannZeta s -> -1` in the punctured neighborhood of
`1`.  This has also been packaged into the local norm bound
`ZeroFreeRegion.eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one`,
which says eventually near the pole
`‖logDeriv riemannZeta s‖ <= 2 / ‖s - 1‖`.  The same eventual bound is
available in quotient notation as
`ZeroFreeRegion.eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
and
`ZeroFreeRegion.eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`.
For the real-valued estimates used directly by the 3-4-1 inequality, this
has also been converted to
`ZeroFreeRegion.eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`.
The constant bookkeeping is not tied to `2`: for every `C > 1`, the local
principal-part limit also gives
`ZeroFreeRegion.eventually_norm_mul_logDeriv_riemannZeta_lt_const`,
`ZeroFreeRegion.eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one`,
`ZeroFreeRegion.eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`,
`ZeroFreeRegion.eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`,
and
`ZeroFreeRegion.eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`.
The corresponding one-sided real-part form is
`ZeroFreeRegion.eventually_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`.
It is also packaged into the disk-shaped
`ZeroFreeRegion.exists_punctured_ball_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one`.
The same local estimate is also available on a smaller closed punctured ball as
`ZeroFreeRegion.exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one`,
which is the form needed when a later argument ranges over compact closed
local neighborhoods.
For compatibility with the sign conventions used in the 3-4-1 contradiction,
the closed-ball estimate is also exposed in explicit quotient notation as
`ZeroFreeRegion.exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`
and
`ZeroFreeRegion.exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`.
The corresponding closed-ball real-part estimate is
`ZeroFreeRegion.exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one`.
The flexible-constant closed-ball quotient analogues are
`ZeroFreeRegion.exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`
and
`ZeroFreeRegion.exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`;
the corresponding real-part analogue is
`ZeroFreeRegion.exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`.
The one-sided real-part closed-ball form is
`ZeroFreeRegion.exists_punctured_closedBall_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one`.
For the real-axis term in the 3-4-1 contradiction, this has also been
specialized at the concrete norm level as
`ZeroFreeRegion.exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one`,
which yields `norm (-zeta'/zeta)(sigma) <= 2 / (sigma - 1)` for `1 < sigma`
sufficiently close to `1`; at the concrete real-part level as
`ZeroFreeRegion.exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one`
and
`ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one`;
and at the flexible norm level as
`ZeroFreeRegion.exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one`,
which yields `norm (-zeta'/zeta)(sigma) < C / (sigma - 1)` for `1 < sigma`
sufficiently close to `1`, and at the real-part level as
`ZeroFreeRegion.exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one`,
which yields `|Re(-zeta'/zeta)(sigma)| < C / (sigma - 1)` for
`1 < sigma` sufficiently close to `1`.
The direct one-sided real-axis form is
`ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one`.
These estimates are also packaged in the exact real-axis input shape used by
the 3-4-1 high-height assembly:
`ZeroFreeRegion.exists_rightNeighborhood_hreal_two_div_sub_one` and
`ZeroFreeRegion.exists_rightNeighborhood_hreal_const_div_sub_one` produce the
`hreal` hypothesis for `realBound t = 2 / (sigmaOf t - 1)` or
`realBound t = C / (sigmaOf t - 1)` whenever the chosen `sigmaOf t` remains in
the local right neighborhood of `1`.
For the standard choice `sigmaOf t = 1 + a / log |t|`, the concrete and
flexible versions are now specialized further as
`ZeroFreeRegion.exists_sigmaOf_log_hreal_two_div_sub_one` and
`ZeroFreeRegion.exists_sigmaOf_log_hreal_const_div_sub_one`.  These leave only
the expected smallness constraints on `a`: positivity, `a <= log 2`, and
`a <= d log 2` for the local-neighborhood radius returned by the pole estimate.
The same inputs are also normalized into the vertical-height scale by
`ZeroFreeRegion.exists_sigmaOf_log_hreal_two_mul_log_div` and
`ZeroFreeRegion.exists_sigmaOf_log_hreal_const_mul_log_div`, giving the real-axis
term directly as `<= 2 * log |t| / a` or `<= C * log |t| / a`.
The half-plane L-series triangle inequality now also gives weak `sigma + 2it`
controls:
`ZeroFreeRegion.exists_sigmaOf_log_two_t_norm_bound_const_mul_log_div` and
`ZeroFreeRegion.exists_sigmaOf_log_two_t_bound_const_mul_log_div`.  These have
the same `<= C * log |t| / a` scale, so they do not close the classical
3-4-1 margin.  They mark the exact limit of what follows from absolute
convergence alone; the remaining analytic estimate must remove this `1/a`
loss and prove a genuine vertical-strip `O(log |t|)` bound.
This obstruction is now formalized as
`ZeroFreeRegion.sigmaOf_log_weak_two_t_margin_impossible`: once the real-axis
and `sigma + 2it` terms both carry coefficients at least `1/a`, the required
constant inequality is impossible for every positive width `c`, even before any
nonnegative regular-part contribution is added.  The existential wrapper
`ZeroFreeRegion.no_sigmaOf_log_margin_constants_with_weak_two_t` states the
same obstruction as nonexistence of positive constants `a,c` satisfying the
standard weak-margin inequality.
The theorem
`ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds`
then packages this standard `sigmaOf` choice into the full verified
3-4-1 high-height assembly and the compact bounded-height patch.  Its only
remaining hypotheses are the two shifted logarithmic-derivative estimates and
the final real-variable negativity margin.
The pure real-variable part of that final margin is now isolated as
`ZeroFreeRegion.three_four_one_sigmaOf_log_margin`: once the shifted estimates
have constants satisfying `3*Creal/a + 4*Czero + Ctwo < 4/(a+c)`, the 3-4-1
upper bound is strictly negative for every zero candidate
`beta >= 1 - c / log |t|`.
The small-constant choice itself is also proved as
`ZeroFreeRegion.exists_sigmaOf_log_margin_constants`: if the real-axis
coefficient satisfies `1 < C < 4/3` and the combined shifted-remainder constant
`K` is nonnegative, it produces positive `a,c` satisfying both smallness
constraints and the strict margin inequality.
The shifted-estimate specialization
`ZeroFreeRegion.exists_sigmaOf_log_margin_constants_for_shift_bounds` removes
the `K` bookkeeping when the remaining constants are already named as
nonnegative `Czero,Ctwo`, producing the exact margin
`3*C/a + 4*Czero + Ctwo < 4/(a+c)`.
The same-coefficient specialization
`ZeroFreeRegion.exists_sigmaOf_log_margin_constants_same_const` packages the
frequent case `Czero = Ctwo = B`, producing `3*C/a + 5*B < 4/(a+c)`.
The wrapper
`ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_shift_bounds`
combines this algebra with the closure theorem, leaving exactly the two
zeta-specific shifted estimates:
`Re(-zeta'/zeta)(sigma+it) <= -1/(sigma-beta) + Czero log |t|` at a zero
candidate and `Re(-zeta'/zeta)(sigma+2it) <= Ctwo log |t|`.
Finally,
`ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates`
combines the local pole input, small-constant choice, standard `sigma`, 3-4-1
contradiction, and compact patch into one conditional theorem.  At this point,
the quantitative zero-free-region chain has no remaining real-variable
assembly gap; the remaining gap is the pair of zeta-specific shifted estimates.
Two caller-facing variants remove incidental parameters:
`ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_nonneg_constants`
replaces the bundled `0 <= 4*Czero + Ctwo` hypothesis by individual
nonnegativity of `Czero,Ctwo`,
`ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_nonneg_constants`
packages that general nonnegative interface as one existential analytic input,
`ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths`
fixes the real-axis coefficient to `5/4`,
`ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths_nonneg_constants`
combines those two simplifications,
`ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_five_fourths_nonneg_constants`
packages that fixed `5/4` nonnegative interface as one existential analytic
input, and
`ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const`
uses one nonnegative logarithmic coefficient for both shifted estimates.
`ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const_high_height`
packages that same-constant input when the shifted estimates are available
only above a sufficiently large height; the compact patching in the closure
handles the remaining bounded-height range.
The wrappers
`ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const`
then fix the height cutoff to `2` and package the remaining gap as one
existential input: a nonnegative logarithmic coefficient `B` that proves both
shifted estimates.  Thus the next analytic task is not more 3-4-1 assembly;
it is proving that `B` exists for the zeta-specific shifted logarithmic
derivative bounds.
The first regular-part bridge is
`ZeroFreeRegion.classical_zero_free_region_of_regular_part_bound_and_two_t_bound`:
instead of asking directly for the zero-candidate shifted estimate, it accepts
the Borel-Caratheodory/Jensen-shaped regular-part estimate
`Re(-zeta'/zeta)(s)+1/(Re(s)-Re(rho)) <= B log |Im(s)|`, plus the matching
`sigma+2it` logarithmic bound.  Its existential wrapper
`ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_bound_and_two_t_bound`
packages those two remaining analytic estimates under one nonnegative
coefficient.
The narrower norm-bound bridge is
`ZeroFreeRegion.classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound`.
It accepts the more natural Borel/Jensen output
`||-zeta'/zeta(s)+(s-rho)^(-1)|| <= B log |Im(s)|`; the algebraic lemma
`ZeroFreeRegion.inv_sub_same_im_re` converts the same-height principal part
into `1/(Re(s)-Re(rho))`, and `Re(z) <= ||z||` supplies the real-part estimate.
Its existential wrapper
`ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound`
packages the quotient-notation norm input.  The caller-facing version closest
to future Borel/Jensen work is
`ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound`,
with existential wrapper
`ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_two_t_bound`:
prove the same norm regular-part estimate in `-logDeriv zeta` notation and the
matching `sigma+2it` logarithmic bound for one nonnegative coefficient `B`.
The two-coefficient wrappers
`ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bounds`
remove even that bookkeeping requirement: the regular-part norm estimate and
the `sigma+2it` estimate may be proved with separate nonnegative coefficients,
which the Lean proof merges using `max` and positivity of `log |t|` at height
at least `2`.
The fully norm-bound wrappers
`ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds`
also allow the `sigma+2it` input to be supplied as a norm estimate, using
`Re(z) <= ||z||` to recover the real-part bound required by the 3-4-1
combination.  This is the most analysis-facing conditional interface currently
available in the project.
One further wrapper removes the special `sigma+2it` input altogether:
`ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
accepts a standard vertical-strip estimate
`||-logDeriv zeta(z)|| <= B log |Im(z)|` for `1 <= Re(z) <= 2` and
`|Im(z)| >= 2`.  It specializes this estimate at `z = sigma + 2it`; the
auxiliary lemma `ZeroFreeRegion.log_abs_two_mul_le_two_log_abs` proves
`log |2t| <= 2 log |t|`, so the coefficient only doubles.  Its existential
wrapper
`ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
is now the highest-level conditional interface for this branch.
The sign-convention wrappers
`ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
present the same interface in the standard local-zero form
`||logDeriv zeta(s) - (s-rho)^(-1)|| <= B log |Im(s)|`, converting to the
signed 3-4-1 convention by `||-x|| = ||x||`.  This is the preferred statement
for estimates that are already available from height `2`.
The high-height wrappers
`ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
are the preferred interface for future Borel/Jensen principal-part estimates:
they require the regular-part and vertical-strip logarithmic-derivative bounds
only above an arbitrary cutoff `T0 >= 2`, then use the verified compact patch to
fill the bounded-height gap in the final classical zero-free-region target.
The affine-log wrappers
`ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_bound_and_vertical_logDeriv_norm_affine_log_bound_high_height`
are even closer to the expected Borel/Jensen output: they accept estimates of
the form `A + B log |Im|` above height `3`, absorb the additive constants using
`1 <= log |Im|`, and then feed the high-height logarithmic interface.
The coordinate wrappers
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_bounds_high_height`
state the same affine-log inputs directly in real variables `sigma`, `beta`,
and `t`, matching the usual analytic proof notation around points `sigma+it`
and same-height zero candidates `beta+it`.
The single-constant wrappers
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height`
specialize this one step further to the common estimate shape
`C * (1 + log |t|)` for both remaining zeta-specific bounds.
The safe-height logarithm wrappers
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
accept the equally common shape `C * log(|t| + 3)`.  The comparison lemma
`ZeroFreeRegion.log_abs_add_three_le_two_log_abs` proves
`log(|t| + 3) <= 2 log |t|` above height `3`, so these estimates feed the same
coordinate affine-log closure.
This is still conditional; it does not prove the quantitative zero-free region
until those two zeta-specific estimates are proved.
The next work starts from these meromorphic/nonvanishing/principal-part facts
and proves the vertical-height logarithmic-derivative estimates needed for the
quantitative strip.

### 2. Polynomial Growth for Zeta in Vertical Disks

Mathematical statement:
On fixed-radius disks or fixed-width strips near `Re(s) = 1`, `ζ(s)` has
polynomial growth in `|Im(s)|`.

Suggested Lean statement:

```lean
lemma riemannZeta_norm_le_poly_vertical
    (A B T0 R : ℝ) :
    0 < A → 0 ≤ B → 0 < R → 2 ≤ T0 →
    (∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc (-(R + 1)) (R + 2) →
      ‖riemannZeta z‖ ≤ A * |z.im| ^ B)
```

For implementation, do not quantify over arbitrary constants as above; prove an
existential package:

```lean
lemma exists_riemannZeta_poly_bound_vertical :
    ∃ A > 0, ∃ B ≥ 0, ∃ T0 ≥ 2,
      ∀ z : ℂ, T0 ≤ |z.im| → z.re ∈ Set.Icc (-1) 3 →
        ‖riemannZeta z‖ ≤ A * |z.im| ^ B
```

Mathlib status:
No direct zeta vertical-growth theorem found.  Mathlib has the functional
equation and differentiability/completed-zeta infrastructure, so this should be
proved from existing zeta continuation and Gamma estimates, but it is not an
immediate API call.

Difficulty:
High.  This is analytic-number-theory infrastructure rather than Lean algebra.
It is the main input needed before Borel-Caratheodory can produce
`O(log |t|)` logarithmic-derivative bounds.

### 3. Borel-Caratheodory Log-Derivative Bound

Mathematical statement:
For large `|t|`, away from zeros and the pole at `1`, the logarithmic
derivative of `ζ` in a fixed neighborhood of `1 + it` is `O(log |t|)`, after
accounting for any zero contribution inside the disk.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_regular_part_bound
    (C T0 : ℝ) :
    0 < C → 2 ≤ T0 →
    ∀ s ρ : ℂ,
      T0 ≤ |s.im| →
      s.re ∈ Set.Icc 1 2 →
      riemannZeta ρ = 0 →
      ρ.im = s.im →
      ρ.re < 1 →
      0 < s.re - ρ.re →
      ((-deriv riemannZeta s / riemannZeta s).re
        + 1 / (s.re - ρ.re)) ≤ C * Real.log |s.im|
```

Mathlib status:
`Complex.borelCaratheodory` exists.  `MeromorphicOn.logDeriv` and
`logDeriv` infrastructure exist.  This repository now has the notation bridges
`ZeroFreeRegion.logDeriv_riemannZeta_eq_deriv_div` and
`ZeroFreeRegion.neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re`, so the
remaining gap is the zeta-specific specialization that combines meromorphicity,
zero extraction, and polynomial growth into the stated regular-part estimate.

Difficulty:
High.  This is the core formalization of the classical Borel-Caratheodory
route.

### 4. Pole-Side Log-Derivative Bound

Mathematical statement:
Near the pole at `1`, on the real axis just to the right of `1`,
`-ζ'(σ)/ζ(σ) ≤ 1/(σ - 1) + O(1)`.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_real_near_one_upper
    (C : ℝ) :
    0 ≤ C →
    ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
        ≤ 1 / (σ - 1) + C
```

Mathlib status:
`riemannZeta_residue_one` exists, and this file has `residue_bounds`, but no
ready logarithmic-derivative estimate was found.

Difficulty:
Medium.  This should follow from writing
`ζ(s) = 1/(s - 1) + h(s)` with `h` analytic and bounded on a small disk, or
equivalently `(s - 1)ζ(s)` nonzero and analytic near `1`.

### 5. Off-Zero Log-Derivative Bound at `σ + 2it`

Mathematical statement:
The third 3-4-1 point has no forced zero singularity and is bounded by
`O(log |t|)`.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_two_t_bound
    (C T0 : ℝ) :
    0 < C → 2 ≤ T0 →
    ∀ σ t : ℝ, T0 ≤ |t| → 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
        riemannZeta ((σ : ℂ) + 2 * I * t)).re
        ≤ C * Real.log |t|
```

Mathlib status:
Same as lemma 3: the complex-analysis tools exist, but the zeta-specific bound
does not.

Difficulty:
Medium to High.  Once lemma 3 is proved as a general regular-part bound, this
should be a specialization with no zero subtraction.  Proving it separately
would duplicate work.

### 6. Zero Contribution Bound

Mathematical statement:
If `ρ = β + it` is a zero with `β < 1` and `σ > 1`, then the point
`s = σ + it` contributes the negative term `-1/(σ - β)` to
`Re(-ζ'/ζ(s))`, up to the regular-part bound from lemma 3.

Suggested Lean statement:

```lean
lemma zeta_logDeriv_at_zero_height_upper
    (C T0 : ℝ) :
    0 < C → 2 ≤ T0 →
    ∀ σ t β : ℝ,
      T0 ≤ |t| → 1 < σ → σ ≤ 2 → β < 1 →
      riemannZeta (β + I * t) = 0 →
      (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re
        ≤ -1 / (σ - β) + C * Real.log |t|
```

Mathlib status:
No direct theorem found.  This should be a thin corollary of lemma 3 after
normalizing the zero as `ρ = β + I*t`.

Difficulty:
Medium if lemma 3 exists; High otherwise.

### 7. Algebraic 3-4-1 Contradiction

Mathematical statement:
Given the three upper bounds above, there is a constant `c > 0` such that no
zero can satisfy `β ≥ 1 - c / log |t|` for large `|t|`.

Suggested Lean statement:

```lean
lemma three_four_one_zero_free_high_height
    (C T0 : ℝ) (hC : 0 < C) (hT0 : 2 ≤ T0)
    (hreal :
      ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
          ≤ 1 / (σ - 1) + C)
    (hzero :
      ∀ σ t β : ℝ, T0 ≤ |t| → 1 < σ → σ ≤ 2 → β < 1 →
        riemannZeta (β + I * t) = 0 →
        (-deriv riemannZeta ((σ : ℂ) + I * t) /
          riemannZeta ((σ : ℂ) + I * t)).re
          ≤ -1 / (σ - β) + C * Real.log |t|)
    (htwo :
      ∀ σ t : ℝ, T0 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * I * t) /
          riemannZeta ((σ : ℂ) + 2 * I * t)).re
          ≤ C * Real.log |t|) :
    ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| →
      riemannZeta s ≠ 0
```

Lean status:
This is already proved in the more flexible source-level form
`three_four_one_zero_free_high_height_of_log_deriv_bounds`.

Remaining difficulty:
None for the conditional assembly.  The real work is still proving the three
analytic estimates supplied as hypotheses.

### 8. Compact-to-All-Heights Patching

Mathematical statement:
If the quantitative region is proved for `|t| ≥ T0`, combine it with
`classical_zero_free_region_compact T0` to obtain the target for every
`|t| ≥ 2`.

Suggested Lean statement:

```lean
lemma compact_patch_classical_zero_free_region
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region
```

Lean status:
This is already proved as `compact_patch_classical_zero_free_region`, with
coordinate and arbitrary-width variants:
`compact_patch_classical_zero_free_region_re_im`,
`compact_patch_classical_zero_free_region_of_width`, and
`compact_patch_classical_zero_free_region_of_width_re_im`.

Remaining difficulty:
None for patching.  The high-height estimate remains the missing input.

## Suggested Execution Order

1. Prove the local pole logarithmic-derivative bound near `1` using the proved
   simple-pole/divisor API.
2. Prove a reusable Borel-Caratheodory/Jensen regular-part estimate for
   meromorphic functions with polynomial growth.
3. Specialize it to zeta to obtain the zero-height and `2t` estimates.
4. Feed those estimates into the already-proved conditional 3-4-1 assembly.
5. Only then convert `classical_zero_free_region` from `def ... : Prop` to a
   theorem, and verify with `lake env lean -R . ZeroFreeRegion.lean`.

## Already Filled Non-Analytic Lemmas

The non-analytic Lean work that used to be the easiest target is now complete:

- conditional high-height algebra wrapping the 3-4-1 contradiction;
- compact patching from high height to all `|t| ≥ 2`;
- coordinate-form patching in `(β, t)`;
- arbitrary-width patching;
- real-variable comparison showing the Vinogradov-Korobov width dominates a
  classical `c / log |t|` width.
- half-plane von Mangoldt L-series triangle inequality reducing
  `‖logDeriv ζ(s)‖` to the real-axis `-Re(ζ'/ζ(Re(s)))` for `Re(s) > 1`.

The next useful Lean work is zeta-specific: logarithmic-derivative estimates
and Borel-Caratheodory/Jensen specialization.
