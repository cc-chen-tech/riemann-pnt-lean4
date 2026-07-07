# Zero-Free Region Chain

This note audits the remaining Lean work needed to turn the current
zero-free-region infrastructure into the target
`ZeroFreeRegion.classical_zero_free_region : Prop`.

Current Lean status: `ZeroFreeRegion.lean` checks with
`lake env lean -R . ZeroFreeRegion.lean`.  The quantitative target is still a
`def ... : Prop`, not a proved theorem.

## Current Distance Boundary

The repository has formalized the front half of the de la Vallee Poussin
machinery:

```text
von Mangoldt series for -zeta'/zeta
        -> 3-4-1 inequality
        -> compact zero-free strip
        -> conditional high-height closure interfaces
```

It has not yet crossed the analytic boundary needed for the classical
zero-free region.  The next hard input is not a wrapper or documentation item;
it is a boundary-strip logarithmic-derivative estimate, for example:

```lean
∃ B T0, ∀ z : ℂ,
  1 ≤ z.re → z.re ≤ 2 → T0 ≤ |z.im| →
  ‖logDeriv riemannZeta z‖ ≤ B * Real.log |z.im|
```

The existing fixed-margin theorem proves this only in half-planes
`1 + ε ≤ Re(z)`.  That follows from absolute convergence and does not imply the
uniform boundary-strip estimate above.  A second missing input is the
zero-candidate regular-part estimate

```text
Re(-ζ'/ζ(σ + i t)) <= -1 / (σ - β) + O(log |t|)
```

when `ρ = β + i t` is a zero.  These are the hard analytic estimates usually
supplied by zeta growth plus Borel-Caratheodory, Jensen/Hadamard, or equivalent
zero-repulsion machinery.

The boundary-strip estimate now has named Lean interfaces:
`ZeroFreeRegion.LogDerivVerticalLogBound`,
`ZeroFreeRegion.NegLogDerivVerticalLogBound`, and
`ZeroFreeRegion.ReNegDerivDivVerticalLogBound`.  The constructors
`ZeroFreeRegion.logDeriv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`,
`ZeroFreeRegion.negLogDeriv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`,
and
`ZeroFreeRegion.reNegDerivDiv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
convert future affine `A + B log(|t|+3)` high-height estimates into these
interfaces.  They are proved normalization handoffs; they do not prove the
zeta-specific estimate.
If the future high-height theorem is already available in the exact
`B log |t|` scale, the constructors
`ZeroFreeRegion.logDerivVerticalLogBound_of_high_height_log_abs_bound`,
`ZeroFreeRegion.negLogDerivVerticalLogBound_of_high_height_log_abs_bound`, and
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_high_height_log_abs_bound`
package it directly as the named vertical interfaces.
The named interfaces also feed the shifted 3-4-1 inputs directly via
`ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_LogDerivVerticalLogBound`,
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_LogDerivVerticalLogBound`,
and
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_NegLogDerivVerticalLogBound`.
For the higher-degree BTY detector, the mixed bridge
`ZeroFreeRegion.log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound`
uses the same named vertical bound for all nonzero detector frequencies and
leaves only the real-axis `k = 0` quotient bound as a separate input.
The fixed-margin variant
`ZeroFreeRegion.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound`
discharges that center bound from the existing `Re(s) >= 1 + epsilon` estimate
when the caller stays a fixed distance to the right of the boundary.
Their `_simplified` variants use `btyDetectorCoeff_mixed_center_sum` to expose
the evaluated noncentral coefficient `4431901 / 2485395`.

The matching zero-candidate regular-part estimate is now named as well:
`ZeroFreeRegion.LogDerivRegularPartLogBound` and
`ZeroFreeRegion.MultiplicityLogDerivRegularPartLogBound` state the expected
`O(log |t|)` bound after subtracting the principal part of a zero on the same
horizontal line.  The proved closures
`ZeroFreeRegion.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_LogDerivVerticalLogBound`
and
`ZeroFreeRegion.classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_LogDerivVerticalLogBound`
show that the remaining classical zero-free-region target reduces to these
named regular-part estimates plus the named vertical estimate.  This is still
conditional: those two zeta-specific high-height estimates are not proved in
this checkout.

The direct real-part final assemblies
`ZeroFreeRegion.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_ReNegDerivDivVerticalLogBound`
and
`ZeroFreeRegion.classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_ReNegDerivDivVerticalLogBound`
close the same conditional target from the exact `Re(-zeta'/zeta)` vertical
estimate used by the 3-4-1 inequality.  This avoids requiring a stronger
vertical norm bound when future analysis proves the signed real-part estimate
directly.

The signed norm final assemblies
`ZeroFreeRegion.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`
and
`ZeroFreeRegion.classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`
accept the natural `||-logDeriv zeta||` convention produced by many local
Borel/Jensen estimates and convert it to the unsigned vertical norm interface.

The two hard inputs do not need to share the same cutoff.  The monotonicity
lemmas `ZeroFreeRegion.logDerivVerticalLogBound_mono_height`,
`ZeroFreeRegion.negLogDerivVerticalLogBound_mono_height`,
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_mono_height`,
`ZeroFreeRegion.logDerivRegularPartLogBound_mono_height`, and
`ZeroFreeRegion.multiplicityLogDerivRegularPartLogBound_mono_height` allow the
cutoff to be raised, and the existential closures
`ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_LogDerivVerticalLogBound`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_MultiplicityLogDerivRegularPartLogBound_and_exists_LogDerivVerticalLogBound`
as well as the corresponding `...exists_NegLogDerivVerticalLogBound` and
`...exists_ReNegDerivDivVerticalLogBound` variants
merge separately proved high-height regular-part and vertical estimates by
taking the maximum cutoff.

The primitive vertical estimates can now be fed directly into that final
assembly.  The proved closures
`ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_deriv_bound_zeta_lower_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_MultiplicityLogDerivRegularPartLogBound_and_deriv_bound_zeta_lower_bound_high_height`,
together with their `..._on_verticalRegion` variants, compose the
regular-part input with affine high-height control of `ζ'` and a positive
lower bound for `ζ`.  These theorems reduce the final target to standard
complex-analysis-shaped zeta estimates; they still do not prove those
primitive estimates.

For the vertical `logDeriv ζ` side specifically,
`ZeroFreeRegion.exists_norm_deriv_riemannZeta_bound_on_compact_vertical_band`
proves compact bounded-height control of `‖ζ'‖`, and
`ZeroFreeRegion.exists_deriv_riemannZeta_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
patches it with a future high-height affine derivative-growth estimate.
Together with
`ZeroFreeRegion.exists_norm_riemannZeta_pos_lower_bound_on_verticalRegion_of_compact_band_and_high_height`,
the wrapper
`ZeroFreeRegion.logDerivVerticalLogBound_of_compact_band_and_high_height_deriv_bound_zeta_lower_bound`
feeds primitive `ζ'` growth and positive `ζ` lower-bound inputs directly into
`LogDerivVerticalLogBound`.

For the 3-4-1 pair input specifically,
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_deriv_bound_and_zeta_lower_bound_high_height`
and
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height`
compose those primitive derivative/lower-bound or Cauchy sphere-growth inputs
directly into the ordinary and shifted `Re(-ζ'/ζ)` bounds at `σ+it` and
`σ+2it`.  These are handoff theorems, not the missing zeta-specific high-height
estimates themselves.

At the already-formed `logDeriv ζ` level,
`ZeroFreeRegion.exists_logDeriv_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
patches the proved compact bounded-height norm bound with a future high-height
affine logarithmic estimate on `‖z‖ + 3`, and
`ZeroFreeRegion.logDerivVerticalLogBound_of_compact_band_and_high_height_affine_log_norm_add_three_bound`
feeds the result into the named `LogDerivVerticalLogBound` interface.  The
signed pair
`ZeroFreeRegion.exists_negLogDeriv_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
and
`ZeroFreeRegion.negLogDerivVerticalLogBound_of_compact_band_and_high_height_affine_log_norm_add_three_bound`
does the same for the `-logDeriv ζ` convention used by 3-4-1.  The direct
real-part quotient pair
`ZeroFreeRegion.exists_reNegDerivDiv_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
and
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_compact_band_and_high_height_affine_log_norm_add_three_bound`
feeds an estimate already stated as `Re(-ζ'/ζ)` into
`ReNegDerivDivVerticalLogBound`.  This keeps the next hard target precise:
prove the high-height zeta-specific
affine/logarithmic estimate, not another compactness patch.

The even more direct wrappers
`ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_logDeriv_bound`,
`ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_negLogDeriv_bound`,
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_reNegDerivDiv_bound`,
with their multiplicity-aware analogues, accept a future high-height
`B log |t|` vertical estimate directly in the unsigned norm, signed norm, or
exact real-part quotient convention.  These are proved bookkeeping bridges;
the zeta-specific high-height estimates remain open analytic inputs.

The same named interfaces are also monotone in the bound constant:
`ZeroFreeRegion.logDerivVerticalLogBound_mono_const`,
`ZeroFreeRegion.negLogDerivVerticalLogBound_mono_const`,
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_mono_const`,
`ZeroFreeRegion.logDerivRegularPartLogBound_mono_const`, and
`ZeroFreeRegion.multiplicityLogDerivRegularPartLogBound_mono_const` let later
proofs replace separate constants by a larger shared constant without changing
the analytic target shape.

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

A fixed-margin version of this logarithmic control is already proved:
`exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re`
shows that for every `ε > 0` there is `C >= 0` with
`‖logDeriv ζ(z)‖ <= C * log(|Im z| + 3)` throughout `1 + ε <= Re z`.
This follows from absolute convergence, the L-series triangle inequality, and
real-axis antitonicity. It does not close the classical zero-free region, whose
missing estimate must hold uniformly in the boundary strip down to `Re z = 1`.
The shifted 3-4-1 third point has the corresponding fixed-margin forms:
`exists_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le`
handles the `σ+it` real-part quotient term, while
`exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le`
and
`exists_re_neg_deriv_div_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le`
bound `σ+2it` by `C * log(|t|+3)` whenever `1+ε <= σ`. The helper
`log_abs_two_mul_add_three_le_two_log_abs_add_three` absorbs the factor `2` in
the imaginary part.
The high-height forms
`exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin` and
`exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin`
put the same proved fixed-margin estimates into the exact `C * log |t|` scale.
They still assume `1+ε <= σ`, so they are not substitutes for the missing
boundary-strip estimate.
The one-entry package
`exists_re_neg_deriv_div_riemannZeta_fixed_margin_three_four_one_bounds` gives
one constant for the real-axis, `σ+it`, and `σ+2it` real-part terms together.
`exists_three_four_one_combination_le_log_abs_add_three_of_one_add_le` then
combines those bounds with the proved 3-4-1 nonnegativity, bounding the whole
fixed-margin combination by `O(log(|t|+3))`.
The exact high-height fixed-margin packages
`exists_norm_logDeriv_riemannZeta_fixed_margin_shift_pair_le_log_abs` and
`exists_re_neg_deriv_div_riemannZeta_fixed_margin_shift_pair_le_log_abs`
upgrade the two shifted points to one shared `C * log |t|` coefficient above
some `T0 >= 3`; `exists_three_four_one_combination_le_log_abs_of_fixed_margin`
does the same for the full 3-4-1 expression.  These are verified analogues of
the desired boundary-strip handoff, but they still require the fixed margin
`1+epsilon <= sigma`.

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
ZeroFreeRegion.classical_zero_free_region_high_height_re_im
ZeroFreeRegion.classical_zero_free_region_high_height_re_im_at_three
ZeroFreeRegion.classical_zero_free_region_high_height_mono_cutoff
ZeroFreeRegion.classical_zero_free_region_high_height_mono_cutoff_re_im
ZeroFreeRegion.classical_zero_free_region_high_height_exists_mono_cutoff
ZeroFreeRegion.classical_zero_free_region_high_height_exists_mono_cutoff_re_im
ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov
ZeroFreeRegion.classical_width_le_vinogradov_korobov_width
ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_mono_cutoff
ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_mono_cutoff_re_im
ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_exists_mono_cutoff
ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_exists_mono_cutoff_re_im
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
- `ZeroFreeRegion.riemannZeta_sigmaOf_log_ne_zero` and the
  `...add_I_mul_ne_zero` / `...add_two_I_mul_ne_zero` variants prove
  denominator nonvanishing for `ζ(sigmaOf t)`, `ζ(sigmaOf t + i t)`, and
  `ζ(sigmaOf t + 2 i t)` using the already-known half-plane nonvanishing.
  These are right-of-line specializations for logarithmic-derivative estimates,
  not a proof of the classical left-of-line zero-free region.
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_sigmaOf_log` and the
  `...add_I_mul` / `...add_two_I_mul` variants feed those same moving-line
  points into the local analytic hypotheses needed by the
  Borel-Caratheodory/Jensen/log-counting wrappers.
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_sigmaOf_log_add_I_mul_height_of_radius_le_width_of_height_add_le`
  lifts the moving real part `sigmaOf t` to closed disks centered at
  `sigmaOf t + i u` for an independent height `u`, assuming the disk radius
  stays inside the right half-plane width and the height condition keeps the
  disk away from the pole.  This is the reusable local regularity handoff for
  shifted-frequency centers.
- `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_sigmaOf_log_add_I_mul_of_radius_le_width_of_height_add_le`
  lifts the `sigmaOf t + i t` point statement to every point of a closed disk
  centered there, assuming the disk radius stays within the right half-plane
  width and the height condition keeps the disk away from the pole.  This is
  a local regularity handoff for future Borel/Jensen estimates, not the
  missing high-height `O(log |t|)` estimate.
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
  `ZeroFreeRegion.ball_sigma_it_abs_im_ge_of_add_le`.  The new direct
  hypotheses
  `ZeroFreeRegion.closedBall_sigma_it_one_le_re_of_add_le` and
  `ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le` turn numeric
  disk conditions into the pointwise right-half-plane and pole-exclusion inputs
  needed by the local `logDeriv ζ` layer.  The combined wrappers
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
  direct disk versions
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  use the numeric `sigma+I*t` disk geometry directly, avoiding the ambient
  `verticalRegion` detour when the estimate is naturally local.  The
  signed wrappers
  `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re`,
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`,
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le`
  provide the same interface in the `-logDeriv ζ` convention used by the
  3-4-1 inequality.  The direct signed disk wrappers
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  similarly avoid the ambient `verticalRegion` detour when the real-part
  estimate is naturally stated on a local right-half `sigma+I*t` ball.  Their
  half-radius versions
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`,
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`,
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`,
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
  remove the raw Borel disk denominator terms directly in the local disk
  geometry.  The affine direct disk variants
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`,
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`,
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`,
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
  accept `A + B log(||sigma+I*t||+3)` estimates directly and produce the
  same scale of local norm/oscillation bounds.  The right-shifted affine
  transfers
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius`
  apply the same Borel handoff from a disk centered at `(sigma+r)+I*t` to the
  left-shifted point `sigma+I*t`, while still leaving the local real-part and
  center estimates as hypotheses.  The widened comparison
  `ZeroFreeRegion.log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three`
  and the normalized right-shift wrappers
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  convert those right-shifted outputs to the pure `C log |t|` scale once the
  same local hypotheses are supplied.  The variants
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_log_abs_add_three_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_log_abs_add_three_re_le_half_radius`
  accept those local hypotheses directly in the safer `log(|t|+3)` height
  scale.  The reverse comparison
  `ZeroFreeRegion.log_abs_le_log_norm_sigma_add_I_mul_add_three`, together with
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`,
  lets those already-normalized outputs feed closures whose hypotheses are
  stated in the full complex-height `log(||sigma+it||+3)` scale.  The companion
  comparison
  `ZeroFreeRegion.log_abs_add_three_le_log_norm_sigma_add_I_mul_add_three`
  lets the proved fixed-margin half-plane bounds in the safe
  `log(|Im|+3)` scale feed those same full-height center estimates.  The
  quotient forms
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius`
  translate these norm bounds into the `Re(-zeta'/zeta)` convention consumed by
  the 3-4-1 inequality; the full-height counterparts
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
  expose the same quotient handoff in the `log(||sigma+it||+3)` scale.  The
  finite-family variants
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_finset_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_finset_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
  package this single-height handoff over a finite family of heights `tau k`,
  which is the Borel-side supplier shape needed by higher-degree detector
  polynomials before the remaining height-comparison work specializes
  `tau k` to shifted frequencies such as `k*t`.  The public API bridges
  `RiemannPNT.API.log_deriv_zeta_finset_single_lower_bound_auto_of_right_shift_borel_family`
  and
  `RiemannPNT.API.log_deriv_zeta_finset_single_lower_bound_auto_of_signed_right_shift_borel_family`
  now compose that finite-family Borel supplier with the automatic finite
  detector lower-bound theorem, eliminating the separate manual `hupper`
  handoff.  Their BTY specializations
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_right_shift_borel_family`
  and
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_signed_right_shift_borel_family`
  discharge the checked degree-16 detector certificate and coefficient
  side-conditions for the selected `k=1` term.  The uniform variants
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family`
  and
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_signed_right_shift_borel_family`
  additionally use the computed remaining-coefficient sum
  `6917296 / 2485395`, yielding the one-constant upper-bound interface needed
  after future global height comparisons.  The named-bound entrypoint
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound`
  gives the current exact handoff from a future `LogDerivVerticalLogBound` to
  the checked BTY detector, with the `k=0` center term still explicit; its
  fixed-margin companion
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound`
  removes that center input when `1 + epsilon <= sigma`.  The `_simplified`
  variants keep the same dependencies while exposing the evaluated coefficient
  sum.  The direct real-part counterparts
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_ReNegDerivDivVerticalLogBound`
  and
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_ReNegDerivDivVerticalLogBound`
  provide the same BTY handoff when the future vertical estimate is already
  stated as `Re(-zeta'/zeta)` rather than as a norm bound.  The exact
  high-height facades
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_logDeriv_bound`,
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_logDeriv_bound_simplified`,
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_negLogDeriv_bound`,
  and
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_negLogDeriv_bound_simplified`
  consume future exact-scale `||±logDeriv zeta|| <= B log |t|` norm estimates
  directly.  The real-part exact-scale facades
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound`
  and
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound_simplified`
  consume a future `Re(-zeta'/zeta) <= B log |t|` estimate directly.  The shifted versions
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius`
  supply the analogous `sigma+2it` third-term estimate, using
  `log |2t| <= 2 log |t|`; their full-height counterparts
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
  expose the same third-term handoff in the `log(||sigma+it||+3)` scale.  The
  pair packages
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius`
  combine the `t` and `2t` local Borel hypotheses into one shared
  `C log |t|` bound for both shifted real-part terms.  These are still
  conditional on the local zeta-specific Borel inputs; they only remove the
  duplicated final bookkeeping before the 3-4-1 inequality.  The full-height
  variants
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
  expose the same paired handoff in the `log(||sigma+it||+3)` scale.  The
  existential variants
  `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius_fixed_margin_center`
  and
  `ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius_fixed_margin_center`
  discharge the two center norm estimates automatically from the fixed-margin
  half-plane theorem; after this step, the right-shift pair bridge only needs
  local real-part Borel inputs on the disks centered at `(sigma+r)+it` and
  `(sigma+r)+2it`.  The
  general half-radius wrappers
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
  the affine full-height wrappers
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`,
  plus
  `ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  for the positive `logDeriv` bound and its centered oscillation in the
  `log(|t|+3)` height scale,
  together with the signed specializations
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_re_le_half_radius`,
  plus the signed affine wrappers
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_re_le_half_radius`,
  with
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  giving the signed `log(|t|+3)` height-scale variants,
  expose those fixed half-radius bounds in both logarithmic-derivative sign
  conventions.  The zero-candidate regular-part bridge
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_regularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  applies the same right-shifted normalization to
  `-logDeriv zeta(w) + (w-rho)^(-1)`, and
  `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius`
  converts it to the exact
  `Re(-zeta'/zeta)(sigma+it) + 1/(sigma-beta) <= C log |t|`
  zero-repulsion input.  The follow-up wrapper
  `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  discharges that bridge's center norm hypothesis using the proved
  fixed-margin `-logDeriv zeta` estimate and the elementary same-height
  principal-part distance bound.  Its full-height companion
  `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  keeps the center bound discharged while replacing the final `log |t|` scale
  by `log(||sigma+it||+3)`; the local regular-part differentiability and
  real-part hypotheses remain the unresolved analytic input.  The
  multiplicity-aware pair
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  and
  `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius`
  gives the same handoff for `-logDeriv zeta(w)+n(w-rho)^(-1)` with
  `n >= 1`, avoiding a hidden simple-zero assumption.  Its center-discharged
  companion
  `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  removes the multiplicity-aware center norm hypothesis at the explicit cost
  `(n : Real) / r`.  The full-height variant
  `ZeroFreeRegion.exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  gives the same center-discharged multiplicity handoff in the
  `log(||sigma+it||+3)` scale.  The positive-sign
  companion
  `ZeroFreeRegion.borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  handles `logDeriv zeta(w)-n(w-rho)^(-1)`, matching the direct output of
  local factorization estimates before sign conversion; its wrapper
  `ZeroFreeRegion.exists_borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius_fixed_margin_center`
  discharges the corresponding positive-sign center bound from the fixed-margin
  `logDeriv zeta` estimate and the same `(n : Real) / r` principal-part cost.
  The full-height scale
  companions
  `ZeroFreeRegion.borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
  and
  `ZeroFreeRegion.borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
  make the same multiplicity-aware handoff available to closures formulated
  with `log(||sigma+it||+3)`.  The positive-sign
  `ZeroFreeRegion.exists_borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center`
  variant additionally discharges the right-shifted center norm from the proved
  fixed-margin `logDeriv zeta` estimate in that full-height scale.  Its signed
  analogue
  `ZeroFreeRegion.exists_borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center`
  does the same directly for `-logDeriv zeta(w)+n(w-rho)^(-1)`, while
  `ZeroFreeRegion.re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius`
  converts that full-height regular-part norm bound into the matching
  zero-repulsion estimate.  The regular-part
  differentiability, real-part, and center bounds are still open zeta-specific
  analytic estimates;
  `ZeroFreeRegion.jensen_circleAverage_log_norm_verticalRegion` is the matching
  Jensen entry point for zero-count and divisor estimates.
- The zeta-specific regularity layer now includes
  `ZeroFreeRegion.differentiableOn_riemannZeta_verticalRegion_of_pos_height`,
  `ZeroFreeRegion.meromorphicOn_riemannZeta_verticalRegion`,
  `ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_verticalRegion`,
  `ZeroFreeRegion.meromorphicOn_neg_logDeriv_riemannZeta_verticalRegion`, and the
  right-half-strip differentiability theorem for `logDeriv ζ`, plus
  Jensen specializations for ζ, `logDeriv ζ`, and `-logDeriv ζ` on
  `sigma + I*t` disks:
  `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_verticalRegion`
  and
  `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion`
  and
  `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion`.
  The direct disk versions
  `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_sigma_it`,
  `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it`,
  `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it`,
  and
  `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms`
  specialize Jensen directly to the local `sigma+I*t` disk without routing
  through an ambient `verticalRegion`.  The positive-radius variants
  `ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_sigma_it_of_pos_radius`,
  `ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it_of_pos_radius`,
  `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_of_pos_radius`,
  and
  `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms_of_pos_radius`
  state the same formulas with closed balls of radius `R` under `0 < R`,
  matching the radius convention used by the local Borel-Caratheodory wrappers.
  The pointwise conversion
  `ZeroFreeRegion.log_norm_neg_logDeriv_riemannZeta_eq` and circle-average
  conversion
  `ZeroFreeRegion.circleAverage_log_norm_neg_logDeriv_riemannZeta_eq` make the
  Jensen left side identical in the `logDeriv ζ` and `-logDeriv ζ`
  conventions.  The corresponding divisor conversions
  `ZeroFreeRegion.divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall`
  and
  `ZeroFreeRegion.divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_verticalRegion`
  make the Jensen right-side divisor bookkeeping identical in both sign
  conventions, while
  `ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq`
  gives the same conversion for the Jensen trailing-coefficient term.  The
  packaged mixed-sign Jensen formulas
  `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall_unsigned_terms`
  and
  `ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion_unsigned_terms`
  expose exactly this combination.
- The value-distribution log-counting API is zero-centered, but the zero-free
  chain uses disks centered at points such as `σ+it`.  The project now proves
  `ZeroFreeRegion.valueDistribution_logCounting_translate_eq_circleAverage_sub_const`,
  which applies Mathlib's log-counting Jensen theorem to the translated
  function `z ↦ f (z+c)` and rewrites the circle average back to the original
  disk centered at `c`.  The zeta-specific wrappers
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage`
  make this bridge available for `logDeriv ζ` and the signed `-logDeriv ζ`
  convention used by 3-4-1.  The specialized wrappers
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_circleAverage_sub_const`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_circleAverage`
  instantiate the center as `σ + I*t`, matching the local disks used in the
  vertical-strip estimates.  The local-divisor wrappers
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor`
  compose that translated bridge with the closed-ball Jensen specialization,
  so future estimates can start directly from the divisor/trailing-coefficient
  side.  The `σ + I*t` specializations
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor`
  give the same direct handoff in the coordinates used by the high-height
  zero-free-region chain.  The trailing-coefficient translation lemmas
  `ZeroFreeRegion.meromorphicTrailingCoeffAt_comp_add_const_zero` and
  `ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero`
  then cancel the extra translated trailing-coefficient term.  The resulting
  pure wrappers
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure`
  express translated log-counting directly as the two local-divisor terms.
  Their `σ + I*t` specializations provide the cleanest current API for future
  high-height Jensen estimates.  The zero-divisor vanishing wrappers
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero`
  additionally turn a no-divisor hypothesis on the local closed ball into
  literal vanishing of the translated log-counting difference; the corresponding
  `σ + I*t` wrappers state this directly in the vertical-strip coordinates.
  The order-zero wrappers
  `ZeroFreeRegion.divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_order_eq_zero`
  add the next local step: an analytic estimate can now be routed through
  pointwise order zero of `logDeriv ζ` directly to log-counting vanishing,
  without manually opening the divisor definition.  The analytic-and-nonzero
  wrappers
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero`
  expose the same vanishing conclusion from the more natural local hypotheses
  produced by holomorphy and nonvanishing arguments.  The new analytic
  regularity bridge
  `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one`
  packages the right-half-plane zeta nonvanishing theorem into pointwise
  analyticity of `logDeriv ζ` away from the pole, while
  `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_of_ne_one_of_ne_zero`
  gives the closed-ball version needed by the local Jensen/log-counting layer.
  The right-half-plane wrappers
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
  now combine these facts into direct log-counting vanishing on local balls in
  `Re(s) >= 1`, leaving only pole exclusion and nonvanishing of `logDeriv ζ`
  as local hypotheses.  The disk-geometric specializations
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero`
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero`
  discharge the right-half-plane and pole-exclusion hypotheses directly from
  `1+|R| <= sigma`, `0 < H`, and `H+|R| <= |t|`, leaving only local
  nonvanishing of `logDeriv ζ` on the disk.  Their positive-radius forms
  `ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero_pos_radius`,
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero_pos_radius`,
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero_pos_radius`
  replace those numeric hypotheses by `1+R <= sigma` and `H+R <= |t|`
  under `0 < R`, which is the direct handoff shape from the Borel disk layer.
  The analyticity wrapper
  `ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half`
  exposes the same geometry as direct pointwise analyticity on the whole disk,
  and
  `ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero`
  lets signed Jensen/Borel estimates keep the local nonvanishing hypothesis in
  the `-logDeriv ζ` convention used by the 3-4-1 inequality.  The corresponding
  differentiability wrappers
  `ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half`
  and
  `ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half`
  are the direct centered-open-disk regularity inputs for future
  Borel-Caratheodory estimates.

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
#check ZeroFreeRegion.circleAverage_log_norm_neg_logDeriv_riemannZeta_eq
#check ZeroFreeRegion.divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall
#check ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq
#check ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall
#check ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall_unsigned_terms
#check ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_sigma_it
#check ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it
#check ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it
#check ZeroFreeRegion.jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_circleAverage_sub_const
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_circleAverage
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor
#check ZeroFreeRegion.meromorphicTrailingCoeffAt_comp_add_const_zero
#check ZeroFreeRegion.norm_meromorphicTrailingCoeffAt_comp_add_const_zero
#check ZeroFreeRegion.log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor_pure
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor_pure
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_divisor_eq_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_divisor_eq_zero
#check ZeroFreeRegion.divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero
#check ZeroFreeRegion.divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_analyticAt_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_order_eq_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_order_eq_zero
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_order_eq_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_order_eq_zero
#check ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
#check ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_analyticAt_ne_zero
#check ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
#check ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one
#check ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_of_ne_one_of_ne_zero
#check ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_of_one_le_re_of_ne_one
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_analyticAt_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_analyticAt_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero
#check ZeroFreeRegion.closedBall_sigma_it_one_le_re_of_add_le
#check ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
#check ZeroFreeRegion.valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero
#check ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
#check ZeroFreeRegion.logDeriv_riemannZeta_ne_zero_of_neg_logDeriv_ne_zero
#check ZeroFreeRegion.valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero
#check ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
#check ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half
#check ZeroFreeRegion.differentiableOn_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half
#check ZeroFreeRegion.differentiableOn_neg_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half
#check ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
#check ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
#check ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
#check ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le
#check ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
#check ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
#check ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
#check ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius
#check ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
#check ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
#check ZeroFreeRegion.borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
#check ZeroFreeRegion.borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius
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
The pole-side principal part has also been separated additively:
`ZeroFreeRegion.eventuallyEq_logDeriv_riemannZeta_simplePoleAtOne` proves
`logDeriv zeta(s) = -(s - 1)^-1 + logDeriv(unit)(s)` on a punctured
neighborhood of `1`,
`ZeroFreeRegion.analyticAt_logDeriv_riemannZetaPoleUnitAtOne` proves the unit
logarithmic derivative is analytic at `1`, and
`ZeroFreeRegion.eventually_norm_logDeriv_riemannZetaPoleUnitAtOne_le_const`
proves this regular term is locally bounded.  Consequently
`ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_inv_sub_one_add_const`
gives the sharper real-axis bookkeeping form
`Re(-zeta'/zeta)(sigma) <= 1 / (sigma - 1) + M` for real `sigma > 1`
sufficiently close to `1`.  This is a local pole-side theorem, not the missing
high-height vertical-strip estimate.
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
`ZeroFreeRegion.exists_sigmaOf_log_hreal_two_mul_log_div`,
`ZeroFreeRegion.exists_sigmaOf_log_hreal_inv_sub_one_add_const_log_bound`, and
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
The fixed-margin logarithmic bound
`ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re`
is useful evidence of the available half-plane control, but it applies only
after choosing a fixed `epsilon > 0`; it therefore cannot replace the missing
uniform boundary-strip input.
The same limitation applies to the fixed-margin `sigma + 2it` real-part bound:
it is a proved shifted-term estimate, but only under `1+epsilon <= sigma`.
The single-constant fixed-margin 3-4-1 package has the same limitation.
So does the fixed-margin full-combination upper bound, including its exact
high-height `C * log |t|` version
`ZeroFreeRegion.exists_three_four_one_combination_le_log_abs_of_fixed_margin`.
On the right edge, the new proved package
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_right_edge_three_four_one_bounds`
adds the real-axis center term to the right-edge shifted-pair estimate, and
`ZeroFreeRegion.exists_three_four_one_combination_le_log_abs_of_two_add_radius_le`
combines that three-term upper bound with 3-4-1 nonnegativity to give
`0 <= combination <= C * log |t|` whenever `2 + R <= sigma`.  This is a useful
boundary condition for Borel/Jensen strip arguments, but it still leaves the
main analytic gap unchanged: the classical zero-free region needs comparable
control inside the high boundary strip `1 <= sigma <= 2`.
The derived lower-bound form
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_sigma_it_lower_bound_log_abs_of_two_add_radius_le`
uses those right-edge upper bounds and the same 3-4-1 nonnegativity to prove
`-C * log |t| <= Re(-zeta'/zeta(sigma+i t))` on the right edge, matching the
sign and scale later zero-repulsion arguments consume.
Together with the direct right-edge upper bound, this gives the two-sided
real-part estimate
`ZeroFreeRegion.exists_abs_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_of_two_add_radius_le`.
For sign-convention compatibility, the weak moving-strip inventory now also
contains signed `-logDeriv zeta` norm variants:
`ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_neg_logDeriv_norm_bound_const_mul_log_div`,
`ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_const_mul_log_div`,
`ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_const_mul_log_div`,
`ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_log_scale`,
and `ZeroFreeRegion.exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_log_scale`.
These are useful public comparison interfaces, but they are still wrappers
around the absolute-convergence estimates and keep `B = C/a` in log-scale form.
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
The local bounded-unit side of these principal-part decompositions is now
automatic: `ZeroFreeRegion.exists_eventually_norm_logDeriv_le_const_of_analyticAt_ne_zero`
and its signed version prove local boundedness of the logarithmic derivative
for any analytic unit, and the `..._analyticAt_order_eq_nat_auto` lemmas
package this into punctured-ball regular-part bounds, including zeta-specific
auto wrappers.  These are local statements; the remaining hard input is still a
uniform high-height logarithmic coefficient, not local existence of some
constant.
The high-height wrappers
`ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
are the preferred interface for future Borel/Jensen principal-part estimates:
they require the regular-part and vertical-strip logarithmic-derivative bounds
only above an arbitrary cutoff `T0 >= 2`, then use the verified compact patch to
fill the bounded-height gap in the final classical zero-free-region target.
The coordinate unit-principal wrappers
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
state the same handoff directly in real variables `sigma`, `beta`, and `t`,
with the local principal part written as `(sigma-beta)^{-1}`.  They are the
non-multiplicity caller-facing form of the multiplicity-aware coordinate
closure.
The direct real-part coordinate wrappers
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_bound_and_vertical_reNegDerivDiv_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_reNegDerivDiv_bound_high_height`
keep the same regular-part input but consume the vertical estimate directly as
`Re(-zeta'/zeta) <= C log |t|`, matching the exact quantity in the 3-4-1
combination.
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
The signed coordinate affine variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_bounds_high_height`
give the same permissive `A + B log |t|` interface in the `-logDeriv zeta`
notation used by the 3-4-1 inequality.
The single-constant wrappers
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bound_high_height`
specialize this one step further to the common estimate shape
`C * (1 + log |t|)` for both remaining zeta-specific bounds.
The variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
allow different constants for those two Big-O estimates.
The signed variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height`,
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height`,
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height`,
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
provide the same one-constant and two-constant Big-O handoffs in the
`-logDeriv zeta` convention used by the 3-4-1 inequality.
The safe-height logarithm wrappers
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
accept the equally common shape `C * log(|t| + 3)`.  The comparison lemma
`ZeroFreeRegion.log_abs_add_three_le_two_log_abs` proves
`log(|t| + 3) <= 2 log |t|` above height `3`, so these estimates feed the same
coordinate affine-log closure.
The single-constant signed versions
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bound_high_height`
give the same safe-height handoff in `-logDeriv zeta` notation.
The variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
drop the unnecessary shared-constant assumption by allowing different
regular-part and vertical-strip constants.
The signed variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_abs_add_three_bounds_high_height`
provide the same `log(|t|+3)` interface in the `-logDeriv zeta`
convention used by the 3-4-1 inequality.
The full-height variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
accept estimates stated with `log(||sigma+it|| + 3)` above height `5`; the
comparison lemmas
`ZeroFreeRegion.norm_sigma_add_I_mul_le_abs_add_two` and
`ZeroFreeRegion.log_norm_sigma_add_I_mul_add_three_le_two_log_abs` normalize
that scale to `log |t|` on the strip `1 <= sigma <= 2`.
The named constructors
`ZeroFreeRegion.logDerivVerticalLogBound_of_affine_log_norm_add_three_bound_high_height`,
`ZeroFreeRegion.negLogDerivVerticalLogBound_of_affine_log_norm_add_three_bound_high_height`,
and
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_affine_log_norm_add_three_bound_high_height`
then package those full-height normalizers directly into the exact vertical
interfaces used by the 3-4-1 route.
The `..._on_verticalRegion` variants accept the same future estimates in the
complex-variable form `z ∈ verticalRegion 1 2 T0`, then specialize to the
coordinate points `sigma + i t`.
For estimates that already bound the signed real part, the direct constructors
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_affine_re_log_norm_add_three_bound_high_height`
and
`ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_affine_re_log_norm_add_three_bound_on_verticalRegion`
feed `Re(-zeta'/zeta)` into the same named interface without first strengthening
to a norm bound.
The named shifted-pair bridge
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_ReNegDerivDivVerticalLogBound`
then supplies both `sigma+it` and `sigma+2it` real-part inputs from that direct
real-part interface, including the `u = 2t` logarithmic height rescaling.
The signed coordinate variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
provide the same handoff in the `-logDeriv zeta` convention used by the
3-4-1 inequality, with hypotheses stated directly in real variables
`sigma`, `beta`, and `t`.
The single-constant variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
package the common Big-O shape where one constant controls both remaining
full-height signed estimates.
The complex-variable comparison
`ZeroFreeRegion.log_norm_add_three_le_two_log_abs_im` and the wrappers
`ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
state the same handoff directly for estimates in variables `s`, `rho`, and
`z`, which is the shape closest to future Borel/Jensen arguments.
The single-constant variants
`ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
package the common complex-variable Big-O shape where one constant controls
both remaining full-height estimates.
The affine variants
`ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
also allow additive constants in those full-height complex-variable estimates,
which is closer to the raw output of local growth lemmas.
The signed variants
`ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
provide the same full-height handoff in the `-logDeriv zeta` convention used
by the 3-4-1 inequality and the signed Borel wrappers.
The signed coordinate affine variants
`ZeroFreeRegion.classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_log_norm_add_three_bounds_high_height`
are the same additive-constant interface in variables `sigma`, `beta`, and
`t`.
The multiplicative signed variants
`ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
are the same signed full-height handoff for complex-variable estimates, with
additive constants set to zero.
The signed single-constant variants
`ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
and
`ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_log_norm_add_three_bound_high_height`
are the compact `-logDeriv zeta` convention handoff when one constant controls
both estimates.
For the separate vertical-strip part of this program,
`ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_vertical_log_bound`
now packages a single future ordinary estimate
`||logDeriv zeta(sigma+iu)|| <= B log |u|` into one shared existential
bound for both `sigma+it` and `sigma+2it`.  The signed-input companion
`ZeroFreeRegion.exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_neg_vertical_log_bound`
does the same when the future estimate is stated for `-logDeriv zeta`, using
only `||f|| = ||-f||`.  The companion theorem
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_vertical_norm_log_bound`
then converts the same input into the real-part quotient bounds used directly
by the 3-4-1 inequality, and
`ZeroFreeRegion.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_neg_vertical_norm_log_bound`
provides the same real-part handoff from signed `-logDeriv zeta` norm input.
These are proved bookkeeping bridges, not a proof of the zeta-specific
high-height estimate itself.
This is still conditional; it does not prove the quantitative zero-free region
until those two zeta-specific estimates are proved.
The next work starts from these meromorphic/nonvanishing/principal-part facts
and proves the vertical-height logarithmic-derivative estimates needed for the
quantitative strip.

### 2. Polynomial Growth for Zeta in Vertical Disks

Mathematical statement:
On fixed-radius disks or fixed-width strips near `Re(s) = 1`, `ζ(s)` has
polynomial growth in `|Im(s)|`.

Lean status:
The zeta-specific polynomial growth theorem is still missing.  The bookkeeping
handoff from such a theorem to the logarithmic scale used by Jensen and
Borel-Caratheodory is now proved:

```lean
ZeroFreeRegion.log_norm_bound_of_polynomial_growth
ZeroFreeRegion.log_norm_riemannZeta_le_affine_log_norm_add_three_of_polynomial_growth
ZeroFreeRegion.log_norm_riemannZeta_sigma_it_le_affine_log_norm_add_three_of_polynomial_growth
ZeroFreeRegion.log_norm_riemannZeta_sigma_it_le_affine_log_abs_add_three_of_polynomial_growth
ZeroFreeRegion.circleAverage_log_norm_riemannZeta_sigma_it_le_affine_log_abs_add_radius_three_of_polynomial_growth
ZeroFreeRegion.jensen_localDivisor_riemannZeta_sigma_it_le_affine_log_abs_add_radius_three_of_polynomial_growth
ZeroFreeRegion.jensen_localDivisor_riemannZeta_sigma_it_le_affine_log_abs_add_radius_three_of_polynomial_growth_of_pos_radius
ZeroFreeRegion.norm_deriv_riemannZeta_le_of_sphere_norm_bound_avoid_one
ZeroFreeRegion.norm_deriv_riemannZeta_le_of_sphere_norm_bound_dist_one
ZeroFreeRegion.norm_deriv_riemannZeta_sigma_it_le_of_sphere_norm_bound_height
ZeroFreeRegion.exists_re_im_logDeriv_vertical_log_bound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height
ZeroFreeRegion.logDerivVerticalLogBound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height
ZeroFreeRegion.reNegDerivDivVerticalLogBound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height
```

These results convert an input of the form
`||zeta z|| <= A * (||z|| + 3)^B` into
`log ||zeta z|| <= log A + B * log (||z|| + 3)`, and on
`1 <= sigma <= 2`, `|t| >= 5`, into
`log ||zeta (sigma + i t)|| <= log A + 2B * log (|t| + 3)`.
The circle-average theorem gives the matching Jensen-side input
`circleAverage(log ||zeta||) <= log A + 2B * log (|t| + |R| + 3)`
for circles that remain inside the same high strip.
The local-divisor theorem then rewrites that average through Jensen's formula,
so the divisor/trailing-coefficient expression is bounded by the same scale.
There is also a positive-radius form with `R` in place of `|R|`.
The three Cauchy derivative estimates then turn a boundary `||zeta||` bound on
a disk avoiding the pole into a center `||zeta'||` bound; they still need a
separate lower bound for `||zeta||` before they yield a `logDeriv zeta` bound.
The bounded-height version of that lower-bound input is now proved by
`exists_norm_riemannZeta_pos_lower_bound_on_compact_vertical_band` and its
coordinate `sigma+it` and shifted `sigma+2it` forms; the unbounded high-height
lower bound remains a zeta-specific analytic input.
The `..._of_high_height_pos_lower_bound` variants patch exactly such a future
high-height lower bound with the compact theorem, so downstream all-height
lower-bound obligations no longer need a separate bounded-height hypothesis.
The sphere/lower-bound handoff composes that Cauchy step with the existing
`zeta'`-plus-lower-bound bridge, so the primitive input can now be stated
directly as boundary control for `zeta` on fixed-radius circles plus a center
lower bound.
They do not prove the polynomial growth bound itself.

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
