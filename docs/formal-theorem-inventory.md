# Formal Theorem Inventory

This inventory separates proved Lean declarations from target statements.  It is
intended for reviewers and for future work planning.

It records internal proof status only.  It should not be read as a standalone
SOTA comparison or as a claim that this repository is the first PNT
formalization, a completed classical analytic PNT proof, or a proof of RH.
External academic value must be judged separately against Isabelle/HOL PNT,
HOL Light PNT, Lean `PrimeNumberTheoremAnd`, Mathlib zeta/L-function
infrastructure, and current Lean PNT repositories at submission time.

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
- `log_deriv_zeta_finset_series_identity`
  proves the finite-sum/Dirichlet-series exchange needed to expand arbitrary
  finite logarithmic-derivative detector combinations in the half-plane
  `sigma > 1`.
- `log_deriv_zeta_nonneg_finset_combination`
  proves a finite trigonometric-detector skeleton: after supplying the
  Dirichlet-series identity and pointwise nonnegativity of the detector
  polynomial, the finite logarithmic-derivative combination is nonnegative.
- `finset_weighted_nonneg_term_lower_bound`
  isolates one selected term from any nonnegative finite weighted sum, the
  algebraic step used to turn detector nonnegativity into a lower bound for a
  chosen logarithmic-derivative term.
- `log_deriv_zeta_term_lower_bound_of_finset_detector` and
  `log_deriv_zeta_bty_first_shift_lower_bound`
  apply that algebraic step to finite logarithmic-derivative detectors,
  including a concrete BTY degree-16 lower bound for the first shifted term.
- `log_deriv_zeta_nonneg_list_combination`
  is the list-indexed wrapper for the same detector skeleton.
- `log_deriv_zeta_nonneg_finset_combination_auto` and
  `log_deriv_zeta_nonneg_list_combination_auto`
  discharge the finite Dirichlet-series identity automatically from
  `log_deriv_zeta_finset_series_identity`, leaving only pointwise
  nonnegativity of the finite cosine polynomial as an input.
- `trigPolynomial_nonneg_of_sq_certificate` and
  `log_deriv_zeta_nonneg_finset_combination_auto_of_sq_certificate`
  turn a finite cosine-square certificate into pointwise detector
  nonnegativity and then into the automatic finite detector inequality.
- `ComplexExpAbsSqCertificate`,
  `trigPolynomial_nonneg_of_complex_exp_abs_sq_certificate`,
  `log_deriv_zeta_nonneg_finset_combination_auto_of_complex_exp_abs_sq_certificate`,
  and their predicate-based wrappers provide the corresponding
  complex-exponential absolute-square certificate interface.
- `ScaledComplexExpAbsSqCertificate`,
  `trigPolynomial_nonneg_of_scaled_complex_exp_abs_sq_certificate`, and
  `log_deriv_zeta_nonneg_finset_combination_auto_of_scaled_complex_exp_abs_sq_certificate`
  provide the scaled certificate shape
  `scale * P(theta) = ||sum c_k exp(i k theta)||^2`, avoiding square-root
  coefficients in finite detector tables.
- `log_deriv_zeta_finset_single_lower_bound_of_scaled_complex_exp_abs_sq_certificate`,
  `log_deriv_zeta_finset_single_lower_bound_of_shift_upper_bounds_of_scaled_complex_exp_abs_sq_certificate`,
  and
  `log_deriv_zeta_finset_single_lower_bound_of_uniform_shift_upper_bound_of_scaled_complex_exp_abs_sq_certificate`
  feed a scaled detector certificate directly into selected-term lower-bound
  extraction, optionally absorbing pointwise or uniform upper bounds for all
  remaining shifted terms.
- `btyRawCoeff`, `btyDetectorCoeff_zero`, `btyDetectorCoeff_one`,
  `btyDetectorCoeff_sum_one_to_K`, `btyDetectorCoeff_sum_support_erase_one`,
  and `btyDetectorCoeff_eq_zero_of_seventeen_le` encode the
  Bellotti-Trudgian-Yang degree-16 detector coefficients, verify the quoted
  values `a_0 = 1`, `a_1 = 865534 / 497079`, and
  `sum_{1 <= k <= 16} a_k = 2919857 / 828465`, compute the coefficient sum
  away from `k = 1` as `6917296 / 2485395`, and prove support truncation beyond
  degree `16`.
- `finite_weighted_sum_single_lower_bound`,
  `finite_weighted_sum_single_lower_bound_of_upper_bounds`,
  `finite_weighted_sum_single_lower_bound_of_uniform_upper_bound`,
  `log_deriv_zeta_finset_single_lower_bound_of_nonneg`,
  `log_deriv_zeta_finset_single_lower_bound_auto`,
  `log_deriv_zeta_finset_single_lower_bound_of_shift_upper_bounds`, and
  `log_deriv_zeta_finset_single_lower_bound_auto_of_shift_upper_bounds`,
  `log_deriv_zeta_finset_single_lower_bound_of_uniform_shift_upper_bound`, and
  `log_deriv_zeta_finset_single_lower_bound_auto_of_uniform_shift_upper_bound`
  isolate one positive-coefficient term from a nonnegative finite detector sum,
  with variants that absorb supplied upper bounds for the remaining shifted
  terms, including one common upper bound for all remaining shifts.
- `norm_sq_sum_real_coeff_complex_exp_eq_double_sum`,
  `bty_scaled_detector_sum_eq_double_sum`,
  `btyScaledComplexExpAbsSqCertificate`, and
  `log_deriv_zeta_nonneg_bty_detector_from_scaled_certificate` expand finite
  real-coefficient exponential-square norms as double Fourier cosine sums,
  prove the full scaled BTY detector certificate, and derive the corresponding
  automatic logarithmic-derivative detector inequality.
- `btyDetectorCoeff_nonneg_of_mem_support`,
  `btyDetectorCoeff_pos_of_mem_support`,
  `btyDetectorCoeff_one_pos`,
  `log_deriv_zeta_bty_detector_one_lower_bound`,
  `log_deriv_zeta_bty_detector_one_lower_bound_of_shift_upper_bounds`,
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound`,
  and
  `log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_shift_upper_bound_simplified`
  specialize the detector lower-bound extraction to the BTY `k = 1` term and
  package the exact interface needed by future shifted log-derivative upper
  bounds, including the simplified rational coefficient penalty
  `3458648 / 2163835`.
- `btyDetectorCoeff_sum_support_erase_one_erase_zero` and
  `btyDetectorCoeff_mixed_center_sum`
  compute the remaining noncentral BTY coefficient sum
  `4431901 / 2485395` and rewrite the mixed center/nonzero expression as
  `B0 + (4431901 / 2485395) * L`.
- `log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound`
  applies the named high-height vertical logarithmic-derivative bound to all
  nonzero BTY frequencies while taking the `k = 0` real-axis term as a separate
  upper-bound input.  This closes the finite-frequency bookkeeping for the BTY
  handoff without asserting the zeta-specific vertical estimate itself.
- `log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound_simplified`
  rewrites the same mixed handoff using the evaluated noncentral coefficient
  sum `4431901 / 2485395`.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound`
  discharges that central `k = 0` input from the already proved fixed-margin
  `Re(s) >= 1 + epsilon` quotient estimate.  It is intentionally still a
  fixed-margin bridge, not the boundary estimate needed for the classical
  zero-free region.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound_simplified`
  is the fixed-margin version with the same coefficient-sum simplification.
- `log_deriv_zeta_nonneg_three_four_one_from_finset`
  re-exposes the verified 3-4-1 theorem as the base detector instance.
- `classical_zero_free_region_compact`
  proves a nonconstructive positive-width zero-free strip for each bounded
  height.
- `classical_zero_free_region_high_height_re_im` and
  `classical_zero_free_region_high_height_re_im_at_three`
  project the classical zero-free-region target into coordinate high-height
  form, including the standard height-`3` cutoff.
- `classical_zero_free_region_high_height_mono_cutoff`,
  `classical_zero_free_region_high_height_mono_cutoff_re_im`, and the two
  existential variants restrict a high-height classical-width estimate from
  cutoff `T0` to any larger cutoff `T1`.
- `vinogradov_korobov_zero_free_region_high_height_mono_cutoff`,
  `vinogradov_korobov_zero_free_region_high_height_mono_cutoff_re_im`, and
  the two existential variants provide the same cutoff restriction for the
  Vinogradov-Korobov width.
- `residue_bounds`
  proves `1 < (sigma - 1) * Re(zeta(sigma)) <= sigma` for `sigma > 1`.
- `log_deriv_zeta_pos_real`
  proves positivity of the real-axis logarithmic derivative expression.
- `log_deriv_zeta_antitone`
  proves the real-axis antitone property of the logarithmic derivative series.
- `exists_norm_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re`
  proves that for every fixed `epsilon > 0`, `logDeriv zeta` has a
  `C * log (|Im z| + 3)` norm bound throughout the half-plane
  `1 + epsilon <= Re z`.
- `exists_norm_neg_logDeriv_riemannZeta_le_log_abs_im_add_three_of_one_add_le_re`
  is the signed version of the same fixed-margin half-plane bound.
- `exists_norm_riemannZeta_pos_lower_bound_on_compact_vertical_band`
  proves that `zeta` has a positive norm lower bound on every compact
  positive-height band `1 <= Re z <= 2`, `H <= |Im z| <= T`.
- `exists_norm_riemannZeta_sigma_it_pos_lower_bound_on_compact_vertical_band`
  is the coordinate form of the same compact lower bound on points
  `sigma + it`.
- `exists_norm_riemannZeta_sigma_two_it_pos_lower_bound_on_compact_vertical_band`
  is the shifted coordinate form at the 3-4-1 point `sigma + 2it`.
- `exists_norm_riemannZeta_sigma_it_pos_lower_bound_of_high_height_pos_lower_bound`
  patches a future high-height lower bound for `zeta(sigma+it)` with the
  compact bounded-height lower bound, yielding an all-height positive lower
  bound above any fixed `H > 0`.
- `exists_norm_riemannZeta_sigma_two_it_pos_lower_bound_of_high_height_pos_lower_bound`
  is the same compact patch for the shifted 3-4-1 point `sigma + 2it`.
- `exists_norm_riemannZeta_pos_lower_bound_on_verticalRegion_of_compact_band_and_high_height`
  patches that proved compact-band lower bound with a future high-height
  lower bound `T <= |Im z|` to supply one positive lower bound on
  `verticalRegion 1 2 H`.
- `exists_norm_deriv_riemannZeta_bound_on_compact_vertical_band`
  proves that `zeta'` has a finite norm bound on every compact positive-height
  band `1 <= Re z <= 2`, `H <= |Im z| <= T`.
- `exists_deriv_riemannZeta_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
  patches that compact `zeta'` bound with a future high-height affine
  logarithmic derivative-growth estimate to cover `verticalRegion 1 2 H`.
- `logDerivVerticalLogBound_of_compact_band_and_high_height_deriv_bound_zeta_lower_bound`
  combines the compact-patched `zeta'` growth estimate and compact-patched
  positive `zeta` lower bound into the named `LogDerivVerticalLogBound`
  interface.  The high-height derivative growth and zeta lower bound remain
  the genuine analytic inputs.
- `exists_norm_logDeriv_riemannZeta_bound_on_compact_vertical_band`
  proves that `logDeriv zeta` has a finite norm bound on every compact
  positive-height band `1 <= Re z <= 2`, `H <= |Im z| <= T`.
- `exists_logDeriv_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
  patches that compact bounded-height `logDeriv zeta` norm bound with a future
  high-height affine logarithmic bound, yielding an affine bound on the full
  vertical region.
- `logDerivVerticalLogBound_of_compact_band_and_high_height_affine_log_norm_add_three_bound`
  feeds the compact-plus-high-height affine bound directly into the named
  `LogDerivVerticalLogBound` interface.
- `exists_negLogDeriv_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
  is the signed `-logDeriv zeta` version of the same compact-plus-high-height
  affine patch.
- `negLogDerivVerticalLogBound_of_compact_band_and_high_height_affine_log_norm_add_three_bound`
  feeds that signed affine patch into the named
  `NegLogDerivVerticalLogBound` interface.
- `exists_reNegDerivDiv_affine_log_norm_add_three_bound_on_verticalRegion_of_compact_band_and_high_height`
  is the direct real-part quotient `Re(-zeta'/zeta)` version of the same
  compact-plus-high-height affine patch.
- `reNegDerivDivVerticalLogBound_of_compact_band_and_high_height_affine_log_norm_add_three_bound`
  feeds that direct real-part affine patch into the named
  `ReNegDerivDivVerticalLogBound` interface.
- `exists_norm_neg_logDeriv_riemannZeta_bound_on_compact_vertical_band`
  is the signed `-logDeriv zeta` version of the same compact bounded-height
  estimate.
- `exists_norm_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band`
  is the coordinate form on points `sigma + it`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_it_bound_on_compact_vertical_band`
  is the signed coordinate form on points `sigma + it`.
- `exists_norm_logDeriv_riemannZeta_sigma_two_it_bound_on_compact_vertical_band`
  is the compact bounded-height norm bound at the shifted 3-4-1 point
  `sigma + 2it`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_bound_on_compact_vertical_band`
  is the signed `-logDeriv zeta` compact bound at `sigma + 2it`.
- `exists_re_neg_deriv_div_riemannZeta_sigma_it_bound_on_compact_vertical_band`
  turns the signed compact norm bound into the real-part quotient convention
  `Re(-zeta'/zeta)` at `sigma + it`.
- `exists_re_neg_deriv_div_riemannZeta_sigma_two_it_bound_on_compact_vertical_band`
  is the same real-part compact bound for the shifted point `sigma + 2it`.
- `exists_re_neg_deriv_div_riemannZeta_sigma_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound`
  patches a future high-height real-part quotient estimate into an all-height
  affine logarithmic bound at `sigma + it`.
- `exists_re_neg_deriv_div_riemannZeta_sigma_two_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound`
  is the same real-part compact-patching bridge at `sigma + 2it`.
- `exists_re_neg_deriv_div_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound`
  patches a high-height real-part quotient estimate while preserving the exact
  `C * log |t|` scale on any range starting at height at least `3`.
- `exists_re_neg_deriv_div_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound`
  repackages that exact-log real-part quotient patch in the standard
  `1 <= sigma -> sigma <= 2 -> T0 <= |t|` vertical-bound form used by the
  quantitative zero-free-region chain.
- `exists_re_neg_deriv_div_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound`
  is the exact-log compact-patching bridge for the shifted point
  `sigma + 2it`.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_high_height_log_abs_bound`
  is the same objective-shaped real-part quotient patch for the shifted
  3-4-1 point `sigma + 2it`.
- `exists_re_neg_deriv_div_riemannZeta_vertical_log_bound_of_norm_high_height_log_abs_bound`
  converts a future high-height norm estimate for `logDeriv zeta` at
  `sigma + it` into the real-part quotient vertical-bound form by
  `Re z <= ||z||`.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_norm_high_height_log_abs_bound`
  is the shifted `sigma + 2it` norm-to-real-part bridge used by the 3-4-1
  route.
- `exists_norm_logDeriv_riemannZeta_sigma_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound`
  patches a future high-height `B * log |t|` estimate with the compact band
  bound, producing an all-height affine `A + B' * log(|t| + 3)` estimate.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound`
  is the signed `-logDeriv zeta` version of the same compact-patching bridge.
- `exists_norm_logDeriv_riemannZeta_sigma_two_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound`
  is the corresponding compact-patching bridge for the shifted 3-4-1 point
  `sigma + 2it`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_affine_log_abs_add_three_bound_of_high_height_log_abs_bound`
  is the signed `-logDeriv zeta` version at `sigma + 2it`.
- `exists_norm_logDeriv_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound`
  patches a high-height norm estimate while preserving the exact
  `C * log |t|` scale at `sigma + it` for height ranges starting at `3`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_it_log_abs_bound_of_high_height_log_abs_bound`
  is the signed `-logDeriv zeta` exact-log norm patch at `sigma + it`.
- `exists_norm_logDeriv_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound`
  packages the same exact-log compact patch in the standard vertical-bound
  shape `1 <= sigma -> sigma <= 2 -> T0 <= |t|`, exposing the exact theorem
  form needed by the quantitative zero-free-region chain.
- `exists_norm_neg_logDeriv_riemannZeta_vertical_log_bound_of_high_height_log_abs_bound`
  is the signed `-logDeriv zeta` version of that objective-shaped vertical
  logarithmic bound wrapper.
- `exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_vertical_log_bound`
  derives the shifted `sigma + 2it` norm estimate from the ordinary vertical
  estimate at `sigma + iu`, absorbing the comparison `log |2t| <= 2 log |t|`.
- `exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_vertical_log_bound`
  packages that same future ordinary vertical estimate into one shared
  existential `C * log |t|` bound for both `sigma + it` and `sigma + 2it`,
  matching the two norm inputs needed by the 3-4-1 route.
- `exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_LogDerivVerticalLogBound`
  is the named-interface version of the same shifted norm-pair handoff.
- `exists_norm_logDeriv_riemannZeta_shift_pair_vertical_log_bound_of_neg_vertical_log_bound`
  is the signed-input version: a future ordinary vertical estimate for
  `-logDeriv zeta` gives the same shared pair bound by norm invariance under
  negation.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_vertical_norm_log_bound`
  converts the shared norm package into one shared real-part quotient package
  for `Re(-zeta'/zeta)(sigma+it)` and `Re(-zeta'/zeta)(sigma+2it)`, the direct
  sign convention of the 3-4-1 inequality.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_LogDerivVerticalLogBound`
  is the named-interface version of that real-part shifted-pair handoff.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_neg_vertical_norm_log_bound`
  is the corresponding signed-input real-part package, letting future
  `-logDeriv zeta` norm estimates enter the 3-4-1 quotient handoff without an
  extra caller-side conversion.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_NegLogDerivVerticalLogBound`
  is the named-interface version of the signed real-part shifted-pair handoff.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_high_height_log_abs_bounds`
  combines separate future high-height real-part estimates at `sigma + it` and
  `sigma + 2it` into one shared `C * log |t|` pair package, matching routes
  that produce the two 3-4-1 inputs separately.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_deriv_bound_and_zeta_lower_bound_high_height`
  and
  `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height`
  compose primitive `zeta'`/`zeta` lower-bound inputs, or Cauchy-style sphere
  zeta-growth inputs, directly into the same ordinary/shifted real-part pair
  consumed by the 3-4-1 route.
- `log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound`
  is the named-interface BTY handoff: it uses `LogDerivVerticalLogBound` for
  every nonzero detector frequency and keeps the central `k = 0` term as a
  separate real-axis quotient bound.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound`
  supplies that real-axis quotient bound from the fixed-margin API when
  `1 + epsilon <= sigma`, leaving only the named vertical estimate for nonzero
  detector frequencies.
- `log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_ReNegDerivDivVerticalLogBound`
  is the direct real-part version of the named BTY handoff, so the future
  nonzero-frequency input can be `Re(-zeta'/zeta)` itself rather than a norm
  estimate.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_ReNegDerivDivVerticalLogBound`
  combines that direct real-part handoff with the same fixed-margin center
  discharge.
- The corresponding `_simplified` BTY handoff lemmas expose the same facts
  after evaluating the noncentral coefficient sum.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_vertical_norm_log_bound`
  converts that shifted norm estimate into the real-part quotient convention
  needed by the 3-4-1 inequality.
- `exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`
  composes the affine `log(||sigma+iu||+3)` normalizer with the shifted bridge,
  producing the `sigma + 2it` norm input from a future ordinary vertical growth
  estimate.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`
  is the corresponding shifted real-part quotient output.
- `exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  composes the affine `log(|u|+3)` ordinary vertical normalizer with the
  shifted bridge, producing the `sigma + 2it` norm input from the common
  safe-height estimate shape.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  is the corresponding shifted real-part quotient output for `log(|u|+3)`.
- `exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_log_abs_add_three_bound_high_height`
  is the multiplicative `B * log(|u|+3)` specialization of the shifted norm
  bridge, avoiding a dummy affine constant at call sites.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_log_abs_add_three_bound_high_height`
  is the corresponding multiplicative shifted real-part quotient bridge.
- `exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_neg_affine_log_abs_add_three_bound_high_height`
  is the signed-input shifted norm bridge for future estimates on
  `||-logDeriv zeta||`.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_neg_affine_log_abs_add_three_bound_high_height`
  is the signed-input shifted real-part quotient bridge.
- `exists_norm_logDeriv_riemannZeta_shifted_vertical_log_bound_of_neg_log_abs_add_three_bound_high_height`
  is the signed multiplicative `B * log(|u|+3)` specialization of the shifted
  norm bridge.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_neg_log_abs_add_three_bound_high_height`
  is the signed multiplicative shifted real-part quotient bridge.
- `exists_norm_logDeriv_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound`
  is the exact-log norm patch at the shifted point `sigma + 2it`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_log_abs_bound_of_high_height_log_abs_bound`
  is the signed exact-log norm patch at `sigma + 2it`.
- `exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le`
  is the coordinate form of the same fixed-margin logarithmic bound on
  vertical lines `sigma + it`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le`
  is the signed coordinate form on vertical lines `sigma + it`.
- `exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin`
  converts that fixed-margin coordinate bound to the exact high-height scale
  `C * log |t|`, still under the hypothesis `1 + epsilon <= sigma`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_it_le_log_abs_of_fixed_margin`
  is the signed fixed-margin version in the same exact high-height scale.
- `log_abs_two_mul_add_three_le_two_log_abs_add_three`
  proves the elementary comparison
  `log (|2*t| + 3) <= 2 * log (|t| + 3)`.
- `exists_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_add_three_of_one_add_le`
  converts the fixed-margin `sigma + I*t` norm estimate into the real-part
  quotient convention used in the 3-4-1 inequality.
- `exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le`
  specializes fixed-margin logarithmic control to the shifted point
  `sigma + 2*I*t`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le`
  is the signed shifted fixed-margin bound in the same `log(|t|+3)` scale.
- `exists_norm_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin`
  converts that shifted fixed-margin bound to the exact high-height scale
  `C * log |t|`.
- `exists_norm_neg_logDeriv_riemannZeta_sigma_two_it_le_log_abs_of_fixed_margin`
  is the signed shifted fixed-margin version in the same exact high-height
  scale.
- `exists_re_neg_deriv_div_riemannZeta_sigma_two_it_le_log_abs_add_three_of_one_add_le`
  converts that shifted norm bound into the real-part form used by the third
  term of the 3-4-1 inequality.
- `exists_re_neg_deriv_div_riemannZeta_fixed_margin_three_four_one_bounds`
  packages the real-axis, `sigma + I*t`, and `sigma + 2*I*t` real-part terms
  under one fixed-margin `C * log (|t| + 3)` bound.
- `exists_three_four_one_combination_le_log_abs_add_three_of_one_add_le`
  combines the 3-4-1 nonnegativity theorem with the fixed-margin term bounds,
  giving a nonnegative `O(log (|t|+3))` bound for the whole combination.

Supporting declarations include:

- `zeta_no_zeros_on_line_one`
- `riemannZeta_pos_of_real_gt_one`
- `log_riemannZeta_dirichlet_series`
- `riemannZeta_re_eq_tsum_real`
- `summable_one_div_rpow`
- `norm_riemannZeta_le_re_zeta_two_of_two_le_re`
  proves the right-boundary estimate `||zeta(s)|| <= Re(zeta(2))` on
  `2 <= Re(s)` from the absolutely convergent Dirichlet series.
- `norm_riemannZeta_le_const_polynomial_on_two_le_re`
  packages that right-boundary estimate as constant-order polynomial growth,
  giving the polynomial-growth chain a proved right-edge input.
- `riemannZeta_re_gt_one`
- `riemannZeta_gt_one_div_sub`
- `riemannZeta_re_le_sigma_div_sub`
- `log_deriv_zeta_real_eq_series`
- `sigmaOf_log_gt_one`
  proves the standard high-height choice `1 + a / log |t|` is greater than
  `1` when `a > 0`.
- `riemannZeta_sigmaOf_log_ne_zero`
  proves `ζ(1 + a / log |t|) != 0` above height `2` when `a > 0`.
- `riemannZeta_sigmaOf_log_add_I_mul_ne_zero`
  proves `ζ(1 + a / log |t| + it) != 0` on the same moving high-height line.
- `riemannZeta_sigmaOf_log_add_two_I_mul_ne_zero`
  proves `ζ(1 + a / log |t| + 2it) != 0` on the shifted line used by
  the 3-4-1 inequality.
- `analyticAt_logDeriv_riemannZeta_sigmaOf_log`
  proves `logDeriv ζ` is analytic at `1 + a / log |t|`.
- `analyticAt_logDeriv_riemannZeta_sigmaOf_log_add_I_mul`
  proves `logDeriv ζ` is analytic at `1 + a / log |t| + it`.
- `analyticAt_logDeriv_riemannZeta_sigmaOf_log_add_two_I_mul`
  proves `logDeriv ζ` is analytic at `1 + a / log |t| + 2it`.
- `analyticAt_logDeriv_riemannZeta_closedBall_sigmaOf_log_add_I_mul_height_of_radius_le_width_of_height_add_le`
  proves `logDeriv ζ` is analytic at every point of a closed ball centered at
  `1 + a / log |t| + iu`, provided the radius fits inside the width to
  `Re(s) = 1` and the independent height `u` keeps the ball away from the
  pole.
- `analyticAt_logDeriv_riemannZeta_closedBall_sigmaOf_log_add_I_mul_of_radius_le_width_of_height_add_le`
  specializes the independent-height closed-ball analyticity theorem to the
  center `1 + a / log |t| + it`.
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
- `analyticAt_logDeriv_riemannZetaPoleUnitAtOne`
  proves the logarithmic derivative of the analytic pole unit is analytic at
  `1`.
- `eventually_norm_logDeriv_riemannZetaPoleUnitAtOne_le_const`
  proves that `norm (logDeriv riemannZetaPoleUnitAtOne s)` is locally bounded
  near `1`.
- `eventuallyEq_logDeriv_riemannZeta_simplePoleAtOne`
  proves the additive simple-pole logarithmic-derivative decomposition
  `logDeriv zeta s = -(s - 1)^-1 + logDeriv unit s` in the punctured
  neighborhood of `1`.
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
- `divisor_neg_of_meromorphicOn`
  proves that multiplying a meromorphic complex-valued function by `-1` does
  not change its divisor.
- `divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_closedBall` and
  `divisor_neg_logDeriv_riemannZeta_eq_divisor_logDeriv_verticalRegion`
  specialize this divisor invariance to the signed/unsigned logarithmic
  derivatives of ζ on closed balls and project vertical regions.
- `meromorphicTrailingCoeffAt_neg_of_meromorphicAt` and
  `norm_meromorphicTrailingCoeffAt_neg_of_meromorphicAt`
  prove the trailing-coefficient sign conversion and norm invariance for
  meromorphic complex-valued functions.
- `log_norm_meromorphicTrailingCoeffAt_neg_logDeriv_riemannZeta_eq`
  specializes the trailing-coefficient logarithmic norm equality to the
  signed/unsigned logarithmic derivatives of ζ.
- `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_closedBall_unsigned_terms`
  and
  `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_verticalRegion_unsigned_terms`
  combine the signed Jensen left side with unsigned `logDeriv ζ` divisor and
  trailing-coefficient terms.
- `meromorphic_riemannZeta`, `meromorphic_logDeriv_riemannZeta`, and
  `meromorphic_neg_logDeriv_riemannZeta` package ζ, `logDeriv ζ`, and
  `-logDeriv ζ` as global meromorphic functions, not just functions
  meromorphic on chosen closed balls.
- `meromorphic_comp_add_const` proves that translating the input of a global
  meromorphic function preserves global meromorphicity, the exact regularity
  input needed for zero-centered value-distribution log-counting.
- `valueDistribution_logCounting_translate_eq_circleAverage_sub_const`
  translates Mathlib's zero-centered value-distribution Jensen formula to a
  disk centered at an arbitrary complex point `c`.
- `valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const`
  specializes that bridge to `logDeriv ζ`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_eq_circleAverage_sub_const`
  specializes it to the signed logarithmic derivative `-logDeriv ζ`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_circleAverage`
  rewrites the signed bridge's circle-average and trailing-coefficient terms
  into the unsigned `logDeriv ζ` convention.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_circleAverage_sub_const`
  specializes the translated log-counting Jensen bridge to disks centered at
  `σ + I*t`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_circleAverage`
  provides the matching signed `-logDeriv ζ` wrapper at `σ + I*t`, with
  unsigned `logDeriv ζ` circle-average and trailing-coefficient terms.
- `valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor`
  rewrites the translated log-counting difference directly to the closed-ball
  local-divisor side for `logDeriv ζ`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor`
  gives the matching signed `-logDeriv ζ` bridge while keeping the right-hand
  side in unsigned `logDeriv ζ` divisor/trailing-coefficient notation.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor`
  specializes the local-divisor log-counting bridge to `σ + I*t` disks.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor`
  provides the signed `σ + I*t` local-divisor version in the same unsigned
  bookkeeping convention.
- `meromorphicTrailingCoeffAt_comp_add_const_zero`,
  `norm_meromorphicTrailingCoeffAt_comp_add_const_zero`, and
  `log_norm_meromorphicTrailingCoeffAt_comp_add_const_zero` prove that
  translating a meromorphic function's input by `c` preserves the trailing
  coefficient at the translated center `0`, including norm and log-norm forms.
- `valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_localDivisor_pure`
  cancels the translated trailing-coefficient terms in the `logDeriv ζ`
  local-divisor bridge.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_localDivisor_pure`
  gives the signed `-logDeriv ζ` version with the same unsigned local-divisor
  right-hand side.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_localDivisor_pure`
  specializes the pure local-divisor bridge to `σ + I*t` disks.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_localDivisor_pure`
  provides the signed pure `σ + I*t` version in unsigned bookkeeping.
- `valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_divisor_eq_zero`
  turns a zero-divisor hypothesis on the closed ball into vanishing of the
  translated log-counting difference for `logDeriv ζ`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_divisor_eq_zero`
  gives the signed `-logDeriv ζ` version with the same unsigned divisor
  hypothesis.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_divisor_eq_zero`
  specializes the zero-divisor log-counting vanishing bridge to `σ + I*t`
  disks.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_divisor_eq_zero`
  provides the signed `σ + I*t` version in unsigned bookkeeping.
- `divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_order_eq_zero`
  converts pointwise order zero of `logDeriv ζ` on a closed ball into
  pointwise vanishing of its local divisor.
- `divisor_logDeriv_riemannZeta_closedBall_eq_zero_of_analyticAt_ne_zero`
  gives the analytic-and-nonzero version of the same divisor-vanishing bridge.
- `valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_order_eq_zero`
  turns an order-zero hypothesis on the local closed ball directly into
  vanishing of the translated log-counting difference for `logDeriv ζ`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_order_eq_zero`
  gives the signed `-logDeriv ζ` version with the same unsigned order
  hypothesis.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_order_eq_zero`
  specializes the order-zero log-counting bridge to `σ + I*t` disks.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_order_eq_zero`
  provides the signed `σ + I*t` version in unsigned order bookkeeping.
- `exists_eventuallyEq_sub_mul_unit_of_analyticAt_zero_deriv_ne_zero`
  factors a simple analytic zero as `(z - x) * g z` with analytic unit `g` on
  a punctured neighborhood, giving the local algebra input for later
  principal-part separation of `logDeriv`.
- `exists_eventuallyEq_logDeriv_sub_inv_of_analyticAt_zero_deriv_ne_zero`
  upgrades that factorization to
  `logDeriv f z - (z - x)⁻¹ = logDeriv g z` on the punctured neighborhood,
  isolating the simple-zero principal logarithmic pole from the regular part.
- `exists_eventuallyEq_neg_logDeriv_add_inv_of_analyticAt_zero_deriv_ne_zero`
  gives the signed `-logDeriv f z + (z - x)⁻¹ = -logDeriv g z` version used
  by de la Vallée Poussin estimates.
- `exists_eventuallyEq_logDeriv_riemannZeta_sub_inv_of_simple_zero`
  specializes the principal-part separation to a simple zero of `riemannZeta`
  away from the pole `1`.
- `exists_eventuallyEq_neg_logDeriv_riemannZeta_add_inv_of_simple_zero`
  packages the signed zeta-specific form matching the regular-part norm
  hypotheses used by the conditional zero-free-region bridge.
- `exists_eventuallyEq_logDeriv_sub_order_mul_inv_of_analyticAt_order_eq_nat`
  proves the multiplicity-weighted local decomposition
  `logDeriv f z - n/(z-x) = logDeriv g z` from
  `analyticOrderAt f x = n`.
- `exists_eventuallyEq_neg_logDeriv_add_order_mul_inv_of_analyticAt_order_eq_nat`
  gives the corresponding signed multiplicity-weighted form.
- `exists_eventuallyEq_logDeriv_riemannZeta_sub_order_mul_inv_of_order_eq_nat`
  specializes the multiplicity-weighted decomposition to `riemannZeta` away
  from its pole.
- `exists_eventuallyEq_neg_logDeriv_riemannZeta_add_order_mul_inv_of_order_eq_nat`
  gives the signed zeta-specific multiplicity-weighted form
  `-logDeriv ζ + n/(z-ρ)`, avoiding a simple-zero assumption in the local
  algebra layer.
- `exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq`
  and `exists_punctured_closedBall_norm_logDeriv_sub_order_mul_inv_le_of_eventuallyEq`
  convert an eventually-equal multiplicity regular part and an eventual norm
  bound into explicit punctured open/closed ball estimates.
- `exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq`
  and `exists_punctured_closedBall_norm_neg_logDeriv_add_order_mul_inv_le_of_eventuallyEq`
  provide the signed `-logDeriv` version used by the de la Vallée Poussin
  zero-free chain.
- `exists_punctured_ball_norm_logDeriv_sub_order_mul_inv_le_of_analyticAt_order_eq_nat`
  and its closed-ball form combine the multiplicity factorization itself with
  an eventual bound on the local analytic unit.
- `exists_punctured_ball_norm_neg_logDeriv_add_order_mul_inv_le_of_analyticAt_order_eq_nat`
  and its closed-ball form give the signed version of the same bridge.
- `exists_punctured_ball_norm_logDeriv_riemannZeta_sub_order_mul_inv_le_of_order_eq_nat`
  and its signed/closed variants specialize these bridges to zeta zeros away
  from the pole.
- `analyticAt_logDeriv_of_analyticAt_ne_zero`
  proves the generic local fact that an analytic nonzero function has analytic
  logarithmic derivative.
- `analyticAt_logDeriv_riemannZeta_of_analyticAt_ne_zero`
  specializes the generic bridge to ζ.
- `analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero`
  derives analyticity of `logDeriv ζ` away from the pole when ζ is nonzero.
- `analyticAt_logDeriv_riemannZeta_of_one_le_re_of_ne_one`
  uses Mathlib zeta nonvanishing on `Re(s) >= 1` to discharge the nonzero
  hypothesis away from the pole.
- `analyticAt_logDeriv_riemannZeta_closedBall_of_ne_one_of_ne_zero`
  packages the same pointwise analytic bridge for closed balls.
- `analyticAt_logDeriv_riemannZeta_closedBall_of_one_le_re_of_ne_one`
  uses right-half-plane zeta nonvanishing to prove pointwise analyticity of
  `logDeriv ζ` on closed balls that avoid the pole.
- `valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_analyticAt_ne_zero`
  turns analytic-and-nonzero local hypotheses on `logDeriv ζ` directly into
  vanishing of the translated log-counting difference.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_analyticAt_ne_zero`
  gives the signed `-logDeriv ζ` version with the same unsigned local
  hypotheses.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_analyticAt_ne_zero`
  specializes the analytic-and-nonzero bridge to `σ + I*t` disks.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_analyticAt_ne_zero`
  provides the signed `σ + I*t` version in unsigned analytic/nonzero
  bookkeeping.
- `valueDistribution_logCounting_logDeriv_riemannZeta_translate_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
  packages right-half-plane zeta nonvanishing, pole exclusion, and local
  nonvanishing of `logDeriv ζ` into translated log-counting vanishing.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_translate_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
  gives the signed version with the same unsigned hypotheses.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
  specializes the right-half-plane bridge to `σ + I*t` disks.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_one_le_re_of_ne_one_of_logDeriv_ne_zero`
  provides the signed `σ + I*t` version in unsigned bookkeeping.
- `closedBall_sigma_it_one_le_re_of_add_le`
  converts the numeric disk condition `1 + R <= sigma` into the pointwise
  right-half-plane hypothesis `1 <= z.re` on disks centered at `sigma + I*t`.
- `closedBall_sigma_it_ne_one_of_height_add_le`
  converts positive-height disk data `0 < H` and `H + R <= |t|` into
  pointwise exclusion of the pole `1`.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero`
  packages the two disk-geometric hypotheses together with local
  nonvanishing of `logDeriv zeta` into log-counting vanishing for
  `logDeriv zeta`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero`
  gives the signed `-logDeriv zeta` version while keeping the nonvanishing
  hypothesis on the unsigned logarithmic derivative.
- `analyticAt_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half`
  packages the same disk geometry as pointwise analyticity of `logDeriv zeta`
  on the whole `sigma + I*t` disk.
- `logDeriv_riemannZeta_ne_zero_of_neg_logDeriv_ne_zero`
  converts local nonvanishing of `-logDeriv zeta` to local nonvanishing of
  `logDeriv zeta`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero`
  gives the signed disk log-counting vanishing wrapper with the nonvanishing
  hypothesis stated directly for `-logDeriv zeta`.
- `valueDistribution_logCounting_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_logDeriv_ne_zero_pos_radius`
  is the positive-radius version of the direct `sigma + I*t` log-counting
  bridge, replacing the old `|R|` disk radius with `R` under `0 < R`.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_unsigned_eq_zero_of_disk_right_half_of_logDeriv_ne_zero_pos_radius`
  gives the same positive-radius normalization for the signed left side with
  unsigned `logDeriv zeta` nonvanishing.
- `valueDistribution_logCounting_neg_logDeriv_riemannZeta_sigma_it_eq_zero_of_disk_right_half_of_neg_logDeriv_ne_zero_pos_radius`
  gives the positive-radius normalization with the local nonvanishing
  hypothesis stated directly for `-logDeriv zeta`.
- `differentiableOn_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half`
  turns the disk-geometric analyticity wrapper into `DifferentiableOn` on the
  closed `sigma + I*t` disk.
- `differentiableOn_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half`
  gives the centered-open-disk regularity input for
  `z ↦ logDeriv zeta (z + (sigma + I*t))`.
- `differentiableOn_neg_logDeriv_riemannZeta_comp_add_sigma_it_ball_of_disk_right_half`
  provides the same centered-open-disk regularity in the signed
  `-logDeriv zeta` convention.
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
- `exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_inv_sub_one_add_const`
  gives the additive real-axis principal-part bound
  `Re(-zeta'/zeta)(sigma) <= 1 / (sigma - 1) + M` for real `sigma > 1`
  sufficiently close to `1`.
- `exists_rightNeighborhood_hreal_two_div_sub_one`
  packages the concrete real-axis bound in the exact `hreal` shape used by
  the 3-4-1 high-height assembly.
- `exists_sigmaOf_log_hreal_two_div_sub_one`
  specializes the concrete `hreal` package to the standard high-height choice
  `sigmaOf t = 1 + a / log |t|`.
- `exists_sigmaOf_log_hreal_two_mul_log_div`
  normalizes that concrete specialization into the vertical-height estimate
  `Re(-zeta'/zeta)(1 + a / log |t|) <= 2 * log |t| / a`.
- `exists_sigmaOf_log_hreal_inv_sub_one_add_const_log_bound`
  specializes the additive pole-side estimate to the standard high-height
  choice `1 + a / log |t|`, giving the separated coefficient
  `(1 / a + M / log 2) * log |t|`.
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
- `exists_sigma_ge_sigmaOf_log_norm_bound_const_mul_log_div`
  extends the same weak absolute-convergence norm bound from the standard
  point `sigma = 1 + a / log |t|` to the moving half-strip
  `1 + a / log |t| <= sigma <= 2`.
- `exists_sigma_ge_sigmaOf_log_re_neg_deriv_div_bound_const_mul_log_div`
  converts that moving-half-strip norm estimate into the one-sided real-part
  shape used by the 3-4-1 inequality.
- `exists_sigma_ge_sigmaOf_log_any_im_norm_bound_const_mul_log_div`
  generalizes the moving-half-strip norm estimate so the estimated point has
  arbitrary imaginary part `u`, while `t` still controls the scale
  `log |t|`.
- `exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_const_mul_log_div`
  gives the corresponding arbitrary-imaginary-coordinate real-part estimate in
  the `-zeta'/zeta` sign convention.
- `exists_sigma_ge_sigmaOf_log_two_t_norm_bound_const_mul_log_div`
  specializes the arbitrary-imaginary-coordinate estimate to the `sigma + 2it`
  point used by the third term of the 3-4-1 inequality.
- `exists_sigma_ge_sigmaOf_log_two_t_re_neg_deriv_div_bound_const_mul_log_div`
  gives the corresponding `sigma + 2it` one-sided real-part estimate.
- `exists_sigma_ge_sigmaOf_log_two_t_norm_bound_log_scale`
  rewrites the weak `sigma + 2it` moving-strip norm estimate into standard
  `B * log |t|` form for each fixed `a`, with `B = C/a`.
- `exists_sigma_ge_sigmaOf_log_two_t_re_neg_deriv_div_bound_log_scale`
  gives the corresponding one-sided real-part `B * log |t|` estimate.
- `exists_sigma_ge_sigmaOf_log_any_im_norm_bound_log_scale`
  rewrites the arbitrary-imaginary-coordinate moving-strip norm estimate in
  standard `B * log |t|` form for each fixed `a`.
- `exists_sigma_ge_sigmaOf_log_any_im_re_neg_deriv_div_bound_log_scale`
  gives the corresponding arbitrary-imaginary-coordinate one-sided real-part
  estimate.
- `exists_sigma_ge_sigmaOf_log_neg_logDeriv_norm_bound_const_mul_log_div`
  gives the signed `-logDeriv zeta` norm variant of the weak moving-strip
  estimate, preserving the same `1/a` loss.
- `exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_const_mul_log_div`
  generalizes that signed norm estimate to arbitrary imaginary coordinate `u`.
- `exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_const_mul_log_div`
  specializes the signed norm estimate to the `sigma + 2it` point.
- `exists_sigma_ge_sigmaOf_log_any_im_neg_logDeriv_norm_bound_log_scale`
  rewrites the arbitrary-imaginary signed norm estimate in `B * log |t|`
  form for fixed `a`, with `B = C/a`.
- `exists_sigma_ge_sigmaOf_log_two_t_neg_logDeriv_norm_bound_log_scale`
  gives the corresponding signed `sigma + 2it` log-scale norm estimate.
- `exists_sigma_ge_sigmaOf_log_shift_pair_re_neg_deriv_div_bound_log_scale`
  packages the weak moving-strip estimates for both `sigma + it` and
  `sigma + 2it` under one shared coefficient `B`, still with `B = C/a`.
- `sigmaOf_log_weak_two_t_margin_impossible`
  proves that this weak `1/a` scale cannot satisfy the standard 3-4-1 constant
  margin when the real-axis and `sigma + 2it` coefficients are both at least
  one.
- `no_sigmaOf_log_margin_constants_with_weak_two_t`
  packages the same obstruction as nonexistence of positive constants `a,c`
  satisfying the standard weak-margin inequality.
- `sigmaOf_log_weak_shift_pair_margin_impossible`
  proves the stronger obstruction when both shifted terms are controlled only
  by the same weak `Cshift/a` scale.
- `sigmaOf_log_weak_shift_pair_log_scale_margin_impossible`
  gives the same obstruction in the normalized `B log |t|` shape whenever
  the shared shifted coefficient still satisfies `1/a <= B`.
- `no_sigmaOf_log_margin_constants_with_weak_shift_pair`
  packages that shared-weak-shift obstruction as nonexistence of positive
  constants `a,c`.
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
- `re_neg_deriv_div_riemannZeta_add_inv_le_of_regular_part_norm`
  converts a pointwise quotient-notation norm bound
  `||-zeta'/zeta(s)+(s-rho)^{-1}|| <= M` into the real-part inequality
  `Re(-zeta'/zeta(s))+1/(Re(s)-Re(rho)) <= M`.
- `re_neg_deriv_div_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm`
  is the multiplicity-aware version: a bound for
  `||-zeta'/zeta(s)+n(s-rho)^{-1}||` with `n > 0` still gives the weaker
  unit-principal real-part estimate needed by the zero-free contradiction.
- `re_neg_logDeriv_riemannZeta_add_inv_le_of_regular_part_norm` and
  `re_neg_logDeriv_riemannZeta_add_inv_le_of_multiplicity_regular_part_norm`
  are the same bridges in Mathlib's signed `-logDeriv zeta` notation.
- `re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm` and
  `re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm`
  are coordinate versions for estimates stated directly at `sigma + i t`
  with same-height zero candidate `beta + i t`.
- `re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm_one_add_log`
  and
  `re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm_one_add_log`
  turn coordinate `C * (1 + log |t|)` regular-part estimates at `|t| >= 3`
  into pure `2*C*log |t|` real-part singular estimates.
- `re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_regular_part_norm_log_abs_add_three`
  and
  `re_neg_logDeriv_riemannZeta_sigma_it_add_inv_le_of_multiplicity_regular_part_norm_log_abs_add_three`
  turn coordinate `C * log(|t| + 3)` regular-part estimates at `|t| >= 3`
  into pure `2*C*log |t|` real-part singular estimates.
- `logDerivRegularPartLogBound_of_high_height_log_abs_bound` and
  `multiplicityLogDerivRegularPartLogBound_of_high_height_log_abs_bound`
  turn future high-height regular-part estimates already stated as
  `B * log |t|` into the named regular-part interfaces, normalizing the
  cutoff to the standard `T0 >= 3` shape.
- `logDerivRegularPartLogBound_of_high_height_log_abs_add_three_bound` and
  `multiplicityLogDerivRegularPartLogBound_of_high_height_log_abs_add_three_bound`
  convert future `B * log(|t| + 3)` regular-part estimates into the exact
  `C * log |t|` named-interface form.
- `logDerivRegularPartLogBound_of_affine_log_abs_add_three_bound_high_height`
  and
  `multiplicityLogDerivRegularPartLogBound_of_affine_log_abs_add_three_bound_high_height`
  absorb affine `A + B * log(|t| + 3)` regular-part estimates into the named
  regular-part interfaces.  These are constructor theorems for future
  Borel/Jensen inputs, not proofs of the zeta-specific analytic estimate.
- `logDerivRegularPartLogBound_of_affine_log_norm_add_three_bound_high_height`
  and
  `multiplicityLogDerivRegularPartLogBound_of_affine_log_norm_add_three_bound_high_height`
  perform the same named-interface handoff for complex-variable estimates of
  the form `A + B * log(||s|| + 3)`, using the proved comparison
  `log(||sigma + i t|| + 3) <= 2 log |t|` above height `5`.
- `logDerivRegularPartLogBound_of_affine_log_norm_add_three_bound_on_verticalRegion`
  and
  `multiplicityLogDerivRegularPartLogBound_of_affine_log_norm_add_three_bound_on_verticalRegion`
  are the corresponding constructors when the future estimate is stated on
  `verticalRegion 1 2 T0`, matching the usual complex-analysis API shape.
- `exists_eventually_norm_logDeriv_le_const_of_analyticAt_ne_zero` and
  `exists_eventually_norm_neg_logDeriv_le_const_of_analyticAt_ne_zero`
  prove local boundedness of `logDeriv g` and `-logDeriv g` for any analytic
  function nonzero at the center.
- The automatic `..._analyticAt_order_eq_nat_auto` lemmas, together with their
  zeta-specific variants, turn analytic-order principal-part decompositions
  into punctured-ball regular-part norm bounds with an internally chosen
  constant, removing the manual `hregularBound` input.
- `classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound`
  replaces the regular-part real estimate by the norm estimate
  `||-zeta'/zeta(s)+(s-rho)^{-1}|| <= B log |Im(s)|`, together with the
  `sigma+2it` shifted estimate.
- `classical_zero_free_region_of_exists_multiplicity_regular_part_norm_bound_and_two_t_bound`
  accepts a future local estimate for
  `||-zeta'/zeta(s)+n(s-rho)^{-1}||` with some positive multiplicity `n`,
  and recovers the unit-principal real estimate used by the existing
  zero-free-region bridge.
- `classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound`
  packages that norm-bound regular-part input under one nonnegative
  logarithmic coefficient.
- `classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_two_t_bound`
  narrows the regular-part norm input to the standard moving line
  `sigma = 1 + a / log |t|`, still requiring the separate `sigma+2it`
  real-part logarithmic bound.
- `classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_two_t_logDeriv_norm_bound`
  accepts the same moving-line regular-part input and supplies the `sigma+2it`
  side from a norm bound for `logDeriv zeta` at the shifted point.
- `classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
  specializes a standard vertical-strip `logDeriv zeta` norm bound to the
  shifted `sigma+2it` point while keeping the regular-part input on the
  moving line only.
- `classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_two_t_bound`
  is the moving-line analogue of the multiplicity-aware regular-part closure:
  the local input may isolate `n * (s-rho)^{-1}` for some positive `n`.
- `classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_two_t_logDeriv_norm_bound`
  supplies the shifted `sigma+2it` side from a pointwise `logDeriv zeta` norm
  bound while keeping the multiplicity-aware regular-part input on the moving
  line.
- `classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`
  specializes a standard vertical-strip `logDeriv zeta` norm bound to the
  shifted point and combines it with the multiplicity-aware moving-line
  regular-part estimate.
- `classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_compact_band_deriv_bound_zeta_lower_bound_high_height`
  feeds the moving-line regular-part closure from primitive high-height `zeta'`
  growth and high-height positive lower bounds for `zeta`.
- `classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_compact_band_deriv_bound_zeta_lower_bound_high_height`
  is the multiplicity-aware version of the derivative-growth primitive route.
- `classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_compact_band_sphere_zeta_bound_high_height_zeta_lower_bound`
  combines the moving-line regular-part input with the compact-patched
  Cauchy/sphere route from fixed-radius `zeta` boundary growth and high-height
  `zeta` lower bounds.
- `classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_compact_band_sphere_zeta_bound_high_height_zeta_lower_bound`
  is the multiplicity-aware version of the same primitive Cauchy/sphere route:
  the moving-line regular part may isolate `n * (s-rho)^{-1}` for positive `n`.
- `classical_zero_free_region_of_exists_sigmaOf_log_regular_part_norm_bound_and_two_t_logDeriv_norm_bound`
  existentially packages the moving-line regular-part estimate and shifted
  norm logarithmic estimate under one nonnegative coefficient.
- `classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound`
  is the same norm-bound closure in Mathlib's natural `-logDeriv zeta`
  notation, rewriting through the verified quotient bridge.
- `classical_zero_free_region_of_exists_multiplicity_neg_logDeriv_regular_part_norm_bound_and_two_t_bound`
  is the multiplicity-aware closure in `-logDeriv zeta` notation, directly
  matching the output shape of the local principal-part decomposition lemmas.
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
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  is the coordinate unit-principal version of that high-height closure, with
  regular-part and vertical estimates stated directly for `sigma+it` and
  same-height zero candidates `beta+it`.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_bound_and_vertical_reNegDerivDiv_bound_high_height`
  is the coordinate unit-principal high-height closure where the vertical
  input is the direct real-part estimate for `Re(-zeta'/zeta)`, not a norm
  bound.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  packages the coordinate unit-principal high-height inputs existentially.
- `classical_zero_free_region_of_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  is the high-height version allowing the regular-part estimate to isolate a
  positive zero multiplicity `n`.
- `classical_zero_free_region_of_exists_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  packages the same multiplicity-aware high-height inputs existentially.
- `classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  is the coordinate version of the multiplicity-aware high-height closure, with
  estimates stated for `sigma+it` and same-height zero candidates `beta+it`.
- `classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_reNegDerivDiv_bound_high_height`
  is the multiplicity-aware coordinate high-height closure with the weaker
  direct real-part vertical input.
- `classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound_high_height`
  packages the coordinate multiplicity-aware high-height inputs existentially.
- `classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  accepts the common single-coefficient estimate shape `C * (1 + log |t|)`
  while preserving the positive multiplicity `n` in the local principal part.
- `classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bounds_high_height`
  allows separate `Cregular * (1 + log |t|)` and
  `Cvertical * (1 + log |t|)` coefficients for the two analytic estimates.
- `classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  and `..._bounds_high_height` package these multiplicity-aware one-add-log
  coordinate interfaces existentially.
- `classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  and `..._bounds_high_height` are the signed `-logDeriv zeta` versions of the
  same multiplicity-aware coordinate one-add-log closures.
- `classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_one_add_log_bound_high_height`
  and `..._bounds_high_height` package those signed high-height inputs
  existentially.
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
- `LogDerivVerticalLogBound`, `NegLogDerivVerticalLogBound`, and
  `ReNegDerivDivVerticalLogBound`
  name the standard `C * log |t|` high-height interfaces on
  `1 <= sigma <= 2` for `logDeriv zeta`, `-logDeriv zeta`, and the real-part
  quotient `Re(-zeta'/zeta)`.
- `LogDerivRegularPartLogBound`
  names the companion high-height zero-candidate regular-part interface
  `||logDeriv zeta (sigma+it) - (sigma-beta)^(-1)|| <= C log |t|`
  for zeros `beta+it` with `beta < 1`.
- `MultiplicityLogDerivRegularPartLogBound`
  is the multiplicity-aware version of that regular-part interface, allowing
  the principal part to be `n/(sigma-beta)` for some positive natural `n`.
- `reNegDerivDivVerticalLogBound_of_logDerivVerticalLogBound`
  turns the named `logDeriv zeta` norm interface into the named
  `Re(-zeta'/zeta)` interface.
- `logDerivVerticalLogBound_of_negLogDerivVerticalLogBound`
  turns the named signed norm interface into the unsigned norm interface.
- `negLogDerivVerticalLogBound_of_logDerivVerticalLogBound`
  gives the converse conversion, making the named `logDeriv zeta` and
  `-logDeriv zeta` norm-bound interfaces interchangeable.
- `reNegDerivDivVerticalLogBound_of_negLogDerivVerticalLogBound`
  turns the named signed norm interface directly into the named
  `Re(-zeta'/zeta)` interface.
- `logDerivVerticalLogBound_mono_height`,
  `negLogDerivVerticalLogBound_mono_height`,
  `reNegDerivDivVerticalLogBound_mono_height`,
  `logDerivRegularPartLogBound_mono_height`, and
  `multiplicityLogDerivRegularPartLogBound_mono_height`
  show the named high-height estimates remain valid after raising the cutoff.
- `logDerivVerticalLogBound_mono_const`,
  `negLogDerivVerticalLogBound_mono_const`,
  `reNegDerivDivVerticalLogBound_mono_const`,
  `logDerivRegularPartLogBound_mono_const`, and
  `multiplicityLogDerivRegularPartLogBound_mono_const`
  show the same named interfaces remain valid after increasing the bound
  constant.
- `multiplicityLogDerivRegularPartLogBound_of_logDerivRegularPartLogBound`
  turns the simple-principal-part regular estimate into the
  multiplicity-aware form with multiplicity `1`.
- `classical_zero_free_region_of_LogDerivRegularPartLogBound_and_LogDerivVerticalLogBound`
  assembles the named regular-part interface and named vertical interface into
  the classical zero-free-region target.
- `classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_LogDerivVerticalLogBound`
  is the same named-input assembly with zero multiplicity in the local
  principal part.
- `classical_zero_free_region_of_LogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`
  assembles the named regular-part interface with the signed
  `-logDeriv zeta` vertical norm interface by converting it to the unsigned
  `LogDerivVerticalLogBound` convention.
- `classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`
  is the multiplicity-aware signed-vertical version of that final assembly.
- `classical_zero_free_region_of_LogDerivRegularPartLogBound_and_ReNegDerivDivVerticalLogBound`
  assembles the named regular-part interface and the named direct real-part
  `Re(-zeta'/zeta)` vertical interface into the classical zero-free-region
  target.
- `classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_ReNegDerivDivVerticalLogBound`
  is the multiplicity-aware direct real-part version of that final assembly.
- `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_LogDerivVerticalLogBound`
  allows the regular-part and vertical estimates to be supplied
  existentially with different high-height cutoffs, then merges the cutoffs by
  taking their maximum.
- `classical_zero_free_region_of_exists_MultiplicityLogDerivRegularPartLogBound_and_exists_LogDerivVerticalLogBound`
  is the multiplicity-aware version of that different-cutoff existential
  assembly.
- `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_ReNegDerivDivVerticalLogBound`
  and its multiplicity-aware analogue provide the same different-cutoff
  assembly for the direct real-part vertical interface.
- `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_NegLogDerivVerticalLogBound`
  and its multiplicity-aware analogue provide the same different-cutoff
  assembly for the signed vertical norm interface.
- `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_deriv_bound_zeta_lower_bound_high_height`
  and its multiplicity-aware / `verticalRegion` variants compose that final
  assembly with the primitive `ζ'` growth plus positive `ζ` lower-bound
  normalizer.  These are proved conditional bridges to
  `classical_zero_free_region`; they do not prove the primitive zeta
  estimates themselves.
- `exists_re_im_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  converts a future boundary-strip estimate
  `||logDeriv zeta (sigma+it)|| <= A + B log(|t|+3)` into the exact
  `C log |t|` target shape.
- `logDeriv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  is the same conversion packaged against the named
  `LogDerivVerticalLogBound` interface.
- `logDerivVerticalLogBound_of_high_height_log_abs_bound`
  packages a future high-height `B * log |t|` estimate directly as the named
  `LogDerivVerticalLogBound` interface.
- `negLogDerivVerticalLogBound_of_high_height_log_abs_bound`
  is the signed `-logDeriv zeta` version of the same exact-scale constructor.
- `reNegDerivDivVerticalLogBound_of_high_height_log_abs_bound`
  packages a future exact-scale real-part quotient estimate directly as the
  named `ReNegDerivDivVerticalLogBound` interface.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_affine_log_abs_add_three_bound_high_height`
  composes that affine high-height normalizer directly with the fixed-margin
  BTY detector handoff, preserving the normalized `LogDerivVerticalLogBound`
  constants for downstream use.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_affine_log_abs_add_three_bound_high_height_simplified`
  is the same direct affine-high-height-to-BTY bridge with the nonzero detector
  coefficient sum evaluated explicitly.
- `exists_re_im_logDeriv_vertical_log_bound_of_log_abs_add_three_bound_high_height`
  is the multiplicative `C log(|t|+3)` version of that normalizer.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_log_abs_add_three_bound_high_height`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_log_abs_add_three_bound_high_height_simplified`
  specialize the direct BTY bridge to multiplicative
  `C log(|t|+3)` high-height inputs.
- `exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  is the signed affine normalizer for future estimates on
  `||-logDeriv zeta (sigma+it)||`.
- `negLogDeriv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  packages the signed affine normalizer against
  `NegLogDerivVerticalLogBound`.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_affine_log_abs_add_three_bound_high_height`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_affine_log_abs_add_three_bound_high_height_simplified`
  compose signed affine high-height inputs with the fixed-margin BTY handoff
  through the `NegLogDerivVerticalLogBound` to `LogDerivVerticalLogBound`
  conversion.
- `exists_re_im_neg_logDeriv_vertical_log_bound_of_log_abs_add_three_bound_high_height`
  is the signed multiplicative `C log(|t|+3)` version.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_log_abs_add_three_bound_high_height`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_log_abs_add_three_bound_high_height_simplified`
  specialize that signed direct BTY bridge to multiplicative
  `C log(|t|+3)` high-height inputs.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_logDeriv_bound`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_logDeriv_bound_simplified`
  feed an exact-scale future norm input
  `||logDeriv zeta(sigma+it)|| <= B log |t|` directly into the fixed-margin
  BTY handoff through the named `LogDerivVerticalLogBound` interface.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_negLogDeriv_bound`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_high_height_negLogDeriv_bound_simplified`
  are the signed-norm exact-scale versions, accepting
  `||-logDeriv zeta(sigma+it)|| <= B log |t|` before converting to the
  unsigned vertical interface used by the BTY detector.
- `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound`
  and
  `exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound_simplified`
  feed an exact-scale future real-part input
  `Re(-zeta'/zeta) <= B log |t|` directly into the fixed-margin BTY handoff
  through the named `ReNegDerivDivVerticalLogBound` interface.
- `exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  converts affine `log(|t|+3)` norm growth for `logDeriv zeta` directly into
  the real-part quotient convention `Re(-zeta'/zeta) <= C log |t|`.
- `reNegDerivDiv_riemannZeta_vertical_log_bound_of_affine_log_abs_add_three_bound_high_height`
  packages that real-part quotient conversion against the named
  `ReNegDerivDivVerticalLogBound` interface.
- `exists_re_neg_deriv_div_vertical_log_bound_of_neg_affine_log_abs_add_three_bound_high_height`
  is the signed-norm version, consuming affine growth for `||-logDeriv zeta||`.
- `norm_sigma_add_I_mul_le_abs_add_two`
  proves `||sigma + it|| <= |t| + 2` on `1 <= sigma <= 2`.
- `log_norm_sigma_add_I_mul_add_three_le_two_log_abs`
  proves `log(||sigma + it|| + 3) <= 2 log |t|` for
  `1 <= sigma <= 2` and `|t| >= 5`.
- `log_norm_sigma_add_I_mul_add_three_le_two_log_abs_of_re_le_three`
  proves the same comparison on the wider `1 <= sigma <= 3` strip for
  `|t| >= 6`, matching right-shifted Borel centers.
- `log_abs_le_log_norm_sigma_add_I_mul_add_three`
  proves the reverse comparison `log |t| <= log(||sigma+it||+3)` at positive
  height, so already-normalized Borel outputs can feed full-height closures.
- `log_norm_add_three_le_two_log_abs_im`
  is the corresponding complex-variable comparison in terms of
  `s.re` and `s.im`.
- `log_norm_sigma_add_I_mul_add_three_le_two_log_abs_add_three`
  gives the same coordinate comparison in the `log(|t|+3)` scale consumed by
  high-height handoff lemmas.
- `log_norm_bound_of_polynomial_growth`
  converts a pointwise polynomial-growth estimate
  `||f z|| <= A * (||z|| + 3)^B`, with `A >= 1` and `B >= 0`, into the
  affine logarithmic norm bound
  `log ||f z|| <= log A + B * log(||z|| + 3)`.
- `log_norm_riemannZeta_le_affine_log_norm_add_three_of_polynomial_growth`
  specializes that conversion to a future zeta polynomial-growth estimate on
  the high vertical region `T0 <= |Im z|`, `1 <= Re z <= 3`.
- `norm_riemannZeta_le_re_zeta_two_of_two_le_re` and
  `norm_riemannZeta_le_const_polynomial_on_two_le_re` now supply the proved
  right-edge input on `2 <= Re(s)`; the still-missing analytic input is the
  continuation of comparable control across the boundary strip
  `1 <= Re(s) <= 2` at high height.
- `norm_deriv_riemannZeta_le_re_zeta_two_div_radius_of_closedBall_two_le_re`
  uses Cauchy's derivative estimate plus the right-edge zeta bound to prove
  `||zeta'(c)|| <= Re(zeta(2)) / R` whenever `closedBall c R` stays in
  `2 <= Re(s)`.
- `norm_deriv_riemannZeta_sigma_it_le_re_zeta_two_div_radius_of_two_add_radius_le`
  is the coordinate version for centers `sigma + i t` with `2 + R <= sigma`.
- `norm_logDeriv_riemannZeta_le_three_mul_re_zeta_two_div_radius_of_two_add_radius_le_re`
  and its coordinate form combine the `Re >= 2` denominator margin with the
  Cauchy derivative estimate to prove a radius-dependent right-edge
  logarithmic-derivative bound.
- `exists_norm_logDeriv_riemannZeta_le_log_abs_im_of_two_add_radius_le_re`,
  its signed and real-part variants, and
  `exists_re_neg_deriv_div_riemannZeta_shift_pair_le_log_abs_of_two_add_radius_le`
  put that right-edge control into the high-height `C * log |t|` scale for the
  two shifted 3-4-1 points.
- `exists_re_neg_deriv_div_riemannZeta_right_edge_three_four_one_bounds` adds
  the real-axis center term to the shifted pair, giving one `C * log |t|`
  upper bound for all three real parts when `2 + R <= sigma`.
- `exists_three_four_one_combination_le_log_abs_of_two_add_radius_le` combines
  the preceding right-edge three-term upper bound with the proved 3-4-1
  nonnegativity, producing `0 <= combination <= C * log |t|` on the
  right edge.  This is still a right-boundary input, not the missing
  vertical-strip estimate on `1 <= Re(s) <= 2`.
- `exists_re_neg_deriv_div_riemannZeta_sigma_it_lower_bound_log_abs_of_two_add_radius_le`
  uses the same 3-4-1 nonnegativity together with the right-edge upper bounds
  for the real-axis and doubled-height terms to force the middle term
  `Re(-zeta'/zeta(sigma+i t))` to be bounded below by `-C * log |t|`.
  This is the right-edge analogue of the lower-bound shape used in later
  zero-repulsion arguments.
- `exists_abs_re_neg_deriv_div_riemannZeta_sigma_it_le_log_abs_of_two_add_radius_le`
  combines the direct right-edge upper bound and the 3-4-1 lower bound into the
  two-sided real-part estimate
  `|Re(-zeta'/zeta(sigma+i t))| <= C * log |t|`.
- `norm_riemannZeta_sub_one_le_half_of_three_le_re` and
  `half_le_norm_riemannZeta_of_three_le_re` prove the far-right tail estimate
  `||zeta(s)-1|| <= 1/2` and lower bound `1/2 <= ||zeta(s)||` on
  `3 <= Re(s)`.
- `norm_logDeriv_riemannZeta_le_two_mul_re_zeta_two_of_three_le_re` and its
  coordinate form combine the preceding lower bound with the Cauchy derivative
  estimate to prove a constant `logDeriv zeta` bound on `3 <= Re(s)`.
- `exists_norm_logDeriv_riemannZeta_sigma_it_le_log_abs_of_three_le_sigma`
  packages that far-right constant bound into the high-height
  `C * log |t|` scale for `3 <= sigma` and `2 <= |t|`.
- `log_norm_riemannZeta_sigma_it_le_affine_log_norm_add_three_of_polynomial_growth`
  is the coordinate form at points `sigma + i t`.
- `log_norm_riemannZeta_sigma_it_le_affine_log_abs_add_three_of_polynomial_growth`
  combines the zeta polynomial-growth handoff with the height comparison to
  produce the `log(|t|+3)` form on `1 <= sigma <= 2`.
- `circleAverage_log_norm_riemannZeta_sigma_it_le_affine_log_abs_add_radius_three_of_polynomial_growth`
  lifts the same future polynomial-growth input to a circle-average
  `log ||zeta||` bound, with the center height enlarged by the radius.
- `jensen_localDivisor_riemannZeta_sigma_it_le_affine_log_abs_add_radius_three_of_polynomial_growth`
  rewrites that circle-average bound through Jensen's formula into the local
  divisor plus trailing-coefficient side.
- `jensen_localDivisor_riemannZeta_sigma_it_le_affine_log_abs_add_radius_three_of_polynomial_growth_of_pos_radius`
  is the positive-radius form with all closed balls and height scales stated
  using `R` rather than `|R|`.
- `norm_deriv_riemannZeta_le_of_sphere_norm_bound_avoid_one`,
  `norm_deriv_riemannZeta_le_of_sphere_norm_bound_dist_one`, and
  `norm_deriv_riemannZeta_sigma_it_le_of_sphere_norm_bound_height`
  are Cauchy derivative estimates converting a boundary `||zeta||` bound on a
  disk avoiding the pole into a center `||zeta'||` bound.
- `exists_re_im_logDeriv_vertical_log_bound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height`,
  `logDerivVerticalLogBound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height`,
  and
  `reNegDerivDivVerticalLogBound_of_sphere_zeta_bound_and_zeta_lower_bound_high_height`
  compose the Cauchy derivative estimate with a positive center lower bound
  for `zeta`, yielding the same high-height `logDeriv` and real-part quotient
  interfaces from boundary `||zeta||` control on fixed-radius circles.
- `exists_re_im_logDeriv_vertical_log_bound_of_sphere_zeta_bound_and_zeta_lower_bound_on_verticalRegion`,
  `logDerivVerticalLogBound_of_sphere_zeta_bound_and_zeta_lower_bound_on_verticalRegion`,
  and
  `reNegDerivDivVerticalLogBound_of_sphere_zeta_bound_and_zeta_lower_bound_on_verticalRegion`
  are the same Cauchy/sphere handoff when the boundary growth and center
  lower-bound inputs are stated directly on `verticalRegion 1 2 T0`.
- `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_sphere_zeta_bound_zeta_lower_bound_high_height`
  and its multiplicity-aware companion compose an existential regular-part
  estimate with fixed-radius boundary `||zeta||` growth and a positive center
  lower bound to close the conditional `classical_zero_free_region` target.
- `classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_sphere_zeta_bound_zeta_lower_bound_on_verticalRegion`
  and its multiplicity-aware companion provide the same final assembly when
  the future boundary growth and lower-bound estimates are stated directly on
  `verticalRegion 1 2 T0`.
- `logDerivVerticalLogBound_of_compact_band_and_sphere_zeta_bound_high_height_zeta_lower_bound`,
  `reNegDerivDivVerticalLogBound_of_compact_band_and_sphere_zeta_bound_high_height_zeta_lower_bound`,
  and the corresponding final zero-free-region assemblies patch the center
  `zeta` lower bound at bounded height by compactness, so only the high-height
  center lower bound and boundary `||zeta||` growth remain as future inputs.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_compact_band_sphere_zeta_bound_high_height_zeta_lower_bound`
  packages the same compact-patched Cauchy/sphere route directly into the
  ordinary/shifted real-part pair used by the 3-4-1 inequality.
- `exists_re_im_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`
  converts a future boundary-strip estimate
  `||logDeriv zeta (sigma+it)|| <= A + B log(||sigma+it||+3)` into
  the exact `C log |t|` target shape.
- `exists_re_im_logDeriv_vertical_log_bound_of_log_norm_add_three_bound_high_height`
  is the multiplicative version for inputs already stated as
  `C log(||sigma+it||+3)`.
- `exists_re_im_logDeriv_vertical_log_bound_of_deriv_bound_and_zeta_lower_bound_high_height`
  reduces the same vertical `logDeriv zeta` target to an affine logarithmic
  bound for `||zeta'(sigma+it)||` plus a positive lower bound for
  `||zeta(sigma+it)||` on the same high-height strip.
- `exists_re_im_neg_logDeriv_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`
  is the signed affine full-height normalizer for future estimates on
  `||-logDeriv zeta (sigma+it)||`.
- `exists_re_im_neg_logDeriv_vertical_log_bound_of_log_norm_add_three_bound_high_height`
  is the signed multiplicative version for inputs already stated as
  `C log(||sigma+it||+3)`.
- `exists_re_neg_deriv_div_vertical_log_bound_of_affine_log_norm_add_three_bound_high_height`
  converts the same affine norm-growth input for `logDeriv zeta` directly into
  the real-part quotient convention `Re(-zeta'/zeta) <= C log |t|`.
- `exists_re_neg_deriv_div_vertical_log_bound_of_neg_affine_log_norm_add_three_bound_high_height`
  is the signed-norm version, consuming an affine growth estimate for
  `||-logDeriv zeta||` and producing the same real-part quotient output.
- `logDerivVerticalLogBound_of_affine_log_norm_add_three_bound_high_height`
  and `logDerivVerticalLogBound_of_log_norm_add_three_bound_high_height`
  package the full-height `log(||sigma+it||+3)` normalizers directly into the
  named `LogDerivVerticalLogBound` interface.
- `logDerivVerticalLogBound_of_deriv_bound_and_zeta_lower_bound_high_height`
  packages the derivative-growth plus zeta-lower-bound bridge into the same
  named `LogDerivVerticalLogBound` interface.
- `negLogDerivVerticalLogBound_of_affine_log_norm_add_three_bound_high_height`
  and `negLogDerivVerticalLogBound_of_log_norm_add_three_bound_high_height`
  provide the same named-interface packaging in the signed `-logDeriv zeta`
  convention.
- `reNegDerivDivVerticalLogBound_of_affine_log_norm_add_three_bound_high_height`
  and `reNegDerivDivVerticalLogBound_of_neg_affine_log_norm_add_three_bound_high_height`
  package full-height norm-growth inputs into the named real-part quotient
  interface consumed by the 3-4-1 route.
- `reNegDerivDivVerticalLogBound_of_deriv_bound_and_zeta_lower_bound_high_height`
  sends the derivative-growth plus zeta-lower-bound pair directly to the named
  `ReNegDerivDivVerticalLogBound` interface.
- `logDerivVerticalLogBound_of_affine_log_norm_add_three_bound_on_verticalRegion`
  and its multiplicative, signed, and real-part variants accept estimates
  stated directly on `verticalRegion 1 2 T0`, then specialize them to the
  coordinate `sigma + i t` named vertical-bound interfaces.
- `logDerivVerticalLogBound_of_deriv_bound_and_zeta_lower_bound_on_verticalRegion`
  accepts the derivative-growth plus zeta-lower-bound pair directly on
  `verticalRegion 1 2 T0`, matching the natural input shape of future
  Cauchy/Borel/Jensen estimates.
- `reNegDerivDivVerticalLogBound_of_deriv_bound_and_zeta_lower_bound_on_verticalRegion`
  is the corresponding direct real-part quotient handoff for the same
  complex-variable input shape.
- `reNegDerivDivVerticalLogBound_of_affine_re_log_norm_add_three_bound_high_height`
  and `reNegDerivDivVerticalLogBound_of_re_log_norm_add_three_bound_high_height`
  normalize direct `Re(-zeta'/zeta)` estimates in the full-height
  `log(||sigma+it||+3)` scale.
- `reNegDerivDivVerticalLogBound_of_affine_re_log_norm_add_three_bound_on_verticalRegion`
  and `reNegDerivDivVerticalLogBound_of_re_log_norm_add_three_bound_on_verticalRegion`
  provide the same direct real-part handoff for complex-variable estimates on
  `verticalRegion 1 2 T0`.
- `exists_re_neg_deriv_div_riemannZeta_shifted_vertical_log_bound_of_ReNegDerivDivVerticalLogBound`
  applies a named direct real-part vertical bound at `u = 2t`, absorbing
  `log |2t|` into `log |t|`, to produce the shifted third 3-4-1 input.
- `exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_ReNegDerivDivVerticalLogBound`
  packages the ordinary and shifted direct real-part estimates with one shared
  constant and cutoff.
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
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height`
  accepts affine safe-height estimates
  `Aregular + Bregular * log(|t| + 3)` and
  `Avertical + Bvertical * log(|t| + 3)`.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height`
  packages that affine safe-height interface existentially.
- `classical_zero_free_region_of_re_im_neg_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height`
  is the signed `-logDeriv zeta` version of the affine safe-height interface.
- `classical_zero_free_region_of_exists_re_im_neg_logDeriv_regular_part_norm_affine_log_abs_add_three_bounds_high_height`
  packages the signed affine safe-height interface existentially.
- `classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  accepts separate constants in estimates stated with the full complex
  height `log(||sigma + it|| + 3)`.
- `classical_zero_free_region_of_exists_re_im_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  packages that full-height logarithmic interface existentially.
- `classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  and `..._bound_high_height` are the multiplicity-aware coordinate versions,
  allowing the regular-part estimate to isolate `n/(sigma-beta)`.
- `classical_zero_free_region_of_exists_re_im_multiplicity_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  and `..._bound_high_height` package those multiplicity-aware full-height
  coordinate inputs existentially.
- `classical_zero_free_region_of_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  and `..._bound_high_height` are the signed `-logDeriv zeta` multiplicity
  versions of the same full-height coordinate handoff.
- `classical_zero_free_region_of_exists_re_im_multiplicity_neg_logDeriv_regular_part_norm_log_norm_add_three_bounds_high_height`
  and `..._bound_high_height` package those signed multiplicity-aware inputs
  existentially.
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
- `borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  and
  `borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  are direct disk-geometric versions: they avoid the ambient `verticalRegion`
  wrapper and leave only a pointwise real-part bound on the local `sigma+I*t`
  ball.
- `differentiableOn_neg_logDeriv_riemannZeta_closedBall_sigma_it_of_disk_right_half`
  gives the signed closed-disk differentiability wrapper used by direct
  signed Borel estimates.
- `borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  and
  `borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le`
  are the matching direct disk-geometric Borel wrappers in the
  `-logDeriv zeta` convention.
- `borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
  and
  `borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
  remove the raw Borel disk denominator terms directly on local `sigma+I*t`
  disks for `logDeriv zeta`.
- `borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
  and
  `borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_re_le_half_radius`
  give the same direct half-radius interface in the `-logDeriv zeta`
  convention used by the 3-4-1 argument.
- `borelCaratheodory_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_sub_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
  normalize direct disk real-part inputs of the form
  `A + B log(||sigma+I*t||+3)` to denominator-free half-radius bounds.
- `borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_sub_neg_logDeriv_riemannZeta_sigma_it_of_disk_right_half_of_affine_re_le_half_radius`
  provide the same affine direct half-radius interface in the signed
  `-logDeriv zeta` convention.
- `borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_of_affine_re_le_half_radius`
  move the affine half-radius Borel handoff to a disk centered at
  `(sigma+r)+I*t`, controlling the boundary-near point `sigma+I*t` while
  keeping the local real-part and center estimates as explicit hypotheses.
- `borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  combine that right-shifted handoff with the wider logarithmic comparison,
  producing a pure `C log |t|` bound from the same local hypotheses.
- `borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_log_abs_add_three_re_le_half_radius`
  and
  `borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_log_abs_add_three_re_le_half_radius`
  are the same right-shifted pure `C log |t|` outputs, but with the local
  real-part and center hypotheses already stated in the `log(|t|+3)` scale.
- `borelCaratheodory_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
  repackage the same right-shifted handoff in the full complex-height scale
  `C log(||sigma+it|| + 3)`, so closures stated in the natural norm scale can
  consume the normalized Borel output.
- `re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius`
  and
  `re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius`
  convert those normalized right-shifted norm bounds into the
  `Re(-zeta'/zeta) <= C log |t|` convention used by the 3-4-1 chain.
- `re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `re_neg_deriv_div_riemannZeta_sigma_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
  provide the same real-part quotient conversion in the full complex-height
  `C log(||sigma+it|| + 3)` scale.
- `re_neg_deriv_div_riemannZeta_finset_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `re_neg_deriv_div_riemannZeta_finset_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
  package the same right-shifted quotient conversion over a finite family of
  heights `tau k`, giving the Borel-side supplier shape needed before
  higher-degree finite detectors consume one shifted upper bound per
  frequency.
- `re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius_of_pos_A`
  / `...affine_neg_logDeriv..._of_pos_A` and their full-height `log_norm`
  analogues discharge the pair-level Borel positivity conditions at both
  heights `t` and `2t` from `0 < Are` and `0 <= Bre`.  The
  `exists_re_neg_deriv_div_riemannZeta_shift_pair_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius_fixed_margin_center_of_pos_A`
  / signed analogue also combine this with the fixed-margin center discharge,
  leaving only the local real-part Borel hypotheses on the two right-shifted
  disks as the remaining analytic input.
- `RiemannPNT.API.log_deriv_zeta_finset_single_lower_bound_auto_of_right_shift_borel_family`
  and
  `RiemannPNT.API.log_deriv_zeta_finset_single_lower_bound_auto_of_signed_right_shift_borel_family`
  compose those finite-family Borel suppliers with the automatic finite
  detector lower-bound theorem, so the detector algebra now consumes
  right-shifted local Borel hypotheses directly over `S.erase m`.
- `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_right_shift_borel_family`
  and
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_signed_right_shift_borel_family`
  specialize that composition to the checked BTY degree-16 detector and the
  selected `k = 1` term, discharging the BTY certificate and coefficient
  nonnegativity side conditions.
- `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family`,
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_right_shift_borel_family_simplified`,
  and
  `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_uniform_signed_right_shift_borel_family`
  add a final uniform-bound comparison for the remaining BTY frequencies and
  use the computed sum
  `sum_{k in btyDetectorSupport.erase 1} btyDetectorCoeff k =
  6917296 / 2485395`; the unsigned simplified facade rewrites the resulting
  penalty as `3458648 / 2163835`.
- `RiemannPNT.API.log_deriv_zeta_bty_detector_one_lower_bound_of_center_and_LogDerivVerticalLogBound`
  exposes the mixed BTY entrypoint that consumes a future named vertical
  logarithmic-derivative estimate plus a separate central-term bound.
- `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound`
  composes that mixed BTY handoff with the proved fixed-margin
  `Re(s) >= 1 + epsilon` logarithmic-derivative estimate, using the height-zero
  bound to discharge the central `k = 0` term automatically.  This is still a
  fixed-margin result, not the classical shrinking-width zero-free-region
  estimate.
- `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_LogDerivVerticalLogBound_simplified`
  keeps the same fixed-margin hypotheses and central-term discharge, but
  exposes the evaluated nonzero-frequency coefficient sum in the final lower
  bound.
- `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_affine_log_abs_add_three_bound_high_height`
  and
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_affine_log_abs_add_three_bound_high_height_simplified`
  let future affine `A + B log(|t|+3)` high-height `logDeriv zeta` estimates
  feed the same fixed-margin BTY lower-bound interface directly.
- `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_log_abs_add_three_bound_high_height`
  and
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_log_abs_add_three_bound_high_height_simplified`
  are the corresponding direct fixed-margin BTY bridges for multiplicative
  `C log(|t|+3)` high-height inputs.
- `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_affine_log_abs_add_three_bound_high_height`,
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_affine_log_abs_add_three_bound_high_height_simplified`,
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_log_abs_add_three_bound_high_height`, and
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_neg_log_abs_add_three_bound_high_height_simplified`
  expose the same direct BTY bridge for signed `-logDeriv zeta` high-height
  inputs.
- `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound`
  and
  `RiemannPNT.API.exists_log_deriv_zeta_bty_detector_one_lower_bound_of_fixed_margin_center_and_re_high_height_log_abs_bound_simplified`
  expose the exact-scale real-part version, consuming a future
  `Re(-zeta'/zeta) <= B log |t|` high-height estimate directly.
- `RiemannPNT.API.classical_zero_free_region_of_LogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`
  and
  `RiemannPNT.API.classical_zero_free_region_of_MultiplicityLogDerivRegularPartLogBound_and_NegLogDerivVerticalLogBound`
  expose the signed vertical norm final assemblies through the public facade.
- `RiemannPNT.API.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_exists_NegLogDerivVerticalLogBound`
  and
  `RiemannPNT.API.classical_zero_free_region_of_exists_MultiplicityLogDerivRegularPartLogBound_and_exists_NegLogDerivVerticalLogBound`
  expose the corresponding different-cutoff existential signed-vertical
  assemblies.
- `RiemannPNT.API.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_logDeriv_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_negLogDeriv_bound`,
  and
  `RiemannPNT.API.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_high_height_reNegDerivDiv_bound`
  expose the direct exact-scale high-height assemblies, together with their
  multiplicity-aware analogues.
- `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_two_t_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_two_t_logDeriv_norm_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_two_t_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_two_t_logDeriv_norm_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_vertical_logDeriv_norm_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_compact_band_deriv_bound_zeta_lower_bound_high_height`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_compact_band_deriv_bound_zeta_lower_bound_high_height`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_regular_part_norm_bound_and_compact_band_sphere_zeta_bound_high_height_zeta_lower_bound`,
  `RiemannPNT.API.classical_zero_free_region_of_sigmaOf_log_multiplicity_regular_part_norm_bound_and_compact_band_sphere_zeta_bound_high_height_zeta_lower_bound`,
  and
  `RiemannPNT.API.classical_zero_free_region_of_exists_sigmaOf_log_regular_part_norm_bound_and_two_t_logDeriv_norm_bound`
  expose the moving-line regular-part closures through the public facade.
- `RiemannPNT.API.exists_logDeriv_regular_part_sigmaOf_log_bound_of_absolute_convergence`
  exposes the proved weak moving-line regular-part estimate from absolute
  convergence; the constant depends on the fixed margin `a`, so this is a
  baseline theorem rather than the missing uniform Borel/Jensen input.
- `RiemannPNT.API.exists_re_neg_logDeriv_riemannZeta_sigmaOf_log_add_inv_le_of_absolute_convergence`
  exposes the corresponding weak real-part zero-repulsion inequality
  `Re(-zeta'/zeta)(sigma+it)+1/(sigma-beta) <= B(a) log |t|` at
  `sigma = 1 + a/log |t|`.
- `RiemannPNT.API.exists_logDeriv_regular_part_sigmaOf_log_bound_of_absolute_convergence_uniform_of_le`
  and
  `RiemannPNT.API.exists_re_neg_logDeriv_riemannZeta_sigmaOf_log_add_inv_le_of_absolute_convergence_uniform_of_le`
  expose the version uniform over all moving-line parameters `a >= a0`.
- `RiemannPNT.API.exists_norm_logDeriv_riemannZeta_sigma_ge_sigmaOf_log_shift_pair_le_log_abs_uniform_of_le`
  and
  `RiemannPNT.API.exists_re_neg_deriv_div_riemannZeta_sigma_ge_sigmaOf_log_shift_pair_le_log_abs_uniform_of_le`
  expose the matching uniform-away-from-boundary shifted-pair estimates.
- `RiemannPNT.API.exists_norm_multiplicity_neg_logDeriv_regular_part_sigmaOf_log_bound_of_absolute_convergence_uniform_of_le`
  and
  `RiemannPNT.API.exists_re_neg_logDeriv_riemannZeta_sigmaOf_log_add_multiplicity_inv_le_of_absolute_convergence_uniform_of_le`
  expose the fixed-multiplicity version uniform over `a >= a0`.
- `RiemannPNT.API.exists_norm_multiplicity_neg_logDeriv_regular_part_sigmaOf_log_bound_of_absolute_convergence`
  and
  `RiemannPNT.API.exists_re_neg_logDeriv_riemannZeta_sigmaOf_log_add_multiplicity_inv_le_of_absolute_convergence`
  expose the fixed-multiplicity versions of that weak moving-line
  regular-part baseline.
- `RiemannPNT.API.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_sphere_zeta_bound_zeta_lower_bound_high_height`
  and
  `RiemannPNT.API.classical_zero_free_region_of_exists_LogDerivRegularPartLogBound_and_sphere_zeta_bound_zeta_lower_bound_on_verticalRegion`
  expose the fixed-radius boundary-`zeta` final assemblies, together with
  their multiplicity-aware analogues.
- `RiemannPNT.API.logDerivVerticalLogBound_of_compact_band_and_sphere_zeta_bound_high_height_zeta_lower_bound`
  and the matching `ReNegDerivDivVerticalLogBound` / final-assembly aliases
  expose the compact-patched sphere handoff through the public facade.
- `RiemannPNT.API.exists_re_neg_deriv_div_riemannZeta_shift_pair_vertical_log_bound_of_compact_band_sphere_zeta_bound_high_height_zeta_lower_bound`
  exposes the compact-patched Cauchy/sphere route directly in the ordinary
  and shifted real-part pair shape consumed by the 3-4-1 argument.
- `RiemannPNT.API.classical_zero_free_region_of_re_im_logDeriv_regular_part_norm_bound_and_vertical_reNegDerivDiv_bound_high_height`
  and
  `RiemannPNT.API.classical_zero_free_region_of_re_im_multiplicity_logDeriv_regular_part_norm_bound_and_vertical_reNegDerivDiv_bound_high_height`
  expose the coordinate direct-real-part closures through the public facade.
- `RiemannPNT.API.differentiableOn_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_of_disk_right_half`
  and the three public
  `RiemannPNT.API.exists_re_neg_logDeriv_riemannZeta_sigma_it_...right_shift...`
  aliases expose the newest right-shift differentiability discharge and
  zero-repulsion handoffs to downstream users.
- `re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_logDeriv_re_le_half_radius`
  and
  `re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_abs_of_affine_neg_logDeriv_re_le_half_radius`
  repeat the same handoff for the shifted third 3-4-1 point `sigma+2it`,
  absorbing `log |2t|` into `log |t|`.
- `re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_logDeriv_re_le_half_radius`
  and
  `re_neg_deriv_div_riemannZeta_sigma_two_it_right_shift_le_log_norm_of_affine_neg_logDeriv_re_le_half_radius`
  provide the shifted third-term handoff in the same full-height
  `C log(||sigma+it|| + 3)` scale as the main `sigma+it` estimate.
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
- `borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  converts the positive half-radius Borel output to the safer one-dimensional
  height scale `A + B log(|t| + 3)`, assuming `1 <= sigma <= 2`,
  `5 <= |t|`, and nonnegative affine slopes.
- `borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  gives the corresponding centered oscillation bound for
  `logDeriv zeta(z) - logDeriv zeta(sigma+it)` in the same height scale.
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
- `borelCaratheodory_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  is the signed `log(|t| + 3)` version of the same half-radius Borel bridge,
  matching the sign convention used by the 3-4-1 inequality.
- `borelCaratheodory_sub_neg_logDeriv_riemannZeta_verticalRegion_of_one_le_re_of_affine_log_abs_add_three_re_le_half_radius`
  gives the signed centered oscillation version for
  `-logDeriv zeta(z) - (-logDeriv zeta(sigma+it))`.
- `borelCaratheodory_neg_logDeriv_regularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  applies the right-shifted Borel normalization to the zero-candidate regular
  part `-logDeriv zeta(w) + (w-rho)^(-1)`.
- `re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius`
  turns that normalized regular-part norm bound into the real zero-repulsion
  estimate `Re(-zeta'/zeta)(sigma+it) + 1/(sigma-beta) <= C log |t|`.
- `exists_re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  removes the separate regular-part center norm hypothesis in the simple-zero
  handoff by combining the fixed-margin `-logDeriv zeta` bound with the explicit
  same-height principal-part estimate
  `||((sigma+r+it)-(beta+it))^(-1)|| <= 1/r`.
- `exists_re_neg_logDeriv_riemannZeta_sigma_it_add_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  is the same center-discharged simple-zero handoff in the full complex-height
  `C log(||sigma+it|| + 3)` scale.
- `borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  is the multiplicity-aware version with regular part
  `-logDeriv zeta(w) + n * (w-rho)^(-1)`.
- `exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  removes the separate center norm hypothesis from the multiplicity-aware
  zero-repulsion handoff; the explicit center principal-part cost is
  `(n : Real) / r`, and `n >= 1` still recovers the unit principal conclusion.
- `differentiableOn_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_of_disk_right_half`
  proves differentiability of
  `-logDeriv zeta(w) + n * (w-(beta+it))^(-1)` on the right-shifted Borel
  disk from the standard right-shift geometry.  This removes the former
  explicit `hdiff` hypothesis using zeta nonvanishing on `Re(s) >= 1` and
  the fact that the candidate zero `beta+it` lies outside the shifted disk.
- `exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center_of_re_le`
  is the same multiplicity-aware additive zero-repulsion handoff with the
  differentiability hypothesis discharged automatically.  The remaining input
  is the local affine real-part bound for the regular part on the Borel disk.
- `exists_re_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_neg_inv_add_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  rewrites the additive output as
  `Re(-zeta'/zeta)(sigma+it) <= -1/(sigma-beta) + C log |t|`, matching the
  exact input shape consumed by the high-height zero-free-region closures.
- `right_shift_affine_majorant_pos`, `sigmaOf_log_borel_radius_affine_majorant_pos`,
  and the corresponding `..._of_pos_A` bridges discharge the Borel positivity
  side-condition `M > 0` from `0 < Are` and `0 <= Bre` on generic right-shift
  and canonical moving disks.  They do not prove the missing zeta-specific
  affine real-part bound; they remove a bookkeeping hypothesis from that local
  regular-part handoff.
- `affine_log_norm_add_three_pos`, `affine_log_abs_add_three_pos`, and the
  direct-disk, vertical-region, and right-shift `..._of_pos_A` Borel wrappers do
  the same positivity discharge for the half-radius Borel estimates on
  `logDeriv zeta`, `-logDeriv zeta`, and their centered oscillation variants in
  both `log(||sigma+it||+3)` and `log(|t|+3)` scales.  The required affine
  real-part bounds remain explicit hypotheses.
- `exists_re_neg_logDeriv_riemannZeta_sigma_it_right_shift_le_neg_inv_add_log_abs_of_affine_regularPart_re_le_half_radius_fixed_margin_center_of_re_le`
  is the same closure-input zero-repulsion bridge with differentiability
  discharged by the right-shift geometry.
- `exists_re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius_fixed_margin_center`
  is the full-height version of that multiplicity-aware center-discharged
  zero-repulsion handoff.
- `exists_borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius_fixed_margin_center`
  provides the analogous center-discharged Borel handoff in the positive
  local-factorization sign convention `logDeriv zeta(w) - n*(w-rho)^(-1)`.
- `re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_abs_of_affine_regularPart_re_le_half_radius`
  converts that multiplicity-aware bound to the same unit-principal
  zero-repulsion estimate using `n >= 1`.
- `borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_abs_of_affine_re_le_half_radius`
  is the positive-sign multiplicity-aware Borel handoff for
  `logDeriv zeta(w) - n * (w-rho)^(-1)`.
- `borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
  and
  `borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius`
  are the corresponding multiplicity-aware regular-part bridges in the full
  complex-height `C log(||sigma+it|| + 3)` scale.
- `exists_borelCaratheodory_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center`
  is the positive-sign center-discharged version in the same full-height scale;
  it combines the fixed-margin `logDeriv zeta` bound with the explicit
  `(n : Real) / r` principal-part center cost.
- `exists_borelCaratheodory_neg_logDeriv_multiplicityRegularPart_sigma_it_right_shift_le_log_norm_of_affine_re_le_half_radius_fixed_margin_center`
  is the signed center-discharged full-height version, using the fixed-margin
  `-logDeriv zeta` bound and the same `(n : Real) / r` center cost.
- `re_neg_logDeriv_riemannZeta_sigma_it_add_multiplicity_inv_right_shift_le_log_norm_of_affine_regularPart_re_le_half_radius`
  converts the signed multiplicity-aware regular-part norm bound into the
  full-height zero-repulsion estimate
  `Re(-zeta'/zeta)(sigma+it) + 1/(sigma-beta) <= C log(||sigma+it||+3)`.
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
- `jensen_circleAverage_log_norm_riemannZeta_sigma_it`,
  `jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it`,
  `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it`, and
  `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms`
  provide the same Jensen formulas directly on `sigma+I*t` disks without
  ambient vertical-region bookkeeping.
- `jensen_circleAverage_log_norm_riemannZeta_sigma_it_of_pos_radius`,
  `jensen_circleAverage_log_norm_logDeriv_riemannZeta_sigma_it_of_pos_radius`,
  `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_of_pos_radius`,
  and
  `jensen_circleAverage_log_norm_neg_logDeriv_riemannZeta_sigma_it_unsigned_terms_of_pos_radius`
  are the positive-radius versions of the direct Jensen formulas, with
  closed balls stated using radius `R` instead of `|R|`.

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
- `ZeroPairContributionNonnegative`,
  `zero_pair_contribution_nonnegative_of_reflection_condition`,
  `finite_zero_sum_nonnegative_of_pairing_condition`,
  `LaplacePairPositive`, and
  `finite_zero_sum_nonnegative_of_laplace_pair_positive`
  isolate a finite paired-zero nonnegativity skeleton for future
  Stechkin/Heath-Brown style zero detector arguments.
- `nontrivialZerosFinset_pair_sum_nonnegative`,
  `sum_nontrivialZerosFinset_pair_re`,
  `nontrivialZerosFinset_pair_contribution_eq_two_sum_re`, and
  `nontrivialZerosFinset_sum_re_nonnegative_of_pair_contribution_nonnegative`
  specialize the global pair-nonnegativity skeleton to `nontrivialZerosFinset T`
  and convert it into nonnegativity of the unpaired real-part sum.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive`
  specialize the paired-zero skeleton to the finite family of nontrivial zeta
  zeros up to bounded height, including the symmetry `rho -> 1 - rho` and the
  strip-local pair-positivity interface.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_laplace_pair_positive_one`
  specializes that finite paired-zero nonnegativity bridge to center `1`,
  discharging the critical-strip side condition from membership in
  `nontrivialZerosFinset`.
- `nontrivialZerosFinset_sum_re_nonnegative_of_laplace_pair_positive_one`
  converts the paired finite-zero nonnegativity into nonnegativity of the
  unpaired real-part sum using the `rho -> 1 - rho` reindexing identity.
- `nontrivialZerosFinset_average_re_nonnegative_of_pair_contribution_nonnegative`
  and
  `nontrivialZerosFinset_average_re_nonnegative_of_laplace_pair_positive_one`
  turn the same finite-zero real-part nonnegativity statements into normalized
  average-contribution forms over `nontrivialZerosFinset T`.
- `one_sub_mem_nontrivialZerosFinset_sdiff`,
  `sum_nontrivialZerosFinset_sdiff_pair_re`,
  `nontrivialZerosFinset_sdiff_pair_contribution_eq_two_sum_re`, and
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_pair_contribution_nonnegative`
  repeat the reflection/reindexing/nonnegativity layer for newly included
  zeros between two truncation heights
  `nontrivialZerosFinset U \ nontrivialZerosFinset T`, matching the blockwise
  zero contributions used by truncated explicit-formula arguments.
- `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive_one`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_laplace_pair_positive_one`,
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_pair_contribution_nonnegative`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_laplace_pair_positive_one`
  add the corresponding center-one Laplace-pair and normalized-average
  variants for those new-zero blocks.
- `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_laplace_pair_positive`
  generalizes the paired new-zero Laplace bridge to any caller-supplied real
  pairing center, with the strip membership supplied as an explicit hypothesis.
- `laplacePairPositive_of_re_nonnegative_on_strip`,
  `laplacePairPositive_one_of_re_nonnegative_on_critical_strip`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_re_nonnegative_on_critical_strip`,
  `nontrivialZerosFinset_average_re_nonnegative_of_re_nonnegative_on_critical_strip`,
  and the corresponding `sdiff` new-zero sum/average wrappers turn a stronger
  pointwise critical-strip real-part positivity certificate into the existing
  center-one pair-positive finite-zero machinery.  This gives concrete
  Stechkin/Heath-Brown-style kernels a direct supplier shape, but it does not
  prove positivity for any such analytic kernel by itself.
- `weightedKernelCombo`,
  `weightedKernelCombo_re_nonnegative_on_strip`,
  `laplacePairPositive_weightedKernelCombo`, and
  `laplacePairPositive_one_weightedKernelCombo`
  prove that finite nonnegative real-weighted combinations of kernels preserve
  pointwise strip positivity and strip-local pair positivity.
- `nontrivialZerosFinset_sum_re_nonnegative_of_weightedKernelCombo`,
  `nontrivialZerosFinset_average_re_nonnegative_of_weightedKernelCombo`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedKernelCombo`, and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedKernelCombo`
  specialize that generic weighted-combination closure to full finite-zero and
  new-zero contribution sums and averages.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_weightedKernelCombo`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_weightedKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedKernelCombo`, and
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedKernelCombo`
  expose the paired-sum and paired-average variants for the same finite
  nonnegative weighted combinations.
- `resolventLaplaceKernel`,
  `resolventLaplaceKernel_re_nonnegative_of_nonneg_re`,
  `resolventLaplaceKernel_re_nonnegative_on_critical_strip`,
  `laplacePairPositive_resolventLaplaceKernel`, and
  `laplacePairPositive_one_resolventLaplaceKernel`
  provide a concrete prototype supplier `z ↦ (a + z)⁻¹`: for every `a >= 0`
  its real part is nonnegative on the right half-plane, hence it supplies the
  center-one zero-pair positivity interface.
- `nontrivialZerosFinset_sum_re_nonnegative_of_resolventLaplaceKernel`,
  `nontrivialZerosFinset_average_re_nonnegative_of_resolventLaplaceKernel`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_resolventLaplaceKernel`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_resolventLaplaceKernel`
  specialize that prototype kernel to the full finite-zero and new-zero
  contribution sums and averages.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_resolventLaplaceKernel`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_resolventLaplaceKernel`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_resolventLaplaceKernel`,
  and
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_resolventLaplaceKernel`
  expose the paired contribution versions for the single resolvent/Laplace
  prototype.
- `symmetricResolventLaplaceKernel`,
  `symmetricResolventLaplaceKernel_re_nonnegative_on_strip`,
  `laplacePairPositive_symmetricResolventLaplaceKernel`, and
  `laplacePairPositive_one_symmetricResolventLaplaceKernel`
  package the center-reflected resolvent
  `z ↦ (a + z)^-1 + (a + center - z)^-1`; for `a >= 0` it has
  nonnegative real part across the centered strip and supplies the same
  center-one zero-pair positivity interface.
- `nontrivialZerosFinset_sum_re_nonnegative_of_symmetricResolventLaplaceKernel`,
  `nontrivialZerosFinset_average_re_nonnegative_of_symmetricResolventLaplaceKernel`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_symmetricResolventLaplaceKernel`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_symmetricResolventLaplaceKernel`
  specialize the center-one symmetric resolvent to full finite-zero and
  new-zero contribution sums and averages.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_symmetricResolventLaplaceKernel`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_symmetricResolventLaplaceKernel`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_symmetricResolventLaplaceKernel`,
  and
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_symmetricResolventLaplaceKernel`
  expose the paired contribution versions for the single symmetric kernel.
- `symmetricResolventLaplaceKernelCombo`,
  `symmetricResolventLaplaceKernelCombo_re_nonnegative_on_strip`,
  `laplacePairPositive_symmetricResolventLaplaceKernelCombo`, and
  `laplacePairPositive_one_symmetricResolventLaplaceKernelCombo`
  extend the center-reflected supplier to finite nonnegative combinations
  `sum k in K, w k * ((a k + z)^-1 + (a k + 1 - z)^-1)`.
- `dampedKernel`, `dampedKernel_pair_contribution_eq`,
  `laplacePairPositive_dampedKernel_of_pair_le`,
  `laplacePairPositive_one_dampedKernel_of_pair_le`,
  `nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel`, and
  `nontrivialZerosFinset_pair_average_nonnegative_of_dampedKernel`
  package the signed detector shape `F - kappa * G`: once the paired
  Stechkin-style inequality for `F` and `G` is supplied on the critical strip,
  the finite nontrivial-zero paired sum and average are nonnegative.
- `laplacePairPositive_dampedKernel_of_pair_nonneg_le`,
  `laplacePairPositive_one_dampedKernel_of_pair_nonneg_le`,
  `nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel_pair_nonneg_le`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_dampedKernel_pair_nonneg_le`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_pair_nonneg_le`,
  and
  `nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel_pair_nonneg_le`
  cover the common split input where the paired `G` contribution is already
  nonnegative and is bounded above by the paired `F` contribution.  Together
  with `kappa <= 1`, this discharges the signed damped-kernel positivity
  condition and yields full finite-zero paired and unpaired sum/average
  nonnegativity.
- `nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel`,
  `nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_dampedKernel`,
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_dampedKernel`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel`, and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel`
  extend the damped detector bridge from paired full finite-zero sums to
  unpaired sums/averages and to new-zero blocks
  `nontrivialZerosFinset U \ nontrivialZerosFinset T`.
- `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_dampedKernel_pair_nonneg_le`,
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_dampedKernel_pair_nonneg_le`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel_pair_nonneg_le`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel_pair_nonneg_le`
  provide the same pair-nonnegative dominated-kernel split input for new-zero
  `sdiff` paired and unpaired sums/averages.
- `laplacePairPositive_dampedKernel_self_of_le_one`,
  `laplacePairPositive_one_dampedKernel_self_of_le_one`,
  `dampedKernel_self_re_eq`,
  `dampedKernel_self_re_nonnegative_on_strip_of_le_one`,
  `dampedKernel_self_re_nonnegative_on_critical_strip_of_le_one`,
  `nontrivialZerosFinset_pair_sum_nonnegative_of_dampedKernel_self`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_dampedKernel_self`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_self`,
  `nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel_self`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_dampedKernel_self_re_nonnegative`,
  `nontrivialZerosFinset_average_re_nonnegative_of_dampedKernel_self_re_nonnegative`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_dampedKernel_self`,
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_dampedKernel_self`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel_self`, and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel_self`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_dampedKernel_self_re_nonnegative`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_dampedKernel_self_re_nonnegative`
  specialize the same damped detector package to `F - kappa * F` under
  `kappa <= 1`, including both pointwise real-part nonnegativity and
  pair-positive finite-zero consequences.
- `laplacePairPositive_weightedDampedKernelCombo_of_pair_le`,
  `laplacePairPositive_one_weightedDampedKernelCombo_of_pair_le`,
  `nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_weightedDampedKernelCombo`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo`,
  `nontrivialZerosFinset_average_re_nonnegative_of_weightedDampedKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedDampedKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedDampedKernelCombo`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedDampedKernelCombo`
  lift the signed detector bridge to finite nonnegative combinations of
  damped kernels.
- `laplacePairPositive_weightedDampedKernelCombo_self_of_le_one`,
  `laplacePairPositive_one_weightedDampedKernelCombo_self_of_le_one`,
  `weightedDampedKernelCombo_self_re_nonnegative_on_strip_of_le_one`,
  `weightedDampedKernelCombo_self_re_nonnegative_on_critical_strip_of_le_one`,
  `nontrivialZerosFinset_pair_sum_nonnegative_of_weightedDampedKernelCombo_self`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_weightedDampedKernelCombo_self`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self`,
  `nontrivialZerosFinset_average_re_nonnegative_of_weightedDampedKernelCombo_self`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative`,
  `nontrivialZerosFinset_average_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedDampedKernelCombo_self`,
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedDampedKernelCombo_self`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo_self`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedDampedKernelCombo_self`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedDampedKernelCombo_self_re_nonnegative`
  specialize the finite weighted damped-kernel package to the self-damped case
  `F k - (kappa k) * F k` under `kappa k <= 1`.
- `laplacePairPositive_one_weightedSelfDampedResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_pair_sum_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_average_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedSelfDampedResolventLaplaceKernelCombo`
  specialize the finite weighted self-damped package to concrete elementary
  resolvent/Laplace kernels `resolventLaplaceKernel (a k)`.
- `laplacePairPositive_one_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  `weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip`,
  `nontrivialZerosFinset_pair_sum_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_average_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative`,
  `nontrivialZerosFinset_average_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo_re_nonnegative`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_weightedSelfDampedAffineResolventLaplaceKernelCombo`,
  together with the corresponding `_re_nonnegative` new-zero sum and average
  facades, specialize the finite weighted self-damped package to concrete
  elementary affine resolvent/Laplace kernels
  `affineResolventLaplaceKernel (a k) (b k) (c k)` through either
  center-one pair positivity or pointwise critical-strip real-part
  nonnegativity.
- `nontrivialZerosFinset_sum_re_nonnegative_of_symmetricResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_average_re_nonnegative_of_symmetricResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_symmetricResolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_symmetricResolventLaplaceKernelCombo`
  specialize those finite symmetric combinations to full finite-zero and
  new-zero real-part sums and averages.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_symmetricResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_symmetricResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_symmetricResolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_symmetricResolventLaplaceKernelCombo`
  expose the paired contribution versions for finite symmetric combinations.
- `resolventLaplaceKernelCombo`,
  `resolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re`,
  `resolventLaplaceKernelCombo_re_nonnegative_on_critical_strip`,
  `laplacePairPositive_resolventLaplaceKernelCombo`, and
  `laplacePairPositive_one_resolventLaplaceKernelCombo`
  extend the same positivity supplier to finite nonnegative combinations
  `sum k in K, w k * (a k + z)^-1` with `w k >= 0` and `a k >= 0`.
- `nontrivialZerosFinset_sum_re_nonnegative_of_resolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_average_re_nonnegative_of_resolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_resolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_resolventLaplaceKernelCombo`
  specialize those finite nonnegative combinations to the full finite-zero and
  new-zero contribution sums and averages.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_resolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_resolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_resolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_resolventLaplaceKernelCombo`
  expose the paired contribution versions for those finite resolvent/Laplace
  combinations.
- `affineResolventLaplaceKernel`,
  `affineResolventLaplaceKernel_re_nonnegative_of_nonneg_re`,
  `affineResolventLaplaceKernel_re_nonnegative_on_critical_strip`,
  `laplacePairPositive_affineResolventLaplaceKernel`, and
  `laplacePairPositive_one_affineResolventLaplaceKernel`
  extend the prototype supplier to nonnegative real affine precomposition
  `z ↦ (a + (b + c * z))^-1`, with `a >= 0`, `b >= 0`, and `c >= 0`.
- `nontrivialZerosFinset_sum_re_nonnegative_of_affineResolventLaplaceKernel`,
  `nontrivialZerosFinset_average_re_nonnegative_of_affineResolventLaplaceKernel`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_affineResolventLaplaceKernel`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_affineResolventLaplaceKernel`
  specialize the single affine prototype kernel to the full finite-zero and
  new-zero contribution sums and averages.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_affineResolventLaplaceKernel`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_affineResolventLaplaceKernel`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_affineResolventLaplaceKernel`,
  and
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_affineResolventLaplaceKernel`
  expose the paired contribution versions for the single affine
  resolvent/Laplace prototype.
- `affineResolventLaplaceKernelCombo`,
  `affineResolventLaplaceKernelCombo_re_nonnegative_of_nonneg_re`,
  `affineResolventLaplaceKernelCombo_re_nonnegative_on_critical_strip`,
  `laplacePairPositive_affineResolventLaplaceKernelCombo`, and
  `laplacePairPositive_one_affineResolventLaplaceKernelCombo`
  extend the same supplier to finite nonnegative combinations of affine
  resolvent kernels.
- `nontrivialZerosFinset_sum_re_nonnegative_of_affineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_average_re_nonnegative_of_affineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_sum_re_nonnegative_of_affineResolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_average_re_nonnegative_of_affineResolventLaplaceKernelCombo`
  specialize those affine finite nonnegative combinations to the full
  finite-zero and new-zero contribution sums and averages.
- `nontrivialZerosFinset_pair_sum_nonnegative_of_affineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_pair_average_nonnegative_of_affineResolventLaplaceKernelCombo`,
  `nontrivialZerosFinset_sdiff_pair_sum_nonnegative_of_affineResolventLaplaceKernelCombo`,
  and
  `nontrivialZerosFinset_sdiff_pair_average_nonnegative_of_affineResolventLaplaceKernelCombo`
  expose the paired contribution versions for those finite affine
  resolvent/Laplace combinations.
- `norm_finiteNontrivialZeroSum_sub_le_new_zeros_sum_norm` and
  `norm_explicitFormulaApprox_sub_le_new_zeros_sum_norm`
  bound the finite zero-sum change and the corresponding
  `explicitFormulaApprox` change between two truncation heights by the summed
  norms of the newly included zero contributions, giving direct finite
  triangle-inequality handoffs for truncated explicit-formula bookkeeping.
- `finiteNontrivialZeroSum_eq_add_new_zeros`,
  `finiteNontrivialZeroSum_sub_eq_new_zeros`,
  `finiteNontrivialZeroSum_eq_of_sdiff_eq_empty`,
  `explicitFormulaApprox_eq_sub_new_zeros`,
  `explicitFormulaApprox_sub_eq_new_zeros`,
  `explicitFormulaApprox_sub_norm_eq_new_zeros`,
  `explicitFormulaApprox_add_new_zeros`, and
  `explicitFormulaApprox_eq_of_sdiff_eq_empty`
  expose the exact finite-truncation identities behind the norm bounds and
  eventual-empty-tail bridges.
- `explicitFormulaApprox_congr_finset`,
  `explicitFormulaApprox_congr_zero_sum`,
  `explicitFormulaApprox_congr_height`,
  `explicitFormulaApprox_eq_of_global_height_bound`,
  `explicitFormulaApprox_eventually_eq_of_global_height_bound`, and
  `explicitFormulaApprox_eq_of_neg`
  are public stability and congruence wrappers for changing truncation heights
  or degenerate negative-height truncations.
- `explicit_formula_von_mangoldt_of_eventually_eq` and
  `explicit_formula_von_mangoldt_of_eventually_exact`
  expose the basic stability entrypoint for the corrected explicit-formula
  target: once a future construction is eventually equal to the truncated
  approximation and tends to `ψ₀(x)`, or once the truncated approximation itself
  is eventually exactly `ψ₀(x)`, the target follows.
- `new_zero_contribution_sum_eventually_zero_of_eventually_sdiff_eq_empty`,
  `new_zero_contribution_sum_tendsto_zero_of_eventually_sdiff_eq_empty`,
  `new_zero_contribution_sum_norm_eventually_zero_of_eventually_sdiff_eq_empty`,
  `new_zero_contribution_sum_norm_tendsto_zero_of_eventually_sdiff_eq_empty`,
  `new_zero_inv_norm_tail_tendsto_zero_of_eventually_sdiff_eq_empty`, and
  `new_zero_card_tail_tendsto_zero_of_eventually_sdiff_eq_empty`
  turn an eventual empty new-zero block into eventual zero or convergence to
  zero for the finite zero contribution, sum-of-norms tail, reciprocal-norm
  tail, and zero-count tail used by truncated explicit-formula/RH-error
  bookkeeping.
- `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_tendsto_zero`
  turns a stable base truncation identity plus a vanishing new-zero
  contribution tail into the corrected height-truncated explicit-formula
  target.
- `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_norm_tendsto_zero`,
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_sum_norm_tendsto_zero`,
  `explicit_formula_von_mangoldt_of_base_and_eventually_new_zero_contribution_sum_norm_le`,
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_sum_norm_isBigO_tendsto_zero`,
  `explicit_formula_von_mangoldt_of_base_and_eventually_new_zero_contribution_norm_le`,
  and
  `explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_norm_isBigO_tendsto_zero`
  expose the same direct contribution-tail bridge in the norm, sum-of-norms,
  eventual-bound, and Big-O shapes normally produced by contour estimates.
- `RiemannPNT.API.explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_norm_isLittleO_one`
  and
  `RiemannPNT.API.explicit_formula_von_mangoldt_of_base_and_new_zero_contribution_sum_norm_isLittleO_one`
  expose the public little-o wrappers by converting `o(1)` to norm or
  sum-of-norms convergence.
- `explicit_formula_von_mangoldt_of_base_and_eventually_no_new_zeros_via_contribution_tail`
  is the degenerate eventual-empty-new-zero specialization routed through the
  contribution-tail convergence theorem.  It is a finite-tail sanity bridge,
  not a claim that zeta has only finitely many nontrivial zeros.
- `new_zero_contribution_sum_norm_eventually_zero_of_global_height_bound`,
  `new_zero_contribution_sum_norm_tendsto_zero_of_global_height_bound`, and
  `explicit_formula_von_mangoldt_of_base_and_global_height_bound_via_sum_norm_tail`
  specialize the same sum-of-norms tail bridge to a global nontrivial-zero
  height bound, again without adding a Perron-formula proof.
- `explicit_formula_von_mangoldt_of_global_height_bound_exact`,
  `explicitFormulaApprox_eq_chebyshevPsi0_of_global_height_bound`, and
  `explicit_formula_von_mangoldt_iff_global_height_bound_exact`
  record the stronger exact stability statement: under a global nontrivial-zero
  height bound, the corrected explicit-formula target is equivalent to equality
  at the stable base truncation.
- `NoZerosOnVerticalLine`
  is a reusable predicate for excluding zeta zeros on a fixed vertical line.
- `no_zeros_on_one_third_of_RH`
  proves that RH implies no zeta zeros on `Re(s) = 1/3`.
- `no_zeros_on_one_third_of_right_halfplane_two_thirds`
  reflects a zero-free statement on `Re(s) >= 2/3` to exclude zeros on
  `Re(s) = 1/3`.
- `no_zeros_on_reflected_line_of_right_halfplane`
  generalizes that bridge: right-half-plane zero-freeness in `Re(s) >= beta`
  excludes zeros on the reflected line `Re(s)=1-beta`.
- `exists_nontrivial_zero_on_one_third_iff_two_thirds`
  proves the nontrivial-zero existence equivalence between the reflected
  lines `Re(s) = 1/3` and `Re(s) = 2/3`.
- `not_exists_nontrivial_zero_on_line_of_no_zeros_on_vertical_line`,
  `no_zeros_on_vertical_line_of_not_exists_nontrivial_zero_on_line`, and
  `no_zeros_on_vertical_line_iff_not_exists_nontrivial_zero_on_line`
  identify critical-strip line zero-freeness with nonexistence of nontrivial
  zeros on that line.  The strip hypotheses exclude the trivial-zero lines.
- `exists_nontrivial_zero_on_line_iff_reflected` and
  `no_zeros_on_vertical_line_iff_reflected`
  generalize the same functional-equation reflection to arbitrary vertical
  lines `Re(s)=beta` and `Re(s)=1-beta` in the critical strip.
- `no_zeros_on_one_third_of_no_zeros_on_two_thirds` and
  `no_zeros_on_two_thirds_of_no_zeros_on_one_third`
  are the public specialized zero-free reflection wrappers for the two lines
  `Re(s)=1/3` and `Re(s)=2/3`.
- `NoZerosOnVerticalLineOneThirdOfStrongPNTError` and
  `no_zeros_on_one_third_of_strong_pnt_error_bridge`
  isolate the formal bridge from a future strong-PNT-error converse excluding
  `Re(s) = 2/3` zeros to a no-zero result on `Re(s) = 1/3`.
- `PsiPowerErrorBound`, `PsiPowerErrorBelowTwoThirds`, and
  `PsiPowerErrorBelowTwoThirdsExcludesLineTwoThirds`
  package a concrete Chebyshev-`psi` power-error version of that future
  converse-explicit-formula input.
- `psiPowerErrorBound_of_eventual_abs_bound`,
  `psiPowerErrorBound_of_pointwise`,
  `psiPowerErrorBelowLine_of_eventual_abs_bound`,
  `psiPowerErrorBelowLine_of_pointwise`,
  `psiPowerErrorBelowTwoThirds_of_eventual_abs_bound`, and
  `psiPowerErrorBelowTwoThirds_of_pointwise`
  turn eventual or pointwise estimates
  `|chebyshevPsi x - x| <= C * x^theta` into the corresponding power-error
  route predicates.
- `psiPowerErrorBelowLine_of_power_saving`,
  `psiPowerErrorBelowTwoThirds_of_power_saving`,
  `no_zeros_on_one_third_of_explicit_formula_converse_power_saving`, and
  `no_zeros_on_two_thirds_of_explicit_formula_converse_power_saving`
  package the commonly stated conditional input
  `psi(x)-x = O(x^(2/3-delta))` directly into the `1/3` and `2/3` line
  exclusions, still assuming the explicit-formula converse route.
- `no_zeros_on_one_third_of_psi_power_error_below_two_thirds_bridge`
  specializes the abstract strong-PNT-error bridge to the `psi` power-error
  interface.
- `PsiPowerErrorBelowLine`,
  `PsiPowerErrorBelowLineExcludesZerosRightOf`,
  `psiPowerErrorBelowLine_two_thirds_of_below_two_thirds`,
  `no_zeros_on_vertical_line_of_psi_power_error_bridge`,
  `no_zeros_on_reflected_line_of_psi_power_error_bridge`, and
  `no_zeros_on_one_third_of_general_psi_power_error_bridge`
  generalize the `2/3` psi-power-error bridge to arbitrary vertical lines in
  the critical strip, with the explicit-formula converse still kept as an
  assumption.
- `no_zeros_on_two_thirds_of_psi_power_error_below_two_thirds_bridge`
  records the direct `Re(s)=2/3` consequence of the concrete `psi` power-error
  converse, complementary to the reflected `Re(s)=1/3` wrapper.
- `ExplicitFormulaConversePowerTarget`,
  `no_zeros_on_vertical_line_of_explicit_formula_converse_power`,
  `no_zeros_on_reflected_line_of_explicit_formula_converse_power`, and
  `no_zeros_on_one_third_of_explicit_formula_converse_power`
  name the explicit-formula converse dependency directly, including the general
  reflected-line route `Re(s)=1-beta`, and specialize it to the reflected
  `Re(s)=1/3` route.
- `no_zeros_on_vertical_line_of_psi_power_error_bound_sub_delta_bridge`,
  `no_zeros_on_reflected_line_of_psi_power_error_bound_sub_delta_bridge`,
  `no_zeros_on_vertical_line_of_explicit_formula_converse_power_bound_sub_delta`,
  and
  `no_zeros_on_reflected_line_of_explicit_formula_converse_power_bound_sub_delta`
  package the concrete `PsiPowerErrorBound (beta - delta)` input directly into
  the same direct and reflected zero-free vertical-line conclusions, assuming
  the corresponding future zero-exclusion route at `beta`.
- `not_exists_nontrivial_zero_on_line_of_psi_power_error_bridge`,
  `not_exists_nontrivial_zero_on_reflected_line_of_psi_power_error_bridge`,
  `not_exists_nontrivial_zero_on_line_of_explicit_formula_converse_power_bound_sub_delta`,
  and
  `not_exists_nontrivial_zero_on_reflected_line_of_explicit_formula_converse_power_bound_sub_delta`
  are the existence-form versions of those conditional direct/reflected
  bridges.  They convert the route output from `NoZerosOnVerticalLine beta` to
  `¬ ∃ s, IsNontrivialZero s ∧ s.re = beta` or its reflected-line analogue,
  without changing the underlying explicit-formula/PNT-error assumptions.
- `psiPowerErrorBelowLineExcludesZerosRightOf_of_explicit_formula_converse_power`
  and
  `explicitFormulaConversePowerTarget_of_psiPowerErrorBelowLineExcludesZerosRightOf`
  keep the explicitly named explicit-formula converse target interchangeable
  with the underlying `psi`-power-error zero-exclusion interface.
- `not_psi_power_error_bound_sub_delta_of_exists_zero_right_of_bridge`,
  `not_psi_power_error_bound_sub_delta_of_exists_zero_right_of_explicit_formula_converse`,
  `not_psi_power_error_below_line_of_exists_zero_on_line_bridge`,
  `not_psi_power_error_below_line_of_exists_zero_on_line_explicit_formula_converse`,
  `not_psi_power_error_bound_sub_delta_of_exists_zero_on_line_bridge`,
  `not_psi_power_error_bound_sub_delta_of_exists_zero_on_line_explicit_formula_converse`,
  `not_psi_power_error_bound_sub_delta_of_exists_zero_on_reflected_line_bridge`,
  and
  `not_psi_power_error_bound_sub_delta_of_exists_zero_on_reflected_line_explicit_formula_converse`
  record the general power-saving contrapositives: under the future
  zero-exclusion route at boundary `beta`, a nontrivial zero on or to the
  right of `Re(s)=beta`, a zeta zero on the line `Re(s)=beta` inside the
  critical strip, or a zeta zero on the reflected line `Re(s)=1-beta`, rules
  out the corresponding below-line `psi` predicate or concrete
  `PsiPowerErrorBound (beta - delta)` whenever the stated strip and exponent
  hypotheses hold.
- `no_zeros_on_vertical_line_of_explicit_formula_converse_power_mono_error`
  and
  `no_zeros_on_reflected_line_of_explicit_formula_converse_power_mono_error`
  let an explicit-formula converse target at boundary `gamma` consume a
  stronger `psi` error already proved below any smaller boundary `beta <=
  gamma`.
- `no_zeros_on_vertical_line_of_psi_power_error_bridge_mono_error`
  and
  `no_zeros_on_reflected_line_of_psi_power_error_bridge_mono_error`
  provide the same monotone-error wrappers for the underlying
  `PsiPowerErrorBelowLineExcludesZerosRightOf` route interface, without first
  renaming it as an explicit-formula converse target.
- `no_zeros_on_vertical_line_of_psi_power_error_below_two_thirds_mono_bridge`
  and
  `no_zeros_on_reflected_line_of_psi_power_error_below_two_thirds_mono_bridge`
  specialize those route-interface wrappers to the concrete
  `PsiPowerErrorBelowTwoThirds` input for any boundary `gamma >= 2/3`.
- `no_zeros_on_two_thirds_of_explicit_formula_converse_power`,
  `no_zeros_on_one_third_of_explicit_formula_converse_power_below_two_thirds`,
  and
  `no_zeros_on_two_thirds_of_explicit_formula_converse_power_below_two_thirds`
  add direct and concrete `2/3` / `1/3` wrappers for the same conditional
  explicit-formula converse dependency.
- `not_psi_power_error_bound_two_thirds_sub_delta_of_exists_zero_on_one_third_bridge`
  and
  `not_psi_power_error_bound_two_thirds_sub_delta_of_exists_zero_on_one_third_explicit_formula_converse`
  record the contrapositive form: assuming the future `2/3` zero-exclusion
  route, an actual zero on `Re(s)=1/3` rules out the concrete
  `PsiPowerErrorBound (2/3 - delta)` for `0 < delta <= 2/3`.
- `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`
  gives the direct right-side-line consequence of the same conditional
  truncated explicit-formula route at `beta = 2/3`, before applying the
  reflected `1/3` bridge.
- `no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_below_two_thirds`
  and
  `no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds`
  are the public concrete `psi`-error wrappers for the same truncated route,
  using the already named `theta < 2/3` input.
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
- `finite_abs_le_inter_of_compl_mem_codiscrete`
- `critical_line_zeta_zero_bounded_finite_of_codiscrete`
- `hardyZ_zero_bounded_finite_of_codiscrete`
- `hardyZ_zero_codiscrete_iff_critical_line_zeta_zero_codiscrete`
- `critical_line_zeta_zero_codiscrete_of_hardyZ_zero_codiscrete`
- `hardyZ_zero_codiscrete_of_critical_line_zeta_zero_codiscrete`
- `critical_line_zeta_zero_codiscrete_of_finite`
- `hardyZ_zero_codiscrete_of_finite`
- `hardy_theorem_target_iff_abs_unbounded_of_codiscrete`
- `hardy_theorem_target_iff_unbounded_of_codiscrete`
- `hardy_theorem_target_iff_hardyZ_abs_unbounded_of_hardyZ_codiscrete`
- `hardy_zeros_abs_unbounded_of_hardy_theorem_target_of_codiscrete`
- `hardy_zeros_unbounded_of_hardy_theorem_target_of_codiscrete`
- `hardy_zeros_abs_unbounded_of_two_signed_moments_of_codiscrete`
- `hardy_zeros_unbounded_of_two_signed_moments_of_codiscrete`
- `exists_zero_on_critical_line_of_unbounded`
- `exists_zero_on_critical_line_of_abs_unbounded`
- `hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips`
- `hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips`
- `hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_codiscrete`
- `hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_codiscrete`
- `hardy_zeros_unbounded_iff_abs_unbounded`

These prove the local Hardy-Z setup and the equivalence between zeros of
`hardyZ` and zeros of `zeta` on the critical line, plus conditional bridges
from the signed-moment targets to Hardy's infinite and unbounded-height zero
interfaces.  They do not prove Hardy's theorem unconditionally; the moment
estimates needed for Hardy's theorem remain targets.  The codiscrete variants
show that a codiscrete-complement hypothesis for either the critical-line zeta
zero set or the Hardy-Z zero set is enough to supply the bounded-window
finiteness input in these conditional bridges.

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

As of `2026-07-05`, there are **22** mathematical target declarations:

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

For the approximate-functional-equation target, the proved wrappers include
`approximate_functional_equation_target_of`,
`eventually_approximate_functional_equation_of_target`,
`approximate_functional_equation_target_of_threshold_bounds`,
`approximate_functional_equation_target_of_threshold_bounds_le`,
`approximate_functional_equation_target_of_eventually_and_bounded_patch`,
`approximate_functional_equation_target_of_eventually_and_bounded_patch_le`,
and `approximate_functional_equation_target_iff_eventually_and_bounded_patch`.
The `_le` variants are constant-absorption bridges: they turn separate large-
and bounded-height constants into one chosen positive constant before closing
the global target.

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
- `PrimeNumberTheorem.ExplicitFormulaConversePowerTarget`
  route interface from a future power-scale `psi` error converse to exclusion
  of nontrivial zeros on or to the right of a vertical line.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedTarget`
  real-statement truncated explicit-formula interface.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.ExplicitFormulaTruncatedConverseRoute`
  route interface from a future uniform truncated explicit formula plus
  oscillation/converse argument to `ExplicitFormulaConversePowerTarget`.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route`
  repackages the truncated route and a future uniform truncated explicit
  formula proof as the right-half zero-exclusion route interface
  `PsiPowerErrorBelowLineExcludesZerosRightOf`.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_below_two_thirds`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`,
  and
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_below_two_thirds`
  compose the truncated route with the existing power-error converse bridges
  inside the truncated explicit-formula module itself.  The same module also
  exposes
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_mono_error`
  and
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`,
  which feed a smaller-boundary `psi` error into a larger-boundary truncated
  route before applying direct or reflected zero exclusion.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_mono_error`
  and
  `PrimeNumberTheorem.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`
  are the corresponding existence-form facades: the same conditional
  monotone-error route rules out nontrivial zeros on `Re(s)=gamma` and on the
  reflected line `Re(s)=1-gamma`.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`,
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`,
  and
  `PrimeNumberTheorem.ExplicitFormulaTruncated.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_saving`
  are the direct truncated-route facades for an `O(x^(beta-delta))` input,
  including the concrete `2/3` and reflected `1/3` specializations.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving`
  and
  `PrimeNumberTheorem.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`
  are the corresponding existence-form facades for the direct power-saving
  route, ruling out nontrivial zeros on `Re(s)=beta` and `Re(s)=1-beta`.
- `PrimeNumberTheorem.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`
  and
  `PrimeNumberTheorem.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_one_third_of_truncated_explicit_formula_converse_route_saving`
  are the concrete `2/3` and reflected `1/3` existence-form specializations.
- `RiemannPNT.API.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`
  public bridge from a truncated explicit-formula route at any `0 < beta < 1`
  and a `psi` power saving below `beta` to no zeros on the reflected line
  `Re(s)=1-beta`.
- `RiemannPNT.API.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`
  public bridge from the same conditional route at `beta = 2/3` to no zeros on
  the right-side line `Re(s)=2/3`.
- `RiemannPNT.API.ExplicitFormulaTruncated.psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route`
  and
  `RiemannPNT.API.psiPowerErrorBelowLineExcludesZerosRightOf_of_truncated_route`
  expose the same truncated-route-to-right-half-route conversion in the public
  API.
- `RiemannPNT.API.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_below_two_thirds`
  and
  `RiemannPNT.API.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds`
  public concrete wrappers for the same conditional truncated route when the
  `psi` error is stated as `PsiPowerErrorBelowTwoThirds`.
- `RiemannPNT.API.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_below_two_thirds`
  public concrete reflected-line wrapper for any `beta >= 2/3`, using
  `PsiPowerErrorBelowTwoThirds` and the same conditional truncated route.
- `RiemannPNT.API.no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_mono_error`
  and
  `RiemannPNT.API.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`
  public monotone-error wrappers for the conditional truncated route: a `psi`
  power saving below `beta` with `beta <= gamma` feeds a route at `gamma`,
  excluding zeros on `Re(s)=gamma` and on the reflected line `Re(s)=1-gamma`.
- `RiemannPNT.API.not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_mono_error`
  and
  `RiemannPNT.API.not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`
  expose the same monotone-error truncated route in existence form at the
  top-level public API.
- `RiemannPNT.API.no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving`,
  `RiemannPNT.API.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`,
  `RiemannPNT.API.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`,
  and
  `RiemannPNT.API.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_saving`
  expose the same direct `O(x^(beta-delta))` truncated-route wrappers at the
  top-level public API.
- `RiemannPNT.API.not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving`
  and
  `RiemannPNT.API.not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`
  expose the direct power-saving route in existence form at the top-level
  public API.
- `RiemannPNT.API.not_exists_nontrivial_zero_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`
  and
  `RiemannPNT.API.not_exists_nontrivial_zero_on_one_third_of_truncated_explicit_formula_converse_route_saving`
  expose the concrete `2/3` and reflected `1/3` existence-form specializations
  at the top-level public API.
- `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route`,
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_below_two_thirds`,
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route`,
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_below_two_thirds`,
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route`,
  and
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_below_two_thirds`
  expose the same bridges in the nested public namespace next to the truncated
  explicit-formula target.  The nested namespace also exposes the two monotone
  wrappers
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_mono_error`
  and
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`,
  the two existence-form monotone wrappers
  `RiemannPNT.API.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_mono_error`
  and
  `RiemannPNT.API.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_mono_error`,
  plus the four direct power-saving wrappers
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_vertical_line_of_truncated_explicit_formula_converse_route_saving`,
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`,
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`, and
  `RiemannPNT.API.ExplicitFormulaTruncated.no_zeros_on_one_third_of_truncated_explicit_formula_converse_route_saving`.
  It also exposes the two direct power-saving existence facades
  `RiemannPNT.API.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_line_of_truncated_explicit_formula_converse_route_saving`
  and
  `RiemannPNT.API.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_reflected_line_of_truncated_explicit_formula_converse_route_saving`.
  The nested namespace also exposes their concrete `2/3` and `1/3`
  specializations
  `RiemannPNT.API.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_two_thirds_of_truncated_explicit_formula_converse_route_saving`
  and
  `RiemannPNT.API.ExplicitFormulaTruncated.not_exists_nontrivial_zero_on_one_third_of_truncated_explicit_formula_converse_route_saving`.
- `RiemannPNT.API.not_psi_power_error_below_line_of_exists_zero_right_of_bridge`
  and its explicit-formula, general `beta-delta`, reflected-line, and
  below-`2/3` variants are contrapositive facades: under the same future
  zero-exclusion bridge, an actual zero at or to the right of the boundary, or
  on the reflected line, rules out the corresponding `psi` power saving.
- `RiemannExplorer.Conrey40.conrey_40_percent_zeros_on_critical_line_target`
  alias interface to `KnownResults.conrey_40_percent_zeros_on_critical_line_target`.
- `MathlibAux.rectangleIntegral_meromorphic_eq_residue_sum`
  real-statement interface for missing rectangle contour/residue infrastructure.
  The file also proves the constant-function sanity checks
  `MathlibAux.rectangleBoundaryIntegral_const`,
  `MathlibAux.rectangleIntegral_const`, and
  `MathlibAux.rectangleIntegral_const_zero`, exposed through matching
  `RiemannPNT.API` aliases.  These are ordinary theorem-level checks for the
  holomorphic empty-pole case; they do not discharge the general meromorphic
  residue theorem needed for Perron's formula.

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

The project-local contribution is the assembly and formal proof of the
intermediate zeta-function infrastructure listed above, especially the
real-part logarithmic-derivative series, the 3-4-1 combination, compact
zero-free strip, and residue-scale inequalities.  Its external novelty should
be assessed only after the separate SOTA comparison described in the README.

### `PrimeNumberTheorem/ExplicitFormulaAux.lean`

Support-level verified declarations:

- `goodHeight_iff_no_zero_at_height`
  proves that a truncation height is good exactly when no nontrivial zero has
  `|Im rho| = T`.
- `not_goodHeight_iff_exists_zero_at_height`
  gives the negated form used when choosing or excluding bad contour heights.
- `nontrivial_zero_mem_self_height`
  places each nontrivial zero in the self-height truncation
  `finiteNontrivialZeroSum (|rho.im| + 1)`.
- `zeroMultiplicity_eq_one_of_mem` and `zeroMultiplicity_eq_zero_of_not_mem`
  prove the current finset-based auxiliary multiplicity is `1` or `0`
  according to membership in the self-height truncation.  This is support
  bookkeeping for the truncated explicit-formula target, not a proof of the
  analytic zero-order theory.
- `mem_finiteTrivialZeroSum_iff`,
  `finiteTrivialZeroSum_im_eq_zero_of_mem`,
  `finiteTrivialZeroSum_re_lt_zero_of_mem`, and
  `finiteTrivialZeroSum_card_le`
  characterize the retained finite trivial zeros as the displayed negative
  even integers, show they lie on the real axis with negative real part, and
  bound the truncation size by `Nat.floor (T / 2)`.
- `finiteTrivialZeroSum_ne_zero_of_mem`,
  `finiteTrivialZeroSum_abs_im_eq_zero_of_mem`, and
  `finiteTrivialZeroSum_not_isNontrivialZero_of_mem`
  add denominator safety, absolute-height normalization, and disjointness from
  the nontrivial-zero strip predicate for retained trivial zeros.
- `finiteTrivialZeroSum_re_le_neg_two_of_mem`,
  `finiteTrivialZeroSum_two_le_norm_of_mem`, and
  `finiteTrivialZeroSum_inv_norm_le_half_of_mem`
  package the retained trivial-zero support as the norm and reciprocal-norm
  bounds needed for later `x^s / s` estimates.
- `norm_trivial_zero_contribution_le_half_rpow_re`
  bounds each retained trivial-zero contribution by
  `(1 / 2) * x ^ s.re` for `x > 0`.  This is a single-term estimate only, not
  the infinite trivial-zero correction.
- `finiteTrivialZeroSum_rpow_re_le_rpow_neg_two_of_mem`
  records the standalone `x >= 1` power decay comparison
  `x ^ s.re <= x ^ (-2)` for every retained trivial zero.
- `norm_trivial_zero_contribution_le_half_rpow_neg_two`
  specializes the same single-term estimate to `x >= 1`, using the retained
  trivial-zero fact `s.re <= -2` to bound the amplitude by
  `(1 / 2) * x ^ (-2)`.
- `norm_finiteTrivialZeroSum_contribution_le_half_sum_rpow_re`
  sums the preceding single-term estimate over the retained finite trivial-zero
  truncation.  This is still a finite-truncation estimate, not the infinite
  trivial-zero correction.
- `norm_finiteTrivialZeroSum_contribution_le_card_mul_half_rpow_neg_two`
  gives the coarser `x >= 1` finite-sum bound using only the truncation
  cardinality and the first trivial-zero amplitude `x^(-2)`.
- `norm_finiteTrivialZeroSum_contribution_le_floor_mul_half_rpow_neg_two`
  composes that cardinality bound with
  `finiteTrivialZeroSum_card_le`, replacing the finset cardinality by the
  explicit cutoff `Nat.floor (T / 2)`.
- `norm_finiteTrivialZeroSum_contribution_le_height_mul_half_rpow_neg_two`
  weakens the floor cutoff to the continuous nonnegative height scale
  `(T / 2) * ((1 / 2) * x ^ (-2))`, which is easier to compose with later
  contour-error estimates.
- `RiemannPNT.API.ExplicitFormulaTruncated.ExplicitFormulaTruncatedTarget`
  and `RiemannPNT.API.ExplicitFormulaTruncated.explicitFormulaTruncated_of`
  expose the typed truncated explicit-formula target and its conditional
  repackaging lemma through the public API.  They remain target infrastructure,
  not an unconditional proof of the explicit formula.

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
