import PrimeNumberTheorem.CarlsonLengthMinimax

/-!
# Exact exponent ledger for a two-scale Deshouillers--Iwaniec Carlson route

This file contains rational arithmetic only.  In particular, it does not
assert the Deshouillers--Iwaniec mollified mean-square estimate or the
Carlson local-to-global analytic argument.
-/

namespace PrimeNumberTheorem

noncomputable section

/-- The exponent of the exact Mobius core.  Exact reciprocal cancellation up
to this length is what supplies power decay on the far-right boundary. -/
def diCoreExponent : ℝ := 57 / 100

/-- The exponent of the tapered outer mollifier.  It is strictly below the
published Conrey--Deshouillers--Iwaniec `4/7` range. -/
def diOuterExponent : ℝ := 571 / 1000

/-- The far-right boundary in the L2 three-lines interpolation. -/
def diRightBoundary : ℝ := 1000

/-- The explicit epsilon reserved for the published mean-square estimate. -/
def diEpsilon : ℝ := 1 / 10000

/-- The interpolation weight of the critical boundary at `σ = 2/3`. -/
def diInterpolationWeight : ℝ :=
  ((2 / 3 : ℝ) - 1 / 2) / (diRightBoundary - 1 / 2)

/-- The exponent produced by the fully normalized interpolation ledger. -/
def diInterpolatedExponent : ℝ :=
  1 - 18981 / 99950 + 1499 / 14992500

/-- A convenient rational exponent below Carlson's `8/9`. -/
def diTargetExponent : ℝ := 467 / 576

/-- The explicit saving from `8/9` represented by `diTargetExponent`. -/
def diDelta : ℝ := 5 / 64

/-! ## Short-strip specialization

The endpoint `R = 4` is already covered by the concrete polynomial-growth
and Gaussian `L²` infrastructure.  It gives a weaker but still explicit
power saving, avoiding any need to extend those analytic bounds to `R = 1000`
before closing the first unconditional formal certificate. -/

/-- The already formalized right boundary used by the short-strip route. -/
def diShortRightBoundary : ℝ := 4

/-- Three-lines weight at `sigma = 2/3` for the strip `[1/2, 4]`. -/
def diShortInterpolationWeight : ℝ :=
  ((2 / 3 : ℝ) - 1 / 2) / (diShortRightBoundary - 1 / 2)

/-- Exact short-strip exponent obtained from the normalized interpolation
formula, including the critical-boundary epsilon reserve. -/
def diShortInterpolatedExponent : ℝ :=
  (1 - diShortInterpolationWeight) * (1 + diEpsilon) +
    diShortInterpolationWeight *
      (1 + 2 * diCoreExponent * (1 - diShortRightBoundary))

/-- Convenient target exponent for the short-strip route. -/
def diShortTargetExponent : ℝ := 151 / 180

/-- Explicit Carlson saving supplied by the short-strip target. -/
def diShortDelta : ℝ := 1 / 20

theorem di_short_interpolation_weight_eq :
    diShortInterpolationWeight = 1 / 21 := by
  norm_num [diShortInterpolationWeight, diShortRightBoundary]

theorem di_short_interpolated_exponent_eq :
    diShortInterpolatedExponent = 8791 / 10500 := by
  norm_num [diShortInterpolatedExponent, diShortInterpolationWeight,
    diShortRightBoundary, diCoreExponent, diEpsilon]

/-- Exact positive slack between the short-strip interpolation output and
the target `8/9 - 1/20`. -/
theorem di_short_interpolated_exponent_lt_target :
    diShortTargetExponent - diShortInterpolatedExponent = 13 / 7875 ∧
      diShortInterpolatedExponent < diShortTargetExponent := by
  norm_num [diShortTargetExponent, diShortInterpolatedExponent,
    diShortInterpolationWeight, diShortRightBoundary, diCoreExponent,
    diEpsilon]

theorem di_short_target_eq_carlson_sub_delta :
    diShortTargetExponent = 8 / 9 - diShortDelta := by
  norm_num [diShortTargetExponent, diShortDelta]

/-- The `beta = 14/17` contradiction margin left by the short-strip saving. -/
theorem di_short_fourteenSeventeenths_margin :
    (3 / 17) * diShortDelta = 3 / 340 := by
  norm_num [diShortDelta]

/-- Exact separated-density beta threshold for the short-strip target. -/
theorem di_short_separated_threshold_eq :
    (4 / 3 + 8 / 9 + diShortTargetExponent) /
        (2 + 8 / 9 + diShortTargetExponent) = 551 / 671 := by
  norm_num [diShortTargetExponent]

theorem di_interpolation_weight_eq :
    diInterpolationWeight = 1 / 5997 := by
  norm_num [diInterpolationWeight, diRightBoundary]

/-- The core is shorter than the outer taper, and the outer taper lies in the
published `theta < 4/7` range.  This arithmetic statement does not assert that
the published theorem already covers the required two-scale weight. -/
theorem di_twoScale_length_range :
    diCoreExponent < diOuterExponent ∧ diOuterExponent < 4 / 7 := by
  norm_num [diCoreExponent, diOuterExponent]

theorem di_interpolated_exponent_eq :
    diInterpolatedExponent = 12146849 / 14992500 := by
  norm_num [diInterpolatedExponent]

/-- The exact slack between the chosen target and the interpolated exponent. -/
theorem di_interpolated_exponent_lt_target :
    diTargetExponent - diInterpolatedExponent = 409373 / 719640000 ∧
      diInterpolatedExponent < diTargetExponent := by
  norm_num [diTargetExponent, diInterpolatedExponent]

/-- The far-right interpolation exponent controlled by the exact core remains
below the chosen target exponent. -/
theorem di_lower_endpoint_lt_target :
    carlsonLowerEndpointExponent (2 / 3) diCoreExponent = 81 / 100 ∧
      diTargetExponent -
          carlsonLowerEndpointExponent (2 / 3) diCoreExponent = 11 / 14400 ∧
      carlsonLowerEndpointExponent (2 / 3) diCoreExponent < diTargetExponent := by
  norm_num [carlsonLowerEndpointExponent, diCoreExponent, diTargetExponent]

theorem di_target_eq_carlson_sub_delta :
    diTargetExponent = 8 / 9 - diDelta := by
  norm_num [diTargetExponent, diDelta]

/-- If the terminal density exponent saves `diDelta` while forcing still uses
`8/9`, the direct `β=14/17` margin is `3*diDelta/17`. -/
theorem di_fourteenSeventeenths_margin :
    (3 / 17) * diDelta = 15 / 1088 := by
  norm_num [diDelta]

/-- The exact beta threshold for `σ=2/3`, forcing exponent `8/9`, and
density exponent `467/576`. -/
theorem di_separated_threshold_eq :
    (4 / 3 + 8 / 9 + diTargetExponent) /
        (2 + 8 / 9 + diTargetExponent) = 1747 / 2131 := by
  norm_num [diTargetExponent]

/-- Direct exponent gap at `β=14/17`; this is the quantity available for
absorbing further forcing losses. -/
theorem di_direct_gap_at_fourteen_seventeenths :
    2 * (14 / 17 - 2 / 3) -
        (1 - 14 / 17) * (8 / 9 + diTargetExponent) = 15 / 1088 := by
  norm_num [diTargetExponent]

end

end PrimeNumberTheorem
