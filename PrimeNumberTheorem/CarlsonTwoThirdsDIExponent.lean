import PrimeNumberTheorem.CarlsonLengthMinimax

/-!
# Exact exponent ledger for the Deshouillers--Iwaniec Carlson route

This file contains rational arithmetic only.  In particular, it does not
assert the Deshouillers--Iwaniec mollified mean-square estimate or the
Carlson local-to-global analytic argument.
-/

namespace PrimeNumberTheorem

noncomputable section

/-- The mollifier-length exponent used for the explicit DI specialization. -/
def diLengthExponent : ℝ := 57 / 100

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

theorem di_interpolation_weight_eq :
    diInterpolationWeight = 1 / 5997 := by
  norm_num [diInterpolationWeight, diRightBoundary]

/-- The mixed DI term `T^(1/2) X^(7/8)` is power-smaller than `T` at
`x = 57/100`. -/
theorem di_critical_mixed_term_lt_one :
    1 / 2 + (7 / 8) * diLengthExponent = 799 / 800 ∧
      1 / 2 + (7 / 8) * diLengthExponent < 1 := by
  norm_num [diLengthExponent]

/-- The DI term `X^(5/3)` is also power-smaller than `T`. -/
theorem di_critical_long_term_lt_one :
    (5 / 3) * diLengthExponent = 19 / 20 ∧
      (5 / 3) * diLengthExponent < 1 := by
  norm_num [diLengthExponent]

theorem di_interpolated_exponent_eq :
    diInterpolatedExponent = 12146849 / 14992500 := by
  norm_num [diInterpolatedExponent]

/-- The exact slack between the chosen target and the interpolated exponent. -/
theorem di_interpolated_exponent_lt_target :
    diTargetExponent - diInterpolatedExponent = 409373 / 719640000 ∧
      diInterpolatedExponent < diTargetExponent := by
  norm_num [diTargetExponent, diInterpolatedExponent]

/-- The unchanged positive lower endpoint at `x = 57/100` remains below the
chosen target exponent. -/
theorem di_lower_endpoint_lt_target :
    carlsonLowerEndpointExponent (2 / 3) diLengthExponent = 81 / 100 ∧
      diTargetExponent -
          carlsonLowerEndpointExponent (2 / 3) diLengthExponent = 11 / 14400 ∧
      carlsonLowerEndpointExponent (2 / 3) diLengthExponent < diTargetExponent := by
  norm_num [carlsonLowerEndpointExponent, diLengthExponent, diTargetExponent]

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
