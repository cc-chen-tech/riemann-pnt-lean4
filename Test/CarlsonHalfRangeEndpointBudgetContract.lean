import PrimeNumberTheorem.CarlsonHalfRangeEndpointBudget

open Filter
open PrimeNumberTheorem.CarlsonZeroDensity

example {C : ℝ} (hC : 0 ≤ C) : ∀ᶠ V : ℝ in atTop,
    let Y0 := halfRangeCoreCutoff V
    let Y1 := halfRangeOuterCutoff V
    let Delta := 16 * V ^ (19 / 20 : ℝ)
    let B := C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6
    carlsonConreyCriticalEndpointBound Delta Y0 Y1 B B ≤
      halfRangeCriticalConstant C * V ^ (19 / 20 : ℝ) * (1 + Real.log V) ^ 6 ∧
    carlsonConreyRightEndpointBound Delta Y0 ≤
      halfRangeRightConstant * V ^ (-29 / 20 : ℝ) :=
  eventually_halfRange_endpoint_bounds hC

example {C : ℝ} (hC : 0 ≤ C) : 0 < halfRangeCriticalConstant C :=
  halfRangeCriticalConstant_pos hC

example : 0 < halfRangeRightConstant := halfRangeRightConstant_pos

#print axioms eventually_halfRange_endpoint_bounds
#print axioms halfRangeCriticalConstant_pos
#print axioms halfRangeRightConstant_pos
