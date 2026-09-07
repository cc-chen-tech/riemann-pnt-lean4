import PrimeNumberTheorem.CarlsonHalfRangeParameters

open Filter
open PrimeNumberTheorem.CarlsonZeroDensity

-- Floors must preserve a nonempty plateau and uniformly bounded
-- reconstruction coefficients; these are not arbitrary integer lengths.
example : ∀ᶠ V : ℝ in atTop,
    let Y0 := halfRangeCoreCutoff V
    let Y1 := halfRangeOuterCutoff V
    1 < V ∧ 2 ≤ Y0 ∧ Y0 < Y1 ∧
    (Y0 : ℝ) ≤ V ^ (2 / 5 : ℝ) ∧ (Y1 : ℝ) ≤ V ^ (9 / 20 : ℝ) ∧
    V ^ (2 / 5 : ℝ) / 2 ≤ (Y0 : ℝ) ∧
    Real.log V / 40 ≤ Real.log ((Y1 : ℝ) / (Y0 : ℝ)) ∧
    0 ≤ conreyOuterMultiplier Y0 Y1 ∧ conreyOuterMultiplier Y0 Y1 ≤ 18 ∧
    0 ≤ conreyInnerMultiplier Y0 Y1 ∧ conreyInnerMultiplier Y0 Y1 ≤ 16 :=
  eventually_halfRangeCutoff_conditions

#print axioms eventually_halfRangeCutoff_conditions
