import PrimeNumberTheorem.CarlsonHalfRangeAuxiliaryWindow

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem PrimeNumberTheorem.CarlsonZeroDensity

example : halfRangeTargetExponent -
    (1 - (12 / 5 : ℝ) * ((halfRangeAuxiliaryLeft - 1 / 2) / (4 - 1 / 2))) =
      1909 / 3150000 := halfRangeAuxiliary_exact_slack

example {x : ℝ} (hx : x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight) :
    x ∈ Icc (1 / 2 : ℝ) (2 / 3) ∧ (1 / 20000 : ℝ) ≤ 2 / 3 - x ∧
      1 - (12 / 5 : ℝ) * ((x - 1 / 2) / (4 - 1 / 2)) < halfRangeTargetExponent :=
  halfRangeAuxiliary_bounds hx

example : ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
    ∀ x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
    ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
      IntervalIntegrable (fun t : ℝ =>
        ‖twoScaleMollifiedZetaError (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ))‖ ^ 2) volume u v ∧
      (∫ t in u..v,
        ‖twoScaleMollifiedZetaError (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ))‖ ^ 2) ≤
        K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 :=
  exists_eventually_halfRange_auxiliary_subinterval_moment_le

#print axioms halfRangeAuxiliary_exact_slack
#print axioms halfRangeAuxiliary_bounds
#print axioms exists_eventually_halfRange_auxiliary_subinterval_moment_le
