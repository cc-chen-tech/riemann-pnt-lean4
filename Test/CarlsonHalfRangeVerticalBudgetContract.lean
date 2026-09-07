import PrimeNumberTheorem.CarlsonHalfRangeVerticalBudget

set_option autoImplicit false

open Complex Filter MeasureTheory Set
open scoped Interval
open PrimeNumberTheorem.CarlsonZeroDensity

example : ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
    let G := regularizedTwoScaleCarlsonZeroDetector (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
    ∃ x ∈ Ioo halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
      (1 / 20000 : ℝ) ≤ 2 / 3 - x ∧
      (∀ t ∈ Icc (2 * V) (5 * V / 2), G ((x : ℂ) + I * (t : ℂ)) ≠ 0) ∧
      (∀ t : ℝ, G ((4 : ℂ) + I * (t : ℂ)) ≠ 0) ∧
      ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
        (4 - x) * (∫ t in u..v, (logDeriv G ((4 : ℂ) + I * (t : ℂ))).re) +
          (∫ t in u..v, Real.log ‖G ((x : ℂ) + I * (t : ℂ))‖) -
          (∫ t in u..v, Real.log ‖G ((4 : ℂ) + I * (t : ℂ))‖) ≤
          K * V ^ PrimeNumberTheorem.halfRangeTargetExponent * (1 + Real.log V) ^ 6 :=
  exists_eventually_halfRange_selectedVerticalBudget

#print axioms exists_eventually_halfRange_selectedVerticalBudget
