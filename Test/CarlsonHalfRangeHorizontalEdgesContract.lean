import PrimeNumberTheorem.CarlsonHalfRangeHorizontalEdges

set_option autoImplicit false

open Complex Filter MeasureTheory Set
open scoped Interval
open PrimeNumberTheorem.CarlsonZeroDensity

example {Y0 Y1 : ℕ} {x t M : ℝ} (hx0 : 0 < x) (hx4 : x ≤ 4) (hM : 0 ≤ M)
    (hne : ∀ w ∈ Icc x 4,
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((w : ℂ) + (t : ℂ) * I) ≠ 0)
    (hbound : ∀ w ∈ Icc x 4,
      ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((w : ℂ) + (t : ℂ) * I)‖ ≤ M) :
    IntervalIntegrable (fun w : ℝ => (w - x) *
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((w : ℂ) + (t : ℂ) * I)).im)
      volume x 4 ∧
    |∫ w in x..4, (w - x) *
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((w : ℂ) + (t : ℂ) * I)).im| ≤
      (4 - x) ^ 2 * M :=
  integral_twoScale_horizontal_weighted_bound hx0 hx4 hM hne hbound

example : ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
    let V := 10 * U / 21
    let H := regularizedTwoScaleCarlsonZeroDetector (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
    ∃ u ∈ Icc (U - 1) U, ∃ v ∈ Icc (9 * U / 8) (9 * U / 8 + 1),
      2 * V ≤ u ∧ v ≤ 5 * V / 2 ∧ u ≤ v ∧
      (∀ w ∈ Icc halfRangeAuxiliaryLeft 4, H ((w : ℂ) + (u : ℂ) * I) ≠ 0) ∧
      (∀ w ∈ Icc halfRangeAuxiliaryLeft 4, H ((w : ℂ) + (v : ℂ) * I) ≠ 0) ∧
      ∀ x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
        IntervalIntegrable (fun w : ℝ => (w - x) * (logDeriv H ((w : ℂ) + (u : ℂ) * I)).im)
          volume x 4 ∧
        IntervalIntegrable (fun w : ℝ => (w - x) * (logDeriv H ((w : ℂ) + (v : ℂ) * I)).im)
          volume x 4 ∧
        |∫ w in x..4, (w - x) * (logDeriv H ((w : ℂ) + (u : ℂ) * I)).im| +
          |∫ w in x..4, (w - x) * (logDeriv H ((w : ℂ) + (v : ℂ) * I)).im| ≤
          K * (1 + Real.log U) ^ 2 :=
  exists_eventually_halfRange_horizontalEdges

#print axioms integral_twoScale_horizontal_weighted_bound
#print axioms exists_eventually_halfRange_horizontalEdges
