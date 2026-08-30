import PrimeNumberTheorem.CarlsonTwoScaleRegularizedEdges

set_option autoImplicit false

open Complex MeasureTheory Set
open scoped Interval
open PrimeNumberTheorem.CarlsonZeroDensity

example {Y0 Y1 : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hne : twoScaleCarlsonZeroDetector Y0 Y1 s ≠ 0) :
    Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 s‖ =
      2 * Real.log ‖s - 1‖ + Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 s‖ :=
  log_norm_regularizedTwoScale_eq hs0 hs1 hne

example {Y0 Y1 : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hne : twoScaleCarlsonZeroDetector Y0 Y1 s ≠ 0) :
    logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) s =
      2 * (s - 1)⁻¹ + logDeriv (twoScaleCarlsonZeroDetector Y0 Y1) s :=
  logDeriv_regularizedTwoScale_eq hs0 hs1 hne

example {Y0 Y1 : ℕ} {x u v : ℝ} (hx0 : x ≠ 0) (hx1 : x ≠ 1)
    (hne : ∀ t ∈ uIcc u v, twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0) :
    IntervalIntegrable (fun t : ℝ => Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1
      ((x : ℂ) + I * (t : ℂ))‖) volume u v ∧
    (∫ t in u..v, Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) =
      2 * (∫ t in u..v, Real.log ‖(x : ℂ) + I * (t : ℂ) - 1‖) +
        ∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖ :=
  integral_log_norm_regularizedTwoScale_eq hx0 hx1 hne

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {x u v : ℝ} (hxHalf : 1 / 2 < x) (hxOne : x < 1) (huv : u ≤ v)
    (hne : ∀ t ∈ Icc u v, twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0) :
    (∫ t in u..v, Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) -
      (∫ t in u..v, Real.log ‖regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ))‖) ≤
      (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ))‖) -
        (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 ((4 : ℂ) + I * (t : ℂ))‖) :=
  integral_regularizedTwoScale_verticalLogDifference_le hY0 hY01 hxHalf hxOne huv hne

example {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1) (u v : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re)
      volume u v ∧
    |∫ t in u..v,
      (logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((4 : ℂ) + I * (t : ℂ))).re| ≤
      3 * Real.pi :=
  integral_regularizedTwoScale_rightArgument_bound hY0 hY01 u v

#print axioms log_norm_regularizedTwoScale_eq
#print axioms logDeriv_regularizedTwoScale_eq
#print axioms integral_log_norm_regularizedTwoScale_eq
#print axioms integral_regularizedTwoScale_verticalLogDifference_le
#print axioms integral_regularizedTwoScale_rightArgument_bound
