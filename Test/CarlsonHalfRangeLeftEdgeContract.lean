import PrimeNumberTheorem.CarlsonHalfRangeLeftEdge

open Complex Filter MeasureTheory Set
open PrimeNumberTheorem PrimeNumberTheorem.CarlsonZeroDensity

example (Y0 Y1 : ℕ) (s : ℂ) :
    Real.log ‖twoScaleCarlsonZeroDetector Y0 Y1 s‖ ≤
      ‖twoScaleMollifiedZetaError Y0 Y1 s‖ ^ 2 :=
  log_norm_twoScaleCarlsonZeroDetector_le_error_sq Y0 Y1 s

example : ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
    ∀ x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
    ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
      (∀ t ∈ Icc u v, twoScaleCarlsonZeroDetector
        (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
        ((x : ℂ) + I * (t : ℂ)) ≠ 0) →
      IntervalIntegrable (fun t : ℝ => Real.log ‖twoScaleCarlsonZeroDetector
        (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
        ((x : ℂ) + I * (t : ℂ))‖) volume u v ∧
      (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector
        (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
        ((x : ℂ) + I * (t : ℂ))‖) ≤
        K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 :=
  exists_eventually_halfRange_leftEdge_logIntegral_le

#print axioms log_norm_twoScaleCarlsonZeroDetector_le_error_sq
#print axioms exists_eventually_halfRange_leftEdge_logIntegral_le

example : ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
    ∃ x ∈ Ioo halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
      (1 / 20000 : ℝ) ≤ 2 / 3 - x ∧
      (∀ t ∈ Icc (2 * V) (5 * V / 2), twoScaleCarlsonZeroDetector
        (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
        ((x : ℂ) + I * (t : ℂ)) ≠ 0) ∧
      ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
        IntervalIntegrable (fun t : ℝ => Real.log ‖twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ))‖) volume u v ∧
        (∫ t in u..v, Real.log ‖twoScaleCarlsonZeroDetector
          (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
          ((x : ℂ) + I * (t : ℂ))‖) ≤
          K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 :=
  exists_eventually_halfRange_selectedLeftEdge_logIntegral_le

#print axioms exists_eventually_halfRange_selectedLeftEdge_logIntegral_le
