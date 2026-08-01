import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeHeightCriterion

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for target-amplitude contour-height admissibility. -/

example
    {beta : ℝ} {logHeight : ℕ → ℝ}
    (hadmissible :
      IsTargetAmplitudeAdmissibleHeight beta logHeight) :
    Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta logHeight)
      atTop (𝓝 0) :=
  tendsto_pntTargetAmplitudeContourRatio_zero hadmissible

example {beta alpha : ℝ} (hcritical : 1 - beta < alpha) :
    IsTargetAmplitudeAdmissibleHeight beta
      (pntPolynomialLogHeight alpha) :=
  isTargetAmplitudeAdmissibleHeight_pntPolynomial hcritical

example (beta : ℝ) :
    pntTargetAmplitudeContourRatioAtLogHeight beta
        (pntPolynomialLogHeight (1 - beta)) =
      fun _ : ℕ => 1 :=
  pntPolynomialContourRatio_critical beta

example {beta alpha : ℝ} (hcritical : alpha < 1 - beta) :
    Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta
        (pntPolynomialLogHeight alpha))
      atTop atTop :=
  tendsto_pntPolynomialContourRatio_atTop_of_lt_critical hcritical

example (beta alpha : ℝ) :
    Tendsto
        (pntTargetAmplitudeContourRatioAtLogHeight beta
          (pntPolynomialLogHeight alpha))
        atTop (𝓝 0) ↔
      1 - beta < alpha :=
  tendsto_pntPolynomialContourRatio_zero_iff beta alpha

end PrimeNumberTheorem
