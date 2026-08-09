import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeHeightIncompatibility

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for one-height incompatibility. -/

example
    {beta : ℝ} (hbeta : beta < 1)
    {logHeight : ℕ → ℝ}
    (hsubpolynomial : IsPNTSubpolynomialLogHeight logHeight) :
    Tendsto
      (pntTargetAmplitudeContourLogGap beta logHeight)
      atTop atBot :=
  tendsto_targetAmplitudeContourLogGap_atBot_of_subpolynomial
    hbeta hsubpolynomial

example
    {beta : ℝ} (hbeta : beta < 1)
    {logHeight : ℕ → ℝ}
    (hsubpolynomial : IsPNTSubpolynomialLogHeight logHeight) :
    ¬ IsTargetAmplitudeAdmissibleHeight beta logHeight :=
  not_isTargetAmplitudeAdmissibleHeight_of_subpolynomial
    hbeta hsubpolynomial

example
    {beta : ℝ} (hbeta : beta < 1)
    {logHeight : ℕ → ℝ}
    (hsubpolynomial : IsPNTSubpolynomialLogHeight logHeight) :
    Tendsto
      (pntTargetAmplitudeContourRatioAtLogHeight beta logHeight)
      atTop atTop :=
  tendsto_targetAmplitudeContourRatio_atTop_of_subpolynomial
    hbeta hsubpolynomial

example {rate : ℝ} (hrate : 0 ≤ rate) :
    IsPNTSubpolynomialLogHeight (pntSqrtLogHeight rate) :=
  isPNTSubpolynomialLogHeight_pntSqrtLog hrate

example
    {beta rate : ℝ} (hbeta : beta < 1) (hrate : 0 ≤ rate) :
    ¬ IsTargetAmplitudeAdmissibleHeight beta
      (pntSqrtLogHeight rate) :=
  not_isTargetAmplitudeAdmissibleHeight_pntSqrtLog hbeta hrate

end PrimeNumberTheorem
