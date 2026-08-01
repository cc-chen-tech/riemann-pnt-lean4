import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeBarrier

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for the target-amplitude contour-height barrier. -/

example {delta : ℝ} (hdelta : 0 < delta) (rate : ℝ) :
    Tendsto
      (pntSubpolynomialContourToPowerRatio delta rate)
      atTop atTop :=
  pntSubpolynomialContourToPowerRatio_tendsto_atTop hdelta rate

example {delta : ℝ} (hdelta : 0 < delta) (rate : ℝ) :
    ¬ Tendsto
      (pntSubpolynomialContourToPowerRatio delta rate)
      atTop (𝓝 0) :=
  not_tendsto_pntSubpolynomialContourToPowerRatio_zero hdelta rate

example {beta : ℝ} (hbeta : beta < 1) (rate : ℝ) :
    Tendsto
      (pntContourKernelToTargetAmplitudeRatio beta rate)
      atTop atTop :=
  pntContourKernelToTargetAmplitudeRatio_tendsto_atTop hbeta rate

example {beta : ℝ} (hbeta : beta < 1) (rate : ℝ) :
    ¬ Tendsto
      (pntContourKernelToTargetAmplitudeRatio beta rate)
      atTop (𝓝 0) :=
  not_tendsto_pntContourKernelToTargetAmplitudeRatio_zero hbeta rate

end PrimeNumberTheorem
