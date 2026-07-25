import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudePowerGap

open Filter Topology

namespace PrimeNumberTheorem

/-! Public contract for target-amplitude power-layer comparison. -/

example {beta sigma : ℝ} (hgap : sigma < beta) :
    Tendsto
      (pntPowerLayerToTargetRatio beta sigma)
      atTop (𝓝 0) :=
  pntPowerLayerToTargetRatio_tendsto_zero_of_lt hgap

example (beta : ℝ) :
    pntPowerLayerToTargetRatio beta beta = fun _ : ℕ => 1 :=
  pntPowerLayerToTargetRatio_self beta

example (beta : ℝ) :
    ¬ Tendsto
      (pntPowerLayerToTargetRatio beta beta)
      atTop (𝓝 0) :=
  not_tendsto_pntPowerLayerToTargetRatio_self_zero beta

example {beta sigma : ℝ} (hgap : beta < sigma) :
    Tendsto
      (pntPowerLayerToTargetRatio beta sigma)
      atTop atTop :=
  pntPowerLayerToTargetRatio_tendsto_atTop_of_lt hgap

example {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (pntPowerLayerToTargetRatio beta 0)
      atTop (𝓝 0) :=
  pntInverseScaleToTargetRatio_tendsto_zero hbeta

end PrimeNumberTheorem
