import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTMovingSigmaTransfer

open Filter Topology

namespace PrimeNumberTheorem

#check MovingSigmaPNTUpperSchedule
#check UniformMovingSigmaHybridDensityDecay
#check exists_movingSigmaPNTUpperSchedule
#check uniformMovingSigmaHybridDensityDecay_of_fixed
#check MovingSigmaPNTUpperSchedule.relativeBudget_tendsto
#check MovingSigmaPNTUpperSchedule.relativeError_tendsto

example
    {n : ℕ} {rate : ℝ}
    (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (inputAtHeight : ∀ T : ℝ, PositiveZeroBucketInput T n)
    (hdensity :
      UniformMovingSigmaHybridDensityDecay rate inputAtHeight) :
    ∃ C : ℝ, 0 ≤ C ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) :=
  exists_movingSigma_relativeChebyshevPsi0Error_tendsto
    hrate hrateOne inputAtHeight hdensity

end PrimeNumberTheorem
