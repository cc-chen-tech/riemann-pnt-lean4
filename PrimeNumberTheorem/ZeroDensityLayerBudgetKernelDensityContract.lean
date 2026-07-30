import PrimeNumberTheorem.ZeroDensityLayerBudgetKernelDensity

namespace PrimeNumberTheorem

private def zeroKernelFactorization :
    CarlsonKernelLayerFactorization
      (Finset.univ : Finset Bool) (fun x : ℝ => x)
      (fun _ _ _ => 0) where
  kernelFactor := fun _ _ => 0
  densityRatio := fun _ _ => 1
  densityBound := fun _ => 1
  densityBound_nonneg := by
    intro i hi
    norm_num
  factorization := by
    intro i hi x
    norm_num
  kernel_tendsto_zero := by
    intro i hi
    simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
        Filter.atTop (nhds 0))
  densityRatio_eventually_bounded := by
    intro i hi
    simp

example :
    FiniteDynamicLayerDecay (Finset.univ : Finset Bool)
      (fun x : ℝ => x) (fun _ _ _ => 0) :=
  zeroKernelFactorization.toFiniteDynamicLayerDecay

example :
    Filter.Tendsto (fun x : ℝ => (0 : ℝ) * 1)
      Filter.atTop (nhds 0) :=
  tendsto_mul_zero_of_eventually_abs_le
    (bound := 1) (by norm_num)
    (by simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
        Filter.atTop (nhds 0)))
    (by simp)

end PrimeNumberTheorem
