import PrimeNumberTheorem.ZeroDensityLayerBudgetBidirectional

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

private def zeroUpperCertificate :
    DynamicExplicitFormulaUpperCertificate
      (fun _ : ℝ => 0) (Finset.univ : Finset Bool)
      (fun x => x) (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0) where
  eventually_bound := by
    simp [dynamicExplicitFormulaUpperBudgetAlong, finiteLayerBudgetAlong,
      finiteLayerBudget]

example :
    Filter.Tendsto (fun _ : ℝ => 0) Filter.atTop (nhds 0) :=
  dynamicExplicitFormulaUpper_tendsto_zero_of_kernelDensityFactorization
    zeroUpperCertificate zeroKernelFactorization
    (by simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
        Filter.atTop (nhds 0)))
    (by simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
        Filter.atTop (nhds 0)))

end PrimeNumberTheorem
