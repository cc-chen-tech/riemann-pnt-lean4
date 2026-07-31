import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteDecay

namespace PrimeNumberTheorem

private def zeroLayerDecay :
    FiniteDynamicLayerDecay (Finset.univ : Finset Bool)
      (fun x : ℝ => x) (fun _ _ _ => 0) where
  layer_tendsto_zero := by
    intro i hi
    simpa using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
        Filter.atTop (nhds 0))

private def zeroFiniteRemainderCertificate :
    DynamicLayerRemainderCertificate
      (fun _ : ℝ => 0) (fun x => x)
      (finiteLayerBudget (Finset.univ : Finset Bool) (fun _ _ _ => 0)) where
  eventually_bound := by
    simp [dynamicLayerBudgetAlong, finiteLayerBudget]

private theorem constantMainWitness :
    HasFarNormWitness (fun _ : ℝ => 1) 1 := by
  intro X
  exact ⟨X, le_rfl, by norm_num⟩

example :
    Filter.Tendsto
      (finiteLayerBudgetAlong (Finset.univ : Finset Bool)
        (fun x : ℝ => x) (fun _ _ _ => 0))
      Filter.atTop (nhds 0) :=
  zeroLayerDecay.total_tendsto_zero

example :
    HasFarNormWitness (fun _ : ℝ => 1) (1 / 2) :=
  hasFarNormWitness_add_of_finiteLayerDecay
    (by norm_num) constantMainWitness zeroFiniteRemainderCertificate
    zeroLayerDecay (by
      intro x
      norm_num)

end PrimeNumberTheorem
