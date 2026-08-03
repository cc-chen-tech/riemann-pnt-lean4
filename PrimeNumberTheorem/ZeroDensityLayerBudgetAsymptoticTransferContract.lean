import PrimeNumberTheorem.ZeroDensityLayerBudgetAsymptoticTransfer

namespace PrimeNumberTheorem

private def zeroDynamicCertificate :
    DynamicLayerRemainderCertificate
      (fun _ : ℝ => 0) (fun x => x) (fun _ _ => 0) where
  eventually_bound := by
    simp [dynamicLayerBudgetAlong]

private theorem constantMainWitness :
    HasFarNormWitness (fun _ : ℝ => 1) 1 := by
  intro X
  exact ⟨X, le_rfl, by norm_num⟩

example :
    IsEventuallyHalfSmall (fun _ : ℝ => 0) 1 :=
  isEventuallyHalfSmall_of_dynamicLayerBudget_tendsto_zero
    (by norm_num) zeroDynamicCertificate (by
      simpa [dynamicLayerBudgetAlong] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          Filter.atTop (nhds 0)))

example :
    HasFarNormWitness (fun _ : ℝ => 1) (1 / 2) :=
  hasFarNormWitness_add_of_dynamicLayerBudget_tendsto_zero
    (by norm_num) constantMainWitness zeroDynamicCertificate
    (by
      simpa [dynamicLayerBudgetAlong] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
          Filter.atTop (nhds 0)))
    (by
      intro x
      norm_num)

end PrimeNumberTheorem
