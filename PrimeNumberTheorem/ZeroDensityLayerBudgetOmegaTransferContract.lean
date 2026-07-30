import PrimeNumberTheorem.ZeroDensityLayerBudgetOmegaTransfer

namespace PrimeNumberTheorem

private theorem constantMainWitness :
    HasFarNormWitness (fun _ : ℝ => 1) 1 := by
  intro X
  exact ⟨X, le_rfl, by norm_num⟩

private theorem zeroRemainderSmall :
    IsEventuallyHalfSmall (fun _ : ℝ => 0) 1 := by
  simp [IsEventuallyHalfSmall]

example :
    HasFarNormWitness (fun _ : ℝ => 1) (1 / 2) :=
  hasFarNormWitness_add_of_eventuallyHalfSmall
    constantMainWitness zeroRemainderSmall (by
      intro x
      norm_num)

example {error main remainder : ℝ → ℝ} {amplitude : ℝ}
    (hmain : HasFarSignedWitnesses main amplitude)
    (hsmall : IsEventuallyHalfSmall remainder amplitude)
    (hdecomp : ∀ x, error x = main x + remainder x) :
    HasFarSignedWitnesses error (amplitude / 2) :=
  hasFarSignedWitnesses_add_of_eventuallyHalfSmall hmain hsmall hdecomp

end PrimeNumberTheorem
