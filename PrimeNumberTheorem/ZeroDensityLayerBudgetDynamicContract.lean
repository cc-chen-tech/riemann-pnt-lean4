import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamic

namespace PrimeNumberTheorem

noncomputable def identityHeightSchedule :
    DynamicHeightSchedule 2 1 where
  height := id
  admissible := by
    intro x hx
    exact ⟨hx, by simpa [id] using (show (1 : ℝ) ≤ x by linarith)⟩
  tendsToAtTop := Filter.tendsto_id

example :
    explicitFormulaCost
      (fun _ _ => 1) (fun _ _ => 2) (fun _ _ => 3) 10 20 = 6 := by
  norm_num [explicitFormulaCost]

example :
    IsOptimalHeight
      (fun _ T => T)
      (fun _ T => 1 ≤ T)
      (fun _ => 1) := by
  intro x
  constructor
  · norm_num
  · intro U hU
    simpa using hU

example
    (pntError : ℝ → ℂ)
    (layerCost truncationCost compactCost : ℝ → ℝ → ℝ)
    (hformula :
      ∀ x T, AdmissibleHeight 1 x T →
        ‖pntError x‖ ≤
          explicitFormulaCost layerCost truncationCost compactCost x T) :
    ∀ x, 2 ≤ x →
      ‖pntError x‖ ≤
        explicitFormulaCost layerCost truncationCost compactCost x
          (identityHeightSchedule.height x) :=
  dynamic_explicit_formula_upper identityHeightSchedule hformula

end PrimeNumberTheorem
