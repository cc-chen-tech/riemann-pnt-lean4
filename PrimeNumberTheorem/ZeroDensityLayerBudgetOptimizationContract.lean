import PrimeNumberTheorem.ZeroDensityLayerBudgetOptimization

namespace PrimeNumberTheorem

private def twoHeightGrid : FiniteHeightGrid where
  heights := {1, 2}
  nonempty := by simp
  positive := by
    intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rcases hT with rfl | rfl <;> norm_num

example :
    finiteGridOptimalHeight (fun T : ℝ => T ^ 2) twoHeightGrid ∈
      ({1, 2} : Finset ℝ) :=
  finiteGridOptimalHeight_mem _ _

example :
    (fun T : ℝ => T ^ 2)
        (finiteGridOptimalHeight (fun T : ℝ => T ^ 2) twoHeightGrid) ≤ 1 := by
  simpa using
    finiteGridOptimalHeight_le_of_mem (fun T : ℝ => T ^ 2) twoHeightGrid
      (show (1 : ℝ) ∈ twoHeightGrid.heights by simp [twoHeightGrid])

private def onePointCover :
    FiniteGridCostCover (fun T : ℝ => T ^ 2) twoHeightGrid
      (fun T => T = 1) 0 where
  exists_candidate := by
    intro T hT
    subst T
    exact ⟨1, by simp [twoHeightGrid], by norm_num⟩

example :
    (fun T : ℝ => T ^ 2)
        (finiteGridOptimalHeight (fun T : ℝ => T ^ 2) twoHeightGrid) ≤
      (1 : ℝ) ^ 2 + 0 :=
  finiteGridOptimalHeight_le_add
    (fun T : ℝ => T ^ 2) twoHeightGrid (fun T => T = 1) 0 onePointCover rfl

end PrimeNumberTheorem
