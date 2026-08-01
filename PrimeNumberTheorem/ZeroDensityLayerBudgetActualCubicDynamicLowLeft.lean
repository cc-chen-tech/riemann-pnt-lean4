import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCompactLowLeft

namespace PrimeNumberTheorem

open Complex
open ExplicitFormulaResidues

/-- The positive dynamic cubic boundary eventually enters the fixed compact
right-thickening of the imaginary axis.  Hence every fixed low-height segment
of the actual left edge has a uniform `O(1)` logarithmic-derivative budget. -/
theorem exists_dynamicCubicLowLeft_logDeriv_budget
    (b T : ℝ) (hb : 0 < b) :
    ∃ C H0 : ℝ, 0 ≤ C ∧ 4 ≤ H0 ∧
      ∀ H : ℝ, H0 ≤ H →
        ∀ t : ℝ, |t| ≤ T →
          ‖logDeriv riemannZeta
            ((dynamicCubicLeftBoundary b H : ℂ) + I * t)‖ ≤ C := by
  rcases
      exists_norm_logDeriv_riemannZeta_bound_on_right_thickening_of_imaginary_segment T
      with ⟨δ, C, hδ, hC, hcompact⟩
  let H0 : ℝ := max 4 (Real.exp (b / (2 * δ)))
  have hH0 : 4 ≤ H0 := le_max_left _ _
  refine ⟨C, H0, hC, hH0, ?_⟩
  intro H hH t ht
  have hH4 : 4 ≤ H := hH0.trans hH
  have hlog : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith : (1 : ℝ) < H + 6)
  have hexp : Real.exp (b / (2 * δ)) ≤ H + 6 := by
    have hbase : Real.exp (b / (2 * δ)) ≤ H :=
      (le_max_right (4 : ℝ) _).trans hH
    linarith
  have hlogLower : b / (2 * δ) ≤ Real.log (H + 6) := by
    have h := Real.log_le_log (Real.exp_pos _) hexp
    simpa using h
  have ha : 0 < dynamicCubicLeftBoundary b H := by
    dsimp [dynamicCubicLeftBoundary]
    positivity
  have haδ : dynamicCubicLeftBoundary b H ≤ δ := by
    rw [dynamicCubicLeftBoundary,
      div_le_iff₀ (mul_pos (by norm_num) hlog)]
    have hmul : b ≤ 2 * δ * Real.log (H + 6) := by
      have hcross :=
        (div_le_iff₀ (mul_pos (by norm_num) hδ)).mp hlogLower
      nlinarith
    nlinarith
  exact hcompact (dynamicCubicLeftBoundary b H) t ha.le haδ ht

end PrimeNumberTheorem
