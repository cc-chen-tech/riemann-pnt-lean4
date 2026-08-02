import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicContourBudget

namespace PrimeNumberTheorem

open Complex
open ExplicitFormulaResidues

/-- Near the zeta pole, the reflected point attached to the positive dynamic
left boundary costs exactly one reciprocal boundary factor.  Since
`a(H) = b / (2 log (H+6))`, the local pole-order bound becomes an explicit
single logarithmic loss. -/
theorem exists_dynamicCubicReflectedPole_logDeriv_le :
    ∃ r : ℝ, 0 < r ∧
      ∀ b H t : ℝ, 0 < b → 4 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        let w : ℂ := ((1 - a : ℝ) : ℂ) + I * (-t)
        dist w 1 ≤ r →
          ‖logDeriv riemannZeta w‖ ≤ 4 * Real.log (H + 6) / b := by
  rcases
      ZeroFreeRegion.exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one
      with ⟨r, hr, hlocal⟩
  refine ⟨r, hr, ?_⟩
  intro b H t hb hH
  dsimp only
  let a : ℝ := dynamicCubicLeftBoundary b H
  let w : ℂ := ((1 - a : ℝ) : ℂ) + I * (-t)
  have hlog : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith : (1 : ℝ) < H + 6)
  have ha : 0 < a := by
    dsimp [a, dynamicCubicLeftBoundary]
    positivity
  intro hdist
  have hw1 : w ≠ 1 := by
    intro hw
    have hre := congrArg Complex.re hw
    simp [w] at hre
    linarith
  have hbase := hlocal w hw1 hdist
  have hnormLower : a ≤ ‖w - 1‖ := by
    calc
      a = |(w - 1).re| := by simp [w, abs_of_pos ha]
      _ ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
  apply hbase.trans
  calc
    2 / ‖w - 1‖ ≤ 2 / a :=
      div_le_div_of_nonneg_left (by norm_num) ha hnormLower
    _ = 4 * Real.log (H + 6) / b := by
      dsimp [a, dynamicCubicLeftBoundary]
      field_simp [hb.ne', hlog.ne']
      ring

end PrimeNumberTheorem
