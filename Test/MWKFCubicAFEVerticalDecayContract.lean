import PrimeNumberTheorem.MWKFCubicAFEVerticalDecay

open Complex
open scoped Interval

namespace PrimeNumberTheorem.MWKFCubic

#check (@exists_norm_completedRiemannZeta₀_le_on_reIcc :
  ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
    a ≤ z.re → z.re ≤ b → ‖completedRiemannZeta₀ z‖ ≤ C)

#check cubicAFEHorizontalScale

-- The constant must be selected before time, not independently for each t.
#check (@exists_norm_cubicAFECompletedIntegrand_horizontal_le_uniform :
  ∀ {X : ℝ}, 0 ≤ X →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ) {x V : ℝ},
      x ∈ [[-X, X]] → 1 ≤ V →
        ‖cubicAFECompletedIntegrand t
            ((x : ℂ) + (V : ℂ) * I)‖ ≤
          K * cubicAFEHorizontalScale t X V ^ 6 * Real.exp (-V ^ 2))

#check (@exists_norm_cubicAFECompletedIntegrand_horizontal_le :
  ∀ (t : ℝ) {X : ℝ}, 0 ≤ X →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {x V : ℝ},
      x ∈ [[-X, X]] → 1 ≤ V →
        ‖cubicAFECompletedIntegrand t
            ((x : ℂ) + (V : ℂ) * I)‖ ≤
          K * cubicAFEHorizontalScale t X V ^ 6 * Real.exp (-V ^ 2))

#check (@tendsto_cubicAFECompletedIntegrand_horizontalIntegral :
  ∀ (t : ℝ) {X : ℝ}, 0 < X →
    Filter.Tendsto
      (fun V : ℝ ↦ ∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I))
      Filter.atTop (nhds 0))

#check (@tendsto_cubicAFECompletedIntegrand_verticalIntegral :
  ∀ (t : ℝ) {X : ℝ}, 0 < X →
    Filter.Tendsto
      (fun V : ℝ ↦ ∫ y : ℝ in -V..V,
        cubicAFECompletedIntegrand t ((X : ℂ) + (y : ℂ) * I))
      Filter.atTop
      (nhds (Real.pi *
        (completedRiemannZeta (cubicCriticalPoint t) *
          completedRiemannZeta (1 - cubicCriticalPoint t)))))

end PrimeNumberTheorem.MWKFCubic
