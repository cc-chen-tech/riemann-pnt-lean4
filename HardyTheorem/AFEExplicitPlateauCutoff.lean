import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# An explicit quantitative plateau for the critical AFE

Unlike a `ContDiffBump` obtained through the nonconstructive
`someContDiffBumpBase`, this plateau is a product of two translates of the
fixed function `Real.smoothTransition`.  Its transition widths are exactly
one, so its derivative bounds can be chosen independently of the endpoints.
-/

noncomputable section

open Set

namespace HardyTheorem
namespace AFE

/-- A smooth plateau equal to one on `[x,N]`, with unit-width transition
strips `[x-1,x]` and `[N,N+1]`. -/
noncomputable def explicitIntervalPlateau (x N u : ℝ) : ℝ :=
  Real.smoothTransition (u - (x - 1)) *
    Real.smoothTransition ((N + 1) - u)

theorem explicitIntervalPlateau_contDiff (x N : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (explicitIntervalPlateau x N) := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem explicitIntervalPlateau_eq_one {x N u : ℝ} (hu : u ∈ Icc x N) :
    explicitIntervalPlateau x N u = 1 := by
  rw [explicitIntervalPlateau,
    Real.smoothTransition.one_of_one_le (by linarith [hu.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hu.2]), one_mul]

theorem explicitIntervalPlateau_eq_zero_of_le {x N u : ℝ}
    (hu : u ≤ x - 1) :
    explicitIntervalPlateau x N u = 0 := by
  rw [explicitIntervalPlateau,
    Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem explicitIntervalPlateau_eq_zero_of_ge {x N u : ℝ}
    (hu : N + 1 ≤ u) :
    explicitIntervalPlateau x N u = 0 := by
  have hR : Real.smoothTransition ((N + 1) - u) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  rw [explicitIntervalPlateau, hR, mul_zero]

theorem explicitIntervalPlateau_nonneg (x N u : ℝ) :
    0 ≤ explicitIntervalPlateau x N u := by
  exact mul_nonneg (Real.smoothTransition.nonneg _)
    (Real.smoothTransition.nonneg _)

theorem explicitIntervalPlateau_le_one (x N u : ℝ) :
    explicitIntervalPlateau x N u ≤ 1 := by
  have hL0 := Real.smoothTransition.nonneg (u - (x - 1))
  have hL1 := Real.smoothTransition.le_one (u - (x - 1))
  have hR0 := Real.smoothTransition.nonneg ((N + 1) - u)
  have hR1 := Real.smoothTransition.le_one ((N + 1) - u)
  rw [explicitIntervalPlateau]
  nlinarith

theorem explicitIntervalPlateau_hasCompactSupport (x N : ℝ) :
    HasCompactSupport (explicitIntervalPlateau x N) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (x - 1) (N + 1)))
  intro u hu
  rw [mem_Icc, not_and_or] at hu
  rcases hu with hu | hu
  · exact explicitIntervalPlateau_eq_zero_of_le (le_of_lt (lt_of_not_ge hu))
  · exact explicitIntervalPlateau_eq_zero_of_ge (le_of_lt (lt_of_not_ge hu))

end AFE
end HardyTheorem
