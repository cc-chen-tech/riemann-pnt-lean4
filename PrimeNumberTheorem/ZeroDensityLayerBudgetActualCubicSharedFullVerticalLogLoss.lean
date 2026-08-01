import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicSharedFullVerticalBlocks

/-!
# Explicit logarithmic loss on the compact cubic vertical block

For `a(H) = b / (2 log(H+6))`, the coarse cubic denominator loss `a(H)⁻³`
is exactly an explicit `log(H+6)^3` loss.  This module exposes that arithmetic
normal form for later two-height exponent comparisons.
-/

namespace PrimeNumberTheorem

open Complex MeasureTheory Set Filter Topology
open scoped Real
open ExplicitFormulaResidues

/-- Exact conversion of the coarse low-block cubic denominator loss into its
logarithmic form. -/
lemma dynamicCubicLowKernelLoss_eq_log_cube
    {b H x C T : ℝ} (hb : 0 < b) (hH : 4 ≤ H) :
    let a := dynamicCubicLeftBoundary b H
    2 * T * (x ^ a * C / a ^ 3) =
      16 * T * x ^ a * C * Real.log (H + 6) ^ 3 / b ^ 3 := by
  have hlog : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith : (1 : ℝ) < H + 6)
  dsimp [dynamicCubicLeftBoundary]
  field_simp [hb.ne', hlog.ne']
  <;> ring

/-- Shared actual high and low vertical blocks with the compact loss displayed
as `log(H+6)^3 / b^3`. -/
theorem exists_actualCubicSharedFullVerticalBlockLogBounds :
    ∃ b Ctail Clow T0 H0 : ℝ,
      0 < b ∧
      0 ≤ Ctail ∧
      0 ≤ Clow ∧
      4 ≤ T0 ∧
      4 ≤ H0 ∧
      ∀ (x H : ℝ),
        0 < x →
        max T0 H0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        let Mhigh :=
          x ^ a * Ctail * (1 + Real.log (H + 6)) ^ 2 / (2 * T0 ^ 2)
        let Mlow :=
          16 * T0 * x ^ a * Clow * Real.log (H + 6) ^ 3 / b ^ 3
        ((‖∫ t : ℝ in T0..H,
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ Mhigh) ∧
          (‖∫ t : ℝ in (-H)..(-T0),
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ Mhigh)) ∧
        (‖∫ t : ℝ in (-T0)..T0,
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ Mlow) := by
  rcases exists_actualCubicSharedFullVerticalBlockBounds with
    ⟨b, Ctail, Clow, T0, H0, hb, hCtail, hClow, hT0, hH0, hblocks⟩
  refine ⟨b, Ctail, Clow, T0, H0, hb, hCtail, hClow, hT0, hH0, ?_⟩
  intro x H hx hH
  have hH4 : 4 ≤ H := hT0.trans ((le_max_left T0 H0).trans hH)
  rcases hblocks x H hx hH with ⟨htails, hlow⟩
  refine ⟨htails, ?_⟩
  rw [dynamicCubicLowKernelLoss_eq_log_cube hb hH4] at hlow
  exact hlow

end PrimeNumberTheorem
