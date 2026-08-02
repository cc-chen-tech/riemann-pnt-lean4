import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicSharedVerticalTails
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicLowVerticalIntegral

/-!
# Shared actual cubic bounds for all three vertical blocks

The positive high tail, compact low block, and negative high tail use the same
dynamic cubic boundary parameter `b` and the same split height `T0`.  The
theorem keeps the blocks separate: no interval-additivity claim is made here.
-/

namespace PrimeNumberTheorem

open Complex MeasureTheory Set Filter Topology
open scoped Real
open ExplicitFormulaResidues

/-- One cubic boundary supports both actual high tails and the actual compact
low block, with all losses displayed separately. -/
theorem exists_actualCubicSharedFullVerticalBlockBounds :
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
        let Mlow := 2 * T0 * (x ^ a * Clow / a ^ 3)
        ((‖∫ t : ℝ in T0..H,
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ Mhigh) ∧
          (‖∫ t : ℝ in (-H)..(-T0),
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ Mhigh)) ∧
        (‖∫ t : ℝ in (-T0)..T0,
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ Mlow) := by
  rcases exists_norm_integral_actualCubicTwoSidedVerticalTails_le with
    ⟨b, Ctail, T0, hb, hCtail, hT0, htails⟩
  have hT0nonneg : 0 ≤ T0 := (by norm_num : (0 : ℝ) ≤ 4).trans hT0
  rcases exists_norm_integral_actualCubicLowVertical_le b T0 hb hT0nonneg with
    ⟨Clow, H0, hClow, hH0, hlow⟩
  refine ⟨b, Ctail, Clow, T0, H0, hb, hCtail, hClow, hT0, hH0, ?_⟩
  intro x H hx hH
  have hT0H : T0 ≤ H := (le_max_left T0 H0).trans hH
  have hH0H : H0 ≤ H := (le_max_right T0 H0).trans hH
  exact ⟨htails x H hx hT0H, hlow x H hx hH0H⟩

end PrimeNumberTheorem
