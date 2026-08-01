import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicSharedVerticalTails
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicDynamicLowLeft

/-!
# Shared high-tail and low-height budgets on one cubic boundary

This module combines two already concrete estimates without strengthening either
claim.  The same positive boundary parameter `b` controls

* both actual high vertical tails, with one shared `Ctail` and `T0`; and
* the compact-height logarithmic derivative, with a separate constant `Clow`.

The conclusion deliberately does not assert zeta nonvanishing on the low
segment.  That compatibility is a separate analytic input needed before this
budget can be turned into an actual low-segment contour integral.
-/

namespace PrimeNumberTheorem

open Complex MeasureTheory Set Filter Topology
open scoped Real
open ExplicitFormulaResidues

/-- The actual two-sided high tails and the compact-height logarithmic
derivative budget can use the same cubic boundary parameter. -/
theorem exists_actualCubicSharedHighTailLowLogDerivBudget :
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
        let M := x ^ a * Ctail * (1 + Real.log (H + 6)) ^ 2 / (2 * T0 ^ 2)
        ((‖∫ t : ℝ in T0..H,
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ M) ∧
          (‖∫ t : ℝ in (-H)..(-T0),
              thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ M)) ∧
        ∀ t : ℝ, |t| ≤ T0 →
          ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ Clow := by
  rcases exists_norm_integral_actualCubicTwoSidedVerticalTails_le with
    ⟨b, Ctail, T0, hb, hCtail, hT0, htails⟩
  rcases exists_dynamicCubicLowLeft_logDeriv_budget b T0 hb with
    ⟨Clow, H0, hClow, hH0, hlow⟩
  refine ⟨b, Ctail, Clow, T0, H0, hb, hCtail, hClow, hT0, hH0, ?_⟩
  intro x H hx hH
  have hT0H : T0 ≤ H := (le_max_left T0 H0).trans hH
  have hH0H : H0 ≤ H := (le_max_right T0 H0).trans hH
  refine ⟨htails x H hx hT0H, ?_⟩
  intro t ht
  exact hlow H hH0H t ht

end PrimeNumberTheorem
