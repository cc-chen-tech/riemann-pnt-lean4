import HardyTheorem.ConreyCoprimeMobiusHighRectangle

open Complex Set
open scoped BigOperators Interval

-- Detects a merely local disk or a hidden zero-free/analyticity assumption:
-- a single positive width constant must work for every height and modulus.
example : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ ∀ (K : ℝ) (m : ℕ) (z : ℂ),
    2 ≤ K → -(κ / (1 + Real.log (K + 2))) ≤ z.re → z.re ≤ 1 → |z.im| ≤ K →
    ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z) ≠ 0 ∧
    AnalyticAt ℂ (fun z : ℂ => z *
      (ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z))⁻¹ *
      (∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹) z := by
  exact HardyTheorem.exists_conrey_coprime_mobius_analytic_rectangles

-- The actual high rectangle, not an analytic surrogate. Zero shift and
-- arbitrary X > 0 are included, with no norm-error estimate assumed.
example : ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧
    ∀ (K : ℝ) (m : ℕ) (α : ℂ) (X b u : ℝ), 2 ≤ K → 0 < X →
      ‖α‖ < b → ‖α‖ < u →
      b + ‖α‖ ≤ κ / (1 + Real.log (K + 3)) → u + ‖α‖ ≤ 1 →
      AnalyticOnNhd ℂ (fun w => HardyTheorem.conreyCoprimeMobiusRegularized m (α + w))
        ([[-b, u]] ×ℂ [[-K, K]]) ∧
      MathlibAux.boundaryRectIntegral (fun w : ℂ => (X : ℂ) ^ w *
        (riemannZeta (1 + α + w) *
          ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
        (1 / w ^ 2)) (-b) u (-K) K =
        (2 * Real.pi * I) *
          ((Real.log X : ℂ) * HardyTheorem.conreyCoprimeMobiusRegularized m α +
            deriv (HardyTheorem.conreyCoprimeMobiusRegularized m) α) := by
  exact HardyTheorem.exists_conrey_coprime_mobius_high_rectangle_residue

#print axioms HardyTheorem.exists_conrey_coprime_mobius_analytic_rectangles
#print axioms HardyTheorem.exists_conrey_coprime_mobius_high_rectangle_residue
#print axioms HardyTheorem.conrey_coprime_mobius_rectangle_residue_of_analytic
#print axioms HardyTheorem.analyticAt_conreyCoprimeEulerInverse
