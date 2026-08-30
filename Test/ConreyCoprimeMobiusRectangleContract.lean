import HardyTheorem.ConreyCoprimeMobiusRectangle

open Complex Set
open scoped BigOperators Interval

-- The actual Euler integrand, including alpha = 0, must have the exact
-- rectangle residue. Only geometric disk containment is supplied.
example : ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ ∀ (m : ℕ) (α : ℂ)
    (X a b c d : ℝ), 0 < X →
    a < 0 → 0 < b → c < 0 → 0 < d →
    a < (-α).re → (-α).re < b → c < (-α).im → (-α).im < d →
    (∀ w ∈ ([[a, b]] ×ℂ [[c, d]]), ‖α + w‖ ≤ r) →
    MathlibAux.boundaryRectIntegral (fun w : ℂ => (X : ℂ) ^ w *
      (riemannZeta (1 + α + w) *
        ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
      (1 / w ^ 2)) a b c d =
      (2 * Real.pi * I) *
        ((Real.log X : ℂ) * (α *
          (ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + α))⁻¹ *
          (∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α))))⁻¹) +
        deriv (fun z : ℂ => z *
          (ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z))⁻¹ *
          (∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹) α) := by
  exact HardyTheorem.exists_conrey_coprime_mobius_rectangle_residue

#print axioms HardyTheorem.exists_conrey_coprime_mobius_rectangle_residue
