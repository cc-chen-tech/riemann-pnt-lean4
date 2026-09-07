import HardyTheorem.ConreyCoprimeMobiusHorizontalBound

open Complex Set MeasureTheory
open scoped BigOperators Interval

-- Covers both y=K and y=-K, complex shifts, and degenerate intervals.
-- Neither integrability nor an upper bound for an analytic surrogate is assumed.
example : ∃ c T : ℝ, 0 < c ∧ c ≤ 1 ∧ 2 ≤ T ∧
    ∀ (m : ℕ) (δ : ℝ) (α : ℂ) (X b u K y : ℝ),
      0 ≤ δ → δ ≤ 1 / 16 → 1 ≤ X → 0 ≤ b → 0 ≤ u →
      T + 1 ≤ K → |y| = K →
      b + ‖α‖ ≤ 2 * δ → b + ‖α‖ ≤ c / Real.log (K + 1) →
      u + ‖α‖ ≤ 1 →
      let f : ℝ → ℂ := fun x => (X : ℂ) ^ ((x : ℂ) + y * I) *
        (riemannZeta (1 + α + ((x : ℂ) + y * I)) *
          ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + ((x : ℂ) + y * I)))))⁻¹ *
        (1 / ((x : ℂ) + y * I) ^ 2)
      IntervalIntegrable f volume (-b) u ∧
        ‖∫ x in (-b)..u, f x‖ ≤
          (b + u) * X ^ u * (∑' n : ℕ, (n : ℝ) ^ (-(7 / 4 : ℝ))) *
            (∏ p ∈ m.primeFactors, (1 + (p : ℝ) ^ (-(1 - 2 * δ)))) *
            (1 + Real.log (K + 1) / c) * Real.exp (Real.log (K + 1) / 4) / K ^ 2 := by
  exact HardyTheorem.exists_conrey_coprime_mobius_horizontal_bound

#print axioms HardyTheorem.exists_conrey_coprime_mobius_horizontal_bound
