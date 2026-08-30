import HardyTheorem.ConreyCoprimeMobiusLeftBound

open Complex Set MeasureTheory
open scoped BigOperators Interval

-- One constant precedes all varying parameters; no analytic surrogate input.
example : ∃ κ C M : ℝ, 0 < κ ∧ κ ≤ 1 / 4 ∧ 0 < C ∧ 3 ≤ M ∧
    ∀ (K : ℝ) (m : ℕ) (δ : ℝ) (α : ℂ) (X b : ℝ),
      M ≤ K → 0 ≤ δ → δ ≤ 1 / 16 → 0 < X → 0 < b → ‖α‖ < b →
      b + ‖α‖ ≤ 2 * δ → b + ‖α‖ ≤ κ / (1 + Real.log (K + 3)) →
      let f : ℝ → ℂ := fun t => (X : ℂ) ^ ((-b : ℂ) + t * I) *
        (riemannZeta (1 + α + ((-b : ℂ) + t * I)) *
          ∏ p ∈ m.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + ((-b : ℂ) + t * I)))))⁻¹ *
        (1 / ((-b : ℂ) + t * I) ^ 2)
      IntervalIntegrable f volume (-K) K ∧
        ‖∫ t in (-K)..K, f t‖ ≤ C *
          (∏ p ∈ m.primeFactors, (1 + (p : ℝ) ^ (-(1 - 2 * δ)))) *
          X ^ (-b) * (1 + Real.log (1 + 1 / b)) := by
  exact HardyTheorem.exists_conrey_coprime_mobius_left_bound

#print axioms HardyTheorem.exists_conrey_coprime_mobius_left_majorants
#print axioms HardyTheorem.exists_conrey_coprime_mobius_left_bound
