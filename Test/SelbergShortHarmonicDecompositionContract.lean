import HardyTheorem.SelbergShortHarmonicDecomposition

open scoped BigOperators

#check HardyTheorem.sum_lcmHarmonic_quadratic_eq_divisorSquares
#check HardyTheorem.sum_lcmHarmonic_quadratic_nonneg
#check HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_divisorSquares

example (a : ℕ → ℝ) (M N : ℕ) :
    (∑ r ∈ Finset.Icc 1 M, ∑ s ∈ Finset.Icc 1 M,
        a r * a s *
          ((Nat.lcm r s : ℝ)⁻¹ *
            (harmonic (N / Nat.lcm r s) : ℝ))) =
      ∑ k ∈ Finset.Icc 1 N,
        (∑ r ∈ (Finset.Icc 1 M).filter (fun r => r ∣ k), a r) ^ 2 *
          (k : ℝ)⁻¹ := by
  exact HardyTheorem.sum_lcmHarmonic_quadratic_eq_divisorSquares a M N

#print axioms HardyTheorem.sum_lcmHarmonic_quadratic_eq_divisorSquares
#print axioms HardyTheorem.sum_lcmHarmonic_quadratic_nonneg
#print axioms HardyTheorem.sum_normSq_selbergShortDirichletCollectedCoeff_completeRange_eq_divisorSquares
