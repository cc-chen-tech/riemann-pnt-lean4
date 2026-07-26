import ZeroFreeRegion.VinogradovKorobov.TwoAProcessLogSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m N ell₁ ell₂ : ℕ) : ℝ :=
  twoAProcessLogCorrelationBound t m N ell₁ ell₂

example (t : ℝ) (m N L₁ : ℕ) (L₂ : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₁N : L₁ ≤ N)
    (hL₂ : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), 1 ≤ L₂ ell₁)
    (hL₂N : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      L₂ ell₁ ≤ N - ell₁)
    (hturn : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        t * logSecondDifferenceDecrement ell₂ ell₁ m ≤
          2 * Real.pi -
            t * logSecondDifferenceDecrement ell₂ ell₁
              ((m + (N - ell₁ - ell₂ - 1) : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound
            (twoAProcessLogCorrelationBound t m N ell₁)
            (N - ell₁) (L₂ ell₁)))
        N L₁ :=
  norm_zetaOscillation_sum_sq_le_two_aProcess
    t m N L₁ L₂ ht hm hL₁ hL₁N hL₂ hL₂N hturn

end ZeroFreeRegion.VinogradovKorobov
