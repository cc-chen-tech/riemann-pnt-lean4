import ZeroFreeRegion.VinogradovKorobov.ScaledTwoAProcessLogSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m N ell₁ ell₂ : ℕ) : ℝ :=
  scaledTwoAProcessLogCorrelationBound t m N ell₁ ell₂

example (t : ℝ) (m N L₁ : ℕ) (L₂ : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₁N : L₁ ≤ N) (hL₁m : L₁ ≤ m)
    (hL₂ : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), 1 ≤ L₂ ell₁)
    (hL₂N : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      L₂ ell₁ ≤ N - ell₁)
    (hL₂m : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1), L₂ ell₁ ≤ m)
    (hscale : ∀ ell₁ ∈ Finset.Icc 1 (L₁ - 1),
      ∀ ell₂ ∈ Finset.Icc 1 (L₂ ell₁ - 1),
        5 * t * (ell₂ : ℝ) * (ell₁ : ℝ) ≤
          Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound
            (scaledTwoAProcessLogCorrelationBound t m N ell₁)
            (N - ell₁) (L₂ ell₁)))
        N L₁ :=
  norm_zetaOscillation_sum_sq_le_scaled_two_aProcess
    t m N L₁ L₂ ht hm hL₁ hL₁N hL₁m hL₂ hL₂N hL₂m hscale

example (t : ℝ) (m N L₁ L₂ : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (hLN : L₁ + L₂ ≤ N) (hL₁m : L₁ ≤ m) (hL₂m : L₂ ≤ m)
    (hscale :
      5 * t * (L₂ : ℝ) * (L₁ : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      aProcessSquaredBound
        (fun ell₁ ↦ Real.sqrt
          (aProcessSquaredBound
            (scaledTwoAProcessLogCorrelationBound t m N ell₁)
            (N - ell₁) L₂))
        N L₁ :=
  norm_zetaOscillation_sum_sq_le_scaled_two_aProcess_const
    t m N L₁ L₂ ht hm hL₁ hL₂ hLN hL₁m hL₂m hscale

end ZeroFreeRegion.VinogradovKorobov
