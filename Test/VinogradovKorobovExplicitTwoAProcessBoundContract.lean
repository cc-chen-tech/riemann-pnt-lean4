import ZeroFreeRegion.VinogradovKorobov.ExplicitTwoAProcessBound

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m N : ℕ) : ℝ :=
  globalLogCorrelationBound t m N

noncomputable example (t : ℝ) (m N L₂ : ℕ) : ℝ :=
  explicitTwoAProcessInnerBound t m N L₂

noncomputable example (t : ℝ) (m N L₂ ell₁ : ℕ) : ℝ :=
  refinedTwoAProcessInnerBound t m N L₂ ell₁

noncomputable example (N L₂ : ℕ) : ℝ :=
  refinedTwoAProcessConstantPart N L₂

noncomputable example (t : ℝ) (m N L₂ : ℕ) : ℝ :=
  refinedTwoAProcessReciprocalPart t m N L₂

example (t : ℝ) (m N L₁ L₂ : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (hLN : L₁ + L₂ ≤ N) (hL₁m : L₁ ≤ m) (hL₂m : L₂ ≤ m)
    (hscale :
      5 * t * (L₂ : ℝ) * (L₁ : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / L₁ +
        4 * (N : ℝ) * Real.sqrt
          (explicitTwoAProcessInnerBound t m N L₂) :=
  norm_zetaOscillation_sum_sq_le_explicit_two_aProcess
    t m N L₁ L₂ ht hm hL₁ hL₂ hLN hL₁m hL₂m hscale

example (t : ℝ) (m N L₁ L₂ : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hL₁ : 1 ≤ L₁) (hL₂ : 1 ≤ L₂)
    (hLN : L₁ + L₂ ≤ N) (hL₁m : L₁ ≤ m) (hL₂m : L₂ ≤ m)
    (hscale :
      5 * t * (L₂ : ℝ) * (L₁ : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / L₁ +
        4 * (N : ℝ) *
          (Real.sqrt (refinedTwoAProcessConstantPart N L₂) *
              (L₁ : ℝ) ^ 2 +
            Real.sqrt (refinedTwoAProcessReciprocalPart t m N L₂) *
              Real.sqrt ((L₁ : ℝ) ^ 3 * (1 + Real.log L₁))) /
          (L₁ : ℝ) ^ 2 :=
  norm_zetaOscillation_sum_sq_le_refined_two_aProcess
    t m N L₁ L₂ ht hm hL₁ hL₂ hLN hL₁m hL₂m hscale

example (t : ℝ) (m N L : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hLN : 2 * L ≤ N) (hLm : L ≤ m)
    (hscale :
      5 * t * (L : ℝ) ^ 2 ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range N, zetaOscillation t (m + n)‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / L +
        4 * (N : ℝ) *
          (Real.sqrt (refinedTwoAProcessConstantPart N L) *
              (L : ℝ) ^ 2 +
            Real.sqrt (refinedTwoAProcessReciprocalPart t m N L) *
              Real.sqrt ((L : ℝ) ^ 3 * (1 + Real.log L))) /
          (L : ℝ) ^ 2 :=
  norm_zetaOscillation_sum_sq_le_refined_two_aProcess_equal
    t m N L ht hm hL hLN hLm hscale

end ZeroFreeRegion.VinogradovKorobov
