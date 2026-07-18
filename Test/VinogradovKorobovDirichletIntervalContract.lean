import ZeroFreeRegion.VinogradovKorobov.DirichletInterval

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (sigma t : ℝ) (m N : ℕ) : ℂ :=
  dirichletInterval sigma t m N

example (sigma t : ℝ) (m N₁ N₂ : ℕ) :
    dirichletInterval sigma t m (N₁ + N₂) =
      dirichletInterval sigma t m N₁ +
        dirichletInterval sigma t (m + N₁) N₂ :=
  dirichletInterval_add_length sigma t m N₁ N₂

example (sigma t : ℝ) (m q B : ℕ) :
    dirichletInterval sigma t m (q * B) =
      ∑ j ∈ Finset.range q,
        dirichletInterval sigma t (m + j * B) B :=
  dirichletInterval_mul_length sigma t m q B

example (sigma t : ℝ) (m N L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : t * ((L - 1 : ℕ) : ℝ) ≤
      (m : ℝ) * ((m : ℝ) + 2)) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m *
        max (L : ℝ)
          (Real.sqrt (zetaOscillationHarmonicBound t m N L)) :=
  norm_dirichletInterval_le_weight_mul_harmonic_of_scale
    sigma t m N L hsigma ht hm hL hscale

example (sigma t : ℝ) (m q B L : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hL : 1 ≤ L)
    (hscale : ∀ j < q,
      t * ((L - 1 : ℕ) : ℝ) ≤
        ((m + j * B : ℕ) : ℝ) * (((m + j * B : ℕ) : ℝ) + 2)) :
    ‖dirichletInterval sigma t m (q * B)‖ ≤
      ∑ j ∈ Finset.range q,
        dirichletWeight sigma (m + j * B) *
          max (L : ℝ)
            (Real.sqrt
              (zetaOscillationHarmonicBound t (m + j * B) B L)) :=
  norm_dirichletInterval_mul_le_sum_harmonic_of_scale
    sigma t m q B L hsigma ht hm hL hscale

end ZeroFreeRegion.VinogradovKorobov
