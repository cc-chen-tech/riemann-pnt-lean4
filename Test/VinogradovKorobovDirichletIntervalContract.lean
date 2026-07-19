import ZeroFreeRegion.VinogradovKorobov.DirichletInterval

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (sigma t : ℝ) (m N : ℕ) : ℂ :=
  dirichletInterval sigma t m N

example (sigma t : ℝ) (m N : ℕ)
    (hsigma : 0 ≤ sigma) (hm : 0 < m) :
    ‖dirichletInterval sigma t m N‖ ≤ N :=
  norm_dirichletInterval_le_length sigma t m N hsigma hm

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

example (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hh : 1 ≤ h)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : ∀ K, constantAProcessPrefixThreshold depth h ≤ K → K ≤ N →
      2 * Real.pi * (h : ℝ) ≤
        zetaAProcessUniformLeafDeltaLower t m K depth *
          (h : ℝ) ^ depth * (K : ℝ)) :
    ∀ K ≤ N,
      ‖∑ n ∈ Finset.range K, zetaOscillation t (m + n)‖ ≤
        max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) :=
  norm_zetaOscillation_prefix_le_max_constantAProcessExplicitPower
    t m N depth h ht hm hh hmajor hscale

example (sigma t : ℝ) (m N depth h : ℕ)
    (hsigma : 0 ≤ sigma) (ht : 0 < t) (hm : 0 < m) (hh : 1 ≤ h)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : ∀ K, constantAProcessPrefixThreshold depth h ≤ K → K ≤ N →
      2 * Real.pi * (h : ℝ) ≤
        zetaAProcessUniformLeafDeltaLower t m K depth *
          (h : ℝ) ^ depth * (K : ℝ)) :
    ‖dirichletInterval sigma t m N‖ ≤
      dirichletWeight sigma m *
        max (constantAProcessPrefixThreshold depth h : ℝ)
          (6 * (1 + Real.log h) * (N : ℝ) /
            (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) :=
  norm_dirichletInterval_le_weight_mul_constantAProcessExplicitPower
    sigma t m N depth h hsigma ht hm hh hmajor hscale

end ZeroFreeRegion.VinogradovKorobov
