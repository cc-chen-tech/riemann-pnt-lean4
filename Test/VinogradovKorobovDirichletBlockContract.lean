import ZeroFreeRegion.VinogradovKorobov.DirichletBlock

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (sigma : ℝ) (n : ℕ) : 0 ≤ dirichletWeight sigma n :=
  dirichletWeight_nonneg sigma n

example {sigma : ℝ} (hsigma : 0 ≤ sigma) {m k : ℕ} (hm : 0 < m) :
    dirichletWeight sigma (m + (k + 1)) ≤
      dirichletWeight sigma (m + k) :=
  dirichletWeight_antitone hsigma hm k

example {n : ℕ} (hn : n ≠ 0) (sigma t : ℝ) :
    1 / (n : ℂ) ^ ((sigma : ℂ) + Complex.I * t) =
      (dirichletWeight sigma n : ℂ) * zetaOscillation t n :=
  inv_nat_cpow_eq_dirichletWeight_mul_zetaOscillation hn sigma t

example (sigma t : ℝ) (m N : ℕ) (B : ℝ)
    (hsigma : 0 ≤ sigma) (hm : 0 < m)
    (hpartial : ∀ k ≤ N,
      ‖∑ j ∈ Finset.range (k + 1), zetaOscillation t (m + j)‖ ≤ B) :
    ‖∑ k ∈ Finset.range (N + 1),
        1 / ((m + k : ℕ) : ℂ) ^ ((sigma : ℂ) + Complex.I * t)‖ ≤
      dirichletWeight sigma m * B :=
  norm_dirichletBlock_le_weight_mul sigma t m N B hsigma hm hpartial

end ZeroFreeRegion.VinogradovKorobov
