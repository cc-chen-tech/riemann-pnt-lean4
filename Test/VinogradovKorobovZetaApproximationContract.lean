import ZeroFreeRegion.VinogradovKorobov.ZetaApproximation

open Complex Set
open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (sigma t : ℝ) (N : ℕ) :
    dirichletInterval sigma t 1 N =
      ∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((sigma : ℂ) + I * t) :=
  dirichletInterval_one_eq_sum_Icc sigma t N

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
        ∃ R : ℂ,
          riemannZeta ((1 / 2 : ℂ) + I * t) =
            dirichletInterval (1 / 2) t 1
              (HardyTheorem.firstZetaApproximationCutoff T) + R ∧
          ‖R‖ ≤ C / Real.sqrt T :=
  criticalLineZetaFirstApprox_dirichletInterval

example (t : ℝ) (N : ℕ) :
    ‖dirichletInterval (1 / 2) t 1 N‖ ≤ 2 * Real.sqrt N :=
  norm_criticalLine_dirichletInterval_one_le_two_sqrt t N

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
        ∀ m L : ℕ,
          1 ≤ m →
          m ≤ HardyTheorem.firstZetaApproximationCutoff T + 1 →
          1 ≤ L →
          t * ((L - 1 : ℕ) : ℝ) ≤
            (m : ℝ) * ((m : ℝ) + 2) →
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ≤
            (m - 1 : ℕ) +
              dirichletWeight (1 / 2) m *
                max (L : ℝ)
                  (Real.sqrt (zetaOscillationHarmonicBound t m
                    (HardyTheorem.firstZetaApproximationCutoff T + 1 - m) L)) +
              C / Real.sqrt T :=
  norm_riemannZeta_criticalLine_le_harmonic_of_scale

example :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧ ∀ T t : ℝ,
      T0 ≤ T → t ∈ Set.Icc T (2 * T) →
        ∀ m L : ℕ,
          1 ≤ m →
          m ≤ HardyTheorem.firstZetaApproximationCutoff T + 1 →
          1 ≤ L →
          t * ((L - 1 : ℕ) : ℝ) ≤
            (m : ℝ) * ((m : ℝ) + 2) →
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ ≤
            2 * Real.sqrt (m - 1 : ℕ) +
              dirichletWeight (1 / 2) m *
                max (L : ℝ)
                  (Real.sqrt (zetaOscillationHarmonicBound t m
                    (HardyTheorem.firstZetaApproximationCutoff T + 1 - m) L)) +
              C / Real.sqrt T :=
  norm_riemannZeta_criticalLine_le_harmonic_sqrt_initial_of_scale

end ZeroFreeRegion.VinogradovKorobov
