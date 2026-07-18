import ZeroFreeRegion.VinogradovKorobov.ZetaStrip

open Complex Set

namespace ZeroFreeRegion.VinogradovKorobov

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma t : ℝ,
      (1 / 4 : ℝ) ≤ sigma → sigma ≤ 2 → 1 ≤ t →
        ∃ R : ℂ,
          riemannZeta ((sigma : ℂ) + I * t) =
            dirichletInterval sigma t 1 (Nat.floor (2 * t)) +
              (2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
                (((sigma : ℂ) + I * t) - 1) + R ∧
          ‖R‖ ≤ C * (2 * t) ^ (-sigma) :=
  stripZetaFirstApprox_dirichletInterval

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma t : ℝ,
      (1 / 4 : ℝ) ≤ sigma → sigma ≤ 2 → 1 ≤ t →
        ∀ m L : ℕ,
          1 ≤ m → m ≤ Nat.floor (2 * t) + 1 → 1 ≤ L →
          t * ((L - 1 : ℕ) : ℝ) ≤
            (m : ℝ) * ((m : ℝ) + 2) →
          ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
            (m - 1 : ℕ) +
              dirichletWeight sigma m *
                max (L : ℝ)
                  (Real.sqrt (zetaOscillationHarmonicBound t m
                    (Nat.floor (2 * t) + 1 - m) L)) +
              ‖(2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
                (((sigma : ℂ) + I * t) - 1)‖ +
              C * (2 * t) ^ (-sigma) :=
  norm_riemannZeta_strip_le_harmonic_of_scale

end ZeroFreeRegion.VinogradovKorobov
