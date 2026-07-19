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

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma t : ℝ,
      (1 / 4 : ℝ) ≤ sigma → sigma ≤ 2 → 1 ≤ t →
        ∀ m B depth h : ℕ,
          1 ≤ m → m ≤ Nat.floor (2 * t) + 1 → 0 < B → 1 ≤ h →
          (∀ j < (Nat.floor (2 * t) + 1 - m) / B,
            t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
              (((m + j * B : ℕ) : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) →
          (∀ j < (Nat.floor (2 * t) + 1 - m) / B, ∀ K,
            constantAProcessPrefixThreshold depth h ≤ K → K ≤ B →
              2 * Real.pi * (h : ℝ) ≤
                zetaAProcessUniformLeafDeltaLower t (m + j * B) K depth *
                  (h : ℝ) ^ depth * (K : ℝ)) →
          ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
            (m - 1 : ℕ) +
              ∑ j ∈ Finset.range ((Nat.floor (2 * t) + 1 - m) / B),
                dirichletWeight sigma (m + j * B) *
                  max (constantAProcessPrefixThreshold depth h : ℝ)
                    (6 * (1 + Real.log h) * (B : ℝ) /
                      (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) +
              ((Nat.floor (2 * t) + 1 - m) % B : ℕ) +
              ‖(2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
                (((sigma : ℂ) + I * t) - 1)‖ +
              C * (2 * t) ^ (-sigma) :=
  norm_riemannZeta_strip_le_sum_constantAProcessExplicitPower

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ sigma t : ℝ,
      (1 / 4 : ℝ) ≤ sigma → sigma ≤ 2 → 1 ≤ t →
        ∀ m B depth h : ℕ,
          1 ≤ m → m ≤ Nat.floor (2 * t) + 1 → 0 < B → 1 ≤ h →
          t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
            ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi →
          2 * Real.pi * (h : ℝ) ≤
            zetaAProcessUniformLeafDeltaLower t m
                (Nat.floor (2 * t) + 1 - m) depth *
              (h : ℝ) ^ depth *
                (constantAProcessPrefixThreshold depth h : ℝ) →
          ‖riemannZeta ((sigma : ℂ) + I * t)‖ ≤
            (m - 1 : ℕ) +
              ((Nat.floor (2 * t) + 1 - m) / B : ℕ) *
                dirichletWeight sigma m *
                  max (constantAProcessPrefixThreshold depth h : ℝ)
                    (6 * (1 + Real.log h) * (B : ℝ) /
                      (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ)) +
              ((Nat.floor (2 * t) + 1 - m) % B : ℕ) +
              ‖(2 * t : ℂ) ^ (1 - ((sigma : ℂ) + I * t)) /
                (((sigma : ℂ) + I * t) - 1)‖ +
              C * (2 * t) ^ (-sigma) :=
  norm_riemannZeta_strip_le_numBlocks_constantAProcessExplicitPower

end ZeroFreeRegion.VinogradovKorobov
