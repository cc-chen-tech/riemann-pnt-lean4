import ZeroFreeRegion.VinogradovKorobov.VinogradovScaleCancellation

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The degree-dependent scaled differences appearing before cancellation
in Wooley's far-scale congruence argument. -/
def vinogradovFarScaleDifference
    (p k r a γ : ℕ) (ω : ℤ) (d : Fin r → ℤ) (j : Fin r) : ℤ :=
  ω ^ (k - r) *
    (p : ℤ) ^ (γ * (k - r) + a * (j.val + 1)) * d j

/-- The algebraic core of the far-scale branch: a perturbed binomial system
for the scaled differences implies the unscaled degree-by-degree
congruences modulo Wooley's residual exponent `B'`. -/
theorem vinogradovBinomial_scaled_elimination_to_farScale
    (p k r a b γ : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hb : 0 < b)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : IsVinogradovBinomialCoefficientMatrix p k r Ω)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) (d : Fin r → ℤ)
    (hsystem : IsVinogradovHomogeneousCongruenceSystem
      p ((k - r + 1) * b) r Ω
        (vinogradovFarScaleDifference p k r a γ ω d)) :
    ∀ j, d j ≡ 0 [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  have hM : 0 < (k - r + 1) * b :=
    Nat.mul_pos (Nat.succ_pos _) hb
  have hscaled := vinogradovBinomial_homogeneous_elimination
    p k r ((k - r + 1) * b) hrk hkp hM Ω hΩ
      (vinogradovFarScaleDifference p k r a γ ω d) hsystem
  apply vinogradovScaledCongruences_to_farScale
    p k r a b γ (Fact.out : p.Prime).ne_zero hbudget ω hω d
  intro j
  simpa only [vinogradovFarScaleDifference] using hscaled j

end

end ZeroFreeRegion.VinogradovKorobov
