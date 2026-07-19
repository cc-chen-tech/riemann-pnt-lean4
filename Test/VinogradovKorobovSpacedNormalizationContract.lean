import ZeroFreeRegion.VinogradovKorobov.VinogradovSpacedNormalization

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example {r : ℕ} (p c k n : ℕ) (hnk : n ≤ k) (ξ : ℤ)
    (Ω : Fin r → ℤ) (P θ : Polynomial ℤ)
    (hΩ : ∀ j, Ω j ≡ (n.choose (j.val + 1) : ℤ)
      [ZMOD (p : ℤ) ^ c])
    (hP : P =
      (∑ j : Fin r,
        Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
          Polynomial.X ^ (j.val + 1)) +
        Polynomial.X ^ (r + 1) * θ)
    (hrk : r ≤ k) :
    ∃ χ θ' : Polynomial ℤ,
      Polynomial.C (ξ ^ (k - n)) * P =
        vinogradovAlignedSpacedMain ξ k Ω +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ +
          Polynomial.X ^ (r + 1) * θ' :=
  exists_vinogradovRowScaledSpacedNormalForm
    p c k n hnk ξ Ω P θ hΩ hP hrk

example (p c k r : ℕ) (hc : 0 < c) (hrk : r ≤ k)
    (ψ : Fin r → Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : Matrix (Fin r) (Fin r) ℤ,
      ∃ χ θ : Fin r → Polynomial ℤ,
      (∀ i j, Ω i j ≡
        (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ)
          [ZMOD (p : ℤ) ^ c]) ∧
      IsVinogradovBinomialCoefficientMatrix p k r Ω ∧
      ∀ i,
        Polynomial.C
            (ξ ^ (k - vinogradovBinomialPoint k r i)) *
            vinogradovCenteredTaylor ξ
              (vinogradovSpacedPolynomial p c k
                (vinogradovBinomialPoint k r i) (ψ i)) =
          vinogradovAlignedSpacedMain ξ k (Ω i) +
            Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
            Polynomial.X ^ (r + 1) * θ i :=
  exists_vinogradovTranslatedSpacedSystem_normalForm
    p c k r hc hrk ψ ξ

end ZeroFreeRegion.VinogradovKorobov
