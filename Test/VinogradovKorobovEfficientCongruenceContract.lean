import ZeroFreeRegion.VinogradovKorobov.VinogradovEfficientCongruence

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example {s : ℕ} (p c k r a b γ : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hcambient : c ≤ (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (hspacing : (k - r + 1) * b ≤ c + a)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b)
        (fun row ↦
          Polynomial.C
              ((ω * (p : ℤ) ^ γ) ^
                (k - vinogradovBinomialPoint k r row)) *
            vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
              (vinogradovSpacedPolynomial p c k
                (vinogradovBinomialPoint k r row) (ψ row)))
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∀ i : Fin r, vinogradovPowerSumDifferenceInt x y (i.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] :=
  vinogradovTranslatedSpacedSystem_to_farScale
    p c k r a b γ hc hrk hkp hambient hcambient hγa
      hbudget hspacing htail ω hω ψ x y hsystem

example {s : ℕ} (p c k r a b γ : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hcambient : c ≤ (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (hspacing : (k - r + 1) * b ≤ c + a)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b)
        (fun row ↦
          vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r row) (ψ row)))
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∀ i : Fin r, vinogradovPowerSumDifferenceInt x y (i.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] :=
  vinogradovUnscaledTranslatedSpacedSystem_to_farScale
    p c k r a b γ hc hrk hkp hambient hcambient hγa
      hbudget hspacing htail ω hω ψ x y hsystem

end ZeroFreeRegion.VinogradovKorobov
