import ZeroFreeRegion.VinogradovKorobov.VinogradovPolynomialTranslation

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example (ξ : ℤ) (φ : Polynomial ℤ) :
    (vinogradovCenteredTaylor ξ φ).coeff 0 = 0 :=
  coeff_zero_vinogradovCenteredTaylor ξ φ

example (p c k n m : ℕ) (hm : 0 < m) (ψ : Polynomial ℤ) (ξ : ℤ) :
    (vinogradovCenteredTaylor ξ
      (vinogradovSpacedPolynomial p c k n ψ)).coeff m ≡
      ξ ^ (n - m) * (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] :=
  coeff_vinogradovCenteredTaylor_spaced_modEq p c k n m hm ψ ξ

example (D m : ℕ) (hmD : m ≤ D) (ψ : Polynomial ℤ) (ξ : ℤ) :
    ξ ^ (D - m) ∣
      (Polynomial.taylor ξ (Polynomial.X ^ D * ψ)).coeff m :=
  pow_sub_dvd_coeff_taylor_X_pow_mul D m hmD ψ ξ

example (p c k n m : ℕ) (hnk : n ≤ k) (hm0 : 0 < m)
    (hmn : m ≤ n) (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : ℤ,
      (vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k n ψ)).coeff m =
          ξ ^ (n - m) * Ω ∧
        Ω ≡ (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] :=
  exists_vinogradovCenteredTaylor_spaced_coeff_factor
    p c k n m hnk hm0 hmn ψ ξ

example (p c k n m : ℕ) (hnk : n ≤ k) (hm0 : 0 < m)
    (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : ℤ,
      (vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k n ψ)).coeff m =
          ξ ^ (n - m) * Ω ∧
        Ω ≡ (n.choose m : ℤ) [ZMOD (p : ℤ) ^ c] :=
  exists_vinogradovCenteredTaylor_spaced_coeff_factor_all
    p c k n m hnk hm0 ψ ξ

example (r : ℕ) (ξ : ℤ) (φ : Polynomial ℤ) :
    ∃ θ : Polynomial ℤ,
      vinogradovCenteredTaylor ξ φ =
        vinogradovCenteredTaylorTruncation r ξ φ +
          Polynomial.X ^ (r + 1) * θ :=
  exists_vinogradovCenteredTaylor_eq_truncation_add_tail r ξ φ

example (p c k n r : ℕ) (hrn : r ≤ n) (hnk : n ≤ k)
    (ψ : Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : Fin r → ℤ, ∃ θ : Polynomial ℤ,
      (∀ i, Ω i ≡ (n.choose (i.val + 1) : ℤ)
        [ZMOD (p : ℤ) ^ c]) ∧
      vinogradovCenteredTaylor ξ
          (vinogradovSpacedPolynomial p c k n ψ) =
        (∑ i : Fin r,
          Polynomial.C (ξ ^ (n - (i.val + 1)) * Ω i) *
            Polynomial.X ^ (i.val + 1)) +
          Polynomial.X ^ (r + 1) * θ :=
  exists_vinogradovCenteredTaylor_spaced_expansion
    p c k n r hrn hnk ψ ξ

example (p c k r : ℕ) (hc : 0 < c) (hrk : r ≤ k)
    (ψ : Fin r → Polynomial ℤ) (ξ : ℤ) :
    ∃ Ω : Matrix (Fin r) (Fin r) ℤ, ∃ θ : Fin r → Polynomial ℤ,
      IsVinogradovBinomialCoefficientMatrix p k r Ω ∧
      ∀ i,
        vinogradovCenteredTaylor ξ
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i)) =
          (∑ j : Fin r,
            Polynomial.C
                (ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) *
                  Ω i j) * Polynomial.X ^ (j.val + 1)) +
            Polynomial.X ^ (r + 1) * θ i :=
  exists_vinogradovTranslatedSpacedSystemExpansion
    p c k r hc hrk ψ ξ

end ZeroFreeRegion.VinogradovKorobov
