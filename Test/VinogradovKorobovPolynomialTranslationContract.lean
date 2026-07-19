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

example (r : ℕ) (ξ : ℤ) (φ : Polynomial ℤ) :
    ∃ θ : Polynomial ℤ,
      vinogradovCenteredTaylor ξ φ =
        vinogradovCenteredTaylorTruncation r ξ φ +
          Polynomial.X ^ (r + 1) * θ :=
  exists_vinogradovCenteredTaylor_eq_truncation_add_tail r ξ φ

end ZeroFreeRegion.VinogradovKorobov
