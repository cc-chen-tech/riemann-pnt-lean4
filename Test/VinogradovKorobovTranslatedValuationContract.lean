import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedValuation

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example (p c k m γ : ℕ) (hm : m ≤ k + 1)
    (ω : ℤ) (ψ : Polynomial ℤ) :
    (p : ℤ) ^ (c + γ * (k + 1 - m)) ∣
      (p : ℤ) ^ c *
        (Polynomial.taylor (ω * (p : ℤ) ^ γ)
          (Polynomial.X ^ (k + 1) * ψ)).coeff m :=
  primePower_dvd_spacedTaylorCorrection_coeff
    p c k m γ hm ω ψ

example (p c k m a γ : ℕ) (hm : m ≤ k + 1)
    (ω : ℤ) (ψ : Polynomial ℤ) :
    (p : ℤ) ^ (c + γ * (k + 1 - m) + a * m) ∣
      ((p : ℤ) ^ c *
          (Polynomial.taylor (ω * (p : ℤ) ^ γ)
            (Polynomial.X ^ (k + 1) * ψ)).coeff m) *
        ((p : ℤ) ^ a) ^ m :=
  primePower_dvd_spacedTaylorCorrection_dilated_coeff
    p c k m a γ hm ω ψ

example (p c k n m a γ : ℕ) (hm0 : 0 < m) (hm : m ≤ k + 1)
    (ω : ℤ) (ψ : Polynomial ℤ) :
    (p : ℤ) ^ (c + γ * (k + 1 - m) + a * m) ∣
      ((vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k n ψ)).coeff m -
          (ω * (p : ℤ) ^ γ) ^ (n - m) * (n.choose m : ℤ)) *
        ((p : ℤ) ^ a) ^ m :=
  primePower_dvd_centeredSpacedCoefficientError_dilated
    p c k n m a γ hm0 hm ω ψ

example (p c k r a γ : ℕ) (hrk : r ≤ k)
    (ω : ℤ) (ψ : Fin r → Polynomial ℤ) (i j : Fin r) :
    (p : ℤ) ^
        (c + γ * (k + 1 - (j.val + 1)) + a * (j.val + 1)) ∣
      ((vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i))).coeff (j.val + 1) -
          (ω * (p : ℤ) ^ γ) ^
              (vinogradovBinomialPoint k r i - (j.val + 1)) *
            (Nat.choose (vinogradovBinomialPoint k r i)
              (j.val + 1) : ℤ)) *
        ((p : ℤ) ^ a) ^ (j.val + 1) :=
  primePower_dvd_translatedSpacedCoefficientMatrixError
    p c k r a γ hrk ω ψ i j

example (p c k r a γ : ℕ) (hrk : r ≤ k)
    (ω : ℤ) (ψ : Fin r → Polynomial ℤ) (i j : Fin r) :
    (p : ℤ) ^
        (γ * (k - (j.val + 1)) + a * (j.val + 1) + c) ∣
      ((vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i))).coeff (j.val + 1) -
          (ω * (p : ℤ) ^ γ) ^
              (vinogradovBinomialPoint k r i - (j.val + 1)) *
            (Nat.choose (vinogradovBinomialPoint k r i)
              (j.val + 1) : ℤ)) *
        ((p : ℤ) ^ a) ^ (j.val + 1) :=
  primePower_dvd_translatedSpacedCoefficientMatrixError_columnScale
    p c k r a γ hrk ω ψ i j

example (p k r a γ : ℕ) (hrk : r ≤ k)
    (ω : ℤ) (i j : Fin r) :
    (ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r i) *
        ((ω * (p : ℤ) ^ γ) ^
            (vinogradovBinomialPoint k r i - (j.val + 1)) *
          (Nat.choose (vinogradovBinomialPoint k r i)
            (j.val + 1) : ℤ)) *
        ((p : ℤ) ^ a) ^ (j.val + 1) =
      (p : ℤ) ^
          (γ * (k - (j.val + 1)) + a * (j.val + 1)) *
        (ω ^ (k - (j.val + 1)) *
          (Nat.choose (vinogradovBinomialPoint k r i)
            (j.val + 1) : ℤ)) :=
  rowScaledTranslatedMonomialCoefficient_eq_columnFactor
    p k r a γ hrk ω i j

example (p c k r a γ : ℕ) (hrk : r ≤ k)
    (ω : ℤ) (ψ : Fin r → Polynomial ℤ) (i j : Fin r) :
    ∃ E : ℤ,
      (ω * (p : ℤ) ^ γ) ^
            (k - vinogradovBinomialPoint k r i) *
          (vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i))).coeff (j.val + 1) *
          ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) *
          (ω ^ (k - (j.val + 1)) *
              (Nat.choose (vinogradovBinomialPoint k r i)
                (j.val + 1) : ℤ) +
            (p : ℤ) ^ c * E) :=
  exists_rowScaledTranslatedCoefficient_eq_columnFactor
    p c k r a γ hrk ω ψ i j

end ZeroFreeRegion.VinogradovKorobov
