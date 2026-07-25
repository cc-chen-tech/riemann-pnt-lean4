import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalFormEvaluation

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example {s : ℕ} (A q : ℤ) (d : ℕ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference
        (Polynomial.C A * Polynomial.X ^ d)
        (fun i ↦ q * x i) (fun i ↦ q * y i) =
      A * q ^ d * vinogradovPowerSumDifferenceInt x y d :=
  vinogradovPolynomialSumDifference_monomial_scaled A q d x y

example {s : ℕ} (p c a : ℕ) (χ : Polynomial ℤ)
    (x y : Fin s → ℤ) :
    (p : ℤ) ^ (c + a) ∣
      vinogradovPolynomialSumDifference
        (Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ)
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i) :=
  dvd_vinogradovPolynomialSumDifference_spacingTerm p c a χ x y

example {s : ℕ} (p c k r a γ d : ℕ) (hdk : d ≤ k)
    (ω : ℤ) (H χ θ : Polynomial ℤ)
    (hH : H =
      Polynomial.C ((ω * (p : ℤ) ^ γ) ^ (k - d)) *
          Polynomial.X ^ d +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ +
        Polynomial.X ^ (r + 1) * θ)
    (x y : Fin s → ℤ) :
    ∃ E₁ E₂ : ℤ,
      vinogradovPolynomialSumDifference H
          (fun i ↦ (p : ℤ) ^ a * x i)
          (fun i ↦ (p : ℤ) ^ a * y i) =
        ω ^ (k - d) *
            (p : ℤ) ^ (γ * (k - d) + a * d) *
              vinogradovPowerSumDifferenceInt x y d +
          (p : ℤ) ^ (c + a) * E₁ +
          (p : ℤ) ^ (a * (r + 1)) * E₂ :=
  exists_vinogradovPolynomialSumDifference_normalForm_evaluation
    p c k r a γ d hdk ω H χ θ hH x y

end ZeroFreeRegion.VinogradovKorobov
