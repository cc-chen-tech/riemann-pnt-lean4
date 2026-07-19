import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalFormCongruence

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example {s : ℕ} (p c k r a γ d M : ℕ) (hp : p ≠ 0) (hdk : d ≤ k)
    (hmain : γ * (k - d) + a * d ≤ M)
    (hspacing : M ≤ c + a) (htail : M ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H χ θ : Polynomial ℤ)
    (hH : H =
      Polynomial.C ((ω * (p : ℤ) ^ γ) ^ (k - d)) *
          Polynomial.X ^ d +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ +
        Polynomial.X ^ (r + 1) * θ)
    (x y : Fin s → ℤ)
    (hcong :
      vinogradovPolynomialSumDifference H
          (fun i ↦ (p : ℤ) ^ a * x i)
          (fun i ↦ (p : ℤ) ^ a * y i) ≡ 0
        [ZMOD (p : ℤ) ^ M]) :
    vinogradovPowerSumDifferenceInt x y d ≡ 0
      [ZMOD (p : ℤ) ^ (M - (γ * (k - d) + a * d))] :=
  vinogradovPowerSumDifferenceInt_modEq_of_normalForm
    p c k r a γ d M hp hdk hmain hspacing htail
      ω hω H χ θ hH x y hcong

end ZeroFreeRegion.VinogradovKorobov
