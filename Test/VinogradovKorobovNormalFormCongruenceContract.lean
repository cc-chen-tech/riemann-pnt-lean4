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

example {s : ℕ} (p c k r a γ M : ℕ) (hp : p ≠ 0)
    (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (hspacing : M ≤ c + a) (htail : M ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H χ θ : Fin r → Polynomial ℤ)
    (hH : ∀ i : Fin r,
      H i =
        Polynomial.C
              ((ω * (p : ℤ) ^ γ) ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
          Polynomial.X ^ (r + 1) * θ i)
    (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p M H
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∀ i : Fin r, vinogradovPowerSumDifferenceInt x y (i.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ (M - (γ * (k - r) + a * r))] :=
  vinogradovNormalFormSystem_to_uniformPowerSumCongruences
    p c k r a γ M hp hrk hγa hbudget hspacing htail
      ω hω H χ θ hH x y hsystem

example {s : ℕ} (p c k r a b γ : ℕ) (hp : p ≠ 0)
    (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (hspacing : (k - r + 1) * b ≤ c + a)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H χ θ : Fin r → Polynomial ℤ)
    (hH : ∀ i : Fin r,
      H i =
        Polynomial.C
              ((ω * (p : ℤ) ^ γ) ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
          Polynomial.X ^ (r + 1) * θ i)
    (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∀ i : Fin r, vinogradovPowerSumDifferenceInt x y (i.val + 1) ≡ 0
      [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] :=
  vinogradovNormalFormSystem_to_farScale
    p c k r a b γ hp hrk hγa hbudget hspacing htail
      ω hω H χ θ hH x y hsystem

end ZeroFreeRegion.VinogradovKorobov
