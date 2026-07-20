import ZeroFreeRegion.VinogradovKorobov.VinogradovLowerDegreeSystem

namespace ZeroFreeRegion.VinogradovKorobov

example {s : ℕ} (q A : ℤ) (H Ψ : Polynomial ℤ)
    (hfactor : vinogradovPolynomialDilation q H = Polynomial.C A * Ψ)
    (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference H
        (fun i ↦ q * x i) (fun i ↦ q * y i) =
      A * vinogradovPolynomialSumDifference Ψ x y :=
  vinogradovPolynomialSumDifference_of_dilation_factor
    q A H Ψ hfactor x y

example (q A : ℤ) (H : Polynomial ℤ)
    (hcoeff : ∀ n : ℕ, A ∣ H.coeff n * q ^ n) :
    ∃ Ψ : Polynomial ℤ,
      vinogradovPolynomialDilation q H = Polynomial.C A * Ψ :=
  exists_vinogradovPolynomialDilation_factor q A H hcoeff

example {s : ℕ} (p k r a b γ : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H Ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hfactor : ∀ i : Fin r,
      vinogradovPolynomialSumDifference (H i)
          (fun j ↦ (p : ℤ) ^ a * x j)
          (fun j ↦ (p : ℤ) ^ a * y j) =
        ω ^ (k - r) *
          (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1)) *
            vinogradovPolynomialSumDifference (Ψ i) x y)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun j ↦ (p : ℤ) ^ a * x j)
        (fun j ↦ (p : ℤ) ^ a * y j)) :
    IsVinogradovPolynomialCongruenceSystem p
      (vinogradovFarScale k r a b γ) Ψ x y :=
  vinogradovCommonFactorSystem_to_farScale
    p k r a b γ hp hbudget ω hω H Ψ x y hfactor hsystem

example {s : ℕ} (p k r a b γ : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H Ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hfactor : ∀ i : Fin r,
      vinogradovPolynomialDilation ((p : ℤ) ^ a) (H i) =
        Polynomial.C
            (ω ^ (k - r) *
              (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1))) *
          Ψ i)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun j ↦ (p : ℤ) ^ a * x j)
        (fun j ↦ (p : ℤ) ^ a * y j)) :
    IsVinogradovPolynomialCongruenceSystem p
      (vinogradovFarScale k r a b γ) Ψ x y :=
  vinogradovDilationFactorSystem_to_farScale
    p k r a b γ hp hbudget ω hω H Ψ x y hfactor hsystem

example {s : ℕ} (p k r a b γ : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (H : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hcoeff : ∀ (i : Fin r) (n : ℕ),
      ω ^ (k - r) *
          (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1)) ∣
        (H i).coeff n * ((p : ℤ) ^ a) ^ n)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun j ↦ (p : ℤ) ^ a * x j)
        (fun j ↦ (p : ℤ) ^ a * y j)) :
    ∃ Ψ : Fin r → Polynomial ℤ,
      (∀ i : Fin r,
        vinogradovPolynomialDilation ((p : ℤ) ^ a) (H i) =
          Polynomial.C
              (ω ^ (k - r) *
                (p : ℤ) ^ (γ * (k - r) + a * (i.val + 1))) *
            Ψ i) ∧
      IsVinogradovPolynomialCongruenceSystem p
        (vinogradovFarScale k r a b γ) Ψ x y :=
  exists_vinogradovLowerDegreeSystem_to_farScale_of_coeff_dvd
    p k r a b γ hp hbudget ω hω H x y hcoeff hsystem

end ZeroFreeRegion.VinogradovKorobov
