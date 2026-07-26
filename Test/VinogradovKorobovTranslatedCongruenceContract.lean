import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedCongruence

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

example (ξ t : ℤ) (φ : Polynomial ℤ) :
    (vinogradovCenteredTaylor ξ φ).eval t =
      φ.eval (t + ξ) - φ.eval ξ :=
  eval_vinogradovCenteredTaylor ξ φ t

example {s : ℕ} (ξ : ℤ) (φ : Polynomial ℤ) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference (vinogradovCenteredTaylor ξ φ) x y =
      vinogradovPolynomialSumDifference φ
        (fun i ↦ x i + ξ) (fun i ↦ y i + ξ) :=
  vinogradovPolynomialSumDifference_centeredTaylor ξ φ x y

example {s : ℕ} (q : ℤ) (D : ℕ) (θ : Polynomial ℤ)
    (x y : Fin s → ℤ) :
    q ^ D ∣ vinogradovPolynomialSumDifference
      (Polynomial.X ^ D * θ) (fun i ↦ q * x i) (fun i ↦ q * y i) :=
  dvd_vinogradovPolynomialSumDifference_scaledTail q D θ x y

example {s r : ℕ} (ξ q : ℤ) (n : ℕ) (Ω : Fin r → ℤ)
    (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference
        (∑ j : Fin r,
          Polynomial.C (ξ ^ (n - (j.val + 1)) * Ω j) *
            Polynomial.X ^ (j.val + 1))
        (fun i ↦ q * x i) (fun i ↦ q * y i) =
      ∑ j : Fin r,
        ξ ^ (n - (j.val + 1)) * Ω j * q ^ (j.val + 1) *
          vinogradovPowerSumDifferenceInt x y (j.val + 1) :=
  vinogradovPolynomialSumDifference_taylorMain ξ q n Ω x y

example {s r : ℕ} (p c k : ℕ) (hc : 0 < c) (hrk : r ≤ k)
    (ψ : Fin r → Polynomial ℤ) (ξ q : ℤ) (x y : Fin s → ℤ) :
    ∃ Ω : Matrix (Fin r) (Fin r) ℤ, ∃ E : Fin r → ℤ,
      IsVinogradovBinomialCoefficientMatrix p k r Ω ∧
      ∀ i,
        vinogradovPolynomialSumDifference
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r i) (ψ i))
            (fun z ↦ ξ + q * x z) (fun z ↦ ξ + q * y z) =
          (∑ j : Fin r,
            ξ ^ (vinogradovBinomialPoint k r i - (j.val + 1)) *
              Ω i j * q ^ (j.val + 1) *
                vinogradovPowerSumDifferenceInt x y (j.val + 1)) +
            q ^ (r + 1) * E i :=
  exists_vinogradovTranslatedSpacedSystem_sumDifference
    (r := r) p c k hc hrk ψ ξ q x y

end ZeroFreeRegion.VinogradovKorobov
