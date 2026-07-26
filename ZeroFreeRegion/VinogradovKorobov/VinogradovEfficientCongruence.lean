import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalFormCongruence

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Algebraic efficient-congruencing transition for the row-scaled translated
spaced system. Integer row normalization converts this system to identity
normal form; the spacing and Taylor errors then disappear at the ambient
scale, leaving the low-degree power sums modulo `vinogradovFarScale`.

This is the congruence-system core of Wooley's equations (7.10)--(7.12), not
the subsequent mean-value inequality or its induction. -/
theorem vinogradovTranslatedSpacedSystem_to_farScale
    {s : ℕ} (p c k r a b γ : ℕ) [Fact p.Prime]
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
      [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  let ξ : ℤ := ω * (p : ℤ) ^ γ
  let F : Fin r → Polynomial ℤ := fun row ↦
    Polynomial.C (ξ ^ (k - vinogradovBinomialPoint k r row)) *
      vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k
          (vinogradovBinomialPoint k r row) (ψ row))
  obtain ⟨B, χ, θ, _hdet, hnormal, hsystemIff⟩ :=
    exists_vinogradovTranslatedSpacedSystem_identityNormalForm
      p c k r ((k - r + 1) * b) hc hrk hkp hambient hcambient ψ ξ
  let H : Fin r → Polynomial ℤ :=
    vinogradovPolynomialMatrixCombination B F
  have hH : ∀ i : Fin r,
      H i =
        Polynomial.C
              ((ω * (p : ℤ) ^ γ) ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
          Polynomial.X ^ (r + 1) * θ i := by
    intro i
    simpa only [H, F, ξ] using hnormal i
  have htransformed :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b) H
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i) := by
    apply (hsystemIff
      (fun i ↦ (p : ℤ) ^ a * x i)
      (fun i ↦ (p : ℤ) ^ a * y i)).mpr
    simpa only [F, ξ] using hsystem
  exact vinogradovNormalFormSystem_to_farScale
    p c k r a b γ (Fact.out : p.Prime).ne_zero hrk hγa
      hbudget hspacing htail ω hω H χ θ hH x y htransformed

end

/-- Multiplying each congruence row by its complementary center power is a
valid one-way passage from the unscaled translated system to the column-
aligned system used by matrix normalization. No inverse implication is
asserted because the center need not be a unit modulo the ambient prime
power. -/
theorem isVinogradovPolynomialCongruenceSystem_translated_rowScale
    {s : ℕ} (p c M k r : ℕ) (ξ : ℤ)
    (ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p M
        (fun row ↦
          vinogradovCenteredTaylor ξ
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r row) (ψ row))) x y) :
    IsVinogradovPolynomialCongruenceSystem p M
      (fun row ↦
        Polynomial.C
            (ξ ^ (k - vinogradovBinomialPoint k r row)) *
          vinogradovCenteredTaylor ξ
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r row) (ψ row))) x y := by
  intro row
  rw [vinogradovPolynomialSumDifference_C_mul]
  simpa only [mul_zero] using
    (hsystem row).mul_left
      (ξ ^ (k - vinogradovBinomialPoint k r row))

/-- Unscaled entry point for the strong-error-vanishing branch. A translated
spaced system of the form occurring in (7.10) first passes to the row-scaled
system, then through integer matrix normalization and prime-power
cancellation. -/
theorem vinogradovUnscaledTranslatedSpacedSystem_to_farScale
    {s : ℕ} (p c k r a b γ : ℕ) [Fact p.Prime]
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
      [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  have hscaled :=
    isVinogradovPolynomialCongruenceSystem_translated_rowScale
      p c ((k - r + 1) * b) k r (ω * (p : ℤ) ^ γ) ψ
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i) hsystem
  exact vinogradovTranslatedSpacedSystem_to_farScale
    p c k r a b γ hc hrk hkp hambient hcambient hγa
      hbudget hspacing htail ω hω ψ x y hscaled

end ZeroFreeRegion.VinogradovKorobov
