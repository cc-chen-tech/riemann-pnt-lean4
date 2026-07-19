import ZeroFreeRegion.VinogradovKorobov.VinogradovNormalFormCongruence

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Algebraic efficient-congruencing transition for the translated spaced
system. Integer row normalization converts the original system to identity
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

end ZeroFreeRegion.VinogradovKorobov
