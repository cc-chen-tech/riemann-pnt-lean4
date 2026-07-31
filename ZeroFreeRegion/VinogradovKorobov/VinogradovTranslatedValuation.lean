import ZeroFreeRegion.VinogradovKorobov.VinogradovPolynomialTranslation

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The translated `p^c X^(k+1) ψ` correction retains both its original
spacing factor and the center power forced by its initial degree. -/
theorem primePower_dvd_spacedTaylorCorrection_coeff
    (p c k m γ : ℕ) (hm : m ≤ k + 1)
    (ω : ℤ) (ψ : Polynomial ℤ) :
    (p : ℤ) ^ (c + γ * (k + 1 - m)) ∣
      (p : ℤ) ^ c *
        (Polynomial.taylor (ω * (p : ℤ) ^ γ)
          (Polynomial.X ^ (k + 1) * ψ)).coeff m := by
  have hcenter := pow_sub_dvd_coeff_taylor_X_pow_mul
    (k + 1) m hm ψ (ω * (p : ℤ) ^ γ)
  have hpcenter :
      (p : ℤ) ^ (γ * (k + 1 - m)) ∣
        (ω * (p : ℤ) ^ γ) ^ (k + 1 - m) := by
    rw [mul_pow, pow_mul]
    exact dvd_mul_left _ _
  rw [pow_add]
  exact mul_dvd_mul_left ((p : ℤ) ^ c) (hpcenter.trans hcenter)

/-- After the additional dilation `X ↦ p^a X`, the degree-`m` correction
coefficient gains the exact extra factor `p^(am)`. -/
theorem primePower_dvd_spacedTaylorCorrection_dilated_coeff
    (p c k m a γ : ℕ) (hm : m ≤ k + 1)
    (ω : ℤ) (ψ : Polynomial ℤ) :
    (p : ℤ) ^ (c + γ * (k + 1 - m) + a * m) ∣
      ((p : ℤ) ^ c *
          (Polynomial.taylor (ω * (p : ℤ) ^ γ)
            (Polynomial.X ^ (k + 1) * ψ)).coeff m) *
        ((p : ℤ) ^ a) ^ m := by
  have h := primePower_dvd_spacedTaylorCorrection_coeff
    p c k m γ hm ω ψ
  simpa only [pow_add, pow_mul] using
    mul_dvd_mul_right h ((p : ℤ) ^ (a * m))

/-- The error between a translated spaced-polynomial coefficient and its
translated monomial coefficient has the full correction valuation after
dilation. -/
theorem primePower_dvd_centeredSpacedCoefficientError_dilated
    (p c k n m a γ : ℕ) (hm0 : 0 < m) (hm : m ≤ k + 1)
    (ω : ℤ) (ψ : Polynomial ℤ) :
    (p : ℤ) ^ (c + γ * (k + 1 - m) + a * m) ∣
      ((vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k n ψ)).coeff m -
          (ω * (p : ℤ) ^ γ) ^ (n - m) * (n.choose m : ℤ)) *
        ((p : ℤ) ^ a) ^ m := by
  rw [coeff_vinogradovCenteredTaylor_spaced_eq
    p c k n m hm0 ψ (ω * (p : ℤ) ^ γ)]
  simpa only [add_sub_cancel_left] using
    primePower_dvd_spacedTaylorCorrection_dilated_coeff
      p c k m a γ hm ω ψ

/-- Matrix form of the dilated correction valuation for the consecutive
translated degrees `k-r+1, ..., k`. -/
theorem primePower_dvd_translatedSpacedCoefficientMatrixError
    (p c k r a γ : ℕ) (hrk : r ≤ k)
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
        ((p : ℤ) ^ a) ^ (j.val + 1) := by
  apply primePower_dvd_centeredSpacedCoefficientError_dilated
  · omega
  · omega

/-- After removing the degree-dependent column scale, every low-degree
Taylor correction still carries the original uniform spacing factor `p^c`.
This is the valuation shape needed for matrix normalization without losing
the spaced-system structure. -/
theorem primePower_dvd_translatedSpacedCoefficientMatrixError_columnScale
    (p c k r a γ : ℕ) (hrk : r ≤ k)
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
        ((p : ℤ) ^ a) ^ (j.val + 1) := by
  have hstrong := primePower_dvd_translatedSpacedCoefficientMatrixError
    p c k r a γ hrk ω ψ i j
  have hm : j.val + 1 ≤ k :=
    (Nat.succ_le_iff.mpr j.isLt).trans hrk
  have hsub : k + 1 - (j.val + 1) =
      (k - (j.val + 1)) + 1 := by omega
  have hexponent :
      γ * (k - (j.val + 1)) + a * (j.val + 1) + c ≤
        c + γ * (k + 1 - (j.val + 1)) + a * (j.val + 1) := by
    rw [hsub]
    nlinarith
  exact (pow_dvd_pow (p : ℤ) hexponent).trans hstrong

/-- Complementary row scaling aligns the translated monomial matrix by
columns. After dilation, column `m` has the exact prime-power scale
`p^(γ(k-m)+am)` and the remaining coefficient is the binomial entry times
the `p`-coprime center part. -/
theorem rowScaledTranslatedMonomialCoefficient_eq_columnFactor
    (p k r a γ : ℕ) (hrk : r ≤ k)
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
            (j.val + 1) : ℤ)) := by
  let D := vinogradovBinomialPoint k r i
  let m := j.val + 1
  have hDk : D ≤ k := by
    simp only [D, vinogradovBinomialPoint]
    omega
  have hmk : m ≤ k := by
    dsimp only [m]
    exact (Nat.succ_le_iff.mpr j.isLt).trans hrk
  by_cases hmD : m ≤ D
  · have hexponent : k - D + (D - m) = k - m := by omega
    change
      (ω * (p : ℤ) ^ γ) ^ (k - D) *
          ((ω * (p : ℤ) ^ γ) ^ (D - m) *
            (D.choose m : ℤ)) *
          ((p : ℤ) ^ a) ^ m =
        (p : ℤ) ^ (γ * (k - m) + a * m) *
          (ω ^ (k - m) * (D.choose m : ℤ))
    rw [← mul_assoc, ← pow_add, hexponent, mul_pow, ← pow_mul, ← pow_mul,
      pow_add]
    ring
  · have hDm : D < m := lt_of_not_ge hmD
    change
      (ω * (p : ℤ) ^ γ) ^ (k - D) *
          ((ω * (p : ℤ) ^ γ) ^ (D - m) *
            (D.choose m : ℤ)) *
          ((p : ℤ) ^ a) ^ m =
        (p : ℤ) ^ (γ * (k - m) + a * m) *
          (ω ^ (k - m) * (D.choose m : ℤ))
    rw [Nat.choose_eq_zero_of_lt hDm]
    simp

/-- Exact low-degree coefficient normal form after complementary row scaling
and dilation. Each column scale is factored explicitly, and the residual
coefficient matrix is the unit-twisted binomial matrix plus a `p^c`
perturbation. -/
theorem exists_rowScaledTranslatedCoefficient_eq_columnFactor
    (p c k r a γ : ℕ) (hrk : r ≤ k)
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
            (p : ℤ) ^ c * E) := by
  let ξ : ℤ := ω * (p : ℤ) ^ γ
  let D := vinogradovBinomialPoint k r i
  let m := j.val + 1
  let C := (vinogradovCenteredTaylor ξ
    (vinogradovSpacedPolynomial p c k D (ψ i))).coeff m
  let C₀ := ξ ^ (D - m) * (D.choose m : ℤ)
  let S := γ * (k - m) + a * m
  have herror : (p : ℤ) ^ (S + c) ∣
      (C - C₀) * ((p : ℤ) ^ a) ^ m := by
    simpa only [ξ, D, m, C, C₀, S] using
      primePower_dvd_translatedSpacedCoefficientMatrixError_columnScale
        p c k r a γ hrk ω ψ i j
  obtain ⟨E, hE⟩ := herror
  have hEtarget :
      (C - C₀) * ((p : ℤ) ^ a) ^ m =
        (p : ℤ) ^ S * (p : ℤ) ^ c * E := by
    exact hE.trans (by rw [pow_add])
  refine ⟨ξ ^ (k - D) * E, ?_⟩
  have hmain :
      ξ ^ (k - D) * C₀ * ((p : ℤ) ^ a) ^ m =
        (p : ℤ) ^ S *
          (ω ^ (k - m) * (D.choose m : ℤ)) := by
    simpa only [ξ, D, m, C₀, S] using
      rowScaledTranslatedMonomialCoefficient_eq_columnFactor
        p k r a γ hrk ω i j
  change
    ξ ^ (k - D) * C * ((p : ℤ) ^ a) ^ m =
      (p : ℤ) ^ S *
        (ω ^ (k - m) * (D.choose m : ℤ) +
          (p : ℤ) ^ c * (ξ ^ (k - D) * E))
  calc
    ξ ^ (k - D) * C * ((p : ℤ) ^ a) ^ m =
        ξ ^ (k - D) * C₀ * ((p : ℤ) ^ a) ^ m +
          ξ ^ (k - D) *
            ((C - C₀) * ((p : ℤ) ^ a) ^ m) := by ring
    _ = (p : ℤ) ^ S *
          (ω ^ (k - m) * (D.choose m : ℤ)) +
        ξ ^ (k - D) * ((p : ℤ) ^ S * (p : ℤ) ^ c * E) := by
          rw [hmain]
          exact congrArg
            (fun z : ℤ ↦
              (p : ℤ) ^ S *
                  (ω ^ (k - m) * (D.choose m : ℤ)) +
                ξ ^ (k - D) * z) hEtarget
    _ = (p : ℤ) ^ S *
        (ω ^ (k - m) * (D.choose m : ℤ) +
          (p : ℤ) ^ c * (ξ ^ (k - D) * E)) := by ring

end


end ZeroFreeRegion.VinogradovKorobov
