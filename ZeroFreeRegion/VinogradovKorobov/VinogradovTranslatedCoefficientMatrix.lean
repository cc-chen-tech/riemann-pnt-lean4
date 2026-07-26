import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedValuation
import ZeroFreeRegion.VinogradovKorobov.VinogradovUnitTwistedMatrix
import ZeroFreeRegion.VinogradovKorobov.VinogradovIntegralMatrixTransform
import ZeroFreeRegion.VinogradovKorobov.VinogradovLowerDegreeSystem

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Assemble the entrywise valuation witnesses into one integer coefficient
matrix.  After row scaling and dilation, column `j` has its exact common
prime-power factor, while the residual matrix is congruent modulo `p^c` to
the unit-twisted binomial matrix. -/
theorem exists_vinogradovTranslatedCoefficientMatrix
    (p c k r a γ : ℕ) (hrk : r ≤ k)
    (ω : ℤ) (ψ : Fin r → Polynomial ℤ) :
    ∃ Ω : Matrix (Fin r) (Fin r) ℤ,
      (∀ i j,
        (ω * (p : ℤ) ^ γ) ^
              (k - vinogradovBinomialPoint k r i) *
            (vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
              (vinogradovSpacedPolynomial p c k
                (vinogradovBinomialPoint k r i) (ψ i))).coeff (j.val + 1) *
            ((p : ℤ) ^ a) ^ (j.val + 1) =
          (p : ℤ) ^
              (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j) ∧
      (∀ i j,
        Ω i j ≡ vinogradovUnitTwistedBinomialIntMatrix k r ω i j
          [ZMOD (p : ℤ) ^ c]) := by
  choose E hE using fun i j ↦
    exists_rowScaledTranslatedCoefficient_eq_columnFactor
      p c k r a γ hrk ω ψ i j
  let Ω : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j ↦
    vinogradovUnitTwistedBinomialIntMatrix k r ω i j +
      (p : ℤ) ^ c * E i j
  refine ⟨Ω, ?_, ?_⟩
  · intro i j
    simpa only [Ω, Matrix.of_apply,
      vinogradovUnitTwistedBinomialIntMatrix] using hE i j
  · intro i j
    have herror :
        (p : ℤ) ^ c * E i j ≡ 0 [ZMOD (p : ℤ) ^ c] :=
      (dvd_mul_right ((p : ℤ) ^ c) (E i j)).modEq_zero_int
    simpa only [Ω, Matrix.of_apply, add_zero] using
      (Int.ModEq.rfl.add herror)

/-- Any residual coefficient matrix with the preceding `p^c` congruence is
invertible modulo `p^M`, because positive spacing implies that its reduction
modulo `p` is the unit-twisted binomial matrix. -/
theorem isUnit_det_vinogradovTranslatedCoefficientMatrix
    (p k r c M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hc : 0 < c) (hM : 0 < M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : ∀ i j,
      Ω i j ≡ vinogradovUnitTwistedBinomialIntMatrix k r ω i j
        [ZMOD (p : ℤ) ^ c]) :
    IsUnit
      (Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ M)))).det := by
  apply isUnit_det_intMatrix_of_unitTwisted_modEq
    p k r M hrk hkp hM ω hω Ω
  intro i j
  exact (hΩ i j).of_dvd (dvd_pow_self (p : ℤ) hc.ne')

/-- The assembled translated coefficient matrix admits an integer two-sided
inverse representative modulo the ambient prime power. -/
theorem exists_vinogradovTranslatedCoefficientMatrix_twoSidedInverse
    (p k r c M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hc : 0 < c) (hM : 0 < M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : ∀ i j,
      Ω i j ≡ vinogradovUnitTwistedBinomialIntMatrix k r ω i j
        [ZMOD (p : ℤ) ^ c]) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M))) *
          Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ M))) = 1 ∧
        Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ M))) *
          Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M))) = 1 := by
  apply exists_intMatrix_twoSidedInverse_mod_primePower p M r Ω
  exact isUnit_det_vinogradovTranslatedCoefficientMatrix
    p k r c M hrk hkp hc hM ω hω Ω hΩ

/-- Choose the integer inverse in the form needed by polynomial row
normalization: its product with the residual coefficient matrix is the
identity entrywise modulo `p^M`, and the inverse itself is invertible modulo
the same ambient power. -/
theorem exists_vinogradovTranslatedCoefficientMatrix_leftInverse
    (p k r c M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hc : 0 < c) (hM : 0 < M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : ∀ i j,
      Ω i j ≡ vinogradovUnitTwistedBinomialIntMatrix k r ω i j
        [ZMOD (p : ℤ) ^ c]) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      (∀ i j, (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ M]) ∧
      IsUnit
        (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det := by
  obtain ⟨B, hleft, _hright⟩ :=
    exists_vinogradovTranslatedCoefficientMatrix_twoSidedInverse
      p k r c M hrk hkp hc hM ω hω Ω hΩ
  have hentries : ∀ i j,
      (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ M] := by
    intro i j
    apply (ZMod.intCast_eq_intCast_iff
      ((B * Ω) i j) (if i = j then 1 else 0) (p ^ M)).mp
    have hij := congrArg (fun A ↦ A i j) hleft
    simpa only [Matrix.mul_apply, Matrix.of_apply, Int.cast_sum,
      Int.cast_mul, Matrix.one_apply, Int.cast_ite, Int.cast_one,
      Int.cast_zero] using hij
  have hdetEq := congrArg Matrix.det hleft
  rw [Matrix.det_mul, Matrix.det_one] at hdetEq
  refine ⟨B, hentries, ?_⟩
  exact IsUnit.of_mul_eq_one _ hdetEq

/-- Polynomial dilation and integer row combination give the expected
coefficientwise matrix sum. -/
theorem coeff_vinogradovPolynomialDilation_matrixCombination
    {r : ℕ} (q : ℤ) (B : Matrix (Fin r) (Fin r) ℤ)
    (F : Fin r → Polynomial ℤ) (i : Fin r) (n : ℕ) :
    (vinogradovPolynomialDilation q
      (vinogradovPolynomialMatrixCombination B F i)).coeff n =
      ∑ row : Fin r, B i row * ((F row).coeff n * q ^ n) := by
  simp only [vinogradovPolynomialDilation,
    Polynomial.comp_C_mul_X_coeff,
    vinogradovPolynomialMatrixCombination]
  rw [Polynomial.finset_sum_coeff, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro row _
  simp only [Polynomial.coeff_C_mul]
  ring

/-- Applying an integer row matrix to the translated rows and then dilating
turns each low-degree coefficient into its separated column scale times the
ordinary matrix product `B * Ω`. -/
theorem coeff_vinogradovTranslatedMatrixCombination_dilation
    (p k r a γ : ℕ)
    (F : Fin r → Polynomial ℤ)
    (Ω B : Matrix (Fin r) (Fin r) ℤ)
    (hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j)
    (i j : Fin r) :
    (vinogradovPolynomialDilation ((p : ℤ) ^ a)
      (vinogradovPolynomialMatrixCombination B F i)).coeff (j.val + 1) =
      (p : ℤ) ^
          (γ * (k - (j.val + 1)) + a * (j.val + 1)) *
        (B * Ω) i j := by
  rw [coeff_vinogradovPolynomialDilation_matrixCombination]
  simp_rw [hcoeff]
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- If `B` is a left inverse of the residual matrix modulo `p^M`, the
dilated low-degree coefficients are diagonal to the corresponding enhanced
precision `p^(columnScale + M)`. -/
theorem coeff_vinogradovTranslatedMatrixCombination_dilation_modEq_identity
    (p k r a γ M : ℕ)
    (F : Fin r → Polynomial ℤ)
    (Ω B : Matrix (Fin r) (Fin r) ℤ)
    (hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j)
    (hleft : ∀ i j,
      (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ M])
    (i j : Fin r) :
    (vinogradovPolynomialDilation ((p : ℤ) ^ a)
      (vinogradovPolynomialMatrixCombination B F i)).coeff (j.val + 1) ≡
        (if i = j then
          (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1))
        else 0)
      [ZMOD (p : ℤ) ^
        (γ * (k - (j.val + 1)) + a * (j.val + 1) + M)] := by
  let S := γ * (k - (j.val + 1)) + a * (j.val + 1)
  have hscaled := (hleft i j).mul_left' (c := (p : ℤ) ^ S)
  rw [coeff_vinogradovTranslatedMatrixCombination_dilation
    p k r a γ F Ω B hcoeff i j]
  simpa only [S, pow_add, mul_ite, mul_one, mul_zero] using hscaled

/-- Under the ambient scale budget, every low-degree coefficient in
transformed row `i` is divisible by that row's distinguished column scale.
Off-diagonal coefficients acquire the extra factor `p^M` from the left
inverse congruence. -/
theorem primePower_dvd_coeff_vinogradovTranslatedMatrixCombination_dilation
    (p k r a γ M : ℕ)
    (F : Fin r → Polynomial ℤ)
    (Ω B : Matrix (Fin r) (Fin r) ℤ)
    (hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j)
    (hleft : ∀ i j,
      (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ M])
    (hrowScale : ∀ i : Fin r,
      γ * (k - (i.val + 1)) + a * (i.val + 1) ≤ M)
    (i j : Fin r) :
    (p : ℤ) ^ (γ * (k - (i.val + 1)) + a * (i.val + 1)) ∣
      (vinogradovPolynomialDilation ((p : ℤ) ^ a)
        (vinogradovPolynomialMatrixCombination B F i)).coeff (j.val + 1) := by
  rw [coeff_vinogradovTranslatedMatrixCombination_dilation
    p k r a γ F Ω B hcoeff i j]
  by_cases hij : i = j
  · subst j
    exact dvd_mul_right _ _
  · have hoff := hleft i j
    rw [if_neg hij] at hoff
    have hentry : (p : ℤ) ^ M ∣ (B * Ω) i j :=
      Int.modEq_zero_iff_dvd.mp hoff
    have hlarge :
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1) + M) ∣
          (p : ℤ) ^
              (γ * (k - (j.val + 1)) + a * (j.val + 1)) *
            (B * Ω) i j := by
      rw [pow_add]
      exact mul_dvd_mul_left _ hentry
    have hexponent :
        γ * (k - (i.val + 1)) + a * (i.val + 1) ≤
          γ * (k - (j.val + 1)) + a * (j.val + 1) + M := by
      exact (hrowScale i).trans (Nat.le_add_left M _)
    exact (pow_dvd_pow (p : ℤ) hexponent).trans hlarge

end

end ZeroFreeRegion.VinogradovKorobov
