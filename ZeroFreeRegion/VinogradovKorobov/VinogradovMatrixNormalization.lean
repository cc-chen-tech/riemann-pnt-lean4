import ZeroFreeRegion.VinogradovKorobov.VinogradovSpacedNormalization

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

theorem vinogradovPolynomialMatrixCombination_add {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℤ)
    (φ ψ : Fin r → Polynomial ℤ) (i : Fin r) :
    vinogradovPolynomialMatrixCombination B (fun j ↦ φ j + ψ j) i =
      vinogradovPolynomialMatrixCombination B φ i +
        vinogradovPolynomialMatrixCombination B ψ i := by
  unfold vinogradovPolynomialMatrixCombination
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

theorem vinogradovPolynomialMatrixCombination_mul_left {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℤ) (Q : Polynomial ℤ)
    (φ : Fin r → Polynomial ℤ) (i : Fin r) :
    vinogradovPolynomialMatrixCombination B (fun j ↦ Q * φ j) i =
      Q * vinogradovPolynomialMatrixCombination B φ i := by
  unfold vinogradovPolynomialMatrixCombination
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Integer row combinations of aligned main polynomials correspond exactly
to multiplication of their integer coefficient matrix. -/
theorem vinogradovPolynomialMatrixCombination_alignedSpacedMain {r : ℕ}
    (B Ω : Matrix (Fin r) (Fin r) ℤ)
    (ξ : ℤ) (k : ℕ) (i : Fin r) :
    vinogradovPolynomialMatrixCombination B
        (fun row ↦ vinogradovAlignedSpacedMain ξ k (Ω row)) i =
      vinogradovAlignedSpacedMain ξ k ((B * Ω) i) := by
  unfold vinogradovPolynomialMatrixCombination vinogradovAlignedSpacedMain
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [← mul_assoc, ← Polynomial.C_mul]
  rw [← Finset.sum_mul]
  congr 1
  rw [← map_sum]
  congr 1
  simp only [Matrix.mul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- Matrix combinations preserve the split between the aligned main system,
the `p^c X` spacing correction, and the `X^(r+1)` Taylor tail. -/
theorem vinogradovPolynomialMatrixCombination_spacedNormalForm {r : ℕ}
    (p c k : ℕ) (ξ : ℤ)
    (B Ω : Matrix (Fin r) (Fin r) ℤ)
    (F χ θ : Fin r → Polynomial ℤ)
    (hF : ∀ i,
      F i = vinogradovAlignedSpacedMain ξ k (Ω i) +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
        Polynomial.X ^ (r + 1) * θ i)
    (i : Fin r) :
    vinogradovPolynomialMatrixCombination B F i =
      vinogradovAlignedSpacedMain ξ k ((B * Ω) i) +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X *
          vinogradovPolynomialMatrixCombination B χ i +
        Polynomial.X ^ (r + 1) *
          vinogradovPolynomialMatrixCombination B θ i := by
  have hsplit :
      vinogradovPolynomialMatrixCombination B F i =
        vinogradovPolynomialMatrixCombination B
            (fun row ↦ vinogradovAlignedSpacedMain ξ k (Ω row)) i +
          vinogradovPolynomialMatrixCombination B
            (fun row ↦ Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ row) i +
          vinogradovPolynomialMatrixCombination B
            (fun row ↦ Polynomial.X ^ (r + 1) * θ row) i := by
    have hFfun : F = fun row ↦
        vinogradovAlignedSpacedMain ξ k (Ω row) +
          (Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ row +
            Polynomial.X ^ (r + 1) * θ row) := by
      funext row
      rw [hF]
      ring
    rw [hFfun,
      vinogradovPolynomialMatrixCombination_add,
      vinogradovPolynomialMatrixCombination_add]
    ring
  rw [hsplit,
    vinogradovPolynomialMatrixCombination_alignedSpacedMain,
    vinogradovPolynomialMatrixCombination_mul_left B
      (Polynomial.C ((p : ℤ) ^ c) * Polynomial.X) χ i,
    vinogradovPolynomialMatrixCombination_mul_left B
      (Polynomial.X ^ (r + 1)) θ i]

/-- An aligned coefficient row congruent to an identity-matrix row modulo
`p^c` is exactly its distinguished monomial plus a `p^c X` correction. -/
theorem exists_vinogradovAlignedSpacedMain_eq_identity_add_spacing {r : ℕ}
    (p c k : ℕ) (ξ : ℤ)
    (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r)
    (hA : ∀ j, A i j ≡ (if i = j then 1 else 0)
      [ZMOD (p : ℤ) ^ c]) :
    ∃ χ : Polynomial ℤ,
      vinogradovAlignedSpacedMain ξ k (A i) =
        Polynomial.C (ξ ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ := by
  choose e he using fun j : Fin r ↦
    Int.modEq_iff_add_fac.mp (hA j).symm
  let χ : Polynomial ℤ :=
    ∑ j : Fin r,
      Polynomial.C (ξ ^ (k - (j.val + 1)) * e j) *
        Polynomial.X ^ j.val
  have hterm (j : Fin r) :
      Polynomial.C (ξ ^ (k - (j.val + 1)) * A i j) *
          Polynomial.X ^ (j.val + 1) =
        (if i = j then
          Polynomial.C (ξ ^ (k - (i.val + 1))) *
            Polynomial.X ^ (i.val + 1)
        else 0) +
          Polynomial.C ((p : ℤ) ^ c) * Polynomial.X *
            (Polynomial.C (ξ ^ (k - (j.val + 1)) * e j) *
              Polynomial.X ^ j.val) := by
    rw [he j]
    split_ifs with hij
    · subst j
      simp [pow_succ]
      ring
    · simp [pow_succ]
      ring
  refine ⟨χ, ?_⟩
  unfold vinogradovAlignedSpacedMain
  calc
    (∑ j : Fin r,
        Polynomial.C (ξ ^ (k - (j.val + 1)) * A i j) *
          Polynomial.X ^ (j.val + 1)) =
      ∑ j : Fin r,
        ((if i = j then
            Polynomial.C (ξ ^ (k - (i.val + 1))) *
              Polynomial.X ^ (i.val + 1)
          else 0) +
            Polynomial.C ((p : ℤ) ^ c) * Polynomial.X *
              (Polynomial.C (ξ ^ (k - (j.val + 1)) * e j) *
                Polynomial.X ^ j.val)) := by
          apply Finset.sum_congr rfl
          intro j _
          exact hterm j
    _ = Polynomial.C (ξ ^ (k - (i.val + 1))) *
          Polynomial.X ^ (i.val + 1) +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ := by
          rw [Finset.sum_add_distrib]
          simp only [Fintype.sum_ite_eq, χ, Finset.mul_sum]

/-- Entrywise integer congruences extracted from a matrix left inverse over
`ZMod (p^M)`. -/
theorem intMatrix_mul_modEq_identity_of_cast_mul_eq_one
    (p M r : ℕ) (B Ω : Matrix (Fin r) (Fin r) ℤ)
    (hprod :
      Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M))) *
          Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ M))) = 1) :
    ∀ i j, (B * Ω) i j ≡ (if i = j then 1 else 0)
      [ZMOD (p : ℤ) ^ M] := by
  intro i j
  apply (ZMod.intCast_eq_intCast_iff
    ((B * Ω) i j) (if i = j then 1 else 0) (p ^ M)).mp
  have hij := congrArg (fun A ↦ A i j) hprod
  simpa only [Matrix.mul_apply, Matrix.of_apply, Int.cast_sum,
    Int.cast_mul, Matrix.one_apply, Int.cast_ite, Int.cast_one,
    Int.cast_zero] using hij

/-- Choose an integer inverse representative for a perturbed binomial matrix.
Its product is entrywise the identity modulo every smaller spacing exponent,
and the inverse matrix itself has unit determinant modulo the ambient power. -/
theorem exists_vinogradovBinomial_leftInverse_mod_spacing
    (p k r c M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M) (hcM : c ≤ M)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : IsVinogradovBinomialCoefficientMatrix p k r Ω) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      (∀ i j, (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ c]) ∧
      IsUnit
        (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det := by
  obtain ⟨B, hleft, _hright⟩ :=
    exists_vinogradovBinomial_intMatrix_twoSidedInverse
      p k r M hrk hkp hM Ω hΩ
  have hentriesM := intMatrix_mul_modEq_identity_of_cast_mul_eq_one
    p M r B Ω hleft
  have hentriesc : ∀ i j, (B * Ω) i j ≡ (if i = j then 1 else 0)
      [ZMOD (p : ℤ) ^ c] := by
    intro i j
    exact (hentriesM i j).of_dvd (pow_dvd_pow (p : ℤ) hcM)
  have hdetEq := congrArg Matrix.det hleft
  rw [Matrix.det_mul, Matrix.det_one] at hdetEq
  refine ⟨B, hentriesc, ?_⟩
  exact IsUnit.of_mul_eq_one _ hdetEq

/-- Paper-facing matrix normalization: after row scaling and an invertible
integer row combination, the translated consecutive high-degree system has
identity low-degree main terms, retains a `p^c X` spacing correction, and
retains an `X^(r+1)` tail. The transformed and original row-scaled
congruence systems are equivalent modulo the ambient `p^M`. -/
theorem exists_vinogradovTranslatedSpacedSystem_identityNormalForm
    (p c k r M : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hM : 0 < M) (hcM : c ≤ M)
    (ψ : Fin r → Polynomial ℤ) (ξ : ℤ) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      ∃ χ θ : Fin r → Polynomial ℤ,
      IsUnit
          (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det ∧
      (∀ i,
        vinogradovPolynomialMatrixCombination B
            (fun row ↦
              Polynomial.C
                  (ξ ^ (k - vinogradovBinomialPoint k r row)) *
                vinogradovCenteredTaylor ξ
                  (vinogradovSpacedPolynomial p c k
                    (vinogradovBinomialPoint k r row) (ψ row))) i =
          Polynomial.C (ξ ^ (k - (i.val + 1))) *
              Polynomial.X ^ (i.val + 1) +
            Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ i +
            Polynomial.X ^ (r + 1) * θ i) ∧
      ∀ {s : ℕ} (x y : Fin s → ℤ),
        IsVinogradovPolynomialCongruenceSystem p M
            (vinogradovPolynomialMatrixCombination B
              (fun row ↦
                Polynomial.C
                    (ξ ^ (k - vinogradovBinomialPoint k r row)) *
                  vinogradovCenteredTaylor ξ
                    (vinogradovSpacedPolynomial p c k
                      (vinogradovBinomialPoint k r row) (ψ row)))) x y ↔
          IsVinogradovPolynomialCongruenceSystem p M
            (fun row ↦
              Polynomial.C
                  (ξ ^ (k - vinogradovBinomialPoint k r row)) *
                vinogradovCenteredTaylor ξ
                  (vinogradovSpacedPolynomial p c k
                    (vinogradovBinomialPoint k r row) (ψ row))) x y := by
  obtain ⟨Ω, χ₀, θ₀, _hΩc, hΩ, hnormal⟩ :=
    exists_vinogradovTranslatedSpacedSystem_normalForm
      p c k r hc hrk ψ ξ
  obtain ⟨B, hBΩ, hdetB⟩ :=
    exists_vinogradovBinomial_leftInverse_mod_spacing
      p k r c M hrk hkp hM hcM Ω hΩ
  choose δ hδ using fun i : Fin r ↦
    exists_vinogradovAlignedSpacedMain_eq_identity_add_spacing
      p c k ξ (B * Ω) i (hBΩ i)
  let F : Fin r → Polynomial ℤ := fun row ↦
    Polynomial.C (ξ ^ (k - vinogradovBinomialPoint k r row)) *
      vinogradovCenteredTaylor ξ
        (vinogradovSpacedPolynomial p c k
          (vinogradovBinomialPoint k r row) (ψ row))
  let χ : Fin r → Polynomial ℤ := fun i ↦
    δ i + vinogradovPolynomialMatrixCombination B χ₀ i
  let θ : Fin r → Polynomial ℤ := fun i ↦
    vinogradovPolynomialMatrixCombination B θ₀ i
  have hFnorm : ∀ i,
      F i = vinogradovAlignedSpacedMain ξ k (Ω i) +
        Polynomial.C ((p : ℤ) ^ c) * Polynomial.X * χ₀ i +
        Polynomial.X ^ (r + 1) * θ₀ i := by
    intro i
    simpa only [F] using hnormal i
  refine ⟨B, χ, θ, hdetB, ?_, ?_⟩
  · intro i
    rw [vinogradovPolynomialMatrixCombination_spacedNormalForm
      p c k ξ B Ω F χ₀ θ₀ hFnorm i, hδ i]
    dsimp only [χ, θ, F]
    ring
  · intro s x y
    exact isVinogradovPolynomialCongruenceSystem_matrixCombination_iff
      p M B hdetB F x y

end


end ZeroFreeRegion.VinogradovKorobov
