import ZeroFreeRegion.VinogradovKorobov.VinogradovHighDegreeExpansion
import Mathlib.Data.ZMod.Units

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The residual coefficient matrix left after the common prime-power
column scales have been removed from a translated spaced system. -/
def vinogradovUnitTwistedBinomialIntMatrix
    (k r : ℕ) (ω : ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j ↦
    ω ^ (k - (j.val + 1)) *
      (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ)

/-- The twist is diagonal by columns: it does not change the binomial
matrix except by multiplying each column by a power of `ω`. -/
theorem vinogradovUnitTwistedBinomialIntMatrix_eq_mul_diagonal
    (k r : ℕ) (ω : ℤ) :
    vinogradovUnitTwistedBinomialIntMatrix k r ω =
      vinogradovPureBinomialIntMatrix k r *
        Matrix.diagonal (fun j : Fin r ↦ ω ^ (k - (j.val + 1))) := by
  classical
  ext i j
  simp only [vinogradovUnitTwistedBinomialIntMatrix,
    vinogradovPureBinomialIntMatrix, Matrix.of_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro x _ hxj
    simp [Matrix.diagonal_apply_ne _ hxj]
  · simp

/-- If `ω` is coprime to `p`, the column twist is by units modulo every
positive prime power. Hence the translated residual matrix remains
invertible modulo `p^M`. -/
theorem isUnit_det_vinogradovUnitTwistedBinomialIntMatrix
    (p k r M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) :
    IsUnit
      (Matrix.of (fun i j ↦
        (vinogradovUnitTwistedBinomialIntMatrix k r ω i j :
          ZMod (p ^ M)))).det := by
  let B : Matrix (Fin r) (Fin r) (ZMod (p ^ M)) :=
    Matrix.of fun i j ↦
      (vinogradovPureBinomialIntMatrix k r i j : ZMod (p ^ M))
  let D : Matrix (Fin r) (Fin r) (ZMod (p ^ M)) :=
    Matrix.diagonal fun j : Fin r ↦
      (ω : ZMod (p ^ M)) ^ (k - (j.val + 1))
  have hfactor :
      Matrix.of (fun i j ↦
          (vinogradovUnitTwistedBinomialIntMatrix k r ω i j :
            ZMod (p ^ M))) =
        B * D := by
    classical
    ext i j
    simp only [B, D, vinogradovUnitTwistedBinomialIntMatrix,
      vinogradovPureBinomialIntMatrix, Matrix.of_apply, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro x _ hxj
      simp [Matrix.diagonal_apply_ne _ hxj]
    · simp
  rw [hfactor, Matrix.det_mul]
  apply IsUnit.mul
  · exact isUnit_det_intMatrix_of_vinogradovBinomial_modEq
      p k r M hrk hkp hM (vinogradovPureBinomialIntMatrix k r)
        (vinogradovPureBinomialIntMatrix_isVinogradov p k r)
  · rw [show D.det = ∏ j : Fin r,
        (ω : ZMod (p ^ M)) ^ (k - (j.val + 1)) by
          simp [D, Matrix.det_diagonal]]
    rw [IsUnit.prod_univ_iff]
    intro j
    have hωM : IsCoprime ω ((p ^ M : ℕ) : ℤ) := by
      simpa only [Int.natCast_pow] using hω.symm.pow_right
    exact (ZMod.unitOfIsCoprime ω hωM).isUnit.pow _

/-- Prime-modulus form of the same result, used as the reduction test when
lifting arbitrary integer perturbations to `p^M`. -/
theorem isUnit_det_vinogradovUnitTwistedBinomialIntMatrix_mod_prime
    (p k r : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) :
    IsUnit
      (Matrix.of (fun i j ↦
        (vinogradovUnitTwistedBinomialIntMatrix k r ω i j : ZMod p))).det := by
  let B : Matrix (Fin r) (Fin r) (ZMod p) :=
    vinogradovBinomialMatrix p k r
  let D : Matrix (Fin r) (Fin r) (ZMod p) :=
    Matrix.diagonal fun j : Fin r ↦
      (ω : ZMod p) ^ (k - (j.val + 1))
  have hfactor :
      Matrix.of (fun i j ↦
          (vinogradovUnitTwistedBinomialIntMatrix k r ω i j : ZMod p)) =
        B * D := by
    classical
    ext i j
    simp only [B, D, vinogradovUnitTwistedBinomialIntMatrix,
      vinogradovBinomialMatrix, Matrix.of_apply, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Matrix.mul_apply]
    rw [Finset.sum_eq_single j]
    · simp [mul_comm]
    · intro x _ hxj
      simp [Matrix.diagonal_apply_ne _ hxj]
    · simp
  rw [hfactor, Matrix.det_mul]
  apply IsUnit.mul
  · letI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    exact isUnit_iff_ne_zero.mpr
      (det_vinogradovBinomialMatrix_zmod_ne_zero p k r hrk hkp)
  · rw [show D.det = ∏ j : Fin r,
        (ω : ZMod p) ^ (k - (j.val + 1)) by
          simp [D, Matrix.det_diagonal]]
    rw [IsUnit.prod_univ_iff]
    intro j
    exact (ZMod.unitOfIsCoprime ω hω.symm).isUnit.pow _

/-- An integer matrix congruent entrywise modulo `p` to the unit-twisted
binomial matrix is invertible modulo every positive power `p^M`. -/
theorem isUnit_det_intMatrix_of_unitTwisted_modEq
    (p k r M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : ∀ i j,
      Ω i j ≡ vinogradovUnitTwistedBinomialIntMatrix k r ω i j
        [ZMOD (p : ℤ)]) :
    IsUnit
      (Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ M)))).det := by
  apply isUnit_det_of_primePower_reduction_ne_zero p M r hM
  have hmap :
      (Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ M)))).map
          (ZMod.castHom (dvd_pow_self p hM.ne') (ZMod p)) =
        Matrix.of (fun i j ↦
          (vinogradovUnitTwistedBinomialIntMatrix k r ω i j : ZMod p)) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    have hij := (ZMod.intCast_eq_intCast_iff
      (Ω i j)
      (vinogradovUnitTwistedBinomialIntMatrix k r ω i j) p).mpr
        (hΩ i j)
    simpa only [map_intCast] using hij
  rw [hmap]
  letI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  exact
    (isUnit_det_vinogradovUnitTwistedBinomialIntMatrix_mod_prime
      p k r hrk hkp ω hω).ne_zero

/-- The exact perturbation produced by translated spaced polynomials is
therefore harmless: adding a positive power of `p` to every matrix entry
does not destroy invertibility modulo `p^M`. -/
theorem isUnit_det_unitTwisted_add_primePower_mul
    (p k r c M : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hc : 0 < c) (hM : 0 < M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (E : Matrix (Fin r) (Fin r) ℤ) :
    IsUnit
      (Matrix.of (fun i j ↦
        (vinogradovUnitTwistedBinomialIntMatrix k r ω i j +
          (p : ℤ) ^ c * E i j : ZMod (p ^ M)))).det := by
  let Ω : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j ↦
    vinogradovUnitTwistedBinomialIntMatrix k r ω i j +
      (p : ℤ) ^ c * E i j
  have hΩ : ∀ i j,
      Ω i j ≡ vinogradovUnitTwistedBinomialIntMatrix k r ω i j
        [ZMOD (p : ℤ)] := by
    intro i j
    have hp : (p : ℤ) ∣ (p : ℤ) ^ c := dvd_pow_self _ hc.ne'
    have herror :
        (p : ℤ) ^ c * E i j ≡ 0 [ZMOD (p : ℤ)] :=
      (dvd_mul_of_dvd_left hp _).modEq_zero_int
    simpa only [Ω, Matrix.of_apply, add_zero] using
      (Int.ModEq.rfl.add herror)
  simpa only [Ω, Matrix.of_apply, Int.cast_add, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast] using
    isUnit_det_intMatrix_of_unitTwisted_modEq
      p k r M hrk hkp hM ω hω Ω hΩ

end

end ZeroFreeRegion.VinogradovKorobov
