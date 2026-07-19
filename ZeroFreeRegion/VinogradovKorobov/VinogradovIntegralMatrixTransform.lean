import ZeroFreeRegion.VinogradovKorobov.VinogradovSpacedPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open scoped BigOperators Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Every matrix over `ZMod n` has an entrywise integer lift. -/
theorem exists_intMatrix_cast_eq_zmodMatrix
    (n r : ℕ) (A : Matrix (Fin r) (Fin r) (ZMod n)) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      Matrix.of (fun i j ↦ (B i j : ZMod n)) = A := by
  choose B hB using fun i j ↦ ZMod.intCast_surjective (A i j)
  refine ⟨Matrix.of B, ?_⟩
  ext i j
  simpa only [Matrix.of_apply] using hB i j

/-- A matrix with unit determinant modulo `p^N` admits a two-sided integer
inverse representative modulo `p^N`. -/
theorem exists_intMatrix_twoSidedInverse_mod_primePower
    (p N r : ℕ) (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hdet : IsUnit
      (Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N)))).det) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      Matrix.of (fun i j ↦ (B i j : ZMod (p ^ N))) *
          Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N))) = 1 ∧
        Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N))) *
          Matrix.of (fun i j ↦ (B i j : ZMod (p ^ N))) = 1 := by
  let A : Matrix (Fin r) (Fin r) (ZMod (p ^ N)) :=
    Matrix.of fun i j ↦ (Ω i j : ZMod (p ^ N))
  obtain ⟨B, hB⟩ := exists_intMatrix_cast_eq_zmodMatrix
    (p ^ N) r A⁻¹
  refine ⟨B, ?_, ?_⟩
  · rw [hB]
    exact A.nonsing_inv_mul hdet
  · rw [hB]
    exact A.mul_nonsing_inv hdet

/-- Wooley's perturbed binomial coefficient matrix therefore has an
integer two-sided inverse representative modulo every positive `p^N`. -/
theorem exists_vinogradovBinomial_intMatrix_twoSidedInverse
    (p k r N : ℕ) [Fact p.Prime] (hrk : r ≤ k) (hkp : k < p)
    (hN : 0 < N) (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : IsVinogradovBinomialCoefficientMatrix p k r Ω) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      Matrix.of (fun i j ↦ (B i j : ZMod (p ^ N))) *
          Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N))) = 1 ∧
        Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N))) *
          Matrix.of (fun i j ↦ (B i j : ZMod (p ^ N))) = 1 := by
  apply exists_intMatrix_twoSidedInverse_mod_primePower p N r Ω
  exact isUnit_det_intMatrix_of_vinogradovBinomial_modEq
    p k r N hrk hkp hN Ω hΩ

/-- The polynomial family obtained by applying an integer coefficient
matrix row-by-row. -/
def vinogradovPolynomialMatrixCombination {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℤ)
    (φ : Fin r → Polynomial ℤ) (i : Fin r) : Polynomial ℤ :=
  ∑ j, Polynomial.C (B i j) * φ j

@[simp] theorem eval_vinogradovPolynomialMatrixCombination {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℤ)
    (φ : Fin r → Polynomial ℤ) (i : Fin r) (t : ℤ) :
    (vinogradovPolynomialMatrixCombination B φ i).eval t =
      ∑ j, B i j * (φ j).eval t := by
  simp [vinogradovPolynomialMatrixCombination,
    Polynomial.eval_finset_sum]

/-- Polynomial sum differences commute with integer matrix combination. -/
theorem vinogradovPolynomialSumDifference_matrixCombination {s r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℤ)
    (φ : Fin r → Polynomial ℤ) (i : Fin r) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference
        (vinogradovPolynomialMatrixCombination B φ i) x y =
      ∑ j, B i j * vinogradovPolynomialSumDifference (φ j) x y := by
  unfold vinogradovPolynomialSumDifference
  simp_rw [eval_vinogradovPolynomialMatrixCombination]
  rw [Finset.sum_comm]
  conv_lhs =>
    rhs
    rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  simp only [mul_sub]

/-- A polynomial family vanishes in all sum congruences modulo `p^N`. -/
def IsVinogradovPolynomialCongruenceSystem {s r : ℕ}
    (p N : ℕ) (φ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ) : Prop :=
  ∀ i, vinogradovPolynomialSumDifference (φ i) x y ≡ 0
    [ZMOD (p : ℤ) ^ N]

/-- Arbitrary integer linear combinations preserve a polynomial congruence
system. -/
theorem IsVinogradovPolynomialCongruenceSystem.matrixCombination {s r : ℕ}
    (p N : ℕ) (B : Matrix (Fin r) (Fin r) ℤ)
    (φ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (h : IsVinogradovPolynomialCongruenceSystem p N φ x y) :
    IsVinogradovPolynomialCongruenceSystem p N
      (vinogradovPolynomialMatrixCombination B φ) x y := by
  intro i
  rw [vinogradovPolynomialSumDifference_matrixCombination]
  simpa only [Finset.sum_const_zero] using Int.ModEq.sum
    (s := Finset.univ)
    (f := fun j ↦ B i j * vinogradovPolynomialSumDifference (φ j) x y)
    (g := fun _ ↦ 0) (by
      intro j _
      simpa only [mul_zero] using (h j).mul_left (B i j))

/-- If the matrix is invertible modulo `p^N`, taking its integer linear
combinations preserves and reflects the full polynomial congruence system. -/
theorem isVinogradovPolynomialCongruenceSystem_matrixCombination_iff
    {s r : ℕ} (p N : ℕ) (B : Matrix (Fin r) (Fin r) ℤ)
    (hdet : IsUnit
      (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ N)))).det)
    (φ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ) :
    IsVinogradovPolynomialCongruenceSystem p N
        (vinogradovPolynomialMatrixCombination B φ) x y ↔
      IsVinogradovPolynomialCongruenceSystem p N φ x y := by
  constructor
  · intro h
    let d : Fin r → ℤ := fun j ↦
      vinogradovPolynomialSumDifference (φ j) x y
    apply intMatrix_homogeneous_elimination_of_isUnit_det
      p N r B hdet d
    intro i
    rw [← vinogradovPolynomialSumDifference_matrixCombination]
    exact h i
  · exact fun h ↦ h.matrixCombination p N B φ x y

/-- Specialization of invertible polynomial-system replacement to Wooley's
perturbed binomial matrices. -/
theorem isVinogradovPolynomialCongruenceSystem_vinogradovBinomialCombination_iff
    {s : ℕ} (p k r N : ℕ) [Fact p.Prime]
    (hrk : r ≤ k) (hkp : k < p) (hN : 0 < N)
    (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : IsVinogradovBinomialCoefficientMatrix p k r Ω)
    (φ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ) :
    IsVinogradovPolynomialCongruenceSystem p N
        (vinogradovPolynomialMatrixCombination Ω φ) x y ↔
      IsVinogradovPolynomialCongruenceSystem p N φ x y := by
  apply isVinogradovPolynomialCongruenceSystem_matrixCombination_iff
  exact isUnit_det_intMatrix_of_vinogradovBinomial_modEq
    p k r N hrk hkp hN Ω hΩ

end

end ZeroFreeRegion.VinogradovKorobov
