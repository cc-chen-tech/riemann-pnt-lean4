import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite quadratic forms and exact LDL certificates

This module isolates the algebraic implication used by finite Weil-form
experiments: an exact factorization `A = L D L^T` with nonnegative diagonal
gives a nonnegative real quadratic form. It makes no assertion that a supplied
finite matrix is an analytic Weil matrix.
-/

namespace WeilExtremalKernels

open scoped BigOperators

abbrev FiniteVector (n : ℕ) := Fin n → ℝ

abbrev FiniteMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The finite real quadratic form `x^T A x`, written entrywise. -/
def quadraticForm {n : ℕ} (A : FiniteMatrix n) (x : FiniteVector n) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

/-- The squared Euclidean norm, in the same entrywise style as `quadraticForm`. -/
def squaredNorm {n : ℕ} (x : FiniteVector n) : ℝ :=
  ∑ i, (x i) ^ 2

theorem squaredNorm_nonneg {n : ℕ} (x : FiniteVector n) : 0 ≤ squaredNorm x := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

theorem squaredNorm_pos {n : ℕ} {x : FiniteVector n} (hx : x ≠ 0) :
    0 < squaredNorm x := by
  have hexists : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hexists
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, by simp [sq_pos_of_ne_zero hi]⟩

/-- The matrix reconstructed from `L` and the diagonal of `D`. -/
def ldlMatrix {n : ℕ} (L : FiniteMatrix n) (d : FiniteVector n) : FiniteMatrix n :=
  fun i j => ∑ k, L i k * d k * L j k

/-- The linear form given by column `k` of `L`. -/
def columnLinearForm {n : ℕ} (L : FiniteMatrix n) (x : FiniteVector n) (k : Fin n) : ℝ :=
  ∑ i, L i k * x i

/-- Data carried by an exact finite `LDL^T` certificate. -/
structure LDLCertificate (n : ℕ) where
  lower : FiniteMatrix n
  diagonal : FiniteVector n

/-- The exact matrix reconstructed by a certificate. -/
def LDLCertificate.reconstruct {n : ℕ} (certificate : LDLCertificate n) :
    FiniteMatrix n :=
  ldlMatrix certificate.lower certificate.diagonal

/-- An `LDL^T` quadratic form is the weighted sum of its column squares. -/
theorem quadraticForm_ldlMatrix {n : ℕ} (L : FiniteMatrix n)
    (d x : FiniteVector n) :
    quadraticForm (ldlMatrix L d) x =
      ∑ k, d k * (columnLinearForm L x k) ^ 2 := by
  unfold quadraticForm ldlMatrix columnLinearForm
  calc
    (∑ i, ∑ j, x i * (∑ k, L i k * d k * L j k) * x j) =
        ∑ i, ∑ j, ∑ k, x i * (L i k * d k * L j k) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ k, ∑ j, x i * (L i k * d k * L j k) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, x i * (L i k * d k * L j k) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k, d k * ((∑ i, L i k * x i) * ∑ j, L j k * x j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ k, d k * (∑ i, L i k * x i) ^ 2 := by
      congr 1
      funext k
      rw [pow_two]

/-- A nonnegative diagonal makes the reconstructed quadratic form nonnegative. -/
theorem quadraticForm_ldlMatrix_nonneg {n : ℕ} (L : FiniteMatrix n)
    (d x : FiniteVector n) (hdiagonal : ∀ k, 0 ≤ d k) :
    0 ≤ quadraticForm (ldlMatrix L d) x := by
  rw [quadraticForm_ldlMatrix]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hdiagonal k) (sq_nonneg _)

/-- Transfer nonnegativity from an exact certificate reconstruction to `A`. -/
theorem quadraticForm_nonneg_of_certificate {n : ℕ} (A : FiniteMatrix n)
    (certificate : LDLCertificate n)
    (hreconstruct : A = certificate.reconstruct)
    (hdiagonal : ∀ k, 0 ≤ certificate.diagonal k) :
    ∀ x, 0 ≤ quadraticForm A x := by
  intro x
  rw [hreconstruct]
  exact quadraticForm_ldlMatrix_nonneg certificate.lower certificate.diagonal x hdiagonal

/-- A symmetric entrywise perturbation radius with row sums bounded by `ρ`
controls the quadratic-form error with the same constant `ρ`. -/
theorem abs_quadraticForm_sub_le_rowBound {n : ℕ}
    (A C R : FiniteMatrix n) (x : FiniteVector n) (ρ : ℝ)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) :
    |quadraticForm A x - quadraticForm C x| ≤ ρ * squaredNorm x := by
  have hRnonneg : ∀ i j, 0 ≤ R i j := fun i j =>
    (abs_nonneg (A i j - C i j)).trans (hentry i j)
  have hcol : ∀ j, ∑ i, R i j ≤ ρ := by
    intro j
    calc
      (∑ i, R i j) = ∑ i, R j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hR i j
      _ ≤ ρ := hrow j
  have hdiff : quadraticForm A x - quadraticForm C x =
      ∑ i, ∑ j, x i * (A i j - C i j) * x j := by
    unfold quadraticForm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have habs : |quadraticForm A x - quadraticForm C x| ≤
      ∑ i, ∑ j, R i j * |x i| * |x j| := by
    rw [hdiff]
    calc
      |∑ i, ∑ j, x i * (A i j - C i j) * x j| ≤
          ∑ i, |∑ j, x i * (A i j - C i j) * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i * (A i j - C i j) * x j| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, R i j * |x i| * |x j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul]
        calc
          |x i| * |A i j - C i j| * |x j| ≤
              |x i| * R i j * |x j| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hentry i j) (abs_nonneg (x i)))
              (abs_nonneg (x j))
          _ = R i j * |x i| * |x j| := by ring
  have hpair : ∀ i j,
      R i j * |x i| * |x j| ≤
        (R i j * (x i) ^ 2 + R i j * (x j) ^ 2) / 2 := by
    intro i j
    have h := mul_le_mul_of_nonneg_left
      (two_mul_le_add_sq |x i| |x j|) (hRnonneg i j)
    rw [sq_abs, sq_abs] at h
    nlinarith
  have hfirst : (∑ i, ∑ j, R i j * (x i) ^ 2) ≤ ρ * squaredNorm x := by
    unfold squaredNorm
    calc
      (∑ i, ∑ j, R i j * (x i) ^ 2) =
          ∑ i, (∑ j, R i j) * (x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
      _ ≤ ∑ i, ρ * (x i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (x i))
      _ = ρ * ∑ i, (x i) ^ 2 := by rw [Finset.mul_sum]
  have hsecond : (∑ i, ∑ j, R i j * (x j) ^ 2) ≤ ρ * squaredNorm x := by
    unfold squaredNorm
    calc
      (∑ i, ∑ j, R i j * (x j) ^ 2) =
          ∑ j, ∑ i, R i j * (x j) ^ 2 := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, R i j) * (x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ ≤ ∑ j, ρ * (x j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg (x j))
      _ = ρ * ∑ j, (x j) ^ 2 := by rw [Finset.mul_sum]
  calc
    |quadraticForm A x - quadraticForm C x| ≤
        ∑ i, ∑ j, R i j * |x i| * |x j| := habs
    _ ≤ ∑ i, ∑ j,
        (R i j * (x i) ^ 2 + R i j * (x j) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hpair i j
    _ = ((∑ i, ∑ j, R i j * (x i) ^ 2) +
        (∑ i, ∑ j, R i j * (x j) ^ 2)) / 2 := by
      simp_rw [add_div, Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ρ * squaredNorm x := by linarith

/-- A center lower bound that dominates the symmetric interval row budget
certifies every matrix in the enclosure as positive semidefinite. -/
theorem quadraticForm_nonneg_of_interval {n : ℕ}
    (A C R : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) (hbudget : ρ ≤ μ) :
    ∀ x, 0 ≤ quadraticForm A x := by
  intro x
  have hperturb := abs_quadraticForm_sub_le_rowBound A C R x ρ hR hentry hrow
  have hlower : quadraticForm C x - ρ * squaredNorm x ≤ quadraticForm A x := by
    have := neg_abs_le (quadraticForm A x - quadraticForm C x)
    linarith
  have hnorm := squaredNorm_nonneg x
  have hmargin : 0 ≤ (μ - ρ) * squaredNorm x :=
    mul_nonneg (sub_nonneg.mpr hbudget) hnorm
  linarith [hcenter x]

/-- Strict budget slack certifies a positive quadratic form on nonzero vectors. -/
theorem quadraticForm_pos_of_interval {n : ℕ}
    (A C R : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) (hbudget : ρ < μ) :
    ∀ x, x ≠ 0 → 0 < quadraticForm A x := by
  intro x hx
  have hperturb := abs_quadraticForm_sub_le_rowBound A C R x ρ hR hentry hrow
  have hlower : quadraticForm C x - ρ * squaredNorm x ≤ quadraticForm A x := by
    have := neg_abs_le (quadraticForm A x - quadraticForm C x)
    linarith
  have hnorm := squaredNorm_pos hx
  have hmargin : 0 < (μ - ρ) * squaredNorm x :=
    mul_pos (sub_pos.mpr hbudget) hnorm
  linarith [hcenter x]

end WeilExtremalKernels
