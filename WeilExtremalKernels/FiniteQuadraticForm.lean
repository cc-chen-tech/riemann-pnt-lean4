import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
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

end WeilExtremalKernels
