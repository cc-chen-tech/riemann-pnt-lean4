import WeilExtremalKernels.ArchimedeanTailTransfer

/-!
# Exact basis-change transfer for finite Weil matrices

This module formalizes the algebraic contract required when a certified
matrix is expressed in coordinates different from the paper's registered
Fourier coordinates.

For a rectangular matrix `B : R^m -> R^n`, the pulled-back matrix is
`B^T A B`.  Its quadratic form is exactly the quadratic form of `A` at `B y`.
Consequently:

* nonnegativity transfers through every rectangular embedding;
* strict positivity transfers only when the embedding has trivial kernel;
* an explicit left inverse is a checkable sufficient certificate for that
  trivial-kernel condition.

These results do not construct the concrete Weil change-of-basis matrix.
That matrix, its coordinate convention, and its exact left inverse must be
supplied by an analytic or generated certificate.
-/

namespace WeilExtremalKernels

open scoped BigOperators

/-- A real matrix representing a linear map from `R^columns` to `R^rows`. -/
abbrev RectangularMatrix (rows columns : ℕ) :=
  Matrix (Fin rows) (Fin columns) ℝ

/-- Entrywise matrix-vector multiplication for a rectangular matrix. -/
def applyRectangularMatrix {rows columns : ℕ}
    (B : RectangularMatrix rows columns)
    (x : FiniteVector columns) : FiniteVector rows :=
  fun i => ∑ j, B i j * x j

/-- The exact pullback `B^T A B`, written entrywise. -/
def congruenceMatrix {rows columns : ℕ}
    (A : FiniteMatrix rows)
    (B : RectangularMatrix rows columns) : FiniteMatrix columns :=
  fun i j => ∑ k, ∑ l, B k i * A k l * B l j

/-- Quadratic forms commute exactly with rectangular congruence. -/
theorem quadraticForm_congruenceMatrix {rows columns : ℕ}
    (A : FiniteMatrix rows)
    (B : RectangularMatrix rows columns)
    (x : FiniteVector columns) :
    quadraticForm (congruenceMatrix A B) x =
      quadraticForm A (applyRectangularMatrix B x) := by
  unfold quadraticForm congruenceMatrix applyRectangularMatrix
  calc
    (∑ i, ∑ j, x i *
          (∑ k, ∑ l, B k i * A k l * B l j) * x j) =
        ∑ i, ∑ j, ∑ k, ∑ l,
          x i * (B k i * A k l * B l j) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp_rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ k, ∑ j, ∑ l,
          x i * (B k i * A k l * B l j) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, ∑ l,
          x i * (B k i * A k l * B l j) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ l, ∑ j,
          x i * (B k i * A k l * B l j) * x j := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ∑ i, ∑ j,
          x i * (B k i * A k l * B l j) * x j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ l,
          (∑ i, B k i * x i) * A k l *
            (∑ j, B l j * x j) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      calc
        (∑ i, ∑ j,
            x i * (B k i * A k l * B l j) * x j) =
            ∑ i, ∑ j,
              (B k i * x i) * (A k l * (B l j * x j)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = (∑ i, B k i * x i) *
            (∑ j, A k l * (B l j * x j)) := by
          rw [Fintype.sum_mul_sum]
        _ = (∑ i, B k i * x i) * A k l *
            (∑ j, B l j * x j) := by
          rw [← Finset.mul_sum]
          ring

/-- A proof-carrying left inverse for a rectangular basis embedding. -/
structure LeftInverseCertificate {rows columns : ℕ}
    (B : RectangularMatrix rows columns) where
  leftInverse : RectangularMatrix columns rows
  left_inverse :
    ∀ x : FiniteVector columns,
      applyRectangularMatrix leftInverse
          (applyRectangularMatrix B x) = x

/-- A certified left inverse implies that the basis embedding has zero kernel. -/
theorem applyRectangularMatrix_ne_zero_of_leftInverseCertificate
    {rows columns : ℕ}
    {B : RectangularMatrix rows columns}
    (certificate : LeftInverseCertificate B)
    {x : FiniteVector columns} (hx : x ≠ 0) :
    applyRectangularMatrix B x ≠ 0 := by
  intro hzero
  apply hx
  rw [← certificate.left_inverse x, hzero]
  funext i
  simp [applyRectangularMatrix]

/-- Positive semidefiniteness transfers through every exact rectangular
congruence, including a full-to-even contraction. -/
theorem quadraticForm_congruenceMatrix_nonneg {rows columns : ℕ}
    (A : FiniteMatrix rows)
    (B : RectangularMatrix rows columns)
    (hA : ∀ y, 0 ≤ quadraticForm A y) :
    ∀ x, 0 ≤ quadraticForm (congruenceMatrix A B) x := by
  intro x
  rw [quadraticForm_congruenceMatrix]
  exact hA (applyRectangularMatrix B x)

/-- Strict positivity transfers through a congruence only when a left-inverse
certificate proves that no nonzero coordinate vector is collapsed. -/
theorem quadraticForm_congruenceMatrix_pos {rows columns : ℕ}
    (A : FiniteMatrix rows)
    (B : RectangularMatrix rows columns)
    (certificate : LeftInverseCertificate B)
    (hA : ∀ y, y ≠ 0 → 0 < quadraticForm A y) :
    ∀ x, x ≠ 0 → 0 < quadraticForm (congruenceMatrix A B) x := by
  intro x hx
  rw [quadraticForm_congruenceMatrix]
  exact hA (applyRectangularMatrix B x)
    (applyRectangularMatrix_ne_zero_of_leftInverseCertificate certificate hx)

/-- Congruence is additive. This lets finite, tail, and transfer-error
matrices be transformed without changing their bookkeeping. -/
theorem congruenceMatrix_add {rows columns : ℕ}
    (A H : FiniteMatrix rows)
    (B : RectangularMatrix rows columns) :
    congruenceMatrix (A + H) B =
      congruenceMatrix A B + congruenceMatrix H B := by
  funext i j
  unfold congruenceMatrix
  simp_rw [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

/-- A nonnegative cutoff-free tail remains nonnegative after any exact basis
embedding. -/
theorem quadraticForm_congruenceMatrix_add_tail_nonneg
    {rows columns : ℕ}
    (A H : FiniteMatrix rows)
    (B : RectangularMatrix rows columns)
    (hA : ∀ y, 0 ≤ quadraticForm A y)
    (hH : ∀ y, 0 ≤ quadraticForm H y) :
    ∀ x,
      0 ≤ quadraticForm
        (congruenceMatrix (A + H) B) x := by
  exact quadraticForm_congruenceMatrix_nonneg
    (A + H) B
    (quadraticForm_nonneg_add_of_tail_nonneg A H hA hH)

/-- An exact LDL certificate and a nonnegative tail can be transported
through a separately certified coordinate embedding. -/
theorem quadraticForm_congruenceMatrix_add_tail_nonneg_of_certificate
    {rows columns : ℕ}
    (A H : FiniteMatrix rows)
    (B : RectangularMatrix rows columns)
    (certificate : LDLCertificate rows)
    (hreconstruct : A = certificate.reconstruct)
    (hdiagonal : ∀ k, 0 ≤ certificate.diagonal k)
    (hH : ∀ y, 0 ≤ quadraticForm H y) :
    ∀ x,
      0 ≤ quadraticForm
        (congruenceMatrix (A + H) B) x := by
  exact quadraticForm_congruenceMatrix_add_tail_nonneg
    A H B
    (quadraticForm_nonneg_of_certificate
      A certificate hreconstruct hdiagonal)
    hH

end WeilExtremalKernels
