import WeilExtremalKernels.FiniteQuadraticForm

/-!
# Finite-to-cutoff-free quadratic-form transfer

This module isolates the order-theoretic step in a two-sided archimedean-tail
certificate. If a cutoff-free matrix is a finite matrix plus a nonnegative
tail bounded above by `B I`, finite positivity transfers upward, while a
finite witness below `-B` remains negative after adding the tail.

The results are generic finite-dimensional algebra. They do not construct the
archimedean tail of the Weil form or prove an analytic value for `B`.
-/

namespace WeilExtremalKernels

open scoped BigOperators

/-- Quadratic forms turn matrix addition into scalar addition. -/
theorem quadraticForm_add {n : ℕ} (A H : FiniteMatrix n) (x : FiniteVector n) :
    quadraticForm (A + H) x = quadraticForm A x + quadraticForm H x := by
  unfold quadraticForm
  simp_rw [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

/-- A nonnegative finite form remains nonnegative after adding a
nonnegative archimedean tail. -/
theorem quadraticForm_nonneg_add_of_tail_nonneg {n : ℕ}
    (A H : FiniteMatrix n)
    (hA : ∀ x, 0 ≤ quadraticForm A x)
    (hH : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, 0 ≤ quadraticForm (A + H) x := by
  intro x
  rw [quadraticForm_add]
  exact add_nonneg (hA x) (hH x)

/-- A positive finite form remains positive on nonzero vectors after adding
a nonnegative archimedean tail. -/
theorem quadraticForm_pos_add_of_tail_nonneg {n : ℕ}
    (A H : FiniteMatrix n)
    (hA : ∀ x, x ≠ 0 → 0 < quadraticForm A x)
    (hH : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, x ≠ 0 → 0 < quadraticForm (A + H) x := by
  intro x hx
  rw [quadraticForm_add]
  exact add_pos_of_pos_of_nonneg (hA x hx) (hH x)

/-- The negative half of the two-sided tail rule. If a finite quadratic
value lies strictly below the full tail budget `B * ‖x‖²`, adding any tail
within that budget leaves a strictly negative value. -/
theorem quadraticForm_neg_add_of_tail_upper {n : ℕ}
    (A H : FiniteMatrix n) (x : FiniteVector n) (B : ℝ)
    (hfinite : quadraticForm A x < -B * squaredNorm x)
    (htail : quadraticForm H x ≤ B * squaredNorm x) :
    quadraticForm (A + H) x < 0 := by
  rw [quadraticForm_add]
  linarith

/-- Quantitative lower-bound transfer from a symmetric entrywise interval
enclosure. This retains the margin `μ - ρ` instead of discarding it after
proving nonnegativity. -/
theorem quadraticForm_lower_of_interval {n : ℕ}
    (A C R : FiniteMatrix n) (x : FiniteVector n) (μ ρ : ℝ)
    (hcenter : ∀ y, μ * squaredNorm y ≤ quadraticForm C y)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) :
    (μ - ρ) * squaredNorm x ≤ quadraticForm A x := by
  have hperturb :=
    abs_quadraticForm_sub_le_rowBound A C R x ρ hR hentry hrow
  have hnegative :=
    neg_abs_le (quadraticForm A x - quadraticForm C x)
  linarith [hcenter x]

/-- The positive half of the finite-to-cutoff-free rule, including the
entrywise interval budget used to certify the finite matrix. -/
theorem quadraticForm_nonneg_of_interval_and_tail {n : ℕ}
    (A C R H : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ)
    (hbudget : ρ ≤ μ)
    (htail : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, 0 ≤ quadraticForm (A + H) x :=
  quadraticForm_nonneg_add_of_tail_nonneg A H
    (quadraticForm_nonneg_of_interval
      A C R μ ρ hcenter hR hentry hrow hbudget)
    htail

/-- Strict finite interval slack remains strict after adding a nonnegative
tail. -/
theorem quadraticForm_pos_of_interval_and_tail {n : ℕ}
    (A C R H : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ)
    (hbudget : ρ < μ)
    (htail : ∀ x, 0 ≤ quadraticForm H x) :
    ∀ x, x ≠ 0 → 0 < quadraticForm (A + H) x :=
  quadraticForm_pos_add_of_tail_nonneg A H
    (quadraticForm_pos_of_interval
      A C R μ ρ hcenter hR hentry hrow hbudget)
    htail

/-- Combine a finite interval budget, a nonnegative analytic tail, and a
separate symmetric-transfer error controlled directly at quadratic-form
level. The total error budget is `ρ + σ`. -/
theorem quadraticForm_nonneg_of_interval_tail_and_transfer_error {n : ℕ}
    (A C R H E : FiniteMatrix n) (μ ρ σ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ)
    (htail : ∀ x, 0 ≤ quadraticForm H x)
    (htransfer : ∀ x, |quadraticForm E x| ≤ σ * squaredNorm x)
    (hbudget : ρ + σ ≤ μ) :
    ∀ x, 0 ≤ quadraticForm (A + H + E) x := by
  intro x
  rw [quadraticForm_add, quadraticForm_add]
  have hA :=
    quadraticForm_lower_of_interval A C R x μ ρ hcenter hR hentry hrow
  have hEnegative := neg_abs_le (quadraticForm E x)
  have hElower : -σ * squaredNorm x ≤ quadraticForm E x := by
    linarith [htransfer x]
  have hmargin : 0 ≤ (μ - ρ - σ) * squaredNorm x :=
    mul_nonneg (by linarith) (squaredNorm_nonneg x)
  linarith [htail x]

end WeilExtremalKernels
