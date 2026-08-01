import HardyTheorem.SelbergSqrtZetaSignedRationalReducedPairEnergy

/-!
# Arithmetic weights for the reduced-pair complete main term

The complete contribution on a coprime ray is already an exact signed sum:
the four logarithmic pieces have recombined into the two full taper factors.
Consequently this file does not apply coefficientwise absolute values or a
ray-cardinality Cauchy estimate.

Instead, it normalizes the remaining geometric weight exactly.  For a
positive reduced pair `(a,b)`,

`(X * min (a*N) b + 1) / (a*b)`

is the minimum of a denominator budget and a numerator budget.  The complete
signed ray sum stays inside one square throughout the pointwise identity and
both global consequences.
-/

open scoped BigOperators

namespace HardyTheorem

/-- Exact two-coordinate normalization of the complete-ray weight.  No
estimate is made on the signed complete term itself. -/
theorem
    selbergSqrtZetaSignedReducedRayCompleteWeight_eq_min_coordinateWeights
    {N X a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((X * min (a * N) b + 1 : ℕ) : ℝ) *
          ((((a * b : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X a b) ^ 2) =
      (min
          (((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹))
          ((X : ℝ) * ((a : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹))) *
        (selbergSqrtZetaSignedReducedRayCompleteTerm N X a b) ^ 2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  by_cases h : a * N ≤ b
  · have hratio : (N : ℝ) / b ≤ 1 / a := by
      apply (div_le_div_iff₀ hbR haR).2
      norm_num
      exact_mod_cast (show N * a ≤ b by simpa [Nat.mul_comm] using h)
    have hcoordinate :
        (((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹)) ≤
          ((X : ℝ) * ((a : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹)) := by
      have hbase :
          ((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) ≤
            (X : ℝ) * ((a : ℝ)⁻¹) := by
        calc
        ((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) =
            (X : ℝ) * ((N : ℝ) / b) := by
              push_cast
              rw [div_eq_mul_inv]
              ring
        _ ≤ (X : ℝ) * (1 / a) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = (X : ℝ) * ((a : ℝ)⁻¹) := by rw [one_div]
      simpa [add_comm] using
        add_le_add_right hbase (((a * b : ℕ) : ℝ)⁻¹)
    have hweight :
        ((X * (a * N) + 1 : ℕ) : ℝ) *
            (((a * b : ℕ) : ℝ)⁻¹) =
          ((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹) := by
      push_cast
      field_simp [haR.ne', hbR.ne']
    rw [Nat.min_eq_left h, min_eq_left hcoordinate]
    calc
      ((X * (a * N) + 1 : ℕ) : ℝ) *
            ((((a * b : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm N X a b) ^ 2) =
          (((X * (a * N) + 1 : ℕ) : ℝ) *
              (((a * b : ℕ) : ℝ)⁻¹)) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X a b) ^ 2 := by
              ring
      _ = _ := by rw [hweight]
  · have h' : b ≤ a * N := Nat.le_of_not_ge h
    have hratio : (1 : ℝ) / a ≤ N / b := by
      apply (div_le_div_iff₀ haR hbR).2
      norm_num
      exact_mod_cast (show b ≤ N * a by simpa [Nat.mul_comm] using h')
    have hcoordinate :
        ((X : ℝ) * ((a : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹)) ≤
          (((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹)) := by
      have hbase :
          (X : ℝ) * ((a : ℝ)⁻¹) ≤
            ((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) := by
        calc
        (X : ℝ) * ((a : ℝ)⁻¹) =
            (X : ℝ) * (1 / a) := by rw [one_div]
        _ ≤ (X : ℝ) * ((N : ℝ) / b) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = ((X * N : ℕ) : ℝ) * ((b : ℝ)⁻¹) := by
          push_cast
          rw [div_eq_mul_inv]
          ring
      simpa [add_comm] using
        add_le_add_right hbase (((a * b : ℕ) : ℝ)⁻¹)
    have hweight :
        ((X * b + 1 : ℕ) : ℝ) *
            (((a * b : ℕ) : ℝ)⁻¹) =
          (X : ℝ) * ((a : ℝ)⁻¹) +
            (((a * b : ℕ) : ℝ)⁻¹) := by
      push_cast
      field_simp [haR.ne', hbR.ne']
    rw [Nat.min_eq_right h', min_eq_right hcoordinate]
    calc
      ((X * b + 1 : ℕ) : ℝ) *
            ((((a * b : ℕ) : ℝ)⁻¹) *
              (selbergSqrtZetaSignedReducedRayCompleteTerm N X a b) ^ 2) =
          (((X * b + 1 : ℕ) : ℝ) *
              (((a * b : ℕ) : ℝ)⁻¹)) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm N X a b) ^ 2 := by
              ring
      _ = _ := by rw [hweight]

/-- The global complete main-term energy with its mixed reduced-ray weight
rewritten exactly as the minimum of the denominator and numerator coordinate
budgets.  Every complete signed scale sum remains inside one square. -/
theorem
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_eq_min_coordinateWeights
    (N X : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) =
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (min
            (((X * N : ℕ) : ℝ) * ((p.2 : ℝ)⁻¹) +
              (((p.1 * p.2 : ℕ) : ℝ)⁻¹))
            ((X : ℝ) * ((p.1 : ℝ)⁻¹) +
              (((p.1 * p.2 : ℕ) : ℝ)⁻¹))) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm
            N X p.1 p.2) ^ 2 := by
  classical
  apply Finset.sum_congr rfl
  intro p hp
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  exact
    selbergSqrtZetaSignedReducedRayCompleteWeight_eq_min_coordinateWeights
      hpFacts.1 hpFacts.2.1

/-- Dropping the minimum toward the denominator coordinate gives a global
budget without opening the signed complete ray sum. -/
theorem
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_denominatorCoordinateBudget
    (N X : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((((X * N : ℕ) : ℝ) * ((p.2 : ℝ)⁻¹) +
            (((p.1 * p.2 : ℕ) : ℝ)⁻¹)) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm
            N X p.1 p.2) ^ 2) := by
  rw [
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_eq_min_coordinateWeights]
  apply Finset.sum_le_sum
  intro p _hp
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)

/-- Dropping the minimum toward the numerator coordinate gives the symmetric
global budget, again preserving the full signed complete ray sum. -/
theorem
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_le_numeratorCoordinateBudget
    (N X : ℕ) :
    (∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        ((X * min (p.1 * N) p.2 + 1 : ℕ) : ℝ) *
          ((((p.1 * p.2 : ℕ) : ℝ)⁻¹) *
            (selbergSqrtZetaSignedReducedRayCompleteTerm
              N X p.1 p.2) ^ 2)) ≤
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        (((X : ℝ) * ((p.1 : ℝ)⁻¹) +
            (((p.1 * p.2 : ℕ) : ℝ)⁻¹)) *
          (selbergSqrtZetaSignedReducedRayCompleteTerm
            N X p.1 p.2) ^ 2) := by
  rw [
    sum_selbergSqrtZetaSignedReducedPairCompleteEnergy_eq_min_coordinateWeights]
  apply Finset.sum_le_sum
  intro p _hp
  exact mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)

end HardyTheorem
