import HardyTheorem.SelbergSqrtZetaSmallAbsSharpBudget
import MathlibAux.LogRatioLowerBound

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# A near-diagonal majorant for the comparable square-root-zeta gap budget

The factor-of-two split leaves pairs whose product indices are comparable.
For such a pair the logarithmic frequency gap still retains its additive
separation:

`1 / |log m - log n| <= max m n / dist m n`.

This converts the unresolved logarithmic kernel into the sharp discrete
near-diagonal kernel `max m n / dist m n`; no global support maximum is
inserted.  The second bound below applies
`2ab <= a^2 + b^2`, so the remaining arithmetic problem is an explicitly
weighted finite square-energy sum rather than an unstructured `L1` square.
-/

/-- The sharp elementary comparison between logarithmic and additive
separation of two distinct positive natural numbers. -/
theorem inv_abs_log_nat_sub_log_nat_le_max_div_dist
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    1 / |Real.log (m : ℝ) - Real.log (n : ℝ)| ≤
      (max m n : ℝ) / (Nat.dist m n : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdistNatPos : 0 < Nat.dist m n :=
    Nat.dist_pos_of_ne hmn
  have hdistPos : (0 : ℝ) < Nat.dist m n := by
    exact_mod_cast hdistNatPos
  have hmaxPos : (0 : ℝ) < max m n := by
    exact_mod_cast lt_of_lt_of_le hm (le_max_left m n)
  have hdistCast :
      (Nat.dist m n : ℝ) = |(m : ℝ) - (n : ℝ)| := by
    rw [← Nat.dist_cast_real, Real.dist_eq]
  have hmaxCast :
      (max m n : ℝ) = max (m : ℝ) (n : ℝ) := by
    exact_mod_cast (rfl : max m n = max m n)
  have hgap :
      (Nat.dist m n : ℝ) / (max m n : ℝ) ≤
        |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
    rw [hdistCast, hmaxCast]
    simpa only [Real.log_div hmR.ne' hnR.ne'] using
      (MathlibAux.abs_sub_div_max_le_abs_log_div hmR hnR)
  calc
    1 / |Real.log (m : ℝ) - Real.log (n : ℝ)| ≤
        1 / ((Nat.dist m n : ℝ) / (max m n : ℝ)) :=
      one_div_le_one_div_of_le (div_pos hdistPos hmaxPos) hgap
    _ = (max m n : ℝ) / (Nat.dist m n : ℝ) := by
      field_simp [hdistPos.ne', hmaxPos.ne']

/-- The comparable-pair budget with the logarithmic frequency denominator
replaced by the additive near-diagonal distance.  The actual collected
coefficients are retained. -/
noncomputable def selbergSqrtZetaComparableNearDiagonalBudget
    (N X : ℕ) : ℝ :=
  let M := N * X * X
  ∑ m ∈ Finset.Ioc 1 M,
    ∑ n ∈ Finset.Ioc 1 M,
      if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
        2 * (max m n : ℝ) *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
            ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
          (Nat.dist m n : ℝ)
      else 0

/-- The square-energy version of the near-diagonal budget.  Its kernel is
still the exact reciprocal integer distance, while each coefficient product
has been replaced by the corresponding two square terms. -/
noncomputable def selbergSqrtZetaComparableNearDiagonalSquareBudget
    (N X : ℕ) : ℝ :=
  let M := N * X * X
  ∑ m ∈ Finset.Ioc 1 M,
    ∑ n ∈ Finset.Ioc 1 M,
      if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
        (max m n : ℝ) *
            (‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2 +
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ ^ 2) /
          (Nat.dist m n : ℝ)
      else 0

/-- The unresolved comparable logarithmic-frequency budget is controlled by
the additive near-diagonal kernel.  In particular, the factor-of-two range
does not need to be discarded into an `L1`-square estimate. -/
theorem selbergSqrtZetaComparableGapBudget_le_nearDiagonal
    (N X : ℕ) :
    selbergSqrtZetaComparableGapBudget N X ≤
      selbergSqrtZetaComparableNearDiagonalBudget N X := by
  classical
  let M := N * X * X
  let a : ℕ → ℝ := fun k =>
    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖
  have hpoint : ∀ m ∈ Finset.Ioc 1 M, ∀ n ∈ Finset.Ioc 1 M,
      (if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          2 * a m * a n /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|
        else 0) ≤
      (if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          2 * (max m n : ℝ) * a m * a n / (Nat.dist m n : ℝ)
        else 0) := by
    intro m hm n hn
    by_cases hcomp : m ≠ n ∧ m < 2 * n ∧ n < 2 * m
    · rw [if_pos hcomp, if_pos hcomp]
      have hmPos : 0 < m := by
        exact (Finset.mem_Ioc.mp hm).1
      have hnPos : 0 < n := by
        exact (Finset.mem_Ioc.mp hn).1
      have hkernel :
          1 /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| ≤
            (max m n : ℝ) / (Nat.dist m n : ℝ) := by
        rw [selbergShortDirichletCollectedFrequency_eq_neg_log,
          selbergShortDirichletCollectedFrequency_eq_neg_log]
        convert
          inv_abs_log_nat_sub_log_nat_le_max_div_dist
            hmPos hnPos hcomp.1 using 1
        rw [show
            -Real.log (m : ℝ) - -Real.log (n : ℝ) =
              -(Real.log (m : ℝ) - Real.log (n : ℝ)) by ring,
          abs_neg]
      have hcoeff : 0 ≤ 2 * a m * a n := by
        dsimp only [a]
        positivity
      calc
        2 * a m * a n /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| =
            (2 * a m * a n) *
              (1 /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n|) := by
            ring
        _ ≤ (2 * a m * a n) *
              ((max m n : ℝ) / (Nat.dist m n : ℝ)) :=
            mul_le_mul_of_nonneg_left hkernel hcoeff
        _ = 2 * (max m n : ℝ) * a m * a n /
              (Nat.dist m n : ℝ) := by
            ring
    · rw [if_neg hcomp, if_neg hcomp]
  unfold selbergSqrtZetaComparableGapBudget
  unfold selbergSqrtZetaComparableNearDiagonalBudget
  dsimp only [M, a]
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro n hn
  exact hpoint m hm n hn

/-- Young's inequality converts the coefficient products in the
near-diagonal budget into an explicit finite square-energy budget. -/
theorem selbergSqrtZetaComparableNearDiagonalBudget_le_square
    (N X : ℕ) :
    selbergSqrtZetaComparableNearDiagonalBudget N X ≤
      selbergSqrtZetaComparableNearDiagonalSquareBudget N X := by
  classical
  let M := N * X * X
  let a : ℕ → ℝ := fun k =>
    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖
  have hpoint : ∀ m ∈ Finset.Ioc 1 M, ∀ n ∈ Finset.Ioc 1 M,
      (if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          2 * (max m n : ℝ) * a m * a n / (Nat.dist m n : ℝ)
        else 0) ≤
      (if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          (max m n : ℝ) * (a m ^ 2 + a n ^ 2) /
            (Nat.dist m n : ℝ)
        else 0) := by
    intro m hm n hn
    by_cases hcomp : m ≠ n ∧ m < 2 * n ∧ n < 2 * m
    · rw [if_pos hcomp, if_pos hcomp]
      have hmax : 0 ≤ (max m n : ℝ) := by positivity
      have hdist : 0 ≤ (Nat.dist m n : ℝ) := by positivity
      apply div_le_div_of_nonneg_right _ hdist
      have hyoung : 2 * a m * a n ≤ a m ^ 2 + a n ^ 2 := by
        nlinarith [sq_nonneg (a m - a n)]
      calc
        2 * (max m n : ℝ) * a m * a n =
            (max m n : ℝ) * (2 * a m * a n) := by ring
        _ ≤ (max m n : ℝ) * (a m ^ 2 + a n ^ 2) :=
          mul_le_mul_of_nonneg_left hyoung hmax
    · rw [if_neg hcomp, if_neg hcomp]
  unfold selbergSqrtZetaComparableNearDiagonalBudget
  unfold selbergSqrtZetaComparableNearDiagonalSquareBudget
  dsimp only [M, a]
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro n hn
  exact hpoint m hm n hn

/-- The full logarithmic-frequency form is reduced to the square-energy
near-diagonal budget plus the already controlled far `L1` term. -/
theorem selbergSqrtZeta_frequencyGap_le_nearDiagonalSquare_add_far
    (N X : ℕ) :
    (∑ m ∈ Finset.Ioc 1 (N * X * X),
      ∑ n ∈ Finset.Ioc 1 (N * X * X),
        2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|) ≤
      selbergSqrtZetaComparableNearDiagonalSquareBudget N X +
        (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 := by
  calc
    (∑ m ∈ Finset.Ioc 1 (N * X * X),
      ∑ n ∈ Finset.Ioc 1 (N * X * X),
        2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|) ≤
        selbergSqrtZetaComparableGapBudget N X +
          (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 :=
      selbergSqrtZeta_frequencyGap_le_comparable_add_far N X
    _ ≤ selbergSqrtZetaComparableNearDiagonalBudget N X +
          (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 :=
      add_le_add
        (selbergSqrtZetaComparableGapBudget_le_nearDiagonal N X) le_rfl
    _ ≤ selbergSqrtZetaComparableNearDiagonalSquareBudget N X +
          (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 :=
      add_le_add
        (selbergSqrtZetaComparableNearDiagonalBudget_le_square N X) le_rfl

/-- The actual small-window gap sum now leaves only a collected-coefficient
square energy against the reciprocal integer-distance kernel.  This is the
near-diagonal arithmetic input required for a dyadic or Schur-type estimate. -/
theorem selbergSqrtZetaShortDirichletGapSum_le_nearDiagonalSquare_add_far
    {N X : ℕ} {A B H : ℝ} (hAB : A ≤ B) :
    selbergSqrtZetaShortDirichletGapSum N X A B H ≤
      (B - A) *
          ∑ n ∈ Finset.Ioc 1 (N * X * X),
            Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n) +
        H ^ 2 *
          (selbergSqrtZetaComparableNearDiagonalSquareBudget N X +
            (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2) := by
  exact
    (selbergSqrtZetaShortDirichletGapSum_le_comparable_add_far hAB).trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left
          (add_le_add
            ((selbergSqrtZetaComparableGapBudget_le_nearDiagonal N X).trans
              (selbergSqrtZetaComparableNearDiagonalBudget_le_square N X))
            le_rfl)
          (sq_nonneg H)))

end HardyTheorem
