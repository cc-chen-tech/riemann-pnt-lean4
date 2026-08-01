import HardyTheorem.SelbergSqrtZetaGapDecomposition

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# A sharp arithmetic split for the square-root-zeta small-window gap sum

The existing small-absolute-mass argument leaves a finite logarithmic
frequency-gap sum.  This file separates the genuinely close multiplicative
pairs from pairs whose product indices differ by at least a factor of two.
For the latter pairs the logarithmic gap is at least `log 2`, so their entire
contribution is controlled by the square of the actual collected-coefficient
`L¹` mass.  Thus no fiber-cardinality majorant is introduced in the far range.
-/

/-- The part of the actual collected-coefficient gap sum coming from
distinct product indices within a factor of two of each other. -/
noncomputable def selbergSqrtZetaComparableGapBudget
    (N X : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 1 (N * X * X),
    ∑ n ∈ Finset.Ioc 1 (N * X * X),
      if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
        2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|
      else 0

/-- The complementary contribution from distinct product indices separated
by at least a factor of two. -/
noncomputable def selbergSqrtZetaFarGapBudget
    (N X : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ioc 1 (N * X * X),
    ∑ n ∈ Finset.Ioc 1 (N * X * X),
      if m ≠ n ∧ ¬ (m < 2 * n ∧ n < 2 * m) then
        2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|
      else 0

/-- The `L¹` mass of the actual nonconstant collected coefficients. -/
noncomputable def selbergSqrtZetaCollectedCoeffL1
    (N X : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc 1 (N * X * X),
    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖

private theorem log_two_le_abs_log_nat_sub_log_nat_of_not_comparable
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hfar : ¬ (m < 2 * n ∧ n < 2 * m)) :
    Real.log 2 ≤ |Real.log (m : ℝ) - Real.log (n : ℝ)| := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  rcases (by omega : 2 * n ≤ m ∨ 2 * m ≤ n) with hnm | hmn
  · have hcast : (2 : ℝ) * n ≤ m := by exact_mod_cast hnm
    have hlog := Real.log_le_log (mul_pos (by norm_num) hnpos) hcast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hlog
    have hnmLog : Real.log (n : ℝ) ≤ Real.log (m : ℝ) :=
      Real.log_le_log hnpos (by
        exact_mod_cast (le_trans (by omega : n ≤ 2 * n) hnm))
    rw [abs_of_nonneg (sub_nonneg.mpr hnmLog)]
    linarith
  · have hcast : (2 : ℝ) * m ≤ n := by exact_mod_cast hmn
    have hlog := Real.log_le_log (mul_pos (by norm_num) hmpos) hcast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hmpos.ne'] at hlog
    have hmnLog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hmpos (by
        exact_mod_cast (le_trans (by omega : m ≤ 2 * m) hmn))
    rw [abs_of_nonpos (sub_nonpos.mpr hmnLog)]
    linarith

private theorem log_two_le_collectedFrequency_gap_of_not_comparable
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hfar : ¬ (m < 2 * n ∧ n < 2 * m)) :
    Real.log 2 ≤
      |selbergShortDirichletCollectedFrequency m -
        selbergShortDirichletCollectedFrequency n| := by
  rw [selbergShortDirichletCollectedFrequency_eq_neg_log,
    selbergShortDirichletCollectedFrequency_eq_neg_log]
  convert
    log_two_le_abs_log_nat_sub_log_nat_of_not_comparable hm hn hfar using 1
  rw [show
      -Real.log (m : ℝ) - -Real.log (n : ℝ) =
        -(Real.log (m : ℝ) - Real.log (n : ℝ)) by ring,
    abs_neg]

/-- Exact arithmetic partition of the raw frequency-gap form into
factor-of-two comparable pairs and factor-of-two separated pairs. -/
theorem selbergSqrtZeta_frequencyGap_eq_comparable_add_farGap
    (N X : ℕ) :
    (∑ m ∈ Finset.Ioc 1 (N * X * X),
      ∑ n ∈ Finset.Ioc 1 (N * X * X),
        2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|) =
      selbergSqrtZetaComparableGapBudget N X +
        selbergSqrtZetaFarGapBudget N X := by
  classical
  unfold selbergSqrtZetaComparableGapBudget
  unfold selbergSqrtZetaFarGapBudget
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hmn : m = n
  · subst n
    simp
  · by_cases hcomp : m < 2 * n ∧ n < 2 * m
    · simp [hmn, hcomp]
    · simp [hmn, hcomp]

/-- The far part of the exact partition is bounded by `log 2` and the square
of the actual collected-coefficient `L¹` mass. -/
theorem selbergSqrtZeta_farGap_le_l1
    (N X : ℕ) :
    selbergSqrtZetaFarGapBudget N X ≤
      (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 := by
  classical
  let S := Finset.Ioc 1 (N * X * X)
  let a : ℕ → ℝ := fun k =>
    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖
  let gap : ℕ → ℕ → ℝ := fun m n =>
    |selbergShortDirichletCollectedFrequency m -
      selbergShortDirichletCollectedFrequency n|
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpoint : ∀ m ∈ S, ∀ n ∈ S,
      (if m ≠ n ∧ ¬ (m < 2 * n ∧ n < 2 * m) then
          2 * a m * a n / gap m n else 0) ≤
        (2 / Real.log 2) * a m * a n := by
    intro m hm n hn
    by_cases hfar : m ≠ n ∧ ¬ (m < 2 * n ∧ n < 2 * m)
    · rw [if_pos hfar]
      have hm1 : 1 ≤ m := (Finset.mem_Ioc.mp hm).1.le
      have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1.le
      have hgap :
          Real.log 2 ≤ gap m n :=
        log_two_le_collectedFrequency_gap_of_not_comparable
          hm1 hn1 hfar.2
      have hnum : 0 ≤ 2 * a m * a n := by
        dsimp only [a]
        positivity
      calc
        2 * a m * a n / gap m n ≤
            2 * a m * a n / Real.log 2 :=
          div_le_div_of_nonneg_left hnum hlog2 hgap
        _ = (2 / Real.log 2) * a m * a n := by ring
    · rw [if_neg hfar]
      dsimp only [a]
      positivity
  calc
    selbergSqrtZetaFarGapBudget N X =
        ∑ m ∈ S, ∑ n ∈ S,
          if m ≠ n ∧ ¬ (m < 2 * n ∧ n < 2 * m) then
            2 * a m * a n / gap m n else 0 := by rfl
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
          (2 / Real.log 2) * a m * a n := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      exact hpoint m hm n hn
    _ = (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 := by
      unfold selbergSqrtZetaCollectedCoeffL1
      dsimp only [S, a]
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      ring

/-- The full raw logarithmic-frequency bilinear form splits into:

* the actual contribution of comparable product indices, and
* a far-range term controlled by the actual collected-coefficient `L¹` mass.

The factor-of-two split supplies the uniform denominator `log 2`; unlike the
previous high-range estimates, this statement does not replace collected
coefficients by fiber cardinalities. -/
theorem selbergSqrtZeta_frequencyGap_le_comparable_add_far
    (N X : ℕ) :
    (∑ m ∈ Finset.Ioc 1 (N * X * X),
      ∑ n ∈ Finset.Ioc 1 (N * X * X),
        2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|) ≤
      selbergSqrtZetaComparableGapBudget N X +
        (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 := by
  calc
    (∑ m ∈ Finset.Ioc 1 (N * X * X),
      ∑ n ∈ Finset.Ioc 1 (N * X * X),
        2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
              ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
            |selbergShortDirichletCollectedFrequency m -
              selbergShortDirichletCollectedFrequency n|) =
        selbergSqrtZetaComparableGapBudget N X +
          selbergSqrtZetaFarGapBudget N X :=
      selbergSqrtZeta_frequencyGap_eq_comparable_add_farGap N X
    _ ≤ selbergSqrtZetaComparableGapBudget N X +
          (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2 :=
      add_le_add le_rfl (selbergSqrtZeta_farGap_le_l1 N X)

/-- The actual small-window gap sum inherits the factor-of-two arithmetic
split.  The only unresolved gap contribution is now supported on comparable
product indices; all far pairs are absorbed without a fiber-cardinality
majorant. -/
theorem selbergSqrtZetaShortDirichletGapSum_le_comparable_add_far
    {N X : ℕ} {A B H : ℝ} (hAB : A ≤ B) :
    selbergSqrtZetaShortDirichletGapSum N X A B H ≤
      (B - A) *
          ∑ n ∈ Finset.Ioc 1 (N * X * X),
            Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n) +
        H ^ 2 *
          (selbergSqrtZetaComparableGapBudget N X +
            (2 / Real.log 2) * selbergSqrtZetaCollectedCoeffL1 N X ^ 2) := by
  rw [selbergSqrtZetaShortDirichletGapSum_eq_slidingExponentialGapSum]
  calc
    MathlibAux.slidingExponentialGapSum
        (Finset.Ioc 1 (N * X * X))
        (selbergSqrtZetaShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency A B H ≤
      (B - A) *
          ∑ n ∈ Finset.Ioc 1 (N * X * X),
            Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n) +
        H ^ 2 *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              2 * ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
                    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
                  |selbergShortDirichletCollectedFrequency m -
                    selbergShortDirichletCollectedFrequency n| :=
      MathlibAux.slidingExponentialGapSum_le_diagonal_add_frequencyGap
        (Finset.Ioc 1 (N * X * X))
        (selbergSqrtZetaShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency hAB
    _ ≤ _ := by
      gcongr
      exact selbergSqrtZeta_frequencyGap_le_comparable_add_far N X

end HardyTheorem
