import HardyTheorem.SelbergSqrtZetaComparableNearDiagonal
import Mathlib.NumberTheory.Harmonic.Bounds

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# A Schur--harmonic estimate for the comparable near-diagonal budget

For a fixed positive index `m <= M`, the reciprocal integer-distance kernel
has row mass at most twice the `M`-th harmonic number.  The factor two comes
from the indices on the two sides of `m`.  Combining this with
`max m n < 2 * m` on the comparable range gives a Schur-type estimate with
the local weight `m`, before any global support maximum is inserted.
-/

/-- The reciprocal-distance mass to the left of `m` is bounded by the
`M`-th harmonic number. -/
private theorem sum_inv_natDist_Ioc_filter_lt_le_harmonic
    {M m : ℕ} (hm : m ∈ Finset.Ioc 1 M) :
    (∑ n ∈ (Finset.Ioc 1 M).filter (fun n => n < m),
        ((Nat.dist m n : ℝ))⁻¹) ≤
      (harmonic M : ℝ) := by
  classical
  let S := (Finset.Ioc 1 M).filter (fun n => n < m)
  let f : ℕ → ℝ := fun k => ((k : ℝ))⁻¹
  have hinj :
      ∀ a ∈ S, ∀ b ∈ S, m - a = m - b → a = b := by
    intro a ha b hb hab
    have ha_lt : a < m := (Finset.mem_filter.mp ha).2
    have hb_lt : b < m := (Finset.mem_filter.mp hb).2
    omega
  have himage :
      S.image (fun n => m - n) ⊆ Finset.Icc 1 M := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
    have hn_lt : n < m := (Finset.mem_filter.mp hn).2
    have hm_le : m ≤ M := (Finset.mem_Ioc.mp hm).2
    simp only [Finset.mem_Icc]
    omega
  have hrewrite :
      (∑ n ∈ S, ((Nat.dist m n : ℝ))⁻¹) =
        ∑ n ∈ S, f (m - n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn_le : n ≤ m :=
      (Nat.le_of_lt (Finset.mem_filter.mp hn).2)
    rw [Nat.dist_eq_sub_of_le_right hn_le]
  calc
    (∑ n ∈ (Finset.Ioc 1 M).filter (fun n => n < m),
        ((Nat.dist m n : ℝ))⁻¹) =
        ∑ n ∈ S, f (m - n) := by
      simpa only [S] using hrewrite
    _ = ∑ k ∈ S.image (fun n => m - n), f k :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.Icc 1 M, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro k _hk _hnot
        dsimp only [f]
        positivity)
    _ = (harmonic M : ℝ) := by
      simp only [f, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- The reciprocal-distance mass to the right of `m` is bounded by the
`M`-th harmonic number. -/
private theorem sum_inv_natDist_Ioc_filter_gt_le_harmonic
    {M m : ℕ} (_hm : m ∈ Finset.Ioc 1 M) :
    (∑ n ∈ (Finset.Ioc 1 M).filter (fun n => m < n),
        ((Nat.dist m n : ℝ))⁻¹) ≤
      (harmonic M : ℝ) := by
  classical
  let S := (Finset.Ioc 1 M).filter (fun n => m < n)
  let f : ℕ → ℝ := fun k => ((k : ℝ))⁻¹
  have hinj :
      ∀ a ∈ S, ∀ b ∈ S, a - m = b - m → a = b := by
    intro a ha b hb hab
    have ha_gt : m < a := (Finset.mem_filter.mp ha).2
    have hb_gt : m < b := (Finset.mem_filter.mp hb).2
    omega
  have himage :
      S.image (fun n => n - m) ⊆ Finset.Icc 1 M := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
    have hn_gt : m < n := (Finset.mem_filter.mp hn).2
    have hn_le : n ≤ M :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
    simp only [Finset.mem_Icc]
    omega
  have hrewrite :
      (∑ n ∈ S, ((Nat.dist m n : ℝ))⁻¹) =
        ∑ n ∈ S, f (n - m) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hm_le : m ≤ n :=
      Nat.le_of_lt (Finset.mem_filter.mp hn).2
    rw [Nat.dist_eq_sub_of_le hm_le]
  calc
    (∑ n ∈ (Finset.Ioc 1 M).filter (fun n => m < n),
        ((Nat.dist m n : ℝ))⁻¹) =
        ∑ n ∈ S, f (n - m) := by
      simpa only [S] using hrewrite
    _ = ∑ k ∈ S.image (fun n => n - m), f k :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.Icc 1 M, f k :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (by
        intro k _hk _hnot
        dsimp only [f]
        positivity)
    _ = (harmonic M : ℝ) := by
      simp only [f, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast]

/-- A fixed row of the reciprocal integer-distance matrix over
`{2, ..., M}` has mass at most twice the `M`-th harmonic number. -/
theorem sum_inv_natDist_Ioc_le_two_mul_harmonic
    {M m : ℕ} (hm : m ∈ Finset.Ioc 1 M) :
    (∑ n ∈ Finset.Ioc 1 M,
        if n ≠ m then ((Nat.dist m n : ℝ))⁻¹ else 0) ≤
      2 * (harmonic M : ℝ) := by
  classical
  have hsplit :
      (∑ n ∈ Finset.Ioc 1 M,
          if n ≠ m then ((Nat.dist m n : ℝ))⁻¹ else 0) =
        (∑ n ∈ (Finset.Ioc 1 M).filter (fun n => n < m),
            ((Nat.dist m n : ℝ))⁻¹) +
          ∑ n ∈ (Finset.Ioc 1 M).filter (fun n => m < n),
            ((Nat.dist m n : ℝ))⁻¹ := by
    rw [Finset.sum_filter, Finset.sum_filter,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hnm : n = m
    · subst n
      simp
    · rcases lt_or_gt_of_ne hnm with hlt | hgt
      · simp [hnm, hlt, not_lt_of_ge hlt.le]
      · simp [hnm, hgt, not_lt_of_ge hgt.le]
  rw [hsplit]
  linarith [
    sum_inv_natDist_Ioc_filter_lt_le_harmonic hm,
    sum_inv_natDist_Ioc_filter_gt_le_harmonic hm]

/-- On the factor-of-two comparable range, a fixed row of the weighted
kernel is at most `4 * m * harmonic M`.  This is the local Schur bound:
the weight remains the row index `m`, rather than the global endpoint `M`. -/
theorem sum_comparable_max_div_natDist_le_four_mul_self_mul_harmonic
    {M m : ℕ} (hm : m ∈ Finset.Ioc 1 M) :
    (∑ n ∈ Finset.Ioc 1 M,
        if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          (max m n : ℝ) / (Nat.dist m n : ℝ)
        else 0) ≤
      4 * (m : ℝ) * (harmonic M : ℝ) := by
  have hpoint : ∀ n ∈ Finset.Ioc 1 M,
      (if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          (max m n : ℝ) / (Nat.dist m n : ℝ)
        else 0) ≤
      2 * (m : ℝ) *
        (if n ≠ m then ((Nat.dist m n : ℝ))⁻¹ else 0) := by
    intro n hn
    by_cases hcomp : m ≠ n ∧ m < 2 * n ∧ n < 2 * m
    · rw [if_pos hcomp, if_pos hcomp.1.symm]
      have hmax : max m n ≤ 2 * m := by omega
      have hmaxR : (max m n : ℝ) ≤ 2 * (m : ℝ) := by
        exact_mod_cast hmax
      have hinv : 0 ≤ ((Nat.dist m n : ℝ))⁻¹ := by positivity
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hmaxR hinv
    · rw [if_neg hcomp]
      positivity
  calc
    (∑ n ∈ Finset.Ioc 1 M,
        if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          (max m n : ℝ) / (Nat.dist m n : ℝ)
        else 0) ≤
        ∑ n ∈ Finset.Ioc 1 M,
          2 * (m : ℝ) *
            (if n ≠ m then ((Nat.dist m n : ℝ))⁻¹ else 0) :=
      Finset.sum_le_sum hpoint
    _ = 2 * (m : ℝ) *
        (∑ n ∈ Finset.Ioc 1 M,
          if n ≠ m then ((Nat.dist m n : ℝ))⁻¹ else 0) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (m : ℝ) * (2 * (harmonic M : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_inv_natDist_Ioc_le_two_mul_harmonic hm)
        (by positivity)
    _ = 4 * (m : ℝ) * (harmonic M : ℝ) := by ring

/-- Generic Schur estimate for the comparable near-diagonal square form.
The local weight `m` is retained in the coefficient energy. -/
theorem comparableNearDiagonalSquareSum_le_weightedHarmonic
    (M : ℕ) (a : ℕ → ℝ) :
    (∑ m ∈ Finset.Ioc 1 M,
      ∑ n ∈ Finset.Ioc 1 M,
        if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          (max m n : ℝ) * (a m ^ 2 + a n ^ 2) /
            (Nat.dist m n : ℝ)
        else 0) ≤
      8 * (harmonic M : ℝ) *
        ∑ m ∈ Finset.Ioc 1 M, (m : ℝ) * a m ^ 2 := by
  classical
  let S := Finset.Ioc 1 M
  let w : ℕ → ℕ → ℝ := fun m n =>
    if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
      (max m n : ℝ) / (Nat.dist m n : ℝ)
    else 0
  have hw_symm (m n : ℕ) : w m n = w n m := by
    dsimp only [w]
    by_cases hcomp : m ≠ n ∧ m < 2 * n ∧ n < 2 * m
    · rw [if_pos hcomp,
        if_pos ⟨hcomp.1.symm, hcomp.2.2, hcomp.2.1⟩,
        max_comm, Nat.dist_comm]
    · have hcomp' : ¬ (n ≠ m ∧ n < 2 * m ∧ m < 2 * n) := by
        intro h
        exact hcomp ⟨h.1.symm, h.2.2, h.2.1⟩
      rw [if_neg hcomp, if_neg hcomp']
  have hrewrite :
      (∑ m ∈ S, ∑ n ∈ S,
        if m ≠ n ∧ m < 2 * n ∧ n < 2 * m then
          (max m n : ℝ) * (a m ^ 2 + a n ^ 2) /
            (Nat.dist m n : ℝ)
        else 0) =
      (∑ m ∈ S, ∑ n ∈ S, w m n * a m ^ 2) +
        ∑ m ∈ S, ∑ n ∈ S, w m n * a n ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _hm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hcomp : m ≠ n ∧ m < 2 * n ∧ n < 2 * m
    · rw [if_pos hcomp]
      dsimp only [w]
      rw [if_pos hcomp]
      ring
    · rw [if_neg hcomp]
      dsimp only [w]
      rw [if_neg hcomp]
      ring
  have hfirst :
      (∑ m ∈ S, ∑ n ∈ S, w m n * a m ^ 2) ≤
        4 * (harmonic M : ℝ) *
          ∑ m ∈ S, (m : ℝ) * a m ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m hm
    calc
      (∑ n ∈ S, w m n * a m ^ 2) =
          (∑ n ∈ S, w m n) * a m ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ (4 * (m : ℝ) * (harmonic M : ℝ)) * a m ^ 2 :=
        mul_le_mul_of_nonneg_right
          (by
            simpa only [S, w] using
              sum_comparable_max_div_natDist_le_four_mul_self_mul_harmonic
                hm)
          (sq_nonneg (a m))
      _ = 4 * (harmonic M : ℝ) * ((m : ℝ) * a m ^ 2) := by
        ring
  have hsecond :
      (∑ m ∈ S, ∑ n ∈ S, w m n * a n ^ 2) ≤
        4 * (harmonic M : ℝ) *
          ∑ m ∈ S, (m : ℝ) * a m ^ 2 := by
    calc
      (∑ m ∈ S, ∑ n ∈ S, w m n * a n ^ 2) =
          ∑ n ∈ S, ∑ m ∈ S, w m n * a n ^ 2 := by
        rw [Finset.sum_comm]
      _ = ∑ n ∈ S, ∑ m ∈ S, w n m * a n ^ 2 := by
        apply Finset.sum_congr rfl
        intro n _hn
        apply Finset.sum_congr rfl
        intro m _hm
        rw [hw_symm]
      _ ≤ 4 * (harmonic M : ℝ) *
          ∑ m ∈ S, (m : ℝ) * a m ^ 2 := hfirst
  rw [show Finset.Ioc 1 M = S by rfl, hrewrite]
  calc
    (∑ m ∈ S, ∑ n ∈ S, w m n * a m ^ 2) +
        ∑ m ∈ S, ∑ n ∈ S, w m n * a n ^ 2 ≤
      (4 * (harmonic M : ℝ) *
          ∑ m ∈ S, (m : ℝ) * a m ^ 2) +
        4 * (harmonic M : ℝ) *
          ∑ m ∈ S, (m : ℝ) * a m ^ 2 :=
      add_le_add hfirst hsecond
    _ = 8 * (harmonic M : ℝ) *
        ∑ m ∈ S, (m : ℝ) * a m ^ 2 := by ring

/-- The actual Selberg comparable square budget is controlled by the
harmonic factor times the locally weighted collected-coefficient energy. -/
theorem
    selbergSqrtZetaComparableNearDiagonalSquareBudget_le_weightedHarmonic
    (N X : ℕ) :
    selbergSqrtZetaComparableNearDiagonalSquareBudget N X ≤
      8 * (harmonic (N * X * X) : ℝ) *
        ∑ m ∈ Finset.Ioc 1 (N * X * X),
          (m : ℝ) *
            ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2 := by
  simpa only [selbergSqrtZetaComparableNearDiagonalSquareBudget] using
    comparableNearDiagonalSquareSum_le_weightedHarmonic
      (N * X * X)
      (fun m => ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖)

/-- Inserting the support endpoint gives a global `L²` version of the
Schur--harmonic budget. -/
theorem
    selbergSqrtZetaComparableNearDiagonalSquareBudget_le_globalHarmonic
    (N X : ℕ) :
    selbergSqrtZetaComparableNearDiagonalSquareBudget N X ≤
      8 * ((N * X * X : ℕ) : ℝ) * (harmonic (N * X * X) : ℝ) *
        ∑ m ∈ Finset.Ioc 1 (N * X * X),
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2 := by
  let M := N * X * X
  let a : ℕ → ℝ := fun m =>
    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖
  have hweighted :
      (∑ m ∈ Finset.Ioc 1 M, (m : ℝ) * a m ^ 2) ≤
        (M : ℝ) * ∑ m ∈ Finset.Ioc 1 M, a m ^ 2 := by
    calc
      (∑ m ∈ Finset.Ioc 1 M, (m : ℝ) * a m ^ 2) ≤
          ∑ m ∈ Finset.Ioc 1 M, (M : ℝ) * a m ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Finset.mem_Ioc.mp hm).2)
          (sq_nonneg (a m))
      _ = (M : ℝ) * ∑ m ∈ Finset.Ioc 1 M, a m ^ 2 := by
        rw [Finset.mul_sum]
  have hharmonic : 0 ≤ (harmonic M : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  calc
    selbergSqrtZetaComparableNearDiagonalSquareBudget N X ≤
        8 * (harmonic M : ℝ) *
          ∑ m ∈ Finset.Ioc 1 M, (m : ℝ) * a m ^ 2 := by
      simpa only [M, a] using
        selbergSqrtZetaComparableNearDiagonalSquareBudget_le_weightedHarmonic
          N X
    _ ≤ 8 * (harmonic M : ℝ) *
          ((M : ℝ) * ∑ m ∈ Finset.Ioc 1 M, a m ^ 2) :=
      mul_le_mul_of_nonneg_left hweighted (by positivity)
    _ = 8 * (M : ℝ) * (harmonic M : ℝ) *
          ∑ m ∈ Finset.Ioc 1 M, a m ^ 2 := by ring
    _ = 8 * ((N * X * X : ℕ) : ℝ) * (harmonic (N * X * X) : ℝ) *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2 := by
      simp only [M, a]

/-- Logarithmic global form of the near-diagonal Schur budget. -/
theorem selbergSqrtZetaComparableNearDiagonalSquareBudget_le_globalLog
    (N X : ℕ) :
    selbergSqrtZetaComparableNearDiagonalSquareBudget N X ≤
      8 * ((N * X * X : ℕ) : ℝ) *
        (1 + Real.log ((N * X * X : ℕ) : ℝ)) *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2 := by
  let M := N * X * X
  let E : ℝ :=
    ∑ m ∈ Finset.Ioc 1 M,
      ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2
  calc
    selbergSqrtZetaComparableNearDiagonalSquareBudget N X ≤
        8 * (M : ℝ) * (harmonic M : ℝ) * E := by
      simpa only [M, E] using
        selbergSqrtZetaComparableNearDiagonalSquareBudget_le_globalHarmonic
          N X
    _ ≤ 8 * (M : ℝ) * (1 + Real.log (M : ℝ)) * E := by
      have hE : 0 ≤ E := by
        dsimp only [E]
        positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (harmonic_le_one_add_log M)
          (by positivity))
        hE
    _ = 8 * ((N * X * X : ℕ) : ℝ) *
        (1 + Real.log ((N * X * X : ℕ) : ℝ)) *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ ^ 2 := by
      simp only [M, E]

end HardyTheorem
