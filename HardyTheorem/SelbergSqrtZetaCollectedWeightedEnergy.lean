import HardyTheorem.SelbergSqrtZetaHighRangeEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Weighted energy of the collected square-root-zeta coefficients

The actual triple fiber at a product index `k` injects into the two
mollifier indices `(d,l)`.  Its cardinality is therefore at most `X^2`.
Combining this with finite Cauchy--Schwarz and the pointwise `1/k` bound
gives an explicit `N * X^6` bound for the collected weighted square energy.
-/

/-- Every actual triple-product fiber has at most `X^2` elements. -/
theorem card_selbergShortDirichletTriples_le_sq
    (N X k : ℕ) :
    (selbergShortDirichletTriples N X k).card ≤ X ^ 2 := by
  calc
    (selbergShortDirichletTriples N X k).card ≤
        (selbergShortCompleteRangePairs X k).card :=
      card_selbergShortDirichletTriples_le_completeRangePairs N X k
    _ ≤
        ((Finset.Icc 1 X).product (Finset.Icc 1 X)).card := by
      unfold selbergShortCompleteRangePairs
      exact Finset.card_filter_le _ _
    _ = X ^ 2 := by
      simp [Nat.card_Icc, pow_two]

/-- After weighting by its product index, one collected coefficient costs
at most the square of the `X^2` triple-fiber bound. -/
theorem
    mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_sq_sq
    {N X k : ℕ} (hX : 2 ≤ X) (hk : 1 ≤ k) :
    (k : ℝ) *
        ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2 ≤
      (((X ^ 2 : ℕ) : ℝ)) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  have henergy :
      Complex.normSq
          (selbergSqrtZetaShortDirichletCollectedCoeff N X k) ≤
        (selbergShortDirichletTriples N X k).card ^ 2 / (k : ℝ) :=
    (normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_tripleFiber
      N X k).trans
      (selbergSqrtZetaShortCollectedTripleFiberEnergy_le_card_sq_div hX)
  have hkReal : (k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < k))
  calc
    (k : ℝ) * Complex.normSq
        (selbergSqrtZetaShortDirichletCollectedCoeff N X k) ≤
        (k : ℝ) *
          ((selbergShortDirichletTriples N X k).card ^ 2 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left henergy (by positivity)
    _ = ((selbergShortDirichletTriples N X k).card : ℝ) ^ 2 := by
      field_simp
    _ ≤ (((X ^ 2 : ℕ) : ℝ)) ^ 2 := by
      gcongr
      exact_mod_cast card_selbergShortDirichletTriples_le_sq N X k

/-- Summing the pointwise weighted bound over the actual product support
loses at most its endpoint `N * X^2`. -/
theorem
    sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_sq_sq
    {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        (k : ℝ) *
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2) ≤
      ((N * X * X : ℕ) : ℝ) * (((X ^ 2 : ℕ) : ℝ)) ^ 2 := by
  let M := N * X * X
  let B : ℝ := (((X ^ 2 : ℕ) : ℝ)) ^ 2
  have hcard : (Finset.Ioc 1 M).card ≤ M := by
    simp [Nat.card_Ioc]
  calc
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        (k : ℝ) *
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2) ≤
        ∑ _k ∈ Finset.Ioc 1 M, B := by
      apply Finset.sum_le_sum
      intro k hk
      exact
        mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_sq_sq
          hX (Nat.le_of_lt (Finset.mem_Ioc.mp hk).1)
    _ = ((Finset.Ioc 1 M).card : ℝ) * B := by simp
    _ ≤ (M : ℝ) * B :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = ((N * X * X : ℕ) : ℝ) *
        (((X ^ 2 : ℕ) : ℝ)) ^ 2 := by rfl

/-- Polynomial normal form of the collected weighted energy bound. -/
theorem
    sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_pow_six
    {N X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        (k : ℝ) *
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2) ≤
      (N : ℝ) * (X : ℝ) ^ 6 := by
  calc
    (∑ k ∈ Finset.Ioc 1 (N * X * X),
        (k : ℝ) *
          ‖selbergSqrtZetaShortDirichletCollectedCoeff N X k‖ ^ 2) ≤
        ((N * X * X : ℕ) : ℝ) *
          (((X ^ 2 : ℕ) : ℝ)) ^ 2 :=
      sum_mul_normSq_selbergSqrtZetaShortDirichletCollectedCoeff_le_mul_sq_sq
        hX
    _ = (N : ℝ) * (X : ℝ) ^ 6 := by
      push_cast
      ring

end HardyTheorem
