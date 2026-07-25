import HardyTheorem.SelbergSqrtZetaSmallAbsGapBound
import HardyTheorem.SelbergSqrtZetaHighRangeEnergy
import MathlibAux.SlidingExponentialGapDecomposition

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Diagonal/off-diagonal decomposition for the square-root-zeta gap sum

The diagonal is reduced to the proved constant low range and a purely
arithmetic high-range fiber-cardinality sum.  The remaining off-diagonal
term is the logarithmic-frequency bilinear form of the actual collected
coefficients.
-/

/-- The square-root-zeta gap sum is the generic sliding-exponential gap
sum for its collected coefficient family. -/
theorem selbergSqrtZetaShortDirichletGapSum_eq_slidingExponentialGapSum
    (N X : ℕ) (A B H : ℝ) :
    selbergSqrtZetaShortDirichletGapSum N X A B H =
      MathlibAux.slidingExponentialGapSum
        (Finset.Ioc 1 (N * X * X))
        (selbergSqrtZetaShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency A B H := by
  classical
  unfold selbergSqrtZetaShortDirichletGapSum
  unfold MathlibAux.slidingExponentialGapSum
  apply Finset.sum_congr rfl
  intro m _hm
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp [hmn]

/-- The full gap sum is bounded by the constant low-range diagonal, the
explicit high-range square-cardinality sum, and one off-diagonal bilinear
form. -/
theorem selbergSqrtZetaShortDirichletGapSum_le_diagonal_add_offDiagonal
    {N X : ℕ} (hN : 1 ≤ N) (hX : 2 ≤ X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X)
    {A B H : ℝ} (hAB : A ≤ B) :
    selbergSqrtZetaShortDirichletGapSum N X A B H ≤
      (B - A) *
          ((15 : ℝ) / 4 * H ^ 2 +
            ∑ k ∈ Finset.Ioc (min N X) (N * X * X),
              (min |H| (2 / Real.log (k : ℝ))) ^ 2 *
                ((selbergShortCompleteRangePairs X k).card ^ 2 /
                  (k : ℝ))) +
        H ^ 2 *
          ∑ m ∈ Finset.Ioc 1 (N * X * X),
            ∑ n ∈ Finset.Ioc 1 (N * X * X),
              2 *
                    ‖selbergSqrtZetaShortDirichletCollectedCoeff N X m‖ *
                  ‖selbergSqrtZetaShortDirichletCollectedCoeff N X n‖ /
                |selbergShortDirichletCollectedFrequency m -
                  selbergShortDirichletCollectedFrequency n| := by
  rw [selbergSqrtZetaShortDirichletGapSum_eq_slidingExponentialGapSum]
  apply
    (MathlibAux.slidingExponentialGapSum_le_diagonal_add_frequencyGap
      (Finset.Ioc 1 (N * X * X))
      (selbergSqrtZetaShortDirichletCollectedCoeff N X)
      selbergShortDirichletCollectedFrequency hAB).trans
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (sum_normSq_sliding_selbergSqrtZetaShortDirichletCollectedCoeff_le_lowRange_add_completePairCardSqHighRange
        hN hX hlarge H)
      (sub_nonneg.mpr hAB))
    le_rfl

end HardyTheorem
