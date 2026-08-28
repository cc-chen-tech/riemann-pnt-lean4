import HardyTheorem.AFECriticalDyadicLevelGaussian
import MathlibAux.DyadicPrefixDecomposition

/-!
# Gaussian energy of the complete dyadic prefix tree

The tree embeds in a rectangle consisting of `K+1` complete dyadic levels.
The uniform level estimate therefore costs only one factor `K+1`.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem
namespace AFE

/-- The complete aligned dyadic tree has at most `K+1` copies of the uniform
levelwise Gaussian energy. -/
theorem sum_integral_gaussian_normSq_dyadicMollifiedCriticalTree_le
    {K X : ℕ} (hX : 2 ≤ X) {Delta : ℝ}
    (hDelta : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta) (w : ℝ) :
    (∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
      ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t)) ≤
      (K + 1 : ℝ) *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
  let Tree := MathlibAux.dyadicPrefixTree K 0
  let Levels := Finset.range (K + 1)
  let Owners := Finset.range (2 ^ K)
  let B := (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
      MathlibAux.gaussianBucketSchurConstant) *
    (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)
  have hnonneg (p : ℕ × ℕ) :
      0 ≤ ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t) := by
    exact integral_nonneg fun t => mul_nonneg (Real.exp_nonneg _)
      (Complex.normSq_nonneg _)
  have hlevel (j : ℕ) :
      (∑ q ∈ Owners,
        ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (dyadicMollifiedCriticalBlockPolynomial K j X q t)) ≤ B := by
    simpa only [Owners, B] using
      (sum_integral_gaussian_normSq_dyadicMollifiedCriticalBlockPolynomial_le
        (K := K) (j := j) hX hDelta w)
  calc
    (∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
      ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t)) ≤
      ∑ p ∈ Levels.product Owners,
        ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · simpa only [Tree, Levels, Owners] using
          MathlibAux.dyadicPrefixTree_subset_product_range K
      · intro p hp hnot
        exact hnonneg p
    _ = ∑ j ∈ Levels, ∑ q ∈ Owners,
        ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (dyadicMollifiedCriticalBlockPolynomial K j X q t) := by
      exact Finset.sum_product Levels Owners (fun p =>
        ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t))
    _ ≤ ∑ _j ∈ Levels, B := by
      apply Finset.sum_le_sum
      intro j hj
      exact hlevel j
    _ = (K + 1 : ℝ) * B := by
      simp [Levels]
    _ = (K + 1 : ℝ) *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
      rfl

end AFE
end HardyTheorem
