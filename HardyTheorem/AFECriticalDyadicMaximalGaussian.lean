import HardyTheorem.AFECriticalDyadicMaximalPointwise
import HardyTheorem.AFECriticalDyadicTreeGaussian

/-!
# Gaussian Rademacher--Menshov bound for a measurable moving cutoff

The pointwise tree envelope is independent of the chosen prefix.  Hence any
measurable selector of a prefix inside the ambient block has Gaussian second
moment bounded by two factors `K+1`: one from prefix Cauchy--Schwarz and one
from summing the complete dyadic tree by levels.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem
namespace AFE

/-- Gaussian maximal mean square for an arbitrary measurable moving prefix. -/
theorem integral_gaussian_normSq_dyadicMovingPrefixMollifiedPolynomial_le
    {K X : ℕ} (hX : 2 ≤ X) {Delta : ℝ}
    (hDelta : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta) (w : ℝ)
    (cutoff : ℝ → ℕ) (hcutoff : ∀ t, cutoff t ≤ 2 ^ K)
    (hmeas : AEStronglyMeasurable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMovingPrefixMollifiedPolynomial K (cutoff t) X t)) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMovingPrefixMollifiedPolynomial K (cutoff t) X t)) ≤
      (K + 1 : ℝ) ^ 2 *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
  let G : ℝ → ℝ := fun t => Real.exp (-((t - w) ^ 2) / Delta ^ 2)
  let L : ℝ → ℝ := fun t => G t * Complex.normSq
    (dyadicMovingPrefixMollifiedPolynomial K (cutoff t) X t)
  let U : ℝ → ℝ := fun t => (K + 1 : ℝ) *
    ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
      G t * Complex.normSq
        (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t)
  have hDeltaPos : 0 < Delta := by
    have hUXpos : 0 < ((2 ^ K * X : ℕ) : ℝ) := by positivity
    linarith
  have htermInt (p : ℕ × ℕ) : Integrable fun t : ℝ =>
      G t * Complex.normSq
        (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t) := by
    simpa only [G, dyadicMollifiedCriticalBlockPolynomial] using
      (MathlibAux.integrable_gaussian_mul_normSq_exponentialPolynomial
        hDeltaPos w (Finset.Icc 1 (2 ^ K * X))
        (fun k => dyadicMollifiedCriticalBlockCoeff K p.1 X k p.2)
        (fun k => -Real.log k))
  have hsumInt : Integrable fun t : ℝ =>
      ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
        G t * Complex.normSq
          (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t) :=
    integrable_finsetSum (MathlibAux.dyadicPrefixTree K 0)
      (fun p _hp => htermInt p)
  have hUInt : Integrable U := by
    simpa only [U] using hsumInt.const_mul (K + 1 : ℝ)
  have hpoint (t : ℝ) : L t ≤ U t := by
    have hpref := normSq_dyadicMovingPrefixMollifiedPolynomial_le_tree
      K (cutoff t) X (hcutoff t) t
    dsimp only [L, U, G]
    calc
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (dyadicMovingPrefixMollifiedPolynomial K (cutoff t) X t) ≤
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          ((K + 1 : ℝ) *
            ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
              Complex.normSq
                (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t)) :=
        mul_le_mul_of_nonneg_left hpref (Real.exp_nonneg _)
      _ = (K + 1 : ℝ) *
          ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
            Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
              Complex.normSq
                (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t) := by
        calc
          _ = (K + 1 : ℝ) *
              (Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
                ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
                  Complex.normSq
                    (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t)) := by
            ring
          _ = _ := by rw [Finset.mul_sum]
  have hLInt : Integrable L := by
    apply hUInt.mono' hmeas
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (Real.exp_nonneg _) (Complex.normSq_nonneg _))]
      exact hpoint t
  have hmono : (∫ t : ℝ, L t) ≤ ∫ t : ℝ, U t :=
    integral_mono_ae hLInt hUInt
      (Filter.Eventually.of_forall hpoint)
  have htree := sum_integral_gaussian_normSq_dyadicMollifiedCriticalTree_le
    (K := K) hX hDelta w
  calc
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMovingPrefixMollifiedPolynomial K (cutoff t) X t)) =
        ∫ t : ℝ, L t := by rfl
    _ ≤ ∫ t : ℝ, U t := hmono
    _ = (K + 1 : ℝ) *
        ∑ p ∈ MathlibAux.dyadicPrefixTree K 0,
          ∫ t : ℝ, G t * Complex.normSq
            (dyadicMollifiedCriticalBlockPolynomial K p.1 X p.2 t) := by
      dsimp only [U]
      rw [integral_const_mul]
      rw [integral_finsetSum (MathlibAux.dyadicPrefixTree K 0)
        (fun p _hp => htermInt p)]
    _ ≤ (K + 1 : ℝ) *
        ((K + 1 : ℝ) *
          ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              MathlibAux.gaussianBucketSchurConstant) *
            (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4))) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [G] using htree
      · positivity
    _ = (K + 1 : ℝ) ^ 2 *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
      ring

end AFE
end HardyTheorem
