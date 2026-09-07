import HardyTheorem.AFECriticalDyadicBlock

/-!
# Gaussian mean square of a complete dyadic AFE level

The logarithmic-frequency Schur estimate is applied block by block, but the
coefficient energies are summed over the complete level before the divisor
bound is used.  Thus no factor equal to the number of blocks appears.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem
namespace AFE

/-- The critical-line mollified Dirichlet polynomial attached to one aligned
dyadic block. -/
noncomputable def dyadicMollifiedCriticalBlockPolynomial
    (K j X q : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial (Finset.Icc 1 (2 ^ K * X))
    (fun k => dyadicMollifiedCriticalBlockCoeff K j X k q)
    (fun k => -Real.log k) t

/-- A complete dyadic level has Gaussian second moment bounded by the common
Schur factor times its polylogarithmic coefficient energy. -/
theorem sum_integral_gaussian_normSq_dyadicMollifiedCriticalBlockPolynomial_le
    {K j X : ℕ} (hX : 2 ≤ X) {Delta : ℝ}
    (hDelta : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta) (w : ℝ) :
    (∑ q ∈ Finset.range (2 ^ K),
      ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMollifiedCriticalBlockPolynomial K j X q t)) ≤
      (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
          MathlibAux.gaussianBucketSchurConstant) *
        (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4) := by
  let U : ℕ := 2 ^ K * X
  let Q := Finset.range (2 ^ K)
  let S := Finset.Icc 1 U
  let C := Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
    MathlibAux.gaussianBucketSchurConstant
  have hU : 0 < U := by
    dsimp only [U]
    positivity
  have hmean (q : ℕ) :
      (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMollifiedCriticalBlockPolynomial K j X q t)) ≤
        C * ∑ k ∈ S,
          ‖dyadicMollifiedCriticalBlockCoeff K j X k q‖ ^ 2 := by
    simpa only [U, S, C, dyadicMollifiedCriticalBlockPolynomial] using
      (MathlibAux.integral_gaussian_mul_normSq_dirichletPolynomial_le
        hU hDelta w S
        (fun k hk => Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1)
        (fun k hk => (Finset.mem_Icc.mp hk).2)
        (fun k => dyadicMollifiedCriticalBlockCoeff K j X k q))
  have henergy := sum_levelEnergy_dyadicMollifiedCriticalBlockCoeff_le
    (K := K) (j := j) hX
  calc
    (∑ q ∈ Finset.range (2 ^ K),
      ∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicMollifiedCriticalBlockPolynomial K j X q t)) ≤
        ∑ q ∈ Q, C * ∑ k ∈ S,
          ‖dyadicMollifiedCriticalBlockCoeff K j X k q‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      exact hmean q
    _ = C * ∑ q ∈ Q, ∑ k ∈ S,
          ‖dyadicMollifiedCriticalBlockCoeff K j X k q‖ ^ 2 := by
      rw [Finset.mul_sum]
    _ = C * ∑ k ∈ S, ∑ q ∈ Q,
          Complex.normSq
            (dyadicMollifiedCriticalBlockCoeff K j X k q) := by
      congr 1
      simp only [Complex.normSq_eq_norm_sq]
      exact Finset.sum_comm
    _ ≤ C * (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [U, S, Q] using henergy
      · exact mul_nonneg (Real.sqrt_nonneg _)
          MathlibAux.gaussianBucketSchurConstant_pos.le

end AFE
end HardyTheorem
