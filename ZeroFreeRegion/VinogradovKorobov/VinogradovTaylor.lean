import ZeroFreeRegion.VinogradovKorobov.VinogradovJacobian
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.NumberTheory.Multiplicity

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- First-order Taylor expansion of an integer power modulo the square of the
increment scale. -/
theorem int_pow_add_mul_modEq_sq (q x h : ℤ) (n : ℕ) :
    (x + q * h) ^ n ≡
      x ^ n + (n : ℤ) * x ^ (n - 1) * (q * h) [ZMOD q ^ 2] := by
  rw [Int.modEq_iff_dvd]
  have hscale : q ^ 2 ∣ (q * h) ^ 2 := by
    rw [mul_pow]
    exact dvd_mul_right (q ^ 2) (h ^ 2)
  have hraw := hscale.trans (sq_dvd_add_pow_sub_sub (q * h) x n)
  convert hraw.neg_right using 1 <;> ring

/-- Simultaneous first-order Taylor expansion of every power sum.  The
linear term is exactly the power-sum Jacobian applied to the increment
vector. -/
theorem vinogradovPowerSumInt_affine_modEq_sq
    {k : ℕ} (q : ℤ) (x h : Fin k → ℤ) (j : Fin k) :
    vinogradovPowerSumInt (fun i ↦ x i + q * h i) j ≡
      vinogradovPowerSumInt x j +
        q * (vinogradovPowerSumJacobian x).mulVec h j [ZMOD q ^ 2] := by
  have hsum :
      (∑ i : Fin k, (x i + q * h i) ^ (j.val + 1)) ≡
        ∑ i : Fin k,
          (x i ^ (j.val + 1) +
            q * (((j.val + 1 : ℕ) : ℤ) * x i ^ j.val * h i))
          [ZMOD q ^ 2] := by
    apply Int.ModEq.sum
    intro i _
    convert int_pow_add_mul_modEq_sq q (x i) (h i) (j.val + 1) using 1 <;>
      simp <;> ring
  simpa [vinogradovPowerSumInt, vinogradovPowerSumJacobian,
    Matrix.mulVec, dotProduct, Finset.sum_add_distrib, Finset.mul_sum] using hsum

end

end ZeroFreeRegion.VinogradovKorobov
