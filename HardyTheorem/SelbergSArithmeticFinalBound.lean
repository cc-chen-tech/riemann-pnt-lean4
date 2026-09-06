import HardyTheorem.SelbergSArithmeticJordanIdentity
import HardyTheorem.SelbergSArithmeticEulerWeight
import HardyTheorem.SelbergSArithmeticLogTail

open Complex Nat Finset
open scoped BigOperators

namespace HardyTheorem

/-!
# Closing Selberg's arithmetic diagonal estimate

This file inserts S19 into the exact Jordan identity S14, applies the
primewise fourth-power majorant, and spends the single logarithm supplied by
S20.  The result is the uniform `X^(2*theta) / log X` estimate needed in the
diagonal Fourier calculation.
-/

private theorem norm_jordan_pair_term_le_eulerWeight
    {C : ℝ} (hC : 0 ≤ C)
    {rho X : ℕ} [NeZero rho] {theta : ℝ}
    (htheta : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hX : Real.exp 1 ≤ (X : ℝ))
    (hpair : ‖selbergArithmeticPairSum rho X theta‖ ≤
      C * ((X : ℝ) ^ theta) / Real.log (X : ℝ) *
        (rho : ℝ)⁻¹ *
        (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) ^ 2) :
    ‖(selbergJordanWeight (1 - theta) rho : ℂ) *
        selbergArithmeticPairSum rho X theta ^ 2‖ ≤
      (C * ((X : ℝ) ^ theta) / Real.log (X : ℝ)) ^ 2 *
        (rho : ℝ)⁻¹ * selbergSArithEulerWeight rho := by
  let P : ℝ := ∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)
  let K : ℝ := C * ((X : ℝ) ^ theta) / Real.log (X : ℝ)
  let B : ℝ := K * (rho : ℝ)⁻¹ * P ^ 2
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX)
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpairB : ‖selbergArithmeticPairSum rho X theta‖ ≤ B := by
    simpa only [K, P, B] using hpair
  have hpairSq : ‖selbergArithmeticPairSum rho X theta‖ ^ 2 ≤ B ^ 2 := by
    nlinarith [norm_nonneg (selbergArithmeticPairSum rho X theta)]
  have halpha : 0 ≤ 1 - theta := sub_nonneg.mpr htheta1
  have hJ0 : 0 ≤ selbergJordanWeight (1 - theta) rho :=
    selbergJordanWeight_nonneg halpha rho
  have hJleRpow : selbergJordanWeight (1 - theta) rho ≤
      (rho : ℝ) ^ (1 - theta) :=
    selbergJordanWeight_le_rpow halpha (NeZero.ne rho)
  have hrhoOne : (1 : ℝ) ≤ rho := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne rho)
  have hRpowLe : (rho : ℝ) ^ (1 - theta) ≤ (rho : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hrhoOne (by linarith : 1 - theta ≤ 1)
  have hJle : selbergJordanWeight (1 - theta) rho ≤ (rho : ℝ) :=
    hJleRpow.trans hRpowLe
  have hrhoPos : (0 : ℝ) < rho := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne rho)
  rw [norm_mul, norm_pow]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hJ0]
  calc
    selbergJordanWeight (1 - theta) rho *
        ‖selbergArithmeticPairSum rho X theta‖ ^ 2 ≤
        (rho : ℝ) * B ^ 2 := by
      exact mul_le_mul hJle hpairSq (sq_nonneg _)
        (Nat.cast_nonneg rho)
    _ = K ^ 2 * (rho : ℝ)⁻¹ * selbergSArithEulerWeight rho := by
      unfold selbergSArithEulerWeight
      dsimp [B, P]
      field_simp [ne_of_gt hrhoPos]

private theorem one_add_log_sq_le_three_mul_log
    {X : ℕ} (hX : Real.exp 1 ≤ (X : ℝ)) :
    1 + Real.log ((X * X : ℕ) : ℝ) ≤
      3 * Real.log (X : ℝ) := by
  have hXpos : (0 : ℝ) < X := by
    exact lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogOne : 1 ≤ Real.log (X : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hX
  rw [Nat.cast_mul, Real.log_mul hXpos.ne' hXpos.ne']
  linarith

/-- S-arith: the exact diagonal four-variable sum is uniformly bounded by
`X^(2*theta) / log X` for the full nonnegative Jordan range. -/
theorem exists_norm_selbergArithmeticDiagonalSum_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (theta : ℝ),
        0 ≤ theta → theta ≤ 1 → Real.exp 1 ≤ (X : ℝ) →
        ‖selbergArithmeticDiagonalSum X theta‖ ≤
          C * ((X : ℝ) ^ (2 * theta)) / Real.log (X : ℝ) := by
  rcases exists_norm_selbergArithmeticPairSum_le with
    ⟨Cpair, hCpair, hpair⟩
  rcases exists_selbergNineProduct_logTail_le with
    ⟨Ctail, hCtail, htail⟩
  let C : ℝ := 3 * Cpair ^ 2 * Ctail
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro X theta htheta htheta1 hX
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX)
  have hscale : 0 ≤
      (Cpair * ((X : ℝ) ^ theta) / Real.log (X : ℝ)) ^ 2 :=
    sq_nonneg _
  have hXpow :
      ((X : ℝ) ^ theta) ^ 2 = (X : ℝ) ^ (2 * theta) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg X) theta 2]
    congr 1
    ring
  rw [selbergArithmeticDiagonalSum_eq_jordanQuadratic]
  unfold selbergArithmeticJordanQuadraticSum
  calc
    ‖∑ rho ∈ Finset.Icc 1 (X * X),
        (selbergJordanWeight (1 - theta) rho : ℂ) *
          selbergArithmeticPairSum rho X theta ^ 2‖ ≤
        ∑ rho ∈ Finset.Icc 1 (X * X),
          ‖(selbergJordanWeight (1 - theta) rho : ℂ) *
            selbergArithmeticPairSum rho X theta ^ 2‖ :=
      norm_sum_le (Finset.Icc 1 (X * X)) _
    _ ≤ ∑ rho ∈ Finset.Icc 1 (X * X),
        (Cpair * ((X : ℝ) ^ theta) / Real.log (X : ℝ)) ^ 2 *
          (rho : ℝ)⁻¹ * selbergSArithEulerWeight rho := by
      apply Finset.sum_le_sum
      intro rho hrho
      letI : NeZero rho := ⟨Nat.one_le_iff_ne_zero.mp
        (Finset.mem_Icc.mp hrho).1⟩
      exact norm_jordan_pair_term_le_eulerWeight hCpair
        htheta htheta1 hX
        (hpair rho theta X htheta hX)
    _ = (Cpair * ((X : ℝ) ^ theta) / Real.log (X : ℝ)) ^ 2 *
        ∑ rho ∈ Finset.Icc 1 (X * X),
          (rho : ℝ)⁻¹ * selbergSArithEulerWeight rho := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho _hrho
      ring
    _ ≤ (Cpair * ((X : ℝ) ^ theta) / Real.log (X : ℝ)) ^ 2 *
        (Ctail * (1 + Real.log ((X * X : ℕ) : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      exact (Finset.sum_le_sum fun rho _hrho =>
        mul_le_mul_of_nonneg_left
          (selbergSArithEulerWeight_le_nineProduct rho)
          (inv_nonneg.mpr (Nat.cast_nonneg rho))).trans
        (htail (X * X))
    _ ≤ (Cpair * ((X : ℝ) ^ theta) / Real.log (X : ℝ)) ^ 2 *
        (Ctail * (3 * Real.log (X : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      exact mul_le_mul_of_nonneg_left
        (one_add_log_sq_le_three_mul_log hX) hCtail
    _ = C * ((X : ℝ) ^ (2 * theta)) / Real.log (X : ℝ) := by
      dsimp [C]
      rw [← hXpow]
      field_simp [hlogpos.ne']

end HardyTheorem
