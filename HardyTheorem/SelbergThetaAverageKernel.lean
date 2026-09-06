import HardyTheorem.SelbergJLowMassFinal

open MeasureTheory

namespace HardyTheorem

/-! # The positive theta-average kernel for Selberg's high tail -/

noncomputable def selbergThetaAverageKernel (v : ℝ) : ℝ :=
  ∫ theta : ℝ in (0 : ℝ)..1 / 2, theta * Real.exp (-v * theta)

theorem selbergThetaAverageKernel_eq
    {v : ℝ} (hv : v ≠ 0) :
    selbergThetaAverageKernel v =
      (1 - Real.exp (-v / 2) * (1 + v / 2)) / v ^ 2 := by
  let A : ℝ → ℝ :=
    (fun theta => -((v * theta + 1) / v ^ 2)) *
      (fun theta => Real.exp (-v * theta))
  have hder : ∀ theta : ℝ,
      HasDerivAt A (theta * Real.exp (-v * theta)) theta := by
    intro theta
    have hcoef : HasDerivAt
        (fun t : ℝ => -((v * t + 1) / v ^ 2))
        (-v / v ^ 2) theta := by
      simpa only [id_eq, mul_one, neg_one_mul, neg_div] using
        (((((hasDerivAt_id theta).const_mul v).add_const 1).div_const
          (v ^ 2)).const_mul (-1))
    have hexp : HasDerivAt
        (fun t : ℝ => Real.exp (-v * t))
        ((-v) * Real.exp (-v * theta)) theta := by
      simpa only [id_eq, mul_one, neg_mul, mul_comm] using
        ((hasDerivAt_id theta).const_mul (-v)).exp
    have hmul : HasDerivAt A
        ((-v / v ^ 2) * Real.exp (-v * theta) +
          (-((v * theta + 1) / v ^ 2)) *
            ((-v) * Real.exp (-v * theta))) theta := by
      exact hcoef.mul hexp
    convert hmul using 1
    field_simp [hv]
    ring
  have hint : IntervalIntegrable
      (fun theta : ℝ => theta * Real.exp (-v * theta)) volume 0 (1 / 2) := by
    exact (by fun_prop : Continuous
      (fun theta : ℝ => theta * Real.exp (-v * theta))).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun theta _h => hder theta) hint
  unfold selbergThetaAverageKernel
  rw [hFTC]
  dsimp [A]
  field_simp [hv]
  norm_num
  ring

theorem one_sub_two_div_exp_one_pos :
    0 < 1 - 2 / Real.exp 1 := by
  rw [sub_pos, div_lt_one (Real.exp_pos 1)]
  exact Real.exp_one_gt_two

private theorem exp_neg_mul_one_add_le_two_div_exp_one
    {r : ℝ} (hr : 1 ≤ r) :
    Real.exp (-r) * (1 + r) ≤ 2 / Real.exp 1 := by
  have hshift : r ≤ Real.exp (r - 1) := by
    nlinarith [Real.add_one_le_exp (r - 1)]
  have hexp : Real.exp 1 * r ≤ Real.exp r := by
    calc
      Real.exp 1 * r ≤ Real.exp 1 * Real.exp (r - 1) :=
        mul_le_mul_of_nonneg_left hshift (Real.exp_pos 1).le
      _ = Real.exp r := by
        rw [← Real.exp_add]
        congr 1
        ring
  rw [Real.exp_neg, inv_mul_eq_div]
  apply (div_le_iff₀ (Real.exp_pos r)).2
  have hk : 0 ≤ 2 / Real.exp 1 := by positivity
  have hscaled :
      (2 / Real.exp 1) * (Real.exp 1 * r) ≤
        (2 / Real.exp 1) * Real.exp r :=
    mul_le_mul_of_nonneg_left hexp hk
  have hsimpl :
      (2 / Real.exp 1) * (Real.exp 1 * r) = 2 * r := by
    field_simp [(Real.exp_pos 1).ne']
  rw [hsimpl] at hscaled
  nlinarith

theorem one_sub_two_div_exp_one_div_sq_le_selbergThetaAverageKernel
    {v : ℝ} (hv : 2 ≤ v) :
    (1 - 2 / Real.exp 1) / v ^ 2 ≤ selbergThetaAverageKernel v := by
  have hv0 : v ≠ 0 := by linarith
  have hr : 1 ≤ v / 2 := by linarith
  have hterm := exp_neg_mul_one_add_le_two_div_exp_one hr
  have hterm' :
      Real.exp (-v / 2) * (1 + v / 2) ≤ 2 / Real.exp 1 := by
    simpa only [neg_div] using hterm
  rw [selbergThetaAverageKernel_eq hv0]
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg v)

end HardyTheorem
