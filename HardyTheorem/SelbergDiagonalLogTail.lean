import HardyTheorem.SelbergDiagonalGaussianScalar
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Filter MeasureTheory Real Set Topology

namespace HardyTheorem

/-! # The logarithmic tail in Selberg's diagonal kernel. -/

noncomputable def selbergDiagonalLogTail (y : ℝ) : ℝ :=
  Real.exp (-y ^ 2) / y

noncomputable def selbergDiagonalLogTailMajorant (y : ℝ) : ℝ :=
  1 / (y * (1 + y ^ 2))

noncomputable def selbergDiagonalLogPrimitive (y : ℝ) : ℝ :=
  Real.log y - (1 / 2 : ℝ) * Real.log (1 + y ^ 2)

theorem selbergDiagonalLogPrimitive_eq_inverse_log
    {y : ℝ} (hy : 0 < y) :
    selbergDiagonalLogPrimitive y =
      -(1 / 2 : ℝ) * Real.log (1 + y⁻¹ ^ 2) := by
  have hratio : 1 + y⁻¹ ^ 2 = (1 + y ^ 2) / y ^ 2 := by
    field_simp [hy.ne']
    ring
  unfold selbergDiagonalLogPrimitive
  rw [hratio, Real.log_div, Real.log_pow]
  push_cast
  ring
  all_goals positivity

theorem selbergDiagonalLogTail_le_majorant
    {y : ℝ} (hy : 0 < y) :
    selbergDiagonalLogTail y ≤ selbergDiagonalLogTailMajorant y := by
  have hbase : 1 + y ^ 2 ≤ Real.exp (y ^ 2) := by
    simpa [add_comm] using Real.add_one_le_exp (y ^ 2)
  have hinv : 1 / Real.exp (y ^ 2) ≤ 1 / (1 + y ^ 2) :=
    one_div_le_one_div_of_le (by positivity) hbase
  have hexp : Real.exp (-y ^ 2) ≤ 1 / (1 + y ^ 2) := by
    rw [Real.exp_neg]
    simpa only [one_div] using hinv
  unfold selbergDiagonalLogTail selbergDiagonalLogTailMajorant
  calc
    Real.exp (-y ^ 2) / y ≤ (1 / (1 + y ^ 2)) / y :=
      div_le_div_of_nonneg_right hexp hy.le
    _ = 1 / (y * (1 + y ^ 2)) := by
      field_simp [hy.ne']

theorem hasDerivAt_selbergDiagonalLogPrimitive
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt selbergDiagonalLogPrimitive
      (selbergDiagonalLogTailMajorant y) y := by
  have hlogy := hasDerivAt_log hy.ne'
  have hinner := (hasDerivAt_const y (1 : ℝ)).add ((hasDerivAt_id y).pow 2)
  have harg : 1 + y ^ 2 ≠ 0 := by positivity
  have hloginner := hinner.log (by
    simpa only [Pi.add_apply, Pi.pow_apply, id_eq] using harg)
  have hscaled := hloginner.const_mul (1 / 2 : ℝ)
  have hderiv := hlogy.sub hscaled
  simp only [Pi.sub_apply, Pi.add_apply, Pi.pow_apply, id_eq, zero_add,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hderiv
  change HasDerivAt (Real.log - fun y =>
      (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
    (1 / (y * (1 + y ^ 2))) y
  have hcoef : y⁻¹ - (1 / 2 : ℝ) * (2 * y / (1 + y ^ 2)) =
      1 / (y * (1 + y ^ 2)) := by
    field_simp [hy.ne', harg]
    ring
  simpa only [hcoef] using hderiv

theorem tendsto_selbergDiagonalLogPrimitive_atTop :
    Tendsto selbergDiagonalLogPrimitive atTop (𝓝 0) := by
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hsquare : Tendsto (fun y : ℝ => y⁻¹ ^ 2) atTop (𝓝 (0 ^ 2)) :=
    hinv.pow 2
  have hadd : Tendsto (fun y : ℝ => 1 + y⁻¹ ^ 2) atTop (𝓝 (1 + 0 ^ 2)) :=
    tendsto_const_nhds.add hsquare
  have hlog : Tendsto (fun y : ℝ => Real.log (1 + y⁻¹ ^ 2))
      atTop (𝓝 (Real.log (1 + 0 ^ 2))) :=
    (Real.continuousAt_log (by norm_num)).tendsto.comp hadd
  have hscaled := (tendsto_const_nhds (x := (-(1 / 2 : ℝ)))).mul hlog
  norm_num at hscaled
  have hH : Tendsto (fun y : ℝ => -(1 / 2 : ℝ) *
      Real.log (1 + y⁻¹ ^ 2)) atTop (𝓝 0) := by
    simpa only [inv_pow, neg_mul] using hscaled
  apply hH.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact (selbergDiagonalLogPrimitive_eq_inverse_log hy).symm

theorem integrableOn_selbergDiagonalLogTailMajorant_Ioi
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn selbergDiagonalLogTailMajorant (Set.Ioi a) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (g := selbergDiagonalLogPrimitive) (l := (0 : ℝ))
  · intro y hy
    exact hasDerivAt_selbergDiagonalLogPrimitive (ha.trans_le hy)
  · intro y hy
    unfold selbergDiagonalLogTailMajorant
    have hy0 : 0 < y := ha.trans hy
    positivity
  · exact tendsto_selbergDiagonalLogPrimitive_atTop

theorem integral_selbergDiagonalLogTailMajorant_Ioi
    {a : ℝ} (ha : 0 < a) :
    (∫ y in Set.Ioi a, selbergDiagonalLogTailMajorant y) =
      (1 / 2 : ℝ) * Real.log (1 + a⁻¹ ^ 2) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := selbergDiagonalLogPrimitive) (l := (0 : ℝ))
    (fun y hy => hasDerivAt_selbergDiagonalLogPrimitive (ha.trans_le hy))
    (fun y hy => by
      have hy0 : 0 < y := ha.trans hy
      unfold selbergDiagonalLogTailMajorant
      positivity)
    tendsto_selbergDiagonalLogPrimitive_atTop
  rw [selbergDiagonalLogPrimitive_eq_inverse_log ha] at h
  simpa using h

theorem integrableOn_selbergDiagonalLogTail_Ioi
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn selbergDiagonalLogTail (Set.Ioi a) := by
  have hmajor := integrableOn_selbergDiagonalLogTailMajorant_Ioi ha
  apply Integrable.mono' hmajor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro y hy
    unfold selbergDiagonalLogTail
    exact ((by fun_prop : ContinuousAt (fun t : ℝ => Real.exp (-t ^ 2)) y).div
      continuousAt_id (ha.trans hy).ne').continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : 0 < y := ha.trans hy
    have hf0 : 0 ≤ selbergDiagonalLogTail y := by
      unfold selbergDiagonalLogTail
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hf0]
    exact selbergDiagonalLogTail_le_majorant hy0

theorem integral_selbergDiagonalLogTail_Ioi_le
    {a : ℝ} (ha : 0 < a) :
    (∫ y in Set.Ioi a, selbergDiagonalLogTail y) ≤
      (1 / 2 : ℝ) * Real.log (1 + a⁻¹ ^ 2) := by
  calc
    (∫ y in Set.Ioi a, selbergDiagonalLogTail y) ≤
        ∫ y in Set.Ioi a, selbergDiagonalLogTailMajorant y := by
      apply MeasureTheory.integral_mono_ae
        (integrableOn_selbergDiagonalLogTail_Ioi ha)
        (integrableOn_selbergDiagonalLogTailMajorant_Ioi ha)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact selbergDiagonalLogTail_le_majorant (ha.trans hy)
    _ = (1 / 2 : ℝ) * Real.log (1 + a⁻¹ ^ 2) :=
      integral_selbergDiagonalLogTailMajorant_Ioi ha

theorem integral_selbergDiagonalLogTail_Ioi_le_log
    {a : ℝ} (ha : 0 < a) :
    (∫ y in Set.Ioi a, selbergDiagonalLogTail y) ≤
      Real.log (2 + a⁻¹ ^ 2) := by
  have hlog0 : 0 ≤ Real.log (1 + a⁻¹ ^ 2) := by
    apply Real.log_nonneg
    nlinarith [sq_nonneg a⁻¹]
  calc
    (∫ y in Set.Ioi a, selbergDiagonalLogTail y) ≤
        (1 / 2 : ℝ) * Real.log (1 + a⁻¹ ^ 2) :=
      integral_selbergDiagonalLogTail_Ioi_le ha
    _ ≤ Real.log (1 + a⁻¹ ^ 2) := by nlinarith
    _ ≤ Real.log (2 + a⁻¹ ^ 2) := by
      apply Real.log_le_log (by positivity)
      linarith

theorem log_tail_argument_le_eta
    {x eta : ℝ} (hx : 1 ≤ x) (heta : 0 < eta) :
    Real.log (2 + (x * Real.sqrt eta)⁻¹ ^ 2) ≤
      Real.log (2 + eta⁻¹) := by
  have hsqrt : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hinvX : x⁻¹ ^ 2 ≤ 1 := by
    have hxinv : x⁻¹ ≤ 1 := (inv_le_one₀ hx0).2 hx
    have hxinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr hx0.le
    nlinarith
  have hsqrtSq : (Real.sqrt eta) ^ 2 = eta := Real.sq_sqrt heta.le
  have harg : (x * Real.sqrt eta)⁻¹ ^ 2 ≤ eta⁻¹ := by
    have heq : (x * Real.sqrt eta)⁻¹ ^ 2 = x⁻¹ ^ 2 * eta⁻¹ := by
      field_simp [hx0.ne', hsqrt.ne', heta.ne']
      nlinarith [hsqrtSq]
    rw [heq]
    have hetaInv0 : 0 ≤ eta⁻¹ := inv_nonneg.mpr heta.le
    exact mul_le_of_le_one_left hetaInv0 hinvX
  apply Real.log_le_log (by positivity)
  linarith

end HardyTheorem
