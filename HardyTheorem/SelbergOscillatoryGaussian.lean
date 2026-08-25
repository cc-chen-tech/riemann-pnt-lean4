import HardyTheorem.OscillatoryIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Complex Filter MeasureTheory Set Topology

namespace HardyTheorem

/-! # The oscillatory Gaussian tail in Selberg's off-diagonal term. -/

noncomputable def selbergOscillatoryGaussian
    (P Q theta u : ℝ) : ℂ :=
  (u ^ (-theta) : ℝ) •
    Complex.exp (((((-P : ℝ) : ℂ) + I * (Q : ℂ)) * (u : ℂ) ^ 2))

theorem norm_selbergOscillatoryGaussian
    {P Q theta u : ℝ} (hu : 0 ≤ u) :
    ‖selbergOscillatoryGaussian P Q theta u‖ =
      u ^ (-theta) * Real.exp (-P * u ^ 2) := by
  rw [selbergOscillatoryGaussian,
    norm_smul_of_nonneg (Real.rpow_nonneg hu _), Complex.norm_exp]
  congr 1
  norm_num [Complex.mul_re, pow_two]

theorem norm_intervalIntegral_selbergOscillatoryGaussian_damped_le
    {P Q theta x b : ℝ} (hP : 0 ≤ P) (hQ : 0 < Q)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x) (hxb : x ≤ b) :
    ‖∫ u in x..b, selbergOscillatoryGaussian P Q theta u‖ ≤
      2 * Real.exp (-P * x ^ 2) * x ^ (-theta - 1) / Q := by
  let C : ℂ := ((-P : ℝ) : ℂ) + I * (Q : ℂ)
  let E : ℝ → ℂ := fun u => Complex.exp (C * (u : ℂ) ^ 2)
  let V : ℝ → ℂ := fun u => E u / (2 * C)
  let w : ℝ → ℝ := fun u => u ^ (-theta - 1)
  let w' : ℝ → ℝ := fun u => (-theta - 1) * u ^ (-theta - 2)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hC : C ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp [C] at him
    linarith
  have hCnorm : Q ≤ ‖C‖ := by
    have him := Complex.abs_im_le_norm C
    simpa [C, abs_of_pos hQ] using him
  have hE_deriv : ∀ u ∈ Set.Icc x b,
      HasDerivAt E (E u * (2 * C * (u : ℂ))) u := by
    intro u _hu
    have hsq : HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2) (2 * (u : ℂ)) u := by
      simpa using (hasDerivAt_pow 2 u).ofReal_comp
    have harg : HasDerivAt (fun y : ℝ => C * (y : ℂ) ^ 2)
        (C * (2 * (u : ℂ))) u := by
      exact hsq.const_mul C
    simpa [E, mul_assoc, mul_left_comm, mul_comm] using harg.cexp
  have hV_deriv : ∀ u ∈ Set.Icc x b,
      HasDerivAt V ((u : ℝ) • E u) u := by
    intro u hu
    have h := (hE_deriv u hu).div_const (2 * C)
    convert h using 1
    · rfl
    · dsimp [E]
      push_cast
      field_simp [hC]
  have hw_deriv : ∀ u ∈ Set.Icc x b, HasDerivAt w (w' u) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hx0.trans_le hu.1)
    dsimp [w, w']
    convert (Real.hasDerivAt_rpow_const (p := -theta - 1) (Or.inl hu0)) using 1
    ring_nf
  have hV'_cont : ContinuousOn (fun u : ℝ => (u : ℝ) • E u)
      (Set.Icc x b) := by
    have hEcont : ContinuousOn E (Set.Icc x b) := by
      intro u hu
      exact (hE_deriv u hu).continuousAt.continuousWithinAt
    exact continuous_id.continuousOn.smul hEcont
  have hw'_cont : ContinuousOn w' (Set.Icc x b) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (hx0.trans_le hu.1)
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const u (-theta - 2) (Or.inl hu0))).continuousWithinAt
  have hV'_int : IntervalIntegrable (fun u : ℝ => (u : ℝ) • E u)
      volume x b := hV'_cont.intervalIntegrable_of_Icc hxb
  have hw'_int : IntervalIntegrable w' volume x b :=
    hw'_cont.intervalIntegrable_of_Icc hxb
  have hparts := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (a := x) (b := b) (u := w) (u' := w') (v := V)
    (v' := fun u : ℝ => (u : ℝ) • E u)
    (fun u hu => hw_deriv u (by simpa [uIcc_of_le hxb] using hu))
    (fun u hu => hV_deriv u (by simpa [uIcc_of_le hxb] using hu))
    hw'_int hV'_int
  have hleft :
      (∫ u in x..b, w u • ((u : ℝ) • E u)) =
        ∫ u in x..b, selbergOscillatoryGaussian P Q theta u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have huIcc : u ∈ Set.Icc x b := by
      simpa [uIcc_of_le hxb] using hu
    have hu0 : 0 < u := hx0.trans_le huIcc.1
    have hrpow : u ^ (-theta - 1) * u = u ^ (-theta) := by
      calc
        u ^ (-theta - 1) * u = u ^ (-theta - 1) * u ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = u ^ ((-theta - 1) + 1) := (Real.rpow_add hu0 _ _).symm
        _ = u ^ (-theta) := by congr 1 <;> ring
    simp only [w, smul_smul, smul_eq_mul, selbergOscillatoryGaussian]
    rw [show E u = Complex.exp ((((-P : ℝ) : ℂ) + I * (Q : ℂ)) *
        (u : ℂ) ^ 2) by rfl]
    push_cast
    rw [hrpow]
  have hV_bound : ∀ u ∈ Set.Icc x b,
      ‖V u‖ ≤ Real.exp (-P * x ^ 2) / Q := by
    intro u hu
    have hu0 : 0 ≤ u := (hx0.trans_le hu.1).le
    have hEnorm : ‖E u‖ = Real.exp (-P * u ^ 2) := by
      dsimp [E]
      rw [Complex.norm_exp]
      congr 1
      norm_num [C, Complex.mul_re, pow_two]
    have hxSq : x ^ 2 ≤ u ^ 2 := by nlinarith [hu.1]
    have hEle : ‖E u‖ ≤ Real.exp (-P * x ^ 2) := by
      rw [hEnorm]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hden : Q ≤ ‖2 * C‖ := by
      rw [norm_mul]
      norm_num
      nlinarith [norm_nonneg C]
    dsimp [V]
    rw [norm_div]
    calc
      ‖E u‖ / ‖(2 : ℂ) * C‖ ≤
          Real.exp (-P * x ^ 2) / ‖(2 : ℂ) * C‖ :=
        div_le_div_of_nonneg_right hEle (norm_nonneg _)
      _ ≤ Real.exp (-P * x ^ 2) / Q := by
        exact div_le_div_of_nonneg_left (Real.exp_pos _).le hQ hden
  have hw0 : ∀ u ∈ Set.Icc x b, 0 ≤ w u := by
    intro u hu
    exact Real.rpow_nonneg (hx0.trans_le hu.1).le _
  have hw'0 : ∀ u ∈ Set.Icc x b, w' u ≤ 0 := by
    intro u hu
    dsimp [w']
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
      (Real.rpow_nonneg (hx0.trans_le hu.1).le _)
  have hrem : ‖∫ u in x..b, w' u • V u‖ ≤
      (Real.exp (-P * x ^ 2) / Q) * (w x - w b) := by
    have hmajor : IntervalIntegrable
        (fun u => (-w' u) * (Real.exp (-P * x ^ 2) / Q)) volume x b :=
      hw'_int.neg.mul_const (Real.exp (-P * x ^ 2) / Q)
    calc
      ‖∫ u in x..b, w' u • V u‖ ≤
          ∫ u in x..b, (-w' u) * (Real.exp (-P * x ^ 2) / Q) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hxb ?_ hmajor
        filter_upwards with u hu
        have hu' : u ∈ Set.Icc x b := ⟨hu.1.le, hu.2⟩
        have hre : w' u • V u = (-w' u) • (-V u) := by simp
        rw [hre, norm_smul_of_nonneg (neg_nonneg.mpr (hw'0 u hu')), norm_neg]
        exact mul_le_mul_of_nonneg_left (hV_bound u hu')
          (neg_nonneg.mpr (hw'0 u hu'))
      _ = (Real.exp (-P * x ^ 2) / Q) * ∫ u in x..b, -w' u := by
        rw [intervalIntegral.integral_mul_const]
        ring
      _ = (Real.exp (-P * x ^ 2) / Q) * (w x - w b) := by
        rw [intervalIntegral.integral_neg,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun u hu => hw_deriv u (by simpa [uIcc_of_le hxb] using hu)) hw'_int]
        ring
  have hboundary : ‖w b • V b - w x • V x‖ ≤
      w b * (Real.exp (-P * x ^ 2) / Q) +
        w x * (Real.exp (-P * x ^ 2) / Q) := by
    refine (norm_sub_le _ _).trans ?_
    exact add_le_add
      (by
        rw [norm_smul_of_nonneg (hw0 b ⟨hxb, le_rfl⟩)]
        exact mul_le_mul_of_nonneg_left (hV_bound b ⟨hxb, le_rfl⟩)
          (hw0 b ⟨hxb, le_rfl⟩))
      (by
        rw [norm_smul_of_nonneg (hw0 x ⟨le_rfl, hxb⟩)]
        exact mul_le_mul_of_nonneg_left (hV_bound x ⟨le_rfl, hxb⟩)
          (hw0 x ⟨le_rfl, hxb⟩))
  have hparts' : (∫ u in x..b, selbergOscillatoryGaussian P Q theta u) =
      w b • V b - w x • V x - ∫ u in x..b, w' u • V u := by
    rw [← hleft]
    exact hparts
  calc
    ‖∫ u in x..b, selbergOscillatoryGaussian P Q theta u‖ =
        ‖w b • V b - w x • V x - ∫ u in x..b, w' u • V u‖ := by rw [hparts']
    _ ≤ ‖w b • V b - w x • V x‖ + ‖∫ u in x..b, w' u • V u‖ := norm_sub_le _ _
    _ ≤ (w b * (Real.exp (-P * x ^ 2) / Q) +
          w x * (Real.exp (-P * x ^ 2) / Q)) +
        (Real.exp (-P * x ^ 2) / Q) * (w x - w b) :=
      add_le_add hboundary hrem
    _ = 2 * Real.exp (-P * x ^ 2) * x ^ (-theta - 1) / Q := by
      dsimp [w]
      ring

theorem norm_intervalIntegral_selbergOscillatoryGaussian_le
    {P Q theta x b : ℝ} (hP : 0 ≤ P) (hQ : 0 < Q)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x) (hxb : x ≤ b) :
    ‖∫ u in x..b, selbergOscillatoryGaussian P Q theta u‖ ≤
      2 * x ^ (-theta - 1) / Q := by
  refine (norm_intervalIntegral_selbergOscillatoryGaussian_damped_le
    hP hQ htheta hx hxb).trans ?_
  have hExp : Real.exp (-P * x ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hP) (sq_nonneg x))
  have hTwoExp : 2 * Real.exp (-P * x ^ 2) ≤ (2 : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hExp (by norm_num : (0 : ℝ) ≤ 2)
  apply div_le_div_of_nonneg_right _ hQ.le
  exact mul_le_mul_of_nonneg_right
    hTwoExp
    (Real.rpow_nonneg (zero_le_one.trans hx) _)

theorem integrableOn_selbergOscillatoryGaussian_Ioi
    {P Q theta x : ℝ} (hP : 0 < P) (htheta : 0 ≤ theta) (hx : 1 ≤ x) :
    IntegrableOn (selbergOscillatoryGaussian P Q theta) (Ioi x) := by
  apply Integrable.mono' (integrable_exp_neg_mul_sq hP).integrableOn
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun u hu => ?_
    have hu0 : u ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hx.trans hu.le))
    change ContinuousAt (fun v : ℝ => (v ^ (-theta) : ℝ) •
      Complex.exp (((((-P : ℝ) : ℂ) + I * (Q : ℂ)) * (v : ℂ) ^ 2))) u
    exact (Real.continuousAt_rpow_const u (-theta) (Or.inl hu0)).smul (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := hx.trans hu.le
    rw [norm_selbergOscillatoryGaussian (zero_le_one.trans hu1)]
    exact (mul_le_mul_of_nonneg_right
      (Real.rpow_le_one_of_one_le_of_nonpos hu1 (by linarith))
      (Real.exp_pos _).le).trans_eq (one_mul _)

theorem norm_integral_Ioi_selbergOscillatoryGaussian_damped_le
    {P Q theta x : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x) :
    ‖∫ u in Ioi x, selbergOscillatoryGaussian P Q theta u‖ ≤
      2 * Real.exp (-P * x ^ 2) * x ^ (-theta - 1) / Q := by
  have hInt := integrableOn_selbergOscillatoryGaussian_Ioi (Q := Q) hP htheta hx
  have hlim : Tendsto
      (fun b : ℝ => ‖∫ u in x..b, selbergOscillatoryGaussian P Q theta u‖)
      atTop (nhds ‖∫ u in Ioi x, selbergOscillatoryGaussian P Q theta u‖) :=
    (intervalIntegral_tendsto_integral_Ioi x hInt tendsto_id).norm
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop x] with b hxb
  exact norm_intervalIntegral_selbergOscillatoryGaussian_damped_le
    hP.le hQ htheta hx hxb

theorem norm_integral_Ioi_selbergOscillatoryGaussian_le
    {P Q theta x : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x) :
    ‖∫ u in Ioi x, selbergOscillatoryGaussian P Q theta u‖ ≤
      2 * x ^ (-theta - 1) / Q := by
  refine (norm_integral_Ioi_selbergOscillatoryGaussian_damped_le
    hP hQ htheta hx).trans ?_
  have hExp : Real.exp (-P * x ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hP.le) (sq_nonneg x))
  have hTwoExp : 2 * Real.exp (-P * x ^ 2) ≤ (2 : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hExp (by norm_num : (0 : ℝ) ≤ 2)
  apply div_le_div_of_nonneg_right _ hQ.le
  exact mul_le_mul_of_nonneg_right hTwoExp
    (Real.rpow_nonneg (zero_le_one.trans hx) _)

/-- Titchmarsh 10.16, retaining the Gaussian damping needed by the
off-diagonal sum.  The preceding theorem saves one additional power of `x`. -/
theorem norm_integral_Ioi_selbergOscillatoryGaussian_damped_le_titchmarsh
    {P Q theta x : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x) :
    ‖∫ u in Ioi x, selbergOscillatoryGaussian P Q theta u‖ ≤
      2 * Real.exp (-P * x ^ 2) * x ^ (-theta) / Q := by
  refine (norm_integral_Ioi_selbergOscillatoryGaussian_damped_le
    hP hQ htheta hx).trans ?_
  apply div_le_div_of_nonneg_right _ hQ.le
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by positivity)

theorem norm_integral_Ioi_selbergOscillatoryGaussian_le_titchmarsh
    {P Q theta x : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (htheta : 0 ≤ theta) (hx : 1 ≤ x) :
    ‖∫ u in Ioi x, selbergOscillatoryGaussian P Q theta u‖ ≤
      2 * x ^ (-theta) / Q := by
  exact (norm_integral_Ioi_selbergOscillatoryGaussian_le hP hQ htheta hx).trans
    (by
      apply div_le_div_of_nonneg_right _ hQ.le
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith)) (by norm_num))

end HardyTheorem
