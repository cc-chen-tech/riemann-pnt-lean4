import PrimeNumberTheorem.PerronTruncation

/-!
# Third-order Perron kernel and quadratic Riesz mean

This module constructs the genuine reciprocal-cubic Perron kernel.  It proves
Fourier inversion, the exact quadratic Riesz selector, and an explicit finite-
height truncation error of order `W⁻²`.  The result is an analytic prerequisite
for the actual-cubic Carlson energy chain; it does not yet assert a zeta contour
formula or a complete PNT oscillation transfer.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform BigOperators

namespace PrimeNumberTheorem

/-- Laplace transform of the normalized quadratic moment on the positive half-line. -/
theorem integral_sq_div_two_mul_cexp_Ioi (a : ℂ) (ha : a.re < 0) :
    (∫ u : ℝ in Set.Ioi 0, ((u : ℂ) ^ 2 / 2) * Complex.exp (a * u)) =
      -(1 / a ^ 3) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hint : IntegrableOn
      (fun u : ℝ => ((u : ℂ) ^ 2 / 2) * Complex.exp (a * u)) (Ioi 0) := by
    have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 2) (b := -a.re)
      (by norm_num) (by norm_num) (by linarith)
    apply Integrable.mono' hbase
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_pos : 0 < u := hu
      rw [norm_mul, norm_div, norm_pow, norm_real, norm_ofNat,
        Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu_pos]
      rw [Real.rpow_two, Real.rpow_one]
      have hexp : Real.exp (a.re * u) = Real.exp (-(-a.re) * u ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
        congr 1
        ring
      rw [hexp]
      simp only [Real.rpow_one]
      nlinarith [sq_nonneg u, Real.exp_pos (-(-a.re) * u)]
  let F : ℝ → ℂ := fun u =>
    Complex.exp (a * u) *
      (a ^ 2 * (u : ℂ) ^ 2 - 2 * a * u + 2) / (2 * a ^ 3)
  have hF : ∀ u : ℝ,
      HasDerivAt F (((u : ℂ) ^ 2 / 2) * Complex.exp (a * u)) u := by
    intro u
    let H : ℂ → ℂ := fun z =>
      Complex.exp (a * z) * (a ^ 2 * z ^ 2 - 2 * a * z + 2) /
        (2 * a ^ 3)
    have hH : HasDerivAt H (((u : ℂ) ^ 2 / 2) * Complex.exp (a * u)) (u : ℂ) := by
      have hexpD : HasDerivAt (fun z : ℂ => Complex.exp (a * z))
          (a * Complex.exp (a * (u : ℂ))) (u : ℂ) := by
        convert (Complex.hasDerivAt_exp (a * (u : ℂ))).comp (u : ℂ)
            ((hasDerivAt_id (u : ℂ)).const_mul a) using 1 <;>
          ring
      have hpolyD : HasDerivAt
          (fun z : ℂ => a ^ 2 * z ^ 2 - 2 * a * z + 2)
          (2 * a ^ 2 * (u : ℂ) - 2 * a) (u : ℂ) := by
        convert (((((hasDerivAt_id (u : ℂ)).pow 2).const_mul (a ^ 2)).sub
          ((hasDerivAt_id (u : ℂ)).const_mul (2 * a))).add_const 2) using 1 <;>
          simp only [id_eq] <;> ring
      have hprodD := hexpD.mul hpolyD
      have hdivD := hprodD.div_const (2 * a ^ 3)
      dsimp [H]
      convert hdivD using 1 <;> field_simp [ha0] <;> ring
    simpa [F, H] using hH.comp_ofReal
  have hexp : Tendsto (fun u : ℝ => Complex.exp (a * u)) atTop (nhds 0) := by
    simpa [Complex.tendsto_exp_nhds_zero_iff] using
      tendsto_const_nhds.neg_mul_atTop ha tendsto_id
  have hlinear : Tendsto
      (fun u : ℝ => (u : ℂ) * Complex.exp (a * u)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-a.re)
      (by linarith)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
    simp [Real.rpow_one]
  have hquadratic : Tendsto
      (fun u : ℝ => (u : ℂ) ^ 2 * Complex.exp (a * u)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (-a.re)
      (by linarith)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [norm_mul, norm_pow, norm_real, Complex.norm_exp,
      mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
      Real.norm_eq_abs, abs_of_pos hu]
    simp
  have hlim : Tendsto F atTop (nhds 0) := by
    have hparts : Tendsto
        (fun u : ℝ =>
          ((u : ℂ) ^ 2 * Complex.exp (a * u)) / (2 * a) -
            ((u : ℂ) * Complex.exp (a * u)) / a ^ 2 +
              Complex.exp (a * u) / a ^ 3) atTop (nhds 0) := by
      simpa using
        ((hquadratic.div_const (2 * a)).sub (hlinear.div_const (a ^ 2))).add
          (hexp.div_const (a ^ 3))
    refine hparts.congr' ?_
    filter_upwards with u
    dsimp [F]
    field_simp [ha0]
  have hzero : F 0 = 1 / a ^ 3 := by
    simp [F]
    field_simp [ha0]
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F)
    (f' := fun u : ℝ => ((u : ℂ) ^ 2 / 2) * Complex.exp (a * u))
    (a := 0) (m := 0)
    (by simpa [F] using (hF 0).continuousAt.continuousWithinAt)
    (fun u _ => hF u) hint hlim]
  rw [hzero]
  ring

noncomputable def thirdOrderPerronStep (c : ℝ) : ℝ → ℂ :=
  fun u : ℝ => (((max u 0) ^ 2 / 2 : ℝ) : ℂ) *
    Complex.exp (-c * max u 0)

theorem fourier_thirdOrderPerronStep (c : ℝ) (hc : 0 < c) (w : ℝ) :
    𝓕 (thirdOrderPerronStep c) w =
      1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [show (fun u : ℝ =>
      Complex.exp (↑(-2 * Real.pi * u * w) * Complex.I) •
        thirdOrderPerronStep c u) =
      Set.indicator (Set.Ioi 0) (fun u : ℝ =>
        ((u : ℂ) ^ 2 / 2) *
          Complex.exp ((-(c : ℂ) - 2 * Real.pi * w * Complex.I) * u)) by
    funext u
    by_cases hu : u ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hu]
      have hu' : 0 < u := Set.mem_Ioi.mp hu
      simp only [thirdOrderPerronStep, smul_eq_mul, max_eq_left hu'.le]
      rw [mul_left_comm, ← Complex.exp_add]
      congr 2
      · push_cast
        ring
      · push_cast
        ring
    · have hu0 : u ≤ 0 := le_of_not_gt hu
      simp [thirdOrderPerronStep, hu, max_eq_right hu0]]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  let s : ℂ := (c : ℂ) + 2 * Real.pi * w * Complex.I
  have hs0 : s ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    simp [s] at this
    linarith
  rw [integral_sq_div_two_mul_cexp_Ioi
    (-(c : ℂ) - 2 * Real.pi * w * Complex.I) (by simp [hc])]
  have hneg : -(c : ℂ) - 2 * Real.pi * w * Complex.I = -s := by
    simp [s]
    ring
  rw [hneg]
  change -(1 / (-s) ^ 3) = 1 / s ^ 3
  field_simp [hs0]

theorem integrable_thirdOrderPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (thirdOrderPerronStep c) := by
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := 2) (b := c) (by norm_num) (by norm_num) hc
  have hmajor : IntegrableOn
      (fun u : ℝ => ((u : ℂ) ^ 2 / 2) * Complex.exp (-c * u)) (Ioi 0) := by
    apply Integrable.mono' hbase
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu_pos : 0 < u := hu
      rw [norm_mul, norm_div, norm_pow, norm_real, norm_ofNat,
        Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu_pos]
      rw [Real.rpow_two, Real.rpow_one]
      simp only [neg_re, ofReal_re]
      nlinarith [sq_nonneg u, Real.exp_pos (-c * u)]
  apply (hmajor.integrable_indicator measurableSet_Ioi).congr
  filter_upwards with u
  by_cases hu : 0 < u
  · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hu)]
    simp [thirdOrderPerronStep, max_eq_left hu.le]
  · have hu0 : u ≤ 0 := le_of_not_gt hu
    rw [Set.indicator_of_notMem (by simpa using hu)]
    simp [thirdOrderPerronStep, max_eq_right hu0]

theorem integrable_fourier_thirdOrderPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (𝓕 (thirdOrderPerronStep c)) := by
  let s : ℝ → ℂ := fun w => (c : ℂ) + 2 * Real.pi * w * Complex.I
  have hg : Integrable (fun w : ℝ => 1 / (s w) ^ 2) := by
    apply (integrable_fourier_smoothPerronStep c hc).congr
    filter_upwards with w
    exact fourier_smoothPerronStep c hc w
  have hfmeas : AEStronglyMeasurable (fun w : ℝ => 1 / s w) := by
    have hcont : Continuous (fun w : ℝ => (s w)⁻¹) := by
      apply Continuous.inv₀
      · dsimp [s]
        fun_prop
      · intro w hs
        have := congrArg Complex.re hs
        simp [s] at this
        linarith
    simpa only [one_div] using hcont.aestronglyMeasurable
  have hfbound : ∀ᵐ w : ℝ, ‖(1 / s w : ℂ)‖ ≤ c⁻¹ := by
    filter_upwards with w
    have hc_norm : c ≤ ‖s w‖ := by
      calc
        c = |(s w).re| := by simp [s, abs_of_pos hc]
        _ ≤ ‖s w‖ := Complex.abs_re_le_norm _
    rw [one_div, norm_inv]
    exact (inv_le_inv₀ (lt_of_lt_of_le hc hc_norm) hc).2 hc_norm
  have hprod := hg.bdd_mul hfmeas hfbound
  apply hprod.congr
  filter_upwards with w
  rw [fourier_thirdOrderPerronStep c hc w]
  dsimp [s]
  have hs0 : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro hs
    have := congrArg Complex.re hs
    simp at this
    linarith
  field_simp [hs0]

theorem fourierInv_thirdOrderPerronKernel (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (𝓕⁻ (fun w : ℝ => (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3 : ℂ))) u =
      thirdOrderPerronStep c u := by
  have hcont : Continuous (thirdOrderPerronStep c) := by
    change Continuous (fun u : ℝ => (((max u 0) ^ 2 / 2 : ℝ) : ℂ) *
      Complex.exp (-c * max u 0))
    fun_prop
  have hinv := (integrable_thirdOrderPerronStep c hc).fourierInv_fourier_eq
    (v := u) (integrable_fourier_thirdOrderPerronStep c hc) hcont.continuousAt
  have hfun : (fun w : ℝ =>
      (1 / ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3 : ℂ)) =
      𝓕 (thirdOrderPerronStep c) := by
    funext w
    exact (fourier_thirdOrderPerronStep c hc w).symm
  rw [hfun]
  exact hinv

theorem integral_thirdOrderPerronKernel_eq (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (2 * Real.pi * (w : ℂ) * u * Complex.I) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) =
      thirdOrderPerronStep c u := by
  rw [← fourierInv_thirdOrderPerronKernel c hc u]
  rw [Real.fourierInv_eq']
  congr 1
  funext w
  simp only [smul_eq_mul, div_eq_mul_inv]
  congr 1
  · have hinner : inner ℝ w u = u * w := by
      exact RCLike.inner_apply w u
    rw [hinner]
    congr 1
    push_cast
    ring
  · simp

theorem thirdOrderPerron_eq_sq (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) =
      (((max u 0) ^ 2 / 2 : ℝ) : ℂ) := by
  rw [show (fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) =
      fun w : ℝ => Complex.exp ((c : ℂ) * u) *
        (Complex.exp (2 * Real.pi * (w : ℂ) * u * Complex.I) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) by
    funext w
    rw [show ((c : ℂ) + 2 * Real.pi * w * Complex.I) * u =
        (c : ℂ) * u + 2 * Real.pi * w * u * Complex.I by ring]
    rw [Complex.exp_add]
    ring]
  calc
    (∫ w : ℝ, Complex.exp ((c : ℂ) * u) *
        (Complex.exp (2 * Real.pi * (w : ℂ) * u * Complex.I) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3)) =
      Complex.exp ((c : ℂ) * u) *
        (∫ w : ℝ, Complex.exp (2 * Real.pi * (w : ℂ) * u * Complex.I) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) :=
      MeasureTheory.integral_const_mul _ _
    _ = Complex.exp ((c : ℂ) * u) * thirdOrderPerronStep c u := by
      rw [integral_thirdOrderPerronKernel_eq c hc u]
    _ = (((max u 0) ^ 2 / 2 : ℝ) : ℂ) := by
      by_cases hu : 0 < u
      · simp only [thirdOrderPerronStep, max_eq_left hu.le]
        calc
          Complex.exp ((c : ℂ) * u) *
              ((((u ^ 2 / 2 : ℝ) : ℂ)) * Complex.exp (-c * u)) =
              (((u ^ 2 / 2 : ℝ) : ℂ)) *
                (Complex.exp ((c : ℂ) * u) * Complex.exp (-c * u)) := by ring
          _ = (((u ^ 2 / 2 : ℝ) : ℂ)) := by
            rw [← Complex.exp_add]
            simp
          _ = (((u ^ 2 / 2 : ℝ) : ℂ)) := by push_cast; ring
      · have hu0 : u ≤ 0 := le_of_not_gt hu
        simp [thirdOrderPerronStep, max_eq_right hu0]

theorem norm_thirdOrderPerronKernel_le {c u w W : ℝ}
    (hW : 0 < W) (hw : W ≤ |w|) :
    ‖Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
      Real.exp (c * u) / (8 * Real.pi ^ 3 * |w| ^ 3) := by
  let s : ℂ := (c : ℂ) + 2 * Real.pi * w * Complex.I
  have hw_pos : 0 < |w| := lt_of_lt_of_le hW hw
  have hfreq_pos : 0 < 2 * Real.pi * |w| := by positivity
  have hfreq_norm : 2 * Real.pi * |w| ≤ ‖s‖ := by
    calc
      2 * Real.pi * |w| = |s.im| := by
        simp [s, abs_mul, abs_of_pos Real.pi_pos]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm _
  have hden_pos : 0 < 8 * Real.pi ^ 3 * |w| ^ 3 := by positivity
  rw [norm_div, Complex.norm_exp, norm_pow]
  have hre : ((((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).re = c * u := by
    simp
  rw [hre]
  apply div_le_div_of_nonneg_left (Real.exp_pos (c * u)).le hden_pos
  calc
    8 * Real.pi ^ 3 * |w| ^ 3 = (2 * Real.pi * |w|) ^ 3 := by ring
    _ ≤ ‖s‖ ^ 3 := by gcongr
    _ = ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ ^ 3 := by rfl

theorem norm_integral_thirdOrderPerronKernel_Ioi_le {c u W : ℝ}
    (hW : 0 < W) :
    ‖∫ w : ℝ in Ioi W,
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
      Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
  let A : ℝ := Real.exp (c * u) / (8 * Real.pi ^ 3)
  have hpow := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hW
  have hA : 0 ≤ A := by
    exact (div_pos (Real.exp_pos (c * u)) (by positivity)).le
  have hg := hpow.const_mul A
  calc
    ‖∫ w : ℝ in Ioi W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
        ∫ w : ℝ in Ioi W, A * w ^ (-3 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => by
        have hw_pos : 0 < w := lt_trans hW hw
        calc
          ‖Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
              ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
              Real.exp (c * u) / (8 * Real.pi ^ 3 * |w| ^ 3) :=
            norm_thirdOrderPerronKernel_le hW (by simpa [abs_of_pos hw_pos] using hw.le)
          _ = A * w ^ (-3 : ℝ) := by
            rw [abs_of_pos hw_pos, Real.rpow_neg hw_pos.le, Real.rpow_ofNat]
            dsimp [A]
            field_simp [ne_of_gt hw_pos, ne_of_gt Real.pi_pos]
    _ = A * (∫ w : ℝ in Ioi W, w ^ (-3 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A * (-W ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1)) := by
      rw [integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hW]
    _ = Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
      norm_num
      dsimp [A]
      field_simp [ne_of_gt hW, ne_of_gt Real.pi_pos]
      ring

theorem norm_integral_thirdOrderPerronKernel_Iic_le {c u W : ℝ}
    (hW : 0 < W) :
    ‖∫ w : ℝ in Iic (-W),
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3‖ ≤
      Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3
  rw [← integral_comp_neg_Ioi W K]
  let A : ℝ := Real.exp (c * u) / (8 * Real.pi ^ 3)
  have hpow := integrableOn_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hW
  have hA : 0 ≤ A := by
    exact (div_pos (Real.exp_pos (c * u)) (by positivity)).le
  have hg := hpow.const_mul A
  calc
    ‖∫ w : ℝ in Ioi W, K (-w)‖ ≤
        ∫ w : ℝ in Ioi W, A * w ^ (-3 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun w hw => by
        have hw_pos : 0 < w := lt_trans hW hw
        calc
          ‖K (-w)‖ ≤ Real.exp (c * u) / (8 * Real.pi ^ 3 * |-w| ^ 3) :=
            norm_thirdOrderPerronKernel_le hW (by
              rw [abs_neg, abs_of_pos hw_pos]
              exact hw.le)
          _ = A * w ^ (-3 : ℝ) := by
            rw [abs_neg, abs_of_pos hw_pos, Real.rpow_neg hw_pos.le, Real.rpow_ofNat]
            dsimp [A]
            field_simp [ne_of_gt hw_pos, ne_of_gt Real.pi_pos]
    _ = A * (∫ w : ℝ in Ioi W, w ^ (-3 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A * (-W ^ ((-3 : ℝ) + 1) / ((-3 : ℝ) + 1)) := by
      rw [integral_Ioi_rpow_of_lt (a := (-3 : ℝ)) (by norm_num) hW]
    _ = Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
      norm_num
      dsimp [A]
      field_simp [ne_of_gt hW, ne_of_gt Real.pi_pos]
      ring

theorem integrable_thirdOrderPerronKernel (c : ℝ) (hc : 0 < c) (u : ℝ) :
    Integrable (fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) := by
  let s : ℝ → ℂ := fun w => (c : ℂ) + 2 * Real.pi * w * Complex.I
  have hrec : Integrable (fun w : ℝ => 1 / (s w) ^ 3) := by
    apply (integrable_fourier_thirdOrderPerronStep c hc).congr
    filter_upwards with w
    exact fourier_thirdOrderPerronStep c hc w
  have hphaseMeas : AEStronglyMeasurable
      (fun w : ℝ => Complex.exp (2 * Real.pi * (w : ℂ) * u * Complex.I)) := by
    fun_prop
  have hphaseBound : ∀ᵐ w : ℝ,
      ‖Complex.exp (2 * Real.pi * (w : ℂ) * u * Complex.I)‖ ≤ 1 := by
    filter_upwards with w
    rw [Complex.norm_exp]
    simp
  have hphase := hrec.bdd_mul hphaseMeas hphaseBound
  have hscaled := hphase.const_mul (Complex.exp ((c : ℂ) * u))
  apply hscaled.congr
  filter_upwards with w
  dsimp [s]
  rw [show ((c : ℂ) + 2 * Real.pi * w * Complex.I) * u =
      (c : ℂ) * u + 2 * Real.pi * w * u * Complex.I by ring]
  rw [Complex.exp_add]
  field_simp

theorem norm_truncated_thirdOrderPerron_sub_sq_le {c u W : ℝ}
    (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in -W..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) -
        (((max u 0) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
      Real.exp (c * u) / (8 * Real.pi ^ 3 * W ^ 2) := by
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3
  have hK : Integrable K := integrable_thirdOrderPerronKernel c hc u
  have hinterval := intervalIntegral.integral_Iic_sub_Iic (a := -W) (b := W)
    hK.integrableOn hK.integrableOn
  have hwhole := intervalIntegral.integral_Iic_add_Ioi (b := W)
    hK.integrableOn hK.integrableOn
  have hdecomp :
      (∫ w : ℝ in -W..W, K w) - (∫ w : ℝ, K w) =
        -((∫ w : ℝ in Iic (-W), K w) + (∫ w : ℝ in Ioi W, K w)) := by
    rw [← hinterval, ← hwhole]
    abel
  rw [← thirdOrderPerron_eq_sq c hc u]
  change ‖(∫ w : ℝ in -W..W, K w) - (∫ w : ℝ, K w)‖ ≤ _
  rw [hdecomp, norm_neg]
  calc
    ‖(∫ w : ℝ in Iic (-W), K w) + (∫ w : ℝ in Ioi W, K w)‖ ≤
        ‖∫ w : ℝ in Iic (-W), K w‖ + ‖∫ w : ℝ in Ioi W, K w‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) +
        Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) :=
      add_le_add (norm_integral_thirdOrderPerronKernel_Iic_le hW)
        (norm_integral_thirdOrderPerronKernel_Ioi_le hW)
    _ = Real.exp (c * u) / (8 * Real.pi ^ 3 * W ^ 2) := by
      field_simp [ne_of_gt hW, ne_of_gt Real.pi_pos]
      ring

theorem integral_finset_thirdOrderPerron_eq {ι : Type*}
    (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ) (c : ℝ) (hc : 0 < c) :
    (∫ w : ℝ, ∑ i ∈ S, a i *
      (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3)) =
      ∑ i ∈ S, a i * ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ)) := by
  rw [MeasureTheory.integral_finset_sum S (fun i _ =>
    (integrable_thirdOrderPerronKernel c hc (u i)).const_mul (a i))]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (∫ w : ℝ, a i *
        (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3)) =
        a i * (∫ w : ℝ,
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3) :=
      MeasureTheory.integral_const_mul _ _
    _ = a i * ((((max (u i) 0) ^ 2 / 2 : ℝ) : ℂ)) := by
      rw [thirdOrderPerron_eq_sq c hc (u i)]

/-- The second Riesz mean selected by the cubic Perron kernel. -/
noncomputable def secondSmoothedChebyshevPsi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
    vonMangoldt n * (max (Real.log (x / n)) 0) ^ 2 / 2

theorem integral_vonMangoldt_thirdOrderPerron_eq (x c : ℝ) (hc : 0 < c) :
    (∫ w : ℝ,
      ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
        (vonMangoldt n : ℂ) *
          (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) *
              Real.log (x / n)) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 3)) =
      (secondSmoothedChebyshevPsi x : ℂ) := by
  rw [integral_finset_thirdOrderPerron_eq
    (Finset.Ico 1 (Nat.floor x + 1))
    (fun n => (vonMangoldt n : ℂ))
    (fun n => Real.log (x / n)) c hc]
  simp only [secondSmoothedChebyshevPsi, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end PrimeNumberTheorem
