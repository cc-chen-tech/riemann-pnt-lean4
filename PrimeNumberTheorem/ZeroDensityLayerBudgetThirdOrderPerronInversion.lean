import PrimeNumberTheorem.Perron
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderPerronKernel

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace PrimeNumberTheorem

/-- Complex Laplace transform of the second moment on the positive half-line. -/
theorem integral_sq_mul_cexp_Ioi (a : ℂ) (ha : a.re < 0) :
    (∫ u : ℝ in Ioi 0, (u : ℂ) ^ 2 * exp (a * u)) = -2 / a ^ 3 := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hint : IntegrableOn (fun u : ℝ => (u : ℂ) ^ 2 * exp (a * u)) (Ioi 0) := by
    apply Integrable.mono'
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2)
        (b := -a.re) (by norm_num) (by norm_num) (by linarith))
    · fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [norm_mul, norm_pow, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_two]
  let F : ℝ → ℂ := fun u =>
    exp (a * u) * (a ^ 2 * (u : ℂ) ^ 2 - 2 * a * u + 2) / a ^ 3
  have hF : ∀ u : ℝ, HasDerivAt F ((u : ℂ) ^ 2 * exp (a * u)) u := by
    intro u
    let H : ℂ → ℂ := fun z =>
      exp (a * z) * (a ^ 2 * z ^ 2 - 2 * a * z + 2) / a ^ 3
    have hexp : HasDerivAt (fun z : ℂ => exp (a * z))
        (a * exp (a * u)) (u : ℂ) := by
      convert (Complex.hasDerivAt_exp (a * u)).comp (u : ℂ)
        ((hasDerivAt_id (u : ℂ)).const_mul a) using 1 <;> ring
    have hpoly : HasDerivAt
        (fun z : ℂ => a ^ 2 * z ^ 2 - 2 * a * z + 2)
        (2 * a ^ 2 * u - 2 * a) (u : ℂ) := by
      convert ((((hasDerivAt_id (u : ℂ)).pow 2).const_mul (a ^ 2)).sub
        ((hasDerivAt_id (u : ℂ)).const_mul (2 * a))).add_const 2 using 1 <;>
        simp only [id_eq] <;> ring
    have hH : HasDerivAt H ((u : ℂ) ^ 2 * exp (a * u)) (u : ℂ) := by
      dsimp [H]
      convert (hexp.mul hpoly).div_const (a ^ 3) using 1 <;>
        field_simp [ha0] <;> ring
    simpa [F, H] using hH.comp_ofReal
  have hlim : Tendsto F atTop (𝓝 0) := by
    have hexp : Tendsto (fun u : ℝ => exp (a * u)) atTop (𝓝 0) := by
      simpa [Complex.tendsto_exp_nhds_zero_iff] using
        tendsto_const_nhds.neg_mul_atTop ha tendsto_id
    have hmul : Tendsto (fun u : ℝ => (u : ℂ) * exp (a * u)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-a.re) (by linarith)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [norm_mul, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_one]
    have hsqmul : Tendsto (fun u : ℝ => (u : ℂ) ^ 2 * exp (a * u)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (-a.re) (by linarith)).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      rw [norm_mul, norm_pow, norm_real, Complex.norm_exp, mul_re, ofReal_re, ofReal_im,
        mul_zero, sub_zero, Real.norm_eq_abs, abs_of_pos hu]
      simp [Real.rpow_two]
    have hcomb : Tendsto
        (fun u : ℝ =>
          ((u : ℂ) ^ 2 * exp (a * u)) / a -
            2 * (((u : ℂ) * exp (a * u)) / a ^ 2) +
            2 * (exp (a * u) / a ^ 3)) atTop (𝓝 0) := by
      simpa using
        ((hsqmul.div_const a).sub
          (tendsto_const_nhds.mul (hmul.div_const (a ^ 2)))).add
            (tendsto_const_nhds.mul (hexp.div_const (a ^ 3)))
    refine hcomb.congr' ?_
    filter_upwards with u
    dsimp [F]
    field_simp
  have hzero : F 0 = 2 / a ^ 3 := by
    simp [F]
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := F) (f' := fun u : ℝ => (u : ℂ) ^ 2 * exp (a * u))
    (a := 0) (m := 0) (by simpa [F] using (hF 0).continuousAt.continuousWithinAt)
    (fun u _ => hF u) hint hlim]
  rw [hzero]
  ring

/-- Continuous one-sided quadratic ramp corresponding to the cubic Perron kernel. -/
noncomputable def secondRieszPerronStep (c : ℝ) : ℝ → ℂ :=
  fun u => ((((max u 0) ^ 2 / 2 : ℝ) : ℂ) * exp (-c * max u 0))

theorem fourier_secondRieszPerronStep (c : ℝ) (hc : 0 < c) (w : ℝ) :
    𝓕 (secondRieszPerronStep c) w =
      1 / ((c : ℂ) + 2 * Real.pi * w * I) ^ 3 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [show (fun u : ℝ =>
      exp (↑(-2 * Real.pi * u * w) * I) • secondRieszPerronStep c u) =
      indicator (Ioi 0) (fun u : ℝ =>
        ((u : ℂ) ^ 2 / 2) *
          exp ((-(c : ℂ) - 2 * Real.pi * w * I) * u)) by
    funext u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu]
      have hu' : 0 < u := mem_Ioi.mp hu
      simp only [secondRieszPerronStep, smul_eq_mul, max_eq_left hu'.le]
      rw [mul_assoc, mul_left_comm (exp _), ← exp_add]
      congr 1
      · push_cast
        ring
      · apply congrArg exp
        push_cast
        ring
    · have hu0 : u ≤ 0 := le_of_not_gt hu
      simp [secondRieszPerronStep, hu, max_eq_right hu0]]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  rw [show (fun u : ℝ =>
      ((u : ℂ) ^ 2 / 2) * exp ((-(c : ℂ) - 2 * Real.pi * w * I) * u)) =
      fun u : ℝ => (1 / 2 : ℂ) *
        ((u : ℂ) ^ 2 * exp ((-(c : ℂ) - 2 * Real.pi * w * I) * u)) by
    funext u
    ring]
  calc
    _ = (1 / 2 : ℂ) *
        (∫ u : ℝ in Ioi 0,
          (u : ℂ) ^ 2 * exp ((-(c : ℂ) - 2 * Real.pi * w * I) * u)) :=
      MeasureTheory.integral_const_mul _ _
    _ = _ := by
      rw [integral_sq_mul_cexp_Ioi
        (-(c : ℂ) - 2 * Real.pi * w * I) (by simp [hc])]
      have hs0 : (c : ℂ) + 2 * Real.pi * w * I ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      rw [show -(c : ℂ) - 2 * Real.pi * w * I =
          -((c : ℂ) + 2 * Real.pi * w * I) by ring]
      field_simp [hs0]

theorem integrable_secondRieszPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (secondRieszPerronStep c) := by
  have hbase : IntegrableOn
      (fun u : ℝ => u ^ (2 : ℝ) * Real.exp (-c * u)) (Ioi 0) :=
    by
      simpa [Real.rpow_one] using
        (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 2)
          (b := c) (by norm_num) (by norm_num) hc)
  have hind : Integrable (indicator (Ioi 0)
      (fun u : ℝ => u ^ (2 : ℝ) * Real.exp (-c * u))) :=
    hbase.integrable_indicator measurableSet_Ioi
  apply Integrable.mono' hind
  · unfold secondRieszPerronStep
    fun_prop
  · filter_upwards with u
    by_cases hu : 0 < u
    · rw [indicator_of_mem (mem_Ioi.mpr hu)]
      simp only [secondRieszPerronStep, max_eq_left hu.le, ofReal_div, ofReal_pow]
      rw [norm_mul, norm_div, norm_pow, norm_real, Complex.norm_exp,
        Real.norm_eq_abs, abs_of_pos hu]
      norm_num
      have hnonneg : 0 ≤ u ^ 2 * Real.exp (-(c * u)) :=
        mul_nonneg (sq_nonneg u) (Real.exp_pos _).le
      linarith
    · have hu0 : u ≤ 0 := le_of_not_gt hu
      simp [secondRieszPerronStep, hu, max_eq_right hu0]

theorem integrable_fourier_secondRieszPerronStep (c : ℝ) (hc : 0 < c) :
    Integrable (𝓕 (secondRieszPerronStep c)) := by
  rw [integrable_congr
    (Eventually.of_forall (fourier_secondRieszPerronStep c hc))]
  have hsq : Integrable (fun w : ℝ =>
      (1 / ((c : ℂ) + 2 * Real.pi * w * I) ^ 2 : ℂ)) :=
    (integrable_fourier_smoothPerronStep c hc).congr
      (Eventually.of_forall fun w => fourier_smoothPerronStep c hc w)
  have hne (w : ℝ) : (c : ℂ) + 2 * Real.pi * w * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hmeas : AEStronglyMeasurable
      (fun w : ℝ => 1 / ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) :=
    (continuous_const.div₀ (by fun_prop)
      (fun w => pow_ne_zero 3 (hne w))).aestronglyMeasurable
  apply Integrable.mono' (hsq.norm.const_mul (1 / c)) hmeas
  filter_upwards with w
  let s : ℂ := (c : ℂ) + 2 * Real.pi * w * I
  have hs0 : s ≠ 0 := hne w
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hc_norm : c ≤ ‖s‖ := by
    rw [show s = (c : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * I by
      dsimp [s]
      push_cast
      ring]
    rw [← sq_le_sq₀ hc.le (norm_nonneg _), Complex.sq_norm, Complex.normSq_add_mul_I]
    nlinarith [sq_nonneg (2 * Real.pi * w)]
  change ‖(1 / s ^ 3 : ℂ)‖ ≤ (1 / c) * ‖(1 / s ^ 2 : ℂ)‖
  rw [norm_div, norm_one, norm_pow, norm_div, norm_one, norm_pow]
  calc
    1 / ‖s‖ ^ 3 = (1 / ‖s‖ ^ 2) * (1 / ‖s‖) := by field_simp
    _ ≤ (1 / ‖s‖ ^ 2) * (1 / c) := by
      exact mul_le_mul_of_nonneg_left
        (one_div_le_one_div_of_le hc hc_norm) (by positivity)
    _ = (1 / c) * (1 / ‖s‖ ^ 2) := by ring

theorem fourierInv_thirdOrderPerronKernel (c : ℝ) (hc : 0 < c) (u : ℝ) :
    𝓕⁻ (fun w : ℝ =>
      (1 / ((c : ℂ) + 2 * Real.pi * w * I) ^ 3 : ℂ)) u =
      secondRieszPerronStep c u := by
  have hcont : Continuous (secondRieszPerronStep c) := by
    unfold secondRieszPerronStep
    fun_prop
  have hinv : 𝓕⁻ (𝓕 (secondRieszPerronStep c)) u = secondRieszPerronStep c u :=
    (integrable_secondRieszPerronStep c hc).fourierInv_fourier_eq
      (integrable_fourier_secondRieszPerronStep c hc) (v := u) hcont.continuousAt
  rw [show 𝓕 (secondRieszPerronStep c) =
      (fun w : ℝ => (1 / ((c : ℂ) + 2 * Real.pi * w * I) ^ 3 : ℂ)) by
    funext w
    exact fourier_secondRieszPerronStep c hc w] at hinv
  exact hinv

/-- Exact third-order Perron formula recovering the second Riesz ramp. -/
theorem thirdOrderPerron_eq_half_sq_max (c : ℝ) (hc : 0 < c) (u : ℝ) :
    (∫ w : ℝ, exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) =
      ((((max u 0) ^ 2 / 2 : ℝ) : ℂ)) := by
  have hfourier :
      (∫ w : ℝ, exp (2 * Real.pi * (w * u) * I) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) = secondRieszPerronStep c u := by
    rw [← fourierInv_thirdOrderPerronKernel c hc u, Real.fourierInv_eq']
    congr 1
    funext w
    simp only [smul_eq_mul, one_div]
    rw [div_eq_mul_inv]
    rw [show inner ℝ w u = w * u by change u * w = w * u; ring]
    push_cast
    ring
  rw [show (fun w : ℝ =>
      exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) =
      (fun w : ℝ => exp (c * u) *
        (exp (2 * Real.pi * (w * u) * I) /
          ((c : ℂ) + 2 * Real.pi * w * I) ^ 3)) by
    funext w
    rw [show (((c : ℂ) + 2 * Real.pi * w * I) * u) =
        (c * u : ℝ) + 2 * Real.pi * (w * u) * I by push_cast; ring, exp_add]
    push_cast
    ring]
  calc
    _ = exp (c * u) *
        (∫ w : ℝ, exp (2 * Real.pi * (w * u) * I) /
          ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) := integral_const_mul _ _
    _ = exp (c * u) * secondRieszPerronStep c u := by rw [hfourier]
    _ = ((((max u 0) ^ 2 / 2 : ℝ) : ℂ)) := by
      by_cases hu : 0 < u
      · simp only [secondRieszPerronStep, max_eq_left hu.le]
        rw [mul_left_comm, ← exp_add]
        simp
      · have hu0 : u ≤ 0 := le_of_not_gt hu
        simp [secondRieszPerronStep, max_eq_right hu0]

end PrimeNumberTheorem
