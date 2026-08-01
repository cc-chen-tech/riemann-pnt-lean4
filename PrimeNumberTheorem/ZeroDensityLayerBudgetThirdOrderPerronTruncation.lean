import PrimeNumberTheorem.PerronTruncation
import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderPerronInversion

open Complex MeasureTheory Set Filter Topology

namespace PrimeNumberTheorem

theorem norm_thirdOrderPerronKernel_le
    {c u w W : ℝ} (hW : 0 < W) (hw : W ≤ |w|) :
    ‖exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 3‖ ≤
      Real.exp (c * u) / (8 * Real.pi ^ 3 * |w| ^ 3) := by
  have hw_abs : 0 < |w| := hW.trans_le hw
  let s : ℂ := (c : ℂ) + 2 * Real.pi * w * I
  have hs_norm : 2 * Real.pi * |w| ≤ ‖s‖ := by
    have him := abs_im_le_norm s
    dsimp [s] at him
    simp only [add_im, ofReal_im, zero_add, mul_im, ofReal_re, I_im, mul_one,
      I_re, mul_zero, sub_zero] at him
    simp only [add_zero] at him
    rw [abs_mul, abs_mul, abs_of_pos (show 0 < (2 : ℝ) from by norm_num),
      abs_of_pos Real.pi_pos] at him
    simpa [s, mul_assoc, mul_left_comm, mul_comm] using him
  have hs_pos : 0 < ‖s‖ := (mul_pos (mul_pos (by norm_num) Real.pi_pos) hw_abs).trans_le hs_norm
  have hden_pos : 0 < 8 * Real.pi ^ 3 * |w| ^ 3 := by positivity
  rw [norm_div, norm_pow, Complex.norm_exp]
  have hre : (s * u).re = c * u := by
    dsimp [s]
    simp
  rw [hre]
  calc
    Real.exp (c * u) / ‖s‖ ^ 3 ≤
        Real.exp (c * u) / (2 * Real.pi * |w|) ^ 3 := by
      apply div_le_div_of_nonneg_left (Real.exp_nonneg _)
        (by positivity)
      gcongr
    _ = Real.exp (c * u) / (8 * Real.pi ^ 3 * |w| ^ 3) := by ring

theorem integrable_thirdOrderPerronKernel
    (c : ℝ) (hc : 0 < c) (u : ℝ) :
    Integrable (fun w : ℝ =>
      exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) := by
  have hbase : Integrable (fun w : ℝ =>
      (1 / ((c : ℂ) + 2 * Real.pi * w * I) ^ 3 : ℂ)) := by
    exact (integrable_fourier_secondRieszPerronStep c hc).congr
      (Eventually.of_forall fun w => fourier_secondRieszPerronStep c hc w)
  have hmeas : AEStronglyMeasurable (fun w : ℝ =>
      exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) := by
    have hne (w : ℝ) : (c : ℂ) + 2 * Real.pi * w * I ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    exact ((by fun_prop : Continuous fun w : ℝ =>
      exp (((c : ℂ) + 2 * Real.pi * w * I) * u)).div₀
        (by fun_prop) (fun w => pow_ne_zero 3 (hne w))).aestronglyMeasurable
  apply Integrable.mono' (hbase.norm.const_mul (Real.exp (c * u))) hmeas
  filter_upwards with w
  rw [norm_div, norm_pow, Complex.norm_exp, norm_div, norm_one, norm_pow]
  have hre :
      ((((c : ℂ) + 2 * Real.pi * w * I) * u).re) = c * u := by simp
  rw [hre]
  simp [div_eq_mul_inv]

theorem norm_integral_thirdOrderPerronKernel_Ioi_le
    {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Ioi W,
        exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * I) ^ 3‖ ≤
      Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
  let A : ℝ := Real.exp (c * u) / (8 * Real.pi ^ 3)
  have hpow : IntegrableOn (fun w : ℝ => w ^ (-3 : ℝ)) (Ioi W) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hW
  have hg : IntegrableOn (fun w : ℝ => A * w ^ (-3 : ℝ)) (Ioi W) :=
    hpow.const_mul A
  calc
    ‖∫ w : ℝ in Ioi W,
        exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * I) ^ 3‖ ≤
        ∫ w : ℝ in Ioi W, A * w ^ (-3 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      have hw_pos : 0 < w := hW.trans hw
      calc
        ‖exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * I) ^ 3‖ ≤
            Real.exp (c * u) / (8 * Real.pi ^ 3 * |w| ^ 3) :=
          norm_thirdOrderPerronKernel_le hW
            (by simpa [abs_of_pos hw_pos] using hw.le)
        _ = A * w ^ (-3 : ℝ) := by
          rw [abs_of_pos hw_pos, Real.rpow_neg (le_of_lt hw_pos)]
          norm_num
          dsimp [A]
          field_simp
    _ = A * (∫ w : ℝ in Ioi W, w ^ (-3 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A * (W ^ (-2 : ℝ) / 2) := by
      rw [ExplicitFormulaResidues.integral_Ioi_rpow_neg_three W hW]
    _ = Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
      rw [Real.rpow_neg hW.le]
      dsimp [A]
      field_simp
      ring_nf
      congr 1
      exact (Real.rpow_natCast W 2).symm

theorem norm_integral_thirdOrderPerronKernel_Iic_le
    {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Iic (-W),
        exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * I) ^ 3‖ ≤
      Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
  let K : ℝ → ℂ := fun w =>
    exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * I) ^ 3
  rw [← integral_comp_neg_Ioi W K]
  let A : ℝ := Real.exp (c * u) / (8 * Real.pi ^ 3)
  have hpow : IntegrableOn (fun w : ℝ => w ^ (-3 : ℝ)) (Ioi W) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hW
  have hg : IntegrableOn (fun w : ℝ => A * w ^ (-3 : ℝ)) (Ioi W) :=
    hpow.const_mul A
  calc
    ‖∫ w : ℝ in Ioi W, K (-w)‖ ≤
        ∫ w : ℝ in Ioi W, A * w ^ (-3 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      have hw_pos : 0 < w := hW.trans hw
      calc
        ‖K (-w)‖ ≤ Real.exp (c * u) /
            (8 * Real.pi ^ 3 * |-w| ^ 3) := by
          apply norm_thirdOrderPerronKernel_le hW
          simpa [abs_of_pos hw_pos] using hw.le
        _ = A * w ^ (-3 : ℝ) := by
          rw [abs_neg, abs_of_pos hw_pos, Real.rpow_neg (le_of_lt hw_pos)]
          norm_num
          dsimp [A]
          field_simp
    _ = A * (∫ w : ℝ in Ioi W, w ^ (-3 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A * (W ^ (-2 : ℝ) / 2) := by
      rw [ExplicitFormulaResidues.integral_Ioi_rpow_neg_three W hW]
    _ = Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
      rw [Real.rpow_neg hW.le]
      dsimp [A]
      field_simp
      ring_nf
      congr 1
      exact (Real.rpow_natCast W 2).symm

/-- Quantitative finite-height third-order Perron inversion with an explicit
quadratic truncation error. -/
theorem norm_truncated_thirdOrderPerron_sub_half_sq_max_le
    {c u W : ℝ} (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) -
        ((((max u 0) ^ 2 / 2 : ℝ) : ℂ))‖ ≤
      Real.exp (c * u) / (8 * Real.pi ^ 3 * W ^ 2) := by
  let K : ℝ → ℂ := fun w =>
    exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * I) ^ 3
  have hK : Integrable K := by
    simpa [K] using integrable_thirdOrderPerronKernel c hc u
  have hinterval :
      (∫ w : ℝ in Iic W, K w) - (∫ w : ℝ in Iic (-W), K w) =
        ∫ w : ℝ in (-W)..W, K w :=
    intervalIntegral.integral_Iic_sub_Iic hK.integrableOn hK.integrableOn
  have hwhole :
      (∫ w : ℝ in Iic W, K w) + (∫ w : ℝ in Ioi W, K w) =
        ∫ w : ℝ, K w :=
    intervalIntegral.integral_Iic_add_Ioi hK.integrableOn hK.integrableOn
  have hdecomp :
      (∫ w : ℝ in (-W)..W, K w) - (∫ w : ℝ, K w) =
        -((∫ w : ℝ in Iic (-W), K w) + (∫ w : ℝ in Ioi W, K w)) := by
    rw [← hinterval, ← hwhole]
    abel
  rw [show ((((max u 0) ^ 2 / 2 : ℝ) : ℂ)) = ∫ w : ℝ, K w by
    simpa [K] using (thirdOrderPerron_eq_half_sq_max c hc u).symm]
  rw [show (fun w : ℝ =>
      exp (((c : ℂ) + 2 * Real.pi * w * I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * I) ^ 3) = K by rfl]
  rw [hdecomp, norm_neg]
  calc
    ‖(∫ w : ℝ in Iic (-W), K w) + (∫ w : ℝ in Ioi W, K w)‖ ≤
        ‖∫ w : ℝ in Iic (-W), K w‖ + ‖∫ w : ℝ in Ioi W, K w‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) +
        Real.exp (c * u) / (16 * Real.pi ^ 3 * W ^ 2) := by
      apply add_le_add
      · simpa [K] using norm_integral_thirdOrderPerronKernel_Iic_le
          (c := c) (u := u) hW
      · simpa [K] using norm_integral_thirdOrderPerronKernel_Ioi_le
          (c := c) (u := u) hW
    _ = Real.exp (c * u) / (8 * Real.pi ^ 3 * W ^ 2) := by ring

end PrimeNumberTheorem
