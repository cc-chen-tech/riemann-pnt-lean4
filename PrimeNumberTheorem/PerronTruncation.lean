import PrimeNumberTheorem.Perron

/-!
# Finite-height error for second-order Perron inversion

This module proves an explicit `O(exp (c*u) / W)` bound for truncating the
absolutely convergent second-order Perron integral to the interval `[-W, W]`.
-/

open Complex MeasureTheory Set Filter Topology

namespace PrimeNumberTheorem

theorem norm_secondOrderPerronKernel_le
    {c u w W : ℝ} (hW : 0 < W) (hw : W ≤ |w|) :
    ‖Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
      Real.exp (c * u) / (4 * Real.pi ^ 2 * w ^ 2) := by
  have hw0 : w ≠ 0 := by
    intro hwzero
    subst w
    simp at hw
    linarith
  have hden_pos : 0 < 4 * Real.pi ^ 2 * w ^ 2 := by positivity
  rw [norm_div, norm_pow, Complex.norm_exp]
  have hre : (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u).re = c * u := by
    simp
  rw [hre]
  rw [show (c : ℂ) + 2 * Real.pi * w * Complex.I =
      (c : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  apply div_le_div_of_nonneg_left (Real.exp_nonneg _) hden_pos
  nlinarith [sq_nonneg c]

theorem norm_integral_secondOrderPerronKernel_Ioi_le
    {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Set.Ioi W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
      Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
  let A : ℝ := Real.exp (c * u) / (4 * Real.pi ^ 2)
  have hpow : IntegrableOn (fun w : ℝ => w ^ (-2 : ℝ)) (Set.Ioi W) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hW
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hg : IntegrableOn (fun w : ℝ => A * w ^ (-2 : ℝ)) (Set.Ioi W) :=
    hpow.const_mul A
  calc
    ‖∫ w : ℝ in Set.Ioi W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
        ∫ w : ℝ in Set.Ioi W, A * w ^ (-2 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      have hw_pos : 0 < w := hW.trans hw
      calc
        ‖Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
            Real.exp (c * u) / (4 * Real.pi ^ 2 * w ^ 2) :=
          norm_secondOrderPerronKernel_le hW (by simpa [abs_of_pos hw_pos] using hw.le)
        _ = A * w ^ (-2 : ℝ) := by
          rw [Real.rpow_neg (le_of_lt hw_pos)]
          norm_num
          dsimp [A]
          field_simp
    _ = A * (∫ w : ℝ in Set.Ioi W, w ^ (-2 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A / W := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hW]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num]
      rw [Real.rpow_neg_one]
      field_simp
    _ = Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
      dsimp [A]
      field_simp

theorem norm_integral_secondOrderPerronKernel_Iic_le
    {c u W : ℝ} (hW : 0 < W) :
    ‖∫ w : ℝ in Set.Iic (-W),
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2‖ ≤
      Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2
  rw [← integral_comp_neg_Ioi W K]
  let A : ℝ := Real.exp (c * u) / (4 * Real.pi ^ 2)
  have hpow : IntegrableOn (fun w : ℝ => w ^ (-2 : ℝ)) (Set.Ioi W) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hW
  have hg : IntegrableOn (fun w : ℝ => A * w ^ (-2 : ℝ)) (Set.Ioi W) :=
    hpow.const_mul A
  calc
    ‖∫ w : ℝ in Set.Ioi W, K (-w)‖ ≤
        ∫ w : ℝ in Set.Ioi W, A * w ^ (-2 : ℝ) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      apply ae_restrict_of_forall_mem measurableSet_Ioi
      intro w hw
      have hw_pos : 0 < w := hW.trans hw
      calc
        ‖K (-w)‖ ≤ Real.exp (c * u) / (4 * Real.pi ^ 2 * (-w) ^ 2) := by
          apply norm_secondOrderPerronKernel_le hW
          simpa [abs_of_pos hw_pos] using hw.le
        _ = A * w ^ (-2 : ℝ) := by
          rw [neg_sq, Real.rpow_neg (le_of_lt hw_pos)]
          norm_num
          dsimp [A]
          field_simp
    _ = A * (∫ w : ℝ in Set.Ioi W, w ^ (-2 : ℝ)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = A / W := by
      rw [integral_Ioi_rpow_of_lt (by norm_num) hW]
      rw [show (-2 : ℝ) + 1 = -1 by norm_num]
      rw [Real.rpow_neg_one]
      field_simp
    _ = Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
      dsimp [A]
      field_simp

/-- Quantitative finite-height second-order Perron inversion. -/
theorem norm_truncated_secondOrderPerron_sub_max_le
    {c u W : ℝ} (hc : 0 < c) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
        ((max u 0 : ℝ) : ℂ)‖ ≤
      Real.exp (c * u) / (2 * Real.pi ^ 2 * W) := by
  let K : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2
  have hK : Integrable K := by
    simpa [K] using integrable_secondOrderPerronKernel c hc u
  have hWorder : -W ≤ W := by linarith
  have hinterval :
      (∫ w : ℝ in Set.Iic W, K w) - (∫ w : ℝ in Set.Iic (-W), K w) =
        ∫ w : ℝ in (-W)..W, K w :=
    intervalIntegral.integral_Iic_sub_Iic hK.integrableOn hK.integrableOn
  have hwhole :
      (∫ w : ℝ in Set.Iic W, K w) + (∫ w : ℝ in Set.Ioi W, K w) =
        ∫ w : ℝ, K w :=
    intervalIntegral.integral_Iic_add_Ioi hK.integrableOn hK.integrableOn
  have hdecomp :
      (∫ w : ℝ in (-W)..W, K w) - (∫ w : ℝ, K w) =
        -((∫ w : ℝ in Set.Iic (-W), K w) + (∫ w : ℝ in Set.Ioi W, K w)) := by
    rw [← hinterval, ← hwhole]
    abel
  rw [show ((max u 0 : ℝ) : ℂ) = ∫ w : ℝ, K w by
    simpa [K] using (secondOrderPerron_eq_max c hc u).symm]
  rw [show (fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
        ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) = K by rfl]
  rw [hdecomp, norm_neg]
  calc
    ‖(∫ w : ℝ in Set.Iic (-W), K w) + (∫ w : ℝ in Set.Ioi W, K w)‖ ≤
        ‖∫ w : ℝ in Set.Iic (-W), K w‖ + ‖∫ w : ℝ in Set.Ioi W, K w‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (c * u) / (4 * Real.pi ^ 2 * W) +
        Real.exp (c * u) / (4 * Real.pi ^ 2 * W) := by
      apply add_le_add
      · simpa [K] using norm_integral_secondOrderPerronKernel_Iic_le (c := c) (u := u) hW
      · simpa [K] using norm_integral_secondOrderPerronKernel_Ioi_le (c := c) (u := u) hW
    _ = Real.exp (c * u) / (2 * Real.pi ^ 2 * W) := by
      field_simp
      norm_num

end PrimeNumberTheorem
