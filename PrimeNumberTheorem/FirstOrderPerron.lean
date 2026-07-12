import PrimeNumberTheorem.PerronTruncation

set_option maxHeartbeats 800000

/-!
# First-order Perron inversion

This module proves the conditionally convergent ordinary Perron kernel by
integrating by parts against the already established, absolutely convergent
second-order kernel.  At the jump it computes the symmetric truncation
directly, giving the standard half weight.
-/

open Complex MeasureTheory Set Filter Topology

namespace PrimeNumberTheorem

/-- The Heaviside step with the symmetric Perron half weight at the jump. -/
noncomputable def perronHalfStep (u : ℝ) : ℂ :=
  if 0 < u then 1 else if u = 0 then (1 / 2 : ℂ) else 0

private noncomputable def firstOrderBoundaryPrimitive (c u : ℝ) (w : ℝ) : ℂ :=
  Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
    ((c : ℂ) + 2 * Real.pi * w * Complex.I)

private lemma hasDerivAt_firstOrderBoundaryPrimitive
    {c u w : ℝ} (hc : 0 < c) :
    HasDerivAt (firstOrderBoundaryPrimitive c u)
      ((2 * Real.pi * Complex.I) *
        (u * firstOrderBoundaryPrimitive c u w -
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) w := by
  let H : ℂ → ℂ := fun z =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * z * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * z * Complex.I)
  have hden : (c : ℂ) + 2 * Real.pi * (w : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hH : HasDerivAt H
      ((2 * Real.pi * Complex.I) *
        (u * H w -
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2)) (w : ℂ) := by
    dsimp [H]
    convert (((Complex.hasDerivAt_exp
      (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).comp (w : ℂ)
        (((((hasDerivAt_id (w : ℂ)).const_mul (2 * Real.pi : ℂ)).mul_const Complex.I)
          |>.const_add (c : ℂ)).mul_const u)).div
            (((((hasDerivAt_id (w : ℂ)).const_mul (2 * Real.pi : ℂ)).mul_const Complex.I)
              |>.const_add (c : ℂ))) hden) using 1 <;>
      simp only [Function.comp_apply, id_eq] <;> field_simp <;> ring
  simpa [firstOrderBoundaryPrimitive, H] using hH.comp_ofReal

/-- Integration by parts reduces a finite first-order Perron integral to its
two endpoint values and the finite second-order Perron integral. -/
lemma intervalIntegral_firstOrderPerron_eq_boundary_add_secondOrder
    {c u W : ℝ} (hc : 0 < c) (hu : u ≠ 0) :
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
      (firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)) /
        ((2 * Real.pi * Complex.I) * u) +
      (1 / u : ℂ) *
        (∫ w : ℝ in (-W)..W,
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
  let K₂ : ℝ → ℂ := fun w =>
    Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
      ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2
  let D : ℝ → ℂ := fun w =>
    (2 * Real.pi * Complex.I) *
      (u * firstOrderBoundaryPrimitive c u w - K₂ w)
  have hden_all : ∀ w : ℝ,
      (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
    intro w h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hFcont : Continuous (firstOrderBoundaryPrimitive c u) := by
    unfold firstOrderBoundaryPrimitive
    exact (by fun_prop : Continuous fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).div₀
        (by fun_prop) hden_all
  have hK₂cont : Continuous K₂ := by
    dsimp [K₂]
    exact (by fun_prop : Continuous fun w : ℝ =>
      Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u)).div₀
        (by fun_prop) (fun w => pow_ne_zero 2 (hden_all w))
  have hDcont : Continuous D := by
    dsimp [D]
    fun_prop
  have hD : (∫ w : ℝ in (-W)..W, D w) =
      firstOrderBoundaryPrimitive c u W -
        firstOrderBoundaryPrimitive c u (-W) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro w _hw
      simpa [D, K₂] using hasDerivAt_firstOrderBoundaryPrimitive
        (c := c) (u := u) (w := w) hc
    · exact hDcont.intervalIntegrable _ _
  calc
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        ∫ w : ℝ in (-W)..W,
          (1 / ((2 * Real.pi * Complex.I) * u)) * D w +
            (1 / u : ℂ) * K₂ w := by
      apply intervalIntegral.integral_congr
      intro w _hw
      have hden : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      dsimp [D, K₂, firstOrderBoundaryPrimitive]
      field_simp
      simp [hu]
    _ = (1 / ((2 * Real.pi * Complex.I) * u)) *
          (∫ w : ℝ in (-W)..W, D w) +
        (1 / u : ℂ) * (∫ w : ℝ in (-W)..W, K₂ w) := by
      let f : ℝ → ℂ := fun w =>
        (1 / ((2 * Real.pi * Complex.I) * u)) * D w
      let g : ℝ → ℂ := fun w => (1 / u : ℂ) * K₂ w
      have hf : IntervalIntegrable f volume (-W) W := by
        exact (continuous_const.mul hDcont).intervalIntegrable _ _
      have hg : IntervalIntegrable g volume (-W) W := by
        exact (continuous_const.mul hK₂cont).intervalIntegrable _ _
      have hfconst : (∫ w : ℝ in (-W)..W, f w) =
          (1 / ((2 * Real.pi * Complex.I) * u)) *
            (∫ w : ℝ in (-W)..W, D w) := by
        simpa only [f] using
          (intervalIntegral.integral_const_mul
            (a := -W) (b := W)
            (1 / ((2 * Real.pi * Complex.I) * u)) D)
      have hgconst : (∫ w : ℝ in (-W)..W, g w) =
          (1 / u : ℂ) * (∫ w : ℝ in (-W)..W, K₂ w) := by
        simpa only [g] using
          (intervalIntegral.integral_const_mul
            (a := -W) (b := W) (1 / u : ℂ) K₂)
      calc
        (∫ w : ℝ in (-W)..W,
            (1 / ((2 * Real.pi * Complex.I) * u)) * D w +
              (1 / u : ℂ) * K₂ w) =
            (∫ w : ℝ in (-W)..W, f w) +
              (∫ w : ℝ in (-W)..W, g w) := by
                simpa [f, g] using intervalIntegral.integral_add hf hg
        _ = (1 / ((2 * Real.pi * Complex.I) * u)) *
              (∫ w : ℝ in (-W)..W, D w) +
            (1 / u : ℂ) * (∫ w : ℝ in (-W)..W, K₂ w) := by
              rw [hfconst, hgconst]
    _ = (firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)) /
        ((2 * Real.pi * Complex.I) * u) +
      (1 / u : ℂ) *
        (∫ w : ℝ in (-W)..W,
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) := by
      rw [hD]
      simp only [K₂, div_eq_mul_inv]
      ring

private lemma norm_firstOrderBoundaryPrimitive_le
    {c u w W : ℝ} (hW : 0 < W) (hw : W ≤ |w|) :
    ‖firstOrderBoundaryPrimitive c u w‖ ≤
      Real.exp (c * u) / (2 * Real.pi * W) := by
  have hw_pos : 0 < |w| := hW.trans_le hw
  have hsmall_pos : 0 < 2 * Real.pi * W := by positivity
  rw [firstOrderBoundaryPrimitive, norm_div, Complex.norm_exp]
  have hre :
      (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u).re = c * u := by
    simp
  rw [hre]
  have him_le : 2 * Real.pi * |w| ≤
      ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ := by
    have hbase := abs_im_le_norm
      ((c : ℂ) + 2 * Real.pi * w * Complex.I)
    simpa [abs_mul, abs_of_pos Real.pi_pos] using hbase
  have hW_le : 2 * Real.pi * W ≤
      ‖(c : ℂ) + 2 * Real.pi * w * Complex.I‖ := by
    exact (mul_le_mul_of_nonneg_left hw (by positivity)).trans him_le
  exact div_le_div_of_nonneg_left (Real.exp_nonneg _) hsmall_pos hW_le

private lemma perronHalfStep_eq_inv_mul_max {u : ℝ} (hu : u ≠ 0) :
    perronHalfStep u = (1 / u : ℂ) * ((max u 0 : ℝ) : ℂ) := by
  rcases lt_or_gt_of_ne hu with hu_neg | hu_pos
  · rw [perronHalfStep]
    simp [not_lt_of_ge hu_neg.le, hu, max_eq_right hu_neg.le]
  · rw [perronHalfStep, if_pos hu_pos, max_eq_left hu_pos.le]
    simpa [one_div] using (inv_mul_cancel₀ (ofReal_ne_zero.mpr hu)).symm

/-- Quantitative ordinary Perron inversion away from the jump.  Integration
by parts and the second-order truncation estimate give an explicit
`O(exp(c*u) / (|u| W))` error. -/
theorem norm_truncated_firstOrderPerron_sub_halfStep_le_of_ne_zero
    {c u W : ℝ} (hc : 0 < c) (hu : u ≠ 0) (hW : 0 < W) :
    ‖(∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) -
        perronHalfStep u‖ ≤
      Real.exp (c * u) / (Real.pi ^ 2 * |u| * W) := by
  rw [intervalIntegral_firstOrderPerron_eq_boundary_add_secondOrder hc hu,
    perronHalfStep_eq_inv_mul_max hu]
  let B : ℂ :=
    (firstOrderBoundaryPrimitive c u W -
      firstOrderBoundaryPrimitive c u (-W)) /
        ((2 * Real.pi * Complex.I) * u)
  let E : ℂ :=
    (1 / u : ℂ) *
      ((∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
        ((max u 0 : ℝ) : ℂ))
  have hrewrite :
      (firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)) /
          ((2 * Real.pi * Complex.I) * u) +
        (1 / u : ℂ) *
          (∫ w : ℝ in (-W)..W,
            Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
              ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
        (1 / u : ℂ) * ((max u 0 : ℝ) : ℂ) = B + E := by
    dsimp [B, E]
    ring
  rw [hrewrite]
  have hBW : ‖firstOrderBoundaryPrimitive c u W‖ ≤
      Real.exp (c * u) / (2 * Real.pi * W) :=
    norm_firstOrderBoundaryPrimitive_le hW (by simp [abs_of_pos hW])
  have hBnegW : ‖firstOrderBoundaryPrimitive c u (-W)‖ ≤
      Real.exp (c * u) / (2 * Real.pi * W) :=
    norm_firstOrderBoundaryPrimitive_le hW (by simp [abs_of_pos hW])
  have hB : ‖B‖ ≤ Real.exp (c * u) /
      (2 * Real.pi ^ 2 * |u| * W) := by
    dsimp [B]
    rw [norm_div]
    have hdennorm :
        ‖(2 * Real.pi * Complex.I) * (u : ℂ)‖ =
          2 * Real.pi * |u| := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, norm_real,
        norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    rw [hdennorm]
    have hnum := (norm_sub_le _ _).trans (add_le_add hBW hBnegW)
    have hnum' : ‖firstOrderBoundaryPrimitive c u W -
        firstOrderBoundaryPrimitive c u (-W)‖ ≤
        Real.exp (c * u) / (Real.pi * W) := by
      calc
        ‖firstOrderBoundaryPrimitive c u W -
            firstOrderBoundaryPrimitive c u (-W)‖ ≤
            Real.exp (c * u) / (2 * Real.pi * W) +
              Real.exp (c * u) / (2 * Real.pi * W) := hnum
        _ = Real.exp (c * u) / (Real.pi * W) := by
          field_simp
          ring
    have hden_pos : 0 < 2 * Real.pi * |u| := by positivity
    calc
      ‖firstOrderBoundaryPrimitive c u W -
          firstOrderBoundaryPrimitive c u (-W)‖ / (2 * Real.pi * |u|) ≤
          (Real.exp (c * u) / (Real.pi * W)) /
            (2 * Real.pi * |u|) := by
              exact div_le_div_of_nonneg_right hnum' hden_pos.le
      _ = Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) := by
            field_simp
  have hE : ‖E‖ ≤ Real.exp (c * u) /
      (2 * Real.pi ^ 2 * |u| * W) := by
    dsimp [E]
    rw [norm_mul, norm_div, norm_one, norm_real, Real.norm_eq_abs]
    have hsecond := norm_truncated_secondOrderPerron_sub_max_le
      (c := c) (u := u) hc hW
    calc
      (1 / |u|) *
          ‖(∫ w : ℝ in (-W)..W,
            Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
              ((c : ℂ) + 2 * Real.pi * w * Complex.I) ^ 2) -
            ((max u 0 : ℝ) : ℂ)‖ ≤
          (1 / |u|) * (Real.exp (c * u) /
            (2 * Real.pi ^ 2 * W)) :=
              mul_le_mul_of_nonneg_left hsecond (by positivity)
      _ = Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) := by
            field_simp [abs_ne_zero.mpr hu]
  calc
    ‖B + E‖ ≤ ‖B‖ + ‖E‖ := norm_add_le _ _
    _ ≤ Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) +
        Real.exp (c * u) / (2 * Real.pi ^ 2 * |u| * W) :=
      add_le_add hB hE
    _ = Real.exp (c * u) / (Real.pi ^ 2 * |u| * W) := by
      field_simp
      ring

private lemma intervalIntegral_real_firstOrderPerron_zero
    {c W : ℝ} (hc : 0 < c) :
    (∫ w : ℝ in (-W)..W,
      c / (c ^ 2 + (2 * Real.pi * w) ^ 2)) =
        Real.arctan (2 * Real.pi * W / c) / Real.pi := by
  let f : ℝ → ℝ := fun x => (c ^ 2 + x ^ 2)⁻¹
  have hscale :
      (∫ w : ℝ in (-W)..W, f (2 * Real.pi * w)) =
        (2 * Real.pi)⁻¹ *
          (∫ x : ℝ in (2 * Real.pi * (-W))..(2 * Real.pi * W), f x) := by
    exact intervalIntegral.integral_comp_mul_left
      (a := -W) (b := W) f (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  calc
    (∫ w : ℝ in (-W)..W,
        c / (c ^ 2 + (2 * Real.pi * w) ^ 2)) =
        (∫ w : ℝ in (-W)..W, c * f (2 * Real.pi * w)) := by
      apply intervalIntegral.integral_congr
      intro w _hw
      simp [f, div_eq_mul_inv]
    _ = c * (∫ w : ℝ in (-W)..W, f (2 * Real.pi * w)) := by
      exact intervalIntegral.integral_const_mul
        (a := -W) (b := W) c (fun w => f (2 * Real.pi * w))
    _ = c * ((2 * Real.pi)⁻¹ *
        (∫ x : ℝ in (2 * Real.pi * (-W))..(2 * Real.pi * W), f x)) := by
      rw [hscale]
    _ = Real.arctan (2 * Real.pi * W / c) / Real.pi := by
      simp only [f, integral_inv_sq_add_sq hc.ne']
      rw [show 2 * Real.pi * (-W) / c = -(2 * Real.pi * W / c) by ring,
        Real.arctan_neg]
      field_simp [Real.pi_ne_zero, hc.ne']
      ring

private lemma intervalIntegral_im_firstOrderPerron_zero
    {c W : ℝ} :
    (∫ w : ℝ in (-W)..W,
      (2 * Real.pi * w) / (c ^ 2 + (2 * Real.pi * w) ^ 2)) = 0 := by
  let g : ℝ → ℝ := fun w =>
    (2 * Real.pi * w) / (c ^ 2 + (2 * Real.pi * w) ^ 2)
  have hodd : (fun w : ℝ => g (-w)) = fun w => -g w := by
    funext w
    dsimp [g]
    ring
  have hsym := intervalIntegral.integral_comp_neg
    (a := -W) (b := W) g
  have hneg : -(∫ w : ℝ in (-W)..W, g w) =
      (∫ w : ℝ in (-W)..W, g w) := by
    rw [hodd, intervalIntegral.integral_neg] at hsym
    simpa using hsym
  have hzero : (∫ w : ℝ in (-W)..W, g w) = 0 := by
    linarith
  simpa [g] using hzero

/-- At the discontinuity, the symmetric finite Perron integral is an arctangent
approximant.  Its limit is therefore exactly the standard half weight. -/
theorem intervalIntegral_firstOrderPerron_zero_eq
    {c W : ℝ} (hc : 0 < c) :
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * 0) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
      (Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) := by
  let r : ℝ → ℝ := fun w =>
    c / (c ^ 2 + (2 * Real.pi * w) ^ 2)
  let g : ℝ → ℝ := fun w =>
    (2 * Real.pi * w) / (c ^ 2 + (2 * Real.pi * w) ^ 2)
  have hden_real : ∀ w : ℝ,
      c ^ 2 + (2 * Real.pi * w) ^ 2 ≠ 0 := by
    intro w
    positivity
  have hrcont : Continuous r := by
    dsimp [r]
    exact (by fun_prop : Continuous fun _w : ℝ => c).div₀
      (by fun_prop) hden_real
  have hgcont : Continuous g := by
    dsimp [g]
    exact (by fun_prop : Continuous fun w : ℝ => 2 * Real.pi * w).div₀
      (by fun_prop) hden_real
  have hrint : IntervalIntegrable (fun w => (r w : ℂ)) volume (-W) W :=
    (Complex.continuous_ofReal.comp hrcont).intervalIntegrable _ _
  have hgint : IntervalIntegrable
      (fun w => Complex.I * (g w : ℂ)) volume (-W) W :=
    (continuous_const.mul (Complex.continuous_ofReal.comp hgcont)).intervalIntegrable _ _
  calc
    (∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * 0) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I)) =
        ∫ w : ℝ in (-W)..W, (r w : ℂ) - Complex.I * (g w : ℂ) := by
      apply intervalIntegral.integral_congr
      intro w _hw
      have hden : (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp at hre
        linarith
      simp only [mul_zero, Complex.exp_zero]
      dsimp [r, g]
      rw [one_div, Complex.inv_def]
      simp [Complex.normSq_apply]
      rw [starRingEnd_apply, star_ofNat]
      ring
    _ = (∫ w : ℝ in (-W)..W, (r w : ℂ)) -
        (∫ w : ℝ in (-W)..W, Complex.I * (g w : ℂ)) :=
      intervalIntegral.integral_sub hrint hgint
    _ = (Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) := by
      have hI :
          (∫ w : ℝ in (-W)..W, Complex.I * (g w : ℂ)) =
            Complex.I * (∫ w : ℝ in (-W)..W, (g w : ℂ)) := by
        exact intervalIntegral.integral_const_mul
          (a := -W) (b := W) Complex.I (fun w => (g w : ℂ))
      rw [hI]
      simp only [intervalIntegral.integral_ofReal]
      rw [intervalIntegral_real_firstOrderPerron_zero hc]
      rw [show (∫ w : ℝ in (-W)..W, g w) = 0 by
        simpa [g] using intervalIntegral_im_firstOrderPerron_zero (c := c) (W := W)]
      simp

/-- Symmetrically truncated ordinary Perron inversion, including the half
weight at the discontinuity. -/
theorem tendsto_truncated_firstOrderPerronKernel_atTop
    (c : ℝ) (hc : 0 < c) (u : ℝ) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W)..W,
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u) /
          ((c : ℂ) + 2 * Real.pi * w * Complex.I))
      atTop (nhds (perronHalfStep u)) := by
  by_cases hu : u = 0
  · subst u
    have harg : Tendsto (fun W : ℝ => 2 * Real.pi * W / c) atTop atTop := by
      have hcoef : 0 < 2 * Real.pi / c := by positivity
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
        (tendsto_mul_const_atTop_of_pos hcoef).2 tendsto_id
    have hatan : Tendsto
        (fun W : ℝ => Real.arctan (2 * Real.pi * W / c)) atTop
        (nhds (Real.pi / 2)) :=
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
    have hreal : Tendsto
        (fun W : ℝ => Real.arctan (2 * Real.pi * W / c) / Real.pi) atTop
        (nhds ((Real.pi / 2) / Real.pi)) := hatan.div_const Real.pi
    have hcomplex : Tendsto
        (fun W : ℝ =>
          ((Real.arctan (2 * Real.pi * W / c) / Real.pi : ℝ) : ℂ)) atTop
        (nhds (((Real.pi / 2) / Real.pi : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
    convert hcomplex using 1
    · funext W
      exact intervalIntegral_firstOrderPerron_zero_eq hc
    · simp only [perronHalfStep, lt_self_iff_false, ↓reduceIte, one_div]
      field_simp [ofReal_ne_zero.mpr Real.pi_ne_zero]
      congr 1
      norm_num
  · apply tendsto_iff_norm_sub_tendsto_zero.2
    let A : ℝ := Real.exp (c * u) / (Real.pi ^ 2 * |u|)
    have hAdiv : Tendsto (fun W : ℝ => A / W) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero' (Eventually.of_forall fun W => norm_nonneg _)
      _ hAdiv
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with W hW
    have hbound :=
      norm_truncated_firstOrderPerron_sub_halfStep_le_of_ne_zero
        (c := c) (u := u) hc hu hW
    simpa [A, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hbound

/-- Finite-sum ordinary Perron inversion.  Terms exactly on the jump receive
weight `1/2`; positive and negative logarithmic offsets receive weights `1`
and `0`, respectively. -/
theorem tendsto_truncated_finset_firstOrderPerron_atTop
    {ι : Type*} (S : Finset ι) (a : ι → ℂ) (u : ι → ℝ)
    (c : ℝ) (hc : 0 < c) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W)..W, ∑ i ∈ S,
        a i *
          (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I)))
      atTop (nhds (∑ i ∈ S, a i * perronHalfStep (u i))) := by
  have hsum : Tendsto
      (fun W : ℝ => ∑ i ∈ S, a i *
        (∫ w : ℝ in (-W)..W,
          Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I)))
      atTop (nhds (∑ i ∈ S, a i * perronHalfStep (u i))) := by
    apply tendsto_finset_sum
    intro i hi
    exact (tendsto_truncated_firstOrderPerronKernel_atTop c hc (u i)).const_mul (a i)
  convert hsum using 1
  funext W
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact intervalIntegral.integral_const_mul
      (a := -W) (b := W) (a i)
        (fun w => Complex.exp
          (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i) /
            ((c : ℂ) + 2 * Real.pi * w * Complex.I))
  · intro i hi
    have hden : ∀ w : ℝ,
        (c : ℂ) + 2 * Real.pi * w * Complex.I ≠ 0 := by
      intro w h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    exact (continuous_const.mul
      ((by fun_prop : Continuous fun w : ℝ =>
        Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) * u i)).div₀
          (by fun_prop) hden)).intervalIntegrable _ _

private lemma jumpVonMangoldt_natCast (m : ℕ) :
    jumpVonMangoldt (m : ℝ) = vonMangoldt m := by
  classical
  let h : ∃ n : ℕ, (m : ℝ) = (n : ℝ) := ⟨m, rfl⟩
  rw [jumpVonMangoldt, dif_pos h]
  apply congrArg vonMangoldt
  exact_mod_cast (Classical.choose_spec h).symm

/-- The half-step center produced by first-order Perron inversion is exactly
the midpoint Chebyshev function `psi0`. -/
lemma sum_vonMangoldt_perronHalfStep_log_div_eq_chebyshevPsi0
    (x : ℝ) (hx : 0 < x) :
    (∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
      (vonMangoldt n : ℂ) * perronHalfStep (Real.log (x / n))) =
        (chebyshevPsi0 x : ℂ) := by
  classical
  by_cases hex : ∃ m : ℕ, x = (m : ℝ)
  · obtain ⟨m, rfl⟩ := hex
    have hm_pos : 0 < m := by exact_mod_cast hx
    have hm_mem : m ∈ Finset.Ico 1 (Nat.floor (m : ℝ) + 1) := by
      rw [Finset.mem_Ico, Nat.floor_natCast]
      exact ⟨hm_pos, Nat.lt_succ_self m⟩
    have hterm : ∀ n ∈ Finset.Ico 1 (Nat.floor (m : ℝ) + 1),
        (vonMangoldt n : ℂ) *
            perronHalfStep (Real.log ((m : ℝ) / n)) =
          (vonMangoldt n : ℂ) -
            if n = m then (vonMangoldt n : ℂ) / 2 else 0 := by
      intro n hn
      rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
      have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn_one
      have hn_le : n ≤ m := by
        simpa using (Nat.lt_add_one_iff.mp (by simpa using hn_upper))
      by_cases hnm : n = m
      · subst n
        simp [perronHalfStep, hm_pos.ne']
        ring
      · have hn_lt : n < m := lt_of_le_of_ne hn_le hnm
        have hratio : (1 : ℝ) < (m : ℝ) / n := by
          exact (one_lt_div (by exact_mod_cast hn_pos)).2 (by exact_mod_cast hn_lt)
        have hlog : 0 < Real.log ((m : ℝ) / n) := Real.log_pos hratio
        simp [perronHalfStep, hlog, hnm]
    calc
      (∑ n ∈ Finset.Ico 1 (Nat.floor (m : ℝ) + 1),
          (vonMangoldt n : ℂ) *
            perronHalfStep (Real.log ((m : ℝ) / n))) =
          ∑ n ∈ Finset.Ico 1 (Nat.floor (m : ℝ) + 1),
            ((vonMangoldt n : ℂ) -
              if n = m then (vonMangoldt n : ℂ) / 2 else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact hterm n hn
      _ = (∑ n ∈ Finset.Ico 1 (Nat.floor (m : ℝ) + 1),
            (vonMangoldt n : ℂ)) - (vonMangoldt m : ℂ) / 2 := by
        rw [Finset.sum_sub_distrib]
        simp [Nat.ne_of_gt hm_pos]
      _ = (chebyshevPsi0 (m : ℝ) : ℂ) := by
        rw [chebyshevPsi0, jumpVonMangoldt_natCast]
        rw [chebyshevPsi, Complex.ofReal_sub, Complex.ofReal_sum,
          Complex.ofReal_div]
        norm_num
  · have hjump : jumpVonMangoldt x = 0 := by
      rw [jumpVonMangoldt, dif_neg hex]
    rw [chebyshevPsi0, hjump, zero_div, sub_zero, chebyshevPsi,
      Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hn_one, hn_upper⟩
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn_one)
    have hn_floor : n ≤ Nat.floor x := by omega
    have hn_floor_real : (n : ℝ) ≤ (Nat.floor x : ℝ) := by
      exact_mod_cast hn_floor
    have hnx_le : (n : ℝ) ≤ x :=
      hn_floor_real.trans (Nat.floor_le hx.le)
    have hnx_ne : (n : ℝ) ≠ x := by
      intro h
      exact hex ⟨n, h.symm⟩
    have hnx : (n : ℝ) < x := lt_of_le_of_ne hnx_le hnx_ne
    have hratio : (1 : ℝ) < x / n := (one_lt_div hn_pos).2 hnx
    have hlog : 0 < Real.log (x / n) := Real.log_pos hratio
    simp [perronHalfStep, hlog]

/-- First-order Perron inversion specialized to the finite von Mangoldt sum.
The symmetric limit recovers the midpoint Chebyshev function `psi0`, including
the half contribution when `x` is a prime-power integer. -/
theorem tendsto_truncated_vonMangoldt_firstOrderPerron_atTop
    {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Tendsto
      (fun W : ℝ => ∫ w : ℝ in (-W)..W,
        ∑ n ∈ Finset.Ico 1 (Nat.floor x + 1),
          (vonMangoldt n : ℂ) *
            (Complex.exp (((c : ℂ) + 2 * Real.pi * w * Complex.I) *
              Real.log (x / n)) /
                ((c : ℂ) + 2 * Real.pi * w * Complex.I)))
      atTop (nhds (chebyshevPsi0 x : ℂ)) := by
  have h := tendsto_truncated_finset_firstOrderPerron_atTop
    (Finset.Ico 1 (Nat.floor x + 1))
    (fun n => (vonMangoldt n : ℂ))
    (fun n => Real.log (x / n)) c hc
  simpa [sum_vonMangoldt_perronHalfStep_log_div_eq_chebyshevPsi0 x hx] using h

end PrimeNumberTheorem
