import MathlibAux.BoundaryRectResidue

open Complex MeasureTheory Set
open scoped Interval

namespace MathlibAux

private lemma hasDerivAt_neg_inv_horizontal
    {y x : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun x : ℝ => -(((x : ℂ) + (y : ℂ) * I)⁻¹))
      (1 / ((x : ℂ) + (y : ℂ) * I) ^ 2) x := by
  have hzne : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hy this
  have hz : HasDerivAt (fun z : ℂ => z + (y : ℂ) * I) 1 (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)
  have h := (hz.inv hzne).neg
  simpa only [neg_div, neg_neg] using h.comp_ofReal

private lemma hasDerivAt_neg_inv_vertical
    {x y : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => -(((x : ℂ) + (y : ℂ) * I)⁻¹))
      (I / ((x : ℂ) + (y : ℂ) * I) ^ 2) y := by
  have hzne : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hx this
  have hz : HasDerivAt (fun z : ℂ => (x : ℂ) + z * I) I (y : ℂ) := by
    simpa using (hasDerivAt_id (y : ℂ)).mul_const I |>.const_add (x : ℂ)
  have h := (hz.inv hzne).neg
  simpa only [neg_div, neg_neg] using h.comp_ofReal

theorem boundaryRectIntegral_inv_sq_eq_zero
    {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => z⁻¹ ^ 2) x0 x1 y0 y1 = 0 := by
  let Fx (y : ℝ) : ℝ → ℂ := fun x => -(((x : ℂ) + (y : ℂ) * I)⁻¹)
  let Fy (x : ℝ) : ℝ → ℂ := fun y => -(((x : ℂ) + (y : ℂ) * I)⁻¹)
  have hhorizontal (y : ℝ) (hy : y ≠ 0) :
      (∫ x : ℝ in x0..x1, (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2) =
        Fx y x1 - Fx y x0 := by
    have hderiv :
        deriv (Fx y) =
          fun x : ℝ => 1 / ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
      funext x
      exact (hasDerivAt_neg_inv_horizontal hy).deriv
    have hdiff : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℝ (Fx y) x :=
      fun x _ => (hasDerivAt_neg_inv_horizontal hy).differentiableAt
    have hden : Continuous (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I) ^ 2) :=
      (Complex.continuous_ofReal.add continuous_const).pow 2
    have hden_ne : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I) ^ 2 ≠ 0 := by
      intro x
      apply pow_ne_zero
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact hy him
    have hcont : ContinuousOn
        (fun x : ℝ => 1 / ((x : ℂ) + (y : ℂ) * I) ^ 2)
        (Set.uIcc x0 x1) :=
      (continuous_const.div₀ hden hden_ne).continuousOn
    simpa [one_div, inv_pow] using
      intervalIntegral.integral_deriv_eq_sub' (Fx y) hderiv hdiff hcont
  have hvertical (x : ℝ) (hx : x ≠ 0) :
      I * (∫ y : ℝ in y0..y1, (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2) =
        Fy x y1 - Fy x y0 := by
    have hderiv :
        deriv (Fy x) =
          fun y : ℝ => I / ((x : ℂ) + (y : ℂ) * I) ^ 2 := by
      funext y
      exact (hasDerivAt_neg_inv_vertical hx).deriv
    have hdiff : ∀ y ∈ Set.uIcc y0 y1, DifferentiableAt ℝ (Fy x) y :=
      fun y _ => (hasDerivAt_neg_inv_vertical hx).differentiableAt
    have hden : Continuous (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I) ^ 2) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 2
    have hden_ne : ∀ y : ℝ, ((x : ℂ) + (y : ℂ) * I) ^ 2 ≠ 0 := by
      intro y
      apply pow_ne_zero
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      exact hx hre
    have hcont : ContinuousOn
        (fun y : ℝ => I / ((x : ℂ) + (y : ℂ) * I) ^ 2)
        (Set.uIcc y0 y1) :=
      (continuous_const.div₀ hden hden_ne).continuousOn
    have hfund :=
      intervalIntegral.integral_deriv_eq_sub' (Fy x) hderiv hdiff hcont
    have hfun :
        (fun y : ℝ => I / ((x : ℂ) + (y : ℂ) * I) ^ 2) =
          fun y : ℝ => I * (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2 := by
      funext y
      simp [div_eq_mul_inv, inv_pow]
    rw [hfun] at hfund
    have hmul :
        (∫ y : ℝ in y0..y1,
          I * (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2) =
          I * ∫ y : ℝ in y0..y1,
            (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2 :=
      intervalIntegral.integral_const_mul I
        (fun y : ℝ => (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2)
    rw [hmul] at hfund
    exact hfund
  have hb := hhorizontal y0 hy0
  have ht := hhorizontal y1 hy1
  have hr := hvertical x1 hx1
  have hl := hvertical x0 hx0
  unfold boundaryRectIntegral
  simp only [smul_eq_mul]
  rw [hb, ht, hr, hl]
  dsimp [Fx, Fy]
  ring

private lemma hasDerivAt_neg_half_inv_sq_horizontal
    {y x : ℝ} (hy : y ≠ 0) :
    HasDerivAt
      (fun x : ℝ => (-(2 : ℂ)⁻¹) *
        (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2)
      (1 / ((x : ℂ) + (y : ℂ) * I) ^ 3) x := by
  have hzne : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hy this
  have hz : HasDerivAt (fun z : ℂ => z + (y : ℂ) * I) 1 (x : ℂ) :=
    (hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)
  have h := ((hz.inv hzne).pow 2).const_mul (-((2 : ℂ)⁻¹))
  have hc := h.comp_ofReal
  simp only [Pi.inv_apply, Pi.pow_apply] at hc
  change HasDerivAt
    (fun x : ℝ => (-(2 : ℂ)⁻¹) *
      (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2) _ x at hc
  convert hc using 1
  norm_num
  field_simp [hzne]

private lemma hasDerivAt_neg_half_inv_sq_vertical
    {x y : ℝ} (hx : x ≠ 0) :
    HasDerivAt
      (fun y : ℝ => (-(2 : ℂ)⁻¹) *
        (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2)
      (I / ((x : ℂ) + (y : ℂ) * I) ^ 3) y := by
  have hzne : (x : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hx this
  have hz : HasDerivAt (fun z : ℂ => (x : ℂ) + z * I) I (y : ℂ) := by
    simpa using (hasDerivAt_id (y : ℂ)).mul_const I |>.const_add (x : ℂ)
  have h := ((hz.inv hzne).pow 2).const_mul (-((2 : ℂ)⁻¹))
  have hc := h.comp_ofReal
  simp only [Pi.inv_apply, Pi.pow_apply] at hc
  change HasDerivAt
    (fun y : ℝ => (-(2 : ℂ)⁻¹) *
      (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2) _ y at hc
  convert hc using 1
  norm_num
  field_simp [hzne]

theorem boundaryRectIntegral_inv_cube_eq_zero
    {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => z⁻¹ ^ 3) x0 x1 y0 y1 = 0 := by
  let Fx (y : ℝ) : ℝ → ℂ := fun x =>
    (-(2 : ℂ)⁻¹) * (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2
  let Fy (x : ℝ) : ℝ → ℂ := fun y =>
    (-(2 : ℂ)⁻¹) * (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 2
  have hhorizontal (y : ℝ) (hy : y ≠ 0) :
      (∫ x : ℝ in x0..x1, (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 3) =
        Fx y x1 - Fx y x0 := by
    have hderiv :
        deriv (Fx y) =
          fun x : ℝ => 1 / ((x : ℂ) + (y : ℂ) * I) ^ 3 := by
      funext x
      exact (hasDerivAt_neg_half_inv_sq_horizontal hy).deriv
    have hdiff : ∀ x ∈ Set.uIcc x0 x1, DifferentiableAt ℝ (Fx y) x :=
      fun x _ => (hasDerivAt_neg_half_inv_sq_horizontal hy).differentiableAt
    have hden : Continuous (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I) ^ 3) :=
      (Complex.continuous_ofReal.add continuous_const).pow 3
    have hden_ne : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I) ^ 3 ≠ 0 := by
      intro x
      apply pow_ne_zero
      intro h
      have him := congrArg Complex.im h
      simp at him
      exact hy him
    have hcont : ContinuousOn
        (fun x : ℝ => 1 / ((x : ℂ) + (y : ℂ) * I) ^ 3)
        (Set.uIcc x0 x1) :=
      (continuous_const.div₀ hden hden_ne).continuousOn
    simpa [one_div, inv_pow] using
      intervalIntegral.integral_deriv_eq_sub' (Fx y) hderiv hdiff hcont
  have hvertical (x : ℝ) (hx : x ≠ 0) :
      I * (∫ y : ℝ in y0..y1, (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 3) =
        Fy x y1 - Fy x y0 := by
    have hderiv :
        deriv (Fy x) =
          fun y : ℝ => I / ((x : ℂ) + (y : ℂ) * I) ^ 3 := by
      funext y
      exact (hasDerivAt_neg_half_inv_sq_vertical hx).deriv
    have hdiff : ∀ y ∈ Set.uIcc y0 y1, DifferentiableAt ℝ (Fy x) y :=
      fun y _ => (hasDerivAt_neg_half_inv_sq_vertical hx).differentiableAt
    have hden : Continuous (fun y : ℝ => ((x : ℂ) + (y : ℂ) * I) ^ 3) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).pow 3
    have hden_ne : ∀ y : ℝ, ((x : ℂ) + (y : ℂ) * I) ^ 3 ≠ 0 := by
      intro y
      apply pow_ne_zero
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      exact hx hre
    have hcont : ContinuousOn
        (fun y : ℝ => I / ((x : ℂ) + (y : ℂ) * I) ^ 3)
        (Set.uIcc y0 y1) :=
      (continuous_const.div₀ hden hden_ne).continuousOn
    have hfund :=
      intervalIntegral.integral_deriv_eq_sub' (Fy x) hderiv hdiff hcont
    have hfun :
        (fun y : ℝ => I / ((x : ℂ) + (y : ℂ) * I) ^ 3) =
          fun y : ℝ => I * (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 3 := by
      funext y
      simp [div_eq_mul_inv, inv_pow]
    rw [hfun] at hfund
    have hmul :
        (∫ y : ℝ in y0..y1,
          I * (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 3) =
          I * ∫ y : ℝ in y0..y1,
            (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 3 :=
      intervalIntegral.integral_const_mul I
        (fun y : ℝ => (((x : ℂ) + (y : ℂ) * I)⁻¹) ^ 3)
    rw [hmul] at hfund
    exact hfund
  have hb := hhorizontal y0 hy0
  have ht := hhorizontal y1 hy1
  have hr := hvertical x1 hx1
  have hl := hvertical x0 hx0
  unfold boundaryRectIntegral
  simp only [smul_eq_mul]
  rw [hb, ht, hr, hl]
  dsimp [Fx, Fy]
  ring

theorem boundaryRectIntegral_const_mul_inv_sq_eq_zero
    (A : ℂ) {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => A * z⁻¹ ^ 2) x0 x1 y0 y1 = 0 := by
  have h := boundaryRectIntegral_mul_const
    (fun z : ℂ => z⁻¹ ^ 2) A x0 x1 y0 y1
  rw [boundaryRectIntegral_inv_sq_eq_zero hx0 hx1 hy0 hy1, zero_mul] at h
  simpa [mul_comm] using h

theorem boundaryRectIntegral_const_mul_inv_cube_eq_zero
    (A : ℂ) {x0 x1 y0 y1 : ℝ}
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hy0 : y0 ≠ 0) (hy1 : y1 ≠ 0) :
    boundaryRectIntegral (fun z : ℂ => A * z⁻¹ ^ 3) x0 x1 y0 y1 = 0 := by
  have h := boundaryRectIntegral_mul_const
    (fun z : ℂ => z⁻¹ ^ 3) A x0 x1 y0 y1
  rw [boundaryRectIntegral_inv_cube_eq_zero hx0 hx1 hy0 hy1, zero_mul] at h
  simpa [mul_comm] using h

end MathlibAux
