import MathlibAux.HorizontalArgument

open Complex MeasureTheory
open scoped Interval

#check MathlibAux.intervalIntegral_im_inv_horizontal_sub_eq
#check MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi

example {a b t : ℝ} {u : ℂ} (ht : t ≠ u.im) :
    |∫ sigma in a..b,
      (((((sigma : ℂ) + I * t) - u)⁻¹).im)| ≤ Real.pi :=
  MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi ht
