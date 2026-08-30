import MathlibAux.RectangleCauchyDerivative

open Complex Set
open scoped Interval

-- This contract detects a lost double-pole term, an incorrect orientation,
-- or an illicit requirement that the numerator vanish at zero.
example {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f ([[a, b]] ×ℂ [[c, d]]))
    (ha : a < 0) (hb : 0 < b) (hc : c < 0) (hd : 0 < d) :
    MathlibAux.boundaryRectIntegral (fun w => f w / w ^ 2) a b c d =
      (2 * Real.pi * I) * deriv f 0 := by
  exact MathlibAux.boundaryRectIntegral_div_sq hf ha hb hc hd

example : MathlibAux.boundaryRectIntegral
    (fun w : ℂ => (3 + 7 * w + 11 * w ^ 2) / w ^ 2) (-2) 3 (-4) 5 =
      (2 * Real.pi * I) * 7 := by
  have hf : Differentiable ℂ (fun w : ℂ => 3 + 7 * w + 11 * w ^ 2) := by
    fun_prop
  rw [MathlibAux.boundaryRectIntegral_div_sq hf.differentiableOn
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  have hderiv : HasDerivAt (fun w : ℂ => 3 + 7 * w + 11 * w ^ 2) 7 0 := by
    simpa using ((hasDerivAt_const (0 : ℂ) (3 : ℂ)).fun_add
      ((hasDerivAt_id (0 : ℂ)).const_mul 7)).fun_add
      (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul 11)
  rw [hderiv.deriv]

#print axioms MathlibAux.boundaryRectIntegral_div_sq
