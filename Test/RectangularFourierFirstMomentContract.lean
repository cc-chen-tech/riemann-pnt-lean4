import MathlibAux.RectangularFourierFirstMoment

#check MathlibAux.intervalIntegral_mul_cexp_linear_eq_integration_by_parts
#check MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_oscillatory
#check MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_trivial
#check MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_min

open Complex

example {delta omega : ℝ} (hdelta : 0 ≤ delta) (homega : omega ≠ 0) :
    ‖∫ v in (0 : ℝ)..delta,
      (v : ℂ) * Complex.exp (I * (omega * v))‖ ≤
      min (delta ^ 2 / 2) (delta / |omega| + 2 / omega ^ 2) :=
  MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_min hdelta homega

#print axioms MathlibAux.intervalIntegral_mul_cexp_linear_eq_integration_by_parts
#print axioms MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_oscillatory
#print axioms MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_trivial
#print axioms MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_min
