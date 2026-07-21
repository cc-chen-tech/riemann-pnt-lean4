import MathlibAux.RectangularFourierEnvelope

#check MathlibAux.norm_integral_cexp_linear_le_length
#check MathlibAux.norm_integral_cexp_linear_le_min
#check MathlibAux.normSq_integral_cexp_linear_le_min

example {delta omega : ℝ} (hdelta : 0 ≤ delta) (homega : omega ≠ 0) :
    ‖∫ v in (0 : ℝ)..delta, Complex.exp (Complex.I * (omega * v))‖ ≤
      min delta (2 / |omega|) :=
  MathlibAux.norm_integral_cexp_linear_le_min hdelta homega

example {delta omega : ℝ} (hdelta : 0 ≤ delta) (homega : omega ≠ 0) :
    Complex.normSq
        (∫ v in (0 : ℝ)..delta, Complex.exp (Complex.I * (omega * v))) ≤
      (min delta (2 / |omega|)) ^ 2 :=
  MathlibAux.normSq_integral_cexp_linear_le_min hdelta homega

#print axioms MathlibAux.norm_integral_cexp_linear_le_min
#print axioms MathlibAux.normSq_integral_cexp_linear_le_min
