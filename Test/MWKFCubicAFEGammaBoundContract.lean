import MathlibAux.GammaVerticalStripBound

#check MathlibAux.norm_Gamma_le_Gamma_re
#check MathlibAux.exists_norm_Gamma_le_on_positive_reIcc
#check MathlibAux.exists_norm_Gammaℝ_le_on_positive_reIcc

example (t : ℝ) : ‖Complex.Gamma ((1 : ℂ) + Complex.I * t)‖ ≤ 1 := by
  simpa using MathlibAux.norm_Gamma_le_Gamma_re
    (by simp : 0 < ((1 : ℂ) + Complex.I * t).re)
