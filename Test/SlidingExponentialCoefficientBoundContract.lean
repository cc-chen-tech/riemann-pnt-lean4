import MathlibAux.SlidingExponentialCoefficientBound

open Complex MeasureTheory

namespace MathlibAux

#check intervalIntegral_cexp_linear_eq
#check norm_intervalIntegral_cexp_linear_le_abs_length
#check norm_intervalIntegral_cexp_linear_le_two_div_abs
#check norm_intervalIntegral_cexp_linear_le_abs_length_min
#check norm_slidingExponentialCoefficient_le_abs_length
#check norm_slidingExponentialCoefficient_le_two_div_abs
#check norm_slidingExponentialCoefficient_le_min

#print axioms intervalIntegral_cexp_linear_eq
#print axioms norm_intervalIntegral_cexp_linear_le_abs_length_min
#print axioms norm_slidingExponentialCoefficient_le_min

example {iota : Type*} {H : ℝ} (coeff : iota → ℂ) (freq : iota → ℝ) (j : iota)
    (hfreq : freq j ≠ 0) :
    ‖slidingExponentialCoefficient H coeff freq j‖ ≤
      ‖coeff j‖ * min |H| (2 / |freq j|) := by
  exact norm_slidingExponentialCoefficient_le_min coeff freq j hfreq

end MathlibAux
