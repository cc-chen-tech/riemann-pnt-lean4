import HardyTheorem.ConreyDigammaHeight

open Complex

namespace HardyTheorem

example {s : ℂ} (hs : 1 < s.re) :
    deriv conreyH s / conreyH s =
      1 / s + 1 / (s - 1) - Complex.log Real.pi / 2 +
        Complex.digamma (s / 2) / 2 :=
  logDeriv_conreyH_eq hs

example {sigma t : ℝ} (ht : 2 ≤ t) (hsigma : 1 < sigma)
    (hst : sigma ≤ t) :
    ‖Complex.digamma (((sigma : ℂ) + I * t) / 2) - Real.log t‖ ≤ 9 :=
  norm_digamma_halfLine_sub_log_le_nine ht hsigma hst

example {sigma t : ℝ} (ht : 2 ≤ t) (hsigma : 1 < sigma)
    (hst : sigma ≤ t) :
    ‖deriv conreyH ((sigma : ℂ) + I * t) /
          conreyH ((sigma : ℂ) + I * t) -
        ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ ≤ 8 :=
  norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le ht hsigma hst

#print axioms logDeriv_conreyH_eq
#print axioms norm_digamma_halfLine_sub_log_le_nine
#print axioms norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le

end HardyTheorem
