import PrimeNumberTheorem.VKEdgePiOverTwoAbelBoundary

open Complex Filter Set Topology

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check regularizedNegLogDerivModel_eq_neg_logDeriv_sub_pole_of_power_error
#check tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_zero
#check tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_ne_zero
#check exists_missing_oddHarmonic_with_abel_coefficients_of_carlson

example {rho : ℂ} {n : ℕ}
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1)
    (hrhoIm : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (horder : analyticOrderAt riemannZeta rho = n)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound rho.re) :
    Tendsto
      (fun a : ℝ =>
        (a : ℂ) *
          PrimeNumberTheorem.regularizedNegLogDerivModel
            (rho + (a : ℂ)))
      (𝓝[>] 0) (nhds (-(n : ℂ))) :=
  tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_zero
    hrhoRe0 hrhoRe1 hrhoIm hzero horder herror

example {beta gamma : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gamma)
    (hne : riemannZeta ((beta : ℂ) + I * gamma) ≠ 0)
    (herror : PrimeNumberTheorem.PsiPowerErrorBound beta) :
    Tendsto
      (fun a : ℝ =>
        (a : ℂ) *
          PrimeNumberTheorem.regularizedNegLogDerivModel
            ((beta : ℂ) + I * gamma + (a : ℂ)))
      (𝓝[>] 0) (nhds 0) :=
  tendsto_atRight_mul_regularizedNegLogDerivModel_of_zeta_ne_zero
    hbeta0 hbeta1 hgamma hne herror

end PrimeNumberTheorem.VKEdgePiOverTwo
