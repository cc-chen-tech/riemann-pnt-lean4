import PrimeNumberTheorem.VKEdgePiOverTwoAbelIntegral

open Complex Filter Set Topology

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check psiAbelCoefficient
#check psiAbelCoefficient_eq_regularizedNegLogDerivModel
#check tendsto_psiAbelCoefficient_of_zeta_zero
#check tendsto_psiAbelCoefficient_of_zeta_ne_zero

example {beta lambda a : ℝ}
    (hbeta0 : 0 ≤ beta) (ha : 0 < a) :
    psiAbelCoefficient beta lambda a =
      (a : ℂ) /
          ((beta + a : ℝ) + I * lambda) *
        PrimeNumberTheorem.regularizedNegLogDerivModel
          ((beta + a : ℝ) + I * lambda) :=
  psiAbelCoefficient_eq_regularizedNegLogDerivModel hbeta0 ha

end PrimeNumberTheorem.VKEdgePiOverTwo
