import HardyTheorem.SelbergSqrtZetaSignedCoprimeRayLogExpansion

open scoped BigOperators ArithmeticFunction

namespace Test.SelbergSqrtZetaSignedCoprimeRayLogExpansionContract

open HardyTheorem

#check selbergSqrtZetaSignedDenominatorArithmeticCoeff
#check selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
#check selbergSqrtZetaSignedDenominatorCollectedRealCoeff_eq_invSqrt_mul_arithmeticCoeff
#check selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq_invSqrt_mul_invScale
#check selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_bilinearScaleSum
#check selbergSqrtZetaTaperedCoeff_eq_coeff_sub_invLog_mul_logCoeff
#check selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_taper_eq_logExpansion
#check selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_logExpansion

example (N X a b : ℕ) :
    (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
        selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d)) =
      (Real.sqrt (a * b))⁻¹ *
        (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            selbergSqrtZetaCoeff selbergSqrtZetaCoeff -
          (Real.log X)⁻¹ *
            (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                selbergSqrtZetaLogCoeff selbergSqrtZetaCoeff +
              selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                selbergSqrtZetaCoeff selbergSqrtZetaLogCoeff) +
          (Real.log X)⁻¹ ^ 2 *
            selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
              selbergSqrtZetaLogCoeff selbergSqrtZetaLogCoeff) :=
  selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_logExpansion
    N X a b

end Test.SelbergSqrtZetaSignedCoprimeRayLogExpansionContract
