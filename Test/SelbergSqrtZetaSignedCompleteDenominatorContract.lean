import HardyTheorem.SelbergSqrtZetaSignedCompleteDenominator

open scoped BigOperators ArithmeticFunction

namespace Test.SelbergSqrtZetaSignedCompleteDenominatorContract

open HardyTheorem

#check zeta_mul_selbergSqrtZetaLogCoeff
#check selbergSqrtZetaSignedDenominatorFiber_eq_divisorsAntidiagonal
#check sum_selbergSqrtZetaSignedDenominatorFiber_eq_zeta_mul
#check selbergSqrtZetaSignedDenominatorArithmeticCoeff_eq_zeta_mul
#check selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport
#check selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport
#check selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_eq_complete_zeta_add_boundary
#check selbergSqrtZetaSignedCoprimeRayComplete_singleLog_eq_logRatio
#check selbergSqrtZetaSignedCoprimeRayComplete_singleLog_diagonal_eq_zero

example (N X a : ℕ) (ha : 0 < a) :
    (∑ d ∈
        selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a a,
      (d : ℝ)⁻¹ *
        (selbergSqrtZetaLogCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) (a * d)) +
        selbergSqrtZetaCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaLogCoeff) (a * d)))) = 0 :=
  selbergSqrtZetaSignedCoprimeRayComplete_singleLog_diagonal_eq_zero
    N X a ha

end Test.SelbergSqrtZetaSignedCompleteDenominatorContract
