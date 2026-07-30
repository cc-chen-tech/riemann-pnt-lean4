import HardyTheorem.SelbergSqrtZetaSignedRationalCoprimeRayCoeff

open scoped BigOperators

namespace HardyTheorem

#check selbergSqrtZetaSignedDenominatorCollectedRealCoeff
#check selbergSqrtZetaSignedNumeratorRealCoeff
#check selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq
#check selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq_explicit
#check selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_product_eq_explicit
#check selbergSqrtZetaSignedNumeratorRealCoeff_nonneg_iff
#check selbergSqrtZetaSignedNumeratorRealCoeff_nonpos_iff
#check selbergSqrtZetaSignedDenominator_bounds_of_mem
#check selbergSqrtZetaSignedCoprimeRayScales_pair_support_facts
#check selbergSqrtZetaSignedCoprimeRayScales_mem_fixedScaleSupport
#check selbergSqrtZetaSignedCoprimeRayCorrelation_eq_sq_sub_diagonal

example (N X a b d : ℕ) :
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) =
      selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X (b * d) *
        selbergSqrtZetaSignedNumeratorRealCoeff X (a * d) :=
  selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq N X a b d

example (N X a b d : ℕ) :
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) =
      (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X (b * d),
          selbergSqrtZetaTaperedCoeff X p.2 *
            (Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹) *
        (selbergSqrtZetaTaperedCoeff X (a * d) *
          (Real.sqrt (a * d))⁻¹) :=
  selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq_explicit N X a b d

example (N X a b d e : ℕ) :
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) *
        selbergSqrtZetaSignedRationalPairCoeff N X (b * e, a * e) =
      (selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X (b * d) *
        selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X (b * e)) *
      ((selbergSqrtZetaTaperedCoeff X (a * d) *
        selbergSqrtZetaTaperedCoeff X (a * e)) *
      ((Real.sqrt (a * d))⁻¹ * (Real.sqrt (a * e))⁻¹)) :=
  selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_product_eq_explicit
    N X a b d e

example {N X : ℕ} {x : SelbergSqrtZetaSignedCoprimeRayScales}
    (hx :
      x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X) :
    (x.denominator * x.leftScale) ∈
        selbergSqrtZetaSignedDenominatorSupport N X ∧
      (x.numerator * x.leftScale) ∈
        selbergSqrtZetaSignedNumeratorSupport X ∧
      (x.denominator * x.rightScale) ∈
        selbergSqrtZetaSignedDenominatorSupport N X ∧
      (x.numerator * x.rightScale) ∈
        selbergSqrtZetaSignedNumeratorSupport X :=
  selbergSqrtZetaSignedCoprimeRayScales_pair_support_facts hx

example {N X : ℕ} {x : SelbergSqrtZetaSignedCoprimeRayScales}
    (hx :
      x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X) :
    x.leftScale ∈
        selbergSqrtZetaSignedCoprimeRayScaleSupport
          N X x.numerator x.denominator ∧
      x.rightScale ∈
        selbergSqrtZetaSignedCoprimeRayScaleSupport
          N X x.numerator x.denominator :=
  selbergSqrtZetaSignedCoprimeRayScales_mem_fixedScaleSupport hx

example (N X a b : ℕ) :
    (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
        ∑ e ∈
          (selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b).erase d,
          selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) *
            selbergSqrtZetaSignedRationalPairCoeff N X (b * e, a * e)) =
      (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
          selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d)) ^ 2 -
        ∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
          (selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d)) ^ 2 :=
  selbergSqrtZetaSignedCoprimeRayCorrelation_eq_sq_sub_diagonal N X a b

end HardyTheorem
