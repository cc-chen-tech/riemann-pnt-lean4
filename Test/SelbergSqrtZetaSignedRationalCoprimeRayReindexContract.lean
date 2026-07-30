import HardyTheorem.SelbergSqrtZetaSignedRationalCoprimeRayReindex

open scoped BigOperators

namespace HardyTheorem

#check selbergSqrtZetaSignedCoprimeRayScales_coprime
#check selbergSqrtZetaSignedCoprimeRayScales_denominator_pos
#check selbergSqrtZetaSignedCoprimeRayScales_scale_facts
#check selbergSqrtZetaSignedCoprimeRayScales_leftPair
#check selbergSqrtZetaSignedCoprimeRayScales_rightPair
#check selbergSqrtZetaSignedRationalCoefficientOffDiagonal_eq_coprimeRayScaleSum
#check sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_product_add_coprimeRayScaleSum

example (N X : ℕ) :
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal N X =
      ∑ x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X,
        selbergSqrtZetaSignedRationalPairCoeff N X
            (selbergSqrtZetaSignedCoprimeRayScales_leftPair x) *
          selbergSqrtZetaSignedRationalPairCoeff N X
            (selbergSqrtZetaSignedCoprimeRayScales_rightPair x) :=
  selbergSqrtZetaSignedRationalCoefficientOffDiagonal_eq_coprimeRayScaleSum N X

example (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k)) *
        (∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
          Complex.normSq (selbergSqrtZetaSignedNumeratorCoeff X l)) +
        ∑ x ∈
            selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X,
          selbergSqrtZetaSignedRationalPairCoeff N X
              (selbergSqrtZetaSignedCoprimeRayScales_leftPair x) *
            selbergSqrtZetaSignedRationalPairCoeff N X
              (selbergSqrtZetaSignedCoprimeRayScales_rightPair x) :=
  sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_product_add_coprimeRayScaleSum
    N X

end HardyTheorem
