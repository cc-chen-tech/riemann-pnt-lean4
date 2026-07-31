import PrimeNumberTheorem.VKEdgeZeroClusterClosedTermsL2

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check zeroPackageClosedTermsUniformBound
#check normalizedZeroPackageClosedTerms
#check normalizedZeroPackageClosedTermsSecondMoment
#check normalizedFiniteZeroClusterComplementContribution
#check normalizedFiniteZeroClusterApproximationError
#check zero_lt_zeroPackageClosedTermsUniformBound
#check norm_zeroPackageClosedTerms_le_uniformBound
#check norm_normalizedZeroPackageClosedTerms_le_uniformBound
#check normalizedZeroPackageClosedTermsSecondMoment_le
#check normalizedFiniteZeroClusterPsiRemainderWithoutJump_eq_components

example :
    0 < zeroPackageClosedTermsUniformBound :=
  zero_lt_zeroPackageClosedTermsUniformBound

example {y : ℝ} (hy : 1 ≤ y) :
    ‖ZeroForcedOscillation.zeroPackageClosedTerms y‖ ≤
      zeroPackageClosedTermsUniformBound :=
  norm_zeroPackageClosedTerms_le_uniformBound hy

example {beta a y : ℝ}
    (hbeta : 0 ≤ beta) (ha : 1 ≤ a) (hay : a ≤ y) :
    ‖normalizedZeroPackageClosedTerms beta y‖ ≤
      Real.exp (-beta * a) * zeroPackageClosedTermsUniformBound :=
  norm_normalizedZeroPackageClosedTerms_le_uniformBound
    hbeta ha hay

example {beta a L : ℝ}
    (hbeta : 0 ≤ beta) (ha : 1 ≤ a) (hL : 0 ≤ L) :
    normalizedZeroPackageClosedTermsSecondMoment beta a L ≤
      L * (Real.exp (-beta * a) *
        zeroPackageClosedTermsUniformBound) ^ 2 :=
  normalizedZeroPackageClosedTermsSecondMoment_le hbeta ha hL

example (S : Finset ℂ) (T beta y : ℝ) :
    normalizedFiniteZeroClusterPsiRemainderWithoutJump S T beta y =
      normalizedFiniteZeroClusterComplementContribution S T beta y +
        normalizedFiniteZeroClusterApproximationError T beta y +
        normalizedZeroPackageClosedTerms beta y :=
  normalizedFiniteZeroClusterPsiRemainderWithoutJump_eq_components
    S T beta y

end VKEdgePiOverTwo
end PrimeNumberTheorem
