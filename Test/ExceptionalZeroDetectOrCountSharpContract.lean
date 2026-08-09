import PrimeNumberTheorem.ExceptionalZeroDetectOrCountSharp

open Complex

namespace PrimeNumberTheorem
namespace ExceptionalZeroDetectOrCount

#check
  (exists_strictly_larger_recordedZeroSet_of_fullMovingGaussianSecondMoment_pos :
    ∀ {S : Finset ℂ} {T beta a m L : ℝ},
      S ⊆ nontrivialZerosFinset T →
      0 <
          VKEdgePiOverTwo.dynamicComplementForwardMovingGaussianSecondMoment
            S T beta a (VKEdgePiOverTwo.dynamicComplementFullBucketSet S T) m L →
      ∃ S' : Finset ℂ,
        S ⊆ S' ∧
          S.card < S'.card ∧
          S' ⊆ nontrivialZerosFinset T)

#check
  (exists_strictly_larger_recordedZeroSet_of_remainder_energy_gt_three_errors :
    ∀ {S : Finset ℂ} {T beta a m L eta : ℝ},
      S ⊆ nontrivialZerosFinset T →
      0 < m →
      0 ≤ beta →
      1 ≤ a →
      0 ≤ eta →
      (∀ y ∈ Set.Icc a (a + L),
        ‖VKEdgePiOverTwo.normalizedFiniteZeroClusterApproximationError T beta y‖ ≤
          eta) →
      3 *
          (eta ^ 2 +
            (Real.exp (-beta * a) *
              VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound) ^ 2) <
        VKEdgePiOverTwo.normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L →
      ∃ S' : Finset ℂ,
        S ⊆ S' ∧
          S.card < S'.card ∧
          S' ⊆ nontrivialZerosFinset T)

end ExceptionalZeroDetectOrCount
end PrimeNumberTheorem
