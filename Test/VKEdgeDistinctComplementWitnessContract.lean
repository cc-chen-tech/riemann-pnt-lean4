import PrimeNumberTheorem.VKEdgeDistinctComplementWitness

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check
  (normalizedFiniteZeroClusterComplementContribution_eq_zero_of_subset :
    ∀ (S : Finset ℂ) (T beta y : ℝ),
      nontrivialZerosFinset T ⊆ S →
      normalizedFiniteZeroClusterComplementContribution S T beta y = 0)

#check
  (dynamicComplementFullMovingGaussianSecondMoment_eq_zero_of_subset :
    ∀ (S : Finset ℂ) (T beta a m L : ℝ),
      nontrivialZerosFinset T ⊆ S →
      dynamicComplementForwardMovingGaussianSecondMoment
        S T beta a (dynamicComplementFullBucketSet S T) m L = 0)

#check
  (exists_nontrivialZero_not_mem_of_fullMovingGaussianSecondMoment_pos :
    ∀ {S : Finset ℂ} {T beta a m L : ℝ},
      0 <
          dynamicComplementForwardMovingGaussianSecondMoment
            S T beta a (dynamicComplementFullBucketSet S T) m L →
      ∃ rho ∈ nontrivialZerosFinset T, rho ∉ S)

#check
  (exists_nontrivialZero_not_mem_of_remainder_energy_gt_three_errors :
    ∀ {S : Finset ℂ} {T beta a m L eta : ℝ},
      0 < m →
      0 ≤ beta →
      1 ≤ a →
      0 ≤ eta →
      (∀ y ∈ Set.Icc a (a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ≤ eta) →
      3 *
          (eta ^ 2 +
            (Real.exp (-beta * a) *
              zeroPackageClosedTermsUniformBound) ^ 2) <
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L →
      ∃ rho ∈ nontrivialZerosFinset T, rho ∉ S)

end VKEdgePiOverTwo
end PrimeNumberTheorem
