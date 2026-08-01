import PrimeNumberTheorem.ExceptionalZeroTargetDyadicGramSchur

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check dyadicUnitBucketIndexSet
#check dynamicComplementDyadicOccupancy
#check finiteZeroClusterCoefficientAt_norm_sq_eq
#check dynamicComplementDyadicTargetSquareCapacity
#check dynamicComplementDyadicGaussianMajorantEnergy_le_targetSquareCapacity
#check dynamicComplementDyadicCenteredFrozenGaussianSecondMoment_le_targetSquareCapacity
#check rightHigherDyadicGaussianMajorantEnergy_le_targetSquareCapacity
#check rightHigherDyadicCenteredFrozenGaussianSecondMoment_le_targetSquareCapacity
#check rightHigherDyadic_fartherRight_or_all_re_le
#check rightHigherDyadicTargetSquareCapacity_le_unweighted_of_re_le
#check rightHigherDyadic_fartherRight_or_gram_le_unweighted

example : dyadicUnitBucketIndexSet 0 = {1} := by native_decide

#check
  (rightHigherDyadicCenteredFrozenGaussianSecondMoment_le_targetSquareCapacity :
    ∀ (S : Finset ℂ) (Told sigma T beta a : ℝ) (k : ℕ) {m : ℝ},
      1 ≤ m →
      dynamicComplementCenteredFrozenGaussianSecondMoment
          (rightHigherExclusionSet S Told sigma T) T beta a
          (dyadicUnitBucketIndexSet k) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          (1 + (dynamicComplementDyadicOccupancy
            (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
          dynamicComplementDyadicTargetSquareCapacity
            (rightHigherExclusionSet S Told sigma T) T beta a k)

#check
  (rightHigherDyadic_fartherRight_or_gram_le_unweighted :
    ∀ (S : Finset ℂ) {Told sigma T beta a : ℝ} (k : ℕ),
      0 ≤ Told → 0 ≤ a → ∀ {m : ℝ}, 1 ≤ m →
      (∃ n ∈ dyadicUnitBucketIndexSet k, ∃ rho,
        rho ∈ dynamicComplementZeroPacket
            (rightHigherExclusionSet S Told sigma T) T n ∧
          beta < rho.re ∧
          rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
          Told < rho.im ∧ rho ∉ S) ∨
        dynamicComplementCenteredFrozenGaussianSecondMoment
            (rightHigherExclusionSet S Told sigma T) T beta a
            (dyadicUnitBucketIndexSet k) m ≤
          MathlibAux.gaussianBucketSchurConstant *
            (1 + (dynamicComplementDyadicOccupancy
              (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
            dynamicComplementDyadicSquareReciprocalCapacity
              (rightHigherExclusionSet S Told sigma T) T k)

end VKEdgePiOverTwo
end PrimeNumberTheorem
