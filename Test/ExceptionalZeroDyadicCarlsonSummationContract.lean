import PrimeNumberTheorem.ExceptionalZeroDyadicCarlsonSummation

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check carlsonDyadicExponent
#check carlsonDyadicEnergyRatio
#check carlsonDyadicEnergyMajorant

#check
  (carlsonDyadicExponent_lt_one :
    ∀ {sigma : ℝ}, 1 / 2 < sigma → sigma < 1 →
      carlsonDyadicExponent sigma < 1)

#check
  (summable_carlsonDyadicEnergyMajorant :
    ∀ {sigma : ℝ}, 1 / 2 < sigma → sigma < 1 →
      Summable (carlsonDyadicEnergyMajorant sigma))

#check
  (exists_rightHigherDyadicCapacity_le_carlsonMajorant :
    ∀ {sigma : ℝ}, 1 / 2 < sigma → sigma < 1 →
      ∃ A : ℝ, 0 ≤ A ∧ ∃ K0 : ℕ, 2 ≤ K0 ∧
        ∀ (S : Finset ℂ) (Told T : ℝ) (k : ℕ),
          4 ≤ Told → K0 ≤ k → (2 : ℝ) ^ (k + 1) ≤ T →
          (1 + (dynamicComplementDyadicOccupancy
            (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
              dynamicComplementDyadicSquareReciprocalCapacity
                (rightHigherExclusionSet S Told sigma T) T k ≤
            A * carlsonDyadicEnergyMajorant sigma k)

#check dyadicUnitBucketRange
#check dyadicUnitBucketRange_eq_biUnion

#check
  (dynamicComplementDyadicRangeCenteredFrozenGaussianSecondMoment_le :
    ∀ (S : Finset ℂ) (T beta a : ℝ) {K L : ℕ} {m : ℝ},
      K ≤ L → 1 ≤ m →
      dynamicComplementCenteredFrozenGaussianSecondMoment S T beta a
          (dyadicUnitBucketRange K L) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ k ∈ Finset.Ico K L,
            (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
              dynamicComplementDyadicTargetSquareCapacity S T beta a k)

#check
  (rightHigherDyadicRange_fartherRight_or_centeredFrozen_le_unweighted :
    ∀ (S : Finset ℂ) {Told sigma T beta a : ℝ} {K L : ℕ},
      0 ≤ Told → 0 ≤ a → K ≤ L → ∀ {m : ℝ}, 1 ≤ m →
      (∃ n ∈ dyadicUnitBucketRange K L, ∃ rho,
        rho ∈ dynamicComplementZeroPacket
            (rightHigherExclusionSet S Told sigma T) T n ∧
          beta < rho.re ∧
          rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
          Told < rho.im ∧ rho ∉ S) ∨
        dynamicComplementCenteredFrozenGaussianSecondMoment
            (rightHigherExclusionSet S Told sigma T) T beta a
            (dyadicUnitBucketRange K L) m ≤
          MathlibAux.gaussianBucketSchurConstant *
            ∑ k ∈ Finset.Ico K L,
              (1 + (dynamicComplementDyadicOccupancy
                (rightHigherExclusionSet S Told sigma T) T k : ℝ)) *
                dynamicComplementDyadicSquareReciprocalCapacity
                  (rightHigherExclusionSet S Told sigma T) T k)

example (S : Finset ℂ) (T beta a : ℝ) {m : ℝ} (hm : 1 ≤ m) :
    dynamicComplementCenteredFrozenGaussianSecondMoment S T beta a
        (dyadicUnitBucketRange 2 4) m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ∑ k ∈ Finset.Ico 2 4,
          (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
            dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  exact dynamicComplementDyadicRangeCenteredFrozenGaussianSecondMoment_le
    S T beta a (by norm_num) hm

end PrimeNumberTheorem.VKEdgePiOverTwo
