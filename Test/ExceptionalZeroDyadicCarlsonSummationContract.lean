import PrimeNumberTheorem.ExceptionalZeroDyadicCarlsonSummation

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check (carlsonDyadicExponent : ℝ → ℝ)
#check (carlsonDyadicEnergyRatio : ℝ → ℝ)
#check (carlsonDyadicEnergyMajorant : ℝ → ℕ → ℝ)

example (sigma : ℝ) :
    carlsonDyadicExponent sigma = 4 * sigma * (1 - sigma) := by
  rfl

example (sigma : ℝ) :
    carlsonDyadicEnergyRatio sigma =
      (2 : ℝ) ^ (4 * sigma * (1 - sigma) - 2) := by
  rfl

example (sigma : ℝ) (k : ℕ) :
    carlsonDyadicEnergyMajorant sigma k =
      ((k + 1 : ℕ) : ℝ) ^ 6 *
        ((2 : ℝ) ^ (4 * sigma * (1 - sigma) - 2)) ^ k := by
  rfl

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

#check (dyadicUnitBucketRange : ℕ → ℕ → Finset ℕ)

example (K L : ℕ) :
    dyadicUnitBucketRange K L = Finset.Icc (2 ^ K) (2 ^ L - 1) := by
  rfl

#check
  (dyadicUnitBucketRange_eq_biUnion :
    ∀ {K L : ℕ}, K ≤ L →
      dyadicUnitBucketRange K L =
        (Finset.Ico K L).biUnion dyadicUnitBucketIndexSet)

#check
  (dynamicComplementDyadicRangeWeightedSquareCapacity :
    Finset ℂ → ℝ → ℝ → ℝ → ℕ → ℕ → ℝ)

example (S : Finset ℂ) (T beta a : ℝ) (K L : ℕ) :
    dynamicComplementDyadicRangeWeightedSquareCapacity S T beta a K L =
      ∑ k ∈ Finset.Ico K L,
        (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
          dynamicComplementDyadicTargetSquareCapacity S T beta a k := by
  rfl

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

#check
  (eventually_rightHigherDyadicRange_fartherRight_or_energy_lt :
    ∀ {sigma beta eta : ℝ},
      1 / 2 < sigma → sigma < 1 → sigma < beta → 0 < eta →
      ∃ Keta : ℕ, 2 ≤ Keta ∧
        ∀ (S : Finset ℂ) {Told T a : ℝ} {K L : ℕ} {m : ℝ},
          4 ≤ Told → 0 ≤ a → 1 ≤ m →
          Keta ≤ K → K < L → (2 : ℝ)^L ≤ T →
          (∃ n ∈ dyadicUnitBucketRange K L, ∃ rho,
            rho ∈ dynamicComplementZeroPacket
                (rightHigherExclusionSet S Told sigma T) T n ∧
              beta < rho.re ∧
              rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
              Told < rho.im ∧ rho ∉ S) ∨
            dynamicComplementCenteredFrozenGaussianSecondMoment
                (rightHigherExclusionSet S Told sigma T) T beta a
                (dyadicUnitBucketRange K L) m < eta)

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
