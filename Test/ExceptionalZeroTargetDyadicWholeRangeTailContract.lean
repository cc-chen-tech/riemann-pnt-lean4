import PrimeNumberTheorem.ExceptionalZeroTargetDyadicWholeRangeTail

open Complex

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check (targetDyadicUnitBucketRange : ℕ → ℕ → Finset ℕ)

example (K L : ℕ) :
    targetDyadicUnitBucketRange K L = Finset.Icc (2 ^ K) (2 ^ L - 1) := by
  rfl

#check
  (targetDyadicUnitBucketRange_eq_biUnion :
    ∀ {K L : ℕ}, K ≤ L →
      targetDyadicUnitBucketRange K L =
        (Finset.Ico K L).biUnion dyadicUnitBucketIndexSet)

#check
  (dynamicComplementTargetDyadicRangeCenteredFrozenGaussianSecondMoment_le :
    ∀ (S : Finset ℂ) (T beta a : ℝ) {K L : ℕ} {m : ℝ},
      K ≤ L → 1 ≤ m →
      dynamicComplementCenteredFrozenGaussianSecondMoment S T beta a
          (targetDyadicUnitBucketRange K L) m ≤
        MathlibAux.gaussianBucketSchurConstant *
          ∑ k ∈ Finset.Ico K L,
            (1 + (dynamicComplementDyadicOccupancy S T k : ℝ)) *
              dynamicComplementDyadicTargetSquareCapacity S T beta a k)

#check
  (eventually_rightHigherTargetDyadicRange_fartherRight_or_energy_lt :
    ∀ {eta : ℝ}, 0 < eta →
      ∃ Keta : ℕ, 2 ≤ Keta ∧
        ∀ (S : Finset ℂ) {Told sigma T beta a : ℝ} {K L : ℕ} {m : ℝ},
          0 ≤ Told → 0 ≤ a → 1 ≤ m → Keta ≤ K → K < L →
          (∃ n ∈ targetDyadicUnitBucketRange K L, ∃ rho,
            rho ∈ dynamicComplementZeroPacket
                (rightHigherExclusionSet S Told sigma T) T n ∧
              beta < rho.re ∧
              rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
              Told < rho.im ∧ rho ∉ S) ∨
            dynamicComplementCenteredFrozenGaussianSecondMoment
                (rightHigherExclusionSet S Told sigma T) T beta a
                (targetDyadicUnitBucketRange K L) m < eta)

end PrimeNumberTheorem.VKEdgePiOverTwo
