import PrimeNumberTheorem.ExceptionalZeroSharpEnergyLowerWitnessAdapter

open Complex

namespace PrimeNumberTheorem.VKEdgePiOverTwo

#check
  (eventually_rightHigherDyadicRange_fartherRight_of_energy_lowerBound :
    ∀ {sigma beta eta : ℝ},
      1 / 2 < sigma → sigma < 1 → sigma < beta → 0 < eta →
      ∃ Keta : ℕ, 2 ≤ Keta ∧
        ∀ (S : Finset ℂ) {Told T a : ℝ} {K L : ℕ} {m : ℝ},
          4 ≤ Told → 0 ≤ a → 1 ≤ m →
          Keta ≤ K → K < L → (2 : ℝ) ^ L ≤ T →
          eta ≤ dynamicComplementCenteredFrozenGaussianSecondMoment
              (rightHigherExclusionSet S Told sigma T) T beta a
              (dyadicUnitBucketRange K L) m →
          ∃ n ∈ dyadicUnitBucketRange K L, ∃ rho,
            rho ∈ dynamicComplementZeroPacket
                (rightHigherExclusionSet S Told sigma T) T n ∧
              beta < rho.re ∧
              rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T ∧
              Told < rho.im ∧ rho ∉ S)

end PrimeNumberTheorem.VKEdgePiOverTwo
