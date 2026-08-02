import PrimeNumberTheorem.ExceptionalZeroDyadicCarlsonSummation

open Complex

namespace PrimeNumberTheorem.VKEdgePiOverTwo

/-- A lower bound on the exact centered-frozen energy used by the dyadic
Carlson tail eliminates its small-energy branch and forces a surviving,
strictly higher zero to the right of `beta`.  The lower bound is the precise
external analytic input still required from the Sharp side. -/
theorem eventually_rightHigherDyadicRange_fartherRight_of_energy_lowerBound
    {sigma beta eta : ℝ}
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hsigmaBeta : sigma < beta) (heta : 0 < eta) :
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
            Told < rho.im ∧ rho ∉ S := by
  obtain ⟨Keta, hKeta, htail⟩ :=
    eventually_rightHigherDyadicRange_fartherRight_or_energy_lt
      hsigmaHalf hsigmaOne hsigmaBeta heta
  refine ⟨Keta, hKeta, ?_⟩
  intro S Told T a K L m hTold ha hm hKetaK hKL hLT hlower
  rcases htail S hTold ha hm hKetaK hKL hLT with hwitness | hsmall
  · exact hwitness
  · exact (not_lt_of_ge hlower hsmall).elim

end PrimeNumberTheorem.VKEdgePiOverTwo
