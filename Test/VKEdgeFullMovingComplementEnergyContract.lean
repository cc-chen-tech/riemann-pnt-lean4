import PrimeNumberTheorem.VKEdgeFullMovingComplementEnergy

open Complex Filter MeasureTheory Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check (dynamicComplementFullBucketSet :
  Finset ℂ → ℝ → Finset ℕ)

#check (dynamicComplementZeroPacket_eq_floorFiber :
  ∀ (S : Finset ℂ) (T : ℝ) (n : ℕ),
    dynamicComplementZeroPacket S T n =
      (nontrivialZerosFinset T \ S).filter
        (fun rho => Nat.floor |rho.im| = n))

#check (dynamicComplementMovingPacketContribution_fullBucketSet :
  ∀ (S : Finset ℂ) (T beta a y : ℝ),
    dynamicComplementMovingPacketContribution S T beta a
        (dynamicComplementFullBucketSet S T) y =
      normalizedFiniteZeroClusterComplementContribution S T beta y)

#check (normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment :
  Finset ℂ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

#check (dynamicComplementForwardMovingGaussianSecondMoment_fullBucketSet :
  ∀ (S : Finset ℂ) (T beta a m L : ℝ),
    dynamicComplementForwardMovingGaussianSecondMoment
        S T beta a (dynamicComplementFullBucketSet S T) m L =
      normalizedFiniteZeroClusterComplementForwardGaussianSecondMoment
        S T beta a m L)

#check
  (normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment :
    Finset ℂ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ)

#check
  (normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment_le_fullMoving_add_uniformErrors :
    ∀ {S : Finset ℂ} {T beta a m L eta : ℝ},
      0 < m →
      0 ≤ beta →
      1 ≤ a →
      0 ≤ eta →
      (∀ y ∈ Set.Icc a (a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ≤ eta) →
      normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L ≤
        3 *
            dynamicComplementForwardMovingGaussianSecondMoment
              S T beta a (dynamicComplementFullBucketSet S T) m L +
          3 *
            (eta ^ 2 +
              (Real.exp (-beta * a) *
                zeroPackageClosedTermsUniformBound) ^ 2))

#check
  (dynamicComplementFullMovingGaussianSecondMoment_ge_of_normalizedRemainder :
    ∀ {S : Finset ℂ} {T beta a m L eta R : ℝ},
      0 < m →
      0 ≤ beta →
      1 ≤ a →
      0 ≤ eta →
      (∀ y ∈ Set.Icc a (a + L),
        ‖normalizedFiniteZeroClusterApproximationError T beta y‖ ≤ eta) →
      R ≤
        normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
          S T beta a m L →
      (1 / 3 : ℝ) * R -
          (eta ^ 2 +
            (Real.exp (-beta * a) *
              zeroPackageClosedTermsUniformBound) ^ 2) ≤
        dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a (dynamicComplementFullBucketSet S T) m L)

#check
  (eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy :
    ∀ {S : Finset ℂ} {beta L m eta : ℝ},
      1 / 2 < beta →
      beta < 1 →
      0 ≤ L →
      0 < m →
      0 < eta →
      ∀ᶠ a in atTop,
        ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            (1 / 3 : ℝ) *
                  normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                    S T beta a m L -
                (eta ^ 2 +
                  (Real.exp (-beta * a) *
                    zeroPackageClosedTermsUniformBound) ^ 2) ≤
              dynamicComplementForwardMovingGaussianSecondMoment
                S T beta a (dynamicComplementFullBucketSet S T) m L)

end VKEdgePiOverTwo
end PrimeNumberTheorem
