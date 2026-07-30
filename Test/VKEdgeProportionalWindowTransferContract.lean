import PrimeNumberTheorem.VKEdgeProportionalWindowTransfer

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check
  (eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy_proportional :
    ∀ {S : Finset ℂ} {beta ε eta : ℝ},
      1 / 2 < beta →
      beta < 1 →
      0 < ε →
      (1 - beta) * ε < beta - 1 / 2 →
      0 < eta →
      ∀ᶠ a : ℝ in atTop,
        ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            (1 / 3 : ℝ) *
                  normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                    S T beta a ((ε * a) ^ 2) (ε * a) -
                (eta ^ 2 +
                  (Real.exp (-beta * a) *
                    zeroPackageClosedTermsUniformBound) ^ 2) ≤
              dynamicComplementForwardMovingGaussianSecondMoment
                S T beta a (dynamicComplementFullBucketSet S T)
                  ((ε * a) ^ 2) (ε * a))

#check (initialEmptyClusterFullMovingGaussianL2Constant :
  ℝ → ℂ → ℕ → ℝ)

#check
  (exists_eventually_emptyClusterFullMovingGaussianSecondMoment_gt :
    ∀ {ε : ℝ} {rho : ℂ} {sigma : ℝ},
      0 < ε →
      0 < rho.im →
      riemannZeta rho = 0 →
      1 / 2 < sigma →
      sigma < rho.re →
      rho.re < 1 →
      (1 - rho.re) * ε < rho.re - 1 / 2 →
      ∃ k : ℕ,
        riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
        0 < initialEmptyClusterFullMovingGaussianL2Constant ε rho k ∧
        ∀ᶠ Y : ℝ in atTop,
          ∃ T ∈
              Set.Icc
                (Real.exp (Real.log Y / 2))
                (Real.exp (Real.log Y / 2) + 1),
            ExplicitFormulaAux.goodHeight T ∧
              initialEmptyClusterFullMovingGaussianL2Constant ε rho k <
                dynamicComplementForwardMovingGaussianSecondMoment
                  ∅ T rho.re (Real.log Y)
                    (dynamicComplementFullBucketSet ∅ T)
                    ((ε * Real.log Y) ^ 2) (ε * Real.log Y))

end VKEdgePiOverTwo
end PrimeNumberTheorem
