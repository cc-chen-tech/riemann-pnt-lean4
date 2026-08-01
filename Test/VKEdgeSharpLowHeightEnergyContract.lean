import PrimeNumberTheorem.VKEdgeSharpLowHeightEnergy

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check
  (eventually_exp_gammaLow_mul_add_one_le_exp_alpha_mul :
    ∀ {gammaLow alpha : ℝ},
      0 < gammaLow →
      gammaLow < alpha →
      ∀ᶠ a : ℝ in atTop,
        Real.exp (gammaLow * a) + 1 ≤ Real.exp (alpha * a))

#check
  (eventually_exists_goodHeight_normalizedRemainder_to_fullMovingGaussianEnergy_powerHeight_proportional :
    ∀ {S : Finset ℂ} {beta gammaLow ε eta : ℝ},
      1 / 2 < beta →
      beta < 1 →
      0 < gammaLow →
      gammaLow < beta →
      (1 - beta) * (1 + ε) < gammaLow →
      0 < ε →
      0 < eta →
      ∀ᶠ a : ℝ in atTop,
        ∃ Tlow ∈
            Set.Icc
              (Real.exp (gammaLow * a))
              (Real.exp (gammaLow * a) + 1),
          ExplicitFormulaAux.goodHeight Tlow ∧
            (1 / 3 : ℝ) *
                  normalizedFiniteZeroClusterPsiRemainderWithoutJumpForwardGaussianSecondMoment
                    S Tlow beta a ((ε * a) ^ 2) (ε * a) -
                (eta ^ 2 +
                  (Real.exp (-beta * a) *
                    zeroPackageClosedTermsUniformBound) ^ 2) ≤
              dynamicComplementForwardMovingGaussianSecondMoment
                S Tlow beta a (dynamicComplementFullBucketSet S Tlow)
                  ((ε * a) ^ 2) (ε * a))

#check
  (exists_eventually_emptyClusterLowHeightFullMovingGaussianSecondMoment_gt :
    ∀ {ε : ℝ} {rho : ℂ} {sigma gammaLow alpha : ℝ},
      0 < ε →
      0 < rho.im →
      riemannZeta rho = 0 →
      1 / 2 < sigma →
      sigma < rho.re →
      2 / 3 < rho.re →
      rho.re < 1 →
      0 < gammaLow →
      gammaLow < rho.re →
      (1 - rho.re) * (1 + ε) < gammaLow →
      gammaLow < alpha →
      alpha ≤ 1 →
      ∃ k : ℕ,
        riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
        0 < initialEmptyClusterFullMovingGaussianL2Constant ε rho k ∧
        ∀ᶠ Y : ℝ in atTop,
          ∃ Tlow ∈
              Set.Icc
                (Real.exp (gammaLow * Real.log Y))
                (Real.exp (gammaLow * Real.log Y) + 1),
            ExplicitFormulaAux.goodHeight Tlow ∧
              Tlow ≤ Real.exp (alpha * Real.log Y) ∧
              initialEmptyClusterFullMovingGaussianL2Constant ε rho k <
                dynamicComplementForwardMovingGaussianSecondMoment
                  ∅ Tlow rho.re (Real.log Y)
                    (dynamicComplementFullBucketSet ∅ Tlow)
                    ((ε * Real.log Y) ^ 2) (ε * Real.log Y))

end VKEdgePiOverTwo
end PrimeNumberTheorem
