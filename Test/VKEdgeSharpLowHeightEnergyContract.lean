import PrimeNumberTheorem.VKEdgeSharpLowHeightEnergy

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

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
