import PrimeNumberTheorem.VKEdgeSharpMovingLeftStrip

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check
  (leftStripNontrivialZerosFinset : ℝ → ℝ → Finset ℂ)

#check
  (exists_eventually_leftStripLowHeightNormalizedComplementSecondMoment_gt :
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
              initialEmptyClusterFullMovingGaussianL2Constant ε rho k / 4 <
                ∫ t : ℝ in Set.Icc 0 (ε * Real.log Y),
                  normalizedGaussian ((ε * Real.log Y) ^ 2) t *
                    ‖normalizedFiniteZeroClusterComplementContribution
                      (leftStripNontrivialZerosFinset sigma Tlow)
                      Tlow rho.re (Real.log Y + t)‖ ^ 2)

end VKEdgePiOverTwo
end PrimeNumberTheorem
