import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicTwoHeightDyadicCuts

namespace PrimeNumberTheorem

open Filter Topology

example (gamma : ℝ) (m : ℕ) :
    actualCubicDyadicPolynomialCut gamma m =
      Nat.floor
        (Real.log (carlsonPolynomialHeight gamma (m : ℝ)) / Real.log 2) := rfl

example (gammaLow : ℝ) (m : ℕ) :
    actualCubicLowDyadicCut gammaLow m =
      actualCubicDyadicPolynomialCut gammaLow m := rfl

example (alpha : ℝ) (m : ℕ) :
    actualCubicOuterDyadicCut alpha m =
      actualCubicDyadicPolynomialCut alpha m := rfl

example {gamma : ℝ} (hgamma : 0 < gamma) :
    Tendsto (actualCubicDyadicPolynomialCut gamma) atTop atTop :=
  tendsto_actualCubicDyadicPolynomialCut_atTop hgamma

example {gammaLow : ℝ} (hgammaLow : 0 < gammaLow) :
    Tendsto (actualCubicLowDyadicCut gammaLow) atTop atTop :=
  tendsto_actualCubicLowDyadicCut_atTop hgammaLow

example {alpha : ℝ} (halpha : 0 < alpha) :
    Tendsto (actualCubicOuterDyadicCut alpha) atTop atTop :=
  tendsto_actualCubicOuterDyadicCut_atTop halpha

example {gammaLow alpha : ℝ} (hgammaLowAlpha : gammaLow ≤ alpha) :
    ∀ᶠ m : ℕ in atTop,
      actualCubicLowDyadicCut gammaLow m ≤
        actualCubicOuterDyadicCut alpha m :=
  eventually_actualCubicLowDyadicCut_le_outer hgammaLowAlpha

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau gammaLow : ℝ} (hx : 1 ≤ x) (hgammaLow : 0 < gammaLow)
    (S : Finset ℂ) :
    Tendsto
      (fun m : ℕ =>
        actualCubicDyadicStripSquareCapacityExcludingTail
          x sigma tau S (actualCubicLowDyadicCut gammaLow m))
      atTop (nhds 0) :=
  certificate.tendsto_actualCubicTail_at_lowDyadicCut_zero
    hx hgammaLow S

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau alpha : ℝ} (hx : 1 ≤ x) (halpha : 0 < alpha)
    (S : Finset ℂ) :
    Tendsto
      (fun m : ℕ =>
        actualCubicDyadicStripSquareCapacityExcludingTail
          x sigma tau S (actualCubicOuterDyadicCut alpha m))
      atTop (nhds 0) :=
  certificate.tendsto_actualCubicTail_at_outerDyadicCut_zero
    hx halpha S

end PrimeNumberTheorem
