import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticCoefficientCap
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryBidirectionalTransfer

/-!
# Fully automatic dynamic-boundary upper and bidirectional transfer

The Carlson strip margin already implies `sigma < beta`.  Consequently the
global Carlson-plus-real coefficient constant automatically caps every moving
equal-real-part package.

The upper theorem below has no package-side hypothesis.  The bidirectional
theorem adds only the genuinely oscillatory package witness.
-/

namespace PrimeNumberTheorem

open Filter

/--
Fully automatic relative PNT upper bound at the dynamic right-edge scale.

All low-layer, high-tail, real-ordinate, contour, and moving-package
coefficient bounds are discharged from the stated analytic inputs.
-/
theorem actualDynamicBoundaryFullyAutomaticPNTUpperTransfer
    {H : ℝ → ℝ} {beta sigma alpha epsilon eta : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto :
      Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  have hsigmaBeta : sigma < beta := by
    linarith
  exact
    actualDynamicBoundaryAutomaticPNTUpperTransfer
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate
      heta
      (actualCarlsonDynamicBoundaryCoefficientCap
        hsigma hsigmaOne hsigmaBeta H)

/--
Fully automatic upper/lower transfer on the same actual PNT error.

The upper coefficient is the explicit global Carlson-plus-real mass.  The only
remaining package-side input is a far witness with coefficient `c`; every
fixed `0 < loss < c` survives in the true PNT error as `c - loss`.
-/
theorem actualDynamicBoundaryFullyAutomaticPNTBidirectionalTransfer
    {H : ℝ → ℝ}
    {beta sigma alpha epsilon eta c loss : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto :
      Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness
        chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta) := by
  have hsigmaBeta : sigma < beta := by
    linarith
  exact
    actualDynamicBoundaryAutomaticPNTBidirectionalTransfer
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate
      heta
      (actualCarlsonDynamicBoundaryCoefficientCap
        hsigma hsigmaOne hsigmaBeta H)
      hloss hlossC hmain

end PrimeNumberTheorem
