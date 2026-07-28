import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryUpperTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticUnnormalizedTransfer

/-!
# Bidirectional dynamic-boundary PNT transfer

This module places the upper and lower consequences of the same moving
equal-real-part zero package in one theorem.

The shared density and explicit-formula inputs discharge every term outside
the package.  A uniform package coefficient cap gives the upper bound, while a
far package witness gives the lower bound.  These are intentionally separate
package-side hypotheses.
-/

namespace PrimeNumberTheorem

open Filter

/--
Unified upper/lower transfer for the actual dynamic boundary package.

The conclusions are:

* an eventual relative PNT upper bound with coefficient `C + eta`;
* positivity of the surviving lower coefficient `c - loss`;
* a relative PNT far witness with coefficient `c - loss`; and
* the corresponding unnormalized `psi0(x) - x` witness at `x^beta` scale.
-/
theorem actualDynamicBoundaryAutomaticPNTBidirectionalTransfer
    {H : ℝ → ℝ}
    {beta sigma alpha epsilon C eta c loss : ℝ}
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
    (hcap : DynamicBoundaryPackageCoefficientCap beta H C)
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
        (C + eta) * targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness
        chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta) := by
  have hupper :=
    actualDynamicBoundaryAutomaticPNTUpperTransfer
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate
      heta hcap
  rcases
      actualDynamicBoundaryAutomaticPNTWitnessTransfer
        hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
        hmargin hpositiveRightEdge hrealRightEdge remainderCertificate
        hloss hlossC hmain with
    ⟨hcoefficient, hrelative⟩
  exact
    ⟨hupper, hcoefficient, hrelative,
      hrelative.relativeChebyshevPsi0Error_to_unnormalized⟩

end PrimeNumberTheorem
