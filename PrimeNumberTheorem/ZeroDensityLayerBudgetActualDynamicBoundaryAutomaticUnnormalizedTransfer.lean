import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticWitnessTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Automatic dynamic-boundary transfer at the unnormalized PNT scale

The dynamic-boundary facade naturally controls the relative Chebyshev error at
scale `x^(beta - 1)`.  This module multiplies back by the positive sample point
and states the final result directly for `psi0(x) - x` at scale `x^beta`.

All multiplicity and reciprocal-zero factors remain in the coefficient `c`.
-/

namespace PrimeNumberTheorem

/--
Automatic dynamic-boundary transfer to the genuine unnormalized Chebyshev
error.

If the independently supplied moving-package theorem has coefficient `c`, then
every fixed `0 < loss < c` gives arbitrarily far points satisfying

`(c - loss) * x^beta <= |psi0(x) - x|`.
-/
theorem actualDynamicBoundaryAutomaticPsi0ErrorWitnessTransfer
    {H : ℝ → ℝ} {beta sigma alpha epsilon c loss : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in Filter.atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto :
      Filter.Tendsto (fun m : ℕ => H (m : ℝ))
        Filter.atTop Filter.atTop)
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
    0 < c - loss ∧
      HasFarTargetAmplitudeWitness
        chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta) := by
  rcases
      actualDynamicBoundaryAutomaticPNTWitnessTransfer
        hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha
        hepsilon hmargin hpositiveRightEdge hrealRightEdge
        remainderCertificate hloss hlossC hmain with
    ⟨hcoefficient, hrelative⟩
  exact
    ⟨hcoefficient,
      hrelative.relativeChebyshevPsi0Error_to_unnormalized⟩

end PrimeNumberTheorem
