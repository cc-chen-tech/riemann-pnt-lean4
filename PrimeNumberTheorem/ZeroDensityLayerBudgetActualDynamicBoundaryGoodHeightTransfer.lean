import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryFullyAutomaticTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTDynamicReverseZeroFree

/-!
# Canonical good-height dynamic-boundary transfer

The dynamic-boundary upper transfer previously accepted a cofinal height
schedule and a natural-point explicit-formula remainder certificate.  The
uniform short-interval good-height theorem constructs both inputs at the
polynomial scale `x ^ alpha`.

This module fixes the repository's canonical selector.  Under

* `0 < alpha <= 1`;
* the contour margin `1 - beta < alpha`;

the resulting schedule is cofinal, lies eventually below `x ^ alpha`, and
has an actual explicit-formula remainder negligible relative to
`x ^ (beta - 1)`.  Combining this package with the automatic Carlson
coefficient cap removes every upper-side certificate from the dynamic
boundary transfer.

The lower conclusion still requires a far witness for the moving
equal-real-part package.  That anti-cancellation input belongs to the
independent sharp-oscillation development.
-/

namespace PrimeNumberTheorem

open Filter

/-- The fixed selected good-height schedule used by the automatic dynamic
boundary transfer. -/
noncomputable def actualDynamicBoundaryCanonicalSelectedGoodHeight
    (alpha x : ℝ) : ℝ :=
  selectedUniformGoodHeight alpha uniformNaturalPointGoodHeightSelection x

/-- The canonical selected good height automatically supplies every
height-side input of the dynamic-boundary transfer. -/
theorem actualDynamicBoundaryCanonicalSelectedGoodHeight_spec
    {beta alpha : ℝ}
    (hbeta : 0 < beta)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha) :
    (∀ᶠ m : ℕ in atTop,
        actualDynamicBoundaryCanonicalSelectedGoodHeight alpha (m : ℝ) ≤
          carlsonPolynomialHeight alpha (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          actualDynamicBoundaryCanonicalSelectedGoodHeight alpha (m : ℝ))
        atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha) := by
  have hheightReal :
      ∀ᶠ x : ℝ in atTop,
        actualDynamicBoundaryCanonicalSelectedGoodHeight alpha x ≤
          carlsonPolynomialHeight alpha x := by
    filter_upwards [
      eventually_selectedUniformGoodHeight_mem halpha
        uniformNaturalPointGoodHeightSelection] with x hx
    simpa [actualDynamicBoundaryCanonicalSelectedGoodHeight,
      carlsonPolynomialHeight] using hx.2
  refine
    ⟨tendsto_natCast_atTop_atTop.eventually hheightReal, ?_, ?_⟩
  · exact
      (selectedUniformGoodHeight_tendsto_atTop halpha
        uniformNaturalPointGoodHeightSelection).comp
          tendsto_natCast_atTop_atTop
  · have hheight_eq :
        actualDynamicBoundaryCanonicalSelectedGoodHeight alpha =
          selectedUniformGoodHeight alpha
            uniformNaturalPointGoodHeightSelection := by
      funext x
      rfl
    rw [hheight_eq]
    exact selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hcontourMargin
        uniformNaturalPointGoodHeightSelection

/-- Fully automatic upper transfer at the canonical selected good height.

The bound uses the explicit Carlson total-weight coefficient cap; no
height, contour-remainder, or package-coefficient certificate remains as an
input. -/
theorem actualDynamicBoundaryCanonicalGoodHeightPNTUpperTransfer
    {beta sigma alpha epsilon eta : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (hepsilon : 0 < epsilon)
    (hCarlsonMargin : sigma - beta + alpha + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (heta : 0 < eta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  rcases
      actualDynamicBoundaryCanonicalSelectedGoodHeight_spec
        hbeta halpha halphaOne hcontourMargin with
    ⟨hheightUpper, hheightTendsto, remainderCertificate⟩
  exact
    actualDynamicBoundaryFullyAutomaticPNTUpperTransfer
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
        hCarlsonMargin hpositiveRightEdge hrealRightEdge
          remainderCertificate heta

/-- Canonical-good-height bidirectional transfer on the same genuine PNT
error.

The upper conclusion is automatic.  A moving-package witness with
coefficient `c` transfers to relative and unnormalized PNT witnesses with
every prescribed loss `0 < loss < c`. -/
theorem actualDynamicBoundaryCanonicalGoodHeightPNTBidirectionalTransfer
    {beta sigma alpha epsilon eta c loss : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (hepsilon : 0 < epsilon)
    (hCarlsonMargin : sigma - beta + alpha + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
            (dynamicEqualRealPartZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              beta (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * targetZeroPowerAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            targetZeroPowerAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x => (c - loss) * targetZeroPowerAmplitude beta x) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x => (c - loss) * x ^ beta) := by
  rcases
      actualDynamicBoundaryCanonicalSelectedGoodHeight_spec
        hbeta halpha halphaOne hcontourMargin with
    ⟨hheightUpper, hheightTendsto, remainderCertificate⟩
  exact
    actualDynamicBoundaryFullyAutomaticPNTBidirectionalTransfer
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
        hCarlsonMargin hpositiveRightEdge hrealRightEdge
          remainderCertificate heta hloss hlossC hmain

end PrimeNumberTheorem
