import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryWitnessTransfer

/-!
# Automatic dynamic-boundary witness transfer

This is the single-entry facade for the dynamic-boundary upper/lower transfer
chain.  It combines:

* automatic decay of the canonical low Carlson layer;
* dominated-convergence decay of the actual high zero tail;
* decay or dynamic absorption of real-ordinate zeros;
* the selected-height explicit-formula remainder certificate; and
* an independently supplied far witness for the moving boundary package.

The final coefficient loss is an arbitrary fixed `loss > 0`.  The theorem does
not construct the package witness and therefore does not claim a new local
anti-cancellation result.
-/

namespace PrimeNumberTheorem

/--
Single-entry transfer from a dynamic equal-real-part package witness to a
genuine relative PNT-error witness.

The strict margin
`sigma - beta + alpha + epsilon < 0`
controls the canonical low layer.  The non-strict right-edge hypotheses are
sufficient for the high and real-ordinate boundary terms because zeros with
real part exactly `beta` are eventually absorbed by the moving package.
-/
theorem actualDynamicBoundaryAutomaticPNTWitnessTransfer
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
        relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * targetZeroPowerAmplitude beta x) := by
  have hresidual :=
    actualDynamicBoundaryExplicitFormulaResidual_targetAmplitudeNegligible
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate
  exact
    actualDynamicBoundaryMainWitness_realTransfer
      hloss hlossC hresidual hmain

end PrimeNumberTheorem
