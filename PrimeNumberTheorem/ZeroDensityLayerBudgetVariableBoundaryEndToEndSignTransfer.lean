import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryLowStripDecay

/-!
# End-to-end variable-boundary PNT sign transfer

All analytic zero-tail pieces are discharged by the moving Pintz--Carlson
chain.  An external anti-cancellation witness for the actual moving package is
the sole oscillatory input, and the conclusion concerns the unnormalized
Chebyshev error at the exact variable exponent scale.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Automatic moving analytic residual plus one moving-package witness gives
a persistent positive-or-negative unnormalized PNT witness. -/
theorem
    actualVariableBoundaryAutomaticZeroTails_unnormalizedSignAlternativeTransfer
    {sigma beta0 alpha epsilon c loss : ℝ} {H beta : ℝ → ℝ}
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + alpha + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta0 H)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    0 < c - loss ∧
      ((HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ beta x)) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ beta x)) := by
  apply variableBoundaryMainWitness_unnormalizedSignAlternativeTransfer
    hloss hlossC
  · exact
      actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_automaticZeroTails
        hbeta0 hbetaLower hHle hHtop halpha hepsilon hmargin
          hrightReal hhalf hone hright hgap remainder
  · exact hmain

end PrimeNumberTheorem
