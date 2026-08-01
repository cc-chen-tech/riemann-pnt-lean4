import PrimeNumberTheorem.ZeroDensityLayerBudgetCanonicalPolynomialUnifiedUpperSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmega

/-!
# Canonical polynomial running-boundary unified transfer

The canonical polynomial selected height is combined with the natural running
maximum of visible zero real parts. This discharges all moving-boundary
geometry required by the unified power-scale transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Canonical selected height attached to the exact critical-half target
window. -/
noncomputable def canonicalPolynomialRunningBoundaryHeight
    (beta0 sigma : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  selectedUniformGoodHeight
    (canonicalPolynomialHeightInnerExponent beta0 sigma) selection

/-- Natural running maximum boundary at the canonical polynomial height. -/
noncomputable def canonicalPolynomialRunningVisibleZeroBoundary
    (beta0 sigma : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  naturalRunningVisibleZeroBoundaryReal
    (canonicalPolynomialRunningBoundaryHeight beta0 sigma selection) beta0

/-- Fully canonical power-scale upper/signed transfer. Height selection,
Carlson residuals, coefficient caps, boundary monotonicity, and indexed
right-edge geometry are automatic. -/
theorem actualCanonicalPolynomialRunningBoundaryUnifiedUpperSignedOmega
    {sigma beta0 eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hhalf : 1 / 2 < sigma)
    (htarget : (1 + sigma) / 2 < beta0)
    (hbeta0One : beta0 < 1)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (canonicalPolynomialRunningBoundaryHeight beta0 sigma selection)
            (variableBoundaryZeroPackage
              (canonicalPolynomialRunningBoundaryHeight beta0 sigma selection)
              (canonicalPolynomialRunningVisibleZeroBoundary
                beta0 sigma selection) (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (canonicalPolynomialRunningVisibleZeroBoundary
              beta0 sigma selection) (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (canonicalPolynomialRunningBoundaryHeight beta0 sigma selection)
            (variableBoundaryZeroPackage
              (canonicalPolynomialRunningBoundaryHeight beta0 sigma selection)
              (canonicalPolynomialRunningVisibleZeroBoundary
                beta0 sigma selection) (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (canonicalPolynomialRunningVisibleZeroBoundary
              beta0 sigma selection) (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          variableBoundaryTargetAmplitude
            (canonicalPolynomialRunningVisibleZeroBoundary
              beta0 sigma selection) (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * x ^
            canonicalPolynomialRunningVisibleZeroBoundary
              beta0 sigma selection x) := by
  let H := canonicalPolynomialRunningBoundaryHeight beta0 sigma selection
  let beta := canonicalPolynomialRunningVisibleZeroBoundary beta0 sigma selection
  have hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ) := by
    filter_upwards with m
    exact beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast H beta0 m
  have hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)) := by
    exact naturalRunningVisibleZeroBoundaryReal_sampled_monotone H beta0
  have hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta := by
    exact naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge H beta0
  exact
    actualCanonicalPolynomialVariableBoundaryUnifiedUpperSignedOmega
      selection heta hloss hlossC hhalf htarget hbeta0One
      hbetaLower hbetaMono hrightReal hright
      (by simpa [H, beta, canonicalPolynomialRunningVisibleZeroBoundary,
          canonicalPolynomialRunningBoundaryHeight] using hmainPos)
      (by simpa [H, beta, canonicalPolynomialRunningVisibleZeroBoundary,
          canonicalPolynomialRunningBoundaryHeight] using hmainNeg)

end PrimeNumberTheorem
