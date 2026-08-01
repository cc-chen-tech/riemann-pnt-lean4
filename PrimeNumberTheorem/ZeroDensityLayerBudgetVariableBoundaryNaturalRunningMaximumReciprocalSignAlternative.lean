import PrimeNumberTheorem.ZeroDensityLayerBudgetReciprocalVariableBoundaryTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmega

/-!
# Reciprocal sign alternative for the natural running zero boundary

The actual natural running maximum supplies a sampled-monotone visible right
edge without assuming that a global maximal zero real part is attained.  The
reciprocal variable-boundary residual removes the polynomial-height loss, and
one unsigned moving-package witness is enough to force one persistent sign of
the true unnormalized PNT error.
-/

namespace PrimeNumberTheorem

open Filter

noncomputable section

/-- Unified reciprocal upper bound and one-sign Omega alternative from one
unsigned moving-package witness along a monotone visible right edge. -/
theorem
    actualMonotoneVariableBoundaryUnifiedUpperSignAlternative_reciprocal
    {sigma beta0 alpha epsilon eta c loss : ℝ} {H beta : ℝ → ℝ}
    (heta : 0 < eta)
    (hloss : 0 < loss) (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (hHle : ∀ᶠ m : ℕ in atTop,
      H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright : IsIndexedVariableBoundaryVisibleRightEdge
      (sigma := sigma) H beta)
    (remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta0 H)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ beta x) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ beta x)) := by
  have hsigmaBeta0 : sigma < beta0 := by linarith
  have hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta :=
    variableBoundaryAbsorptionOrGap_of_monotone hHtop hbetaMono hright
  have hresidual :=
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_reciprocal
      hbeta0 hbetaLower hHle hHtop halpha hepsilon hmargin
      hrightReal hhalf hone hright hgap remainder
  have hupper :=
    eventually_abs_relativeChebyshevPsi0Error_lt_variableBoundaryCap_add
      heta
      (actualCarlsonVariableBoundaryCoefficientCap
        hhalf hone hsigmaBeta0 hbetaLower)
      hresidual
  rcases
      variableBoundaryMainWitness_unnormalizedSignAlternativeTransfer
        hloss hlossC hresidual hmain with
    ⟨hcoefficient, hsign⟩
  exact ⟨hupper, hcoefficient, hsign⟩

/-- The visible-zero running maximum is constructed from actual zeta zeros at
the canonical selected heights.  Under the reciprocal margin, one unsigned
witness for that moving package yields the unified upper bound and one-sign
Omega alternative at the exact variable exponent. -/
theorem
    actualNaturalRunningMaximumBoundaryCanonicalGoodHeightUnifiedUpperSignAlternative_reciprocal
    {sigma beta0 alpha epsilon eta c loss : ℝ}
    (heta : 0 < eta)
    (hloss : 0 < loss) (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
            (variableBoundaryZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (naturalRunningVisibleZeroBoundaryReal
              (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
              beta0)
            (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0)
              (m : ℝ)) ∧
      0 < c - loss ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ =>
            (c - loss) * x ^
              naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0 x) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ =>
            (c - loss) * x ^
              naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight alpha)
                beta0 x)) := by
  let H := actualDynamicBoundaryCanonicalSelectedGoodHeight alpha
  let beta := naturalRunningVisibleZeroBoundaryReal H beta0
  rcases
      actualDynamicBoundaryCanonicalSelectedGoodHeight_spec
        hbeta0 halpha halphaOne hcontourMargin with
    ⟨hHle, hHtop, remainder⟩
  have hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ) := by
    filter_upwards with m
    exact beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast H beta0 m
  have hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)) :=
    naturalRunningVisibleZeroBoundaryReal_sampled_monotone H beta0
  have hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta :=
    naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge H beta0
  exact
    actualMonotoneVariableBoundaryUnifiedUpperSignAlternative_reciprocal
      heta hloss hlossC hbeta0 hbetaLower hbetaMono hHle hHtop
      halpha hepsilon hmargin hrightReal hhalf hone hright remainder
      (by simpa [H, beta] using hmain)

end
end PrimeNumberTheorem
