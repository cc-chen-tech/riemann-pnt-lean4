import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryNaturalRunningMaximumUnifiedUpperSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonAutomaticBetaPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryBalancedGoodHeightTransfer

/-!
# Sigma-only running-boundary unified transfer

All height, density-slack, and fixed lower-anchor parameters are selected from
one Carlson threshold `sigma`.  The fixed real-ordinate zero slice is included
in the lower-anchor bottleneck, so its strict separation is automatic.
-/

namespace PrimeNumberTheorem

open Filter

noncomputable section

/-- Positive density slack selected from the distance of `sigma` to one. -/
noncomputable def sigmaOnlyRunningBoundaryEpsilon (sigma : ℝ) : ℝ :=
  (1 - sigma) / 4

/-- Joint obstruction from the real-ordinate zero slice and the Carlson
height-plus-density threshold. -/
noncomputable def sigmaOnlyRunningBoundaryJointBottleneck
    (sigma : ℝ) : ℝ :=
  max realOrdinatePNTZeroBottleneck
    (sigma + actualDynamicBoundaryBalancedGoodHeightExponent sigma +
      sigmaOnlyRunningBoundaryEpsilon sigma)

/-- Fixed lower anchor halfway between the joint obstruction and one. -/
noncomputable def sigmaOnlyRunningBoundaryBeta0 (sigma : ℝ) : ℝ :=
  (sigmaOnlyRunningBoundaryJointBottleneck sigma + 1) / 2

/-- A single Carlson threshold in `(1/2,1)` automatically supplies every
numerical and real-zero hypothesis of the running-boundary transfer. -/
theorem sigmaOnlyRunningBoundaryParameters_spec
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    0 < actualDynamicBoundaryBalancedGoodHeightExponent sigma ∧
      actualDynamicBoundaryBalancedGoodHeightExponent sigma ≤ 1 ∧
      0 < sigmaOnlyRunningBoundaryEpsilon sigma ∧
      0 < sigmaOnlyRunningBoundaryBeta0 sigma ∧
      1 - sigmaOnlyRunningBoundaryBeta0 sigma <
        actualDynamicBoundaryBalancedGoodHeightExponent sigma ∧
      sigma - sigmaOnlyRunningBoundaryBeta0 sigma +
          actualDynamicBoundaryBalancedGoodHeightExponent sigma +
          sigmaOnlyRunningBoundaryEpsilon sigma < 0 ∧
      (∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
        rho.re < sigmaOnlyRunningBoundaryBeta0 sigma) := by
  let alpha := actualDynamicBoundaryBalancedGoodHeightExponent sigma
  let epsilon := sigmaOnlyRunningBoundaryEpsilon sigma
  let B := sigmaOnlyRunningBoundaryJointBottleneck sigma
  let beta0 := sigmaOnlyRunningBoundaryBeta0 sigma
  have halpha : 0 < alpha := by
    dsimp [alpha, actualDynamicBoundaryBalancedGoodHeightExponent]
    linarith
  have halphaOne : alpha ≤ 1 := by
    dsimp [alpha, actualDynamicBoundaryBalancedGoodHeightExponent]
    linarith
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon, sigmaOnlyRunningBoundaryEpsilon]
    linarith
  have hthreshold : sigma + alpha + epsilon < 1 := by
    dsimp [alpha, epsilon, actualDynamicBoundaryBalancedGoodHeightExponent,
      sigmaOnlyRunningBoundaryEpsilon]
    linarith
  have hBnonneg : 0 ≤ B := by
    exact realOrdinatePNTZeroBottleneck_nonneg.trans
      (le_max_left _ _)
  have hBOne : B < 1 := by
    exact max_lt realOrdinatePNTZeroBottleneck_lt_one hthreshold
  have hBBeta : B < beta0 := by
    dsimp [beta0, sigmaOnlyRunningBoundaryBeta0]
    linarith
  have hthresholdBeta : sigma + alpha + epsilon < beta0 :=
    (le_max_right realOrdinatePNTZeroBottleneck
      (sigma + alpha + epsilon)).trans_lt hBBeta
  have hidentity : sigma + 2 * alpha = 1 := by
    dsimp [alpha, actualDynamicBoundaryBalancedGoodHeightExponent]
    ring
  have hbeta0 : 0 < beta0 := by
    dsimp [beta0, sigmaOnlyRunningBoundaryBeta0]
    linarith
  have hcontour : 1 - beta0 < alpha := by
    linarith
  have hmargin : sigma - beta0 + alpha + epsilon < 0 := by
    linarith
  have hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0 := by
    intro rho hrho
    exact
      (realOrdinateNontrivialZero_re_le_bottleneck hrho).trans_lt
        ((le_max_left realOrdinatePNTZeroBottleneck
          (sigma + alpha + epsilon)).trans_lt hBBeta)
  simpa [alpha, epsilon, beta0] using
    ⟨halpha, halphaOne, hepsilon, hbeta0, hcontour, hmargin, hreal⟩

/-- Unified actual PNT upper and conditional signed-Omega transfer whose full
moving boundary and all numerical parameters are determined by `sigma`. -/
theorem actualSigmaOnlyNaturalRunningMaximumBoundaryUnifiedUpperSignedOmega
    {sigma eta c loss : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight
              (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
            (variableBoundaryZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight
                  (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
                (sigmaOnlyRunningBoundaryBeta0 sigma))
              (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (naturalRunningVisibleZeroBoundaryReal
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
              (sigmaOnlyRunningBoundaryBeta0 sigma))
            (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (actualDynamicBoundaryCanonicalSelectedGoodHeight
              (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
            (variableBoundaryZeroPackage
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight
                  (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
                (sigmaOnlyRunningBoundaryBeta0 sigma))
              (m : ℝ))
            (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude
            (naturalRunningVisibleZeroBoundaryReal
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
              (sigmaOnlyRunningBoundaryBeta0 sigma))
            (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude
              (naturalRunningVisibleZeroBoundaryReal
                (actualDynamicBoundaryCanonicalSelectedGoodHeight
                  (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
                (sigmaOnlyRunningBoundaryBeta0 sigma))
              (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * x ^
            naturalRunningVisibleZeroBoundaryReal
              (actualDynamicBoundaryCanonicalSelectedGoodHeight
                (actualDynamicBoundaryBalancedGoodHeightExponent sigma))
              (sigmaOnlyRunningBoundaryBeta0 sigma) x) := by
  rcases sigmaOnlyRunningBoundaryParameters_spec hhalf hone with
    ⟨halpha, halphaOne, hepsilon, hbeta0, hcontour, hmargin, hreal⟩
  exact
    actualNaturalRunningMaximumBoundaryCanonicalGoodHeightUnifiedUpperSignedOmega
      heta hloss hlossC hbeta0 halpha halphaOne hcontour hepsilon hmargin
        hreal hhalf hone hmainPos hmainNeg

end

end PrimeNumberTheorem
