import PrimeNumberTheorem.ZeroDensityLayerBudgetReciprocalSigmaOnlyRunningBoundary
import PrimeNumberTheorem.ZeroDensityLayerBudgetReciprocalOptimalContourHeight

/-!
# Near-optimal sigma-only reciprocal transfer

This module replaces the fixed midpoint height window in the sigma-only
running-boundary facade by a `delta`-parameterized window whose outer exponent
is exactly `1 - beta0 + delta`.  Thus the actual selected height can approach
the reciprocal contour floor arbitrarily closely while retaining the full
upper and conditional signed transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

noncomputable def nearOptimalSigmaOnlyInnerExponent
    (sigma delta : ℝ) : ℝ :=
  reciprocalContourNearOptimalInnerExponent
    (reciprocalSigmaOnlyBeta0 sigma) delta

noncomputable def nearOptimalSigmaOnlyOuterExponent
    (sigma delta : ℝ) : ℝ :=
  reciprocalContourNearOptimalOuterExponent
    (reciprocalSigmaOnlyBeta0 sigma) delta

noncomputable def nearOptimalSigmaOnlyRunningHeight
    (sigma delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  selectedUniformGoodHeight
    (nearOptimalSigmaOnlyInnerExponent sigma delta) selection

noncomputable def nearOptimalSigmaOnlyRunningBoundary
    (sigma delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  naturalRunningVisibleZeroBoundaryReal
    (nearOptimalSigmaOnlyRunningHeight sigma delta selection)
    (reciprocalSigmaOnlyBeta0 sigma)

noncomputable def nearOptimalSigmaOnlyVisibleMain
    (sigma delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℕ → ℝ :=
  fun m =>
    dynamicVisibleClusterPNTMain
      (nearOptimalSigmaOnlyRunningHeight sigma delta selection)
      (variableBoundaryZeroPackage
        (nearOptimalSigmaOnlyRunningHeight sigma delta selection)
        (nearOptimalSigmaOnlyRunningBoundary sigma delta selection) (m : ℝ))
      (m : ℝ)

noncomputable def nearOptimalSigmaOnlyAmplitude
    (sigma delta : ℝ)
    (selection : UniformNaturalPointGoodHeightSelection) : ℝ → ℝ :=
  variableBoundaryTargetAmplitude
    (nearOptimalSigmaOnlyRunningBoundary sigma delta selection)

/-- The automatic reciprocal anchor and a positive `delta < beta0` produce a
near-optimal feasible contour window together with the unchanged low-layer
margin. -/
theorem nearOptimalSigmaOnlyParameters_spec
    {sigma delta : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hdelta : 0 < delta)
    (hdeltaBeta : delta < reciprocalSigmaOnlyBeta0 sigma) :
    sigma < reciprocalSigmaOnlyBeta0 sigma ∧
      0 < reciprocalSigmaOnlyBeta0 sigma ∧
      reciprocalSigmaOnlyBeta0 sigma < 1 ∧
      (∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
        rho.re < reciprocalSigmaOnlyBeta0 sigma) ∧
      IsReciprocalContourHeightWindow
        (reciprocalSigmaOnlyBeta0 sigma)
        (nearOptimalSigmaOnlyInnerExponent sigma delta)
        (nearOptimalSigmaOnlyOuterExponent sigma delta) ∧
      nearOptimalSigmaOnlyOuterExponent sigma delta =
        1 - reciprocalSigmaOnlyBeta0 sigma + delta ∧
      nearOptimalSigmaOnlyOuterExponent sigma delta < 1 ∧
      0 < nearOptimalSigmaOnlyOuterExponent sigma delta ∧
      0 < reciprocalSigmaOnlyEpsilon sigma ∧
      sigma - reciprocalSigmaOnlyBeta0 sigma +
          reciprocalSigmaOnlyEpsilon sigma < 0 := by
  rcases reciprocalSigmaOnlyParameters_spec hhalf hone with
    ⟨hsigmaBeta, hbeta, hbetaOne, hreal, _, _, _, _, _, hepsilon, hmargin⟩
  rcases reciprocalContourNearOptimalWindow_spec
      hbetaOne hdelta hdeltaBeta with
    ⟨hwindow, houterEq, houterOne⟩
  have houter : 0 < nearOptimalSigmaOnlyOuterExponent sigma delta := by
    exact hwindow.1.trans hwindow.2.2.2
  exact ⟨hsigmaBeta, hbeta, hbetaOne, hreal, hwindow, houterEq,
    houterOne, houter, hepsilon, hmargin⟩

/-- The near-optimal window is realized by an actual cofinal selected height
with the natural-point contour remainder certificate. -/
theorem nearOptimalSigmaOnlySelectedHeight_spec
    {sigma delta : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hdelta : 0 < delta)
    (hdeltaBeta : delta < reciprocalSigmaOnlyBeta0 sigma)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ m : ℕ in atTop,
        nearOptimalSigmaOnlyRunningHeight sigma delta selection (m : ℝ) ≤
          carlsonPolynomialHeight
            (nearOptimalSigmaOnlyOuterExponent sigma delta) (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          nearOptimalSigmaOnlyRunningHeight sigma delta selection (m : ℝ))
        atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate
        (reciprocalSigmaOnlyBeta0 sigma)
        (nearOptimalSigmaOnlyRunningHeight sigma delta selection) ∧
      nearOptimalSigmaOnlyOuterExponent sigma delta < 1 := by
  rcases reciprocalSigmaOnlyParameters_spec hhalf hone with
    ⟨_, hbeta, hbetaOne, _, _, _, _, _, _, _, _⟩
  simpa [nearOptimalSigmaOnlyInnerExponent,
    nearOptimalSigmaOnlyOuterExponent, nearOptimalSigmaOnlyRunningHeight] using
    (reciprocalContourNearOptimalSelectedHeight_spec
      hbeta hbetaOne hdelta hdeltaBeta selection)

/-- Every positive tolerance admits an actual sigma-only selected-height
window whose outer exponent is within that tolerance of `1 - beta0`. -/
theorem exists_nearOptimalSigmaOnlySelectedHeight_within
    {sigma tolerance : ℝ}
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (htolerance : 0 < tolerance)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∃ delta : ℝ,
      0 < delta ∧
      delta < reciprocalSigmaOnlyBeta0 sigma ∧
      nearOptimalSigmaOnlyOuterExponent sigma delta <
        1 - reciprocalSigmaOnlyBeta0 sigma + tolerance ∧
      (∀ᶠ m : ℕ in atTop,
        nearOptimalSigmaOnlyRunningHeight sigma delta selection (m : ℝ) ≤
          carlsonPolynomialHeight
            (nearOptimalSigmaOnlyOuterExponent sigma delta) (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          nearOptimalSigmaOnlyRunningHeight sigma delta selection (m : ℝ))
        atTop atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate
        (reciprocalSigmaOnlyBeta0 sigma)
        (nearOptimalSigmaOnlyRunningHeight sigma delta selection) := by
  rcases reciprocalSigmaOnlyParameters_spec hhalf hone with
    ⟨_, hbeta, hbetaOne, _, _, _, _, _, _, _, _⟩
  rcases exists_reciprocalContourSelectedHeight_within
      hbeta hbetaOne htolerance selection with
    ⟨delta, hdelta, hdeltaBeta, houter, hHle, hHtop, remainder⟩
  refine ⟨delta, hdelta, hdeltaBeta, ?_, ?_, ?_, ?_⟩
  · simpa [nearOptimalSigmaOnlyOuterExponent] using houter
  · simpa [nearOptimalSigmaOnlyInnerExponent,
      nearOptimalSigmaOnlyOuterExponent,
      nearOptimalSigmaOnlyRunningHeight] using hHle
  · simpa [nearOptimalSigmaOnlyInnerExponent,
      nearOptimalSigmaOnlyRunningHeight] using hHtop
  · simpa [nearOptimalSigmaOnlyInnerExponent,
      nearOptimalSigmaOnlyRunningHeight] using remainder

/-- Sigma-only running-boundary upper and conditional signed transfer at an
outer height exponent exactly `delta` above the reciprocal contour floor. -/
theorem actualNearOptimalSigmaOnlyUnifiedUpperSignedOmega
    {sigma delta eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hdelta : 0 < delta)
    (hdeltaBeta : delta < reciprocalSigmaOnlyBeta0 sigma)
    (heta : 0 < eta) (hloss : 0 < loss) (hlossC : loss < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (nearOptimalSigmaOnlyVisibleMain sigma delta selection)
        (fun m : ℕ =>
          c * nearOptimalSigmaOnlyAmplitude sigma delta selection (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (nearOptimalSigmaOnlyVisibleMain sigma delta selection)
        (fun m : ℕ =>
          c * nearOptimalSigmaOnlyAmplitude sigma delta selection (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            nearOptimalSigmaOnlyAmplitude sigma delta selection (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) *
            x ^ nearOptimalSigmaOnlyRunningBoundary sigma delta selection x) := by
  rcases nearOptimalSigmaOnlyParameters_spec
      hhalf hone hdelta hdeltaBeta with
    ⟨_, hbeta0, _, hreal, _, _, _, halpha, hepsilon, hmargin⟩
  rcases nearOptimalSigmaOnlySelectedHeight_spec
      hhalf hone hdelta hdeltaBeta selection with
    ⟨hHle, hHtop, remainder, _⟩
  exact actualMonotoneVariableBoundaryUnifiedUpperSignedOmega_reciprocal
    heta hloss hlossC hbeta0
    (Filter.univ_mem' fun m =>
      beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast
        (nearOptimalSigmaOnlyRunningHeight sigma delta selection)
        (reciprocalSigmaOnlyBeta0 sigma) m)
    (naturalRunningVisibleZeroBoundaryReal_sampled_monotone
      (nearOptimalSigmaOnlyRunningHeight sigma delta selection)
      (reciprocalSigmaOnlyBeta0 sigma))
    hHle hHtop halpha hepsilon hmargin hreal hhalf hone
    (naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge
      (sigma := sigma)
      (nearOptimalSigmaOnlyRunningHeight sigma delta selection)
      (reciprocalSigmaOnlyBeta0 sigma))
    remainder hmainPos hmainNeg

end

end PrimeNumberTheorem
