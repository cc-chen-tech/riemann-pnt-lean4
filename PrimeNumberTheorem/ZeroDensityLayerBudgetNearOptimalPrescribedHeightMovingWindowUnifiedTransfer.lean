import PrimeNumberTheorem.ZeroDensityLayerBudgetNearOptimalPrescribedHeightAnchorTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryMovingWindowMeanSquareHandoff

/-!
# Near-optimal prescribed height with a moving-window lower transfer

The near-optimal prescribed-height selector and the reciprocal moving-boundary
lower transfer are assembled here.  One strict normalized square-energy input
now yields, in a single theorem, the anchor approximation, selected-height
control, the PNT upper bound, and one persistent oscillation sign.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

noncomputable section

/-- A strict mean-square lower bound for the normalized near-optimal moving
package supplies the unsigned natural-point witness at its exact variable
target amplitude. -/
theorem
    nearOptimalPrescribedHeightMovingPackageWitness_of_windowMeanSquare
    {sigma alpha delta c : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hc : 0 ≤ c)
    (henergy :
      HasFarWindowStrictMeanSquareLowerBound
        (fun m : ℕ =>
          nearOptimalPrescribedHeightVisibleMain
              sigma alpha delta selection m /
            nearOptimalPrescribedHeightAmplitude
              sigma alpha delta selection (m : ℝ))
        c) :
    HasFarNaturalPointTargetAmplitudeWitness
      (nearOptimalPrescribedHeightVisibleMain sigma alpha delta selection)
      (fun m : ℕ =>
        c * nearOptimalPrescribedHeightAmplitude
          sigma alpha delta selection (m : ℝ)) := by
  apply henergy.normalized_to_mul_amplitude hc
  exact eventually_variableBoundaryTargetAmplitude_pos _

/-- Unified near-optimal-height certificate and reciprocal upper/lower PNT
transfer from one repeatable moving-window square-energy lower bound. -/
theorem
    actualNearOptimalPrescribedHeightUnifiedUpperSignAlternative_of_windowMeanSquare_reciprocal
    {sigma alpha delta eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (halpha : 0 < alpha) (halphaOne : alpha < 1)
    (hdelta : 0 < delta) (hdeltaAlpha : delta < alpha)
    (heta : 0 < eta)
    (hloss : 0 < loss) (hlossC : loss < c)
    (hc : 0 ≤ c)
    (henergy :
      HasFarWindowStrictMeanSquareLowerBound
        (fun m : ℕ =>
          nearOptimalPrescribedHeightVisibleMain
              sigma alpha delta selection m /
            nearOptimalPrescribedHeightAmplitude
              sigma alpha delta selection (m : ℝ))
        c) :
    prescribedHeightAnchorFloor sigma alpha ≤
        nearOptimalPrescribedHeightBeta0 sigma alpha delta ∧
      nearOptimalPrescribedHeightBeta0 sigma alpha delta ≤
        prescribedHeightAnchorFloor sigma alpha + delta ∧
      (∀ᶠ m : ℕ in atTop,
        nearOptimalPrescribedHeightRunningHeight
            sigma alpha delta selection (m : ℝ) ≤
          carlsonPolynomialHeight alpha (m : ℝ)) ∧
      Tendsto
        (fun m : ℕ =>
          nearOptimalPrescribedHeightRunningHeight
            sigma alpha delta selection (m : ℝ))
        atTop atTop ∧
      (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            nearOptimalPrescribedHeightAmplitude
              sigma alpha delta selection (m : ℝ)) ∧
      0 < c - loss ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ =>
            (c - loss) * x ^
              nearOptimalPrescribedHeightRunningBoundary
                sigma alpha delta selection x) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ =>
            (c - loss) * x ^
              nearOptimalPrescribedHeightRunningBoundary
                sigma alpha delta selection x)) := by
  rcases nearOptimalPrescribedHeightParameters_spec
      hhalf hone halphaOne hdelta hdeltaAlpha with
    ⟨_, hbeta0, _, hreal, hfloor, hwithin, _, hepsilon, hmargin⟩
  rcases nearOptimalPrescribedHeightSelectedHeight_spec
      hhalf hone halphaOne hdelta hdeltaAlpha selection with
    ⟨hHle, hHtop, remainder⟩
  have hmain :=
    nearOptimalPrescribedHeightMovingPackageWitness_of_windowMeanSquare
      selection hc henergy
  have hunified :=
    actualMonotoneVariableBoundaryUnifiedUpperSignAlternative_reciprocal
      heta hloss hlossC hbeta0
      (Filter.univ_mem' fun m =>
        beta0_le_naturalRunningVisibleZeroBoundaryReal_natCast
          (nearOptimalPrescribedHeightRunningHeight
            sigma alpha delta selection)
          (nearOptimalPrescribedHeightBeta0 sigma alpha delta) m)
      (naturalRunningVisibleZeroBoundaryReal_sampled_monotone
        (nearOptimalPrescribedHeightRunningHeight
          sigma alpha delta selection)
        (nearOptimalPrescribedHeightBeta0 sigma alpha delta))
      hHle hHtop halpha hepsilon hmargin hreal hhalf hone
      (naturalRunningVisibleZeroBoundaryReal_indexedVisibleRightEdge
        (sigma := sigma)
        (nearOptimalPrescribedHeightRunningHeight
          sigma alpha delta selection)
        (nearOptimalPrescribedHeightBeta0 sigma alpha delta))
      remainder
      (by
        simpa [nearOptimalPrescribedHeightVisibleMain,
          nearOptimalPrescribedHeightAmplitude,
          nearOptimalPrescribedHeightRunningBoundary] using hmain)
  refine ⟨hfloor, hwithin, hHle, hHtop, ?_⟩
  simpa [nearOptimalPrescribedHeightAmplitude,
    nearOptimalPrescribedHeightRunningBoundary] using hunified

end
end PrimeNumberTheorem
