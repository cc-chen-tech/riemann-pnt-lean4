import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryAmplitudeDomination
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryVisibleCarlsonTail

/-!
# Variable-boundary visible residual assembly

This module connects the nonnegative visible Carlson kernel tail to the actual
signed complement outside a moving equal-real-part package through one exact
pointwise majorization interface.  Fixed-exponent closed-axis and contour
estimates are then promoted to the moving target amplitude and assembled with
the exact explicit formula.

The majorization interface is deliberately explicit: proving it from the
finite complement and indexed Carlson sum remains a separate indexing bridge.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- The actual signed complement outside the moving boundary package is
eventually dominated, after target normalization, by the nonnegative visible
Carlson kernel tail. -/
def VariableBoundaryVisibleComplementMajorized
    {sigma : ℝ} (H beta : ℝ → ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    |dynamicOutsideClusterPNTComplement H
        (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| /
        variableBoundaryTargetAmplitude beta (m : ℝ) ≤
      variableBoundaryVisibleNormalizedKernelTail
        (sigma := sigma) H beta m

/-- Visible Carlson-tail decay transfers to target-amplitude negligibility of
the actual signed complement once the finite-sum/indexing majorization is
available. -/
theorem variableBoundaryVisibleComplement_targetAmplitudeNegligible
    {sigma : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (hmajorized :
      VariableBoundaryVisibleComplementMajorized
        (sigma := sigma) H beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        dynamicOutsideClusterPNTComplement H
          (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  have htail :=
    variableBoundaryVisibleNormalizedKernelTail_tendsto_zero
      hhalf hone hright hgap
  have hamplitude := eventually_variableBoundaryTargetAmplitude_pos beta
  unfold NaturalPointTargetAmplitudeNegligible
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [hamplitude] with m hamplitudeM
    exact ha.trans_le (div_nonneg (abs_nonneg _) hamplitudeM.le)
  · intro b hb
    have htailB := (tendsto_order.mp htail).2 b hb
    unfold VariableBoundaryVisibleComplementMajorized at hmajorized
    filter_upwards [hmajorized, htailB] with m hmajorizedM htailM
    exact hmajorizedM.trans_lt htailM

/-- Complete moving-target residual theorem for the actual explicit formula.
The analytic closed-axis and contour estimates may be supplied at any fixed
`beta0` eventually below the moving boundary. -/
theorem
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible
    {sigma beta0 : ℝ} {H beta : ℝ → ℝ}
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (hmajorized :
      VariableBoundaryVisibleComplementMajorized
        (sigma := sigma) H beta)
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta0 H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  have hamplitude := eventually_variableBoundaryTargetAmplitude_pos beta
  have hclosedFixed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta0 (m : ℝ))
        (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
      hbeta0).naturalPoint
  have hclosed :=
    naturalPointTargetAmplitudeNegligible_variableBoundary_of_fixed
      hbetaLower hclosedFixed
  have hcontour :=
    naturalPointTargetAmplitudeNegligible_variableBoundary_of_fixed
      hbetaLower remainder.negligible
  have hcomplement :=
    variableBoundaryVisibleComplement_targetAmplitudeNegligible
      hhalf hone hright hgap hmajorized
  have hthree :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H
              (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.add hamplitude
      (NaturalPointTargetAmplitudeNegligible.add
        hamplitude hclosed hcontour)
      hcomplement
  unfold NaturalPointTargetAmplitudeNegligible at hthree ⊢
  apply hthree.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_variableBoundaryPackage_add_actualResiduals
    H beta (m : ℝ)]
  congr 2
  all_goals ring

end PrimeNumberTheorem
