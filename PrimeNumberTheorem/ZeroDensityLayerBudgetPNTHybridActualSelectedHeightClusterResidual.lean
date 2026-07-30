import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualSelectedHeightFiniteStrips
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightClusterApproximation
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonWeightedGoodHeightPNTTransfer

/-!
# Actual PNT cluster residual at the optimized hybrid selected height

The optimized hybrid schedule uses global zero counting on thresholds at most
`1 / 2` and Carlson density above `1 / 2`.  This file connects its full
outside-cluster tail estimate to the natural-point explicit formula.

The mixed margin automatically places the height exponent strictly above the
contour floor.  Under nonnegative strip endpoints it also places the exponent
at most one, so the existing natural-point contour remainder theorem applies
without an extra exponent hypothesis.
-/

namespace PrimeNumberTheorem

open Filter Set
open scoped Topology

noncomputable section

/-- A positive mixed optimal margin puts the balanced exponent strictly above
the explicit-formula contour floor. -/
theorem pntHybridAffineDensityFloor_lt_balancedExponent
    {n : ℕ} {beta : ℝ}
    {sigma tau : Fin (n + 1) → ℝ}
    (hdelta : 0 < pntHybridAffineOptimalMargin beta sigma tau) :
    1 - beta < pntHybridAffineBalancedExponent beta sigma tau := by
  simp [pntHybridAffineBalancedExponent, finiteAffineBalancedExponent,
    pntHybridAffineDensityFloor]
  exact hdelta

/-- With nonnegative strip endpoints, the feasible optimized mixed exponent
is at most one. -/
theorem pntHybridAffineBalancedExponent_le_one
    {n : ℕ} {beta : ℝ}
    {sigma tau : Fin (n + 1) → ℝ}
    (hbetaOne : beta < 1)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (htau : ∀ i, 0 ≤ tau i) :
    pntHybridAffineBalancedExponent beta sigma tau ≤ 1 := by
  let i : Fin (n + 1) := ⟨0, Nat.succ_pos n⟩
  let alpha := pntHybridAffineBalancedExponent beta sigma tau
  let delta := pntHybridAffineOptimalMargin beta sigma tau
  let slope := pntHybridAffineDensitySlope sigma i
  have hdelta : 0 < delta := by
    exact pntHybridAffineOptimalMargin_pos hsigmaOneHigh hbudget
  have halpha : 0 < alpha := by
    exact pntHybridAffineBalancedExponent_pos
      hbetaOne hsigmaOneHigh hbudget
  have hslope : 0 < slope := by
    exact pntHybridAffineDensitySlope_pos hsigmaOneHigh i
  have hstrip :=
    (pntHybridAffineBalancedExponent_marginCertificate
      beta sigma tau hsigmaOneHigh).strip i
  have halphaEq : alpha = 1 - beta + delta := by
    rfl
  have hslopeAlpha : 0 ≤ slope * alpha :=
    mul_nonneg hslope.le halpha.le
  change delta ≤ beta - tau i - slope * alpha at hstrip
  have htauNonneg : 0 ≤ tau i := htau i
  change alpha ≤ 1
  linarith

/-- At the optimized hybrid selected height, the actual relative PNT error
tracks the visible-cluster main term up to `o(x^(beta-1))` on natural
points. -/
theorem
    actualHybridSelectedHeightClusterResidual_targetNegligible
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (htau : ∀ i, 0 ≤ tau i)
    (hsigmaOneHigh :
      ∀ i ∈ pintzCarlsonHighDensityIndices sigma, sigma i < 1)
    (hbudget :
      ∀ i,
        pntHybridAffineDensitySlope sigma i *
              pntHybridAffineDensityFloor beta <
            pntHybridAffineDensityCeiling beta tau i)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (pntHybridAffineSelectedGoodHeight
            beta sigma tau selection x)
          S (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    let H :=
      pntHybridAffineSelectedGoodHeight beta sigma tau selection
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H S (m : ℝ)) := by
  let alpha := pntHybridAffineBalancedExponent beta sigma tau
  let H := pntHybridAffineSelectedGoodHeight beta sigma tau selection
  have hdelta :
      0 < pntHybridAffineOptimalMargin beta sigma tau :=
    pntHybridAffineOptimalMargin_pos hsigmaOneHigh hbudget
  have halpha : 0 < alpha := by
    exact pntHybridAffineBalancedExponent_pos
      hbetaOne hsigmaOneHigh hbudget
  have halphaOne : alpha ≤ 1 := by
    exact pntHybridAffineBalancedExponent_le_one
      hbetaOne hsigmaOneHigh hbudget htau
  have hmargin : 1 - beta < alpha := by
    exact pntHybridAffineDensityFloor_lt_balancedExponent hdelta
  have hheightInterval :
      ∀ᶠ x : ℝ in atTop,
        H x ∈
          Set.Icc
            (actualCarlsonPolynomialGoodHeightBase alpha x)
            (actualCarlsonPolynomialGoodHeightBase alpha x + 1) := by
    simpa [H, alpha, pntHybridAffineSelectedGoodHeight,
      actualCarlsonPolynomialGoodHeightBase] using
      eventually_selectedUniformGoodHeight_mem halpha selection
  have hheightNonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    eventually_selectedHeight_nonneg halpha hheightInterval
  have hamplitude :
      ∀ᶠ x : ℝ in atTop,
        0 < targetZeroPowerAmplitude beta x :=
    targetZeroPowerAmplitude_eventually_pos beta
  have hpositive :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicPositiveOutsideClusterPNTTailNorm H S) := by
    simpa [H] using
      actualHybridFiniteStripsOutsideCluster_optimizedSelectedHeight_positiveTail_negligible
        sigma tau kappa selection input hbetaOne hfixedSigma
        hsigmaOneHigh hbudget hkappa hnorm hre
  have hrealTail :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S) :=
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      H S beta hheightNonneg hreal
  have hfullTail :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicFullOutsideClusterPNTZeroTailNorm H S) :=
    dynamicFullOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      hS hamplitude hpositive hrealTail
  have hcomplementCertificate :
      ClusterExcludedTargetComplementCertificate
        (targetZeroPowerAmplitude beta)
        (dynamicOutsideClusterPNTComplement H S)
        (dynamicFullOutsideClusterPNTZeroTailNorm H S) := by
    refine
      { amplitude_eventually_pos := hamplitude
        complement_dominated := ?_
        excluded_tail_negligible := hfullTail }
    exact Eventually.of_forall fun x =>
      abs_dynamicOutsideClusterPNTComplement_le_tailNorm H S x
  have hclosed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
      hbeta).naturalPoint
  have hcontour :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) := by
    simpa [H, alpha, pntHybridAffineSelectedGoodHeight] using
      (selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hbeta halpha halphaOne hmargin selection).negligible
  have hcomplement :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          dynamicOutsideClusterPNTComplement H S (m : ℝ)) :=
    hcomplementCertificate.complement_negligible.naturalPoint
  have hamplitudeNat :
      ∀ᶠ m : ℕ in atTop,
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_naturalPoint_pos_of_eventually_pos hamplitude
  have hthree :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H S (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.add hamplitudeNat
      (NaturalPointTargetAmplitudeNegligible.add
        hamplitudeNat hclosed hcontour)
      hcomplement
  unfold NaturalPointTargetAmplitudeNegligible at hthree ⊢
  apply hthree.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
    H S (m : ℝ)]
  simp only [H, add_sub_cancel_left]

end

end PrimeNumberTheorem
