import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineActualOutsideClusterCoefficient
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightClusterApproximation
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonWeightedGoodHeightPNTTransfer

/-!
# Coefficient-aware actual PNT cluster residual

The optimized actual Carlson coefficient chain now reaches the same PNT
error decomposition used by the oscillation transfer.  Positive
outside-cluster zeros are controlled by the exposed affine majorant; zero
conjugation and a strict real-ordinate gap control the complete signed
outside-cluster complement; the selected-height explicit-formula theorem
controls the contour remainder.

Consequently the actual relative PNT error minus the visible-cluster main
term is negligible relative to the target zero amplitude at natural points.
The finite outside-cluster bucket input and the real-ordinate gap remain
explicit assumptions.
-/

namespace PrimeNumberTheorem

open Filter Set
open scoped Topology

/-- At the optimized weighted selected height, the actual relative PNT error
tracks the visible cluster main term up to `o(x^(beta-1))` on natural points,
with the positive outside-cluster part supplied by the exposed Carlson
coefficient majorant. -/
theorem
    actualSelectedHeightWeightedBalancedClusterResidual_targetNegligible
    {beta : ℝ} (hbeta : 0 < beta) (hbetaOne : beta < 1)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
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
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
        beta sigma tau selection
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H S (m : ℝ)) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  let H :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
      beta sigma tau selection
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := hspec.2.1
  have halphaOne : alpha ≤ 1 := hspec.2.2.1.le
  have hmargin : 1 - beta < alpha := hspec.2.2.2.1
  have hheightInterval :
      ∀ᶠ x : ℝ in atTop,
        H x ∈
          Set.Icc
            (actualCarlsonPolynomialGoodHeightBase alpha x)
            (actualCarlsonPolynomialGoodHeightBase alpha x + 1) := by
    simpa [H, alpha,
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight,
      actualCarlsonPolynomialGoodHeightBase,
      carlsonPolynomialHeight] using
      eventually_selectedUniformGoodHeight_mem halpha selection
  have hheightNonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    eventually_selectedHeight_nonneg halpha hheightInterval
  have hamplitude :
      ∀ᶠ x : ℝ in atTop,
        0 < targetZeroPowerAmplitude beta x :=
    targetZeroPowerAmplitude_eventually_pos beta
  have hpositiveRaw :
      Tendsto
        (fun x : ℝ =>
          dynamicPositiveOutsideClusterPNTTailNorm H S x /
            targetZeroPowerAmplitude beta x)
        atTop (nhds 0) := by
    simpa [H] using
      tendsto_actualSelectedHeightWeightedBalancedPositiveOutsideClusterTail_zero
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
        input kappa hfixedSigma hkappa hnorm hre
  have hpositive :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicPositiveOutsideClusterPNTTailNorm H S) := by
    have htailNonneg :
        ∀ x : ℝ, 0 ≤ dynamicPositiveOutsideClusterPNTTailNorm H S x := by
      intro x
      unfold dynamicPositiveOutsideClusterPNTTailNorm
      exact norm_nonneg _
    unfold TargetAmplitudeNegligible
    apply hpositiveRaw.congr'
    exact Eventually.of_forall fun x => by
      simp only [abs_of_nonneg (htailNonneg x)]
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
    change
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder
            (selectedUniformGoodHeight alpha selection) (m : ℝ))
    exact
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

end PrimeNumberTheorem
