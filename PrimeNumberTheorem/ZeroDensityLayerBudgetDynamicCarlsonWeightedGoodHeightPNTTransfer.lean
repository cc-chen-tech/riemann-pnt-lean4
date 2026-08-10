import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonWeightedGoodHeightTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClosedRealAxisTargetDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualExplicitFormulaClusterDecomposition
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetTwoHeightComplementSplit

/-!
# Dynamic Carlson transfer to the actual PNT error

This module closes the upper-bound path from the dynamic Carlson estimate at
the weighted balanced selected good height to the actual multiplicity-aware
explicit formula.

The positive-height zeta tail is controlled automatically by the finite strip
budget.  A strict real-part gap for the fixed real-ordinate zeros then gives
the complete finite zero-tail estimate.  Finally, the closed real-axis term
and the selected-contour remainder are added at natural evaluation points.
-/

namespace PrimeNumberTheorem

open Complex Filter Topology

/-- Natural-point target-amplitude negligibility is closed under addition. -/
theorem NaturalPointTargetAmplitudeNegligible.add
    {amplitude left right : ℕ → ℝ}
    (hamplitude : ∀ᶠ m in atTop, 0 < amplitude m)
    (hleft : NaturalPointTargetAmplitudeNegligible amplitude left)
    (hright : NaturalPointTargetAmplitudeNegligible amplitude right) :
    NaturalPointTargetAmplitudeNegligible amplitude
      (fun m => left m + right m) := by
  unfold NaturalPointTargetAmplitudeNegligible at hleft hright ⊢
  have hupper :
      Tendsto
        (fun m => |left m| / amplitude m + |right m| / amplitude m)
        atTop (nhds 0) := by
    simpa using hleft.add hright
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hamplitude] with m hm
    exact div_nonneg (abs_nonneg _) hm.le
  · filter_upwards [hamplitude] with m hm
    calc
      |left m + right m| / amplitude m ≤
          (|left m| + |right m|) / amplitude m :=
        div_le_div_of_nonneg_right (abs_add_le _ _) hm.le
      _ = |left m| / amplitude m + |right m| / amplitude m := by
        ring

/-- The automatic finite-strip Carlson estimate controls the complete
positive-height zeta tail at the weighted balanced selected good height. -/
theorem
    actualZetaFiniteStrips_weightedBalancedGoodHeight_dynamicCarlson_positiveTail_negligible
    {beta : ℝ} {n : ℕ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositivePNTTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)) := by
  have hsum :=
    actualZetaFiniteStrips_weightedBalancedGoodHeight_dynamicCarlson_layerNormSum_negligible
      sigma tau kappa hbetaOne hsigma hsigmaOne htau hthreshold
      selection input hfixedSigma hkappa hnorm hre
  refine TargetAmplitudeNegligible.of_eventually_abs_le
    (targetZeroPowerAmplitude_eventually_pos beta) hsum ?_
  filter_upwards with x
  have hnonneg :
      0 ≤ dynamicPositivePNTTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection) x :=
    norm_nonneg _
  rw [abs_of_nonneg hnonneg]
  exact dynamicPositivePNTTailNorm_le_sum_layerNorms input x

/-- Adding the fixed real-ordinate residual gives target-scale control of the
complete multiplicity-weighted finite zeta sum. -/
theorem
    actualZetaFiniteStrips_weightedBalancedGoodHeight_dynamicCarlson_fullTail_negligible
    {beta : ℝ} {n : ℕ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullPNTZeroTailNorm
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  let H :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
      beta sigma tau selection
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have hheightBounds :=
    eventually_selectedUniformGoodHeight_gt_one_le_self
      hspec.2.1 hspec.2.2.1.le selection
  have hheight : ∀ᶠ x in atTop, 0 ≤ H x := by
    filter_upwards [hheightBounds] with x hx
    have hx0 :
        0 ≤ selectedUniformGoodHeight alpha selection x :=
      (zero_lt_one.trans hx.1).le
    simpa [H, alpha,
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using hx0
  have hrealOutside :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re < beta := by
    intro rho hrho
    apply hreal rho
    simpa [realOrdinateNontrivialZerosOutsideClusterFinset] using hrho
  have hrealNegligible :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicRealOrdinatePNTZeroTailNorm H) := by
    have houtside :=
      dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
        H ∅ beta hheight hrealOutside
    have heq :
        dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H ∅ =
          dynamicRealOrdinatePNTZeroTailNorm H := by
      funext x
      simp [dynamicRealOrdinateOutsideClusterPNTZeroTailNorm,
        realOrdinateNontrivialZerosOutsideClusterFinset,
        dynamicRealOrdinatePNTZeroTailNorm]
    rw [← heq]
    exact houtside
  have hpositive :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicPositivePNTTailNorm H) := by
    simpa [H] using
      actualZetaFiniteStrips_weightedBalancedGoodHeight_dynamicCarlson_positiveTail_negligible
        sigma tau kappa hbetaOne hsigma hsigmaOne htau hthreshold
        selection input hfixedSigma hkappa hnorm hre
  simpa [H] using
    dynamicFullPNTZeroTailNorm_targetAmplitudeNegligible
      (targetZeroPowerAmplitude_eventually_pos beta)
      hpositive hrealNegligible

/-- At natural points, the actual relative PNT error is negligible on the
target-zero scale at the same weighted balanced selected good height. -/
theorem
    relativeChebyshevPsi0Error_natural_weightedBalancedGoodHeight_dynamicCarlson_negligible
    {beta : ℝ} (hbeta : 0 < beta) {n : ℕ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ)) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  let H :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
      beta sigma tau selection
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have hfull :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicFullPNTZeroTailNorm H) := by
    simpa [H] using
      actualZetaFiniteStrips_weightedBalancedGoodHeight_dynamicCarlson_fullTail_negligible
        sigma tau kappa hbetaOne hsigma hsigmaOne htau hthreshold
        selection input hfixedSigma hkappa hnorm hre hreal
  have hfinite :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (fun x => (dynamicFinitePNTZeroSum H x).re) := by
    refine TargetAmplitudeNegligible.of_eventually_abs_le
      (targetZeroPowerAmplitude_eventually_pos beta) hfull ?_
    filter_upwards with x
    calc
      |(dynamicFinitePNTZeroSum H x).re| ≤
          ‖dynamicFinitePNTZeroSum H x‖ :=
        abs_re_le_norm _
      _ = dynamicFullPNTZeroTailNorm H x := by
        rfl
  have hremainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H := by
    simpa [H, alpha,
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using
      selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hbeta hspec.2.1 hspec.2.2.1.le hspec.2.2.2.1 selection
  have hamplitudeNat :
      ∀ᶠ m : ℕ in atTop,
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hclosedRemainder :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
            actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.add hamplitudeNat
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
        hbeta).naturalPoint
      hremainder.negligible
  have htotal :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          (dynamicFinitePNTZeroSum H (m : ℝ)).re +
            (actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ))) :=
    NaturalPointTargetAmplitudeNegligible.add hamplitudeNat
      hfinite.naturalPoint hclosedRemainder
  unfold NaturalPointTargetAmplitudeNegligible at htotal ⊢
  apply htotal.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_dynamicFinite_add_closed_add_remainder
    H (m : ℝ)]

/-- The target-scale estimate implies ordinary PNT decay on natural points
because `beta < 1`. -/
theorem
    tendsto_relativeChebyshevPsi0Error_natural_dynamicCarlsonWeightedGoodHeight
    {beta : ℝ} (hbeta : 0 < beta) {n : ℕ}
    (sigma tau kappa : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hnormalized :=
    relativeChebyshevPsi0Error_natural_weightedBalancedGoodHeight_dynamicCarlson_negligible
      hbeta sigma tau kappa hbetaOne hsigma hsigmaOne htau hthreshold
      selection input hfixedSigma hkappa hnorm hre hreal
  have htargetReal :
      Tendsto (targetZeroPowerAmplitude beta) atTop (nhds 0) := by
    unfold targetZeroPowerAmplitude
    convert tendsto_rpow_neg_atTop (sub_pos.mpr hbetaOne) using 1
    funext x
    congr 1
    ring
  have htarget :
      Tendsto
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) :=
    htargetReal.comp tendsto_natCast_atTop_atTop
  have habs :
      Tendsto
        (fun m : ℕ => |relativeChebyshevPsi0Error (m : ℝ)|)
        atTop (nhds 0) := by
    unfold NaturalPointTargetAmplitudeNegligible at hnormalized
    have hproduct :
        Tendsto
          (fun m : ℕ =>
            |relativeChebyshevPsi0Error (m : ℝ)| /
                targetZeroPowerAmplitude beta (m : ℝ) *
              targetZeroPowerAmplitude beta (m : ℝ))
          atTop (nhds 0) := by
      simpa only [zero_mul] using hnormalized.mul htarget
    apply hproduct.congr'
    filter_upwards
        [eventually_naturalPoint_pos_of_eventually_pos
          (targetZeroPowerAmplitude_eventually_pos beta)] with m hm
    rw [div_mul_cancel₀]
    exact hm.ne'
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa [Real.norm_eq_abs] using habs

end PrimeNumberTheorem
