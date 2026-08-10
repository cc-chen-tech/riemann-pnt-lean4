import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightMovingCarlsonPositiveTailTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer

/-!
# Selected moving Carlson transfer to the actual PNT error

This module connects the selected-height moving Carlson decomposition to the
complete finite zeta-zero sum and then to the actual truncated explicit
formula.  At ordinary relative-PNT scale, real-ordinate nontrivial zeros are
automatic because every nontrivial zero has real part strictly below one.
-/

namespace PrimeNumberTheorem

open Filter
open Complex
open scoped Topology

/-- Real-ordinate finite-zero residuals vanish at every positive-exponent
selected height in a unit polynomial window. -/
theorem
    tendsto_dynamicRealOrdinatePNTZeroTailNorm_of_selectedHeightUnitWindow
    {H : ℝ → ℝ} {alpha : ℝ}
    (halpha : 0 < alpha)
    (hwindow : ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc
        (carlsonPolynomialHeight alpha x)
        (carlsonPolynomialHeight alpha x + 1)) :
    Tendsto
      (fun m : ℕ =>
        dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ))
      atTop (nhds 0) := by
  have hHtop :=
    tendsto_selectedHeight_atTop_of_unitWindow halpha hwindow
  have hheight : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hHtop.eventually (eventually_ge_atTop (0 : ℝ))
  have hre :
      ∀ rho ∈
        realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re < 1 := by
    intro rho hrho
    have hreal :
        rho ∈ realOrdinateNontrivialZerosFinset 0 := by
      simpa [realOrdinateNontrivialZerosOutsideClusterFinset] using hrho
    have hzero : RiemannHypothesis.IsNontrivialZero rho :=
      (mem_nontrivialZerosFinset.mp
        (mem_realOrdinateNontrivialZerosFinset.mp hreal).1).1
    exact hzero.2.2
  have hnegligible :=
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      H ∅ 1 hheight hre
  have heq :
      dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H ∅ =
        dynamicRealOrdinatePNTZeroTailNorm H := by
    funext x
    simp [dynamicRealOrdinateOutsideClusterPNTZeroTailNorm,
      realOrdinateNontrivialZerosOutsideClusterFinset,
      dynamicRealOrdinatePNTZeroTailNorm]
  rw [heq] at hnegligible
  unfold TargetAmplitudeNegligible at hnegligible
  have hrealTendsto :
      Tendsto (dynamicRealOrdinatePNTZeroTailNorm H)
        atTop (nhds 0) := by
    simpa [targetZeroPowerAmplitude,
      dynamicRealOrdinatePNTZeroTailNorm] using hnegligible
  exact hrealTendsto.comp tendsto_natCast_atTop_atTop

/-- Complete finite zeta-zero tail decay at a selected moving Carlson height. -/
theorem tendsto_dynamicFullPNTZeroTailNorm_of_selectedHeightMovingCarlson
    {H : ℝ → ℝ} {innerAlpha outerAlpha epsilon : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (hwindow : ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc
        (carlsonPolynomialHeight innerAlpha x)
        (carlsonPolynomialHeight innerAlpha x + 1))
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap : ∀ᶠ m : ℕ in atTop,
      ActualSelectedHeightMovingPositiveRightEdgeCap H delta m)
    (hmiddle :
      Tendsto
        (actualSelectedHeightMovingCarlsonMiddleMass H delta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ => dynamicFullPNTZeroTailNorm H (m : ℝ))
      atTop (nhds 0) := by
  have hpositive :=
    tendsto_dynamicPositivePNTTailNorm_of_selectedHeightMovingCarlson
      hinner hstrict houter hepsilon hmargin hwindow
      hdelta hgap hcap hmiddle
  have hreal :=
    tendsto_dynamicRealOrdinatePNTZeroTailNorm_of_selectedHeightUnitWindow
      hinner hwindow
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          dynamicPositivePNTTailNorm H (m : ℝ) +
            dynamicPositivePNTTailNorm H (m : ℝ) +
            dynamicRealOrdinatePNTZeroTailNorm H (m : ℝ))
        atTop (nhds 0) := by
    simpa using (hpositive.add hpositive).add hreal
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards with m
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast hm
    exact dynamicFullPNTZeroTailNorm_le_two_positive_add_real hmPos

/-- Selected moving Carlson density control plus an actual natural-point
contour remainder certificate proves ordinary relative PNT decay. -/
theorem
    tendsto_relativeChebyshevPsi0Error_of_selectedHeightMovingCarlson
    {H : ℝ → ℝ} {innerAlpha outerAlpha epsilon : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (hwindow : ∀ᶠ x : ℝ in atTop,
      H x ∈ Set.Icc
        (carlsonPolynomialHeight innerAlpha x)
        (carlsonPolynomialHeight innerAlpha x + 1))
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap : ∀ᶠ m : ℕ in atTop,
      ActualSelectedHeightMovingPositiveRightEdgeCap H delta m)
    (hmiddle :
      Tendsto
        (actualSelectedHeightMovingCarlsonMiddleMass H delta)
        atTop (nhds 0))
    (hremainder :
      ActualSelectedHeightNaturalPointRemainderCertificate 1 H) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hfull :=
    tendsto_dynamicFullPNTZeroTailNorm_of_selectedHeightMovingCarlson
      hinner hstrict houter hepsilon hmargin hwindow
      hdelta hgap hcap hmiddle
  have hfiniteAbs :
      Tendsto
        (fun m : ℕ =>
          |(dynamicFinitePNTZeroSum H (m : ℝ)).re|)
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hfull
    · filter_upwards with m
      exact abs_nonneg _
    · filter_upwards with m
      calc
        |(dynamicFinitePNTZeroSum H (m : ℝ)).re| ≤
            ‖dynamicFinitePNTZeroSum H (m : ℝ)‖ :=
          abs_re_le_norm _
        _ = dynamicFullPNTZeroTailNorm H (m : ℝ) := by
          rfl
  have hfinite :
      Tendsto
        (fun m : ℕ =>
          (dynamicFinitePNTZeroSum H (m : ℝ)).re)
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using hfiniteAbs
  have hclosedNegligible :=
    actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
      (show (0 : ℝ) < 1 by norm_num)
  unfold TargetAmplitudeNegligible at hclosedNegligible
  have hclosedAbs :
      Tendsto
        (fun x : ℝ => |actualPNTClosedRealAxisRelativeTerm x|)
        atTop (nhds 0) := by
    simpa [targetZeroPowerAmplitude] using hclosedNegligible
  have hclosed :
      Tendsto
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ))
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using
      hclosedAbs.comp tendsto_natCast_atTop_atTop
  have hremainderNegligible := hremainder.negligible
  unfold NaturalPointTargetAmplitudeNegligible at hremainderNegligible
  have hremainderAbs :
      Tendsto
        (fun m : ℕ =>
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)|)
        atTop (nhds 0) := by
    simpa [targetZeroPowerAmplitude] using hremainderNegligible
  have hremainderTendsto :
      Tendsto
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ))
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using hremainderAbs
  have htotal :
      Tendsto
        (fun m : ℕ =>
          (dynamicFinitePNTZeroSum H (m : ℝ)).re +
            (actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)))
        atTop (nhds 0) := by
    simpa using hfinite.add (hclosed.add hremainderTendsto)
  apply htotal.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_dynamicFinite_add_closed_add_remainder
    H (m : ℝ)]

/-- Generic ordinary-scale explicit-formula assembler.  Any selected height
with a vanishing complete finite zero tail and an actual natural-point
remainder certificate at target `beta = 1` proves relative PNT decay. -/
theorem tendsto_relativeChebyshevPsi0Error_of_dynamicFullPNTZeroTailNorm
    {H : ℝ → ℝ}
    (hfull :
      Tendsto
        (fun m : ℕ => dynamicFullPNTZeroTailNorm H (m : ℝ))
        atTop (nhds 0))
    (hremainder :
      ActualSelectedHeightNaturalPointRemainderCertificate 1 H) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hfiniteAbs :
      Tendsto
        (fun m : ℕ =>
          |(dynamicFinitePNTZeroSum H (m : ℝ)).re|)
        atTop (nhds 0) := by
    refine squeeze_zero' ?_ ?_ hfull
    · filter_upwards with m
      exact abs_nonneg _
    · filter_upwards with m
      calc
        |(dynamicFinitePNTZeroSum H (m : ℝ)).re| ≤
            ‖dynamicFinitePNTZeroSum H (m : ℝ)‖ :=
          abs_re_le_norm _
        _ = dynamicFullPNTZeroTailNorm H (m : ℝ) := by
          rfl
  have hfinite :
      Tendsto
        (fun m : ℕ =>
          (dynamicFinitePNTZeroSum H (m : ℝ)).re)
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using hfiniteAbs
  have hclosedNegligible :=
    actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
      (show (0 : ℝ) < 1 by norm_num)
  unfold TargetAmplitudeNegligible at hclosedNegligible
  have hclosedAbs :
      Tendsto
        (fun x : ℝ => |actualPNTClosedRealAxisRelativeTerm x|)
        atTop (nhds 0) := by
    simpa [targetZeroPowerAmplitude] using hclosedNegligible
  have hclosed :
      Tendsto
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ))
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using
      hclosedAbs.comp tendsto_natCast_atTop_atTop
  have hremainderNegligible := hremainder.negligible
  unfold NaturalPointTargetAmplitudeNegligible at hremainderNegligible
  have hremainderAbs :
      Tendsto
        (fun m : ℕ =>
          |actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)|)
        atTop (nhds 0) := by
    simpa [targetZeroPowerAmplitude] using hremainderNegligible
  have hremainderTendsto :
      Tendsto
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ))
        atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [Real.norm_eq_abs] using hremainderAbs
  have htotal :
      Tendsto
        (fun m : ℕ =>
          (dynamicFinitePNTZeroSum H (m : ℝ)).re +
            (actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)))
        atTop (nhds 0) := by
    simpa using hfinite.add (hclosed.add hremainderTendsto)
  apply htotal.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_dynamicFinite_add_closed_add_remainder
    H (m : ℝ)]

end PrimeNumberTheorem
