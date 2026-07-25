import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualFiniteStrips

/-!
# From the positive zeta tail to the full finite zero tail

Complex conjugation identifies the negative-ordinate relative PNT zero sum
with the conjugate of the positive-ordinate sum.  The full finite zero tail is
therefore bounded by twice the positive-tail norm plus the real-ordinate
residual.

The real-ordinate residual remains explicit.  Carlson's positive-height count
does not control it.
-/

open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem

open Filter
open Complex

/-- Norm of the complete multiplicity-weighted relative PNT finite zero sum at
a dynamic height. -/
noncomputable def dynamicFullPNTZeroTailNorm
    (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  ‖∑ rho ∈ nontrivialZerosFinset (T x),
      pntRelativeZeroContribution x rho‖

/-- Norm of the real-ordinate residual in the finite zero sum. -/
noncomputable def dynamicRealOrdinatePNTZeroTailNorm
    (T : ℝ → ℝ) (x : ℝ) : ℝ :=
  ‖∑ rho ∈ realOrdinateNontrivialZerosFinset (T x),
      pntRelativeZeroContribution x rho‖

/-- The full finite zero tail is bounded by twice its positive-ordinate part
plus the real-ordinate residual. -/
theorem dynamicFullPNTZeroTailNorm_le_two_positive_add_real
    {T : ℝ → ℝ} {x : ℝ} (hx : 0 < x) :
    dynamicFullPNTZeroTailNorm T x ≤
      dynamicPositivePNTTailNorm T x +
        dynamicPositivePNTTailNorm T x +
          dynamicRealOrdinatePNTZeroTailNorm T x := by
  let positiveSum :=
    ∑ rho ∈ positiveNontrivialZerosFinset (T x),
      pntRelativeZeroContribution x rho
  let negativeSum :=
    ∑ rho ∈ negativeNontrivialZerosFinset (T x),
      pntRelativeZeroContribution x rho
  let realSum :=
    ∑ rho ∈ realOrdinateNontrivialZerosFinset (T x),
      pntRelativeZeroContribution x rho
  have hdecomp :
      (∑ rho ∈ nontrivialZerosFinset (T x),
          pntRelativeZeroContribution x rho) =
        positiveSum + negativeSum + realSum :=
    finiteZeroSum_eq_positive_add_negative_add_real (T x)
      (pntRelativeZeroContribution x)
  have hnegative : negativeSum = conj positiveSum := by
    apply sum_negative_eq_conj_sum_positive
    intro rho hrho
    exact pntRelativeZeroContribution_conj hx
      (mem_nontrivialZerosFinset.mp hrho).1
  rw [dynamicFullPNTZeroTailNorm, hdecomp]
  calc
    ‖positiveSum + negativeSum + realSum‖ ≤
        ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
      calc
        ‖positiveSum + negativeSum + realSum‖ ≤
            ‖positiveSum + negativeSum‖ + ‖realSum‖ :=
          norm_add_le _ _
        _ ≤ ‖positiveSum‖ + ‖negativeSum‖ + ‖realSum‖ := by
          gcongr
          exact norm_add_le _ _
    _ = dynamicPositivePNTTailNorm T x +
          dynamicPositivePNTTailNorm T x +
            dynamicRealOrdinatePNTZeroTailNorm T x := by
      rw [hnegative, norm_conj]
      rfl

/-- Target-normalized control of the positive tail and real-ordinate residual
implies target-normalized control of the full finite zero tail. -/
theorem dynamicFullPNTZeroTailNorm_targetAmplitudeNegligible
    {T amplitude : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (hpositive :
      TargetAmplitudeNegligible amplitude
        (dynamicPositivePNTTailNorm T))
    (hreal :
      TargetAmplitudeNegligible amplitude
        (dynamicRealOrdinatePNTZeroTailNorm T)) :
    TargetAmplitudeNegligible amplitude
      (dynamicFullPNTZeroTailNorm T) := by
  have hmajorant :
      TargetAmplitudeNegligible amplitude
        (fun x =>
          dynamicPositivePNTTailNorm T x +
            dynamicPositivePNTTailNorm T x +
              dynamicRealOrdinatePNTZeroTailNorm T x) :=
    (hpositive.add hamplitude hpositive).add hamplitude hreal
  unfold TargetAmplitudeNegligible at hmajorant ⊢
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards [hamplitude] with x hx
    exact div_nonneg (abs_nonneg _) hx.le
  · filter_upwards [hamplitude,
      eventually_gt_atTop (0 : ℝ)] with x hxAmplitude hx
    have hfull :=
      dynamicFullPNTZeroTailNorm_le_two_positive_add_real
        (T := T) hx
    have hfullNonneg :
        0 ≤ dynamicFullPNTZeroTailNorm T x :=
      norm_nonneg _
    have hmajorantNonneg :
        0 ≤ dynamicPositivePNTTailNorm T x +
            dynamicPositivePNTTailNorm T x +
              dynamicRealOrdinatePNTZeroTailNorm T x := by
      exact add_nonneg
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (norm_nonneg _)
    rw [abs_of_nonneg hfullNonneg,
      abs_of_nonneg hmajorantNonneg]
    exact div_le_div_of_nonneg_right hfull hxAmplitude.le

end PrimeNumberTheorem
