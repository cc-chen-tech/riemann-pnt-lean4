import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailConjugation

/-!
# Actual two-height finite-zero tail control

A split-height explicit formula has an inner finite zero tail and the annulus
created by enlarging the truncation height.  This file defines the actual
multiplicity-weighted annulus as the norm of the difference of the two finite
zero sums.

The resulting `TwoHeightTargetComplementControl` is a control by nonnegative
norm budgets.  It does not assert that the real-valued budget equals the
underlying complex explicit-formula remainder.
-/

open scoped BigOperators

namespace PrimeNumberTheorem

open Filter

/-- The multiplicity-weighted relative PNT finite zero sum at a dynamic
height, before taking its norm. -/
noncomputable def dynamicFullPNTZeroTailSum
    (T : ℝ → ℝ) (x : ℝ) : ℂ :=
  ∑ rho ∈ nontrivialZerosFinset (T x),
    pntRelativeZeroContribution x rho

/-- Norm of the actual finite-zero annulus between two dynamic heights. -/
noncomputable def dynamicPNTZeroHeightAnnulusNorm
    (innerHeight outerHeight : ℝ → ℝ) (x : ℝ) : ℝ :=
  ‖dynamicFullPNTZeroTailSum outerHeight x -
      dynamicFullPNTZeroTailSum innerHeight x‖

/-- The actual annulus norm is bounded by the sum of the two complete finite
tail norms.  No ordering relation between the heights is needed for this
structural inequality. -/
theorem dynamicPNTZeroHeightAnnulusNorm_le_fullTail_add_fullTail
    (innerHeight outerHeight : ℝ → ℝ) (x : ℝ) :
    dynamicPNTZeroHeightAnnulusNorm innerHeight outerHeight x ≤
      dynamicFullPNTZeroTailNorm outerHeight x +
        dynamicFullPNTZeroTailNorm innerHeight x := by
  unfold dynamicPNTZeroHeightAnnulusNorm
    dynamicFullPNTZeroTailSum dynamicFullPNTZeroTailNorm
  exact norm_sub_le _ _

/-- If the finite zero tails at both dynamic heights are negligible relative
to the target amplitude, then their actual difference annulus is negligible. -/
theorem dynamicPNTZeroHeightAnnulusNorm_targetAmplitudeNegligible
    {amplitude innerHeight outerHeight : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (hinner :
      TargetAmplitudeNegligible amplitude
        (dynamicFullPNTZeroTailNorm innerHeight))
    (houter :
      TargetAmplitudeNegligible amplitude
        (dynamicFullPNTZeroTailNorm outerHeight)) :
    TargetAmplitudeNegligible amplitude
      (dynamicPNTZeroHeightAnnulusNorm innerHeight outerHeight) := by
  have hmajorant :
      TargetAmplitudeNegligible amplitude
        (fun x =>
          dynamicFullPNTZeroTailNorm outerHeight x +
            dynamicFullPNTZeroTailNorm innerHeight x) :=
    houter.add hamplitude hinner
  unfold TargetAmplitudeNegligible at hmajorant ⊢
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards [hamplitude] with x hx
    exact div_nonneg (abs_nonneg _) hx.le
  · filter_upwards [hamplitude] with x hx
    have hannulus :=
      dynamicPNTZeroHeightAnnulusNorm_le_fullTail_add_fullTail
        innerHeight outerHeight x
    have hannulusNonneg :
        0 ≤ dynamicPNTZeroHeightAnnulusNorm
          innerHeight outerHeight x :=
      norm_nonneg _
    have hmajorantNonneg :
        0 ≤ dynamicFullPNTZeroTailNorm outerHeight x +
            dynamicFullPNTZeroTailNorm innerHeight x :=
      add_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [abs_of_nonneg hannulusNonneg,
      abs_of_nonneg hmajorantNonneg]
    exact div_le_div_of_nonneg_right hannulus hx.le

/-- Actual two-height finite-zero norm budgets form the abstract complementary
control expected by the unified transfer layer. -/
theorem actualTwoHeightPNTZeroTailControl
    {amplitude innerHeight outerHeight : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (hinner :
      TargetAmplitudeNegligible amplitude
        (dynamicFullPNTZeroTailNorm innerHeight))
    (houter :
      TargetAmplitudeNegligible amplitude
        (dynamicFullPNTZeroTailNorm outerHeight)) :
    TwoHeightTargetComplementControl amplitude
      (dynamicFullPNTZeroTailNorm innerHeight)
      (dynamicPNTZeroHeightAnnulusNorm innerHeight outerHeight) where
  amplitude_eventually_pos := hamplitude
  inner_negligible := hinner
  annulus_negligible :=
    dynamicPNTZeroHeightAnnulusNorm_targetAmplitudeNegligible
      hamplitude hinner houter

/-- The actual inner-tail plus annulus norm budget is negligible after
target-amplitude normalization. -/
theorem actualTwoHeightPNTZeroTail_combined_targetAmplitudeNegligible
    {amplitude innerHeight outerHeight : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in Filter.atTop, 0 < amplitude x)
    (hinner :
      TargetAmplitudeNegligible amplitude
        (dynamicFullPNTZeroTailNorm innerHeight))
    (houter :
      TargetAmplitudeNegligible amplitude
        (dynamicFullPNTZeroTailNorm outerHeight)) :
    TargetAmplitudeNegligible amplitude
      (twoHeightComplement
        (dynamicFullPNTZeroTailNorm innerHeight)
        (dynamicPNTZeroHeightAnnulusNorm
          innerHeight outerHeight)) :=
  (actualTwoHeightPNTZeroTailControl
    hamplitude hinner houter).combined_negligible

end PrimeNumberTheorem
