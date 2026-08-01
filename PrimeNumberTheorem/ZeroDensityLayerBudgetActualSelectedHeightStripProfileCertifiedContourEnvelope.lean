import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripProfileCertifiedCostOptimality
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay

/-!
# Certified contour-envelope optimality

This module instantiates the abstract certified cost comparison with the
project's actual selected-polynomial contour majorant.  After division by the
target zero amplitude, its profile-dependent power is exactly the robust
decay factor at the balanced exponent.  The depth-one tail is independent of
the profile.
-/

namespace PrimeNumberTheorem

open scoped Real

namespace ActualSelectedHeightFiniteStripProfile

theorem balancedExponent_sub_contourTransition_eq_optimalRobustMargin
    (beta : ℝ)
    (profile : ActualSelectedHeightFiniteStripProfile) :
    profile.balancedExponent beta - (1 - beta) =
      profile.optimalRobustMargin beta := by
  rw [optimalRobustMargin_eq_half_ceiling_gap]
  change
    ((1 - beta + profile.effectiveAlphaCeiling beta) / 2) - (1 - beta) =
      (profile.effectiveAlphaCeiling beta - (1 - beta)) / 2
  ring

/-- The actual normalized contour majorant evaluated at a profile's balanced
polynomial height. -/
noncomputable def selectedBalancedContourNormalizedCost
    (C beta : ℝ)
    (m : ℕ)
    (profile : ActualSelectedHeightFiniteStripProfile) : ℝ :=
  selectedPolynomialNaturalContourMajorant C (profile.balancedExponent beta) m /
    targetZeroPowerAmplitude beta (m : ℝ)

end ActualSelectedHeightFiniteStripProfile

/-- Exact target-normalized two-power decomposition of the selected contour
majorant. -/
theorem selectedPolynomialNaturalContourMajorant_div_targetZeroPowerAmplitude
    {C beta alpha : ℝ}
    {m : ℕ}
    (hm : 1 ≤ m) :
    selectedPolynomialNaturalContourMajorant C alpha m /
        targetZeroPowerAmplitude beta (m : ℝ) =
      actualPolynomialRemainderTargetMajorant (10 * C) beta alpha (m : ℝ) +
        actualPolynomialRemainderTargetMajorant
          (2 * cofinalPNTZeroDepthTailConstant) beta 1 (m : ℝ) := by
  have hxpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hm)
  unfold selectedPolynomialNaturalContourMajorant
    actualPolynomialRemainderTargetMajorant targetZeroPowerAmplitude
  rw [add_div]
  have hpowAlpha :
      (m : ℝ) ^ (-alpha) * (m : ℝ) ^ (-(beta - 1)) =
        (m : ℝ) ^ (1 - beta - alpha) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  have hpowOne :
      (m : ℝ) ^ (-1 : ℝ) * (m : ℝ) ^ (-(beta - 1)) =
        (m : ℝ) ^ (1 - beta - 1) := by
    rw [← Real.rpow_add hxpos]
    congr 1
    ring
  congr 1
  · rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le, ← hpowAlpha]
    ring
  · rw [div_eq_mul_inv, ← Real.rpow_neg hxpos.le, ← hpowOne]
    ring

namespace ActualSelectedHeightFiniteStripProfile

theorem actualPolynomialRemainderTargetMajorant_balancedExponent_eq
    (C beta x : ℝ)
    (profile : ActualSelectedHeightFiniteStripProfile) :
    actualPolynomialRemainderTargetMajorant
        (10 * C) beta (profile.balancedExponent beta) x =
      (10 * C * (1 + Real.log x) ^ 2) *
        profile.robustDecayFactor beta x := by
  have hexponent :
      1 - beta - profile.balancedExponent beta =
        -profile.optimalRobustMargin beta := by
    rw [← profile.balancedExponent_sub_contourTransition_eq_optimalRobustMargin beta]
    ring
  unfold actualPolynomialRemainderTargetMajorant robustDecayFactor
  rw [hexponent]
  ring

theorem selectedBalancedContourNormalizedCost_eq_weightedRobustDecayEnvelope
    {C beta : ℝ}
    {m : ℕ}
    (profile : ActualSelectedHeightFiniteStripProfile)
    (hm : 1 ≤ m) :
    selectedBalancedContourNormalizedCost C beta m profile =
      profile.weightedRobustDecayEnvelope beta (m : ℝ)
        (10 * C * (1 + Real.log (m : ℝ)) ^ 2)
        (actualPolynomialRemainderTargetMajorant
          (2 * cofinalPNTZeroDepthTailConstant) beta 1 (m : ℝ)) := by
  unfold selectedBalancedContourNormalizedCost
  rw [selectedPolynomialNaturalContourMajorant_div_targetZeroPowerAmplitude hm]
  unfold weightedRobustDecayEnvelope
  rw [actualPolynomialRemainderTargetMajorant_balancedExponent_eq]

theorem selectedBalancedContourNormalizedCost_robustMarginAntitoneCost
    {C beta : ℝ}
    {m : ℕ}
    (hC : 0 ≤ C)
    (hm : 1 ≤ m) :
    RobustMarginAntitoneCost beta
      (selectedBalancedContourNormalizedCost C beta m) := by
  intro profile candidate hmargin
  rw [profile.selectedBalancedContourNormalizedCost_eq_weightedRobustDecayEnvelope hm]
  rw [candidate.selectedBalancedContourNormalizedCost_eq_weightedRobustDecayEnvelope hm]
  apply weightedRobustDecayEnvelope_robustMarginAntitoneCost
    (beta := beta) (x := (m : ℝ))
  · exact_mod_cast hm
  · exact mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg _)
  · exact hmargin

/-- The certificate-aware robust-margin optimizer genuinely minimizes the
actual target-normalized selected contour majorant among certified profiles. -/
theorem optimalRobustMargin_minimizes_selectedBalancedContourNormalizedCost
    {C beta : ℝ}
    {m : ℕ}
    {selection : UniformNaturalPointGoodHeightSelection}
    {S : Finset ℂ}
    {candidates : Finset ActualSelectedHeightFiniteStripProfile}
    {chosen : ActualSelectedHeightFiniteStripProfile}
    (hC : 0 ≤ C)
    (hm : 1 ≤ m)
    (hoptimal :
      ∀ profile ∈ candidates,
        profile.HasAnalyticTransferCertificate beta selection S →
          profile.optimalRobustMargin beta ≤ chosen.optimalRobustMargin beta) :
    ∀ profile ∈ candidates,
      profile.HasAnalyticTransferCertificate beta selection S →
        selectedBalancedContourNormalizedCost C beta m chosen ≤
          selectedBalancedContourNormalizedCost C beta m profile := by
  exact optimalRobustMargin_minimizes_antitoneCost hoptimal
    (selectedBalancedContourNormalizedCost_robustMarginAntitoneCost hC hm)

end ActualSelectedHeightFiniteStripProfile

end PrimeNumberTheorem
