import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonAutomaticBetaPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightBalancedExponentOptimality

/-!
# Optimality of the automatic dynamic-Carlson PNT target exponent

The automatic target exponent is the midpoint between the complete actual-PNT
bottleneck and `1`.  Hence it uniquely maximizes the smaller of:

* its separation from every finite-strip and real-ordinate zero obstruction;
* its remaining distance to the PNT boundary `1`.

This is a precise maximin certificate.  It does not assert that the midpoint
optimizes every analytic error term or every possible height selection.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- The two-sided safety margin for a candidate PNT target exponent. -/
def dynamicCarlsonAutomaticTargetBetaRobustMargin
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) (beta : ℝ) : ℝ :=
  selectedHeightExponentRobustMargin
    (dynamicCarlsonActualPNTBottleneck sigma tau) 1 beta

/-- The automatic target exponent is exactly the midpoint of the admissible
interval determined by the joint actual-PNT bottleneck. -/
theorem dynamicCarlsonAutomaticTargetBeta_eq_midpoint
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) :
    dynamicCarlsonAutomaticTargetBeta sigma tau =
      selectedHeightExponentMidpoint
        (dynamicCarlsonActualPNTBottleneck sigma tau) 1 := by
  rfl

/-- Exact robust margin attained by the automatic target exponent. -/
theorem dynamicCarlsonAutomaticTargetBeta_robustMargin
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) :
    dynamicCarlsonAutomaticTargetBetaRobustMargin sigma tau
        (dynamicCarlsonAutomaticTargetBeta sigma tau) =
      (1 - dynamicCarlsonActualPNTBottleneck sigma tau) / 2 := by
  rw [dynamicCarlsonAutomaticTargetBeta_eq_midpoint]
  exact
    selectedHeightExponentRobustMargin_midpoint
      (dynamicCarlsonActualPNTBottleneck sigma tau) 1

/-- The automatic target exponent maximizes the joint two-sided safety margin
over every real candidate exponent. -/
theorem dynamicCarlsonAutomaticTargetBeta_maximizes_robustMargin
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) (beta : ℝ) :
    dynamicCarlsonAutomaticTargetBetaRobustMargin sigma tau beta ≤
      dynamicCarlsonAutomaticTargetBetaRobustMargin sigma tau
        (dynamicCarlsonAutomaticTargetBeta sigma tau) := by
  rw [dynamicCarlsonAutomaticTargetBeta_eq_midpoint]
  exact
    selectedHeightExponentMidpoint_maximizes_robustMargin
      (dynamicCarlsonActualPNTBottleneck sigma tau) 1 beta

/-- The automatic target exponent is the unique maximizer of the joint
two-sided safety margin. -/
theorem dynamicCarlsonAutomaticTargetBeta_unique_maximizer
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) (beta : ℝ)
    (hoptimal :
      dynamicCarlsonAutomaticTargetBetaRobustMargin sigma tau
          (dynamicCarlsonAutomaticTargetBeta sigma tau) ≤
        dynamicCarlsonAutomaticTargetBetaRobustMargin sigma tau beta) :
    beta = dynamicCarlsonAutomaticTargetBeta sigma tau := by
  rw [dynamicCarlsonAutomaticTargetBeta_eq_midpoint] at hoptimal ⊢
  exact
    selectedHeightExponentMidpoint_unique_maximizer
      (dynamicCarlsonActualPNTBottleneck sigma tau) 1 beta hoptimal

/-- Under the strip endpoint hypotheses, the optimal joint safety margin is
strictly positive. -/
theorem dynamicCarlsonAutomaticTargetBeta_robustMargin_pos
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1) :
    0 <
      dynamicCarlsonAutomaticTargetBetaRobustMargin sigma tau
        (dynamicCarlsonAutomaticTargetBeta sigma tau) := by
  rw [dynamicCarlsonAutomaticTargetBeta_robustMargin]
  have hbottleneck :
      dynamicCarlsonActualPNTBottleneck sigma tau < 1 :=
    dynamicCarlsonActualPNTBottleneck_lt_one
      sigma tau hthresholdOne
  linarith

end PrimeNumberTheorem
