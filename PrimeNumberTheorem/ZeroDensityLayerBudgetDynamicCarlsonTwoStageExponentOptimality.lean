import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonAutomaticBetaOptimality
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponentUniqueness

/-!
# Two-stage optimality of the dynamic Carlson exponent pair

There are two distinct maximin choices in the dynamic transfer:

1. choose the PNT target exponent midway between the joint actual-zero
   bottleneck and `1`;
2. at that target exponent, choose the polynomial height exponent which
   maximizes the common physical margin of the contour and all Carlson strips.

This module packages those choices as a lexicographic certificate and proves
that the resulting pair is unique.  The statement is an exponent-optimization
result; it does not assert inhabitation of the complete all-Carlson zero
bucket input.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- The weighted balanced height exponent evaluated at the automatic PNT
target exponent. -/
def dynamicCarlsonAutomaticWeightedHeightExponent
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  actualSelectedHeightFiniteStripWeightedBalancedExponent
    (dynamicCarlsonAutomaticTargetBeta sigma tau) sigma tau

/-- Lexicographic two-stage optimality certificate for a target exponent and
a polynomial truncation-height exponent. -/
structure DynamicCarlsonTwoStageExponentCertificate
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (beta alpha : ℝ) : Prop where
  beta_maximizes :
    ∀ candidate,
      dynamicCarlsonAutomaticTargetBetaRobustMargin
          sigma tau candidate ≤
        dynamicCarlsonAutomaticTargetBetaRobustMargin
          sigma tau beta
  height_attains_optimal_margin :
    ActualSelectedHeightFiniteStripPhysicalMarginCertificate
      beta sigma tau alpha
      (actualSelectedHeightFiniteStripOptimalPhysicalMargin
        beta sigma tau)

/-- The explicit automatic target exponent and weighted balanced height
exponent satisfy the two-stage optimality certificate. -/
theorem dynamicCarlsonAutomaticExponentPair_certificate
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    DynamicCarlsonTwoStageExponentCertificate sigma tau
      (dynamicCarlsonAutomaticTargetBeta sigma tau)
      (dynamicCarlsonAutomaticWeightedHeightExponent sigma tau) := by
  constructor
  · intro candidate
    exact
      dynamicCarlsonAutomaticTargetBeta_maximizes_robustMargin
        sigma tau candidate
  · exact
      actualSelectedHeightFiniteStripWeightedBalancedExponent_marginCertificate
        sigma tau hsigma hsigmaOne

/-- Any two-stage optimal pair is the explicit automatic target exponent and
weighted balanced height exponent. -/
theorem dynamicCarlsonAutomaticExponentPair_unique
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    {beta alpha : ℝ}
    (certificate :
      DynamicCarlsonTwoStageExponentCertificate
        sigma tau beta alpha) :
    beta = dynamicCarlsonAutomaticTargetBeta sigma tau ∧
      alpha =
        dynamicCarlsonAutomaticWeightedHeightExponent sigma tau := by
  have hbeta :
      beta = dynamicCarlsonAutomaticTargetBeta sigma tau :=
    dynamicCarlsonAutomaticTargetBeta_unique_maximizer
      sigma tau beta
      (certificate.beta_maximizes
        (dynamicCarlsonAutomaticTargetBeta sigma tau))
  subst beta
  refine ⟨rfl, ?_⟩
  exact
    actualSelectedHeightFiniteStripWeightedBalancedExponent_unique
      sigma tau hsigma hsigmaOne
      certificate.height_attains_optimal_margin

/-- Under the endpoint hypotheses, both stages of the explicit exponent pair
have strictly positive certified margin. -/
theorem dynamicCarlsonAutomaticExponentPair_margins_pos
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1) :
    0 <
        dynamicCarlsonAutomaticTargetBetaRobustMargin sigma tau
          (dynamicCarlsonAutomaticTargetBeta sigma tau) ∧
      0 <
        actualSelectedHeightFiniteStripOptimalPhysicalMargin
          (dynamicCarlsonAutomaticTargetBeta sigma tau)
          sigma tau := by
  constructor
  · exact
      dynamicCarlsonAutomaticTargetBeta_robustMargin_pos
        sigma tau hthresholdOne
  · exact
      actualSelectedHeightFiniteStripOptimalPhysicalMargin_pos
        sigma tau hsigma hsigmaOne
        (carlsonStripEndpointTargetThreshold_lt_automaticTargetBeta
          sigma tau hthresholdOne)

end PrimeNumberTheorem
