import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightBalancedExponent

/-!
# Maximin optimality of the balanced selected-height exponent

The explicit balanced exponent is not asserted to optimize every analytic
error budget.  It has a precise robust optimality property: it uniquely
maximizes the minimum distance to the contour lower transition and the
effective Carlson upper ceiling.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- Midpoint of a lower and upper exponent boundary. -/
def selectedHeightExponentMidpoint
    (lower upper : ℝ) : ℝ :=
  (lower + upper) / 2

/-- Two-sided safety margin of an exponent between a lower and upper
boundary. -/
def selectedHeightExponentRobustMargin
    (lower upper alpha : ℝ) : ℝ :=
  min (alpha - lower) (upper - alpha)

/-- The midpoint has equal margins and realizes half of the total gap. -/
theorem selectedHeightExponentRobustMargin_midpoint
    (lower upper : ℝ) :
    selectedHeightExponentRobustMargin lower upper
        (selectedHeightExponentMidpoint lower upper) =
      (upper - lower) / 2 := by
  have hleft :
      selectedHeightExponentMidpoint lower upper - lower =
        (upper - lower) / 2 := by
    simp [selectedHeightExponentMidpoint]
    ring
  have hright :
      upper - selectedHeightExponentMidpoint lower upper =
        (upper - lower) / 2 := by
    simp [selectedHeightExponentMidpoint]
    ring
  simp [selectedHeightExponentRobustMargin, hleft, hright]

/-- No exponent has two-sided safety margin larger than half the total gap. -/
theorem selectedHeightExponentRobustMargin_le_half_gap
    (lower upper alpha : ℝ) :
    selectedHeightExponentRobustMargin lower upper alpha ≤
      (upper - lower) / 2 := by
  by_cases hleft :
      alpha ≤ selectedHeightExponentMidpoint lower upper
  · calc
      selectedHeightExponentRobustMargin lower upper alpha ≤
          alpha - lower :=
        min_le_left _ _
      _ ≤ (upper - lower) / 2 := by
        dsimp [selectedHeightExponentMidpoint] at hleft
        linarith
  · have hright :
        selectedHeightExponentMidpoint lower upper < alpha :=
      lt_of_not_ge hleft
    calc
      selectedHeightExponentRobustMargin lower upper alpha ≤
          upper - alpha :=
        min_le_right _ _
      _ ≤ (upper - lower) / 2 := by
        dsimp [selectedHeightExponentMidpoint] at hright
        linarith

/-- The midpoint maximizes the two-sided safety margin. -/
theorem selectedHeightExponentMidpoint_maximizes_robustMargin
    (lower upper alpha : ℝ) :
    selectedHeightExponentRobustMargin lower upper alpha ≤
      selectedHeightExponentRobustMargin lower upper
        (selectedHeightExponentMidpoint lower upper) := by
  rw [selectedHeightExponentRobustMargin_midpoint]
  exact
    selectedHeightExponentRobustMargin_le_half_gap
      lower upper alpha

/-- The midpoint is the unique maximizer of the two-sided safety margin. -/
theorem selectedHeightExponentMidpoint_unique_maximizer
    (lower upper alpha : ℝ)
    (hoptimal :
      selectedHeightExponentRobustMargin lower upper
          (selectedHeightExponentMidpoint lower upper) ≤
        selectedHeightExponentRobustMargin lower upper alpha) :
    alpha = selectedHeightExponentMidpoint lower upper := by
  have hleft :
      selectedHeightExponentRobustMargin lower upper
          (selectedHeightExponentMidpoint lower upper) ≤
        alpha - lower :=
    hoptimal.trans (min_le_left _ _)
  have hright :
      selectedHeightExponentRobustMargin lower upper
          (selectedHeightExponentMidpoint lower upper) ≤
        upper - alpha :=
    hoptimal.trans (min_le_right _ _)
  rw [selectedHeightExponentRobustMargin_midpoint] at hleft hright
  dsimp [selectedHeightExponentMidpoint]
  linarith

/-- Effective common upper boundary used by the balanced finite-strip
exponent. -/
noncomputable def actualSelectedHeightFiniteStripEffectiveAlphaCeiling
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  min 1 (actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau)

/-- Robustness objective for a finite Carlson strip exponent. -/
noncomputable def actualSelectedHeightFiniteStripRobustMargin
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ)
    (alpha : ℝ) : ℝ :=
  selectedHeightExponentRobustMargin
    (1 - beta)
    (actualSelectedHeightFiniteStripEffectiveAlphaCeiling beta sigma tau)
    alpha

/-- The explicit balanced exponent is exactly the midpoint used by the finite
strip robustness objective. -/
theorem actualSelectedHeightFiniteStripBalancedExponent_eq_midpoint
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ) :
    actualSelectedHeightFiniteStripBalancedExponent beta sigma tau =
      selectedHeightExponentMidpoint
        (1 - beta)
        (actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta sigma tau) := by
  rfl

/-- Exact optimal robustness value of the explicit balanced exponent. -/
theorem actualSelectedHeightFiniteStripBalancedExponent_robustMargin
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ) :
    actualSelectedHeightFiniteStripRobustMargin beta sigma tau
        (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau) =
      (actualSelectedHeightFiniteStripEffectiveAlphaCeiling beta sigma tau -
        (1 - beta)) / 2 := by
  rw [actualSelectedHeightFiniteStripBalancedExponent_eq_midpoint]
  exact
    selectedHeightExponentRobustMargin_midpoint
      (1 - beta)
      (actualSelectedHeightFiniteStripEffectiveAlphaCeiling
        beta sigma tau)

/-- The explicit balanced exponent maximizes finite-strip robustness over all
real exponents. -/
theorem actualSelectedHeightFiniteStripBalancedExponent_maximizes
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ)
    (alpha : ℝ) :
    actualSelectedHeightFiniteStripRobustMargin beta sigma tau alpha ≤
      actualSelectedHeightFiniteStripRobustMargin beta sigma tau
        (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau) := by
  rw [actualSelectedHeightFiniteStripBalancedExponent_eq_midpoint]
  exact
    selectedHeightExponentMidpoint_maximizes_robustMargin
      (1 - beta)
      (actualSelectedHeightFiniteStripEffectiveAlphaCeiling
        beta sigma tau)
      alpha

/-- The explicit balanced exponent is the unique maximizer of finite-strip
robustness. -/
theorem actualSelectedHeightFiniteStripBalancedExponent_unique_maximizer
    {n : ℕ} (beta : ℝ) (sigma tau : Fin (n + 1) → ℝ)
    (alpha : ℝ)
    (hoptimal :
      actualSelectedHeightFiniteStripRobustMargin beta sigma tau
          (actualSelectedHeightFiniteStripBalancedExponent beta sigma tau) ≤
        actualSelectedHeightFiniteStripRobustMargin
          beta sigma tau alpha) :
    alpha =
      actualSelectedHeightFiniteStripBalancedExponent beta sigma tau := by
  rw [actualSelectedHeightFiniteStripBalancedExponent_eq_midpoint] at hoptimal ⊢
  exact
    selectedHeightExponentMidpoint_unique_maximizer
      (1 - beta)
      (actualSelectedHeightFiniteStripEffectiveAlphaCeiling
        beta sigma tau)
      alpha hoptimal

/-- Under the endpoint-threshold hypotheses, the optimal robustness margin is
strictly positive. -/
theorem actualSelectedHeightFiniteStripBalancedExponent_robustMargin_pos
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbeta : 0 < beta)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) :
    0 <
      actualSelectedHeightFiniteStripRobustMargin beta sigma tau
        (actualSelectedHeightFiniteStripBalancedExponent
          beta sigma tau) := by
  have hfinite :
      1 - beta <
        actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau :=
    (contourTransition_lt_finiteStripAlphaCeiling_iff
      sigma tau hsigma hsigmaOne).2 hthreshold
  have hone : 1 - beta < 1 := by linarith
  have heffective :
      1 - beta <
        actualSelectedHeightFiniteStripEffectiveAlphaCeiling
          beta sigma tau := by
    exact lt_min hone hfinite
  rw [actualSelectedHeightFiniteStripBalancedExponent_robustMargin]
  linarith

end PrimeNumberTheorem
