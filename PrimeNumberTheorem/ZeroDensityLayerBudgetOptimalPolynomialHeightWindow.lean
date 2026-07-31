import PrimeNumberTheorem.ZeroDensityLayerBudgetCanonicalPolynomialSigmaOnlyUnifiedUpperSignedOmega

/-!
# Minimax-optimal polynomial-height window

The feasible exponent width is allocated among four independent strict
margins: contour decay, selected-height separation, logarithmic slack, and
the final density exponent. Their common margin is at most one quarter of the
total width, and an explicit quarter-balanced construction attains this bound.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Optimal common safety margin. -/
noncomputable def optimalPolynomialHeightSafetyMargin
    (beta sigma : ℝ) : ℝ :=
  canonicalPolynomialHeightGap beta sigma / 4

/-- Inner selected-height exponent in the quarter-balanced window. -/
noncomputable def optimalPolynomialHeightInnerExponent
    (beta sigma : ℝ) : ℝ :=
  1 - beta + optimalPolynomialHeightSafetyMargin beta sigma

/-- Outer density exponent in the quarter-balanced window. -/
noncomputable def optimalPolynomialHeightOuterExponent
    (beta sigma : ℝ) : ℝ :=
  1 - beta + 2 * optimalPolynomialHeightSafetyMargin beta sigma

/-- Logarithmic slack in the quarter-balanced window. -/
noncomputable def optimalPolynomialHeightEpsilon
    (beta sigma : ℝ) : ℝ :=
  optimalPolynomialHeightSafetyMargin beta sigma

/-- No feasible allocation can give all four independent margins a common
value larger than one quarter of the available exponent width. -/
theorem polynomialHeightCommonSafetyMargin_le_optimal
    {beta sigma inner outer epsilon margin : ℝ}
    (hcontour : 1 - beta + margin ≤ inner)
    (hwindow : inner + margin ≤ outer)
    (hlog : margin ≤ epsilon)
    (hdensity : outer + epsilon + margin ≤ beta - sigma) :
    margin ≤ optimalPolynomialHeightSafetyMargin beta sigma := by
  unfold optimalPolynomialHeightSafetyMargin canonicalPolynomialHeightGap
  linarith

/-- The quarter-balanced construction makes all four safety margins exactly
equal to the optimal value. -/
theorem optimalPolynomialHeightWindow_equalMargins
    (beta sigma : ℝ) :
    1 - beta + optimalPolynomialHeightSafetyMargin beta sigma =
        optimalPolynomialHeightInnerExponent beta sigma ∧
    optimalPolynomialHeightInnerExponent beta sigma +
        optimalPolynomialHeightSafetyMargin beta sigma =
      optimalPolynomialHeightOuterExponent beta sigma ∧
    optimalPolynomialHeightSafetyMargin beta sigma =
      optimalPolynomialHeightEpsilon beta sigma ∧
    optimalPolynomialHeightOuterExponent beta sigma +
        optimalPolynomialHeightEpsilon beta sigma +
        optimalPolynomialHeightSafetyMargin beta sigma = beta - sigma := by
  unfold optimalPolynomialHeightInnerExponent
    optimalPolynomialHeightOuterExponent
    optimalPolynomialHeightEpsilon
    optimalPolynomialHeightSafetyMargin
    canonicalPolynomialHeightGap
  constructor
  · rfl
  constructor
  · ring
  constructor
  · rfl
  · ring

/-- Complete feasible-window specification of the minimax-optimal allocation. -/
theorem optimalPolynomialHeightWindow_spec
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hbeta : (1 + sigma) / 2 < beta) (hbetaOne : beta < 1) :
    0 < optimalPolynomialHeightSafetyMargin beta sigma ∧
    0 < optimalPolynomialHeightInnerExponent beta sigma ∧
    optimalPolynomialHeightInnerExponent beta sigma <
      optimalPolynomialHeightOuterExponent beta sigma ∧
    1 - beta < optimalPolynomialHeightInnerExponent beta sigma ∧
    optimalPolynomialHeightOuterExponent beta sigma < beta - sigma ∧
    optimalPolynomialHeightInnerExponent beta sigma ≤ 1 ∧
    0 < optimalPolynomialHeightEpsilon beta sigma ∧
    sigma - beta + optimalPolynomialHeightOuterExponent beta sigma +
        optimalPolynomialHeightEpsilon beta sigma < 0 := by
  unfold optimalPolynomialHeightInnerExponent
    optimalPolynomialHeightOuterExponent
    optimalPolynomialHeightEpsilon
    optimalPolynomialHeightSafetyMargin
    canonicalPolynomialHeightGap
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The minimax-optimal inner selected height is eventually below its outer
polynomial height, is cofinal, and carries the actual power-scale remainder
certificate. -/
theorem optimalPolynomialSelectedHeight_spec
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hbeta : (1 + sigma) / 2 < beta) (hbetaOne : beta < 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ m : ℕ in atTop,
      selectedUniformGoodHeight
          (optimalPolynomialHeightInnerExponent beta sigma)
          selection (m : ℝ) ≤
        carlsonPolynomialHeight
          (optimalPolynomialHeightOuterExponent beta sigma) (m : ℝ)) ∧
    Tendsto
      (fun m : ℕ =>
        selectedUniformGoodHeight
          (optimalPolynomialHeightInnerExponent beta sigma)
          selection (m : ℝ))
      atTop atTop ∧
    ActualSelectedHeightNaturalPointRemainderCertificate beta
      (selectedUniformGoodHeight
        (optimalPolynomialHeightInnerExponent beta sigma) selection) := by
  have hspec := optimalPolynomialHeightWindow_spec hsigma hbeta hbetaOne
  have hheightReal :=
    eventually_selectedUniformGoodHeight_le_polynomialHeight
      hspec.2.1 hspec.2.2.1 selection
  have hheightNatural := tendsto_natCast_atTop_atTop.eventually hheightReal
  have htopReal := selectedUniformGoodHeight_tendsto_atTop hspec.2.1 selection
  have htopNatural := htopReal.comp tendsto_natCast_atTop_atTop
  have hremainder :=
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      (by linarith : 0 < beta)
      hspec.2.1 hspec.2.2.2.2.2.1 hspec.2.2.2.1 selection
  exact ⟨hheightNatural, htopNatural, hremainder⟩

end PrimeNumberTheorem
