import PrimeNumberTheorem.ZeroDensityLayerBudgetOptimalPolynomialHeightWindow

namespace PrimeNumberTheorem

noncomputable section

/-- Remaining exponent budget after a density estimate with polynomial-height
slope `q` pays for the contour lower threshold `1 - beta`. -/
noncomputable def weightedPolynomialHeightFeasibilityGap
    (beta sigma q : ℝ) : ℝ :=
  beta - sigma - q * (1 - beta)

/-- Minimax common safety margin for the four weighted polynomial-height
constraints: contour, selected-height window, logarithmic slack, and density. -/
noncomputable def weightedOptimalPolynomialHeightSafetyMargin
    (beta sigma q : ℝ) : ℝ :=
  weightedPolynomialHeightFeasibilityGap beta sigma q / (2 * (q + 1))

/-- Inner exponent in the minimax weighted polynomial-height window. -/
noncomputable def weightedOptimalPolynomialHeightInnerExponent
    (beta sigma q : ℝ) : ℝ :=
  1 - beta + weightedOptimalPolynomialHeightSafetyMargin beta sigma q

/-- Outer exponent in the minimax weighted polynomial-height window. -/
noncomputable def weightedOptimalPolynomialHeightOuterExponent
    (beta sigma q : ℝ) : ℝ :=
  1 - beta + 2 * weightedOptimalPolynomialHeightSafetyMargin beta sigma q

/-- Logarithmic slack in the minimax weighted polynomial-height window. -/
noncomputable def weightedOptimalPolynomialHeightEpsilon
    (beta sigma q : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightSafetyMargin beta sigma q

/-- No allocation satisfying all four weighted constraints can have common
safety margin larger than the weighted minimax value. -/
theorem weightedPolynomialHeightCommonSafetyMargin_le_optimal
    {beta sigma q inner outer epsilon margin : ℝ}
    (hq : 0 ≤ q)
    (hcontour : 1 - beta + margin ≤ inner)
    (hwindow : inner + margin ≤ outer)
    (hlog : margin ≤ epsilon)
    (hdensity : q * outer + epsilon + margin ≤ beta - sigma) :
    margin ≤ weightedOptimalPolynomialHeightSafetyMargin beta sigma q := by
  have hinnerOuter : 1 - beta + 2 * margin ≤ outer := by
    linarith
  have hweighted : q * (1 - beta + 2 * margin) ≤ q * outer :=
    mul_le_mul_of_nonneg_left hinnerOuter hq
  have htail : q * outer + 2 * margin ≤ beta - sigma := by
    linarith
  have hbudget :
      q * (1 - beta + 2 * margin) + 2 * margin ≤ beta - sigma := by
    nlinarith
  have hden : 0 < 2 * (q + 1) := by
    nlinarith
  unfold weightedOptimalPolynomialHeightSafetyMargin
  apply (le_div_iff₀ hden).2
  unfold weightedPolynomialHeightFeasibilityGap
  nlinarith

/-- The weighted minimax allocation makes the four safety margins equal. -/
theorem weightedOptimalPolynomialHeightWindow_equalMargins
    (beta sigma q : ℝ) (hq : 0 ≤ q) :
    weightedOptimalPolynomialHeightInnerExponent beta sigma q - (1 - beta) =
        weightedOptimalPolynomialHeightSafetyMargin beta sigma q ∧
      weightedOptimalPolynomialHeightOuterExponent beta sigma q -
          weightedOptimalPolynomialHeightInnerExponent beta sigma q =
        weightedOptimalPolynomialHeightSafetyMargin beta sigma q ∧
      weightedOptimalPolynomialHeightEpsilon beta sigma q =
        weightedOptimalPolynomialHeightSafetyMargin beta sigma q ∧
      beta - sigma -
          (q * weightedOptimalPolynomialHeightOuterExponent beta sigma q +
            weightedOptimalPolynomialHeightEpsilon beta sigma q) =
        weightedOptimalPolynomialHeightSafetyMargin beta sigma q := by
  have hden : 2 * (q + 1) ≠ 0 := by
    nlinarith
  unfold weightedOptimalPolynomialHeightInnerExponent
    weightedOptimalPolynomialHeightOuterExponent
    weightedOptimalPolynomialHeightEpsilon
    weightedOptimalPolynomialHeightSafetyMargin
    weightedPolynomialHeightFeasibilityGap
  constructor
  · ring
  constructor
  · ring
  constructor
  · rfl
  · field_simp [hden]
    ring

/-- At density slope `q = 1`, the weighted optimizer is exactly the quarter-gap
optimizer from the unweighted polynomial-height window. -/
theorem weightedOptimalPolynomialHeight_q_one (beta sigma : ℝ) :
    weightedOptimalPolynomialHeightSafetyMargin beta sigma 1 =
        optimalPolynomialHeightSafetyMargin beta sigma ∧
      weightedOptimalPolynomialHeightInnerExponent beta sigma 1 =
        optimalPolynomialHeightInnerExponent beta sigma ∧
      weightedOptimalPolynomialHeightOuterExponent beta sigma 1 =
        optimalPolynomialHeightOuterExponent beta sigma ∧
      weightedOptimalPolynomialHeightEpsilon beta sigma 1 =
        optimalPolynomialHeightEpsilon beta sigma := by
  have hmargin :
      weightedOptimalPolynomialHeightSafetyMargin beta sigma 1 =
        optimalPolynomialHeightSafetyMargin beta sigma := by
    unfold weightedOptimalPolynomialHeightSafetyMargin
      weightedPolynomialHeightFeasibilityGap
      optimalPolynomialHeightSafetyMargin canonicalPolynomialHeightGap
    ring
  refine ⟨hmargin, ?_, ?_, ?_⟩
  · unfold weightedOptimalPolynomialHeightInnerExponent
      optimalPolynomialHeightInnerExponent
    rw [hmargin]
  · unfold weightedOptimalPolynomialHeightOuterExponent
      optimalPolynomialHeightOuterExponent
    rw [hmargin]
  · unfold weightedOptimalPolynomialHeightEpsilon
      optimalPolynomialHeightEpsilon
    exact hmargin

/-- Arithmetic specification of the weighted minimax window. The strict
feasibility gap is the exact hypothesis needed after the density slope `q`
pays for the contour threshold. -/
theorem weightedOptimalPolynomialHeightWindow_spec
    {beta sigma q : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : 0 < sigma) (hq : 0 ≤ q)
    (hgap : 0 < weightedPolynomialHeightFeasibilityGap beta sigma q) :
    0 < weightedOptimalPolynomialHeightSafetyMargin beta sigma q ∧
      0 < weightedOptimalPolynomialHeightInnerExponent beta sigma q ∧
      weightedOptimalPolynomialHeightInnerExponent beta sigma q <
          weightedOptimalPolynomialHeightOuterExponent beta sigma q ∧
      1 - beta < weightedOptimalPolynomialHeightInnerExponent beta sigma q ∧
      q * weightedOptimalPolynomialHeightOuterExponent beta sigma q +
          weightedOptimalPolynomialHeightEpsilon beta sigma q < beta - sigma ∧
      weightedOptimalPolynomialHeightInnerExponent beta sigma q ≤ 1 ∧
      0 < weightedOptimalPolynomialHeightEpsilon beta sigma q ∧
      q * weightedOptimalPolynomialHeightOuterExponent beta sigma q +
          weightedOptimalPolynomialHeightEpsilon beta sigma q +
          weightedOptimalPolynomialHeightSafetyMargin beta sigma q =
        beta - sigma := by
  have hden : 0 < 2 * (q + 1) := by
    nlinarith
  have hmargin :
      0 < weightedOptimalPolynomialHeightSafetyMargin beta sigma q := by
    unfold weightedOptimalPolynomialHeightSafetyMargin
    exact div_pos hgap hden
  have hgapLtBeta :
      weightedPolynomialHeightFeasibilityGap beta sigma q < beta := by
    have hweighted : 0 ≤ q * (1 - beta) := by
      exact mul_nonneg hq (by linarith)
    unfold weightedPolynomialHeightFeasibilityGap
    linarith
  have hdenOne : 1 < 2 * (q + 1) := by
    nlinarith
  have hmarginLtGap :
      weightedOptimalPolynomialHeightSafetyMargin beta sigma q <
        weightedPolynomialHeightFeasibilityGap beta sigma q := by
    unfold weightedOptimalPolynomialHeightSafetyMargin
    exact div_lt_self hgap hdenOne
  have hmarginLtBeta :
      weightedOptimalPolynomialHeightSafetyMargin beta sigma q < beta :=
    lt_trans hmarginLtGap hgapLtBeta
  have hinner :
      0 < weightedOptimalPolynomialHeightInnerExponent beta sigma q := by
    unfold weightedOptimalPolynomialHeightInnerExponent
    linarith
  have hinnerOuter :
      weightedOptimalPolynomialHeightInnerExponent beta sigma q <
        weightedOptimalPolynomialHeightOuterExponent beta sigma q := by
    unfold weightedOptimalPolynomialHeightInnerExponent
      weightedOptimalPolynomialHeightOuterExponent
    linarith
  have hcontour :
      1 - beta < weightedOptimalPolynomialHeightInnerExponent beta sigma q := by
    unfold weightedOptimalPolynomialHeightInnerExponent
    linarith
  have hinnerOne :
      weightedOptimalPolynomialHeightInnerExponent beta sigma q ≤ 1 := by
    unfold weightedOptimalPolynomialHeightInnerExponent
    linarith
  have hepsilon :
      0 < weightedOptimalPolynomialHeightEpsilon beta sigma q := by
    exact hmargin
  have hequal :=
    (weightedOptimalPolynomialHeightWindow_equalMargins beta sigma q hq).2.2.2
  have hdensity :
      q * weightedOptimalPolynomialHeightOuterExponent beta sigma q +
          weightedOptimalPolynomialHeightEpsilon beta sigma q < beta - sigma := by
    linarith
  have hexact :
      q * weightedOptimalPolynomialHeightOuterExponent beta sigma q +
          weightedOptimalPolynomialHeightEpsilon beta sigma q +
          weightedOptimalPolynomialHeightSafetyMargin beta sigma q =
        beta - sigma := by
    linarith
  exact ⟨hmargin, hinner, hinnerOuter, hcontour, hdensity, hinnerOne,
    hepsilon, hexact⟩

/-- The weighted minimax exponents produce the actual selected-height growth
and natural-point explicit-formula remainder certificate. -/
theorem weightedOptimalPolynomialSelectedHeight_spec
    {beta sigma q : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : 0 < sigma) (hq : 0 ≤ q)
    (hgap : 0 < weightedPolynomialHeightFeasibilityGap beta sigma q)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ (m : ℕ) in Filter.atTop,
        selectedUniformGoodHeight
              (weightedOptimalPolynomialHeightInnerExponent beta sigma q)
              selection m ≤
          carlsonPolynomialHeight
            (weightedOptimalPolynomialHeightOuterExponent beta sigma q) m) ∧
      Filter.Tendsto
          (fun m : ℕ =>
            selectedUniformGoodHeight
              (weightedOptimalPolynomialHeightInnerExponent beta sigma q)
              selection m)
          Filter.atTop Filter.atTop ∧
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (selectedUniformGoodHeight
          (weightedOptimalPolynomialHeightInnerExponent beta sigma q) selection) := by
  rcases weightedOptimalPolynomialHeightWindow_spec hbeta hbetaOne hsigma hq hgap with
    ⟨_, hinner, hinnerOuter, hcontour, _, hinnerOne, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · exact tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_le_polynomialHeight
        hinner hinnerOuter selection)
  · exact (selectedUniformGoodHeight_tendsto_atTop hinner selection).comp
      tendsto_natCast_atTop_atTop
  · exact selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta hinner hinnerOne hcontour selection

end

end PrimeNumberTheorem
