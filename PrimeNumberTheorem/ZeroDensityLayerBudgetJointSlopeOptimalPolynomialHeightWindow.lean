import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonWeightedOptimalPolynomialHeightWindow

namespace PrimeNumberTheorem

noncomputable section

/-- Two independent polynomial-height costs are governed by their larger
slope. -/
noncomputable def jointPolynomialHeightEffectiveSlope (q k : ℝ) : ℝ :=
  max q k

/-- Feasibility gap after paying both polynomial-height slopes. -/
noncomputable def jointPolynomialHeightFeasibilityGap
    (beta sigma q k : ℝ) : ℝ :=
  weightedPolynomialHeightFeasibilityGap beta sigma
    (jointPolynomialHeightEffectiveSlope q k)

/-- Minimax common margin for the joint-slope height problem. -/
noncomputable def jointOptimalPolynomialHeightSafetyMargin
    (beta sigma q k : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightSafetyMargin beta sigma
    (jointPolynomialHeightEffectiveSlope q k)

/-- Inner exponent for the joint-slope minimax allocation. -/
noncomputable def jointOptimalPolynomialHeightInnerExponent
    (beta sigma q k : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightInnerExponent beta sigma
    (jointPolynomialHeightEffectiveSlope q k)

/-- Outer exponent for the joint-slope minimax allocation. -/
noncomputable def jointOptimalPolynomialHeightOuterExponent
    (beta sigma q k : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightOuterExponent beta sigma
    (jointPolynomialHeightEffectiveSlope q k)

/-- Logarithmic slack for the joint-slope minimax allocation. -/
noncomputable def jointOptimalPolynomialHeightEpsilon
    (beta sigma q k : ℝ) : ℝ :=
  weightedOptimalPolynomialHeightEpsilon beta sigma
    (jointPolynomialHeightEffectiveSlope q k)

/-- For a nonnegative outer exponent, imposing two density/analytic height
budgets is equivalent to imposing the single budget with slope `max q k`. -/
theorem jointPolynomialHeightConstraints_iff_effectiveSlope
    {q k outer epsilon margin budget : ℝ} (houter : 0 ≤ outer) :
    (q * outer + epsilon + margin ≤ budget ∧
        k * outer + epsilon + margin ≤ budget) ↔
      jointPolynomialHeightEffectiveSlope q k * outer + epsilon + margin ≤
        budget := by
  constructor
  · intro h
    rcases le_total q k with hqk | hkq
    · simpa [jointPolynomialHeightEffectiveSlope, max_eq_right hqk] using h.2
    · simpa [jointPolynomialHeightEffectiveSlope, max_eq_left hkq] using h.1
  · intro h
    have hqmax : q * outer ≤ jointPolynomialHeightEffectiveSlope q k * outer := by
      exact mul_le_mul_of_nonneg_right
        (le_max_left q k) houter
    have hkmax : k * outer ≤ jointPolynomialHeightEffectiveSlope q k * outer := by
      exact mul_le_mul_of_nonneg_right
        (le_max_right q k) houter
    constructor <;> linarith

/-- The general weighted minimax theorem remains optimal when two independent
height slopes are present: their maximum is the only effective slope. -/
theorem jointPolynomialHeightCommonSafetyMargin_le_optimal
    {beta sigma q k inner outer epsilon margin : ℝ}
    (hq : 0 ≤ q) (hk : 0 ≤ k) (houter : 0 ≤ outer)
    (hcontour : 1 - beta + margin ≤ inner)
    (hwindow : inner + margin ≤ outer)
    (hlog : margin ≤ epsilon)
    (hqdensity : q * outer + epsilon + margin ≤ beta - sigma)
    (hkdensity : k * outer + epsilon + margin ≤ beta - sigma) :
    margin ≤ jointOptimalPolynomialHeightSafetyMargin beta sigma q k := by
  have heffective :
      jointPolynomialHeightEffectiveSlope q k * outer + epsilon + margin ≤
        beta - sigma :=
    (jointPolynomialHeightConstraints_iff_effectiveSlope houter).1
      ⟨hqdensity, hkdensity⟩
  have heffectiveNonneg : 0 ≤ jointPolynomialHeightEffectiveSlope q k := by
    rcases le_total q k with hqk | hkq
    · simpa [jointPolynomialHeightEffectiveSlope, max_eq_right hqk] using hk
    · simpa [jointPolynomialHeightEffectiveSlope, max_eq_left hkq] using hq
  simpa [jointOptimalPolynomialHeightSafetyMargin] using
    (weightedPolynomialHeightCommonSafetyMargin_le_optimal
      heffectiveNonneg hcontour hwindow hlog heffective)

/-- The joint optimizer attains equal margins for both constraints through the
effective maximum slope. -/
theorem jointOptimalPolynomialHeightWindow_equalMargins
    (beta sigma q k : ℝ) (hq : 0 ≤ q) (hk : 0 ≤ k) :
    jointOptimalPolynomialHeightInnerExponent beta sigma q k - (1 - beta) =
        jointOptimalPolynomialHeightSafetyMargin beta sigma q k ∧
      jointOptimalPolynomialHeightOuterExponent beta sigma q k -
          jointOptimalPolynomialHeightInnerExponent beta sigma q k =
        jointOptimalPolynomialHeightSafetyMargin beta sigma q k ∧
      jointOptimalPolynomialHeightEpsilon beta sigma q k =
        jointOptimalPolynomialHeightSafetyMargin beta sigma q k ∧
      beta - sigma -
          (jointPolynomialHeightEffectiveSlope q k *
              jointOptimalPolynomialHeightOuterExponent beta sigma q k +
            jointOptimalPolynomialHeightEpsilon beta sigma q k) =
        jointOptimalPolynomialHeightSafetyMargin beta sigma q k := by
  have heffectiveNonneg : 0 ≤ jointPolynomialHeightEffectiveSlope q k := by
    rcases le_total q k with hqk | hkq
    · simpa [jointPolynomialHeightEffectiveSlope, max_eq_right hqk] using hk
    · simpa [jointPolynomialHeightEffectiveSlope, max_eq_left hkq] using hq
  simpa [jointOptimalPolynomialHeightInnerExponent,
    jointOptimalPolynomialHeightOuterExponent,
    jointOptimalPolynomialHeightEpsilon,
    jointOptimalPolynomialHeightSafetyMargin] using
    (weightedOptimalPolynomialHeightWindow_equalMargins
      beta sigma (jointPolynomialHeightEffectiveSlope q k) heffectiveNonneg)

/-- Carlson's density slope is strictly below one inside the classical
half-strip. -/
theorem carlsonPolynomialDensitySlope_lt_one
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    carlsonPolynomialDensitySlope sigma < 1 := by
  have hqPos : 0 < carlsonPolynomialDensitySlope sigma :=
    carlsonPolynomialDensitySlope_pos (by linarith) hsigmaOne
  have htwosigma : 0 < 2 * sigma - 1 := by
    linarith
  have hsquare : 0 < (2 * sigma - 1) * (2 * sigma - 1) :=
    mul_pos htwosigma htwosigma
  unfold carlsonPolynomialDensitySlope
  nlinarith

/-- Combining Carlson's density slope with the independent unit-slope low
kernel cost gives effective slope exactly one. -/
theorem carlsonFullTransferEffectiveSlope_eq_one
    {sigma : ℝ} (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    jointPolynomialHeightEffectiveSlope
        (carlsonPolynomialDensitySlope sigma) 1 = 1 := by
  unfold jointPolynomialHeightEffectiveSlope
  exact max_eq_right (carlsonPolynomialDensitySlope_lt_one hsigma hsigmaOne).le

/-- Consequently the full-transfer joint optimizer is exactly the existing
quarter-gap unit-slope optimizer. -/
theorem carlsonFullTransferJointOptimizer_eq_unweighted
    (beta sigma : ℝ) (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    jointOptimalPolynomialHeightSafetyMargin beta sigma
          (carlsonPolynomialDensitySlope sigma) 1 =
        optimalPolynomialHeightSafetyMargin beta sigma ∧
      jointOptimalPolynomialHeightInnerExponent beta sigma
          (carlsonPolynomialDensitySlope sigma) 1 =
        optimalPolynomialHeightInnerExponent beta sigma ∧
      jointOptimalPolynomialHeightOuterExponent beta sigma
          (carlsonPolynomialDensitySlope sigma) 1 =
        optimalPolynomialHeightOuterExponent beta sigma ∧
      jointOptimalPolynomialHeightEpsilon beta sigma
          (carlsonPolynomialDensitySlope sigma) 1 =
        optimalPolynomialHeightEpsilon beta sigma := by
  have heffective :=
    carlsonFullTransferEffectiveSlope_eq_one hsigma hsigmaOne
  simpa [jointOptimalPolynomialHeightSafetyMargin,
    jointOptimalPolynomialHeightInnerExponent,
    jointOptimalPolynomialHeightOuterExponent,
    jointOptimalPolynomialHeightEpsilon, heffective] using
    (weightedOptimalPolynomialHeight_q_one beta sigma)

/-- The unit-slope full-transfer margin always implies the weaker
Carlson-density margin when the outer exponent is nonnegative. -/
theorem fullTransferMargin_implies_carlsonDensityMargin
    {beta sigma outer epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (houter : 0 ≤ outer)
    (hfull : outer + epsilon < beta - sigma) :
    carlsonPolynomialDensitySlope sigma * outer + epsilon < beta - sigma := by
  have hqOne : carlsonPolynomialDensitySlope sigma ≤ 1 :=
    (carlsonPolynomialDensitySlope_lt_one hsigma hsigmaOne).le
  have hmul : carlsonPolynomialDensitySlope sigma * outer ≤ 1 * outer :=
    mul_le_mul_of_nonneg_right hqOne houter
  linarith

/-- The converse fails quantitatively even with positive outer exponent and
positive logarithmic slack. Thus the Carlson-weighted density budget alone
cannot be fed into the current full PNT transfer. -/
theorem exists_carlsonDensityMargin_without_fullTransferMargin
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hbetaSigma : sigma < beta) :
    ∃ outer epsilon : ℝ,
      0 < outer ∧ 0 < epsilon ∧
      carlsonPolynomialDensitySlope sigma * outer + epsilon < beta - sigma ∧
      ¬(outer + epsilon < beta - sigma) := by
  have hbudget : 0 < beta - sigma := by
    linarith
  have hqOne : carlsonPolynomialDensitySlope sigma < 1 :=
    carlsonPolynomialDensitySlope_lt_one hsigma hsigmaOne
  have hproduct :
      0 < (1 - carlsonPolynomialDensitySlope sigma) * (beta - sigma) :=
    mul_pos (sub_pos.mpr hqOne) hbudget
  refine ⟨beta - sigma,
    (1 - carlsonPolynomialDensitySlope sigma) * (beta - sigma) / 2,
    hbudget, div_pos hproduct (by norm_num), ?_, ?_⟩
  · nlinarith
  · intro hfull
    nlinarith

end

end PrimeNumberTheorem
