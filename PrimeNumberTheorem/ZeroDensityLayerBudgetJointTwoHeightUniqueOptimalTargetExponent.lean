import Mathlib.Topology.Order.IntermediateValue
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightImprovedCapThresholdStrictMono

/-!
# Unique optimal target exponent

The strictly increasing improved cap threshold is inverted.  Every prescribed
cap `theta` in `(1 / 2, 1)` has a unique target exponent `beta` in
`(2 / 3, 1)` whose improved threshold equals `theta`.
-/

namespace PrimeNumberTheorem

open Set

/-- Denominator-cleared equation for
`jointTwoHeightImprovedGlobalCapThreshold beta = theta`. -/
noncomputable def jointTwoHeightImprovedCapInversePolynomial
    (theta beta : ℝ) : ℝ :=
  (beta - theta) *
      (jointTwoHeightCanonicalDensityExponent beta + 1) -
    (1 - beta) * jointTwoHeightCanonicalDensityExponent beta ^ 2

theorem continuous_jointTwoHeightImprovedCapInversePolynomial
    (theta : ℝ) :
    Continuous (jointTwoHeightImprovedCapInversePolynomial theta) := by
  unfold jointTwoHeightImprovedCapInversePolynomial
    jointTwoHeightCanonicalDensityExponent
  fun_prop

theorem jointTwoHeightImprovedCapInversePolynomial_twoThird
    (theta : ℝ) :
    jointTwoHeightImprovedCapInversePolynomial theta (2 / 3) =
      1 - 2 * theta := by
  unfold jointTwoHeightImprovedCapInversePolynomial
    jointTwoHeightCanonicalDensityExponent
  ring

theorem jointTwoHeightImprovedCapInversePolynomial_one
    (theta : ℝ) :
    jointTwoHeightImprovedCapInversePolynomial theta 1 =
      1 - theta := by
  unfold jointTwoHeightImprovedCapInversePolynomial
    jointTwoHeightCanonicalDensityExponent
  ring

/-- Predicate characterizing the inverse target exponent for a prescribed
real-part cap. -/
def IsJointTwoHeightOptimalTargetExponent
    (theta beta : ℝ) : Prop :=
  2 / 3 < beta ∧
    beta < 1 ∧
    jointTwoHeightImprovedGlobalCapThreshold beta = theta

/-- Every cap in `(1 / 2, 1)` has an inverse target exponent. -/
theorem exists_jointTwoHeightOptimalTargetExponent
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    ∃ beta : ℝ, IsJointTwoHeightOptimalTargetExponent theta beta := by
  let f := jointTwoHeightImprovedCapInversePolynomial theta
  have hleft : f (2 / 3) < 0 := by
    dsimp [f]
    rw [jointTwoHeightImprovedCapInversePolynomial_twoThird]
    linarith
  have hright : 0 < f 1 := by
    dsimp [f]
    rw [jointTwoHeightImprovedCapInversePolynomial_one]
    linarith
  have hzero : (0 : ℝ) ∈ Set.Icc (f (2 / 3)) (f 1) :=
    ⟨hleft.le, hright.le⟩
  have himage :
      (0 : ℝ) ∈ f '' Set.Icc (2 / 3) 1 :=
    intermediate_value_Icc (by norm_num)
      (continuous_jointTwoHeightImprovedCapInversePolynomial theta).continuousOn
      hzero
  rcases himage with ⟨beta, hbetaIcc, hbetaZero⟩
  have hbetaNeLeft : beta ≠ 2 / 3 := by
    intro hbeta
    subst beta
    linarith
  have hbetaNeOne : beta ≠ 1 := by
    intro hbeta
    subst beta
    linarith
  have hbeta : 2 / 3 < beta :=
    lt_of_le_of_ne hbetaIcc.1 (Ne.symm hbetaNeLeft)
  have hbetaOne : beta < 1 :=
    lt_of_le_of_ne hbetaIcc.2 hbetaNeOne
  let q := jointTwoHeightCanonicalDensityExponent beta
  have hqPos : 0 < q := by
    dsimp [q, jointTwoHeightCanonicalDensityExponent]
    have hleftFactor : 0 < 3 * beta - 1 := by linarith
    have hrightFactor : 0 < 1 - beta := sub_pos.mpr hbetaOne
    positivity
  have hqDen : q + 1 ≠ 0 := by linarith
  have hpolynomial :
      (beta - theta) * (q + 1) -
          (1 - beta) * q ^ 2 =
        0 := by
    simpa [f, jointTwoHeightImprovedCapInversePolynomial, q] using hbetaZero
  have hquotient :
      beta - theta =
        (1 - beta) * q ^ 2 / (q + 1) := by
    rw [eq_div_iff hqDen]
    nlinarith
  have hthreshold :
      jointTwoHeightImprovedGlobalCapThreshold beta = theta := by
    rw [jointTwoHeightImprovedGlobalCapThreshold_explicit]
    change beta - (1 - beta) * (q ^ 2 / (q + 1)) = theta
    rw [show
      (1 - beta) * (q ^ 2 / (q + 1)) =
        (1 - beta) * q ^ 2 / (q + 1) by ring]
    nlinarith
  exact ⟨beta, hbeta, hbetaOne, hthreshold⟩

/-- Two inverse target exponents for the same prescribed cap coincide. -/
theorem IsJointTwoHeightOptimalTargetExponent.unique
    {theta beta₁ beta₂ : ℝ}
    (hbeta₁ : IsJointTwoHeightOptimalTargetExponent theta beta₁)
    (hbeta₂ : IsJointTwoHeightOptimalTargetExponent theta beta₂) :
    beta₁ = beta₂ := by
  rcases hbeta₁ with ⟨hbeta₁Lower, hbeta₁One, hthreshold₁⟩
  rcases hbeta₂ with ⟨hbeta₂Lower, hbeta₂One, hthreshold₂⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstrict :=
      jointTwoHeightImprovedGlobalCapThreshold_strictMono
        hbeta₁Lower hlt hbeta₂One
    linarith
  · have hstrict :=
      jointTwoHeightImprovedGlobalCapThreshold_strictMono
        hbeta₂Lower hgt hbeta₁One
    linarith

theorem existsUnique_jointTwoHeightOptimalTargetExponent
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    ∃! beta : ℝ, IsJointTwoHeightOptimalTargetExponent theta beta := by
  rcases
      exists_jointTwoHeightOptimalTargetExponent
        hthetaHalf hthetaOne with
    ⟨beta, hbeta⟩
  refine ⟨beta, hbeta, ?_⟩
  intro beta' hbeta'
  exact
    (IsJointTwoHeightOptimalTargetExponent.unique hbeta hbeta').symm

/-- Canonical inverse target exponent, with a harmless fallback outside the
cap interval. -/
noncomputable def jointTwoHeightOptimalTargetExponent
    (theta : ℝ) : ℝ :=
  if h : 1 / 2 < theta ∧ theta < 1 then
    Classical.choose
      (existsUnique_jointTwoHeightOptimalTargetExponent
        h.1 h.2).exists
  else
    2 / 3

theorem jointTwoHeightOptimalTargetExponent_spec
    {theta : ℝ}
    (hthetaHalf : 1 / 2 < theta)
    (hthetaOne : theta < 1) :
    IsJointTwoHeightOptimalTargetExponent theta
      (jointTwoHeightOptimalTargetExponent theta) := by
  unfold jointTwoHeightOptimalTargetExponent
  rw [dif_pos ⟨hthetaHalf, hthetaOne⟩]
  exact
    Classical.choose_spec
      (existsUnique_jointTwoHeightOptimalTargetExponent
        hthetaHalf hthetaOne).exists

end PrimeNumberTheorem
