import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicSquareMultiplicityCapacity
import PrimeNumberTheorem.ZeroDensityLayerBudgetJointTwoHeightParameterFeasibility

/-!
# Actual cubic two-height L2 tail capacity

This module keeps the third-order explicit-formula zero coefficient at cubic
order.  It converts the actual reciprocal-square multiplicity capacity into
the coefficient-square mass carrying the four additional powers of the zero
height.  Removing a finite exceptional set uses only nonnegative-mass
monotonicity.
-/

namespace PrimeNumberTheorem

open scoped BigOperators

/-- Square mass of the actual cubic zero coefficients in one Carlson dyadic
strip.  The factorization displays the reciprocal-square capacity already
provided by the direct-L2 interface and the four extra cubic powers. -/
noncomputable def actualCubicDyadicStripSquareCapacity
    (x sigma tau : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
    ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
      (x ^ (2 * rho.re) / ‖rho‖ ^ 4)

/-- The same actual cubic square mass after deleting an arbitrary finite set
of zeros. -/
noncomputable def actualCubicDyadicStripSquareCapacityExcluding
    (x sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) : ℝ :=
  ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
    ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
      (x ^ (2 * rho.re) / ‖rho‖ ^ 4)

/-- Deleting a finite set cannot increase the nonnegative cubic coefficient
square mass.  No density estimate is specialized to the deleted set. -/
theorem actualCubicDyadicStripSquareCapacityExcluding_le
    (x sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (hx : 0 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      actualCubicDyadicStripSquareCapacity x sigma tau n := by
  unfold actualCubicDyadicStripSquareCapacityExcluding
    actualCubicDyadicStripSquareCapacity
  exact Finset.sum_le_sum_of_subset_of_nonneg
    Finset.sdiff_subset
    (fun _ _ _ => mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
      (div_nonneg (Real.rpow_nonneg hx _) (by positivity)))

/-- On a dyadic strip, the four extra cubic denominator powers and the real
part cap reduce the cubic square mass to the reciprocal-square capacity. -/
theorem actualCubicDyadicStripSquareCapacityExcluding_le_reciprocal
    {x sigma tau : ℝ} {n : ℕ} (S : Finset ℂ) (hx : 1 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma tau n S := by
  have hterm :
      ∀ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
            (x ^ (2 * rho.re) / ‖rho‖ ^ 4) ≤
          ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
            (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) := by
    intro rho hrho
    have hstrip : rho ∈ actualCarlsonDyadicZeroStrip sigma tau n :=
      (Finset.mem_sdiff.mp hrho).1
    have hre : rho.re ≤ tau :=
      (Finset.mem_filter.mp hstrip).2
    have hshell : rho ∈ actualCarlsonDyadicZeroShell sigma n :=
      actualCarlsonDyadicZeroStrip_subset_shell sigma tau n hstrip
    have him : (2 : ℝ) ^ n < rho.im :=
      actualCarlsonDyadicZeroShell_im_gt hshell
    have hnorm : (2 : ℝ) ^ n ≤ ‖rho‖ :=
      him.le.trans (Complex.im_le_norm rho)
    have hxpow : x ^ (2 * rho.re) ≤ x ^ (2 * tau) :=
      Real.rpow_le_rpow_of_exponent_le hx (by linarith)
    have hfactor :
        x ^ (2 * rho.re) / ‖rho‖ ^ 4 ≤
          x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4 := by
      gcongr
    exact mul_le_mul_of_nonneg_left hfactor
      (div_nonneg (sq_nonneg _) (sq_nonneg _))
  unfold actualCubicDyadicStripSquareCapacityExcluding
    actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
  calc
    (∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
          (x ^ (2 * rho.re) / ‖rho‖ ^ 4)) ≤
        ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
          ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
            (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) :=
      Finset.sum_le_sum hterm
    _ = (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
          ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rho _
      ring

/-- Actual zeta instance: one logarithmic multiplicity loss times the Carlson
linear count, with four additional dyadic denominator powers visible. -/
theorem exists_actualCubicDyadicStripSquareCapacityExcluding_le_count :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (x sigma tau : ℝ) (n : ℕ),
        1 ≤ x →
        4 ≤ (2 : ℝ) ^ n →
        ∀ S : Finset ℂ,
          actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
            (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
              (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
                (actualCarlsonDyadicCount sigma (n + 1) /
                  ((2 : ℝ) ^ n) ^ 2)) := by
  rcases
      exists_actualCarlsonDyadicStripSquareReciprocalCapacityExcluding_le_count
    with ⟨B, hB, hbound⟩
  refine ⟨B, hB, ?_⟩
  intro x sigma tau n hx hn S
  calc
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
        (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
          actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
            sigma tau n S :=
      actualCubicDyadicStripSquareCapacityExcluding_le_reciprocal S hx
    _ ≤ (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 2)) :=
      mul_le_mul_of_nonneg_left (hbound sigma tau n hn S)
        (div_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _) (by positivity))

/-- The displayed product in the actual block bound has total denominator
power six. -/
theorem cubicDyadicCountProduct_eq_sixthPower
    (B x sigma tau : ℝ) (n : ℕ) :
    (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 2)) =
      B * x ^ (2 * tau) *
        (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 6) := by
  have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
  field_simp [htwo]

/-- Polynomial exponent of one cubic coefficient-square Carlson block at
height `x^gamma`, normalized by a fixed target coefficient of real part
`beta`. -/
noncomputable def cubicCarlsonL2BlockExponent
    (beta sigma tau gamma : ℝ) : ℝ :=
  2 * (tau - beta) +
    gamma * (carlsonTwoHeightDensityExponent sigma - 6)

/-- The cubic coefficient-square denominator improves the unconditional
Carlson density slope to at most `-5`. -/
theorem pntCarlsonClassicalDensityExponent_sub_six_le_neg_five
    (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 6 ≤ -5 := by
  have htwo := pntCarlsonClassicalDensityExponent_sub_two_le_neg_one sigma
  linarith

/-- At the Carlson equality point `sigma = 1/2`, the cubic L2 exponent is
still strictly negative and equals `-5`. -/
theorem pntCarlsonClassicalDensityExponent_half_sub_six_eq_neg_five :
    pntCarlsonClassicalDensityExponent (1 / 2) - 6 = -5 := by
  rw [pntCarlsonClassicalDensityExponent_half_eq_one]
  norm_num

/-- Every positive polynomial block exponent has strictly decaying cubic L2
mass once the strip lies strictly left of the target real part. -/
theorem cubicCarlsonL2BlockExponent_lt_zero
    {beta sigma tau gamma : ℝ}
    (htau : tau < beta) (hgamma : 0 < gamma) :
    cubicCarlsonL2BlockExponent beta sigma tau gamma < 0 := by
  have hq : carlsonTwoHeightDensityExponent sigma - 6 ≤ -5 := by
    simpa [carlsonTwoHeightDensityExponent,
      pntCarlsonClassicalDensityExponent] using
      pntCarlsonClassicalDensityExponent_sub_six_le_neg_five sigma
  have hqneg : carlsonTwoHeightDensityExponent sigma - 6 < 0 := by
    linarith
  have hprod :
      gamma * (carlsonTwoHeightDensityExponent sigma - 6) < 0 :=
    mul_neg_of_pos_of_neg hgamma hqneg
  unfold cubicCarlsonL2BlockExponent
  linarith

/-- The explicit block majorant used in both sides of the two-height split. -/
noncomputable def actualCubicDyadicCountMajorant
    (B x sigma tau : ℝ) (n : ℕ) : ℝ :=
  (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
    (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
      (actualCarlsonDyadicCount sigma (n + 1) /
        ((2 : ℝ) ^ n) ^ 2))

/-- Actual cubic square tail split once at the dyadic index corresponding to
the Carlson balance height. -/
noncomputable def actualCubicTwoHeightSquareTailCapacity
    (x sigma tau : ℝ) (nLow nSplit nHigh : ℕ)
    (S : Finset ℂ) : ℝ :=
  (∑ n ∈ Finset.Icc nLow nSplit,
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S) +
    ∑ n ∈ Finset.Ioc nSplit nHigh,
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S

/-- The same actual Carlson constant controls both sides of the unique
two-height split. -/
theorem exists_actualCubicTwoHeightSquareTailCapacity_le :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (x sigma tau : ℝ) (nLow nSplit nHigh : ℕ),
        1 ≤ x →
        (∀ n ∈ Finset.Icc nLow nSplit, 4 ≤ (2 : ℝ) ^ n) →
        (∀ n ∈ Finset.Ioc nSplit nHigh, 4 ≤ (2 : ℝ) ^ n) →
        ∀ S : Finset ℂ,
          actualCubicTwoHeightSquareTailCapacity
              x sigma tau nLow nSplit nHigh S ≤
            (∑ n ∈ Finset.Icc nLow nSplit,
              actualCubicDyadicCountMajorant B x sigma tau n) +
              ∑ n ∈ Finset.Ioc nSplit nHigh,
                actualCubicDyadicCountMajorant B x sigma tau n := by
  rcases exists_actualCubicDyadicStripSquareCapacityExcluding_le_count with
    ⟨B, hB, hblock⟩
  refine ⟨B, hB, ?_⟩
  intro x sigma tau nLow nSplit nHigh hx hlow hhigh S
  unfold actualCubicTwoHeightSquareTailCapacity
    actualCubicDyadicCountMajorant
  apply add_le_add
  · exact Finset.sum_le_sum fun n hn => hblock x sigma tau n hx (hlow n hn) S
  · exact Finset.sum_le_sum fun n hn => hblock x sigma tau n hx (hhigh n hn) S

/-- The joint two-height parameter theorem simultaneously supplies all four
legacy strict margins and strict cubic L2 decay at the detector, balance, and
outer exponents. -/
theorem exists_jointTwoHeightTargetAmplitudeParameters_with_cubicL2
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh epsilonLow epsilonHigh : ℝ,
      1 / 2 < sigma ∧
      sigma < tau ∧
      tau < beta ∧
      sigma < 1 ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      gammaLow = alpha / 2 ∧
      0 < gammaLow ∧
      gammaLow ≤ alpha ∧
      gammaHigh = carlsonTwoHeightBalancedCut sigma alpha ∧
      0 < gammaHigh ∧
      gammaHigh < alpha ∧
      0 < epsilonLow ∧
      0 < epsilonHigh ∧
      gammaLow + sigma - beta + epsilonLow < 0 ∧
      alpha + sigma - beta - gammaLow + epsilonLow < 0 ∧
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gammaHigh + epsilonHigh < 0 ∧
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gammaHigh + epsilonHigh < 0 ∧
      cubicCarlsonL2BlockExponent beta sigma tau gammaLow < 0 ∧
      cubicCarlsonL2BlockExponent beta sigma tau gammaHigh < 0 ∧
      cubicCarlsonL2BlockExponent beta sigma tau alpha < 0 := by
  rcases exists_jointTwoHeightTargetAmplitudeParameters hbeta hbetaOne with
    ⟨sigma, tau, alpha, gammaLow, gammaHigh, epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, htauBeta, hsigmaOne,
      hcontour, halphaPos, halphaOne, hgammaLowEq,
      hgammaLowPos, hgammaLowAlpha, hgammaHighEq,
      hgammaHighPos, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowMargin, hhighGlobalMargin, hcarlsonLow, hcarlsonHigh⟩
  refine ⟨sigma, tau, alpha, gammaLow, gammaHigh, epsilonLow, epsilonHigh,
    hsigmaHalf, hsigmaTau, htauBeta, hsigmaOne,
    hcontour, halphaPos, halphaOne, hgammaLowEq,
    hgammaLowPos, hgammaLowAlpha, hgammaHighEq,
    hgammaHighPos, hgammaHighAlpha,
    hepsilonLow, hepsilonHigh,
    hlowMargin, hhighGlobalMargin, hcarlsonLow, hcarlsonHigh, ?_, ?_, ?_⟩
  · exact cubicCarlsonL2BlockExponent_lt_zero htauBeta hgammaLowPos
  · exact cubicCarlsonL2BlockExponent_lt_zero htauBeta hgammaHighPos
  · exact cubicCarlsonL2BlockExponent_lt_zero htauBeta halphaPos

end PrimeNumberTheorem
