import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail

open scoped BigOperators

namespace PrimeNumberTheorem

noncomputable section

-- Five public definitions.

example (x sigma tau : ℝ) (n : ℕ) :
    actualCubicDyadicStripSquareCapacity x sigma tau n =
      ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n,
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
          (x ^ (2 * rho.re) / ‖rho‖ ^ 4) :=
  rfl

example (x sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S =
      ∑ rho ∈ actualCarlsonDyadicZeroStrip sigma tau n \ S,
        ((analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / ‖rho‖ ^ 2) *
          (x ^ (2 * rho.re) / ‖rho‖ ^ 4) :=
  rfl

example (beta sigma tau gamma : ℝ) :
    cubicCarlsonL2BlockExponent beta sigma tau gamma =
      2 * (tau - beta) +
        gamma * (carlsonTwoHeightDensityExponent sigma - 6) :=
  rfl

example (B x sigma tau : ℝ) (n : ℕ) :
    actualCubicDyadicCountMajorant B x sigma tau n =
      (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 2)) :=
  rfl

example (x sigma tau : ℝ) (nLow nSplit nHigh : ℕ)
    (S : Finset ℂ) :
    actualCubicTwoHeightSquareTailCapacity
        x sigma tau nLow nSplit nHigh S =
      (∑ n ∈ Finset.Icc nLow nSplit,
        actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S) +
      ∑ n ∈ Finset.Ioc nSplit nHigh,
        actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S :=
  rfl

-- Nine public theorems.

example (x sigma tau : ℝ) (n : ℕ) (S : Finset ℂ) (hx : 0 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      actualCubicDyadicStripSquareCapacity x sigma tau n :=
  actualCubicDyadicStripSquareCapacityExcluding_le x sigma tau n S hx

example {x sigma tau : ℝ} {n : ℕ} (S : Finset ℂ) (hx : 1 ≤ x) :
    actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
      (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        actualCarlsonDyadicStripSquareReciprocalCapacityExcluding
          sigma tau n S :=
  actualCubicDyadicStripSquareCapacityExcluding_le_reciprocal S hx

example :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (x sigma tau : ℝ) (n : ℕ),
        1 ≤ x →
        4 ≤ (2 : ℝ) ^ n →
        ∀ S : Finset ℂ,
          actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
            (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
              (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
                (actualCarlsonDyadicCount sigma (n + 1) /
                  ((2 : ℝ) ^ n) ^ 2)) :=
  exists_actualCubicDyadicStripSquareCapacityExcluding_le_count

example (B x sigma tau : ℝ) (n : ℕ) :
    (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
        (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 2)) =
      B * x ^ (2 * tau) *
        (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
          (actualCarlsonDyadicCount sigma (n + 1) /
            ((2 : ℝ) ^ n) ^ 6) :=
  cubicDyadicCountProduct_eq_sixthPower B x sigma tau n

example (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 6 ≤ -5 :=
  pntCarlsonClassicalDensityExponent_sub_six_le_neg_five sigma

example :
    pntCarlsonClassicalDensityExponent (1 / 2) - 6 = -5 :=
  pntCarlsonClassicalDensityExponent_half_sub_six_eq_neg_five

example {beta sigma tau gamma : ℝ}
    (htau : tau < beta) (hgamma : 0 < gamma) :
    cubicCarlsonL2BlockExponent beta sigma tau gamma < 0 :=
  cubicCarlsonL2BlockExponent_lt_zero htau hgamma

example :
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
                actualCubicDyadicCountMajorant B x sigma tau n :=
  exists_actualCubicTwoHeightSquareTailCapacity_le

example {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
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
      cubicCarlsonL2BlockExponent beta sigma tau alpha < 0 :=
  exists_jointTwoHeightTargetAmplitudeParameters_with_cubicL2 hbeta hbetaOne

end

end PrimeNumberTheorem
