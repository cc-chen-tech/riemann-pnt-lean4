import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonQuantitativeMovingTail

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

example (sigma : ℝ) (n : ℕ) :
    actualCubicCarlsonLogFifthCore sigma n =
      (n + 1 : ℝ) ^ 5 * actualCubicCarlsonDyadicRatio sigma ^ (n + 1) := rfl

example (sigma : ℝ) :
    actualCubicCarlsonLogFifthConstant sigma =
      ∑' n : ℕ, actualCubicCarlsonLogFifthCore sigma n := rfl

example (C sigma : ℝ) (N : ℕ) :
    actualCubicCarlsonDyadicLogFifthTail C sigma N =
      ∑' n : ℕ,
        actualCubicCarlsonDyadicLogFifthMajorant C sigma (n + (N + 1)) := rfl

example (C beta tau sigma gamma : ℝ) (m : ℕ) :
    actualCubicCarlsonNormalizedMovingLogFifthTail C beta tau sigma gamma m =
      (m : ℝ) ^ (2 * (tau - beta)) *
        actualCubicCarlsonDyadicLogFifthTail C sigma
          (actualCubicDyadicPolynomialCut gamma m) := rfl

example (C beta tau sigma gamma : ℝ) (m : ℕ) :
    actualCubicCarlsonNormalizedMovingLogFifthMajorant C beta tau sigma gamma m =
      (C * actualCubicCarlsonLogFifthConstant sigma *
          (gamma / Real.log 2 + 2) ^ 5) *
        (m : ℝ) ^ cubicCarlsonL2BlockExponent beta sigma tau gamma *
          Real.log (m : ℝ) ^ 5 := rfl

example (sigma : ℝ) : Summable (actualCubicCarlsonLogFifthCore sigma) := by
  exact summable_actualCubicCarlsonLogFifthCore sigma

example (sigma : ℝ) : 0 ≤ actualCubicCarlsonLogFifthConstant sigma := by
  exact actualCubicCarlsonLogFifthConstant_nonneg sigma

example {C : ℝ} (hC : 0 ≤ C) (sigma : ℝ) (N : ℕ) :
    actualCubicCarlsonDyadicLogFifthTail C sigma N ≤
      (C * (N + 2 : ℝ) ^ 5 * actualCubicCarlsonDyadicRatio sigma ^ (N + 1)) *
        actualCubicCarlsonLogFifthConstant sigma := by
  exact actualCubicCarlsonDyadicLogFifthTail_le hC sigma N

example (gamma sigma : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    actualCubicCarlsonDyadicRatio sigma ^
        (actualCubicDyadicPolynomialCut gamma m + 1) ≤
      (m : ℝ) ^ (gamma * (carlsonTwoHeightDensityExponent sigma - 6)) := by
  exact actualCubicCarlsonDyadicRatio_pow_cut_succ_le gamma sigma hm

example {gamma : ℝ} (hgamma : 0 < gamma) :
    ∀ᶠ m : ℕ in atTop,
      (actualCubicDyadicPolynomialCut gamma m + 2 : ℝ) ≤
        (gamma / Real.log 2 + 2) * Real.log (m : ℝ) := by
  exact eventually_actualCubicDyadicPolynomialCut_add_two_le_log hgamma

example {exponent epsilon : ℝ} (k : ℕ)
    (hepsilon : 0 < epsilon) (hmargin : exponent + epsilon < 0) :
    Tendsto (fun x : ℝ => x ^ exponent * Real.log x ^ k)
      atTop (nhds 0) := by
  exact tendsto_rpow_mul_log_pow_atTop_nhds_zero k hepsilon hmargin

example {C gamma : ℝ} (hC : 0 ≤ C) (hgamma : 0 < gamma)
    (beta tau sigma : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      actualCubicCarlsonNormalizedMovingLogFifthTail C beta tau sigma gamma m ≤
        actualCubicCarlsonNormalizedMovingLogFifthMajorant
          C beta tau sigma gamma m := by
  exact eventually_actualCubicCarlsonNormalizedMovingLogFifthTail_le_majorant
    hC hgamma beta tau sigma

example {C beta tau sigma gamma : ℝ}
    (hexponent : cubicCarlsonL2BlockExponent beta sigma tau gamma < 0) :
    Tendsto
      (actualCubicCarlsonNormalizedMovingLogFifthMajorant
        C beta tau sigma gamma) atTop (nhds 0) := by
  exact tendsto_actualCubicCarlsonNormalizedMovingLogFifthMajorant_zero hexponent

example {C beta tau sigma gamma : ℝ}
    (hC : 0 ≤ C) (hgamma : 0 < gamma)
    (hexponent : cubicCarlsonL2BlockExponent beta sigma tau gamma < 0) :
    Tendsto
      (actualCubicCarlsonNormalizedMovingLogFifthTail
        C beta tau sigma gamma) atTop (nhds 0) := by
  exact tendsto_actualCubicCarlsonNormalizedMovingLogFifthTail_zero
    hC hgamma hexponent

example {C beta : ℝ} (hC : 0 ≤ C)
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      0 < gammaLow ∧ gammaLow ≤ alpha ∧
      0 < gammaHigh ∧ gammaHigh < alpha ∧ 0 < alpha ∧
      Tendsto
        (actualCubicCarlsonNormalizedMovingLogFifthTail
          C beta tau sigma gammaLow) atTop (nhds 0) ∧
      Tendsto
        (actualCubicCarlsonNormalizedMovingLogFifthTail
          C beta tau sigma gammaHigh) atTop (nhds 0) ∧
      Tendsto
        (actualCubicCarlsonNormalizedMovingLogFifthTail
          C beta tau sigma alpha) atTop (nhds 0) := by
  exact exists_jointTwoHeightParameters_with_quantitative_cubicCarlsonTails
    hC hbeta hbetaOne

end PrimeNumberTheorem
