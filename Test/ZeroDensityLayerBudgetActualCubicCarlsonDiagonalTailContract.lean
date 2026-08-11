import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonDiagonalTail

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) (B : ℝ) :
    actualCubicCarlsonUniformCoefficient certificate B =
      192 * B * certificate.C * Real.log 2 ^ 5 := rfl

example (sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    actualCubicCarlsonDiagonalTail sigma tau gamma S m =
      ∑' n : ℕ,
        actualCubicDyadicStripSquareCapacityExcluding
          (m : ℝ) sigma tau
          (n + (actualCubicDyadicPolynomialCut gamma m + 1)) S := rfl

example (beta sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    actualCubicCarlsonNormalizedDiagonalTail beta sigma tau gamma S m =
      (m : ℝ) ^ (-2 * beta) *
        actualCubicCarlsonDiagonalTail sigma tau gamma S m := rfl

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ x tau : ℝ, 1 ≤ x →
      actualCubicDyadicCountMajorant B x sigma tau n ≤
        actualCubicCarlsonCertificateBlockMajorant certificate B x tau n := by
  exact certificate.eventually_forall_actualCubicDyadicCountMajorant_le hB

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ x tau : ℝ, 1 ≤ x →
      actualCubicCarlsonCertificateBlockMajorant certificate B x tau n ≤
        actualCubicCarlsonDyadicLogFifthMajorant
          (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
          sigma n := by
  exact certificate.eventually_forall_actualCubicCertificateBlock_le_logFifth hB

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ n : ℕ in atTop, ∀ x tau : ℝ, 1 ≤ x → ∀ S : Finset ℂ,
        actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
          actualCubicCarlsonDyadicLogFifthMajorant
            (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
            sigma n := by
  exact certificate.exists_eventually_forall_actualCubicCapacity_le_logFifth

example (a C sigma : ℝ) (N : ℕ) :
    actualCubicCarlsonDyadicLogFifthTail (a * C) sigma N =
      a * actualCubicCarlsonDyadicLogFifthTail C sigma N := by
  exact actualCubicCarlsonDyadicLogFifthTail_mul_coefficient a C sigma N

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {gamma : ℝ} (hgamma : 0 < gamma) (tau : ℝ) (S : Finset ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ m : ℕ in atTop,
        actualCubicCarlsonDiagonalTail sigma tau gamma S m ≤
          actualCubicCarlsonDyadicLogFifthTail
            (actualCubicCarlsonUniformCoefficient certificate B *
              (m : ℝ) ^ (2 * tau)) sigma
            (actualCubicDyadicPolynomialCut gamma m) := by
  exact certificate.exists_eventually_actualCubicCarlsonDiagonalTail_le
    hgamma tau S

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta gamma : ℝ} (hgamma : 0 < gamma) (tau : ℝ) (S : Finset ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ m : ℕ in atTop,
        actualCubicCarlsonNormalizedDiagonalTail beta sigma tau gamma S m ≤
          actualCubicCarlsonNormalizedMovingLogFifthTail
            (actualCubicCarlsonUniformCoefficient certificate B)
            beta tau sigma gamma m := by
  exact certificate.eventually_actualCubicCarlsonNormalizedDiagonalTail_le
    hgamma tau S

example (beta sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicCarlsonNormalizedDiagonalTail beta sigma tau gamma S m := by
  exact actualCubicCarlsonNormalizedDiagonalTail_nonneg
    beta sigma tau gamma S m

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gamma : ℝ} (hgamma : 0 < gamma)
    (hexponent : cubicCarlsonL2BlockExponent beta sigma tau gamma < 0)
    (S : Finset ℂ) :
    Tendsto
      (actualCubicCarlsonNormalizedDiagonalTail beta sigma tau gamma S)
      atTop (nhds 0) := by
  exact certificate.tendsto_actualCubicCarlsonNormalizedDiagonalTail_zero
    hgamma hexponent S

example {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      0 < gammaLow ∧ gammaLow ≤ alpha ∧
      0 < gammaHigh ∧ gammaHigh < alpha ∧ 0 < alpha ∧
      ∀ certificate : CarlsonEventualMajorant sigma, ∀ S : Finset ℂ,
        Tendsto
          (actualCubicCarlsonNormalizedDiagonalTail
            beta sigma tau gammaLow S) atTop (nhds 0) ∧
        Tendsto
          (actualCubicCarlsonNormalizedDiagonalTail
            beta sigma tau gammaHigh S) atTop (nhds 0) ∧
        Tendsto
          (actualCubicCarlsonNormalizedDiagonalTail
            beta sigma tau alpha S) atTop (nhds 0) := by
  exact exists_jointTwoHeightParameters_with_actualCubicCarlsonDiagonalTails
    hbeta hbetaOne

end PrimeNumberTheorem
