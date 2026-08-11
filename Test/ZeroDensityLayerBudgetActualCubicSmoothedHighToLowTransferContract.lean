import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicSmoothedHighToLowTransfer

open Filter Topology
open scoped BigOperators

namespace PrimeNumberTheorem

example (sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    actualCubicSmoothedStripEnergyUpTo sigma tau gamma S m =
      ∑ n ∈ Finset.range (actualCubicDyadicPolynomialCut gamma m + 1),
        actualCubicDyadicStripSquareCapacityExcluding (m : ℝ) sigma tau n S := rfl

example (sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) :
    actualCubicSmoothedStripEnergyBetween sigma tau gammaFrom gammaTo S m =
      ∑ n ∈ Finset.Ico
          (actualCubicDyadicPolynomialCut gammaFrom m + 1)
          (actualCubicDyadicPolynomialCut gammaTo m + 1),
        actualCubicDyadicStripSquareCapacityExcluding (m : ℝ) sigma tau n S := rfl

example (beta sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    actualCubicNormalizedSmoothedStripEnergyUpTo beta sigma tau gamma S m =
      (m : ℝ) ^ (-2 * beta) *
        actualCubicSmoothedStripEnergyUpTo sigma tau gamma S m := rfl

example (beta sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) :
    actualCubicNormalizedSmoothedStripEnergyBetween
        beta sigma tau gammaFrom gammaTo S m =
      (m : ℝ) ^ (-2 * beta) *
        actualCubicSmoothedStripEnergyBetween
          sigma tau gammaFrom gammaTo S m := rfl

example (x sigma tau : ℝ) (hx : 0 ≤ x) (n : ℕ) (S : Finset ℂ) :
    0 ≤ actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S :=
  actualCubicDyadicStripSquareCapacityExcluding_nonneg x sigma tau hx n S

example (sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicSmoothedStripEnergyUpTo sigma tau gamma S m :=
  actualCubicSmoothedStripEnergyUpTo_nonneg sigma tau gamma S m

example (sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicSmoothedStripEnergyBetween
      sigma tau gammaFrom gammaTo S m :=
  actualCubicSmoothedStripEnergyBetween_nonneg sigma tau gammaFrom gammaTo S m

example (beta sigma tau gammaFrom gammaTo : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicNormalizedSmoothedStripEnergyBetween
      beta sigma tau gammaFrom gammaTo S m :=
  actualCubicNormalizedSmoothedStripEnergyBetween_nonneg
    beta sigma tau gammaFrom gammaTo S m

example {sigma tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hcut : actualCubicDyadicPolynomialCut gammaFrom m ≤
      actualCubicDyadicPolynomialCut gammaTo m) :
    actualCubicSmoothedStripEnergyUpTo sigma tau gammaTo S m =
      actualCubicSmoothedStripEnergyUpTo sigma tau gammaFrom S m +
        actualCubicSmoothedStripEnergyBetween
          sigma tau gammaFrom gammaTo S m :=
  actualCubicSmoothedStripEnergyUpTo_eq_add_between hcut

example {beta sigma tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hcut : actualCubicDyadicPolynomialCut gammaFrom m ≤
      actualCubicDyadicPolynomialCut gammaTo m) :
    actualCubicNormalizedSmoothedStripEnergyUpTo
        beta sigma tau gammaTo S m =
      actualCubicNormalizedSmoothedStripEnergyUpTo
          beta sigma tau gammaFrom S m +
        actualCubicNormalizedSmoothedStripEnergyBetween
          beta sigma tau gammaFrom gammaTo S m :=
  actualCubicNormalizedSmoothedStripEnergyUpTo_eq_add_between hcut

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hm : 1 ≤ m) :
    actualCubicSmoothedStripEnergyBetween
        sigma tau gammaFrom gammaTo S m ≤
      actualCubicCarlsonDiagonalTail sigma tau gammaFrom S m :=
  certificate.actualCubicSmoothedStripEnergyBetween_le_diagonalTail hm

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gammaFrom gammaTo : ℝ} {S : Finset ℂ} {m : ℕ}
    (hm : 1 ≤ m) :
    actualCubicNormalizedSmoothedStripEnergyBetween
        beta sigma tau gammaFrom gammaTo S m ≤
      actualCubicCarlsonNormalizedDiagonalTail
        beta sigma tau gammaFrom S m :=
  certificate.actualCubicNormalizedSmoothedStripEnergyBetween_le_diagonalTail hm

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gammaFrom gammaTo : ℝ} (S : Finset ℂ)
    (htail : Tendsto
      (actualCubicCarlsonNormalizedDiagonalTail
        beta sigma tau gammaFrom S) atTop (nhds 0)) :
    Tendsto
      (actualCubicNormalizedSmoothedStripEnergyBetween
        beta sigma tau gammaFrom gammaTo S) atTop (nhds 0) :=
  certificate.tendsto_actualCubicNormalizedSmoothedStripEnergyBetween_zero_of_tail
    S htail

example {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gammaFrom gammaTo : ℝ}
    (hgamma : gammaFrom ≤ gammaTo) (S : Finset ℂ)
    (htail : Tendsto
      (actualCubicCarlsonNormalizedDiagonalTail
        beta sigma tau gammaFrom S) atTop (nhds 0)) :
    (∀ᶠ m : ℕ in atTop,
      actualCubicNormalizedSmoothedStripEnergyUpTo
          beta sigma tau gammaTo S m =
        actualCubicNormalizedSmoothedStripEnergyUpTo
            beta sigma tau gammaFrom S m +
          actualCubicNormalizedSmoothedStripEnergyBetween
            beta sigma tau gammaFrom gammaTo S m) ∧
      Tendsto
        (actualCubicNormalizedSmoothedStripEnergyBetween
          beta sigma tau gammaFrom gammaTo S) atTop (nhds 0) :=
  certificate.actualCubicSmoothedHighToLowTransfer_of_tail hgamma S htail

example {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      0 < gammaLow ∧ gammaLow ≤ alpha ∧
      0 < gammaHigh ∧ gammaHigh < alpha ∧ 0 < alpha ∧
      ∀ (certificate : CarlsonEventualMajorant sigma) (S : Finset ℂ),
        ((∀ᶠ m : ℕ in atTop,
          actualCubicNormalizedSmoothedStripEnergyUpTo
              beta sigma tau alpha S m =
            actualCubicNormalizedSmoothedStripEnergyUpTo
                beta sigma tau gammaLow S m +
              actualCubicNormalizedSmoothedStripEnergyBetween
                beta sigma tau gammaLow alpha S m) ∧
          Tendsto
            (actualCubicNormalizedSmoothedStripEnergyBetween
              beta sigma tau gammaLow alpha S) atTop (nhds 0)) ∧
        ((∀ᶠ m : ℕ in atTop,
          actualCubicNormalizedSmoothedStripEnergyUpTo
              beta sigma tau alpha S m =
            actualCubicNormalizedSmoothedStripEnergyUpTo
                beta sigma tau gammaHigh S m +
              actualCubicNormalizedSmoothedStripEnergyBetween
                beta sigma tau gammaHigh alpha S m) ∧
          Tendsto
            (actualCubicNormalizedSmoothedStripEnergyBetween
              beta sigma tau gammaHigh alpha S) atTop (nhds 0)) :=
  exists_jointTwoHeightParameters_with_actualCubicSmoothedHighToLowTransfers
    hbeta hbetaOne

end PrimeNumberTheorem
