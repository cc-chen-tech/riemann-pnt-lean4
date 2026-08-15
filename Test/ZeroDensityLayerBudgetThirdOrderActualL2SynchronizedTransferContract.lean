import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderActualL2SynchronizedTransfer

open Complex Set Filter Topology
open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem

example {beta c : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1)
    (hc : 1 < c) (hcTwo : c ≤ 2) :
    ∃ sigma tau gammaLow : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      0 < gammaLow ∧ gammaLow ≤ (3 / 4 : ℝ) ∧
      cubicCarlsonL2BlockExponent beta sigma tau gammaLow < 0 ∧
      ∀ (certificate : CarlsonEventualMajorant sigma) (S : Finset ℂ)
          (ε : ℝ), 0 < ε →
        ∀ᶠ m : ℕ in atTop,
          ∃ T ∈ Icc ((m : ℝ) ^ (3 / 4 : ℝ))
              ((m : ℝ) ^ (3 / 4 : ℝ) + 1),
            ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
              ExplicitFormulaAux.goodHeight T ∧
              ‖ExplicitFormulaResidues.thirdOrderContourRemainder
                  (m : ℝ) (-1) c (T / (2 * Real.pi))‖ < ε ∧
              0 ∈ poles ∧
              (∀ p ∈ poles, (-1 : ℝ) < p.re ∧ p.re < c ∧
                -T < p.im ∧ p.im < T) ∧
              (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
              (∀ p ∈ poles, residue p =
                if p = 0 then residue 0
                else if p = 1 then ((m : ℝ) : ℂ)
                else -(analyticOrderNatAt riemannZeta p : ℂ) *
                  (((m : ℝ) : ℂ) ^ p) / p ^ 3) ∧
              residue 0 =
                iteratedDeriv 2
                  (ExplicitFormulaResidues.thirdOrderZeroCore (m : ℝ)) 0 / 2 ∧
              cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
              (m : ℝ) ^ (-beta) *
                  ‖(∑ p ∈ poles, residue p) -
                    ExplicitFormulaResidues.thirdOrderContourRemainder
                      (m : ℝ) (-1) c (T / (2 * Real.pi)) -
                    (secondSmoothedChebyshevPsi (m : ℝ) : ℂ)‖ < ε ∧
              actualCubicNormalizedSmoothedStripEnergyUpTo
                  beta sigma tau (3 / 4 : ℝ) S m =
                actualCubicNormalizedSmoothedStripEnergyUpTo
                    beta sigma tau gammaLow S m +
                  actualCubicNormalizedSmoothedStripEnergyBetween
                    beta sigma tau gammaLow (3 / 4 : ℝ) S m ∧
              actualCubicNormalizedSmoothedStripEnergyBetween
                  beta sigma tau gammaLow (3 / 4 : ℝ) S m < ε :=
  exists_actualThirdOrderPsiFormula_with_cubicHighToLowL2Tail
    hbeta hbetaOne hc hcTwo

end PrimeNumberTheorem
