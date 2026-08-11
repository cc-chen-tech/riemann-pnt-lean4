import PrimeNumberTheorem.ZeroDensityLayerBudgetThirdOrderActualSynchronizedFormula

open Complex Set Filter Topology
open scoped ArithmeticFunction BigOperators

namespace PrimeNumberTheorem

example {c T : ℝ} (hc : 1 < c) (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∀ p ∈ uIcc (-1 : ℝ) c ×ℂ uIcc (-T) T,
      p = 1 ∨ riemannZeta p = 0 →
        (-1 : ℝ) < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T :=
  thirdOrderExplicitFormulaBoundary_of_goodHeight hc hT hgood

example {beta c : ℝ} (hbeta : 2 / 3 < beta)
    (hc : 1 < c) (hcTwo : c ≤ 2) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ x : ℝ in atTop,
        ∃ T ∈ Icc (x ^ (3 / 4 : ℝ)) (x ^ (3 / 4 : ℝ) + 1),
          ∃ (poles : Finset ℂ) (residue : ℂ → ℂ) (cubic : ℂ),
            ExplicitFormulaAux.goodHeight T ∧
            ‖ExplicitFormulaResidues.thirdOrderContourRemainder
                x (-1) c (T / (2 * Real.pi))‖ < ε ∧
            0 ∈ poles ∧
            (∀ p ∈ poles, (-1 : ℝ) < p.re ∧ p.re < c ∧
              -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p ∈ poles, residue p =
              if p = 0 then residue 0
              else if p = 1 then (x : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                (x : ℂ) ^ p / p ^ 3) ∧
            residue 0 =
              iteratedDeriv 2
                (ExplicitFormulaResidues.thirdOrderZeroCore x) 0 / 2 ∧
            cubic = -deriv riemannZeta 0 / riemannZeta 0 ∧
            x ^ (-beta) *
                ‖(∑ p ∈ poles, residue p) -
                  ExplicitFormulaResidues.thirdOrderContourRemainder
                    x (-1) c (T / (2 * Real.pi)) -
                  (secondSmoothedChebyshevPsi x : ℂ)‖ < ε :=
  eventually_exists_goodHeight_thirdOrderActualPsiFormula_normalized_error_lt
    hbeta hc hcTwo

end PrimeNumberTheorem
