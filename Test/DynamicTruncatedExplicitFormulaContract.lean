import PrimeNumberTheorem.CofinalExplicitFormula

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), goodHeight T ∧
        ∀ (m N : ℕ), 3 ≤ m →
          ‖(∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)),
                -(((m : ℝ) : ℂ) ^ p) / p) +
              (((m : ℝ) : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
                ∑ ρ ∈ nontrivialZerosFinset T,
                  -(analyticOrderNatAt riemannZeta ρ : ℂ) *
                    (((m : ℝ) : ℂ) ^ ρ) / ρ) -
              (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
            C * (m : ℝ) *
                ((1 + Real.log (m : ℝ)) ^ 2 +
                  (1 + Real.log (A + 6)) ^ 2) / T +
              (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
                2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
                  Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
                (m : ℝ) ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
                (2 * Real.pi) :=
  exists_uniform_goodHeight_Icc_norm_nat_movingRight_truncatedExplicitFormula_sub_chebyshevPsi0_le

end ExplicitFormulaResidues
end PrimeNumberTheorem
