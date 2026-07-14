import PrimeNumberTheorem.CofinalExplicitFormula

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

example {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), goodHeight T ∧ ∀ N : ℕ,
        ‖(∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
            ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset T,
                -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
            (chebyshevPsi0 x : ℂ)‖ ≤
          C * (1 + Real.log (A + 6)) ^ 2 / T +
            (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
              2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
                Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
              x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
              (2 * Real.pi) :=
  exists_goodHeight_Icc_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_horizontal_add_left
    hx

end ExplicitFormulaResidues
end PrimeNumberTheorem
