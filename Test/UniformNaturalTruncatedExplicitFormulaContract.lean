import PrimeNumberTheorem.CofinalExplicitFormula

open Complex Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), goodHeight T ∧
        ∀ (m N : ℕ), 2 ≤ m →
          ‖(∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)),
                -(((m : ℝ) : ℂ) ^ p) / p) +
              (((m : ℝ) : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
                ∑ ρ ∈ nontrivialZerosFinset T,
                  -(analyticOrderNatAt riemannZeta ρ : ℂ) *
                    (((m : ℝ) : ℂ) ^ ρ) / ρ) -
              (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
            C * ((m : ℝ) ^ 5 +
              (m : ℝ) ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2) / T +
              (((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
                2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
                  Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
                (m : ℝ) ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
                (2 * Real.pi) :=
  exists_uniform_goodHeight_Icc_norm_nat_truncatedExplicitFormula_sub_chebyshevPsi0_le

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      ∃ T ∈ Set.Icc ((m : ℝ) ^ 5) ((m : ℝ) ^ 5 + 1), goodHeight T ∧
        ‖(∑ p ∈ finiteTrivialZeroSum (2 * (2 : ℝ)),
              -(((m : ℝ) : ℂ) ^ p) / p) +
            (((m : ℝ) : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset T,
                -(analyticOrderNatAt riemannZeta ρ : ℂ) *
                  (((m : ℝ) : ℂ) ^ ρ) / ρ) -
            (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
          C * (1 + Real.log ((m : ℝ) ^ 5 + 9)) ^ 2 :=
  exists_nat_goodHeight_pow_five_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_log_sq

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      ∃ T ∈ Set.Icc ((m : ℝ) ^ 5) ((m : ℝ) ^ 5 + 1), goodHeight T ∧
        ‖(∑ p ∈ finiteTrivialZeroSum (2 * (2 : ℝ)),
              -(((m : ℝ) : ℂ) ^ p) / p) +
            (((m : ℝ) : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
              ∑ ρ ∈ nontrivialZerosFinset T,
                -(analyticOrderNatAt riemannZeta ρ : ℂ) *
                  (((m : ℝ) : ℂ) ^ ρ) / ρ) -
            (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
          C * (1 + Real.log (m : ℝ)) ^ 2 :=
  exists_nat_goodHeight_pow_five_norm_truncatedExplicitFormula_sub_chebyshevPsi0_le_log_nat_sq

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 2 ≤ m →
      ∃ T ∈ Set.Icc ((m : ℝ) ^ 5) ((m : ℝ) ^ 5 + 1), goodHeight T ∧
        ‖explicitFormulaApproxWithMultiplicity (m : ℝ) T -
            (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
          C * (1 + Real.log (m : ℝ)) ^ 2 :=
  exists_nat_goodHeight_pow_five_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_nat_sq

end ExplicitFormulaResidues
end PrimeNumberTheorem
