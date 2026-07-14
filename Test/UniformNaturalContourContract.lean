import PrimeNumberTheorem.CofinalExplicitFormula

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x a T : ℝ}, 2 ≤ x → a ≤ -1 → 1 ≤ |T| →
      IntervalIntegrable
          (fun σ : ℝ => explicitFormulaIntegrand x ((σ : ℂ) + T * I))
          volume a (-1) ∧
        ‖∫ σ : ℝ in a..(-1),
            explicitFormulaIntegrand x ((σ : ℂ) + T * I)‖ ≤
          C * (1 + Real.log (1 + |T|)) / |T| :=
  exists_uniform_norm_integral_farLeft_explicit_le_log_div

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧ ∀ {x : ℝ}, 2 ≤ x →
          ∀ {a : ℝ}, a ≤ -1 →
          ‖(∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) -
            (∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * T))‖ ≤
            C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T :=
  exists_uniform_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le

end ExplicitFormulaResidues
end PrimeNumberTheorem
