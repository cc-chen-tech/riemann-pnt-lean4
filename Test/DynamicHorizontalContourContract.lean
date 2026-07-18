import PrimeNumberTheorem.CentralHorizontalEdge

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ (m : ℕ) {a : ℝ}, 3 ≤ m → a ≤ -1 →
            ‖(∫ σ : ℝ in a..(1 + 1 / Real.log (m : ℝ)),
                  explicitFormulaIntegrand (m : ℝ)
                    ((σ : ℂ) + I * (-T))) -
              (∫ σ : ℝ in a..(1 + 1 / Real.log (m : ℝ)),
                  explicitFormulaIntegrand (m : ℝ)
                    ((σ : ℂ) + I * T))‖ ≤
              C * (m : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T :=
  exists_uniform_goodHeight_Icc_norm_nat_movingRight_horizontal_complete_explicitFormulaContour_difference_le

end ExplicitFormulaResidues
end PrimeNumberTheorem
