import PrimeNumberTheorem.CentralHorizontalEdge

open Complex MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

example {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧ ∀ {a : ℝ}, a ≤ -1 →
          ‖(∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * (-T))) -
            (∫ σ : ℝ in a..2,
                explicitFormulaIntegrand x ((σ : ℂ) + I * T))‖ ≤
            C * (1 + Real.log (A + 6)) ^ 2 / T :=
  exists_goodHeight_Icc_norm_horizontal_complete_explicitFormulaContour_difference_le hx

end ExplicitFormulaResidues
end PrimeNumberTheorem
