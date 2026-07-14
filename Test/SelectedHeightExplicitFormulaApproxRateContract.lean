import PrimeNumberTheorem.CofinalExplicitFormula

open Complex Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

example {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), goodHeight T ∧
        ‖explicitFormulaApproxWithMultiplicity x T -
            (chebyshevPsi0 x : ℂ)‖ ≤
          C * (1 + Real.log (A + 6)) ^ 2 / T :=
  exists_goodHeight_Icc_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
    hx

end ExplicitFormulaResidues
end PrimeNumberTheorem
