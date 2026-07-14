import PrimeNumberTheorem.ExplicitFormulaAllHeights

open Complex

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

example {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 8 ≤ T →
      ‖explicitFormulaApproxWithMultiplicity x T -
          (chebyshevPsi0 x : ℂ)‖ ≤
        C * (1 + Real.log (T + 8)) ^ 2 / T :=
  exists_norm_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le_log_sq_div
    hx

end ExplicitFormulaResidues
end PrimeNumberTheorem
