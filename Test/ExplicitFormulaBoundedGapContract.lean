import PrimeNumberTheorem.ExplicitFormulaAllHeights

open Complex

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x T U : ℝ} (hTU : T ≤ U) (hUT : U ≤ T + 3) :
    ‖explicitFormulaApproxWithMultiplicity x T -
        explicitFormulaApproxWithMultiplicity x U‖ ≤
      ExplicitFormulaAux.localZeroContributionNorm x (T + 1 / 4) +
        ExplicitFormulaAux.localZeroContributionNorm x (T + 7 / 4) :=
  norm_explicitFormulaApproxWithMultiplicity_sub_le_two_localWindows
    hTU hUT

example {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T U : ℝ}, 4 ≤ T → T ≤ U → U ≤ T + 3 →
      ‖explicitFormulaApproxWithMultiplicity x T -
          explicitFormulaApproxWithMultiplicity x U‖ ≤
        2 * C * x * (1 + Real.log (T + 8)) / (T - 1 / 2) :=
  exists_norm_explicitFormulaApproxWithMultiplicity_sub_le_log_div_of_le_add_three hx

end PrimeNumberTheorem.ExplicitFormulaResidues
