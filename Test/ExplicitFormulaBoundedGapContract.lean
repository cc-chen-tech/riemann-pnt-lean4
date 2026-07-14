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

end PrimeNumberTheorem.ExplicitFormulaResidues
