import PrimeNumberTheorem.ExplicitFormulaUniformNaturalHeight

open Complex Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

#check exists_uniform_goodHeight_Icc_norm_nat_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
        ∀ m : ℕ, 3 ≤ m →
          ‖explicitFormulaApproxWithMultiplicity (m : ℝ) T -
              (chebyshevPsi0 (m : ℝ) : ℂ)‖ ≤
            C * (m : ℝ) *
              ((1 + Real.log (m : ℝ)) ^ 2 +
                (1 + Real.log (A + 6)) ^ 2) / T :=
  exists_uniform_goodHeight_Icc_norm_nat_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le

end ExplicitFormulaResidues
end PrimeNumberTheorem
