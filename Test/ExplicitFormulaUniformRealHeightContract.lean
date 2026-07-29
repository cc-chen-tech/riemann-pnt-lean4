import PrimeNumberTheorem.ExplicitFormulaUniformRealHeight

open Complex Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

#check exists_uniform_goodHeight_Icc_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 8 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
        ∀ x : ℝ, 3 ≤ x →
          ‖explicitFormulaApproxWithMultiplicity x T -
              (chebyshevPsi0 x : ℂ)‖ ≤
            C * x *
                ((1 + Real.log x) ^ 2 +
                  (1 + Real.log (A + 6)) ^ 2) / T +
              (1 + D * T * (1 + Real.log (T + 6))) +
              2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
              Real.log x :=
  exists_uniform_goodHeight_Icc_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le

end ExplicitFormulaResidues
end PrimeNumberTheorem
