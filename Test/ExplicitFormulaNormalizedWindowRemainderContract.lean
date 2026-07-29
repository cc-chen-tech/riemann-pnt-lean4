import PrimeNumberTheorem.ExplicitFormulaNormalizedWindowRemainder

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

#check tendsto_exp_mul_one_add_sq_atTop_nhds_zero_of_neg
#check exists_uniform_goodHeight_exp_half_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le
#check normalizedWindowRemainderEnvelope
#check tendsto_normalizedWindowRemainderEnvelope_atTop_nhds_zero
#check eventually_exists_uniform_goodHeight_normalized_window_remainder_lt

example {c : ℝ} (hc : c < 0) :
    Tendsto (fun a : ℝ => Real.exp (c * a) * (1 + a) ^ 2)
      atTop (nhds 0) :=
  tendsto_exp_mul_one_add_sq_atTop_nhds_zero_of_neg hc

example :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ a : ℝ, 8 ≤ Real.exp (a / 2) →
        ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ∀ y : ℝ, Real.log 3 ≤ y →
              ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                  (chebyshevPsi0 (Real.exp y) : ℂ)‖ ≤
                C * Real.exp y *
                    ((1 + y) ^ 2 +
                      (1 + Real.log (Real.exp (a / 2) + 6)) ^ 2) / T +
                  (1 + D * T * (1 + Real.log (T + 6))) +
                  2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound +
                  y :=
  exists_uniform_goodHeight_exp_half_norm_real_explicitFormulaApproxWithMultiplicity_sub_chebyshevPsi0_le

example (C D beta L a : ℝ) :
    normalizedWindowRemainderEnvelope C D beta L a =
      C * Real.exp ((1 - beta) * L) *
          (Real.exp ((1 / 2 - beta) * a) *
            ((1 + a + L) ^ 2 + (2 + a) ^ 2)) +
        2 * D * Real.exp ((1 / 2 - beta) * a) * (2 + a) +
        Real.exp (-beta * a) *
          (1 + 2 * VKEdgePiOverTwo.zeroPackageClosedTermsUniformBound + a + L) :=
  rfl

example {C D beta L : ℝ} (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1) :
    Tendsto (normalizedWindowRemainderEnvelope C D beta L)
      atTop (nhds 0) :=
  tendsto_normalizedWindowRemainderEnvelope_atTop_nhds_zero hbeta hbeta1

example {beta L eta : ℝ}
    (hbeta : 1 / 2 < beta) (hbeta1 : beta < 1)
    (hL : 0 ≤ L) (heta : 0 < eta) :
    ∀ᶠ a in atTop,
      ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ y ∈ Set.Icc a (a + L),
            Real.exp (-beta * y) *
                ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                    (chebyshevPsi0 (Real.exp y) : ℂ)‖ < eta :=
  eventually_exists_uniform_goodHeight_normalized_window_remainder_lt
    hbeta hbeta1 hL heta

end ExplicitFormulaResidues
end PrimeNumberTheorem
