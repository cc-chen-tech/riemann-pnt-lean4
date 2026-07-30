import PrimeNumberTheorem.ExplicitFormulaNormalizedWindowRemainder

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

#check
  (tendsto_normalizedWindowRemainderEnvelope_proportional_atTop_nhds_zero :
    ∀ {C D beta ε : ℝ},
      1 / 2 < beta →
      beta < 1 →
      (1 - beta) * ε < beta - 1 / 2 →
      Tendsto
        (fun a =>
          normalizedWindowRemainderEnvelope C D beta (ε * a) a)
        atTop (nhds 0))

#check
  (eventually_exists_uniform_goodHeight_normalized_proportional_window_remainder_lt :
    ∀ {beta ε eta : ℝ},
      1 / 2 < beta →
      beta < 1 →
      0 < ε →
      (1 - beta) * ε < beta - 1 / 2 →
      0 < eta →
      ∀ᶠ a : ℝ in atTop,
        ∃ T ∈ Set.Icc (Real.exp (a / 2)) (Real.exp (a / 2) + 1),
          ExplicitFormulaAux.goodHeight T ∧
            ∀ y ∈ Set.Icc a ((1 + ε) * a),
              Real.exp (-beta * y) *
                  ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                    (chebyshevPsi0 (Real.exp y) : ℂ)‖ < eta)

end ExplicitFormulaResidues
end PrimeNumberTheorem
