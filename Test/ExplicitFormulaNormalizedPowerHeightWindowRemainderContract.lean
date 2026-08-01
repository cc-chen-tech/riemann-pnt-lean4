import PrimeNumberTheorem.ExplicitFormulaNormalizedPowerHeightWindowRemainder

open Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

#check
  (eventually_exists_uniform_goodHeight_normalized_powerHeight_proportional_window_remainder_lt :
    ∀ {beta gammaLow ε eta : ℝ},
      1 / 2 < beta →
      beta < 1 →
      0 < gammaLow →
      gammaLow < beta →
      (1 - beta) * (1 + ε) < gammaLow →
      0 < ε →
      0 < eta →
      ∀ᶠ a : ℝ in atTop,
        ∃ Tlow ∈
            Set.Icc
              (Real.exp (gammaLow * a))
              (Real.exp (gammaLow * a) + 1),
          ExplicitFormulaAux.goodHeight Tlow ∧
            ∀ y ∈ Set.Icc a ((1 + ε) * a),
              Real.exp (-beta * y) *
                  ‖explicitFormulaApproxWithMultiplicity (Real.exp y) Tlow -
                    (chebyshevPsi0 (Real.exp y) : ℂ)‖ < eta)

end ExplicitFormulaResidues
end PrimeNumberTheorem
