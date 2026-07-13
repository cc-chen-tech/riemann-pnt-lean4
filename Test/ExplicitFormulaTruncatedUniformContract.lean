import PrimeNumberTheorem.ExplicitFormulaTruncated

open Complex

namespace PrimeNumberTheorem.ExplicitFormulaTruncated

example : ExplicitFormulaTruncatedTarget ↔
    ∀ x : ℝ, 2 ≤ x → ∃ C > (0 : ℝ), ∀ T : ℝ, 2 ≤ T →
      ‖((ExplicitFormulaAux.chebyshevPsi0 x : ℂ) -
        ((x : ℂ)
          - PrimeNumberTheorem.finiteNontrivialZeroSumWithMultiplicity x T
          - (Real.log (2 * Real.pi) : ℂ)
          - (1 / 2 : ℂ) * (Real.log (1 - x ^ (-2 : ℝ)) : ℂ)))‖
        ≤ C * x / T * (Real.log (x * T)) ^ 2 := by
  rfl

end PrimeNumberTheorem.ExplicitFormulaTruncated
