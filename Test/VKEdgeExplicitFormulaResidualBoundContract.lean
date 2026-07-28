import PrimeNumberTheorem.VKEdgeExplicitFormulaResidualBound

open Complex
open scoped ComplexConjugate
open PrimeNumberTheorem
open PrimeNumberTheorem.VKEdgePiOverTwo

namespace Test

#check
  (normalizedFiniteNontrivialZeroResidueRemainder :
    ℂ → ℝ → ℝ → ℂ)

#check
  (@norm_normalizedFiniteNontrivialZeroResidueRemainder_le :
    ∀ {rho0 : ℂ} {T delta y : ℝ},
      0 ≤ y →
      (∀ rho ∈
        ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
        rho.re ≤ rho0.re - delta) →
      ‖normalizedFiniteNontrivialZeroResidueRemainder rho0 T y‖ ≤
        ‖rho0‖ * Real.exp (-delta * y) *
          ExplicitFormulaAux.globalReciprocalZeroMultiplicity T)

#check
  (@norm_normalizedExplicitFormulaResidual_le_components :
    ∀ (rho0 : ℂ) (T y : ℝ),
      ‖normalizedExplicitFormulaResidual rho0 T y‖ ≤
        ‖rho0‖ * Real.exp (-rho0.re * y) *
          (|chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y)| +
            ‖finiteNontrivialZeroResidueRemainder
              (Real.exp y) T rho0‖ +
            ‖explicitFormulaClosedTerms y‖ +
            ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
              (chebyshevPsi0 (Real.exp y) : ℂ)‖))

#check
  (@norm_normalizedExplicitFormulaResidual_le_components_of_gap :
    ∀ {rho0 : ℂ} {T delta y : ℝ},
      0 ≤ y →
      (∀ rho ∈
        ((nontrivialZerosFinset T).erase rho0).erase (conj rho0),
        rho.re ≤ rho0.re - delta) →
      ‖normalizedExplicitFormulaResidual rho0 T y‖ ≤
        ‖rho0‖ * Real.exp (-rho0.re * y) *
            (|chebyshevPsi (Real.exp y) - chebyshevPsi0 (Real.exp y)| +
              ‖explicitFormulaClosedTerms y‖ +
              ‖explicitFormulaApproxWithMultiplicity (Real.exp y) T -
                (chebyshevPsi0 (Real.exp y) : ℂ)‖) +
          ‖rho0‖ * Real.exp (-delta * y) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity T)

end Test
