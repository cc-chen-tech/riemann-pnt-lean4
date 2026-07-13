import PrimeNumberTheorem.QuantitativeGoodHeight

open Complex

namespace PrimeNumberTheorem.ExplicitFormulaAux

example :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ A : ℝ, 4 ≤ A →
      localZeroMultiplicity A ≤ B * (1 + Real.log (A + 6)) :=
  exists_localZeroMultiplicity_le_log_bound

end PrimeNumberTheorem.ExplicitFormulaAux
