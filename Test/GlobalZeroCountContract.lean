import PrimeNumberTheorem.GlobalZeroCount

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      globalZeroMultiplicity T ≤ C * T * (1 + Real.log (T + 6)) :=
  exists_globalZeroMultiplicity_le_mul_log

example :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      ((nontrivialZerosFinset T).card : ℝ) ≤
        C * T * (1 + Real.log (T + 6)) :=
  exists_card_nontrivialZerosFinset_le_mul_log

end ExplicitFormulaAux
end PrimeNumberTheorem
