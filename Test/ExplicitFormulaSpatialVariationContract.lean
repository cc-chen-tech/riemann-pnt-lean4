import PrimeNumberTheorem.ExplicitFormulaSpatialVariation

open Complex
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

#check norm_zeroTerm_sub_zeroTerm_le_abs_sub
#check norm_finiteNontrivialZeroSumWithMultiplicity_sub_le
#check norm_main_sub_finiteZeroSum_sub_le
#check exists_norm_main_sub_finiteZeroSum_sub_le_mul_log

example {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    {x m : ℝ} (hx : 1 ≤ x) (hm : 1 ≤ m) :
    ‖(x : ℂ) ^ rho / rho - (m : ℂ) ^ rho / rho‖ ≤
      |x - m| :=
  norm_zeroTerm_sub_zeroTerm_le_abs_sub hrho hx hm

example {x m T : ℝ} (hx : 1 ≤ x) (hm : 1 ≤ m) :
    ‖finiteNontrivialZeroSumWithMultiplicity x T -
        finiteNontrivialZeroSumWithMultiplicity m T‖ ≤
      globalZeroMultiplicity T * |x - m| :=
  norm_finiteNontrivialZeroSumWithMultiplicity_sub_le hx hm

example {x m T : ℝ} (hx : 1 ≤ x) (hm : 1 ≤ m) :
    ‖((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
        ((m : ℂ) - finiteNontrivialZeroSumWithMultiplicity m T)‖ ≤
      (1 + globalZeroMultiplicity T) * |x - m| :=
  norm_main_sub_finiteZeroSum_sub_le hx hm

example :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {x m T : ℝ}, 1 ≤ x → 1 ≤ m → 4 ≤ T →
        ‖((x : ℂ) - finiteNontrivialZeroSumWithMultiplicity x T) -
            ((m : ℂ) - finiteNontrivialZeroSumWithMultiplicity m T)‖ ≤
          (1 + C * T * (1 + Real.log (T + 6))) * |x - m| :=
  exists_norm_main_sub_finiteZeroSum_sub_le_mul_log

end ExplicitFormulaAux
end PrimeNumberTheorem
