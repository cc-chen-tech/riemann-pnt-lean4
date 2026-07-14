import PrimeNumberTheorem.CofinalExplicitFormula

open Complex Set

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

example {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1), ExplicitFormulaAux.goodHeight T ∧
        ∀ N : ℕ,
          ‖firstOrderContourRemainder x (-(2 * (N : ℝ) + 1)) 2
              (T / (2 * Real.pi))‖ ≤
            (C * (1 + Real.log (A + 6)) ^ 2 / T +
              ((vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
                2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
                  Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
                x ^ (-(2 * (N : ℝ) + 1))) * (2 * T)) /
              (2 * Real.pi) :=
  exists_goodHeight_Icc_norm_firstOrderContourRemainder_le_horizontal_add_left hx

end ExplicitFormulaResidues
end PrimeNumberTheorem
