import PrimeNumberTheorem.ExplicitFormulaAllHeights

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x : ℝ} (hx : 2 ≤ x) :
    explicit_formula_von_mangoldt x hx :=
  explicit_formula_von_mangoldt_proved hx

end PrimeNumberTheorem.ExplicitFormulaResidues
