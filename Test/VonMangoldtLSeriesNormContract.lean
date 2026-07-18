import PrimeNumberTheorem.RightHorizontalEdge

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The von Mangoldt Dirichlet-series norm has the expected quadratic growth
as its real part approaches one from the right. -/
example {ε : ℝ} (hε : 0 < ε) :
    vonMangoldtLSeriesNorm ε ≤
      (2 / ε) * (1 + 2 / ε) :=
  vonMangoldtLSeriesNorm_le_two_div_mul_one_add_two_div hε

end ExplicitFormulaResidues
end PrimeNumberTheorem
