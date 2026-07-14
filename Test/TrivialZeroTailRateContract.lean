import PrimeNumberTheorem.ExplicitFormulaAux

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

example {x : ℝ} (hx : 1 < x) (N : ℕ) :
    ‖(∑ ρ ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ ρ) / ρ) -
        (((-(1 / 2 : ℝ) * Real.log (1 - x ^ (-2 : ℝ)) : ℝ) : ℂ))‖ ≤
      (x ^ (-2 : ℝ) / 2) * (x ^ (-2 : ℝ)) ^ N /
        (1 - x ^ (-2 : ℝ)) :=
  norm_finiteTrivialZeroSum_residues_sub_logTerm_le_geometric hx N

end ExplicitFormulaAux
end PrimeNumberTheorem
