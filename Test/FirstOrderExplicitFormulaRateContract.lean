import PrimeNumberTheorem.FirstOrderExplicitFormula

open Complex Filter Topology Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

open ExplicitFormulaAux

example {x c : ℝ} (hx : 1 < x) (hc : 1 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (W : ℝ), 1 ≤ W →
      ExplicitFormulaAux.goodHeight (2 * Real.pi * W) →
      ‖((∑ p ∈ finiteTrivialZeroSum (2 * (N : ℝ)), -((x : ℂ) ^ p) / p) +
          ((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
            ∑ ρ ∈ nontrivialZerosFinset (2 * Real.pi * W),
              -(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ) -
          firstOrderContourRemainder x (-(2 * (N : ℝ) + 1)) c W) -
        (chebyshevPsi0 x : ℂ)‖ ≤ C / W :=
  exists_norm_truncatedExplicitFormula_sub_contourRemainder_sub_chebyshevPsi0_le_div
    hx hc

end ExplicitFormulaResidues
end PrimeNumberTheorem
