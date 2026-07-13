import PrimeNumberTheorem

open Complex Filter Topology

open scoped BigOperators

namespace PrimeNumberTheorem

example (x T : ℝ) :
    finiteNontrivialZeroSumWithMultiplicity x T =
      ∑ ρ ∈ nontrivialZerosFinset T,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  rfl

example {x : ℝ} {hx : x ≥ 2} :
    explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ => explicitFormulaApproxWithMultiplicity x T)
        atTop (𝓝 (chebyshevPsi0 x : ℂ)) := by
  rfl

end PrimeNumberTheorem
