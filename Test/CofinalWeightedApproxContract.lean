import PrimeNumberTheorem.CofinalExplicitFormula

open Filter Set Topology

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x : ℝ} (hx : 1 < x) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ, T n ∈ Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) ∧
        ExplicitFormulaAux.goodHeight (T n)) ∧
      Tendsto
        (fun n : ℕ => explicitFormulaApproxWithMultiplicity x (T n))
        atTop (𝓝 (chebyshevPsi0 x : ℂ)) := by
  exact exists_cofinal_explicitFormulaApproxWithMultiplicity_tendsto hx

end PrimeNumberTheorem.ExplicitFormulaResidues
