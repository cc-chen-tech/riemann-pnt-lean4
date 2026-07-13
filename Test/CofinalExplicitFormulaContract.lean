import PrimeNumberTheorem.CofinalExplicitFormula

open Complex Filter Set Topology

open scoped BigOperators Interval

namespace PrimeNumberTheorem.ExplicitFormulaResidues

example {x : ℝ} (hx : 1 < x) :
    ∃ T : ℕ → ℝ, StrictMono T ∧ Tendsto T atTop atTop ∧
      (∀ n : ℕ, T n ∈ Icc (2 * (n : ℝ) + 4) (2 * (n : ℝ) + 5) ∧
        0 < T n ∧ ExplicitFormulaAux.goodHeight (T n)) := by
  rcases exists_cofinal_nontrivialZeroSum_tendsto hx with
    ⟨T, hmono, htop, hgood, _hformula, _hremainder, _hzeros⟩
  exact ⟨T, hmono, htop, hgood⟩

end PrimeNumberTheorem.ExplicitFormulaResidues
