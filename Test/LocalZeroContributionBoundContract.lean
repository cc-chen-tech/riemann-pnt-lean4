import PrimeNumberTheorem.QuantitativeGoodHeight

open Filter Topology

namespace PrimeNumberTheorem.ExplicitFormulaAux

example {x : ℝ} (hx : 1 < x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      localZeroContributionNorm x A ≤
        C * x * (1 + Real.log (A + 6)) / (A - 1 / 2) :=
  exists_localZeroContributionNorm_le_log_div hx

example {x : ℝ} (hx : 1 < x) :
    Tendsto (localZeroContributionNorm x) atTop (𝓝 0) :=
  tendsto_localZeroContributionNorm_atTop hx

end PrimeNumberTheorem.ExplicitFormulaAux
