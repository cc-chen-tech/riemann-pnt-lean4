import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex Metric
open scoped BigOperators

namespace PrimeNumberTheorem

example {c : ℂ} {R : ℝ} (S : Finset ℂ)
    (havoid : ∀ z : ℂ, z ∈ closedBall c R → z ≠ 1)
    (hS : ∀ ρ ∈ S,
      RiemannHypothesis.IsNontrivialZero ρ ∧ ρ ∈ closedBall c R) :
    (∑ ρ ∈ S, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
      ∑ᶠ u, (MeromorphicOn.divisor riemannZeta (closedBall c R) u : ℝ) :=
  sum_analyticOrderNatAt_riemannZeta_le_finsum_divisor_closedBall
    S havoid hS

end PrimeNumberTheorem
