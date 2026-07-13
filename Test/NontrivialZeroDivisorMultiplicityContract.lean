import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex Metric

namespace PrimeNumberTheorem

example {c ρ : ℂ} {R : ℝ} (hρ : RiemannHypothesis.IsNontrivialZero ρ)
    (hmem : ρ ∈ closedBall c R) :
    MeromorphicOn.divisor riemannZeta (closedBall c R) ρ =
      (analyticOrderNatAt riemannZeta ρ : ℤ) :=
  divisor_riemannZeta_closedBall_eq_analyticOrderNatAt_of_nontrivialZero hρ hmem

end PrimeNumberTheorem
