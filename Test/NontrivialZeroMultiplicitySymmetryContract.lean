import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex

namespace PrimeNumberTheorem

example {ρ : ℂ} (hρ : RiemannHypothesis.IsNontrivialZero ρ) :
    analyticOrderNatAt riemannZeta (1 - ρ) =
      analyticOrderNatAt riemannZeta ρ :=
  analyticOrderNatAt_riemannZeta_one_sub_of_nontrivialZero hρ

end PrimeNumberTheorem
