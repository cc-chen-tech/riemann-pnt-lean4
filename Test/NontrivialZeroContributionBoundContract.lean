import PrimeNumberTheorem.NontrivialZeroMultiplicity

open Complex

namespace PrimeNumberTheorem

example {x T : ℝ} {ρ : ℂ} (hx : 1 < x) (hT : 0 < T)
    (hρ : RiemannHypothesis.IsNontrivialZero ρ) (hheight : T < |ρ.im|) :
    ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
      (analyticOrderNatAt riemannZeta ρ : ℝ) * x / T :=
  norm_multiplicity_zero_contribution_le_div_height hx hT hρ hheight

end PrimeNumberTheorem
