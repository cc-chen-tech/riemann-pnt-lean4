import PrimeNumberTheorem.CarlsonGeometricSummation

set_option autoImplicit false
open Filter
open PrimeNumberTheorem

example {F : ℝ → ℝ} {r q C : ℝ} {B : ℕ}
    (hF : Monotone F) (hF0 : ∀ T, 0 ≤ F T)
    (hr : 1 < r) (hq : 0 < q) (hC : 0 < C)
    (hstep : ∀ᶠ U : ℝ in atTop,
      F (r * U) ≤ F U + C * U ^ q * (1 + Real.log U) ^ B) :
    ∃ K > (0 : ℝ), ∀ᶠ T : ℝ in atTop,
      F T ≤ K * T ^ q * (1 + Real.log T) ^ B :=
  exists_eventually_powerLog_bound_of_geometric_step hF hF0 hr hq hC hstep

#print axioms exists_eventually_powerLog_bound_of_geometric_step
