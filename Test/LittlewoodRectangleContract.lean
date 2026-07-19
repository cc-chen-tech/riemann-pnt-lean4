import PrimeNumberTheorem.LittlewoodRectangle

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ) (anchor : ℂ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ => (z - anchor) * logDeriv f z)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ poles, (rho - anchor) * (multiplicity rho : ℂ) :=
  boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
    poles multiplicity anchor hf hzero horder hpoles

#print axioms boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum

end CarlsonZeroDensity
end PrimeNumberTheorem
