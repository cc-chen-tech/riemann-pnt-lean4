import MathlibAux.LogDerivArgumentPrinciple

open Complex Set
open scoped BigOperators Interval

example {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (zeros : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]]),
      f z = 0 ↔ z ∈ zeros)
    (hinside : ∀ rho ∈ zeros,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1)
    (horder : ∀ rho ∈ zeros,
      analyticOrderAt f rho = multiplicity rho) :
    MathlibAux.boundaryRectIntegral (logDeriv f) x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ zeros, (multiplicity rho : ℂ) :=
  MathlibAux.boundaryRectIntegral_logDeriv_eq_finite_zero_multiplicity_sum
    zeros multiplicity hf hzero hinside horder
