import MathlibAux.LeftRegularizedLogDeriv

/-!
This contract fails if left-boundary roots are forbidden, if the continuous
trace is assumed instead of constructed, or if the residue includes the
removed left-boundary multiplicities. The same `G` must satisfy every clause.
-/

open Complex Set
open scoped BigOperators Interval

example {f : ℂ → ℂ} {x0 x1 U T : ℝ}
    (hx : x0 < x1) (hUT : U < T)
    (off left : Finset ℂ) (m : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[U, T]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[U, T]]),
      f z = 0 ↔ z ∈ off ∪ left)
    (hoff : ∀ p ∈ off, x0 < p.re ∧ p.re < x1 ∧ U < p.im ∧ p.im < T)
    (hleft : ∀ p ∈ left, p.re = x0 ∧ U < p.im ∧ p.im < T)
    (horder : ∀ p ∈ off ∪ left, analyticOrderAt f p = m p) :
    ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G (([[x0, x1]] ×ℂ [[U, T]]) \ (off : Set ℂ)) ∧
      (∀ z ∈ ([[x0, x1]] ×ℂ [[U, T]]), f z ≠ 0 →
        G z = logDeriv f z - ∑ p ∈ left, (z - p)⁻¹ * (m p : ℂ)) ∧
      ContinuousOn (fun t : ℝ => (G ((x0 : ℂ) + I * t)).re) (Icc U T) ∧
      (∀ t ∈ Icc U T, f ((x0 : ℂ) + I * t) ≠ 0 →
        (G ((x0 : ℂ) + I * t)).re =
          (logDeriv f ((x0 : ℂ) + I * t)).re) ∧
      MathlibAux.boundaryRectIntegral G x0 x1 U T =
        (2 * Real.pi * I) * ∑ p ∈ off, (m p : ℂ) := by
  exact MathlibAux.exists_left_regularized_logDeriv
    hx hUT off left m hf hzero hoff hleft horder

#print axioms MathlibAux.exists_left_regularized_logDeriv
