import MathlibAux.HalfBoundaryArgumentPrinciple

/-!
The real trace must be constructed, not assumed. This checks the full oriented
identity with interior weight one and left-boundary weight one half, permitting
left-edge zeros but excluding other edges/corners via the exact zero geometry.
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
    ∃ q : ℝ → ℝ,
      ContinuousOn q (Icc U T) ∧
      (∀ t ∈ Icc U T, f ((x0 : ℂ) + I * t) ≠ 0 →
        q t = (logDeriv f ((x0 : ℂ) + I * t)).re) ∧
      (∫ x in x0..x1, (logDeriv f ((x : ℂ) + I * U)).im) +
        (∫ t in U..T, (logDeriv f ((x1 : ℂ) + I * t)).re) -
        (∫ x in x0..x1, (logDeriv f ((x : ℂ) + I * T)).im) -
        (∫ t in U..T, q t) =
          2 * Real.pi * ((∑ p ∈ off, (m p : ℝ)) + (∑ p ∈ left, (m p : ℝ)) / 2) := by
  exact MathlibAux.exists_regularized_trace_half_boundary_argument
    hx hUT off left m hf hzero hoff hleft horder

#print axioms MathlibAux.exists_regularized_trace_half_boundary_argument
