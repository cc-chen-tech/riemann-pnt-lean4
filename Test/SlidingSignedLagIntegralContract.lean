import MathlibAux.SlidingSignedLagIntegral

set_option autoImplicit false

open MeasureTheory Set

namespace MathlibAux

example {F : ℝ → ℝ} (hF : Continuous F) {A B H : ℝ}
    (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (slidingWindowMass F H t) ^ 2) =
      ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ),
        ∫ x in A + v..B + v, F x * F (x + τ) :=
  integral_sq_slidingWindowMass_eq_lagIntegral hF hAB hH

end MathlibAux
