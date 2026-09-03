import MathlibAux.HorizontalArgument

open Complex MeasureTheory Set
open scoped BigOperators Interval

-- A wrong sign in the vertical derivative or a missing endpoint term breaks
-- this exact antiderivative contract, including reversed integration limits.
example {a b x : ℝ} {u : ℂ} (hx : x ≠ u.re) :
    (∫ t in a..b, ((((x : ℂ) + I * t) - u)⁻¹).re) =
      Real.arctan ((b - u.im) / (x - u.re)) -
        Real.arctan ((a - u.im) / (x - u.re)) := by
  exact MathlibAux.intervalIntegral_re_inv_vertical_sub_eq hx

-- The bottom/right/top orientation must yield pi, not -pi or 2*pi.
-- The root is strictly between the left corners, not a corner root.
example {x0 x1 U T tau : ℝ} (hx : x0 < x1) (hU : U < tau) (hT : tau < T) :
    (∫ x in x0..x1,
      ((((x : ℂ) + I * U) - ((x0 : ℂ) + I * tau))⁻¹).im) +
    (∫ t in U..T,
      ((((x1 : ℂ) + I * t) - ((x0 : ℂ) + I * tau))⁻¹).re) -
    (∫ x in x0..x1,
      ((((x : ℂ) + I * T) - ((x0 : ℂ) + I * tau))⁻¹).im) = Real.pi := by
  exact MathlibAux.threeEdgeArgument_left_boundary_root_eq_pi hx hU hT

#print axioms MathlibAux.intervalIntegral_re_inv_vertical_sub_eq
#print axioms MathlibAux.threeEdgeArgument_left_boundary_root_eq_pi

-- Multiplicities must be retained under the finite sum; no singular left
-- edge integral or unjustified integral-of-sum identity is an input.
example {x0 x1 U T : ℝ} (left : Finset ℂ) (m : ℂ → ℕ)
    (hx : x0 < x1)
    (hleft : ∀ p ∈ left, p.re = x0 ∧ U < p.im ∧ p.im < T) :
    (∫ x in x0..x1,
      (∑ p ∈ left, (((x : ℂ) + I * U) - p)⁻¹ * (m p : ℂ)).im) +
    (∫ t in U..T,
      (∑ p ∈ left, (((x1 : ℂ) + I * t) - p)⁻¹ * (m p : ℂ)).re) -
    (∫ x in x0..x1,
      (∑ p ∈ left, (((x : ℂ) + I * T) - p)⁻¹ * (m p : ℂ)).im) =
      Real.pi * ∑ p ∈ left, (m p : ℝ) := by
  exact MathlibAux.threeEdgeArgument_left_principalParts_eq_pi_mul_sum left m hx hleft

#print axioms MathlibAux.threeEdgeArgument_left_principalParts_eq_pi_mul_sum
