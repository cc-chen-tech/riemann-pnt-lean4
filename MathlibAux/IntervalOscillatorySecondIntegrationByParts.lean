import Mathlib

/-!
# Two exact integrations by parts against a nonlinear phase

This file isolates the algebraic skeleton needed for summable far-frequency
tails.  The caller supplies the two quotient amplitudes and proves their
derivative and endpoint identities; no analytic estimate is assumed here.
-/

open Complex MeasureTheory Set

namespace MathlibAux

/-- Two integrations by parts with vanishing boundary quotients.  If
`E=exp(iF)`, `A=Q*iF'`, and `Q'=R*iF'`, then the two endpoint cancellations
leave exactly the second remainder `integral R' E`. -/
theorem intervalIntegral_mul_cexp_phase_eq_secondRemainder
    {A Q Q' R R' : ℝ → ℂ} {F F' : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (F' x) x)
    (hQ : ∀ x ∈ uIcc a b, HasDerivAt Q (Q' x) x)
    (hR : ∀ x ∈ uIcc a b, HasDerivAt R (R' x) x)
    (hQ'int : IntervalIntegrable Q' volume a b)
    (hR'int : IntervalIntegrable R' volume a b)
    (hE'int : IntervalIntegrable
      (fun x => Complex.exp (I * F x) * (I * (F' x : ℂ))) volume a b)
    (hA : ∀ x ∈ uIcc a b, A x = Q x * (I * (F' x : ℂ)))
    (hQ' : ∀ x ∈ uIcc a b, Q' x = R x * (I * (F' x : ℂ)))
    (hQ_end : Q a = 0 ∧ Q b = 0)
    (hR_end : R a = 0 ∧ R b = 0) :
    (∫ x in a..b, A x * Complex.exp (I * F x)) =
      ∫ x in a..b, R' x * Complex.exp (I * F x) := by
  let E : ℝ → ℂ := fun x => Complex.exp (I * F x)
  let E' : ℝ → ℂ := fun x => E x * (I * (F' x : ℂ))
  have hE : ∀ x ∈ uIcc a b, HasDerivAt E (E' x) x := by
    intro x hx
    have hreal : HasDerivAt (fun y : ℝ => (F y : ℂ)) (F' x : ℂ) x :=
      (hF x hx).ofReal_comp
    have harg : HasDerivAt (fun y : ℝ => I * (F y : ℂ))
        (I * (F' x : ℂ)) x := hreal.const_mul I
    simpa [E, E', mul_comm, mul_left_comm, mul_assoc] using harg.cexp
  have hE'int' : IntervalIntegrable E' volume a b := by
    simpa only [E, E'] using hE'int
  have hpartsQ := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hQ hE hQ'int hE'int'
  have hpartsR := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hR hE hR'int hE'int'
  have hAE :
      (∫ x in a..b, A x * E x) = ∫ x in a..b, Q x * E' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change A x * E x = Q x * E' x
    rw [hA x hx]
    dsimp only [E']
    ring
  have hQE :
      (∫ x in a..b, Q' x * E x) = ∫ x in a..b, R x * E' x := by
    apply intervalIntegral.integral_congr
    intro x hx
    change Q' x * E x = R x * E' x
    rw [hQ' x hx]
    dsimp only [E']
    ring
  calc
    (∫ x in a..b, A x * Complex.exp (I * F x)) =
        ∫ x in a..b, A x * E x := by rfl
    _ = ∫ x in a..b, Q x * E' x := hAE
    _ = -(∫ x in a..b, Q' x * E x) := by
      rw [hpartsQ, hQ_end.1, hQ_end.2]
      simp
    _ = -(∫ x in a..b, R x * E' x) := by rw [hQE]
    _ = ∫ x in a..b, R' x * E x := by
      rw [hpartsR, hR_end.1, hR_end.2]
      simp
    _ = ∫ x in a..b, R' x * Complex.exp (I * F x) := by rfl

/-- Norm form of the twice-integrated identity.  All oscillation has been
reduced to the `L1` norm of the explicit second remainder. -/
theorem norm_intervalIntegral_mul_cexp_phase_le_secondRemainder
    {A Q Q' R R' : ℝ → ℂ} {F F' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hF : ∀ x ∈ uIcc a b, HasDerivAt F (F' x) x)
    (hQ : ∀ x ∈ uIcc a b, HasDerivAt Q (Q' x) x)
    (hR : ∀ x ∈ uIcc a b, HasDerivAt R (R' x) x)
    (hQ'int : IntervalIntegrable Q' volume a b)
    (hR'int : IntervalIntegrable R' volume a b)
    (hE'int : IntervalIntegrable
      (fun x => Complex.exp (I * F x) * (I * (F' x : ℂ))) volume a b)
    (hA : ∀ x ∈ uIcc a b, A x = Q x * (I * (F' x : ℂ)))
    (hQ' : ∀ x ∈ uIcc a b, Q' x = R x * (I * (F' x : ℂ)))
    (hQ_end : Q a = 0 ∧ Q b = 0)
    (hR_end : R a = 0 ∧ R b = 0) :
    ‖∫ x in a..b, A x * Complex.exp (I * F x)‖ ≤
      ∫ x in a..b, ‖R' x‖ := by
  rw [intervalIntegral_mul_cexp_phase_eq_secondRemainder
    hF hQ hR hQ'int hR'int hE'int hA hQ' hQ_end hR_end]
  refine intervalIntegral.norm_integral_le_of_norm_le hab ?_ hR'int.norm
  filter_upwards with x _hx
  rw [norm_mul, Complex.norm_exp]
  simp

end MathlibAux
