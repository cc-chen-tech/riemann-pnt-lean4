import Mathlib

/-!
# Quotient amplitudes for nonlinear oscillatory integration by parts

For `E=exp(iF)`, division by `iF'` produces the amplitude used in one
integration by parts.  This file records the exact quotient-rule derivative
and its endpoint vanishing consequences.
-/

open Complex

namespace MathlibAux

/-- The first integration-by-parts quotient `A/(i v)`, where eventually
`v=F'`. -/
noncomputable def oscillatoryPhaseQuotient
    (A : ℝ → ℂ) (v : ℝ → ℝ) (x : ℝ) : ℂ :=
  (v⁻¹) x • ((-I) * A x)

theorem oscillatoryPhaseQuotient_differentiableAt
    {A A' : ℝ → ℂ} {v v' : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hv : HasDerivAt v (v' x) x)
    (hv0 : v x ≠ 0) :
    DifferentiableAt ℝ (oscillatoryPhaseQuotient A v) x := by
  have hB : HasDerivAt (fun y : ℝ => (-I) * A y) ((-I) * A' x) x :=
    hA.const_mul (-I)
  exact ((hv.inv hv0).smul hB).differentiableAt

/-- The real-scalar representation is exactly division by `i v`: multiplying
the quotient back by the phase velocity recovers the amplitude. -/
theorem oscillatoryPhaseQuotient_mul_phaseVelocity
    {A : ℝ → ℂ} {v : ℝ → ℝ} {x : ℝ} (hv0 : v x ≠ 0) :
    oscillatoryPhaseQuotient A v x * (I * (v x : ℂ)) = A x := by
  rw [oscillatoryPhaseQuotient, Complex.real_smul]
  change (((v x)⁻¹ : ℝ) : ℂ) * (-I * A x) * (I * (v x : ℂ)) = A x
  rw [Complex.ofReal_inv]
  have hvC : (v x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv0
  field_simp [hvC, I_ne_zero]
  simp [Complex.I_sq]

/-- A zero amplitude gives a zero first quotient whenever the phase velocity
is nonzero. -/
theorem oscillatoryPhaseQuotient_eq_zero
    {A : ℝ → ℂ} {v : ℝ → ℝ} {x : ℝ}
    (hA : A x = 0) :
    oscillatoryPhaseQuotient A v x = 0 := by
  simp [oscillatoryPhaseQuotient, hA]

end MathlibAux
