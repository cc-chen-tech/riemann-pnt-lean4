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

/-- The derivative amplitude produced by the quotient rule for
`oscillatoryPhaseQuotient A v`, given derivatives `A'` and `v'`. -/
noncomputable def oscillatoryPhaseQuotientDerivative
    (A A' : ℝ → ℂ) (v v' : ℝ → ℝ) (x : ℝ) : ℂ :=
  (((v⁻¹ x : ℝ) : ℂ) * ((-I) * A' x) +
    ((-v' x / (v x) ^ 2 : ℝ) : ℂ) * ((-I) * A x))

/-- Derivative of the real coefficient `-v'/v^2` which occurs in the
first quotient derivative. -/
theorem phaseReciprocalDerivative_hasDerivAt
    {v v' v'' : ℝ → ℝ} {x : ℝ}
    (hv : HasDerivAt v (v' x) x) (hv' : HasDerivAt v' (v'' x) x)
    (hv0 : v x ≠ 0) :
    HasDerivAt (fun y => -v' y / (v y) ^ 2)
      (-v'' x / (v x) ^ 2 + 2 * (v' x) ^ 2 / (v x) ^ 3) x := by
  convert hv'.neg.div (hv.pow 2) (pow_ne_zero 2 hv0) using 1 <;> try rfl
  simp only [Pi.pow_apply, Pi.neg_apply, pow_two]
  field_simp [hv0]
  ring

/-- The exact four product-rule terms in the derivative of
`oscillatoryPhaseQuotientDerivative`. -/
noncomputable def oscillatoryPhaseQuotientSecondDerivative
    (A A' A'' : ℝ → ℂ) (v v' v'' : ℝ → ℝ) (x : ℝ) : ℂ :=
  ((((-v' x / (v x) ^ 2 : ℝ) : ℂ) * ((-I) * A' x) +
      (((v⁻¹ x : ℝ) : ℂ) * ((-I) * A'' x))) +
    (((-v'' x / (v x) ^ 2 + 2 * (v' x) ^ 2 / (v x) ^ 3 : ℝ) : ℂ) *
        ((-I) * A x) +
      (((-v' x / (v x) ^ 2 : ℝ) : ℂ) * ((-I) * A' x))))

/-- Exact quotient-rule derivative for the first oscillatory quotient. -/
theorem oscillatoryPhaseQuotient_hasDerivAt
    {A A' : ℝ → ℂ} {v v' : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hv : HasDerivAt v (v' x) x)
    (hv0 : v x ≠ 0) :
    HasDerivAt (oscillatoryPhaseQuotient A v)
      (oscillatoryPhaseQuotientDerivative A A' v v' x) x := by
  have hB : HasDerivAt (fun y : ℝ => (-I) * A y) ((-I) * A' x) x :=
    hA.const_mul (-I)
  simpa only [oscillatoryPhaseQuotient, oscillatoryPhaseQuotientDerivative,
    Complex.real_smul] using!
    (hv.inv hv0).smul hB

theorem oscillatoryPhaseQuotient_differentiableAt
    {A A' : ℝ → ℂ} {v v' : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hv : HasDerivAt v (v' x) x)
    (hv0 : v x ≠ 0) :
    DifferentiableAt ℝ (oscillatoryPhaseQuotient A v) x :=
  (oscillatoryPhaseQuotient_hasDerivAt hA hv hv0).differentiableAt

/-- Exact second derivative of the first quotient, retaining its four
product-rule terms for later termwise bounds. -/
theorem oscillatoryPhaseQuotientDerivative_hasDerivAt
    {A A' A'' : ℝ → ℂ} {v v' v'' : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hA' : HasDerivAt A' (A'' x) x)
    (hv : HasDerivAt v (v' x) x) (hv' : HasDerivAt v' (v'' x) x)
    (hv0 : v x ≠ 0) :
    HasDerivAt (oscillatoryPhaseQuotientDerivative A A' v v')
      (oscillatoryPhaseQuotientSecondDerivative A A' A'' v v' v'' x) x := by
  have hc : HasDerivAt (fun y : ℝ => ((v⁻¹ y : ℝ) : ℂ))
      ((-v' x / (v x) ^ 2 : ℝ) : ℂ) x := by
    simpa using! (hv.inv hv0).ofReal_comp
  have hd := (phaseReciprocalDerivative_hasDerivAt hv hv' hv0).ofReal_comp
  have hB : HasDerivAt (fun y : ℝ => (-I) * A y) ((-I) * A' x) x :=
    hA.const_mul (-I)
  have hB' : HasDerivAt (fun y : ℝ => (-I) * A' y) ((-I) * A'' x) x :=
    hA'.const_mul (-I)
  simpa only [oscillatoryPhaseQuotientDerivative,
    oscillatoryPhaseQuotientSecondDerivative, Pi.mul_apply, Pi.add_apply] using!
    (hc.mul hB').add (hd.mul hB)

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

/-- If both the amplitude and its first derivative vanish, then the first
quotient derivative vanishes. -/
theorem oscillatoryPhaseQuotientDerivative_eq_zero
    {A A' : ℝ → ℂ} {v v' : ℝ → ℝ} {x : ℝ}
    (hA : A x = 0) (hA' : A' x = 0) :
    oscillatoryPhaseQuotientDerivative A A' v v' x = 0 := by
  simp [oscillatoryPhaseQuotientDerivative, hA, hA']

/-- The quotient used in the second nonlinear oscillatory integration by
parts: `R=Q'/(i v)`. -/
noncomputable def oscillatorySecondPhaseQuotient
    (A A' : ℝ → ℂ) (v v' : ℝ → ℝ) (x : ℝ) : ℂ :=
  oscillatoryPhaseQuotient (oscillatoryPhaseQuotientDerivative A A' v v') v x

/-- The exact derivative amplitude of the second quotient. -/
noncomputable def oscillatorySecondPhaseQuotientDerivative
    (A A' A'' : ℝ → ℂ) (v v' v'' : ℝ → ℝ) (x : ℝ) : ℂ :=
  oscillatoryPhaseQuotientDerivative
    (oscillatoryPhaseQuotientDerivative A A' v v')
    (oscillatoryPhaseQuotientSecondDerivative A A' A'' v v' v'') v v' x

/-- The four collected amplitude classes in the derivative of the second
quotient. -/
noncomputable def oscillatorySecondPhaseQuotientDerivativeCollected
    (A A' A'' : ℝ → ℂ) (v v' v'' : ℝ → ℝ) (x : ℝ) : ℂ :=
  -(((1 / (v x) ^ 2 : ℝ) : ℂ) * A'' x) +
  (((3 * v' x / (v x) ^ 3 : ℝ) : ℂ) * A' x) +
  (((v'' x / (v x) ^ 3 : ℝ) : ℂ) * A x) -
  (((3 * (v' x) ^ 2 / (v x) ^ 4 : ℝ) : ℂ) * A x)

/-- Collecting the exact quotient-rule expression for `R'` gives the four
terms with coefficients `-1, 3, 1, -3`. -/
theorem oscillatorySecondPhaseQuotientDerivative_eq_collected
    {A A' A'' : ℝ → ℂ} {v v' v'' : ℝ → ℝ} {x : ℝ}
    (hv0 : v x ≠ 0) :
    oscillatorySecondPhaseQuotientDerivative A A' A'' v v' v'' x =
      oscillatorySecondPhaseQuotientDerivativeCollected A A' A'' v v' v'' x := by
  simp only [oscillatorySecondPhaseQuotientDerivative,
    oscillatorySecondPhaseQuotientDerivativeCollected,
    oscillatoryPhaseQuotientDerivative, oscillatoryPhaseQuotientSecondDerivative]
  push_cast
  have hvC : (v x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hv0
  simp only [inv_eq_one_div]
  field_simp [hv0, hvC]
  simp [Complex.I_sq]
  have hinvpow1 : (v x : ℂ)⁻¹ * (v x : ℂ) ^ 2 = (v x : ℂ) := by
    field_simp [hvC]
  have hinv1 : (v x : ℂ)⁻¹ * (v x : ℂ) = 1 := by
    exact inv_mul_cancel₀ hvC
  simp only [hinvpow1, hinv1, one_mul]
  ring

theorem oscillatorySecondPhaseQuotient_hasDerivAt
    {A A' A'' : ℝ → ℂ} {v v' v'' : ℝ → ℝ} {x : ℝ}
    (hA : HasDerivAt A (A' x) x) (hA' : HasDerivAt A' (A'' x) x)
    (hv : HasDerivAt v (v' x) x) (hv' : HasDerivAt v' (v'' x) x)
    (hv0 : v x ≠ 0) :
    HasDerivAt (oscillatorySecondPhaseQuotient A A' v v')
      (oscillatorySecondPhaseQuotientDerivative A A' A'' v v' v'' x) x := by
  exact oscillatoryPhaseQuotient_hasDerivAt
    (oscillatoryPhaseQuotientDerivative_hasDerivAt hA hA' hv hv' hv0) hv hv0

theorem oscillatorySecondPhaseQuotient_mul_phaseVelocity
    {A A' : ℝ → ℂ} {v v' : ℝ → ℝ} {x : ℝ}
    (hv0 : v x ≠ 0) :
    oscillatorySecondPhaseQuotient A A' v v' x * (I * (v x : ℂ)) =
      oscillatoryPhaseQuotientDerivative A A' v v' x := by
  exact oscillatoryPhaseQuotient_mul_phaseVelocity hv0

/-- The second quotient has zero endpoint value when the amplitude and its
first derivative both have zero endpoint value. -/
theorem oscillatorySecondPhaseQuotient_eq_zero
    {A A' : ℝ → ℂ} {v v' : ℝ → ℝ} {x : ℝ}
    (hA : A x = 0) (hA' : A' x = 0) :
    oscillatorySecondPhaseQuotient A A' v v' x = 0 := by
  apply oscillatoryPhaseQuotient_eq_zero
  exact oscillatoryPhaseQuotientDerivative_eq_zero hA hA'

end MathlibAux
