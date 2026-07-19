import PrimeNumberTheorem.ScaledHilbertKernel

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The real derivative in Carneiro--Littmann's extremal Heaviside majorant,
with its two removable singularities filled by their limiting values. -/
noncomputable def carneiroLittmannDerivative (x : ℝ) : ℝ :=
  if x = -1 then 1
  else if x = 0 then 0
  else
    -(Real.sin (Real.pi * x)) ^ 2 /
      (Real.pi ^ 2 * x * (x + 1) ^ 2)

@[simp] theorem carneiroLittmannDerivative_neg_one :
    carneiroLittmannDerivative (-1) = 1 := by
  simp [carneiroLittmannDerivative]

@[simp] theorem carneiroLittmannDerivative_zero :
    carneiroLittmannDerivative 0 = 0 := by
  simp [carneiroLittmannDerivative]

/-- Away from the removable singularities, the definition is exactly the
derivative formula in Carneiro--Littmann. -/
theorem carneiroLittmannDerivative_eq_formula {x : ℝ}
    (hxNegOne : x ≠ -1) (hxZero : x ≠ 0) :
    carneiroLittmannDerivative x =
      -(Real.sin (Real.pi * x)) ^ 2 /
        (Real.pi ^ 2 * x * (x + 1) ^ 2) := by
  simp [carneiroLittmannDerivative, hxNegOne, hxZero]

/-- The extremal majorant increases on the negative half-line. -/
theorem carneiroLittmannDerivative_nonneg_of_neg {x : ℝ} (hx : x < 0) :
    0 ≤ carneiroLittmannDerivative x := by
  by_cases hxNegOne : x = -1
  · subst x
    simp
  have hxZero : x ≠ 0 := ne_of_lt hx
  rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero]
  have hxPlusOne : x + 1 ≠ 0 := by
    intro h
    apply hxNegOne
    linarith
  have hden : Real.pi ^ 2 * x * (x + 1) ^ 2 < 0 := by
    have hpiSq : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hxPlusOneSq : 0 < (x + 1) ^ 2 := sq_pos_of_ne_zero hxPlusOne
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpiSq hx) hxPlusOneSq
  exact (div_nonneg_iff.mpr (Or.inr
    ⟨neg_nonpos.mpr (sq_nonneg (Real.sin (Real.pi * x))), hden.le⟩))

/-- The extremal majorant decreases on the positive half-line. -/
theorem carneiroLittmannDerivative_nonpos_of_pos {x : ℝ} (hx : 0 < x) :
    carneiroLittmannDerivative x ≤ 0 := by
  have hxNegOne : x ≠ -1 := by linarith
  have hxZero : x ≠ 0 := ne_of_gt hx
  rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero]
  have hden : 0 ≤ Real.pi ^ 2 * x * (x + 1) ^ 2 := by positivity
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg (Real.sin (Real.pi * x)))) hden

/-- The sign pattern can be summarized as `x * G'(x) ≤ 0`. -/
theorem mul_carneiroLittmannDerivative_nonpos (x : ℝ) :
    x * carneiroLittmannDerivative x ≤ 0 := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · exact mul_nonpos_of_nonpos_of_nonneg hx.le
      (carneiroLittmannDerivative_nonneg_of_neg hx)
  · simp
  · exact mul_nonpos_of_nonneg_of_nonpos hx.le
      (carneiroLittmannDerivative_nonpos_of_pos hx)

end DirichletPolynomial
end PrimeNumberTheorem
