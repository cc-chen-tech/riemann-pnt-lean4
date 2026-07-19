import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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

/-- A continuous local formula around zero.  The factor `x` makes the
removable value at zero explicit. -/
theorem carneiroLittmannDerivative_eq_sinc_zeroChart {x : ℝ}
    (hxNegOne : x ≠ -1) :
    carneiroLittmannDerivative x =
      -x * (Real.sinc (Real.pi * x)) ^ 2 / (x + 1) ^ 2 := by
  by_cases hxZero : x = 0
  · subst x
    simp
  rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero]
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxZero)]
  have hxPlusOne : x + 1 ≠ 0 := by
    intro h
    apply hxNegOne
    linarith
  field_simp [Real.pi_ne_zero, hxZero, hxPlusOne]

/-- A continuous local formula around `-1`.  Translating the sinc function
makes the removable value at `-1` explicit. -/
theorem carneiroLittmannDerivative_eq_sinc_negOneChart {x : ℝ}
    (hxZero : x ≠ 0) :
    carneiroLittmannDerivative x =
      -(Real.sinc (Real.pi * (x + 1))) ^ 2 / x := by
  by_cases hxNegOne : x = -1
  · subst x
    simp
  rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero]
  have hxPlusOne : x + 1 ≠ 0 := by
    intro h
    apply hxNegOne
    linarith
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxPlusOne)]
  have hsin : Real.sin (Real.pi * (x + 1)) =
      -Real.sin (Real.pi * x) := by
    rw [show Real.pi * (x + 1) = Real.pi * x + Real.pi by ring]
    exact Real.sin_add_pi _
  rw [hsin]
  field_simp [Real.pi_ne_zero, hxZero, hxPlusOne]

/-- The filled value at zero is the actual limit of the derivative formula. -/
theorem continuousAt_carneiroLittmannDerivative_zero :
    ContinuousAt carneiroLittmannDerivative 0 := by
  have hSinc : ContinuousAt
      (fun x : ℝ => Real.sinc (Real.pi * x)) 0 :=
    Real.continuous_sinc.continuousAt.comp'
      (continuousAt_const.mul continuousAt_id)
  have hChart : ContinuousAt
      (fun x : ℝ => -x * (Real.sinc (Real.pi * x)) ^ 2 / (x + 1) ^ 2) 0 := by
    exact (continuousAt_id.neg.mul (hSinc.pow 2)).div
      ((continuousAt_id.add continuousAt_const).pow 2) (by norm_num)
  apply hChart.congr
  filter_upwards [eventually_ne_nhds (by norm_num : (0 : ℝ) ≠ -1)] with x hx
  exact (carneiroLittmannDerivative_eq_sinc_zeroChart hx).symm

/-- The filled value at `-1` is the actual limit of the derivative formula. -/
theorem continuousAt_carneiroLittmannDerivative_neg_one :
    ContinuousAt carneiroLittmannDerivative (-1) := by
  have hSinc : ContinuousAt
      (fun x : ℝ => Real.sinc (Real.pi * (x + 1))) (-1) :=
    Real.continuous_sinc.continuousAt.comp'
      (continuousAt_const.mul (continuousAt_id.add continuousAt_const))
  have hChart : ContinuousAt
      (fun x : ℝ => -(Real.sinc (Real.pi * (x + 1))) ^ 2 / x) (-1) := by
    exact (hSinc.pow 2).neg.div continuousAt_id (by norm_num)
  apply hChart.congr
  filter_upwards [eventually_ne_nhds (by norm_num : (-1 : ℝ) ≠ 0)] with x hx
  exact (carneiroLittmannDerivative_eq_sinc_negOneChart hx).symm

/-- The two filled singularities make the Carneiro--Littmann derivative
continuous on the whole real line. -/
theorem continuous_carneiroLittmannDerivative :
    Continuous carneiroLittmannDerivative := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hxNegOne : x = -1
  · subst x
    exact continuousAt_carneiroLittmannDerivative_neg_one
  have hxPlusOne : x + 1 ≠ 0 := by
    intro h
    apply hxNegOne
    linarith
  have hSinc : ContinuousAt
      (fun y : ℝ => Real.sinc (Real.pi * y)) x :=
    Real.continuous_sinc.continuousAt.comp'
      (continuousAt_const.mul continuousAt_id)
  have hChart : ContinuousAt
      (fun y : ℝ => -y * (Real.sinc (Real.pi * y)) ^ 2 / (y + 1) ^ 2) x := by
    exact (continuousAt_id.neg.mul (hSinc.pow 2)).div
      ((continuousAt_id.add continuousAt_const).pow 2)
      (pow_ne_zero 2 hxPlusOne)
  apply hChart.congr
  filter_upwards [eventually_ne_nhds hxNegOne] with y hy
  exact (carneiroLittmannDerivative_eq_sinc_zeroChart hy).symm

/-- A finite-interval primitive of the concrete Carneiro--Littmann derivative.
The improper-integral normalization used in the extremal majorant is a later
step; this definition isolates the local calculus first. -/
noncomputable def carneiroLittmannPrimitive (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, carneiroLittmannDerivative u

@[simp] theorem carneiroLittmannPrimitive_zero :
    carneiroLittmannPrimitive 0 = 0 := by
  simp [carneiroLittmannPrimitive]

/-- The finite-interval primitive has the filled derivative everywhere. -/
theorem hasDerivAt_carneiroLittmannPrimitive (x : ℝ) :
    HasDerivAt carneiroLittmannPrimitive (carneiroLittmannDerivative x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_carneiroLittmannDerivative.intervalIntegrable 0 x)
    continuous_carneiroLittmannDerivative.aestronglyMeasurable.stronglyMeasurableAtFilter
    continuous_carneiroLittmannDerivative.continuousAt

/-- The primitive increases up to its peak at zero. -/
theorem monotoneOn_carneiroLittmannPrimitive_Iic :
    MonotoneOn carneiroLittmannPrimitive (Set.Iic 0) := by
  have hDiff : Differentiable ℝ carneiroLittmannPrimitive :=
    fun x ↦ (hasDerivAt_carneiroLittmannPrimitive x).differentiableAt
  refine monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := carneiroLittmannDerivative) (convex_Iic (0 : ℝ))
    hDiff.continuous.continuousOn ?_ ?_
  · intro x hx
    exact (hasDerivAt_carneiroLittmannPrimitive x).hasDerivWithinAt
  · intro x hx
    have hxNeg : x < 0 := by simpa only [interior_Iic] using hx
    exact carneiroLittmannDerivative_nonneg_of_neg hxNeg

/-- The primitive decreases after its peak at zero. -/
theorem antitoneOn_carneiroLittmannPrimitive_Ici :
    AntitoneOn carneiroLittmannPrimitive (Set.Ici 0) := by
  have hDiff : Differentiable ℝ carneiroLittmannPrimitive :=
    fun x ↦ (hasDerivAt_carneiroLittmannPrimitive x).differentiableAt
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := carneiroLittmannDerivative) (convex_Ici (0 : ℝ))
    hDiff.continuous.continuousOn ?_ ?_
  · intro x hx
    exact (hasDerivAt_carneiroLittmannPrimitive x).hasDerivWithinAt
  · intro x hx
    have hxPos : 0 < x := by simpa only [interior_Ici] using hx
    exact carneiroLittmannDerivative_nonpos_of_pos hxPos

end DirichletPolynomial
end PrimeNumberTheorem
