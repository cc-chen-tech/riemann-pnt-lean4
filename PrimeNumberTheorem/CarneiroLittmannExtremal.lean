import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
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

/-- The positive tail decays cubically. -/
theorem abs_carneiroLittmannDerivative_le_rpow_neg_three {x : ℝ}
    (hx : 1 ≤ x) :
    |carneiroLittmannDerivative x| ≤ x ^ (-3 : ℝ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hxZero : x ≠ 0 := hx0.ne'
  have hxNegOne : x ≠ -1 := by linarith
  have hxPlusOne0 : 0 < x + 1 := by linarith
  have hAbs :
      |carneiroLittmannDerivative x| =
        (Real.sin (Real.pi * x)) ^ 2 /
          (Real.pi ^ 2 * x * (x + 1) ^ 2) := by
    rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero]
    simp only [abs_div, abs_neg, abs_pow, abs_mul, sq_abs,
      abs_of_pos Real.pi_pos, abs_of_pos hx0, abs_of_pos hxPlusOne0]
  have hSin : (Real.sin (Real.pi * x)) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin (Real.pi * x), Real.sin_le_one (Real.pi * x)]
  have hPiSq : 1 ≤ Real.pi ^ 2 := by
    nlinarith [Real.two_le_pi]
  have hShiftSq : x ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
  have hDenPos : 0 < Real.pi ^ 2 * x * (x + 1) ^ 2 := by positivity
  have hCubePos : 0 < x ^ 3 := pow_pos hx0 3
  have hDen : x ^ 3 ≤ Real.pi ^ 2 * x * (x + 1) ^ 2 := by
    calc
      x ^ 3 = 1 * x * x ^ 2 := by ring
      _ ≤ Real.pi ^ 2 * x * (x + 1) ^ 2 := by gcongr
  calc
    |carneiroLittmannDerivative x| =
        (Real.sin (Real.pi * x)) ^ 2 /
          (Real.pi ^ 2 * x * (x + 1) ^ 2) := hAbs
    _ ≤ 1 / (Real.pi ^ 2 * x * (x + 1) ^ 2) :=
      div_le_div_of_nonneg_right hSin hDenPos.le
    _ ≤ 1 / x ^ 3 := one_div_le_one_div_of_le hCubePos hDen
    _ = x ^ (-3 : ℝ) := by
      rw [Real.rpow_neg hx0.le]
      norm_num [Real.rpow_natCast]

/-- The negative tail has the same cubic decay, with a harmless factor four
coming from `|-x - 1| ≥ |-x| / 2` once `x ≤ -2`. -/
theorem abs_carneiroLittmannDerivative_le_four_mul_neg_rpow {x : ℝ}
    (hx : x ≤ -2) :
    |carneiroLittmannDerivative x| ≤
      4 * (-x) ^ (-3 : ℝ) := by
  have hx0 : x < 0 := lt_of_le_of_lt hx (by norm_num)
  have hxPlusOne0 : x + 1 < 0 := by linarith
  have hxZero : x ≠ 0 := hx0.ne
  have hxNegOne : x ≠ -1 := by linarith
  let y : ℝ := -x
  have hy : 2 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 < y := by linarith
  have hyMinusOne0 : 0 < y - 1 := by linarith
  have hAbs :
      |carneiroLittmannDerivative x| =
        (Real.sin (Real.pi * x)) ^ 2 /
          (Real.pi ^ 2 * y * (y - 1) ^ 2) := by
    rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero]
    simp only [abs_div, abs_neg, abs_pow, abs_mul, sq_abs,
      abs_of_pos Real.pi_pos, abs_of_neg hx0, abs_of_neg hxPlusOne0]
    dsimp [y]
    congr 2
    ring
  have hSin : (Real.sin (Real.pi * x)) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin (Real.pi * x), Real.sin_le_one (Real.pi * x)]
  have hPiSq : 1 ≤ Real.pi ^ 2 := by
    nlinarith [Real.two_le_pi]
  have hHalfNonneg : 0 ≤ y / 2 := by positivity
  have hShift : y / 2 ≤ y - 1 := by linarith
  have hShiftSq : (y / 2) ^ 2 ≤ (y - 1) ^ 2 := by nlinarith
  have hDenPos : 0 < Real.pi ^ 2 * y * (y - 1) ^ 2 := by
    exact mul_pos (mul_pos (sq_pos_of_pos Real.pi_pos) hy0)
      (sq_pos_of_pos hyMinusOne0)
  have hCubePos : 0 < y ^ 3 := pow_pos hy0 3
  have hDen : y ^ 3 ≤ 4 * (Real.pi ^ 2 * y * (y - 1) ^ 2) := by
    calc
      y ^ 3 = 4 * (1 * y * (y / 2) ^ 2) := by ring
      _ ≤ 4 * (Real.pi ^ 2 * y * (y - 1) ^ 2) := by gcongr
  calc
    |carneiroLittmannDerivative x| =
        (Real.sin (Real.pi * x)) ^ 2 /
          (Real.pi ^ 2 * y * (y - 1) ^ 2) := hAbs
    _ ≤ 1 / (Real.pi ^ 2 * y * (y - 1) ^ 2) :=
      div_le_div_of_nonneg_right hSin hDenPos.le
    _ ≤ 4 / y ^ 3 := by
      exact (div_le_div_iff₀ hDenPos hCubePos).2 (by simpa using hDen)
    _ = 4 * y ^ (-3 : ℝ) := by
      rw [Real.rpow_neg hy0.le]
      norm_num [Real.rpow_natCast, div_eq_mul_inv]
    _ = 4 * (-x) ^ (-3 : ℝ) := by rfl

/-- The concrete derivative is absolutely integrable.  The proof uses the
cubic bounds on both tails and continuity on the remaining compact interval. -/
theorem integrable_carneiroLittmannDerivative :
    MeasureTheory.Integrable carneiroLittmannDerivative := by
  let globalMajorant : ℝ → ℝ :=
    fun x => 16 * (1 + ‖x‖) ^ (-2 : ℝ)
  have hGlobalMajorant : MeasureTheory.Integrable globalMajorant := by
    exact (integrable_one_add_norm (E := ℝ) (r := (2 : ℝ)) (by norm_num)).const_mul 16
  have hDecayCompare {y : ℝ} (hy : 1 ≤ y) :
      4 * y ^ (-3 : ℝ) ≤ 16 * (1 + y) ^ (-2 : ℝ) := by
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have hOneY0 : 0 < 1 + y := by linarith
    rw [Real.rpow_neg hy0.le, Real.rpow_neg hOneY0.le]
    rw [show y ^ (3 : ℝ) = y ^ (3 : ℕ) by norm_num [Real.rpow_natCast]]
    rw [show (1 + y) ^ (2 : ℝ) = (1 + y) ^ (2 : ℕ) by
      norm_num [Real.rpow_natCast]]
    rw [← div_eq_mul_inv, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (pow_pos hy0 3) (pow_pos hOneY0 2)).2
    have hOneAddSq : (1 + y) ^ 2 ≤ (2 * y) ^ 2 := by nlinarith
    have hSqCube : y ^ 2 ≤ y ^ 3 := by
      calc
        y ^ 2 = y ^ 2 * 1 := by ring
        _ ≤ y ^ 2 * y := by gcongr
        _ = y ^ 3 := by ring
    nlinarith
  have hRight : MeasureTheory.IntegrableOn carneiroLittmannDerivative (Set.Ioi 1) := by
    change MeasureTheory.Integrable carneiroLittmannDerivative
      (MeasureTheory.volume.restrict (Set.Ioi 1))
    have hMajorantOn := hGlobalMajorant.integrableOn (s := Set.Ioi (1 : ℝ))
    change MeasureTheory.Integrable globalMajorant
      (MeasureTheory.volume.restrict (Set.Ioi 1)) at hMajorantOn
    refine hMajorantOn.mono'
      continuous_carneiroLittmannDerivative.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    calc
      ‖carneiroLittmannDerivative x‖ = |carneiroLittmannDerivative x| :=
        Real.norm_eq_abs _
      _ ≤ x ^ (-3 : ℝ) :=
        abs_carneiroLittmannDerivative_le_rpow_neg_three hx.le
      _ ≤ 4 * x ^ (-3 : ℝ) := by
        have := Real.rpow_nonneg hx0.le (-3 : ℝ)
        linarith
      _ ≤ 16 * (1 + x) ^ (-2 : ℝ) := hDecayCompare hx.le
      _ = globalMajorant x := by
        simp only [globalMajorant, Real.norm_eq_abs, abs_of_pos hx0]
  have hLeft : MeasureTheory.IntegrableOn carneiroLittmannDerivative (Set.Iic (-2)) := by
    change MeasureTheory.Integrable carneiroLittmannDerivative
      (MeasureTheory.volume.restrict (Set.Iic (-2)))
    have hMajorantOn := hGlobalMajorant.integrableOn (s := Set.Iic (-2 : ℝ))
    change MeasureTheory.Integrable globalMajorant
      (MeasureTheory.volume.restrict (Set.Iic (-2))) at hMajorantOn
    refine hMajorantOn.mono'
      continuous_carneiroLittmannDerivative.aestronglyMeasurable.restrict ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with x hx
    have hxLe : x ≤ -2 := by simpa only [Set.mem_Iic] using hx
    have hx0 : x < 0 := lt_of_le_of_lt hxLe (by norm_num)
    calc
      ‖carneiroLittmannDerivative x‖ = |carneiroLittmannDerivative x| :=
        Real.norm_eq_abs _
      _ ≤ 4 * (-x) ^ (-3 : ℝ) :=
        abs_carneiroLittmannDerivative_le_four_mul_neg_rpow hxLe
      _ ≤ 16 * (1 + (-x)) ^ (-2 : ℝ) := hDecayCompare (by linarith [hxLe])
      _ = globalMajorant x := by
        simp only [globalMajorant, Real.norm_eq_abs, abs_of_neg hx0]
  have hMiddle : MeasureTheory.IntegrableOn carneiroLittmannDerivative
      (Set.Icc (-2) 1) :=
    continuous_carneiroLittmannDerivative.continuousOn.integrableOn_compact isCompact_Icc
  have hCover :
      (Set.Iic (-2 : ℝ) ∪ Set.Icc (-2 : ℝ) 1) ∪ Set.Ioi (1 : ℝ) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc, Set.mem_Ioi,
      Set.mem_univ, iff_true]
    by_cases hxLeft : x ≤ -2
    · exact Or.inl (Or.inl hxLeft)
    by_cases hxRight : x ≤ 1
    · exact Or.inl (Or.inr ⟨le_of_not_ge hxLeft, hxRight⟩)
    · exact Or.inr (lt_of_not_ge hxRight)
  have hAll : MeasureTheory.IntegrableOn carneiroLittmannDerivative Set.univ := by
    have hUnion := (hLeft.union hMiddle).union hRight
    exact hCover ▸ hUnion
  exact Iff.mp MeasureTheory.integrableOn_univ hAll

/-- The actual cumulative integral beginning at negative infinity.  Its total
mass is not fixed here; proving the Carneiro--Littmann normalization is a
separate analytic step. -/
noncomputable def carneiroLittmannCumulative (x : ℝ) : ℝ :=
  ∫ u in Set.Iic x, carneiroLittmannDerivative u

/-- Changing the upper endpoint from zero to `x` produces exactly the finite
interval primitive. -/
theorem carneiroLittmannCumulative_sub_zero_eq_primitive (x : ℝ) :
    carneiroLittmannCumulative x - carneiroLittmannCumulative 0 =
      carneiroLittmannPrimitive x := by
  simpa only [carneiroLittmannCumulative, carneiroLittmannPrimitive] using
    (intervalIntegral.integral_Iic_sub_Iic
      (a := (0 : ℝ)) (b := x)
      integrable_carneiroLittmannDerivative.integrableOn
      integrable_carneiroLittmannDerivative.integrableOn)

theorem carneiroLittmannCumulative_eq_primitive_add_zero (x : ℝ) :
    carneiroLittmannCumulative x =
      carneiroLittmannPrimitive x + carneiroLittmannCumulative 0 :=
  sub_eq_iff_eq_add.mp (carneiroLittmannCumulative_sub_zero_eq_primitive x)

/-- The cumulative integral has the concrete filled derivative everywhere. -/
theorem hasDerivAt_carneiroLittmannCumulative (x : ℝ) :
    HasDerivAt carneiroLittmannCumulative (carneiroLittmannDerivative x) x := by
  have hFun : carneiroLittmannCumulative =
      fun y => carneiroLittmannPrimitive y + carneiroLittmannCumulative 0 := by
    funext y
    exact carneiroLittmannCumulative_eq_primitive_add_zero y
  rw [hFun]
  exact (hasDerivAt_carneiroLittmannPrimitive x).add_const _

theorem continuous_carneiroLittmannCumulative :
    Continuous carneiroLittmannCumulative := by
  exact (show Differentiable ℝ carneiroLittmannCumulative from
    fun x ↦ (hasDerivAt_carneiroLittmannCumulative x).differentiableAt).continuous

/-- The cumulative integral rises on the negative half-line. -/
theorem monotoneOn_carneiroLittmannCumulative_Iic :
    MonotoneOn carneiroLittmannCumulative (Set.Iic 0) := by
  intro x hx y hy hxy
  rw [carneiroLittmannCumulative_eq_primitive_add_zero x,
    carneiroLittmannCumulative_eq_primitive_add_zero y]
  exact add_le_add_left
    (monotoneOn_carneiroLittmannPrimitive_Iic hx hy hxy) _

/-- The cumulative integral falls on the positive half-line. -/
theorem antitoneOn_carneiroLittmannCumulative_Ici :
    AntitoneOn carneiroLittmannCumulative (Set.Ici 0) := by
  intro x hx y hy hxy
  rw [carneiroLittmannCumulative_eq_primitive_add_zero x,
    carneiroLittmannCumulative_eq_primitive_add_zero y]
  exact add_le_add_left
    (antitoneOn_carneiroLittmannPrimitive_Ici hx hy hxy) _

end DirichletPolynomial
end PrimeNumberTheorem
