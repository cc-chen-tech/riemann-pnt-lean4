import PrimeNumberTheorem.CarneiroLittmannExtremal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The unshifted sinc-square term that carries the mass of the
Carneiro--Littmann derivative. -/
noncomputable def carneiroLittmannSincSquareBase (x : ℝ) : ℝ :=
  (Real.sinc (Real.pi * x)) ^ 2

/-- The translated sinc-square term appearing in the derivative
decomposition. -/
noncomputable def carneiroLittmannSincSquare (x : ℝ) : ℝ :=
  carneiroLittmannSincSquareBase (x + 1)

/-- A continuous potential whose unit translation gives the zero-mass part
of the derivative. -/
noncomputable def carneiroLittmannTranslationPotential (x : ℝ) : ℝ :=
  x * carneiroLittmannSincSquareBase x

theorem carneiroLittmannSincSquareBase_nonneg (x : ℝ) :
    0 ≤ carneiroLittmannSincSquareBase x := by
  exact sq_nonneg _

theorem carneiroLittmannSincSquareBase_le_abs_rpow {x : ℝ}
    (hx : 1 ≤ |x|) :
    carneiroLittmannSincSquareBase x ≤ |x| ^ (-2 : ℝ) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have habs0 : 0 < |x| := abs_pos.mpr hx0
  have harg0 : Real.pi * x ≠ 0 := mul_ne_zero Real.pi_ne_zero hx0
  rw [carneiroLittmannSincSquareBase, Real.sinc_of_ne_zero harg0]
  have hSin : (Real.sin (Real.pi * x)) ^ 2 ≤ 1 := by
    nlinarith [Real.neg_one_le_sin (Real.pi * x), Real.sin_le_one (Real.pi * x)]
  have hPiSq : 1 ≤ Real.pi ^ 2 := by
    nlinarith [Real.two_le_pi]
  have hDenPos : 0 < Real.pi ^ 2 * x ^ 2 := by
    exact mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_ne_zero hx0)
  have hAbsSq : |x| ^ 2 = x ^ 2 := sq_abs x
  have hDen : |x| ^ 2 ≤ Real.pi ^ 2 * x ^ 2 := by
    rw [hAbsSq]
    exact le_mul_of_one_le_left (sq_nonneg x) hPiSq
  calc
    (Real.sin (Real.pi * x) / (Real.pi * x)) ^ 2 =
        (Real.sin (Real.pi * x)) ^ 2 / (Real.pi ^ 2 * x ^ 2) := by
      field_simp [Real.pi_ne_zero, hx0]
    _ ≤ 1 / (Real.pi ^ 2 * x ^ 2) :=
      div_le_div_of_nonneg_right hSin hDenPos.le
    _ ≤ 1 / |x| ^ 2 :=
      one_div_le_one_div_of_le (pow_pos habs0 2) hDen
    _ = |x| ^ (-2 : ℝ) := by
      rw [Real.rpow_neg habs0.le]
      norm_num [Real.rpow_natCast, div_eq_mul_inv]

/-- A single integrable Japanese-bracket majorant controls the sinc-square
term both near zero and on both tails. -/
theorem carneiroLittmannSincSquareBase_le_japanese (x : ℝ) :
    carneiroLittmannSincSquareBase x ≤
      4 * (1 + ‖x‖) ^ (-2 : ℝ) := by
  have hnorm0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hOneNorm0 : 0 < 1 + ‖x‖ := by positivity
  by_cases hxSmall : ‖x‖ ≤ 1
  · have hBaseOne : carneiroLittmannSincSquareBase x ≤ 1 := by
      rw [carneiroLittmannSincSquareBase]
      have hAbs := Real.abs_sinc_le_one (Real.pi * x)
      have hAbs0 := abs_nonneg (Real.sinc (Real.pi * x))
      have hSq : |Real.sinc (Real.pi * x)| ^ 2 ≤ 1 := by
        nlinarith [mul_nonneg hAbs0 (sub_nonneg.mpr hAbs)]
      simpa only [sq_abs] using hSq
    refine hBaseOne.trans ?_
    rw [Real.rpow_neg hOneNorm0.le]
    rw [show (1 + ‖x‖) ^ (2 : ℝ) = (1 + ‖x‖) ^ (2 : ℕ) by
      norm_num [Real.rpow_natCast]]
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos hOneNorm0 2)).2
    nlinarith
  · have hxLarge : 1 ≤ |x| := by
      simpa only [Real.norm_eq_abs] using le_of_not_ge hxSmall
    refine (carneiroLittmannSincSquareBase_le_abs_rpow hxLarge).trans ?_
    have habs0 : 0 < |x| := zero_lt_one.trans_le hxLarge
    have hOneAbs0 : 0 < 1 + |x| := by positivity
    rw [Real.norm_eq_abs, Real.rpow_neg habs0.le, Real.rpow_neg hOneAbs0.le]
    rw [show |x| ^ (2 : ℝ) = |x| ^ (2 : ℕ) by
      norm_num [Real.rpow_natCast]]
    rw [show (1 + |x|) ^ (2 : ℝ) = (1 + |x|) ^ (2 : ℕ) by
      norm_num [Real.rpow_natCast]]
    rw [← one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (pow_pos habs0 2) (pow_pos hOneAbs0 2)).2
    nlinarith

theorem continuous_carneiroLittmannSincSquareBase :
    Continuous carneiroLittmannSincSquareBase := by
  unfold carneiroLittmannSincSquareBase
  exact (Real.continuous_sinc.comp
    (continuous_const.mul continuous_id)).pow 2

theorem continuous_carneiroLittmannTranslationPotential :
    Continuous carneiroLittmannTranslationPotential := by
  exact continuous_id.mul continuous_carneiroLittmannSincSquareBase

theorem abs_carneiroLittmannTranslationPotential_le_inv_abs {x : ℝ}
    (hx : 1 ≤ |x|) :
    |carneiroLittmannTranslationPotential x| ≤ 1 / |x| := by
  have hx0 : 0 < |x| := zero_lt_one.trans_le hx
  have hbase := carneiroLittmannSincSquareBase_le_abs_rpow hx
  rw [carneiroLittmannTranslationPotential, abs_mul,
    abs_of_nonneg (carneiroLittmannSincSquareBase_nonneg x)]
  calc
    |x| * carneiroLittmannSincSquareBase x ≤ |x| * |x| ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_left hbase (abs_nonneg x)
    _ = 1 / |x| := by
      rw [Real.rpow_neg hx0.le]
      rw [show |x| ^ (2 : ℝ) = |x| ^ (2 : ℕ) by
        norm_num [Real.rpow_natCast]]
      field_simp

theorem integrable_carneiroLittmannSincSquareBase :
    MeasureTheory.Integrable carneiroLittmannSincSquareBase := by
  let majorant : ℝ → ℝ := fun x => 4 * (1 + ‖x‖) ^ (-2 : ℝ)
  have hMajorant : MeasureTheory.Integrable majorant := by
    exact (integrable_one_add_norm (E := ℝ) (r := (2 : ℝ)) (by norm_num)).const_mul 4
  refine hMajorant.mono' continuous_carneiroLittmannSincSquareBase.aestronglyMeasurable ?_
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (carneiroLittmannSincSquareBase_nonneg x)]
  exact carneiroLittmannSincSquareBase_le_japanese x

theorem integrable_carneiroLittmannSincSquare :
    MeasureTheory.Integrable carneiroLittmannSincSquare := by
  simpa only [carneiroLittmannSincSquare, add_comm] using
    integrable_carneiroLittmannSincSquareBase.comp_add_left 1

theorem integral_carneiroLittmannSincSquare_eq_base :
    (∫ x, carneiroLittmannSincSquare x) =
      ∫ x, carneiroLittmannSincSquareBase x := by
  simpa only [carneiroLittmannSincSquare, add_comm] using
    (MeasureTheory.integral_add_left_eq_self
      carneiroLittmannSincSquareBase (1 : ℝ))

/-- The derivative splits into a unit translation difference and the
integrable sinc-square mass term. -/
theorem carneiroLittmannDerivative_eq_translationDifference_add_sincSquare
    (x : ℝ) :
    carneiroLittmannDerivative x =
      carneiroLittmannTranslationPotential (x + 1) -
        carneiroLittmannTranslationPotential x +
          carneiroLittmannSincSquare x := by
  by_cases hxZero : x = 0
  · subst x
    simp [carneiroLittmannTranslationPotential, carneiroLittmannSincSquare,
      carneiroLittmannSincSquareBase, Real.sinc_of_ne_zero Real.pi_ne_zero,
      Real.sin_pi]
  by_cases hxNegOne : x = -1
  · subst x
    simp [carneiroLittmannTranslationPotential, carneiroLittmannSincSquare,
      carneiroLittmannSincSquareBase, Real.sinc_of_ne_zero Real.pi_ne_zero,
      Real.sin_pi]
  have hxPlusOne : x + 1 ≠ 0 := by
    intro h
    apply hxNegOne
    linarith
  rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero]
  simp only [carneiroLittmannTranslationPotential, carneiroLittmannSincSquare,
    carneiroLittmannSincSquareBase]
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxPlusOne)]
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxZero)]
  have hsin : Real.sin (Real.pi * (x + 1)) =
      -Real.sin (Real.pi * x) := by
    rw [show Real.pi * (x + 1) = Real.pi * x + Real.pi by ring]
    exact Real.sin_add_pi _
  rw [hsin]
  field_simp [Real.pi_ne_zero, hxZero, hxPlusOne]
  ring

/-- The integrable translation-difference part of the derivative. -/
noncomputable def carneiroLittmannTranslationDifference (x : ℝ) : ℝ :=
  carneiroLittmannTranslationPotential (x + 1) -
    carneiroLittmannTranslationPotential x

theorem carneiroLittmannTranslationDifference_eq_derivative_sub_sincSquare
    (x : ℝ) :
    carneiroLittmannTranslationDifference x =
      carneiroLittmannDerivative x - carneiroLittmannSincSquare x := by
  rw [carneiroLittmannTranslationDifference]
  linarith [carneiroLittmannDerivative_eq_translationDifference_add_sincSquare x]

theorem integrable_carneiroLittmannTranslationDifference :
    MeasureTheory.Integrable carneiroLittmannTranslationDifference := by
  refine (integrable_carneiroLittmannDerivative.sub
    integrable_carneiroLittmannSincSquare).congr ?_
  filter_upwards [] with x
  exact (carneiroLittmannTranslationDifference_eq_derivative_sub_sincSquare x).symm

/-- On a symmetric finite interval, the integral of the unit translation
difference telescopes to two unit boundary intervals. -/
theorem intervalIntegral_carneiroLittmannTranslationDifference_eq_boundary
    (T : ℝ) :
    (∫ x in -T..T, carneiroLittmannTranslationDifference x) =
      (∫ x in T..T + 1, carneiroLittmannTranslationPotential x) -
        ∫ x in -T..-T + 1, carneiroLittmannTranslationPotential x := by
  have hqShift : Continuous
      (fun x => carneiroLittmannTranslationPotential (x + 1)) :=
    continuous_carneiroLittmannTranslationPotential.comp
      (continuous_id.add continuous_const)
  change (∫ x in -T..T,
    carneiroLittmannTranslationPotential (x + 1) -
      carneiroLittmannTranslationPotential x) = _
  rw [intervalIntegral.integral_sub
    (hqShift.intervalIntegrable (μ := MeasureTheory.volume) (-T) T)
    (continuous_carneiroLittmannTranslationPotential.intervalIntegrable
      (μ := MeasureTheory.volume) (-T) T)]
  rw [intervalIntegral.integral_comp_add_right]
  have hLeft := intervalIntegral.integral_add_adjacent_intervals
    (continuous_carneiroLittmannTranslationPotential.intervalIntegrable
      (μ := MeasureTheory.volume) (-T) (-T + 1))
    (continuous_carneiroLittmannTranslationPotential.intervalIntegrable
      (μ := MeasureTheory.volume) (-T + 1) T)
  have hRight := intervalIntegral.integral_add_adjacent_intervals
    (continuous_carneiroLittmannTranslationPotential.intervalIntegrable
      (μ := MeasureTheory.volume) (-T + 1) T)
    (continuous_carneiroLittmannTranslationPotential.intervalIntegrable
      (μ := MeasureTheory.volume) T (T + 1))
  rw [show -T + 1 = -T + 1 by rfl]
  linarith

/-- The symmetric truncated integral of the translation difference is
controlled by the two decaying boundary intervals. -/
theorem norm_intervalIntegral_carneiroLittmannTranslationDifference_le
    {T : ℝ} (hT : 2 ≤ T) :
    ‖∫ x in -T..T, carneiroLittmannTranslationDifference x‖ ≤
      2 / (T - 1) := by
  have hDen : 0 < T - 1 := by linarith
  have hRightPoint : ∀ x ∈ Set.uIoc T (T + 1),
      ‖carneiroLittmannTranslationPotential x‖ ≤ 1 / (T - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    rcases hx with ⟨hxLower, hxUpper⟩
    have hxNonneg : 0 ≤ x := by linarith
    have hAbs : T - 1 ≤ |x| := by
      rw [abs_of_nonneg hxNonneg]
      linarith
    have hOne : 1 ≤ |x| := by linarith
    rw [Real.norm_eq_abs]
    exact (abs_carneiroLittmannTranslationPotential_le_inv_abs hOne).trans
      (one_div_le_one_div_of_le hDen hAbs)
  have hLeftPoint : ∀ x ∈ Set.uIoc (-T) (-T + 1),
      ‖carneiroLittmannTranslationPotential x‖ ≤ 1 / (T - 1) := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    rcases hx with ⟨hxLower, hxUpper⟩
    have hxNonpos : x ≤ 0 := by linarith
    have hAbs : T - 1 ≤ |x| := by
      rw [abs_of_nonpos hxNonpos]
      linarith
    have hOne : 1 ≤ |x| := by linarith
    rw [Real.norm_eq_abs]
    exact (abs_carneiroLittmannTranslationPotential_le_inv_abs hOne).trans
      (one_div_le_one_div_of_le hDen hAbs)
  have hRight := intervalIntegral.norm_integral_le_of_norm_le_const hRightPoint
  have hLeft := intervalIntegral.norm_integral_le_of_norm_le_const hLeftPoint
  have hRight' :
      ‖∫ x in T..T + 1, carneiroLittmannTranslationPotential x‖ ≤
        1 / (T - 1) := by
    simpa [show T + 1 - T = 1 by ring] using hRight
  have hLeft' :
      ‖∫ x in -T..-T + 1, carneiroLittmannTranslationPotential x‖ ≤
        1 / (T - 1) := by
    simpa [show -T + 1 - -T = 1 by ring] using hLeft
  rw [intervalIntegral_carneiroLittmannTranslationDifference_eq_boundary]
  calc
    ‖(∫ x in T..T + 1, carneiroLittmannTranslationPotential x) -
        ∫ x in -T..-T + 1, carneiroLittmannTranslationPotential x‖ ≤
        ‖∫ x in T..T + 1, carneiroLittmannTranslationPotential x‖ +
          ‖∫ x in -T..-T + 1, carneiroLittmannTranslationPotential x‖ :=
      norm_sub_le _ _
    _ ≤ 1 / (T - 1) + 1 / (T - 1) := add_le_add hRight' hLeft'
    _ = 2 / (T - 1) := by ring

/-- The integrable unit-translation difference has zero total mass. -/
theorem integral_carneiroLittmannTranslationDifference_eq_zero :
    (∫ x, carneiroLittmannTranslationDifference x) = 0 := by
  have hDen : Filter.Tendsto (fun T : ℝ => T - 1)
      Filter.atTop Filter.atTop := by
    simpa only [sub_eq_add_neg] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ)
        Filter.tendsto_id)
  have hUpper : Filter.Tendsto (fun T : ℝ => 2 / (T - 1))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hDen
  have hNorm : Filter.Tendsto
      (fun T : ℝ => ‖∫ x in -T..T, carneiroLittmannTranslationDifference x‖)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with T hT
    exact norm_intervalIntegral_carneiroLittmannTranslationDifference_le hT
  have hZero : Filter.Tendsto
      (fun T : ℝ => ∫ x in -T..T, carneiroLittmannTranslationDifference x)
      Filter.atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hNorm
  have hIntegral : Filter.Tendsto
      (fun T : ℝ => ∫ x in -T..T, carneiroLittmannTranslationDifference x)
      Filter.atTop (nhds (∫ x, carneiroLittmannTranslationDifference x)) :=
    MeasureTheory.intervalIntegral_tendsto_integral
      integrable_carneiroLittmannTranslationDifference
      Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  exact tendsto_nhds_unique hIntegral hZero

/-- Exact reduction of the derivative mass to the translation-difference
integral and the unshifted sinc-square integral. -/
theorem integral_carneiroLittmannDerivative_eq_translationDifference_add_base :
    (∫ x, carneiroLittmannDerivative x) =
      (∫ x, carneiroLittmannTranslationDifference x) +
        ∫ x, carneiroLittmannSincSquareBase x := by
  have hFun : carneiroLittmannDerivative =
      fun x => carneiroLittmannTranslationDifference x +
        carneiroLittmannSincSquare x := by
    funext x
    rw [carneiroLittmannTranslationDifference]
    exact carneiroLittmannDerivative_eq_translationDifference_add_sincSquare x
  rw [hFun, MeasureTheory.integral_add
    integrable_carneiroLittmannTranslationDifference
    integrable_carneiroLittmannSincSquare]
  rw [integral_carneiroLittmannSincSquare_eq_base]

/-- The zero-mass translation difference can be removed from the derivative
normalization, leaving only the sinc-square mass. -/
theorem integral_carneiroLittmannDerivative_eq_sincSquareBase :
    (∫ x, carneiroLittmannDerivative x) =
      ∫ x, carneiroLittmannSincSquareBase x := by
  rw [integral_carneiroLittmannDerivative_eq_translationDifference_add_base,
    integral_carneiroLittmannTranslationDifference_eq_zero, zero_add]

end DirichletPolynomial
end PrimeNumberTheorem
