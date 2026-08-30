import PrimeNumberTheorem.MWKFCubicAFEWeightShift

open Complex MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Weighted integrability of the actual infinite-height product weight

The small-product bound comes from the proved residue-one contour shift,
not from a negative-line hypothesis. The large-product bound comes from
the actual positive-line norm mass. Both are combined on the full positive
half-line, including the lower endpoint. This is a fixed-time, product-
variable statement, not yet a change-of-variables theorem for a shifted
physical kernel or an interchange with the complete shift series.
-/

theorem stronglyMeasurable_cubicAFERealProductWeightVertical (t : ℝ) {X : ℝ}
    (hX : -1 / 2 < X) (hne : X ≠ 0) :
    StronglyMeasurable (cubicAFERealProductWeightVertical t X) := by
  have hs : Measurable (fun p : ℝ × ℝ ↦ cubicAFEScalar t (cubicAFEVerticalPoint X p.2)) :=
    (continuous_cubicAFEScalar_vertical_of_halfPlane t hX hne).measurable.comp measurable_snd
  have hv : Measurable (fun p : ℝ × ℝ ↦ cubicAFEVerticalPoint X p.2) := by
    unfold cubicAFEVerticalPoint
    fun_prop
  have hl : Measurable (fun p : ℝ × ℝ ↦ (Real.log p.1 : ℂ)) :=
    Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst)
  have he := Complex.continuous_exp.measurable.comp (hv.neg.mul hl)
  have hj : StronglyMeasurable (fun p : ℝ × ℝ ↦
      cubicAFERealProductMellinIntegrand t X p.1 p.2) := (hs.mul he).stronglyMeasurable
  exact hj.integral_prod_right'.const_mul (1 / (2 * Real.pi) : ℂ)

/-- A bound uniform over 0<P≤1, with fixed physical time. -/
theorem norm_cubicAFERealProductWeightVertical_le_of_le_one (t : ℝ) {X P : ℝ}
    (hX : 0 < X) (hP : 0 < P) (hP1 : P ≤ 1) :
    ‖cubicAFERealProductWeightVertical t X P‖ ≤ 1 + cubicAFEWeightNormMass t (-1 / 4) := by
  have hb := norm_cubicAFERealProductWeightVertical_le_one_add t hP
    (a := -1 / 4) (b := X) (by norm_num) (by norm_num) hX
  have hr : P ^ (-(-1 / 4 : ℝ)) ≤ 1 := Real.rpow_le_one hP.le hP1 (by norm_num)
  calc
    _ ≤ 1 + cubicAFEWeightNormMass t (-1 / 4) * P ^ (-(-1 / 4 : ℝ)) := hb
    _ ≤ 1 + cubicAFEWeightNormMass t (-1 / 4) * 1 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (cubicAFEWeightNormMass_nonneg _ _))
    _ = _ := by rw [mul_one]

/-- Absolute integrability with the product square-root amplitude on the
entire positive half-line. Neither endpoint is removed by a cutoff. -/
theorem integrableOn_cubicAFERealProductWeightVertical_weighted (t : ℝ) {X : ℝ}
    (hX : 1 / 2 < X) :
    IntegrableOn (fun P : ℝ ↦ ((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      cubicAFERealProductWeightVertical t X P) (Ioi 0) := by
  have hx : -1 / 2 < X := by linarith
  have hx0 : 0 < X := by linarith
  have hp : StronglyMeasurable (fun P : ℝ ↦ ((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp (measurable_id.pow measurable_const)).stronglyMeasurable
  have hm := hp.mul (stronglyMeasurable_cubicAFERealProductWeightVertical t hx hx0.ne')
  have hsmall : IntegrableOn (fun P : ℝ ↦ ((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      cubicAFERealProductWeightVertical t X P) (Ioc 0 1) := by
    have hh : IntegrableOn (fun P : ℝ ↦ P ^ (-1 / 2 : ℝ)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)
    have hh' : IntegrableOn (fun P : ℝ ↦ P ^ (-1 / 2 : ℝ)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact hh
    apply (hh'.const_mul (1 + cubicAFEWeightNormMass t (-1 / 4))).mono'
      hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with P hP
    simp only [Pi.mul_apply]
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hP.1.le _)]
    exact (mul_le_mul_of_nonneg_left
      (norm_cubicAFERealProductWeightVertical_le_of_le_one t hx0 hP.1 hP.2)
      (Real.rpow_nonneg hP.1.le _)).trans_eq (by ring)
  have hlarge : IntegrableOn (fun P : ℝ ↦ ((P ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
      cubicAFERealProductWeightVertical t X P) (Ioi 1) := by
    have hh : IntegrableOn (fun P : ℝ ↦ P ^ (-X - 1 / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    apply (hh.const_mul (cubicAFEWeightNormMass t X)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with P hP
    have hp0 : 0 < P := zero_lt_one.trans hP
    simp only [Pi.mul_apply]
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg hp0.le _)]
    calc
      _ ≤ P ^ (-1 / 2 : ℝ) * (cubicAFEWeightNormMass t X * P ^ (-X)) :=
        mul_le_mul_of_nonneg_left (norm_cubicAFERealProductWeightVertical_le t X hp0)
          (Real.rpow_nonneg hp0.le _)
      _ = _ := by
        rw [show -X - 1 / 2 = (-1 / 2 : ℝ) + -X by ring, Real.rpow_add hp0]
        ring
  rw [← Ioc_union_Ioi_eq_Ioi (a := (0 : ℝ)) (b := 1) zero_le_one, integrableOn_union]
  exact ⟨hsmall, hlarge⟩

end PrimeNumberTheorem.MWKFCubic
