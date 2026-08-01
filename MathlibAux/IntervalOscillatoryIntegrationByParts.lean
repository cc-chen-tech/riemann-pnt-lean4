import MathlibAux.RectangularFourierFirstMoment

open Complex MeasureTheory Set

namespace MathlibAux

/-- Integration by parts for a differentiable complex amplitude against a
nonzero linear phase. The bound exposes the reciprocal frequency needed on
the dynamic left edge of the zeta contour. -/
theorem norm_intervalIntegral_mul_cexp_linear_le_of_norm_deriv
    {A A' : ℝ → ℂ} {u v omega M0 M1 : ℝ}
    (huv : u ≤ v) (homega : omega ≠ 0)
    (hA : ∀ t ∈ uIcc u v, HasDerivAt A (A' t) t)
    (hA'int : IntervalIntegrable A' volume u v)
    (hA0 : ∀ t ∈ uIcc u v, ‖A t‖ ≤ M0)
    (hA1 : ∀ t ∈ uIcc u v, ‖A' t‖ ≤ M1) :
    ‖∫ t in u..v, A t * Complex.exp (I * (omega * t))‖ ≤
      (2 * M0 + (v - u) * M1) / |omega| := by
  let c : ℂ := I * (omega : ℂ)
  let V : ℝ → ℂ := fun t => Complex.exp (I * (omega * t)) / c
  have hc : c ≠ 0 := by
    exact mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr homega)
  have hV : ∀ t ∈ uIcc u v,
      HasDerivAt V (Complex.exp (I * (omega * t))) t := by
    intro t _ht
    have hexp : HasDerivAt
        (fun y : ℝ => Complex.exp (I * (omega * y)))
        (Complex.exp (I * (omega * t)) * c) t := by
      convert (Complex.hasDerivAt_exp (I * (omega * t))).comp t
        (((hasDerivAt_id (t : ℂ)).comp_ofReal.const_mul (omega : ℂ)).const_mul I) using 1
      simp [c]
    convert hexp.div_const c using 1
    field_simp [hc]
  have hV'int : IntervalIntegrable
      (fun t : ℝ => Complex.exp (I * (omega * t))) volume u v := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hA hV hA'int hV'int
  have hVnorm (t : ℝ) : ‖V t‖ = 1 / |omega| := by
    dsimp [V, c]
    rw [norm_div, norm_mul, norm_I, norm_real, Complex.norm_exp]
    norm_num
  have hend : ‖A v * V v - A u * V u‖ ≤ 2 * M0 / |omega| := by
    calc
      ‖A v * V v - A u * V u‖ ≤ ‖A v * V v‖ + ‖A u * V u‖ :=
        norm_sub_le _ _
      _ = ‖A v‖ / |omega| + ‖A u‖ / |omega| := by
        rw [norm_mul, norm_mul, hVnorm, hVnorm]
        ring
      _ ≤ M0 / |omega| + M0 / |omega| := by
        gcongr
        · exact hA0 v right_mem_uIcc
        · exact hA0 u left_mem_uIcc
      _ = 2 * M0 / |omega| := by ring
  have hrem : ‖∫ t in u..v, A' t * V t‖ ≤
      (M1 / |omega|) * (v - u) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => A' t * V t) (a := u) (b := v)
      (C := M1 / |omega|) (fun t ht => by
        calc
          ‖A' t * V t‖ = ‖A' t‖ / |omega| := by
            rw [norm_mul, hVnorm]
            simp [div_eq_mul_inv]
          _ ≤ M1 / |omega| := by
            gcongr
            exact hA1 t (Set.uIoc_subset_uIcc ht))
    simpa [abs_of_nonneg (sub_nonneg.mpr huv)] using hbound
  calc
    ‖∫ t in u..v, A t * Complex.exp (I * (omega * t))‖ =
        ‖A v * V v - A u * V u - ∫ t in u..v, A' t * V t‖ := by
      simpa using congrArg norm hparts
    ‖A v * V v - A u * V u - ∫ t in u..v, A' t * V t‖ ≤
        ‖A v * V v - A u * V u‖ + ‖∫ t in u..v, A' t * V t‖ :=
      norm_sub_le _ _
    _ ≤ 2 * M0 / |omega| + (M1 / |omega|) * (v - u) :=
      add_le_add hend hrem
    _ = (2 * M0 + (v - u) * M1) / |omega| := by ring

end MathlibAux
