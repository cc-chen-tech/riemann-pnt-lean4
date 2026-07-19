import PrimeNumberTheorem.TriangleFourierKernel

open MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- On the negative half-line, the cumulative Carneiro--Littmann derivative
is nonnegative. -/
theorem carneiroLittmannCumulative_nonneg_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    0 ≤ carneiroLittmannCumulative x := by
  unfold carneiroLittmannCumulative
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  rcases lt_or_eq_of_le (hu.trans hx) with hu0 | rfl
  · exact carneiroLittmannDerivative_nonneg_of_neg hu0
  · simp

/-- On the positive half-line, the cumulative derivative stays above its
unit total mass. -/
theorem one_le_carneiroLittmannCumulative_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ carneiroLittmannCumulative x := by
  have hsplit :
      (∫ u in Set.Iic x, carneiroLittmannDerivative u) +
          (∫ u in (Set.Iic x)ᶜ, carneiroLittmannDerivative u) =
        ∫ u, carneiroLittmannDerivative u :=
    integral_add_compl (s := Set.Iic x) measurableSet_Iic
      integrable_carneiroLittmannDerivative
  have htail :
      (∫ u in (Set.Iic x)ᶜ, carneiroLittmannDerivative u) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic.compl] with u hu
    have hxu : x < u := by simpa only [compl_Iic, Set.mem_Ioi] using hu
    exact carneiroLittmannDerivative_nonpos_of_pos (hx.trans_lt hxu)
  rw [integral_carneiroLittmannDerivative_eq_one] at hsplit
  unfold carneiroLittmannCumulative
  linarith

/-- The error between the cumulative extremal function and the Heaviside
step, with the value at zero taken from the negative side. -/
noncomputable def carneiroLittmannKernelError (x : ℝ) : ℝ :=
  if x ≤ 0 then carneiroLittmannCumulative x
  else carneiroLittmannCumulative x - 1

theorem carneiroLittmannKernelError_nonneg (x : ℝ) :
    0 ≤ carneiroLittmannKernelError x := by
  by_cases hx : x ≤ 0
  · rw [carneiroLittmannKernelError, if_pos hx]
    exact carneiroLittmannCumulative_nonneg_of_nonpos hx
  · rw [carneiroLittmannKernelError, if_neg hx]
    exact sub_nonneg.mpr
      (one_le_carneiroLittmannCumulative_of_nonneg (le_of_not_ge hx))

/-- Positive dilation moves the Heaviside error away from its peak at zero,
so the kernel decreases as the dilation scale grows. -/
theorem carneiroLittmannKernelError_dilation_antitone
    {deltaSmall deltaLarge : ℝ}
    (hsmall : 0 < deltaSmall) (hle : deltaSmall ≤ deltaLarge) (t : ℝ) :
    carneiroLittmannKernelError (deltaLarge * t) ≤
      carneiroLittmannKernelError (deltaSmall * t) := by
  have hlarge : 0 < deltaLarge := hsmall.trans_le hle
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hlargeNonpos : deltaLarge * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlarge.le ht.le
    have hsmallNonpos : deltaSmall * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsmall.le ht.le
    simp only [carneiroLittmannKernelError, if_pos hlargeNonpos,
      if_pos hsmallNonpos]
    exact monotoneOn_carneiroLittmannCumulative_Iic hlargeNonpos hsmallNonpos
      (mul_le_mul_of_nonpos_right hle ht.le)
  · simp [carneiroLittmannKernelError]
  · have hlargePos : 0 < deltaLarge * t := mul_pos hlarge ht
    have hsmallPos : 0 < deltaSmall * t := mul_pos hsmall ht
    simp only [carneiroLittmannKernelError, if_neg (not_le.mpr hlargePos),
      if_neg (not_le.mpr hsmallPos)]
    exact sub_le_sub_right
      (antitoneOn_carneiroLittmannCumulative_Ici hsmallPos.le hlargePos.le
        (mul_le_mul_of_nonneg_right hle ht.le)) 1

/-- The positive tail of the Heaviside error decays quadratically. -/
theorem carneiroLittmannKernelError_le_rpow_neg_two_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    carneiroLittmannKernelError x ≤ x ^ (-2 : ℝ) / 2 := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsplit :
      (∫ u in Set.Iic x, carneiroLittmannDerivative u) +
          (∫ u in Set.Ioi x, carneiroLittmannDerivative u) = 1 := by
    rw [← compl_Iic]
    simpa [integral_carneiroLittmannDerivative_eq_one] using
      (integral_add_compl (s := Set.Iic x) measurableSet_Iic
        integrable_carneiroLittmannDerivative)
  have hErrorEq :
      carneiroLittmannKernelError x =
        ∫ u in Set.Ioi x, |carneiroLittmannDerivative u| := by
    rw [carneiroLittmannKernelError, if_neg (not_le.mpr hx0)]
    have hAbs :
        (∫ u in Set.Ioi x, |carneiroLittmannDerivative u|) =
          -(∫ u in Set.Ioi x, carneiroLittmannDerivative u) := by
      rw [← MeasureTheory.integral_neg]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      rw [abs_of_nonpos
        (carneiroLittmannDerivative_nonpos_of_pos (hx0.trans hu))]
    rw [hAbs]
    unfold carneiroLittmannCumulative
    linarith
  rw [hErrorEq]
  calc
    (∫ u in Set.Ioi x, |carneiroLittmannDerivative u|) ≤
        ∫ u in Set.Ioi x, u ^ (-3 : ℝ) := by
      apply integral_mono_ae
      · exact integrable_carneiroLittmannDerivative.norm.integrableOn
      · exact integrableOn_Ioi_rpow_of_lt (by norm_num) hx0
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact abs_carneiroLittmannDerivative_le_rpow_neg_three
          (hx.trans hu.le)
    _ = x ^ (-2 : ℝ) / 2 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hx0]
      norm_num

/-- The negative tail of the Heaviside error decays quadratically. -/
theorem carneiroLittmannKernelError_le_two_mul_neg_rpow_neg_two_of_le_neg_two
    {x : ℝ} (hx : x ≤ -2) :
    carneiroLittmannKernelError x ≤ 2 * (-x) ^ (-2 : ℝ) := by
  have hxneg : x < 0 := lt_of_le_of_lt hx (by norm_num)
  have hnegx : 0 < -x := neg_pos.mpr hxneg
  have hErrorEq :
      carneiroLittmannKernelError x =
        ∫ u in Set.Iic x, |carneiroLittmannDerivative u| := by
    rw [carneiroLittmannKernelError, if_pos hxneg.le]
    unfold carneiroLittmannCumulative
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    rw [abs_of_nonneg
      (carneiroLittmannDerivative_nonneg_of_neg (hu.trans_lt hxneg))]
  rw [hErrorEq]
  calc
    (∫ u in Set.Iic x, |carneiroLittmannDerivative u|) ≤
        ∫ u in Set.Iic x, 4 * (-u) ^ (-3 : ℝ) := by
      apply integral_mono_ae
      · exact integrable_carneiroLittmannDerivative.norm.integrableOn
      · have hbase : IntegrableOn (fun y : ℝ => 4 * y ^ (-3 : ℝ))
            (Set.Ioi (-x)) :=
          (integrableOn_Ioi_rpow_of_lt (by norm_num) hnegx).const_mul 4
        exact (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hbase).comp_neg_Iic
      · filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
        exact abs_carneiroLittmannDerivative_le_four_mul_neg_rpow
          (hu.trans hx)
    _ = 2 * (-x) ^ (-2 : ℝ) := by
      change (∫ u in Set.Iic x,
        (fun y : ℝ => 4 * y ^ (-3 : ℝ)) (-u)) = _
      rw [integral_comp_neg_Iic x (fun y : ℝ => 4 * y ^ (-3 : ℝ))]
      rw [MeasureTheory.integral_const_mul]
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hnegx]
      norm_num
      ring

/-- The Heaviside error is absolutely integrable. Its two tails are controlled
by the quadratic estimates above, while the jump at zero is split across two
compact intervals. -/
theorem integrable_carneiroLittmannKernelError :
    Integrable carneiroLittmannKernelError := by
  let globalMajorant : ℝ → ℝ :=
    fun x => 8 * (1 + ‖x‖) ^ (-2 : ℝ)
  have hGlobalMajorant : Integrable globalMajorant := by
    exact (integrable_one_add_norm (E := ℝ) (r := (2 : ℝ)) (by norm_num)).const_mul 8
  have hDecayCompare {y : ℝ} (hy : 1 ≤ y) :
      2 * y ^ (-2 : ℝ) ≤ 8 * (1 + y) ^ (-2 : ℝ) := by
    have hy0 : 0 < y := zero_lt_one.trans_le hy
    have hsum : 0 < 1 + y := by linarith
    rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hy0.le, Real.rpow_neg hsum.le,
      Real.rpow_two, Real.rpow_two]
    change 2 / y ^ 2 ≤ 8 / (1 + y) ^ 2
    rw [div_le_div_iff₀ (pow_pos hy0 2) (pow_pos hsum 2)]
    nlinarith [sq_nonneg y]
  have hMeas : Measurable carneiroLittmannKernelError := by
    have hEq : carneiroLittmannKernelError =
        (Set.Iic (0 : ℝ)).piecewise carneiroLittmannCumulative
          (fun x => carneiroLittmannCumulative x - 1) := by
      funext x
      simp only [carneiroLittmannKernelError, Set.piecewise, Set.mem_Iic]
    rw [hEq]
    exact Measurable.piecewise measurableSet_Iic
      continuous_carneiroLittmannCumulative.measurable
      (continuous_carneiroLittmannCumulative.sub continuous_const).measurable
  have hLeft : IntegrableOn carneiroLittmannKernelError (Set.Iic (-2 : ℝ)) := by
    have hMajorantOn := hGlobalMajorant.integrableOn (s := Set.Iic (-2 : ℝ))
    refine hMajorantOn.mono' hMeas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    have hxLe : x ≤ -2 := by simpa only [Set.mem_Iic] using hx
    have hxneg : x < 0 := lt_of_le_of_lt hxLe (by norm_num)
    calc
      ‖carneiroLittmannKernelError x‖ = carneiroLittmannKernelError x :=
        Real.norm_of_nonneg (carneiroLittmannKernelError_nonneg x)
      _ ≤ 2 * (-x) ^ (-2 : ℝ) :=
        carneiroLittmannKernelError_le_two_mul_neg_rpow_neg_two_of_le_neg_two hxLe
      _ ≤ 8 * (1 + (-x)) ^ (-2 : ℝ) := hDecayCompare (by linarith [hxLe])
      _ = globalMajorant x := by
        simp only [globalMajorant, Real.norm_eq_abs, abs_of_neg hxneg]
  have hMiddleLeft :
      IntegrableOn carneiroLittmannKernelError (Set.Icc (-2 : ℝ) 0) := by
    refine continuous_carneiroLittmannCumulative.integrableOn_Icc.congr_fun ?_
      measurableSet_Icc
    intro x hx
    simp [carneiroLittmannKernelError, hx.2]
  have hMiddleRight :
      IntegrableOn carneiroLittmannKernelError (Set.Ioc (0 : ℝ) 1) := by
    have hCont : Continuous (fun x => carneiroLittmannCumulative x - 1) :=
      continuous_carneiroLittmannCumulative.sub continuous_const
    refine (hCont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).congr_fun ?_
      measurableSet_Ioc
    intro x hx
    simp [carneiroLittmannKernelError, not_le.mpr hx.1]
  have hMiddle :
      IntegrableOn carneiroLittmannKernelError (Set.Icc (-2 : ℝ) 1) := by
    rw [← Set.Icc_union_Ioc_eq_Icc (by norm_num : (-2 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) ≤ 1)]
    exact hMiddleLeft.union hMiddleRight
  have hRight : IntegrableOn carneiroLittmannKernelError (Set.Ioi (1 : ℝ)) := by
    have hMajorantOn := hGlobalMajorant.integrableOn (s := Set.Ioi (1 : ℝ))
    refine hMajorantOn.mono' hMeas.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := zero_lt_one.trans hx
    have hrpow : 0 ≤ x ^ (-2 : ℝ) := Real.rpow_nonneg hx0.le _
    calc
      ‖carneiroLittmannKernelError x‖ = carneiroLittmannKernelError x :=
        Real.norm_of_nonneg (carneiroLittmannKernelError_nonneg x)
      _ ≤ x ^ (-2 : ℝ) / 2 :=
        carneiroLittmannKernelError_le_rpow_neg_two_of_one_le hx.le
      _ ≤ 2 * x ^ (-2 : ℝ) := by linarith
      _ ≤ 8 * (1 + x) ^ (-2 : ℝ) := hDecayCompare hx.le
      _ = globalMajorant x := by
        simp only [globalMajorant, Real.norm_eq_abs, abs_of_pos hx0]
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
  have hAll : IntegrableOn carneiroLittmannKernelError Set.univ := by
    exact hCover ▸ (hLeft.union hMiddle).union hRight
  exact integrableOn_univ.mp hAll

end DirichletPolynomial
end PrimeNumberTheorem
