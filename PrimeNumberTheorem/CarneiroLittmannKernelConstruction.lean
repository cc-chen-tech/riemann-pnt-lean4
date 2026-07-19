import PrimeNumberTheorem.CarneiroLittmannSpectralProfile

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

/-- Multiplying the extremal derivative by `-x` gives exactly the translated
sinc-square density whose total mass is one. -/
theorem neg_mul_carneiroLittmannDerivative_eq_sincSquare (x : ℝ) :
    -(x * carneiroLittmannDerivative x) = carneiroLittmannSincSquare x := by
  by_cases hxNegOne : x = -1
  · subst x
    simp [carneiroLittmannSincSquare, carneiroLittmannSincSquareBase]
  by_cases hxZero : x = 0
  · subst x
    simp [carneiroLittmannSincSquare, carneiroLittmannSincSquareBase,
      Real.sinc_of_ne_zero Real.pi_ne_zero, Real.sin_pi]
  have hxPlusOne : x + 1 ≠ 0 := by
    intro h
    apply hxNegOne
    linarith
  rw [carneiroLittmannDerivative_eq_formula hxNegOne hxZero,
    carneiroLittmannSincSquare, carneiroLittmannSincSquareBase,
    Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hxPlusOne)]
  have hsin : Real.sin (Real.pi * (x + 1)) =
      -Real.sin (Real.pi * x) := by
    rw [show Real.pi * (x + 1) = Real.pi * x + Real.pi by ring]
    exact Real.sin_add_pi _
  rw [hsin]
  field_simp [Real.pi_ne_zero, hxZero, hxPlusOne]

private theorem tendsto_mul_carneiroLittmannKernelError_atTop : Filter.Tendsto
    (fun x : ℝ => x * carneiroLittmannKernelError x)
    Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hUpper : Filter.Tendsto (fun x : ℝ => 1 / x)
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hError := carneiroLittmannKernelError_le_rpow_neg_two_of_one_le hx
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hx0.le (carneiroLittmannKernelError_nonneg x))]
  calc
    x * carneiroLittmannKernelError x ≤ x * (x ^ (-2 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hError hx0.le
    _ = 1 / (2 * x) := by
      rw [Real.rpow_neg hx0.le]
      norm_num [Real.rpow_natCast]
      field_simp
    _ ≤ 1 / x := by
      exact one_div_le_one_div_of_le hx0 (by linarith)

private theorem tendsto_mul_carneiroLittmannKernelError_atBot : Filter.Tendsto
    (fun x : ℝ => x * carneiroLittmannKernelError x)
    Filter.atBot (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hDen : Filter.Tendsto (fun x : ℝ => -x)
      Filter.atBot Filter.atTop := Filter.tendsto_neg_atBot_atTop
  have hUpper : Filter.Tendsto (fun x : ℝ => 2 / (-x))
      Filter.atBot (nhds 0) := tendsto_const_nhds.div_atTop hDen
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) _ hUpper
  filter_upwards [Filter.eventually_le_atBot (-2 : ℝ)] with x hx
  have hxneg : x < 0 := lt_of_le_of_lt hx (by norm_num)
  have hnegx : 0 < -x := neg_pos.mpr hxneg
  have hError :=
    carneiroLittmannKernelError_le_two_mul_neg_rpow_neg_two_of_le_neg_two hx
  rw [Real.norm_eq_abs, abs_of_nonpos
    (mul_nonpos_of_nonpos_of_nonneg hxneg.le
      (carneiroLittmannKernelError_nonneg x))]
  calc
    -(x * carneiroLittmannKernelError x) =
        (-x) * carneiroLittmannKernelError x := by ring
    _ ≤ (-x) * (2 * (-x) ^ (-2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hError hnegx.le
    _ = 2 / (-x) := by
      rw [Real.rpow_neg hnegx.le]
      norm_num [Real.rpow_natCast]
      field_simp

private theorem tendsto_carneiroLittmannKernelError_atTop : Filter.Tendsto
    carneiroLittmannKernelError Filter.atTop (nhds 0) := by
  have h := tendsto_mul_carneiroLittmannKernelError_atTop.div_atTop
    Filter.tendsto_id
  refine h.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [id_eq]
  field_simp [hx.ne']

private theorem tendsto_carneiroLittmannKernelError_atBot : Filter.Tendsto
    carneiroLittmannKernelError Filter.atBot (nhds 0) := by
  have hNumerator : Filter.Tendsto
      (fun x : ℝ => -(x * carneiroLittmannKernelError x))
      Filter.atBot (nhds 0) :=
    by simpa using tendsto_mul_carneiroLittmannKernelError_atBot.neg
  have h := hNumerator.div_atTop Filter.tendsto_neg_atBot_atTop
  refine h.congr' ?_
  filter_upwards [Filter.eventually_lt_atBot (0 : ℝ)] with x hx
  field_simp [hx.ne]

private noncomputable def carneiroLittmannFourierPhase (xi x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (xi * x))

private theorem hasDerivAt_carneiroLittmannFourierPhase (xi x : ℝ) :
    HasDerivAt (carneiroLittmannFourierPhase xi)
      (Complex.I * xi * carneiroLittmannFourierPhase xi x) x := by
  have hInner : HasDerivAt
      (fun y : ℝ => (Complex.I * (xi : ℂ)) * (y : ℂ))
      (Complex.I * (xi : ℂ)) x := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id (x : ℂ)).const_mul
        (Complex.I * (xi : ℂ))).comp_ofReal
  have h := (Complex.hasDerivAt_exp
    ((Complex.I * (xi : ℂ)) * (x : ℂ))).comp x hInner
  convert h using 1
  · funext y
    unfold carneiroLittmannFourierPhase
    congr 1
    push_cast
    ring
  · unfold carneiroLittmannFourierPhase
    push_cast
    ring

private theorem tendsto_carneiroLittmannKernelError_mul_phase_atTop (xi : ℝ) :
    Filter.Tendsto
      (fun x : ℝ => (carneiroLittmannKernelError x : ℂ) *
        carneiroLittmannFourierPhase xi x)
      Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  convert tendsto_carneiroLittmannKernelError_atTop using 1
  funext x
  have hPhase : ‖carneiroLittmannFourierPhase xi x‖ = 1 := by
    unfold carneiroLittmannFourierPhase
    simpa only [Complex.ofReal_mul] using
      Complex.norm_exp_I_mul_ofReal (xi * x)
  rw [norm_mul, hPhase, mul_one, Complex.norm_real]
  exact abs_of_nonneg (carneiroLittmannKernelError_nonneg x)

private theorem tendsto_carneiroLittmannKernelError_mul_phase_atBot (xi : ℝ) :
    Filter.Tendsto
      (fun x : ℝ => (carneiroLittmannKernelError x : ℂ) *
        carneiroLittmannFourierPhase xi x)
      Filter.atBot (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  convert tendsto_carneiroLittmannKernelError_atBot using 1
  funext x
  have hPhase : ‖carneiroLittmannFourierPhase xi x‖ = 1 := by
    unfold carneiroLittmannFourierPhase
    simpa only [Complex.ofReal_mul] using
      Complex.norm_exp_I_mul_ofReal (xi * x)
  rw [norm_mul, hPhase, mul_one, Complex.norm_real]
  exact abs_of_nonneg (carneiroLittmannKernelError_nonneg x)

private theorem tendsto_mul_carneiroLittmannKernelError_Ioi_zero : Filter.Tendsto
    (fun x : ℝ => x * carneiroLittmannKernelError x)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hBase : Filter.Tendsto
      (fun x : ℝ => x * (carneiroLittmannCumulative x - 1))
      (nhds 0) (nhds 0) := by
    have hId : ContinuousAt (fun x : ℝ => x) 0 := continuousAt_id
    have hCum : ContinuousAt carneiroLittmannCumulative 0 :=
      continuous_carneiroLittmannCumulative.continuousAt
    have hOne : ContinuousAt (fun _ : ℝ => (1 : ℝ)) 0 := continuousAt_const
    simpa using (hId.mul (hCum.sub hOne)).tendsto
  refine (hBase.mono_left inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < x := hx
  rw [carneiroLittmannKernelError, if_neg (not_le.mpr hx')]

private theorem tendsto_mul_carneiroLittmannKernelError_Iio_zero : Filter.Tendsto
    (fun x : ℝ => x * carneiroLittmannKernelError x)
    (nhdsWithin 0 (Set.Iio 0)) (nhds 0) := by
  have hBase : Filter.Tendsto
      (fun x : ℝ => x * carneiroLittmannCumulative x)
      (nhds 0) (nhds 0) := by
    have hId : ContinuousAt (fun x : ℝ => x) 0 := continuousAt_id
    have hCum : ContinuousAt carneiroLittmannCumulative 0 :=
      continuous_carneiroLittmannCumulative.continuousAt
    simpa using (hId.mul hCum).tendsto
  refine (hBase.mono_left inf_le_left).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x < 0 := hx
  rw [carneiroLittmannKernelError, if_pos hx'.le]

private theorem integrable_mul_carneiroLittmannDerivative :
    Integrable (fun x : ℝ => x * carneiroLittmannDerivative x) := by
  refine integrable_carneiroLittmannSincSquare.neg.congr ?_
  filter_upwards with x
  simpa using (congrArg Neg.neg
    (neg_mul_carneiroLittmannDerivative_eq_sincSquare x)).symm

/-- The Heaviside majorant error has total mass one. Consequently the signum
majorant error, which is twice this kernel, has the required mass two. -/
theorem integral_carneiroLittmannKernelError_eq_one :
    (∫ x : ℝ, carneiroLittmannKernelError x) = 1 := by
  have hDerivRight : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt carneiroLittmannKernelError
        (carneiroLittmannDerivative x) x := by
    intro x hx
    have hx' : 0 < x := hx
    have hBase := (hasDerivAt_carneiroLittmannCumulative x).sub_const 1
    apply hBase.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx'] with y hy
    rw [carneiroLittmannKernelError, if_neg (not_le.mpr hy)]
  have hDerivLeft : ∀ x ∈ Set.Iio (0 : ℝ),
      HasDerivAt carneiroLittmannKernelError
        (carneiroLittmannDerivative x) x := by
    intro x hx
    have hx' : x < 0 := hx
    have hBase := hasDerivAt_carneiroLittmannCumulative x
    apply hBase.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx'] with y hy
    rw [carneiroLittmannKernelError, if_pos hy.le]
  have hRight := integral_Ioi_deriv_mul_eq_sub
    (a := (0 : ℝ)) (u := fun x : ℝ => x)
    (u' := fun _ : ℝ => 1) (v := carneiroLittmannKernelError)
    (v' := carneiroLittmannDerivative)
    (fun x _ => hasDerivAt_id x) hDerivRight
    (by
      have h :=
        (integrable_carneiroLittmannKernelError.integrableOn (s := Set.Ioi (0 : ℝ))).add
          (integrable_mul_carneiroLittmannDerivative.integrableOn
            (s := Set.Ioi (0 : ℝ)))
      refine h.congr_fun ?_ measurableSet_Ioi
      intro x hx
      simp)
    tendsto_mul_carneiroLittmannKernelError_Ioi_zero
    tendsto_mul_carneiroLittmannKernelError_atTop
  have hLeft := integral_Iic_deriv_mul_eq_sub
    (a := (0 : ℝ)) (u := fun x : ℝ => x)
    (u' := fun _ : ℝ => 1) (v := carneiroLittmannKernelError)
    (v' := carneiroLittmannDerivative)
    (fun x _ => hasDerivAt_id x) hDerivLeft
    (by
      have h :=
        (integrable_carneiroLittmannKernelError.integrableOn (s := Set.Iic (0 : ℝ))).add
          (integrable_mul_carneiroLittmannDerivative.integrableOn
            (s := Set.Iic (0 : ℝ)))
      refine h.congr_fun ?_ measurableSet_Iic
      intro x hx
      simp)
    tendsto_mul_carneiroLittmannKernelError_Iio_zero
    tendsto_mul_carneiroLittmannKernelError_atBot
  rw [sub_self] at hRight hLeft
  simp only [one_mul] at hRight hLeft
  rw [integral_add
      integrable_carneiroLittmannKernelError.integrableOn
      integrable_mul_carneiroLittmannDerivative.integrableOn] at hRight hLeft
  have hSplitError :
      (∫ x in Set.Iic (0 : ℝ), carneiroLittmannKernelError x) +
          (∫ x in Set.Ioi (0 : ℝ), carneiroLittmannKernelError x) =
        ∫ x : ℝ, carneiroLittmannKernelError x := by
    simpa only [Set.compl_Iic] using
      (integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic
        integrable_carneiroLittmannKernelError)
  have hSplitDerivative :
      (∫ x in Set.Iic (0 : ℝ), x * carneiroLittmannDerivative x) +
          (∫ x in Set.Ioi (0 : ℝ), x * carneiroLittmannDerivative x) =
        ∫ x : ℝ, x * carneiroLittmannDerivative x := by
    simpa only [Set.compl_Iic] using
      (integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic
        integrable_mul_carneiroLittmannDerivative)
  have hMoment :
      (∫ x : ℝ, carneiroLittmannKernelError x) =
        -(∫ x : ℝ, x * carneiroLittmannDerivative x) := by
    linarith
  rw [hMoment]
  have hIntegralMoment :
      -(∫ x : ℝ, x * carneiroLittmannDerivative x) =
        ∫ x : ℝ, carneiroLittmannSincSquare x := by
    rw [← MeasureTheory.integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    exact neg_mul_carneiroLittmannDerivative_eq_sincSquare x
  rw [hIntegralMoment, integral_carneiroLittmannSincSquare_eq_base,
    integral_carneiroLittmannSincSquareBase_eq_one]

/-- The signum-majorant kernel is twice the Heaviside-majorant error. -/
noncomputable def carneiroLittmannRawKernel (x : ℝ) : ℝ :=
  2 * carneiroLittmannKernelError x

theorem integrable_carneiroLittmannRawKernel :
    Integrable carneiroLittmannRawKernel := by
  simpa only [carneiroLittmannRawKernel] using
    integrable_carneiroLittmannKernelError.const_mul 2

theorem carneiroLittmannRawKernel_nonneg (x : ℝ) :
    0 ≤ carneiroLittmannRawKernel x := by
  exact mul_nonneg (by norm_num) (carneiroLittmannKernelError_nonneg x)

theorem carneiroLittmannRawKernel_dilation_antitone
    {deltaSmall deltaLarge : ℝ}
    (hsmall : 0 < deltaSmall) (hle : deltaSmall ≤ deltaLarge) (t : ℝ) :
    carneiroLittmannRawKernel (deltaLarge * t) ≤
      carneiroLittmannRawKernel (deltaSmall * t) := by
  unfold carneiroLittmannRawKernel
  exact mul_le_mul_of_nonneg_left
    (carneiroLittmannKernelError_dilation_antitone hsmall hle t) (by norm_num)

theorem fourierKernel_carneiroLittmannRawKernel_zero :
    fourierKernel carneiroLittmannRawKernel 0 = (2 : ℂ) := by
  have hOfReal :
      (∫ t : ℝ, (carneiroLittmannKernelError t : ℂ) ∂MeasureTheory.volume) =
        Complex.ofReal
          (∫ t : ℝ, carneiroLittmannKernelError t ∂MeasureTheory.volume) := by
    exact integral_ofReal
  have hRealMass :
      (∫ t : ℝ, carneiroLittmannKernelError t ∂MeasureTheory.volume) = 1 :=
    integral_carneiroLittmannKernelError_eq_one
  unfold fourierKernel carneiroLittmannRawKernel
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_zero,
    zero_mul, mul_zero, Complex.exp_zero, mul_one]
  calc
    (∫ t : ℝ, (2 : ℂ) * (carneiroLittmannKernelError t : ℂ)) =
        (2 : ℂ) * ∫ t : ℝ, (carneiroLittmannKernelError t : ℂ) :=
      MeasureTheory.integral_const_mul _ _
    _ = (2 : ℂ) * Complex.ofReal
        (∫ t : ℝ, carneiroLittmannKernelError t ∂MeasureTheory.volume) := by
      exact congrArg (fun z : ℂ => (2 : ℂ) * z)
        hOfReal
    _ = 2 := by
      rw [hRealMass]
      norm_num

private theorem fourierKernel_carneiroLittmannDerivative_add_error (xi : ℝ) :
    fourierKernel carneiroLittmannDerivative xi +
        (Complex.I * xi) * fourierKernel carneiroLittmannKernelError xi = 1 := by
  have hPhaseContinuous : Continuous (carneiroLittmannFourierPhase xi) :=
    continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_carneiroLittmannFourierPhase xi x).continuousAt
  have hDerivativePhase : Integrable (fun x : ℝ =>
      (carneiroLittmannDerivative x : ℂ) *
        carneiroLittmannFourierPhase xi x) := by
    apply integrable_carneiroLittmannDerivative.ofReal.mul_bdd (c := 1)
    · exact hPhaseContinuous.aestronglyMeasurable
    · filter_upwards with x
      unfold carneiroLittmannFourierPhase
      have hNorm : ‖Complex.exp (Complex.I * ((xi : ℂ) * (x : ℂ)))‖ = 1 := by
        simpa only [Complex.ofReal_mul] using
          Complex.norm_exp_I_mul_ofReal (xi * x)
      exact hNorm.le
  have hErrorPhase : Integrable (fun x : ℝ =>
      (carneiroLittmannKernelError x : ℂ) *
        carneiroLittmannFourierPhase xi x) := by
    apply integrable_carneiroLittmannKernelError.ofReal.mul_bdd (c := 1)
    · exact hPhaseContinuous.aestronglyMeasurable
    · filter_upwards with x
      unfold carneiroLittmannFourierPhase
      have hNorm : ‖Complex.exp (Complex.I * ((xi : ℂ) * (x : ℂ)))‖ = 1 := by
        simpa only [Complex.ofReal_mul] using
          Complex.norm_exp_I_mul_ofReal (xi * x)
      exact hNorm.le
  have hErrorPhaseDerivative : Integrable (fun x : ℝ =>
      (carneiroLittmannKernelError x : ℂ) *
        (Complex.I * xi * carneiroLittmannFourierPhase xi x)) := by
    refine (hErrorPhase.const_mul (Complex.I * xi)).congr ?_
    filter_upwards with x
    ring
  have hIntegrable : Integrable (fun x : ℝ =>
      (carneiroLittmannDerivative x : ℂ) *
          carneiroLittmannFourierPhase xi x +
        (carneiroLittmannKernelError x : ℂ) *
          (Complex.I * xi * carneiroLittmannFourierPhase xi x)) :=
    hDerivativePhase.add hErrorPhaseDerivative
  have hDerivRight : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun y : ℝ => (carneiroLittmannKernelError y : ℂ))
        (carneiroLittmannDerivative x : ℂ) x := by
    intro x hx
    have hx' : 0 < x := hx
    have hBase := (hasDerivAt_carneiroLittmannCumulative x).sub_const 1
    have hError : HasDerivAt carneiroLittmannKernelError
        (carneiroLittmannDerivative x) x := by
      apply hBase.congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hx'] with y hy
      rw [carneiroLittmannKernelError, if_neg (not_le.mpr hy)]
    exact hError.ofReal_comp
  have hDerivLeft : ∀ x ∈ Set.Iio (0 : ℝ),
      HasDerivAt (fun y : ℝ => (carneiroLittmannKernelError y : ℂ))
        (carneiroLittmannDerivative x : ℂ) x := by
    intro x hx
    have hx' : x < 0 := hx
    have hBase := hasDerivAt_carneiroLittmannCumulative x
    have hError : HasDerivAt carneiroLittmannKernelError
        (carneiroLittmannDerivative x) x := by
      apply hBase.congr_of_eventuallyEq
      filter_upwards [Iio_mem_nhds hx'] with y hy
      rw [carneiroLittmannKernelError, if_pos hy.le]
    exact hError.ofReal_comp
  have hErrorRightZeroReal : Filter.Tendsto carneiroLittmannKernelError
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (carneiroLittmannCumulative 0 - 1)) := by
    have hBase : Filter.Tendsto
        (fun x : ℝ => carneiroLittmannCumulative x - 1)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (carneiroLittmannCumulative 0 - 1)) :=
      ((continuous_carneiroLittmannCumulative.sub
        continuous_const).continuousAt.tendsto).mono_left inf_le_left
    refine hBase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [carneiroLittmannKernelError, if_neg (not_le.mpr hx)]
  have hErrorLeftZeroReal : Filter.Tendsto carneiroLittmannKernelError
      (nhdsWithin 0 (Set.Iio 0))
      (nhds (carneiroLittmannCumulative 0)) := by
    have hBase : Filter.Tendsto carneiroLittmannCumulative
        (nhdsWithin 0 (Set.Iio 0))
        (nhds (carneiroLittmannCumulative 0)) :=
      continuous_carneiroLittmannCumulative.continuousAt.tendsto.mono_left
        inf_le_left
    refine hBase.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [carneiroLittmannKernelError, if_pos hx.le]
  have hPhaseRightZero : Filter.Tendsto (carneiroLittmannFourierPhase xi)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa [carneiroLittmannFourierPhase] using
      ((hasDerivAt_carneiroLittmannFourierPhase xi 0).continuousAt.tendsto).mono_left
        inf_le_left
  have hPhaseLeftZero : Filter.Tendsto (carneiroLittmannFourierPhase xi)
      (nhdsWithin 0 (Set.Iio 0)) (nhds 1) := by
    simpa [carneiroLittmannFourierPhase] using
      ((hasDerivAt_carneiroLittmannFourierPhase xi 0).continuousAt.tendsto).mono_left
        inf_le_left
  have hRightZero : Filter.Tendsto
      ((fun x : ℝ => (carneiroLittmannKernelError x : ℂ)) *
        carneiroLittmannFourierPhase xi)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((carneiroLittmannCumulative 0 - 1 : ℝ) : ℂ)) := by
    have hCast := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      hErrorRightZeroReal).mul hPhaseRightZero
    simpa only [mul_one] using hCast
  have hLeftZero : Filter.Tendsto
      ((fun x : ℝ => (carneiroLittmannKernelError x : ℂ)) *
        carneiroLittmannFourierPhase xi)
      (nhdsWithin 0 (Set.Iio 0))
      (nhds ((carneiroLittmannCumulative 0 : ℝ) : ℂ)) := by
    have hCast := (Complex.continuous_ofReal.continuousAt.tendsto.comp
      hErrorLeftZeroReal).mul hPhaseLeftZero
    simpa only [mul_one] using hCast
  have hRight := integral_Ioi_deriv_mul_eq_sub
    (a := (0 : ℝ))
    (u := fun x : ℝ => (carneiroLittmannKernelError x : ℂ))
    (u' := fun x : ℝ => (carneiroLittmannDerivative x : ℂ))
    (v := carneiroLittmannFourierPhase xi)
    (v' := fun x : ℝ =>
      Complex.I * xi * carneiroLittmannFourierPhase xi x)
    hDerivRight
    (fun x _ => hasDerivAt_carneiroLittmannFourierPhase xi x)
    hIntegrable.integrableOn hRightZero
    (tendsto_carneiroLittmannKernelError_mul_phase_atTop xi)
  have hLeft := integral_Iic_deriv_mul_eq_sub
    (a := (0 : ℝ))
    (u := fun x : ℝ => (carneiroLittmannKernelError x : ℂ))
    (u' := fun x : ℝ => (carneiroLittmannDerivative x : ℂ))
    (v := carneiroLittmannFourierPhase xi)
    (v' := fun x : ℝ =>
      Complex.I * xi * carneiroLittmannFourierPhase xi x)
    hDerivLeft
    (fun x _ => hasDerivAt_carneiroLittmannFourierPhase xi x)
    hIntegrable.integrableOn hLeftZero
    (tendsto_carneiroLittmannKernelError_mul_phase_atBot xi)
  have hRight' :
      (∫ x in Set.Ioi (0 : ℝ),
          (carneiroLittmannDerivative x : ℂ) *
              carneiroLittmannFourierPhase xi x +
            (carneiroLittmannKernelError x : ℂ) *
              (Complex.I * xi * carneiroLittmannFourierPhase xi x)) =
        0 - ((carneiroLittmannCumulative 0 - 1 : ℝ) : ℂ) := by
    simpa only [] using hRight
  have hLeft' :
      (∫ x in Set.Iic (0 : ℝ),
          (carneiroLittmannDerivative x : ℂ) *
              carneiroLittmannFourierPhase xi x +
            (carneiroLittmannKernelError x : ℂ) *
              (Complex.I * xi * carneiroLittmannFourierPhase xi x)) =
        ((carneiroLittmannCumulative 0 : ℝ) : ℂ) - 0 := by
    simpa only [] using hLeft
  have hSplit :
      (∫ x in Set.Iic (0 : ℝ),
          (carneiroLittmannDerivative x : ℂ) *
              carneiroLittmannFourierPhase xi x +
            (carneiroLittmannKernelError x : ℂ) *
              (Complex.I * xi * carneiroLittmannFourierPhase xi x)) +
        (∫ x in Set.Ioi (0 : ℝ),
          (carneiroLittmannDerivative x : ℂ) *
              carneiroLittmannFourierPhase xi x +
            (carneiroLittmannKernelError x : ℂ) *
              (Complex.I * xi * carneiroLittmannFourierPhase xi x)) =
        ∫ x : ℝ,
          (carneiroLittmannDerivative x : ℂ) *
              carneiroLittmannFourierPhase xi x +
            (carneiroLittmannKernelError x : ℂ) *
              (Complex.I * xi * carneiroLittmannFourierPhase xi x) := by
    simpa only [Set.compl_Iic] using
      (integral_add_compl (s := Set.Iic (0 : ℝ)) measurableSet_Iic hIntegrable)
  have hWhole :
      (∫ x : ℝ,
          (carneiroLittmannDerivative x : ℂ) *
              carneiroLittmannFourierPhase xi x +
            (carneiroLittmannKernelError x : ℂ) *
              (Complex.I * xi * carneiroLittmannFourierPhase xi x)) = 1 := by
    rw [← hSplit, hLeft', hRight']
    push_cast
    ring
  rw [integral_add hDerivativePhase hErrorPhaseDerivative] at hWhole
  have hDerivativeIntegral :
      (∫ x : ℝ, (carneiroLittmannDerivative x : ℂ) *
          carneiroLittmannFourierPhase xi x) =
        fourierKernel carneiroLittmannDerivative xi := by
    rfl
  have hErrorIntegral :
      (∫ x : ℝ, (carneiroLittmannKernelError x : ℂ) *
          (Complex.I * xi * carneiroLittmannFourierPhase xi x)) =
        (Complex.I * xi) *
          fourierKernel carneiroLittmannKernelError xi := by
    unfold fourierKernel carneiroLittmannFourierPhase
    calc
      (∫ x : ℝ, (carneiroLittmannKernelError x : ℂ) *
          (Complex.I * xi * Complex.exp (Complex.I * (xi * x)))) =
          ∫ x : ℝ, (Complex.I * xi) *
            ((carneiroLittmannKernelError x : ℂ) *
              Complex.exp (Complex.I * (xi * x))) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = (Complex.I * xi) *
          ∫ x : ℝ, (carneiroLittmannKernelError x : ℂ) *
            Complex.exp (Complex.I * (xi * x)) :=
        MeasureTheory.integral_const_mul _ _
  rw [hDerivativeIntegral, hErrorIntegral] at hWhole
  exact hWhole

/-- At frequencies outside the compact derivative spectrum, integration by
parts across the Heaviside jump gives the reciprocal Fourier tail required by
the Carneiro--Littmann Hilbert kernel. -/
theorem fourierKernel_carneiroLittmannRawKernel_of_two_pi_le_abs
    {xi : ℝ} (hxi : 2 * Real.pi ≤ |xi|) :
    fourierKernel carneiroLittmannRawKernel xi =
      (-2 * Complex.I) / xi := by
  have hxi0 : xi ≠ 0 := by
    intro hzero
    subst xi
    have htwoPi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    norm_num at hxi
    linarith
  have hDerivativeZero :
      fourierKernel carneiroLittmannDerivative xi = 0 :=
    fourierKernel_carneiroLittmannDerivative_eq_zero_of_two_pi_le_abs hxi
  have hRelation := fourierKernel_carneiroLittmannDerivative_add_error xi
  rw [hDerivativeZero, zero_add] at hRelation
  have hError : fourierKernel carneiroLittmannKernelError xi =
      -Complex.I / xi := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hxi0)).2
    calc
      fourierKernel carneiroLittmannKernelError xi * (xi : ℂ) =
          -Complex.I * ((Complex.I * xi) *
            fourierKernel carneiroLittmannKernelError xi) := by
        have hminusI_mul_I : -Complex.I * Complex.I = 1 := by
          rw [neg_mul, Complex.I_mul_I]
          norm_num
        rw [show -Complex.I * ((Complex.I * xi) *
            fourierKernel carneiroLittmannKernelError xi) =
            (-Complex.I * Complex.I) *
              ((xi : ℂ) * fourierKernel carneiroLittmannKernelError xi) by ring,
          hminusI_mul_I, one_mul]
        ring
      _ = -Complex.I := by rw [hRelation, mul_one]
  unfold fourierKernel carneiroLittmannRawKernel
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
  calc
    (∫ t : ℝ, (2 : ℂ) * (carneiroLittmannKernelError t : ℂ) *
        Complex.exp (Complex.I * (xi * t))) =
        ∫ t : ℝ, (2 : ℂ) * ((carneiroLittmannKernelError t : ℂ) *
          Complex.exp (Complex.I * (xi * t))) := by
      congr 1
      funext t
      ring
    _ = (2 : ℂ) * ∫ t : ℝ, (carneiroLittmannKernelError t : ℂ) *
          Complex.exp (Complex.I * (xi * t)) :=
      MeasureTheory.integral_const_mul _ _
    _ = (2 : ℂ) * fourierKernel carneiroLittmannKernelError xi := rfl
    _ = (-2 * Complex.I) / xi := by rw [hError]; ring

end DirichletPolynomial
end PrimeNumberTheorem
