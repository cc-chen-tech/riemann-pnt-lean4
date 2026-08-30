import PrimeNumberTheorem.MWKFCubicAFEIntegralLimit

open Complex Filter MeasureTheory
open scoped Interval BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The physical time integral and the full finite-height AFE series

The vertical height is kept finite throughout each interchange.  A jointly
continuous scalar and a time-independent summable Dirichlet envelope supply
dominated convergence.  The actual mollifier weights are specialized only
after this domination has been proved.
-/

private theorem continuous_Gamma_comp_of_re_pos
    {f : ℝ × ℝ → ℂ} (hf : Continuous f) (hpos : ∀ p, 0 < (f p).re) :
    Continuous (fun p ↦ Gammaℝ (f p)) := by
  have hi : Continuous (fun p ↦ (Gammaℝ (f p))⁻¹) :=
    differentiable_Gammaℝ_inv.continuous.comp hf
  have hii : Continuous (fun p ↦ ((Gammaℝ (f p))⁻¹)⁻¹) :=
    hi.inv₀ (fun p ↦ inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (hpos p)))
  simpa only [inv_inv] using hii

/-- Joint continuity, not merely continuity along a line of fixed time. -/
theorem continuous_cubicAFEScalar_joint {X : ℝ} (hX : 1 / 2 < X) :
    Continuous (fun p : ℝ × ℝ ↦
      cubicAFEScalar p.1 (cubicAFEVerticalPoint X p.2)) := by
  let s : ℝ × ℝ → ℂ := fun p ↦ cubicCriticalPoint p.1
  let u : ℝ × ℝ → ℂ := fun p ↦ 1 - s p
  let z : ℝ × ℝ → ℂ := fun p ↦ cubicAFEVerticalPoint X p.2
  have hs : Continuous s := by unfold s cubicCriticalPoint; fun_prop
  have hu : Continuous u := continuous_const.sub hs
  have hz : Continuous z := by unfold z cubicAFEVerticalPoint; fun_prop
  have hs0 : ∀ p, s p ≠ 0 := fun p ↦ cubicCriticalPoint_ne_zero p.1
  have hu0 : ∀ p, u p ≠ 0 := fun p ↦ one_sub_cubicCriticalPoint_ne_zero p.1
  have hz0 : ∀ p, z p ≠ 0 := by
    intro p h
    have hre := congrArg Complex.re h
    simp [z, cubicAFEVerticalPoint] at hre
    linarith
  have hGs : Continuous (fun p ↦ Gammaℝ (s p)) :=
    continuous_Gamma_comp_of_re_pos hs (fun p ↦ by norm_num [s, cubicCriticalPoint])
  have hGu : Continuous (fun p ↦ Gammaℝ (u p)) :=
    continuous_Gamma_comp_of_re_pos hu (fun p ↦ by norm_num [u, s, cubicCriticalPoint])
  have hGsz : Continuous (fun p ↦ Gammaℝ (s p + z p)) :=
    continuous_Gamma_comp_of_re_pos (hs.add hz) (fun p ↦ by
      simp [s, z, cubicCriticalPoint, cubicAFEVerticalPoint]
      linarith)
  have hGuz : Continuous (fun p ↦ Gammaℝ (u p + z p)) :=
    continuous_Gamma_comp_of_re_pos (hu.add hz) (fun p ↦ by
      norm_num [u, s, z, cubicCriticalPoint, cubicAFEVerticalPoint]
      linarith)
  have hkernel : Continuous (fun p ↦ cubicAFEKernelG p.1 (z p)) := by
    unfold cubicAFEKernelG cubicAFEPoleCanceller
    exact (Complex.continuous_exp.comp (hz.pow 2)).mul
      (((continuous_const.sub (continuous_const.mul (hz.pow 2))).mul
        (continuous_const.sub ((hz.pow 2).div₀ (hs.pow 2)
          (fun p ↦ pow_ne_zero 2 (hs0 p))))).mul
        (continuous_const.sub ((hz.pow 2).div₀ (hu.pow 2)
          (fun p ↦ pow_ne_zero 2 (hu0 p)))))
  have hgamma0 : ∀ p, Gammaℝ (s p) * Gammaℝ (u p) ≠ 0 := by
    intro p
    simpa [s, u, cubicAFEGammaProduct] using cubicAFEGammaProduct_zero_ne p.1
  have hform : (fun p : ℝ × ℝ ↦
      cubicAFEScalar p.1 (cubicAFEVerticalPoint X p.2)) =
      fun p ↦ cubicAFEKernelG p.1 (z p) *
        (Gammaℝ (s p + z p) * Gammaℝ (u p + z p)) /
          (Gammaℝ (s p) * Gammaℝ (u p)) / z p := by
    funext p
    simp [cubicAFEScalar, cubicAFEGammaProduct, s, u, z]
  rw [hform]
  exact ((hkernel.mul (hGsz.mul hGuz)).div₀ (hGs.mul hGu) hgamma0).div₀ hz hz0

/-- The summable Dirichlet envelope depends on neither physical time nor
vertical height. -/
theorem norm_cubicAFEDirichletTerm_time_vertical_eq
    (t X y : ℝ) (p : ℕ × ℕ) :
    ‖cubicAFEDirichletTerm t (cubicAFEVerticalPoint X y) p‖ =
      ‖cubicAFEDirichletTerm 0 (X : ℂ) p‖ := by
  simp only [cubicAFEDirichletTerm, norm_mul, norm_div, norm_one]
  have hb1 : (p.1 + 1 : ℂ) = (((p.1 + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  have hb2 : (p.2 + 1 : ℂ) = (((p.2 + 1 : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [hb1, hb2,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp [cubicCriticalPoint, cubicAFEVerticalPoint]

theorem continuous_cubicAFENormalizedDirichletTerm_joint
    {X : ℝ} (hX : 1 / 2 < X) (p : ℕ × ℕ) :
    Continuous (fun v : ℝ × ℝ ↦
      cubicAFENormalizedDirichletTerm v.1 (cubicAFEVerticalPoint X v.2) p) := by
  change Continuous (fun v : ℝ × ℝ ↦
    cubicAFEScalar v.1 (cubicAFEVerticalPoint X v.2) *
      cubicAFEDirichletTerm v.1 (cubicAFEVerticalPoint X v.2) p)
  apply (continuous_cubicAFEScalar_joint hX).mul
  have hb1 : (p.1 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p.1
  have hb2 : (p.2 + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p.2
  let : NeZero (p.1 + 1 : ℂ) := ⟨hb1⟩
  let : NeZero (p.2 + 1 : ℂ) := ⟨hb2⟩
  have hc1 : Continuous (fun v : ℝ × ℝ ↦
      (p.1 + 1 : ℂ) ^ (cubicCriticalPoint v.1 + cubicAFEVerticalPoint X v.2)) := by
    apply (continuous_const_cpow (p.1 + 1 : ℂ)).comp
    unfold cubicCriticalPoint cubicAFEVerticalPoint
    fun_prop
  have hc2 : Continuous (fun v : ℝ × ℝ ↦
      (p.2 + 1 : ℂ) ^ (1 - cubicCriticalPoint v.1 + cubicAFEVerticalPoint X v.2)) := by
    apply (continuous_const_cpow (p.2 + 1 : ℂ)).comp
    unfold cubicCriticalPoint cubicAFEVerticalPoint
    fun_prop
  exact (continuous_const.div₀ hc1 (fun _ ↦
    Complex.cpow_ne_zero_iff.mpr (Or.inl hb1))).mul
      (continuous_const.div₀ hc2 (fun _ ↦
        Complex.cpow_ne_zero_iff.mpr (Or.inl hb2)))

theorem continuous_cubicAFEWeightFinite_time
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) (p : ℕ × ℕ) :
    Continuous (fun t : ℝ ↦ cubicAFEWeightFinite t X V p) := by
  unfold cubicAFEWeightFinite
  have hjoint : Continuous (Function.uncurry (fun t y : ℝ ↦
      cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p)) :=
    continuous_cubicAFENormalizedDirichletTerm_joint hX p
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hjoint (-V) V)

/-- The scalar factor in a uniform arithmetic envelope.  The absolute value
also covers negative and zero finite heights without changing orientation. -/
noncomputable def cubicAFEWeightEnvelope (X V t : ℝ) : ℝ :=
  ‖(1 / (2 * Real.pi) : ℂ)‖ *
    |∫ y : ℝ in -V..V, ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖|

theorem continuous_cubicAFEWeightEnvelope
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    Continuous (cubicAFEWeightEnvelope X V) := by
  have hjoint : Continuous (Function.uncurry (fun t y : ℝ ↦
      ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖)) :=
    (continuous_cubicAFEScalar_joint hX).norm
  exact continuous_const.mul
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hjoint (-V) V).abs

theorem norm_cubicAFEWeightFinite_le_envelope
    (t X V : ℝ) (p : ℕ × ℕ) :
    ‖cubicAFEWeightFinite t X V p‖ ≤
      cubicAFEWeightEnvelope X V t * ‖cubicAFEDirichletTerm 0 (X : ℂ) p‖ := by
  have hnorm :
      (fun y : ℝ ↦ ‖cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p‖) =
      fun y : ℝ ↦ ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖ *
        ‖cubicAFEDirichletTerm 0 (X : ℂ) p‖ := by
    funext y
    rw [cubicAFENormalizedDirichletTerm_eq, norm_mul,
      norm_cubicAFEDirichletTerm_time_vertical_eq]
  have hi := intervalIntegral.norm_integral_le_abs_integral_norm
    (f := fun y : ℝ ↦
      cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p)
    (a := -V) (b := V) (μ := volume)
  rw [hnorm, intervalIntegral.integral_mul_const, abs_mul,
    abs_of_nonneg (norm_nonneg _)] at hi
  calc
    ‖cubicAFEWeightFinite t X V p‖ = ‖(1 / (2 * Real.pi) : ℂ)‖ *
        ‖∫ y : ℝ in -V..V,
          cubicAFENormalizedDirichletTerm t (cubicAFEVerticalPoint X y) p‖ :=
      norm_mul _ _
    _ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ *
        (|∫ y : ℝ in -V..V, ‖cubicAFEScalar t (cubicAFEVerticalPoint X y)‖| *
          ‖cubicAFEDirichletTerm 0 (X : ℂ) p‖) :=
      mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    _ = _ := by unfold cubicAFEWeightEnvelope; ring

/-- Series--time-integral interchange for any actual continuous compact
physical multiplier.  Domination and summability are conclusions of the
proof, not caller-supplied analytic hypotheses. -/
theorem hasSum_integral_cubicAFEWeightFinite_mul
    {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) {b : ℝ → ℂ}
    (hb : Continuous b) (hbc : HasCompactSupport b) :
    HasSum (fun p : ℕ × ℕ ↦ ∫ t : ℝ, cubicAFEWeightFinite t X V p * b t)
      (∫ t : ℝ, cubicAFEDoubleSumFinite t X V * b t) := by
  let a : ℕ × ℕ → ℝ := fun p ↦ ‖cubicAFEDirichletTerm 0 (X : ℂ) p‖
  let C : ℝ → ℝ := fun t ↦ cubicAFEWeightEnvelope X V t * ‖b t‖
  have ha : Summable a := summable_norm_cubicAFEDirichletTerm 0 hX
  have hC : Continuous C := (continuous_cubicAFEWeightEnvelope hX V).mul hb.norm
  have hCcompact : HasCompactSupport C := hbc.norm.mul_left
  have hCi : Integrable C := hC.integrable_of_hasCompactSupport hCcompact
  apply MeasureTheory.hasSum_integral_of_dominated_convergence (bound := fun p t ↦ C t * a p)
  · intro p
    exact ((continuous_cubicAFEWeightFinite_time hX V p).mul hb).aestronglyMeasurable
  · intro p
    filter_upwards with t
    rw [norm_mul]
    calc
      _ ≤ (cubicAFEWeightEnvelope X V t * a p) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right (norm_cubicAFEWeightFinite_le_envelope t X V p)
          (norm_nonneg _)
      _ = C t * a p := by dsimp [C]; ring
  · filter_upwards with t
    exact ha.mul_left (C t)
  · simpa only [tsum_mul_left] using hCi.mul_const (∑' p, a p)
  · filter_upwards with t
    exact (summable_cubicAFEWeightFinite t hX V).hasSum.mul_right (b t)

/-- The exact outer multiplier of one ordered mollifier pair. -/
noncomputable def cubicAFEPairOuterWeight
    (W : CubicTestWeight) (T : ℝ) (d e : ℕ) (t : ℝ) : ℂ :=
  (cubicMollifierCoefficient T d : ℂ) *
    (cubicMollifierCoefficient T e : ℂ) * 2 *
    ((1 / (d : ℂ) ^ cubicCriticalPoint t) *
      (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t)) *
    (W (t / T) : ℂ)

theorem continuous_cubicAFEPairOuterWeight
    (W : CubicTestWeight) (T : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    Continuous (cubicAFEPairOuterWeight W T d e) := by
  have hW : Continuous (fun t : ℝ ↦ (W (t / T) : ℂ)) :=
    Complex.continuous_ofReal.comp (W.continuous.comp (continuous_id.div_const T))
  unfold cubicAFEPairOuterWeight
  simp_rw [cubicCriticalPoint, cubicCriticalPair_eq_exp hd he]
  fun_prop

theorem hasCompactSupport_cubicAFEPairOuterWeight
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) (d e : ℕ) :
    HasCompactSupport (cubicAFEPairOuterWeight W T d e) := by
  rw [show cubicAFEPairOuterWeight W T d e = fun t : ℝ ↦
      W (t / T) • ((cubicMollifierCoefficient T d : ℂ) *
        (cubicMollifierCoefficient T e : ℂ) * 2 *
        ((1 / (d : ℂ) ^ cubicCriticalPoint t) *
          (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t))) by
    funext t
    simp only [cubicAFEPairOuterWeight, Complex.real_smul]
    ring]
  exact (W.hasCompactSupport_dilate hT).smul_right

theorem cubicAFEMollifierPairApproximation_eq_outerWeight
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (t : ℝ) :
    cubicAFEMollifierPairApproximation W T X V d e t =
      cubicAFEDoubleSumFinite t X V * cubicAFEPairOuterWeight W T d e t := by
  unfold cubicAFEMollifierPairApproximation cubicAFEPairOuterWeight
  ring

theorem cubicAFECombinedSummandFinite_eq_outerWeight
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (t : ℝ) (p : ℕ × ℕ) :
    cubicAFECombinedSummandFinite W T X V d e t p =
      cubicAFEWeightFinite t X V p * cubicAFEPairOuterWeight W T d e t := by
  rw [cubicAFEWeightFinite_eq_arithmetic_mul_productWeight]
  unfold cubicAFECombinedSummandFinite cubicAFECombinedArithmeticFactor
    cubicAFEPairOuterWeight
  ring

theorem integrable_cubicAFEMollifierPairApproximation
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    Integrable (cubicAFEMollifierPairApproximation W T X V d e) := by
  rw [show cubicAFEMollifierPairApproximation W T X V d e = fun t : ℝ ↦
      cubicAFEDoubleSumFinite t X V * cubicAFEPairOuterWeight W T d e t by
    funext t
    exact cubicAFEMollifierPairApproximation_eq_outerWeight W T X V d e t]
  exact ((continuous_cubicAFEDoubleSumFinite_time hX V).mul
    (continuous_cubicAFEPairOuterWeight W T hd he)).integrable_of_hasCompactSupport
      (hasCompactSupport_cubicAFEPairOuterWeight W hT d e).mul_left

/-- Exact physical integral of the complete combined arithmetic series for
one ordered pair.  The two tapered Möbius coefficients are never replaced. -/
theorem hasSum_integral_cubicAFECombinedSummandFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : d ≠ 0) (he : e ≠ 0) :
    HasSum (fun p : ℕ × ℕ ↦ ∫ t : ℝ,
      cubicAFECombinedSummandFinite W T X V d e t p)
      (∫ t : ℝ, cubicAFEMollifierPairApproximation W T X V d e t) := by
  have h := hasSum_integral_cubicAFEWeightFinite_mul hX V
    (continuous_cubicAFEPairOuterWeight W T hd he)
    (hasCompactSupport_cubicAFEPairOuterWeight W hT d e)
  convert h using 1
  · funext p
    apply integral_congr_ae
    exact Eventually.of_forall (fun t ↦
      cubicAFECombinedSummandFinite_eq_outerWeight W T X V d e t p)
  · apply integral_congr_ae
    exact Eventually.of_forall (fun t ↦
      cubicAFEMollifierPairApproximation_eq_outerWeight W T X V d e t)

private theorem cubicSupport_ne_zero {T : ℝ} {n : ℕ}
    (hn : n ∈ cubicMollifierSupport T) : n ≠ 0 := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  omega

/-- Full ordered `(d,e,p)` expansion with all arithmetic sums outside the
genuine physical time integral.  This is an equality at every finite height. -/
theorem cubicAFEMollifiedMomentFinite_eq_tripleIntegral
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) :
    cubicAFEMollifiedMomentFinite W T X V =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        ∑' p : ℕ × ℕ, ∫ t : ℝ,
          cubicAFECombinedSummandFinite W T X V d e t p := by
  have hpair : ∀ d ∈ cubicMollifierSupport T, ∀ e ∈ cubicMollifierSupport T,
      Integrable (cubicAFEMollifierPairApproximation W T X V d e) := by
    intro d hd e he
    exact integrable_cubicAFEMollifierPairApproximation W hT hX V
      (cubicSupport_ne_zero hd) (cubicSupport_ne_zero he)
  unfold cubicAFEMollifiedMomentFinite
  rw [show cubicAFEMollifiedApproximation W T X V = fun t : ℝ ↦
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        cubicAFEMollifierPairApproximation W T X V d e t by
    funext t
    exact cubicAFEMollifiedApproximation_eq_pairSum W T X V t]
  rw [integral_finsetSum (cubicMollifierSupport T)
    (fun d hd ↦ integrable_finsetSum (cubicMollifierSupport T) (hpair d hd))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [integral_finsetSum (cubicMollifierSupport T) (hpair d hd)]
  apply Finset.sum_congr rfl
  intro e he
  exact (hasSum_integral_cubicAFECombinedSummandFinite W hT hX V
    (cubicSupport_ne_zero hd) (cubicSupport_ne_zero he)).tsum_eq.symm

/-- Exact infinite-height representation of the literal moment as the limit
of the fully integrated triple arithmetic expression.  This does not move
the height limit through the infinite arithmetic series. -/
theorem tendsto_cubicAFETripleIntegral
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        ∑' p : ℕ × ℕ, ∫ t : ℝ,
          cubicAFECombinedSummandFinite W T X V d e t p)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  apply (tendsto_cubicAFEMollifiedMomentFinite W hT hX).congr'
  exact Eventually.of_forall (fun V ↦
    cubicAFEMollifiedMomentFinite_eq_tripleIntegral W hT hX V)

end PrimeNumberTheorem.MWKFCubic
