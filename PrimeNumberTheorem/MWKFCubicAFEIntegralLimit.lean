import PrimeNumberTheorem.MWKFCubicAFETimeContinuity

open Complex Filter MeasureTheory
open scoped Interval

namespace PrimeNumberTheorem.MWKFCubic

/-!
# The finite-height AFE converges under the actual mollified integral

The height limit is taken at fixed physical scale `T`.  The proof constructs
an integrable majorant from the exact horizontal-edge error and the physical
test weight.  It asserts no uniform-in-`T` asymptotic estimate.
-/

/-- The complete physical multiplier of the horizontal contour error. -/
noncomputable def cubicAFEErrorAmplitude
    (W : CubicTestWeight) (T t : ℝ) : ℂ :=
  -(I : ℂ) / ((Real.pi : ℂ) * cubicAFEGammaProduct t 0) *
    (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ) *
    (W (t / T) : ℂ)

theorem continuous_cubicAFEErrorAmplitude (W : CubicTestWeight) (T : ℝ) :
    Continuous (cubicAFEErrorAmplitude W T) := by
  have hs : Continuous (fun t : ℝ ↦ cubicCriticalPoint t) := by
    unfold cubicCriticalPoint
    fun_prop
  have hu : Continuous (fun t : ℝ ↦ 1 - cubicCriticalPoint t) :=
    continuous_const.sub hs
  have hg : Continuous (fun t : ℝ ↦ (cubicAFEGammaProduct t 0)⁻¹) := by
    have hprod : Continuous (fun t : ℝ ↦
        (Gammaℝ (1 - cubicCriticalPoint t))⁻¹ *
          (Gammaℝ (cubicCriticalPoint t))⁻¹) :=
      (differentiable_Gammaℝ_inv.continuous.comp hu).mul
        (differentiable_Gammaℝ_inv.continuous.comp hs)
    convert hprod using 1
    funext t
    simp [cubicAFEGammaProduct, mul_inv_rev]
  have hscalar : Continuous (fun t : ℝ ↦
      -(I : ℂ) / ((Real.pi : ℂ) * cubicAFEGammaProduct t 0)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    exact continuous_const.mul (hg.mul continuous_const)
  have hmoll : Continuous (fun t : ℝ ↦
      (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
        (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Complex.continuous_normSq.comp
        (HardyTheorem.continuous_selbergMollifier_criticalLine
          (cubicMollifierLength T)
          (fun n ↦ (HardyTheorem.selbergMoebiusCoeff
            (cubicMollifierLength T) n : ℂ))))
  exact (hscalar.mul hmoll).mul
    (Complex.continuous_ofReal.comp
      (W.continuous.comp (continuous_id.div_const T)))

theorem hasCompactSupport_cubicAFEErrorAmplitude
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) :
    HasCompactSupport (cubicAFEErrorAmplitude W T) := by
  rw [show cubicAFEErrorAmplitude W T = fun t : ℝ ↦
      W (t / T) •
        (-(I : ℂ) / ((Real.pi : ℂ) * cubicAFEGammaProduct t 0) *
          (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
            (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ)) by
    funext t
    simp only [cubicAFEErrorAmplitude, Complex.real_smul]
    ring]
  exact (W.hasCompactSupport_dilate hT).smul_right

/-- Exact error with both mollifier factors and the original physical weight. -/
theorem cubicAFEMollifiedApproximation_sub_eq
    (W : CubicTestWeight) (T t : ℝ) {X V : ℝ}
    (hX : 1 / 2 < X) (hV : 0 < V) :
    cubicAFEMollifiedApproximation W T X V t - (cubicMomentIntegrand W T t : ℂ) =
      (∫ x : ℝ in -X..X,
        cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I)) *
      cubicAFEErrorAmplitude W T t := by
  calc
    _ = (2 * cubicAFEDoubleSumFinite t X V -
          (Complex.normSq (riemannZeta (cubicCriticalPoint t)) : ℂ)) *
        (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
          (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ) *
        (W (t / T) : ℂ) := by
      simp only [cubicAFEMollifiedApproximation, cubicMomentIntegrand,
        Complex.ofReal_mul, cubicCriticalPoint]
      ring
    _ = _ := by
      rw [two_mul_cubicAFEDoubleSumFinite_sub_normSq_eq t hX hV]
      unfold cubicAFEErrorAmplitude
      ring

/-- An integrable envelope for the finite-height error.  All time dependence
is inside `F`; the sole remaining height factor is `V^6 exp(-V^2)`. -/
theorem exists_integrable_cubicAFE_error_envelope
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0)
    {X : ℝ} (hX : 1 / 2 < X) :
    ∃ F : ℝ → ℝ, Integrable F ∧ (∀ t, 0 ≤ F t) ∧
      ∀ {V : ℝ}, 1 ≤ V → ∀ t : ℝ,
        ‖cubicAFEMollifiedApproximation W T X V t -
            (cubicMomentIntegrand W T t : ℂ)‖ ≤
          F t * (V ^ 6 * Real.exp (-V ^ 2)) := by
  have hX0 : 0 < X := by linarith
  obtain ⟨K, hK, hpoint⟩ :=
    exists_norm_cubicAFECompletedIntegrand_horizontal_le_uniform hX0.le
  let F : ℝ → ℝ := fun t ↦
    (2 * X * K) * (cubicAFEHorizontalScale t X 0 + 1) ^ 6 *
      ‖cubicAFEErrorAmplitude W T t‖
  have hscaleC : Continuous (fun t : ℝ ↦ cubicAFEHorizontalScale t X 0) := by
    unfold cubicAFEHorizontalScale cubicCriticalPoint
    fun_prop
  have hFC : Continuous F :=
    (continuous_const.mul ((hscaleC.add continuous_const).pow 6)).mul
      (continuous_cubicAFEErrorAmplitude W T).norm
  have hFcompact : HasCompactSupport F :=
    (hasCompactSupport_cubicAFEErrorAmplitude W hT).norm.mul_left
  refine ⟨F, hFC.integrable_of_hasCompactSupport hFcompact, ?_, ?_⟩
  · intro t
    dsimp [F]
    positivity
  · intro V hV t
    have hV0 : 0 ≤ V := by linarith
    have hB : 0 ≤ cubicAFEHorizontalScale t X 0 := by
      unfold cubicAFEHorizontalScale
      positivity
    have hscale0 : 0 ≤ cubicAFEHorizontalScale t X V := by
      unfold cubicAFEHorizontalScale
      positivity
    have hscale : cubicAFEHorizontalScale t X V ≤
        (cubicAFEHorizontalScale t X 0 + 1) * V := by
      have heq : cubicAFEHorizontalScale t X V =
          cubicAFEHorizontalScale t X 0 + V := by
        simp [cubicAFEHorizontalScale, abs_of_nonneg hV0]
      rw [heq]
      nlinarith [mul_nonneg hB (sub_nonneg.mpr hV)]
    have hH := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x : ℝ ↦ cubicAFECompletedIntegrand t ((x : ℂ) + (V : ℂ) * I))
      (a := -X) (b := X)
      (C := K * cubicAFEHorizontalScale t X V ^ 6 * Real.exp (-V ^ 2))
      (fun x hx ↦ hpoint t (Set.uIoc_subset_uIcc hx) hV)
    rw [cubicAFEMollifiedApproximation_sub_eq W T t hX (by linarith), norm_mul]
    calc
      _ ≤ (K * cubicAFEHorizontalScale t X V ^ 6 * Real.exp (-V ^ 2) *
          |X - -X|) * ‖cubicAFEErrorAmplitude W T t‖ :=
        mul_le_mul_of_nonneg_right hH (norm_nonneg _)
      _ ≤ (K * ((cubicAFEHorizontalScale t X 0 + 1) * V) ^ 6 *
          Real.exp (-V ^ 2) * |X - -X|) *
            ‖cubicAFEErrorAmplitude W T t‖ := by gcongr
      _ = F t * (V ^ 6 * Real.exp (-V ^ 2)) := by
        rw [abs_of_nonneg (by linarith : 0 ≤ X - -X)]
        dsimp [F]
        ring

/-- Unconditional passage of the finite-height AFE to the genuine full-line
mollified second moment.  `T` is fixed and nonzero; no analytic estimate is
assumed by the caller. -/
theorem tendsto_cubicAFEMollifiedMomentFinite
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0)
    {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEMollifiedMomentFinite W T X V)
      atTop (nhds (cubicMollifiedSecondMoment W T : ℂ)) := by
  obtain ⟨F, hFi, _hFnonneg, hbound⟩ :=
    exists_integrable_cubicAFE_error_envelope W hT hX
  have hgauss : Tendsto (fun V : ℝ ↦ V ^ 6 * Real.exp (-V ^ 2))
      atTop (nhds 0) := by
    have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
      (a := (1 : ℝ)) one_pos (6 : ℝ)
    apply (h.mono_left atTop_le_cocompact).congr'
    filter_upwards [eventually_gt_atTop 0] with V hV
    simp [abs_of_pos hV]
  have hmajor : Tendsto
      (fun V : ℝ ↦ (∫ t : ℝ, F t) * (V ^ 6 * Real.exp (-V ^ 2)))
      atTop (nhds 0) := by
    simpa using hgauss.const_mul (∫ t : ℝ, F t)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hmajor
  filter_upwards [eventually_ge_atTop 1] with V hV
  have herr : cubicAFEMollifiedMomentFinite W T X V -
      (cubicMollifiedSecondMoment W T : ℂ) =
      ∫ t : ℝ, cubicAFEMollifiedApproximation W T X V t -
        (cubicMomentIntegrand W T t : ℂ) := by
    have hactual : Integrable (fun t : ℝ ↦ (cubicMomentIntegrand W T t : ℂ)) :=
      (integrable_cubicMomentIntegrand W hT).ofReal
    calc
      _ = (∫ t : ℝ, cubicAFEMollifiedApproximation W T X V t) -
          (∫ t : ℝ, (cubicMomentIntegrand W T t : ℂ)) := by
        exact congrArg (fun z : ℂ ↦ cubicAFEMollifiedMomentFinite W T X V - z)
          (cubicComplexMollifiedSecondMoment_eq_ofReal W hT).symm
      _ = _ := (integral_sub
        (integrable_cubicAFEMollifiedApproximation W hT hX V) hactual).symm
  rw [herr]
  calc
    _ ≤ ∫ t : ℝ, F t * (V ^ 6 * Real.exp (-V ^ 2)) :=
      norm_integral_le_of_norm_le (hFi.mul_const _)
        (Eventually.of_forall (hbound hV))
    _ = _ := integral_mul_const _ _

end PrimeNumberTheorem.MWKFCubic
