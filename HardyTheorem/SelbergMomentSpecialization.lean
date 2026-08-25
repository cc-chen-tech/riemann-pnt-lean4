import HardyTheorem.SelbergMomentParameter
import HardyTheorem.SelbergFirstMomentSliding
import HardyTheorem.SelbergSlidingSecondMoment
import HardyTheorem.SelbergSlidingAbsoluteSecondMoment
import MathlibAux.StrictCancellationMeasure

open Complex Filter MeasureTheory Set
open scoped Interval

namespace HardyTheorem

/-!
# S2--S4 at the final common Selberg parameters

This module puts all three moment estimates on the same real completed
mollified function with `delta=1/T`, `X=floor(T^(1/32))`, and
`H=2*pi/log(X^a)`.
-/

private theorem normSq_interval_selbergCompletedMollifiedFComplex_eq_sq_abs
    (delta : ℝ) (X : ℕ) {t H : ℝ} :
    Complex.normSq
        (∫ z in t..t + H,
          selbergCompletedMollifiedFComplex delta X z) =
      |∫ z in t..t + H, selbergCompletedMollifiedF delta X z| ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have hreal := intervalIntegral.integral_ofReal
    (a := t) (b := t + H)
    (f := selbergCompletedMollifiedF delta X) (μ := volume)
  rw [show (∫ z in t..t + H,
      selbergCompletedMollifiedFComplex delta X z) =
        ((∫ z in t..t + H,
          selbergCompletedMollifiedF delta X z : ℝ) : ℂ) by
      simpa only [selbergCompletedMollifiedFComplex] using hreal]
  simp

private theorem norm_selbergCompletedMollifiedFComplex_eq_abs
    (delta : ℝ) (X : ℕ) (t : ℝ) :
    ‖selbergCompletedMollifiedFComplex delta X t‖ =
      |selbergCompletedMollifiedF delta X t| := by
  simp [selbergCompletedMollifiedFComplex]

/-- The completed real absolute sliding mass is globally square-integrable
at every admissible positive tilt and nonnegative window length. -/
theorem integrable_sq_slidingAbsoluteMass_selbergCompletedMollifiedF
    {delta H : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (hH : 0 ≤ H) :
    Integrable (fun t =>
      (MathlibAux.slidingAbsoluteMass
        (selbergCompletedMollifiedF delta X) H t) ^ 2) := by
  have hcomplex := MathlibAux.integrable_sq_abs_slidingWindow
    (Complex.continuous_ofReal.comp
      (continuous_selbergCompletedMollifiedF delta X))
    (memLp_two_selbergCompletedMollifiedF_complex hdelta hdeltaPi X) hH
  refine hcomplex.congr (Filter.Eventually.of_forall fun t => ?_)
  dsimp only [MathlibAux.slidingAbsoluteMass,
    MathlibAux.slidingWindowMass]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _hu
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]

/-- S2--S4 with one common final parameter choice.  The S3 logarithmic
ratio is simplified using `log T / log X ≤ 64`. -/
theorem exists_fixed_parameter_selberg_moment_bounds
    {a : ℝ} (ha : 0 < a) (haSix : a ≤ 6) :
    ∃ c₁ C₂ C₃ T0 : ℝ,
      0 < c₁ ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        let X := selbergFirstMomentCutoff T
        let H := selbergMomentWindow a T
        let F := selbergCompletedMollifiedF (1 / T) X
        0 < H ∧ H ≤ T / 2 ∧
        c₁ * (H * T ^ (3 / 4 : ℝ)) ≤
          ∫ t in 0..T, MathlibAux.slidingAbsoluteMass F H t ∧
        (∫ t in 0..T,
          (MathlibAux.slidingSignedAbsMass F H t) ^ 2) ≤
            C₂ * (H * T ^ (1 / 2 : ℝ) /
              Real.log (X : ℝ)) ∧
        Integrable (fun t =>
          (MathlibAux.slidingAbsoluteMass F H t) ^ 2) ∧
        (∫ t : ℝ,
          (MathlibAux.slidingAbsoluteMass F H t) ^ 2) ≤
            C₃ * (H ^ 2 * T ^ (1 / 2 : ℝ)) := by
  have hc : (0 : ℝ) ≤ 1 / 32 := by norm_num
  have hcEight : (1 / 32 : ℝ) < 1 / 8 := by norm_num
  have hac : (a + 2) * (1 / 32 : ℝ) ≤ 1 / 4 := by
    nlinarith
  obtain ⟨C₂, hC₂, hS2⟩ :=
    exists_integral_normSq_sliding_selbergCompletedMollifiedF_le
      ha.le hc hcEight hac
  obtain ⟨C₃raw, hC₃raw, hS3⟩ :=
    exists_integral_sq_abs_selbergCompletedMollifiedF_sliding_le
      ha.le hc hcEight hac
  obtain ⟨c₁, Tfirst, hc₁, hTfirst, hS4⟩ :=
    exists_pos_rpow_three_quarters_selbergSlidingFirstMoment_lower
  have hparam := eventually_selbergMomentParameter_conditions ha
  obtain ⟨Tparam, hparamAfter⟩ := eventually_atTop.1 hparam
  let T0 := max Tfirst Tparam
  refine ⟨c₁, C₂, 64 * C₃raw, T0, hc₁, hC₂, by positivity,
    hTfirst.trans (le_max_left _ _), ?_⟩
  intro T hT
  have hTfirst' : Tfirst ≤ T := (le_max_left _ _).trans hT
  have hTparam' : Tparam ≤ T := (le_max_right _ _).trans hT
  rcases hparamAfter T hTparam' with
    ⟨hdelta, hdeltaOne, hdeltaPi, hXtwo, hXexp, hXpow,
      hlogXa, hlogDelta, hlogRatio, hH, hHT⟩
  let X := selbergFirstMomentCutoff T
  let H := selbergMomentWindow a T
  let F := selbergCompletedMollifiedF (1 / T) X
  have hTpos : 0 < T := one_div_pos.mp hdelta
  have hdeltaHalf : (1 / T) ^ (-(1 / 2 : ℝ)) =
      T ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    congr 1
    field_simp
  have hInvDelta : 1 / (1 / T) = T := by field_simp
  have hS2T := hS2 X (1 / T) 0 T hdelta hdeltaOne hXtwo hdeltaPi
    hXexp hXpow hlogXa hTpos.le
  have hS2real :
      (∫ t in 0..T,
        (MathlibAux.slidingSignedAbsMass F H t) ^ 2) ≤
          C₂ * (H * T ^ (1 / 2 : ℝ) / Real.log (X : ℝ)) := by
    simpa only [X, H, F, selbergMomentWindow,
      MathlibAux.slidingSignedAbsMass, MathlibAux.slidingWindowMass,
      normSq_interval_selbergCompletedMollifiedFComplex_eq_sq_abs,
      hdeltaHalf] using hS2T
  have hS3T := hS3 X (1 / T) H hdelta hdeltaOne hXtwo hdeltaPi
    hXexp hXpow hlogDelta hH.le
  have hS3realRaw :
      (∫ t : ℝ, (MathlibAux.slidingAbsoluteMass F H t) ^ 2) ≤
        C₃raw * (H ^ 2 *
          (T ^ (1 / 2 : ℝ) * Real.log T /
            Real.log (X : ℝ))) := by
    simpa only [X, H, F, MathlibAux.slidingAbsoluteMass,
      MathlibAux.slidingWindowMass,
      norm_selbergCompletedMollifiedFComplex_eq_abs,
      hdeltaHalf, hInvDelta] using hS3T
  have hlogXpos : 0 < Real.log (X : ℝ) := by
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hXexp)
  have hratioRewrite :
      T ^ (1 / 2 : ℝ) * Real.log T / Real.log (X : ℝ) =
        T ^ (1 / 2 : ℝ) *
          (Real.log T / Real.log (X : ℝ)) := by ring
  have hS3real :
      (∫ t : ℝ, (MathlibAux.slidingAbsoluteMass F H t) ^ 2) ≤
        (64 * C₃raw) * (H ^ 2 * T ^ (1 / 2 : ℝ)) := by
    calc
      _ ≤ C₃raw * (H ^ 2 *
          (T ^ (1 / 2 : ℝ) * Real.log T /
            Real.log (X : ℝ))) := hS3realRaw
      _ ≤ C₃raw * (H ^ 2 *
          (T ^ (1 / 2 : ℝ) * 64)) := by
        gcongr
        rw [hratioRewrite]
        have hlogRatio' :
            Real.log T / Real.log (X : ℝ) ≤ 64 := by
          simpa only [X, hInvDelta] using hlogRatio
        exact mul_le_mul_of_nonneg_left hlogRatio'
          (Real.rpow_nonneg hTpos.le _)
      _ = (64 * C₃raw) * (H ^ 2 * T ^ (1 / 2 : ℝ)) := by ring
  refine ⟨hH, hHT, ?_, hS2real, ?_, hS3real⟩
  · simpa only [X, H, F, MathlibAux.slidingAbsoluteMass,
      MathlibAux.slidingWindowMass] using hS4 T H hTfirst' hH.le hHT
  · exact integrable_sq_slidingAbsoluteMass_selbergCompletedMollifiedF
      hdelta hdeltaPi X hH.le

end HardyTheorem
