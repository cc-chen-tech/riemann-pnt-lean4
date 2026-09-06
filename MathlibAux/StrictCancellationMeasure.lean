import MathlibAux.FirstMomentGapMeasure
import MathlibAux.SlidingSignedMassSecondMoment

open MeasureTheory Set
open scoped Interval

namespace MathlibAux

/-!
# Positive measure of strict-cancellation windows

For a continuous real function `f`, let `A(t)` be the absolute mass in the
forward window and `B(t)` the absolute value of its signed mass.  The triangle
inequality gives `B ≤ A`.  Thus `A-B` is supported exactly on starts with
strict cancellation.  A lower first moment for `A`, an upper first moment
for `B`, and an `L²` bound for `A` force that support to have positive
measure.
-/

noncomputable def slidingAbsoluteMass (f : ℝ → ℝ) (H t : ℝ) : ℝ :=
  slidingWindowMass (fun u => |f u|) H t

noncomputable def slidingSignedAbsMass (f : ℝ → ℝ) (H t : ℝ) : ℝ :=
  |slidingWindowMass f H t|

def strictCancellationStarts (f : ℝ → ℝ) (H : ℝ) : Set ℝ :=
  {t | slidingSignedAbsMass f H t < slidingAbsoluteMass f H t}

/-- Abstract Selberg S5 in product form.  `MS` is the signed sliding second
moment and `MA` the absolute sliding second moment. -/
theorem firstMomentGap_sq_le_strictCancellation_measure_mul_absSecondMoment
    {f : ℝ → ℝ} (hf : Continuous f) {T H L MS MA : ℝ}
    (hT : 0 ≤ T) (hH : 0 ≤ H) (hMS : 0 ≤ MS)
    (hfirst : L ≤ ∫ t in 0..T, slidingAbsoluteMass f H t)
    (hsignedSecond :
      (∫ t in 0..T, (slidingSignedAbsMass f H t) ^ 2) ≤ MS)
    (habsSecondInt : Integrable (fun t => (slidingAbsoluteMass f H t) ^ 2))
    (habsSecond : (∫ t : ℝ, (slidingAbsoluteMass f H t) ^ 2) ≤ MA)
    (hgap : 0 ≤ L - Real.sqrt (T * MS)) :
    (L - Real.sqrt (T * MS)) ^ 2 ≤
      volume.real (Icc 0 T ∩ strictCancellationStarts f H) * MA := by
  let s : Set ℝ := Icc 0 T
  let A : ℝ → ℝ := slidingAbsoluteMass f H
  let B : ℝ → ℝ := slidingSignedAbsMass f H
  let e : Set ℝ := s ∩ strictCancellationStarts f H
  have hAcont : Continuous A := by
    exact continuous_slidingWindowMass_of_continuous hf.abs H
  have hBcont : Continuous B := by
    exact (continuous_slidingWindowMass_of_continuous hf H).abs
  have hBA (t : ℝ) : B t ≤ A t := by
    dsimp only [A, B, slidingSignedAbsMass, slidingAbsoluteMass,
      slidingWindowMass]
    exact intervalIntegral.abs_integral_le_integral_abs
      (show t ≤ t + H by linarith)
  have hs : MeasurableSet s := measurableSet_Icc
  have he : MeasurableSet e := by
    change MeasurableSet (s ∩ {t | B t < A t})
    exact hs.inter (measurableSet_lt hBcont.measurable hAcont.measurable)
  have hes : e ⊆ s := inter_subset_left
  have hμe : volume e ≠ ⊤ :=
    measure_ne_top_of_subset hes measure_Icc_lt_top.ne
  have hAint : IntegrableOn A s volume :=
    hAcont.continuousOn.integrableOn_compact isCompact_Icc
  have hBint : IntegrableOn B s volume :=
    hBcont.continuousOn.integrableOn_compact isCompact_Icc
  have hDsqInt : IntegrableOn (fun t => (A t - B t) ^ 2) e volume := by
    exact (((hAcont.sub hBcont).pow 2).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set hes
  have hzero : ∀ t ∈ s \ e, A t - B t = 0 := by
    intro t ht
    have hnot : ¬ B t < A t := by
      intro hlt
      exact ht.2 ⟨ht.1, hlt⟩
    exact sub_eq_zero.mpr (le_antisymm (le_of_not_gt hnot) (hBA t))
  have hBnonneg : 0 ≤ ∫ t in s, B t :=
    setIntegral_nonneg hs fun t _ => abs_nonneg _
  have hBsq :
      (∫ t in s, B t) ^ 2 ≤ T * MS := by
    have hcs := sq_setIntegral_le_measureReal_mul_setIntegral_sq
      (μ := volume) (s := s) (f := B)
      measure_Icc_lt_top.ne hBcont.measurable
      ((hBcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
    have hsmeasure : volume.real s = T := by
      dsimp only [s]
      simp [Measure.real, Real.volume_Icc, hT]
    have hsecondSet : (∫ t in s, B t ^ 2) ≤ MS := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hT]
      exact hsignedSecond
    calc
      (∫ t in s, B t) ^ 2 ≤ volume.real s * ∫ t in s, B t ^ 2 := hcs
      _ ≤ T * MS := by rw [hsmeasure]; gcongr
  have hBsqrt : (∫ t in s, B t) ≤ Real.sqrt (T * MS) := by
    rw [Real.le_sqrt hBnonneg (mul_nonneg hT hMS)]
    exact hBsq
  have hfirstSet : L ≤ ∫ t in s, A t := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hT]
    exact hfirst
  have hDsecond : (∫ t in e, (A t - B t) ^ 2) ≤ MA := by
    have hpoint : ∀ t, (A t - B t) ^ 2 ≤ A t ^ 2 := by
      intro t
      have hAnonneg : 0 ≤ A t := by
        dsimp only [A, slidingAbsoluteMass, slidingWindowMass]
        exact intervalIntegral.integral_nonneg
          (show t ≤ t + H by linarith) fun _ _ => abs_nonneg _
      have hBnonnegPoint : 0 ≤ B t := by
        dsimp only [B, slidingSignedAbsMass]
        exact abs_nonneg _
      have hDnonneg : 0 ≤ A t - B t := sub_nonneg.mpr (hBA t)
      have hDle : A t - B t ≤ A t := by linarith
      simpa only [pow_two] using mul_self_le_mul_self hDnonneg hDle
    calc
      (∫ t in e, (A t - B t) ^ 2) ≤ ∫ t in e, A t ^ 2 := by
        exact setIntegral_mono_on hDsqInt
          (habsSecondInt.integrableOn.mono_set hes) he
          (fun t _ => hpoint t)
      _ ≤ ∫ t : ℝ, A t ^ 2 := by
        exact setIntegral_le_integral habsSecondInt
          (Filter.Eventually.of_forall fun t => sq_nonneg (A t))
      _ ≤ MA := by simpa only [A] using habsSecond
  simpa only [s, e, A, B] using
    firstMomentGap_sq_le_measureReal_mul_secondMoment
      hs he hμe hes hAint hBint hDsqInt hzero hfirstSet hBsqrt hDsecond hgap

end MathlibAux
