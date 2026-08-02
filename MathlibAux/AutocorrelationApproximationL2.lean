import MathlibAux.AutocorrelationApproximation
import MathlibAux.PaleyZygmund

/-!
# L2 transfer for shifted autocorrelations

A uniform approximation error need not be multiplied by a pointwise bound for
the model.  Cauchy--Schwarz instead converts each remaining factor to its
square mass on the common control interval.
-/

open MeasureTheory Set

namespace MathlibAux

/-- Cauchy--Schwarz on an ordered interval, with only local continuity. -/
theorem
    abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq_of_continuousOn
    {F : ℝ → ℝ} {A B : ℝ}
    (hF : ContinuousOn F (Icc A B)) (hAB : A ≤ B) :
    |∫ x in A..B, F x| ≤
      Real.sqrt (B - A) * Real.sqrt (∫ x in A..B, F x ^ 2) := by
  have hfinite : volume (Ioc A B) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hsq : IntegrableOn (fun x => F x ^ 2) (Ioc A B) volume :=
    (hF.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmeas : AEStronglyMeasurable F (volume.restrict (Ioc A B)) :=
    (hF.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hcs :=
    sq_setIntegral_le_measureReal_mul_setIntegral_sq_of_aestronglyMeasurable
      (s := Ioc A B) hfinite hmeas hsq
  rw [← intervalIntegral.integral_of_le hAB] at hcs
  rw [← intervalIntegral.integral_of_le hAB] at hcs
  have hlen : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hmass : 0 ≤ ∫ x in A..B, F x ^ 2 :=
    intervalIntegral.integral_nonneg hAB fun x _ => sq_nonneg (F x)
  have hrightSq :
      (Real.sqrt (B - A) *
          Real.sqrt (∫ x in A..B, F x ^ 2)) ^ 2 =
        (B - A) * ∫ x in A..B, F x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hlen, Real.sq_sqrt hmass]
  have hmeasure : volume.real (Ioc A B) = B - A := by
    simp [measureReal_def, Real.volume_Ioc, hlen]
  rw [hmeasure] at hcs
  have hleft : 0 ≤ |∫ x in A..B, F x| := abs_nonneg _
  have hright : 0 ≤
      Real.sqrt (B - A) * Real.sqrt (∫ x in A..B, F x ^ 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (sq_le_sq₀ hleft hright).mp
  rw [sq_abs, hrightSq]
  exact hcs

/-- Global continuity specialization of interval Cauchy--Schwarz. -/
theorem abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq
    {F : ℝ → ℝ} (hF : Continuous F) {A B : ℝ} (hAB : A ≤ B) :
    |∫ x in A..B, F x| ≤
      Real.sqrt (B - A) * Real.sqrt (∫ x in A..B, F x ^ 2) :=
  abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq_of_continuousOn
    hF.continuousOn hAB

/-- A uniform approximation on the common control interval transfers a
shifted autocorrelation using square masses rather than pointwise bounds. -/
theorem abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn_L2
    {F P : ℝ → ℝ} {A B tau eps MF MP : ℝ}
    (hF : ContinuousOn F
      (Icc (min A (A + tau)) (max B (B + tau))))
    (hP : ContinuousOn P
      (Icc (min A (A + tau)) (max B (B + tau))))
    (hAB : A ≤ B) (heps : 0 ≤ eps)
    (happrox : ∀ x ∈ Icc (min A (A + tau)) (max B (B + tau)),
      |F x - P x| ≤ eps)
    (hFsq :
      (∫ x in min A (A + tau)..max B (B + tau), F x ^ 2) ≤ MF)
    (hPsq :
      (∫ x in min A (A + tau)..max B (B + tau), P x ^ 2) ≤ MP) :
    |(∫ x in A..B, F x * F (x + tau)) -
        ∫ x in A..B, P x * P (x + tau)| ≤
      eps * Real.sqrt (B - A) *
        (Real.sqrt MF + Real.sqrt MP) := by
  let lo : ℝ := min A (A + tau)
  let hi : ℝ := max B (B + tau)
  have hloA : lo ≤ A := by
    dsimp only [lo]
    exact min_le_left _ _
  have hBhi : B ≤ hi := by
    dsimp only [hi]
    exact le_max_left _ _
  have hloAtau : lo ≤ A + tau := by
    dsimp only [lo]
    exact min_le_right _ _
  have hBtauhi : B + tau ≤ hi := by
    dsimp only [hi]
    exact le_max_right _ _
  have hlohi : lo ≤ hi := hloA.trans (hAB.trans hBhi)
  have hFcontrolInt : IntervalIntegrable (fun x => F x ^ 2) volume lo hi := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlohi]
    simpa only [lo, hi] using hF.pow 2
  have hPcontrolInt : IntervalIntegrable (fun x => P x ^ 2) volume lo hi := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hlohi]
    simpa only [lo, hi] using hP.pow 2
  have hFshiftSq :
      (∫ x in A..B, F (x + tau) ^ 2) ≤ MF := by
    calc
      (∫ x in A..B, F (x + tau) ^ 2) =
          ∫ x in A + tau..B + tau, F x ^ 2 := by
            simpa using intervalIntegral.integral_comp_add_right
              (fun x => F x ^ 2) tau
      _ ≤ ∫ x in lo..hi, F x ^ 2 :=
        intervalIntegral.integral_mono_interval hloAtau
          (by linarith) hBtauhi
          (Filter.Eventually.of_forall fun x => sq_nonneg (F x))
          hFcontrolInt
      _ ≤ MF := by simpa only [lo, hi] using hFsq
  have hPbaseSq :
      (∫ x in A..B, P x ^ 2) ≤ MP := by
    calc
      (∫ x in A..B, P x ^ 2) ≤ ∫ x in lo..hi, P x ^ 2 :=
        intervalIntegral.integral_mono_interval hloA hAB hBhi
          (Filter.Eventually.of_forall fun x => sq_nonneg (P x))
          hPcontrolInt
      _ ≤ MP := by simpa only [lo, hi] using hPsq
  have hbaseMaps :
      MapsTo (fun x : ℝ => x)
        (Icc A B) (Icc lo hi) := by
    intro x hx
    exact ⟨hloA.trans hx.1, hx.2.trans hBhi⟩
  have hshiftMaps :
      MapsTo (fun x : ℝ => x + tau)
        (Icc A B) (Icc lo hi) := by
    intro x hx
    constructor
    · exact hloAtau.trans (by
        simpa [add_comm] using add_le_add_right hx.1 tau)
    · have hx' : x + tau ≤ B + tau := by linarith [hx.2]
      exact hx'.trans hBtauhi
  have hFshiftCont : ContinuousOn (fun x => F (x + tau)) (Icc A B) := by
    simpa only [Function.comp_def] using
      hF.comp (continuous_id.add continuous_const).continuousOn hshiftMaps
  have hPbaseCont : ContinuousOn P (Icc A B) :=
    hP.mono hbaseMaps
  have hFabsL1 :
      (∫ x in A..B, |F (x + tau)|) ≤
        Real.sqrt (B - A) * Real.sqrt MF := by
    have hcs :=
      abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq_of_continuousOn
        hFshiftCont.abs hAB
    have hmass :
        (∫ x in A..B, |F (x + tau)| ^ 2) ≤ MF := by
      simpa only [sq_abs] using hFshiftSq
    calc
      (∫ x in A..B, |F (x + tau)|) ≤
          abs (∫ x in A..B, |F (x + tau)|) := le_abs_self _
      _ ≤ Real.sqrt (B - A) *
          Real.sqrt (∫ x in A..B, |F (x + tau)| ^ 2) := hcs
      _ ≤ Real.sqrt (B - A) * Real.sqrt MF :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass)
          (Real.sqrt_nonneg _)
  have hPabsL1 :
      (∫ x in A..B, |P x|) ≤
        Real.sqrt (B - A) * Real.sqrt MP := by
    have hcs :=
      abs_intervalIntegral_le_sqrt_length_mul_sqrt_intervalIntegral_sq_of_continuousOn
        hPbaseCont.abs hAB
    have hmass :
        (∫ x in A..B, |P x| ^ 2) ≤ MP := by
      simpa only [sq_abs] using hPbaseSq
    calc
      (∫ x in A..B, |P x|) ≤
          abs (∫ x in A..B, |P x|) := le_abs_self _
      _ ≤ Real.sqrt (B - A) *
          Real.sqrt (∫ x in A..B, |P x| ^ 2) := hcs
      _ ≤ Real.sqrt (B - A) * Real.sqrt MP :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass)
          (Real.sqrt_nonneg _)
  let f : ℝ → ℝ := fun x => F x * F (x + tau)
  let p : ℝ → ℝ := fun x => P x * P (x + tau)
  have hFbaseCont : ContinuousOn F (Icc A B) :=
    hF.mono hbaseMaps
  have hPshiftCont : ContinuousOn (fun x => P (x + tau)) (Icc A B) := by
    simpa only [Function.comp_def] using
      hP.comp (continuous_id.add continuous_const).continuousOn hshiftMaps
  have hintervalInt :
      ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc A B) →
        IntervalIntegrable g volume A B := by
    intro g hg
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hAB]
    exact hg
  have hfInt : IntervalIntegrable f volume A B :=
    hintervalInt (hFbaseCont.mul hFshiftCont)
  have hpInt : IntervalIntegrable p volume A B :=
    hintervalInt (hPbaseCont.mul hPshiftCont)
  have habsInt : IntervalIntegrable (fun x => |f x - p x|) volume A B :=
    hintervalInt
      ((hFbaseCont.mul hFshiftCont).sub
        (hPbaseCont.mul hPshiftCont)).abs
  have hmajorInt : IntervalIntegrable
      (fun x => eps * (|F (x + tau)| + |P x|)) volume A B :=
    hintervalInt
      (continuousOn_const.mul (hFshiftCont.abs.add hPbaseCont.abs))
  have hpoint : ∀ x ∈ Icc A B,
      |f x - p x| ≤ eps * (|F (x + tau)| + |P x|) := by
    intro x hx
    have hxControl := hbaseMaps hx
    have hxShiftControl := hshiftMaps hx
    calc
      |f x - p x| =
          |(F x - P x) * F (x + tau) +
            P x * (F (x + tau) - P (x + tau))| := by
              dsimp only [f, p]
              congr 1
              ring
      _ ≤ |F x - P x| * |F (x + tau)| +
          |P x| * |F (x + tau) - P (x + tau)| := by
            calc
              _ ≤ |(F x - P x) * F (x + tau)| +
                  |P x * (F (x + tau) - P (x + tau))| :=
                abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ eps * |F (x + tau)| + |P x| * eps :=
        add_le_add
          (mul_le_mul_of_nonneg_right (happrox x hxControl) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left
            (happrox (x + tau) hxShiftControl) (abs_nonneg _))
      _ = eps * (|F (x + tau)| + |P x|) := by ring
  have hdiff :
      |(∫ x in A..B, f x) - ∫ x in A..B, p x| ≤
        ∫ x in A..B, eps * (|F (x + tau)| + |P x|) := by
    calc
      |(∫ x in A..B, f x) - ∫ x in A..B, p x| =
          |∫ x in A..B, f x - p x| := by
            rw [intervalIntegral.integral_sub hfInt hpInt]
      _ ≤ ∫ x in A..B, |f x - p x| :=
        intervalIntegral.abs_integral_le_integral_abs hAB
      _ ≤ ∫ x in A..B, eps * (|F (x + tau)| + |P x|) :=
        intervalIntegral.integral_mono_on hAB habsInt hmajorInt hpoint
  calc
    |(∫ x in A..B, F x * F (x + tau)) -
        ∫ x in A..B, P x * P (x + tau)| =
        |(∫ x in A..B, f x) - ∫ x in A..B, p x| := rfl
    _ ≤ ∫ x in A..B, eps * (|F (x + tau)| + |P x|) := hdiff
    _ = eps * ((∫ x in A..B, |F (x + tau)|) +
        ∫ x in A..B, |P x|) := by
      calc
        (∫ x in A..B, eps * (|F (x + tau)| + |P x|)) =
            (∫ x in A..B, eps * |F (x + tau)|) +
              ∫ x in A..B, eps * |P x| := by
                simpa only [mul_add] using
                  intervalIntegral.integral_add
                    (hintervalInt
                      (continuousOn_const.mul hFshiftCont.abs))
                    (hintervalInt
                      (continuousOn_const.mul hPbaseCont.abs))
        _ = eps * ((∫ x in A..B, |F (x + tau)|) +
            ∫ x in A..B, |P x|) := by
              simp only [intervalIntegral.integral_const_mul]
              ring
    _ ≤ eps * (Real.sqrt (B - A) * Real.sqrt MF +
        Real.sqrt (B - A) * Real.sqrt MP) :=
      mul_le_mul_of_nonneg_left (add_le_add hFabsL1 hPabsL1) heps
    _ = eps * Real.sqrt (B - A) *
        (Real.sqrt MF + Real.sqrt MP) := by ring

end MathlibAux
