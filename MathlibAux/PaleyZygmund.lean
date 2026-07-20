import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped ENNReal NNReal InnerProductSpace

namespace MathlibAux

/-!
# Paley--Zygmund measure bounds

This file records a setwise Cauchy--Schwarz inequality and the resulting
Paley--Zygmund lower bound for a nonnegative real function on a finite-measure
set.  The formulation uses `Measure.real`, matching the real-valued integral
estimates used by the analytic-number-theory development.
-/

/-- Setwise Cauchy--Schwarz with the constant function `1`. -/
theorem sq_setIntegral_le_measureReal_mul_setIntegral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ}
    (hμs : μ s ≠ ⊤)
    (hf : Measurable f) (hf_sq : IntegrableOn (fun x => f x ^ 2) s μ) :
    (∫ x in s, f x ∂μ) ^ 2 ≤ μ.real s * ∫ x in s, f x ^ 2 ∂μ := by
  haveI : IsFiniteMeasure (μ.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμs.lt_top⟩
  have hf_asm : AEStronglyMeasurable f (μ.restrict s) :=
    hf.aestronglyMeasurable
  have hf_memLp : MemLp f 2 (μ.restrict s) :=
    (memLp_two_iff_integrable_sq hf_asm).2 hf_sq
  have hone_memLp : MemLp (fun _ : α => (1 : ℝ)) 2 (μ.restrict s) :=
    memLp_const 1
  let F : Lp ℝ 2 (μ.restrict s) := hf_memLp.toLp f
  let one : Lp ℝ 2 (μ.restrict s) :=
    hone_memLp.toLp (fun _ => (1 : ℝ))
  have hcs := real_inner_mul_inner_self_le one F
  have honeF : ⟪one, F⟫_ℝ = ∫ x in s, f x ∂μ := by
    rw [L2.inner_def]
    change (∫ x, F x * one x ∂(μ.restrict s)) = _
    rw [show (∫ x, F x * one x ∂(μ.restrict s)) =
        ∫ x, f x * (1 : ℝ) ∂(μ.restrict s) by
      apply integral_congr_ae
      filter_upwards [hone_memLp.coeFn_toLp, hf_memLp.coeFn_toLp] with x h1 hf'
      change one x = 1 at h1
      change F x = f x at hf'
      rw [h1, hf']]
    simp
  have honeone : ⟪one, one⟫_ℝ = μ.real s := by
    rw [L2.inner_def]
    change (∫ x, one x * one x ∂(μ.restrict s)) = _
    rw [show (∫ x, one x * one x ∂(μ.restrict s)) =
        ∫ _x, (1 : ℝ) ∂(μ.restrict s) by
      apply integral_congr_ae
      filter_upwards [hone_memLp.coeFn_toLp] with x h1
      change one x = 1 at h1
      rw [h1]
      norm_num]
    simp [measureReal_def]
  have hFF : ⟪F, F⟫_ℝ = ∫ x in s, f x ^ 2 ∂μ := by
    rw [L2.inner_def]
    change (∫ x, F x * F x ∂(μ.restrict s)) = _
    rw [show (∫ x, F x * F x ∂(μ.restrict s)) =
        ∫ x, f x ^ 2 ∂(μ.restrict s) by
      apply integral_congr_ae
      filter_upwards [hf_memLp.coeFn_toLp] with x hf'
      change F x = f x at hf'
      rw [hf']
      simp [pow_two]]
  rw [honeF, honeone, hFF] at hcs
  simpa [pow_two] using hcs

/-- Paley--Zygmund in product form.  This avoids dividing by the second
moment, so it remains meaningful even when that moment vanishes. -/
theorem paleyZygmund_mul_secondMoment_le_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ} {θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (hμs_pos : 0 < μ.real s)
    (hf : Measurable f) (hf_nonneg : ∀ x ∈ s, 0 ≤ f x)
    (hf_sq : IntegrableOn (fun x => f x ^ 2) s μ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ x in s, f x ∂μ) ^ 2 ≤
      μ.real {x ∈ s | θ * ((∫ y in s, f y ∂μ) / μ.real s) < f x} *
        ∫ x in s, f x ^ 2 ∂μ := by
  let I : ℝ := ∫ x in s, f x ∂μ
  let m : ℝ := μ.real s
  let a : ℝ := θ * (I / m)
  let good : Set α := {x ∈ s | a < f x}
  have hgood : MeasurableSet good := hs.inter (hf measurableSet_Ioi)
  have hgood_subset : good ⊆ s := fun _ hx => hx.1
  have hμgood : μ good ≠ ⊤ := measure_ne_top_of_subset hgood_subset hμs
  haveI : IsFiniteMeasure (μ.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hμs.lt_top⟩
  have hf_asm : AEStronglyMeasurable f (μ.restrict s) :=
    hf.aestronglyMeasurable
  have hf_memLp : MemLp f 2 (μ.restrict s) :=
    (memLp_two_iff_integrable_sq hf_asm).2 hf_sq
  have hf_int : IntegrableOn f s μ := hf_memLp.integrable (by norm_num)
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    exact setIntegral_nonneg hs hf_nonneg
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg hθ0 (div_nonneg hI_nonneg hμs_pos.le)
  have hbad_integral_le :
      (∫ x in s \ good, f x ∂μ) ≤ a * m := by
    have hbad : MeasurableSet (s \ good) := hs.diff hgood
    have hbad_f : IntegrableOn f (s \ good) μ := hf_int.mono_set diff_subset
    have hbad_const : IntegrableOn (fun _ : α => a) (s \ good) μ :=
      integrableOn_const (measure_ne_top_of_subset diff_subset hμs)
    have hpointwise : ∀ x ∈ s \ good, f x ≤ a := by
      intro x hx
      exact le_of_not_gt (fun hax => hx.2 ⟨hx.1, hax⟩)
    calc
      (∫ x in s \ good, f x ∂μ) ≤ ∫ _x in s \ good, a ∂μ :=
        setIntegral_mono_on hbad_f hbad_const hbad hpointwise
      _ = μ.real (s \ good) * a := by simp
      _ ≤ m * a :=
        mul_le_mul_of_nonneg_right (measureReal_mono diff_subset hμs) ha_nonneg
      _ = a * m := mul_comm _ _
  have ham : a * m = θ * I := by
    dsimp [a]
    calc
      θ * (I / m) * m = θ * ((I / m) * m) := by ring
      _ = θ * I := by rw [div_mul_cancel₀ I hμs_pos.ne']
  have hgood_integral_lower :
      (1 - θ) * I ≤ ∫ x in good, f x ∂μ := by
    have hdiff := setIntegral_diff hgood hf_int hgood_subset
    rw [hdiff] at hbad_integral_le
    rw [ham] at hbad_integral_le
    linarith
  have hlower_nonneg : 0 ≤ (1 - θ) * I :=
    mul_nonneg (by linarith) hI_nonneg
  have hcs :
      (∫ x in good, f x ∂μ) ^ 2 ≤
        μ.real good * ∫ x in good, f x ^ 2 ∂μ :=
    sq_setIntegral_le_measureReal_mul_setIntegral_sq hμgood hf
      (hf_sq.mono_set hgood_subset)
  have hsecond_mono :
      (∫ x in good, f x ^ 2 ∂μ) ≤ ∫ x in s, f x ^ 2 ∂μ :=
    setIntegral_mono_set hf_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))
      (Filter.Eventually.of_forall hgood_subset)
  calc
    (1 - θ) ^ 2 * (∫ x in s, f x ∂μ) ^ 2 = ((1 - θ) * I) ^ 2 := by
      dsimp [I]
      ring
    _ ≤ (∫ x in good, f x ∂μ) ^ 2 :=
      by simpa [pow_two] using
        mul_self_le_mul_self hlower_nonneg hgood_integral_lower
    _ ≤ μ.real good * ∫ x in good, f x ^ 2 ∂μ := hcs
    _ ≤ μ.real good * ∫ x in s, f x ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left hsecond_mono measureReal_nonneg
    _ = μ.real {x ∈ s | θ * ((∫ y in s, f y ∂μ) / μ.real s) < f x} *
        ∫ x in s, f x ^ 2 ∂μ := by
      rfl

/-- The usual Paley--Zygmund lower bound for the measure of the set where
`f` exceeds `θ` times its mean over `s`. -/
theorem paleyZygmund_measure_lower_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f : α → ℝ} {θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (hμs_pos : 0 < μ.real s)
    (hf : Measurable f) (hf_nonneg : ∀ x ∈ s, 0 ≤ f x)
    (hf_sq : IntegrableOn (fun x => f x ^ 2) s μ)
    (hsecond : 0 < ∫ x in s, f x ^ 2 ∂μ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ x in s, f x ∂μ) ^ 2 /
        (∫ x in s, f x ^ 2 ∂μ) ≤
      μ.real {x ∈ s | θ * ((∫ y in s, f y ∂μ) / μ.real s) < f x} := by
  exact (div_le_iff₀ hsecond).2
    (paleyZygmund_mul_secondMoment_le_measure hs hμs hμs_pos hf hf_nonneg hf_sq hθ0 hθ1)

/-- Second/fourth-moment form of Paley--Zygmund.  This is the form used when
the nonnegative mass is a square, for example the squared norm of a mollified
Dirichlet polynomial. -/
theorem paleyZygmund_sq_measure_lower_bound
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {g : α → ℝ} {θ : ℝ}
    (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) (hμs_pos : 0 < μ.real s)
    (hg : Measurable g) (hg_fourth : IntegrableOn (fun x => g x ^ 4) s μ)
    (hfourth : 0 < ∫ x in s, g x ^ 4 ∂μ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (∫ x in s, g x ^ 2 ∂μ) ^ 2 /
        (∫ x in s, g x ^ 4 ∂μ) ≤
      μ.real {x ∈ s | θ * ((∫ y in s, g y ^ 2 ∂μ) / μ.real s) < g x ^ 2} := by
  have hsq_meas : Measurable (fun x => g x ^ 2) := hg.pow_const 2
  have hsq_sq : IntegrableOn (fun x => (g x ^ 2) ^ 2) s μ := by
    simpa [← pow_mul] using hg_fourth
  have hsq_sq_pos : 0 < ∫ x in s, (g x ^ 2) ^ 2 ∂μ := by
    simpa [← pow_mul] using hfourth
  simpa [← pow_mul] using
    (paleyZygmund_measure_lower_bound hs hμs hμs_pos hsq_meas
      (fun x _ => sq_nonneg (g x)) hsq_sq hsq_sq_pos hθ0 hθ1)

end MathlibAux
