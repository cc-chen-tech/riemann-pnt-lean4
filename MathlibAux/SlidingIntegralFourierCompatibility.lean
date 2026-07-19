import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MathlibAux.SlidingWindowParseval

/-!
# Fourier compatibility for genuine sliding integrals

This file connects the pointwise convolution by a discontinuous rectangular
kernel with Mathlib's abstract `L2` Fourier transform.  The endpoint
discontinuities are handled measurably; no continuity assumption is imposed on
the rectangular kernel.
-/

open Complex Convolution FourierTransform MeasureTheory Set
open scoped Convolution ENNReal FourierTransform Interval

namespace MathlibAux

/-- The backward rectangular kernel whose convolution with `F` is the forward
sliding integral.  The half-open convention makes the pointwise convolution
match the `Ioc` convention used by interval integrals. -/
noncomputable def backwardRectangularKernel (H x : ℝ) : ℂ :=
  (Ico (-H) 0).indicator (fun _ => (1 : ℂ)) x

theorem integrable_backwardRectangularKernel (H : ℝ) :
    Integrable (backwardRectangularKernel H) := by
  rw [← memLp_one_iff_integrable]
  change MemLp ((Ico (-H) 0).indicator fun _ => (1 : ℂ)) 1
  exact memLp_indicator_const 1 measurableSet_Ico 1
    (Or.inr (measure_Ico_lt_top : volume (Ico (-H) 0) < ∞).ne)

theorem memLp_two_backwardRectangularKernel (H : ℝ) :
    MemLp (backwardRectangularKernel H) 2 := by
  change MemLp ((Ico (-H) 0).indicator fun _ => (1 : ℂ)) 2
  exact memLp_indicator_const 2 measurableSet_Ico 1
    (Or.inr (measure_Ico_lt_top : volume (Ico (-H) 0) < ∞).ne)

/-- Fourier transform of the discontinuous backward rectangle. -/
theorem fourier_backwardRectangularKernel_eq {H : ℝ} (hH : 0 ≤ H) (y : ℝ) :
    𝓕 (backwardRectangularKernel H) y = rectangularFourierMultiplier H y := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * y) * I) •
      (Ico (-H) 0).indicator (fun _ => (1 : ℂ)) v) = _
  have hindicator :
      (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * y) * I) •
        (Ico (-H) 0).indicator (fun _ => (1 : ℂ)) v) =
        (Ico (-H) 0).indicator
          (fun v => Complex.exp (↑(-2 * Real.pi * v * y) * I)) := by
    funext v
    by_cases hv : v ∈ Ico (-H) 0 <;> simp [hv]
  rw [hindicator]
  rw [integral_indicator measurableSet_Ico]
  rw [integral_Ico_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (neg_nonpos.mpr hH)]
  rw [rectangularFourierMultiplier]
  calc
    (∫ x : ℝ in -H..0, Complex.exp (↑(-2 * Real.pi * x * y) * I)) =
        ∫ x : ℝ in 0..H,
          Complex.exp (↑(-2 * Real.pi * (-x) * y) * I) := by
      simpa using (intervalIntegral.integral_comp_neg
        (f := fun x : ℝ => Complex.exp (↑(-2 * Real.pi * x * y) * I))
        (a := 0) (b := H)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _hx
      push_cast
      congr 1
      ring

/-- The convolution with the backward rectangle is the genuine forward
sliding interval integral. -/
theorem convolution_backwardRectangularKernel_eq_slidingIntegral
    {F : ℝ → ℂ} {H : ℝ} (hH : 0 ≤ H) (t : ℝ) :
    (F ⋆[ContinuousLinearMap.mul ℂ ℂ] backwardRectangularKernel H) t =
      ∫ u in t..t + H, F u := by
  rw [convolution_mul]
  rw [intervalIntegral.integral_of_le (le_add_of_nonneg_right hH)]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with u
  simp only [backwardRectangularKernel, Set.indicator_apply]
  have hmem : t - u ∈ Ico (-H) 0 ↔ u ∈ Ioc t (t + H) := by
    constructor <;> intro h
    · constructor <;> linarith [h.1, h.2]
    · constructor <;> linarith [h.1, h.2]
  by_cases hu : u ∈ Ioc t (t + H)
  · rw [if_pos (hmem.mpr hu), if_pos hu]
    simp
  · rw [if_neg (not_congr hmem |>.mpr hu), if_neg hu]
    simp

/-! ## Fourier transform of an `L1` convolution without continuity -/

/-- The Fourier transform of the convolution of two integrable complex-valued
functions on `ℝ` is the product of their Fourier transforms.  Unlike
`Real.fourier_mul_convolution_eq`, this version only uses measurable
integrability and therefore applies to indicator kernels. -/
private theorem fourier_mul_convolution_eq_iteratedIntegral
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (y : ℝ) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) y =
      ∫ u, ∫ v, 𝐞 (-(v + u) * y) • (f u * g v) := by
  calc
    _ = ∫ x, 𝐞 (-(x * y)) • ∫ u, f u * g (x - u) := by
      rw [Real.fourier_real_eq]
      apply integral_congr_ae
      filter_upwards with x
      rw [convolution_mul]
    _ = ∫ x, ∫ u, 𝐞 (-(x * y)) • (f u * g (x - u)) := by
      congr
      ext x
      simp_rw [Circle.smul_def, integral_smul]
    _ = ∫ u, ∫ x, 𝐞 (-(x * y)) • (f u * g (x - u)) := by
      refine integral_integral_swap ?_
      have hbase : Integrable
          (fun p : ℝ × ℝ => f p.2 * g (p.1 - p.2))
          (volume.prod volume) :=
        hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg
      have htarget : Integrable
          (fun p : ℝ × ℝ => 𝐞 (-(p.1 * y)) •
            (f p.2 * g (p.1 - p.2))) (volume.prod volume) := by
        have hmeas : AEStronglyMeasurable
            (fun p : ℝ × ℝ => 𝐞 (-(p.1 * y)) •
              (f p.2 * g (p.1 - p.2))) (volume.prod volume) := by
          exact ((Real.continuous_fourierChar.comp
            (continuous_fst.mul continuous_const).neg).aestronglyMeasurable.smul
              hbase.aestronglyMeasurable)
        exact hbase.mono hmeas (by
          filter_upwards with p
          simp)
      exact htarget
    _ = ∫ u, ∫ v, 𝐞 (-(v + u) * y) • (f u * g v) := by
      congr
      ext u
      let q : ℝ → ℂ := fun v => 𝐞 (-(v + u) * y) • (f u * g v)
      calc
        (∫ x, 𝐞 (-(x * y)) • (f u * g (x - u))) =
            ∫ x, q (x - u) := by
          apply integral_congr_ae
          filter_upwards with x
          simp only [q]
          congr 2
          ring
        _ = ∫ v, q v := integral_sub_right_eq_self q u

/-- The Fourier transform of the convolution of two integrable complex-valued
functions on `ℝ` is the product of their Fourier transforms. -/
theorem fourier_mul_convolution_eq_of_integrable
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (y : ℝ) :
    𝓕 (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) y = 𝓕 f y * 𝓕 g y := by
  calc
    _ = ∫ u, ∫ v, 𝐞 (-(v + u) * y) • (f u * g v) :=
      fourier_mul_convolution_eq_iteratedIntegral hf hg y
    _ = ∫ u, ∫ v, (𝐞 (-(u * y)) * 𝐞 (-(v * y))) • (f u * g v) := by
      congr
      ext u
      congr
      ext v
      rw [← AddChar.map_add_eq_mul]
      congr
      ring
    _ = ∫ u, ∫ v, (𝐞 (-(u * y)) • f u) * (𝐞 (-(v * y)) • g v) := by
      congr
      ext u
      congr
      ext v
      simp only [Circle.smul_def, smul_eq_mul, Circle.coe_mul]
      ring_nf
    _ = ∫ u, (𝐞 (-(u * y)) • f u) * (∫ v, 𝐞 (-(v * y)) • g v) := by
      congr
      ext u
      simpa only [Circle.smul_def, smul_eq_mul, mul_assoc] using
        integral_const_mul (((𝐞 (-(u * y)) : Circle) : ℂ) * f u)
          (fun v => ((𝐞 (-(v * y)) : Circle) : ℂ) * g v)
    _ = (∫ u, 𝐞 (-(u * y)) • f u) * (∫ v, 𝐞 (-(v * y)) • g v) := by
      simpa only [Circle.smul_def, smul_eq_mul] using
        integral_mul_const (∫ v, ((𝐞 (-(v * y)) : Circle) : ℂ) * g v)
          (fun u => ((𝐞 (-(u * y)) : Circle) : ℂ) * f u)
    _ = 𝓕 f y * 𝓕 g y := by
      rw [Real.fourier_real_eq, Real.fourier_real_eq]

/-! ## Compatibility of the classical `L1` and abstract `L2` transforms -/

/-- For an integrable `L2` function, the abstract `L2` Fourier transform is
almost everywhere equal to the classical pointwise Fourier integral.  This is
the missing `L1 ∩ L2` compatibility statement in Mathlib's current API. -/
theorem coe_fourier_toLp_two_ae_eq_of_integrable
    {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    (fun y => (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y) =ᵐ[volume]
      𝓕 f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((MeasureTheory.Lp.memLp
      (𝓕 (hf2.toLp f) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))).locallyIntegrable
        (by norm_num))
    ((VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf).locallyIntegrable)
  intro g hgSmooth hgSupport
  have hgSupportC : HasCompactSupport (Complex.ofRealCLM ∘ g) :=
    hgSupport.comp_left rfl
  let phi : SchwartzMap ℝ ℂ :=
    hgSupportC.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgSmooth)
  have hdist := MeasureTheory.Lp.fourier_toTemperedDistribution_eq (hf2.toLp f)
  have happ := congrArg (fun D : TemperedDistribution ℝ ℂ => D phi) hdist
  have hfubini := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner hf phi.integrable
  have hphiFourier (x : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ).flip
        (phi : ℝ → ℂ) x = (𝓕 phi) x := by
    rw [flip_innerₗ]
    rfl
  have hfFourier (x : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
        f x = 𝓕 f x := by
    rfl
  have hphiValue (x : ℝ) : phi x = (g x : ℂ) := by
    rfl
  simp_rw [hphiFourier, hfFourier, hphiValue] at hfubini
  have hleft :
      (∫ x, g x • (𝓕 (hf2.toLp f) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) x) =
        ∫ x, (𝓕 phi) x * (hf2.toLp f) x := by
    simpa only [phi, TemperedDistribution.fourier_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply, Function.comp_apply,
      Complex.ofRealCLM_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
      mul_comm] using happ.symm
  calc
    _ = ∫ x, (𝓕 phi) x * (hf2.toLp f) x := hleft
    _ = ∫ x, (𝓕 phi) x * f x := by
      apply integral_congr_ae
      filter_upwards [hf2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, g x • 𝓕 f x := by
      simpa only [phi, Function.comp_apply, Complex.ofRealCLM_apply,
        RCLike.real_smul_eq_coe_mul, smul_eq_mul, flip_innerₗ,
        mul_comm] using hfubini.symm

/-- On `L1 ∩ L2`, whenever the classical Fourier transform is also in `L2`,
Mathlib's abstract `L2` Fourier transform is represented by the classical
pointwise transform. -/
theorem fourier_toLp_two_eq_of_integrable
    {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2)
    (hfourier2 : MemLp (𝓕 f) 2) :
    𝓕 (hf2.toLp f) = hfourier2.toLp (𝓕 f) := by
  apply MeasureTheory.Lp.ext
  exact (coe_fourier_toLp_two_ae_eq_of_integrable hf hf2).trans
    hfourier2.coeFn_toLp.symm

/-- Converse Plancherel compatibility: if an integrable function has a
classical Fourier transform in `L2`, then the abstract inverse transform of
that `L2` representative recovers the function almost everywhere. -/
theorem coe_fourierInv_toLp_two_ae_eq_of_integrable
    {f : ℝ → ℂ} (hf : Integrable f) (hfourier2 : MemLp (𝓕 f) 2) :
    (fun x => (𝓕⁻ (hfourier2.toLp (𝓕 f)) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) x) =ᵐ[volume] f := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((MeasureTheory.Lp.memLp
      (𝓕⁻ (hfourier2.toLp (𝓕 f)) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ))).locallyIntegrable (by norm_num))
    hf.locallyIntegrable
  intro g hgSmooth hgSupport
  have hgSupportC : HasCompactSupport (Complex.ofRealCLM ∘ g) :=
    hgSupport.comp_left rfl
  let phi : SchwartzMap ℝ ℂ :=
    hgSupportC.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hgSmooth)
  have hdist := MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq
    (hfourier2.toLp (𝓕 f))
  have happ := congrArg (fun D : TemperedDistribution ℝ ℂ => D phi) hdist
  have hfubini := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ) (μ := volume) (ν := volume)
    Real.continuous_fourierChar continuous_inner hf (𝓕⁻ phi).integrable
  have hFourierInv (x : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ).flip
        ((𝓕⁻ phi : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = phi x := by
    rw [flip_innerₗ]
    change (𝓕 (𝓕⁻ phi) : SchwartzMap ℝ ℂ) x = phi x
    rw [fourier_fourierInv_eq]
  simp_rw [hFourierInv] at hfubini
  have hleft :
      (∫ x, g x • (𝓕⁻ (hfourier2.toLp (𝓕 f)) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) x) =
        ∫ x, (𝓕⁻ phi) x * (hfourier2.toLp (𝓕 f)) x := by
    simpa only [phi, TemperedDistribution.fourierInv_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply, Function.comp_apply,
      Complex.ofRealCLM_apply, RCLike.real_smul_eq_coe_mul, smul_eq_mul,
      mul_comm] using happ.symm
  calc
    _ = ∫ x, (𝓕⁻ phi) x * (hfourier2.toLp (𝓕 f)) x := hleft
    _ = ∫ x, (𝓕⁻ phi) x * 𝓕 f x := by
      apply integral_congr_ae
      filter_upwards [hfourier2.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, g x • f x := by
      simpa only [phi, Function.comp_apply, Complex.ofRealCLM_apply,
        RCLike.real_smul_eq_coe_mul, smul_eq_mul, flip_innerₗ,
        SchwartzMap.fourierInv_coe, mul_comm] using hfubini

/-- The genuine sliding integral is integrable. -/
theorem integrable_slidingIntegral
    {F : ℝ → ℂ} (hF : Integrable F) {H : ℝ} (hH : 0 ≤ H) :
    Integrable (fun t => ∫ u in t..t + H, F u) := by
  have hconv := hF.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_backwardRectangularKernel H)
  exact hconv.congr (Filter.Eventually.of_forall fun t =>
    convolution_backwardRectangularKernel_eq_slidingIntegral hH t)

/-- The genuine sliding integral has the expected classical Fourier
transform, with no continuity assumption on the rectangular kernel. -/
theorem fourier_slidingIntegral_eq
    {F : ℝ → ℂ} (hF : Integrable F) {H : ℝ} (hH : 0 ≤ H) (y : ℝ) :
    𝓕 (fun t => ∫ u in t..t + H, F u) y =
      rectangularFourierMultiplier H y * 𝓕 F y := by
  have hfun : (fun t => ∫ u in t..t + H, F u) =
      F ⋆[ContinuousLinearMap.mul ℂ ℂ] backwardRectangularKernel H := by
    funext t
    exact (convolution_backwardRectangularKernel_eq_slidingIntegral hH t).symm
  rw [hfun]
  rw [fourier_mul_convolution_eq_of_integrable hF
    (integrable_backwardRectangularKernel H)]
  rw [fourier_backwardRectangularKernel_eq hH]
  exact mul_comm _ _

/-- Exact compatibility between the abstract inverse `L2` rectangular
multiplier and the genuine pointwise sliding integral. -/
theorem fourierInv_rectangularMultiplierLp_ae_eq_slidingIntegral
    {F : ℝ → ℂ} (hF1 : Integrable F) (hF2 : MemLp F 2)
    {H : ℝ} (hH : 0 ≤ H) :
    (fun t => (𝓕⁻ (rectangularMultiplierLp (hF2.toLp F) H hH) :
        Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) t) =ᵐ[volume]
      fun t => ∫ u in t..t + H, F u := by
  let S : ℝ → ℂ := fun t => ∫ u in t..t + H, F u
  have hS1 : Integrable S := integrable_slidingIntegral hF1 hH
  have hFcompat := coe_fourier_toLp_two_ae_eq_of_integrable hF1 hF2
  let hmult := memLp_rectangularFourierMultiplier_mul_fourier
    (hF2.toLp F) H hH
  have hfreqAe : (𝓕 S) =ᵐ[volume]
      fun y => rectangularFourierMultiplier H y *
        (𝓕 (hF2.toLp F) : Lp (α := ℝ) ℂ 2 (volume : Measure ℝ)) y := by
    filter_upwards [hFcompat] with y hy
    rw [fourier_slidingIntegral_eq hF1 hH]
    rw [hy]
  have hSFourier2 : MemLp (𝓕 S) 2 := hmult.ae_eq hfreqAe.symm
  have hrecover := coe_fourierInv_toLp_two_ae_eq_of_integrable hS1 hSFourier2
  have hfreq : hSFourier2.toLp (𝓕 S) =
      rectangularMultiplierLp (hF2.toLp F) H hH := by
    exact hSFourier2.toLp_congr hmult hfreqAe
  rw [hfreq] at hrecover
  exact hrecover

end MathlibAux
