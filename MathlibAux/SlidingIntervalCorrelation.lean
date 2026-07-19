import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

open Complex MeasureTheory Set
open scoped Interval ComplexConjugate

namespace MathlibAux

/-- Fubini expansion for the product of two parameter-dependent integrals.
The single product-space integrability hypothesis is exactly what is needed
to exchange the outer variable with both inner variables. -/
theorem integral_conj_mul_integral_eq_triple
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (ξ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ξ]
    (F : α → β → ℂ) (G : α → γ → ℂ)
    (h : Integrable
      (fun p : α × (β × γ) => conj (F p.1 p.2.1) * G p.1 p.2.2)
      (μ.prod (ν.prod ξ))) :
    (∫ t, conj (∫ v, F t v ∂ν) * (∫ w, G t w ∂ξ) ∂μ) =
      ∫ v, ∫ w, ∫ t, conj (F t v) * G t w ∂μ ∂ξ ∂ν := by
  let H : α → β × γ → ℂ := fun t p => conj (F t p.1) * G t p.2
  have hH : Integrable (Function.uncurry H) (μ.prod (ν.prod ξ)) := by
    simpa [H] using h
  calc
    _ = ∫ t, ∫ p, H t p ∂ν.prod ξ ∂μ := by
      apply integral_congr_ae
      filter_upwards with t
      calc
        _ = (∫ v, conj (F t v) ∂ν) * (∫ w, G t w ∂ξ) := by
          congr 1
          exact (integral_conj (f := fun v => F t v) (μ := ν)).symm
        _ = ∫ p, conj (F t p.1) * G t p.2 ∂ν.prod ξ :=
          (integral_prod_mul (fun v => conj (F t v))
            (fun w => G t w)).symm
        _ = ∫ p, H t p ∂ν.prod ξ := rfl
    _ = ∫ p, ∫ t, H t p ∂μ ∂ν.prod ξ := integral_integral_swap hH
    _ = _ := by
      simpa [H] using
        (integral_prod (fun p : β × γ => ∫ t, H t p ∂μ)
          hH.integral_prod_right)

/-- On finite intervals, the square/correlation of two sliding integrals can
be expanded with the window variables outside.  Continuity is sufficient;
no global `L²` hypothesis is needed. -/
theorem slidingIntervalCorrelation_fubini
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {a b delta : ℝ} (hab : a ≤ b) (hdelta : 0 ≤ delta) :
    (∫ t in a..b,
      conj (∫ v in 0..delta, f (t + v)) *
        (∫ w in 0..delta, g (t + w))) =
      ∫ v in 0..delta, ∫ w in 0..delta, ∫ t in a..b,
        conj (f (t + v)) * g (t + w) := by
  let H : ℝ × (ℝ × ℝ) → ℂ :=
    fun p => conj (f (p.1 + p.2.1)) * g (p.1 + p.2.2)
  have hHcc : IntegrableOn H
      (Icc a b ×ˢ (Icc 0 delta ×ˢ Icc 0 delta))
      (volume.prod (volume.prod volume)) := by
    apply ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    dsimp [H]
    fun_prop
  have hH : Integrable H
      ((volume.restrict (Ioc a b)).prod
        ((volume.restrict (Ioc 0 delta)).prod
          (volume.restrict (Ioc 0 delta)))) := by
    simpa only [Measure.prod_restrict, IntegrableOn] using
      hHcc.mono_set
        (Set.prod_mono Ioc_subset_Icc_self
          (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self))
  simpa only [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hdelta] using
    integral_conj_mul_integral_eq_triple
      (volume.restrict (Ioc a b))
      (volume.restrict (Ioc 0 delta))
      (volume.restrict (Ioc 0 delta))
      (fun t v => f (t + v)) (fun t w => g (t + w)) hH

/-- Equivalent finite-window correlation kernel after translating the outer
integration variable by the first short-window displacement. -/
theorem slidingIntervalCorrelation_kernel
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    {a b delta : ℝ} (hab : a ≤ b) (hdelta : 0 ≤ delta) :
    (∫ t in a..b,
      conj (∫ v in 0..delta, f (t + v)) *
        (∫ w in 0..delta, g (t + w))) =
      ∫ v in 0..delta, ∫ w in 0..delta,
        ∫ x in a + v..b + v, conj (f x) * g (x + (w - v)) := by
  rw [slidingIntervalCorrelation_fubini hf hg hab hdelta]
  apply intervalIntegral.integral_congr
  intro v hv
  apply intervalIntegral.integral_congr
  intro w hw
  calc
    _ = ∫ t in a..b,
        (fun x => conj (f x) * g (x + (w - v))) (t + v) := by
      apply intervalIntegral.integral_congr
      intro t ht
      ring_nf
    _ = _ := by
      simpa using
        (intervalIntegral.integral_comp_add_right
          (fun x => conj (f x) * g (x + (w - v))) v :
          (∫ t in a..b,
            (fun x => conj (f x) * g (x + (w - v))) (t + v)) = _)

end MathlibAux
