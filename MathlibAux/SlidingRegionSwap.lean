import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Region swap for translated-correlation double integrals

The sliding-window correlation double integral over the square `[0, H]^2`,
after the substitution `τ = w - v`, covers the diagonal region
`{0 < v ≤ H, -v < τ ≤ H - v}`.  Swapping the order of integration expresses
it as a lag integral over `τ ∈ (-H, H]` with the `v`-section
`max 0 (-τ) < v ≤ min H (H - τ)`, whose length is exactly the triangle weight
`H - |τ|`.  The proof is Tonelli on the indicator of the region; both orders
compute the same product-measure integral.
-/

open MeasureTheory Set

namespace MathlibAux

/-- The translated-correlation double integral over the square window swaps
to the lag form: the inner integral runs over the explicit `v`-section of the
diagonal region. -/
theorem intervalIntegral_pair_sub_swap
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (Function.uncurry Φ)) {H : ℝ} (hH : 0 ≤ H) :
    (∫ v in (0 : ℝ)..H, ∫ τ in (-v)..H - v, Φ v τ) =
      ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), Φ v τ := by
  classical
  set R : Set (ℝ × ℝ) := {p : ℝ × ℝ | (0 : ℝ) < p.1} ∩ {p | p.1 ≤ H} ∩
    {p | -p.1 < p.2} ∩ {p | p.2 ≤ H - p.1} with hRdef
  have hRmem : ∀ v τ : ℝ,
      ((v, τ) ∈ R ↔ 0 < v ∧ v ≤ H ∧ -v < τ ∧ τ ≤ H - v) := by
    intro v τ
    simp only [hRdef, Set.mem_inter_iff, Set.mem_setOf_eq]
    tauto
  have hRmem' : ∀ v τ : ℝ,
      ((v, τ) ∈ R ↔ v ∈ Ioc 0 H ∧ τ ∈ Ioc (-v) (H - v)) := by
    intro v τ
    rw [hRmem, Set.mem_Ioc, Set.mem_Ioc]
    tauto
  have hRτ : ∀ {v τ : ℝ}, (v, τ) ∈ R → τ ∈ Ioc (-H) H := by
    intro v τ hmem
    obtain ⟨hv0, hvH, hτl, hτu⟩ := (hRmem v τ).mp hmem
    rw [Set.mem_Ioc]
    constructor <;> linarith
  have hRmem2 : ∀ {v τ : ℝ}, τ ∈ Ioc (-H) H →
      ((v, τ) ∈ R ↔ v ∈ Ioc (max 0 (-τ)) (min H (H - τ))) := by
    intro v τ hτrange
    obtain ⟨hτ1, hτ2⟩ := Set.mem_Ioc.mp hτrange
    rw [hRmem, Set.mem_Ioc]
    constructor
    · rintro ⟨hv0, hvH, hτl, hτu⟩
      exact ⟨max_lt_iff.mpr ⟨hv0, by linarith⟩,
        le_min_iff.mpr ⟨hvH, by linarith⟩⟩
    · rintro ⟨hmax, hmin⟩
      obtain ⟨h1, h2⟩ := max_lt_iff.mp hmax
      obtain ⟨h3, h4⟩ := le_min_iff.mp hmin
      exact ⟨h1, h3, by linarith, by linarith⟩
  have hRmeas : MeasurableSet R := by
    rw [hRdef]
    exact (((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)).inter
      (measurableSet_lt measurable_fst.neg measurable_snd)).inter
      (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))
  have hRsub : R ⊆ Icc 0 H ×ˢ Icc (-H) H := by
    intro p hp
    obtain ⟨hp1, hp2, hp3, hp4⟩ := (hRmem p.1 p.2).mp hp
    simp only [Set.mem_prod, Set.mem_Icc]
    exact ⟨⟨hp1.le, hp2⟩, ⟨by linarith, by linarith⟩⟩
  have hΦint : IntegrableOn (Function.uncurry Φ) R (volume.prod volume) :=
    (hΦ.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set hRsub
  have hh : Integrable (R.indicator (Function.uncurry Φ)) (volume.prod volume) :=
    hΦint.integrable_indicator hRmeas
  have hh_eq : ∀ v τ : ℝ, (v, τ) ∈ R →
      R.indicator (Function.uncurry Φ) (v, τ) = Φ v τ := by
    intro v τ hmem
    rw [Set.indicator_of_mem hmem _]
    rfl
  have hh_zero : ∀ v τ : ℝ, (v, τ) ∉ R →
      R.indicator (Function.uncurry Φ) (v, τ) = 0 := by
    intro v τ hmem
    exact Set.indicator_of_notMem hmem _
  have hLHS :
      (∫ v in (0 : ℝ)..H, ∫ τ in (-v)..H - v, Φ v τ) =
        ∫ z, R.indicator (Function.uncurry Φ) z ∂(volume.prod volume) := by
    rw [intervalIntegral.integral_of_le hH]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [MeasureTheory.integral_prod _ hh]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ Ioc (0 : ℝ) H
    · rw [Set.indicator_of_mem hv _]
      rw [intervalIntegral.integral_of_le (by linarith : -v ≤ H - v)]
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with τ
      by_cases hτ : τ ∈ Ioc (-v) (H - v)
      · rw [Set.indicator_of_mem hτ,
          hh_eq v τ ((hRmem' v τ).mpr ⟨hv, hτ⟩)]
      · rw [Set.indicator_of_notMem hτ,
          hh_zero v τ (fun hmem => hτ ((hRmem' v τ).mp hmem).2)]
    · rw [Set.indicator_of_notMem hv _]
      have hzero : ∀ τ : ℝ, R.indicator (Function.uncurry Φ) (v, τ) = 0 :=
        fun τ => hh_zero v τ (fun hmem => hv ((hRmem' v τ).mp hmem).1)
      simp [hzero]
  have hRHS :
      (∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), Φ v τ) =
        ∫ z, R.indicator (Function.uncurry Φ) z ∂(volume.prod volume) := by
    rw [intervalIntegral.integral_of_le (by linarith : -H ≤ H)]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [MeasureTheory.integral_prod_symm _ hh]
    apply integral_congr_ae
    filter_upwards with τ
    by_cases hτ : τ ∈ Ioc (-H) H
    · rw [Set.indicator_of_mem hτ _]
      have hminmax : max 0 (-τ) ≤ min H (H - τ) := by
        obtain ⟨hτ1, hτ2⟩ := Set.mem_Ioc.mp hτ
        rw [max_le_iff]
        exact ⟨le_min_iff.mpr ⟨hH, by linarith⟩,
          le_min_iff.mpr ⟨by linarith, by linarith⟩⟩
      rw [intervalIntegral.integral_of_le hminmax]
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards with v
      by_cases hv : v ∈ Ioc (max 0 (-τ)) (min H (H - τ))
      · rw [Set.indicator_of_mem hv _, hh_eq v τ ((hRmem2 hτ).mpr hv)]
      · rw [Set.indicator_of_notMem hv _,
          hh_zero v τ (fun hmem => hv ((hRmem2 hτ).mp hmem))]
    · rw [Set.indicator_of_notMem hτ _]
      have hzero : ∀ v : ℝ, R.indicator (Function.uncurry Φ) (v, τ) = 0 :=
        fun v => hh_zero v τ (fun hmem => hτ (hRτ hmem))
      simp [hzero]
  exact hLHS.trans hRHS.symm

/-- The translated-correlation double integral over the square window,
written directly in the `w - v` translated form, swaps to the lag form. -/
theorem intervalIntegral_pair_sub_eq_lagIntegral
    {Φ : ℝ → ℝ → ℝ} (hΦ : Continuous (Function.uncurry Φ)) {H : ℝ} (hH : 0 ≤ H) :
    (∫ v in (0 : ℝ)..H, ∫ w in (0 : ℝ)..H, Φ v (w - v)) =
      ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ), Φ v τ := by
  have hsub : ∀ v : ℝ, (∫ w in (0 : ℝ)..H, Φ v (w - v)) =
      ∫ τ in (-v)..H - v, Φ v τ := by
    intro v
    have h := intervalIntegral.integral_comp_sub_right (f := Φ v) (a := (0 : ℝ))
      (b := H) v
    rw [zero_sub] at h
    exact h
  rw [intervalIntegral.integral_congr (fun v _hv => hsub v)]
  exact intervalIntegral_pair_sub_swap hΦ hH

end MathlibAux
