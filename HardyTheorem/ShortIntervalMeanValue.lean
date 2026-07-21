import HardyTheorem.FirstZetaApproximation
import HardyTheorem.HardyIntegralBasics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The signed Hardy-Z integral over a sliding interval of length `delta`. -/
noncomputable def hardyShortIntegral (δ t : ℝ) : ℝ :=
  ∫ u in t..t + δ, hardyZ u

/-- The absolute Hardy-Z integral over a sliding interval of length `delta`. -/
noncomputable def hardyShortAbsIntegral (δ t : ℝ) : ℝ :=
  ∫ u in t..t + δ, |hardyZ u|

theorem continuous_hardyShortIntegral (δ : ℝ) :
    Continuous (hardyShortIntegral δ) := by
  let F : ℝ → ℝ := fun x => ∫ u in 0..x, hardyZ u
  have hF : Continuous F := by
    dsimp only [F]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_x : ℝ) u => hardyZ u)
        (hardyZ_continuous.comp continuous_snd) continuous_id
  have hEq : hardyShortIntegral δ = fun t => F (t + δ) - F t := by
    funext t
    have h0add : IntervalIntegrable hardyZ volume 0 (t + δ) :=
      hardyZ_continuous.intervalIntegrable _ _
    have h0t : IntervalIntegrable hardyZ volume 0 t :=
      hardyZ_continuous.intervalIntegrable _ _
    dsimp only [hardyShortIntegral, F]
    exact (intervalIntegral.integral_interval_sub_left h0add h0t).symm
  rw [hEq]
  exact (hF.comp (continuous_id.add continuous_const)).sub hF

theorem continuous_hardyShortAbsIntegral (δ : ℝ) :
    Continuous (hardyShortAbsIntegral δ) := by
  let F : ℝ → ℝ := fun x => ∫ u in 0..x, |hardyZ u|
  have habs : Continuous fun u : ℝ => |hardyZ u| := hardyZ_continuous.abs
  have hF : Continuous F := by
    dsimp only [F]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_x : ℝ) u => |hardyZ u|)
        (habs.comp continuous_snd) continuous_id
  have hEq : hardyShortAbsIntegral δ = fun t => F (t + δ) - F t := by
    funext t
    have h0add : IntervalIntegrable (fun u : ℝ => |hardyZ u|) volume 0 (t + δ) :=
      habs.intervalIntegrable _ _
    have h0t : IntervalIntegrable (fun u : ℝ => |hardyZ u|) volume 0 t :=
      habs.intervalIntegrable _ _
    dsimp only [hardyShortAbsIntegral, F]
    exact (intervalIntegral.integral_interval_sub_left h0add h0t).symm
  rw [hEq]
  exact (hF.comp (continuous_id.add continuous_const)).sub hF

/-- A short absolute Hardy-Z integral inside `[T, 2T]` is bounded by its
length times the uniform `O(sqrt T)` critical-line bound. -/
theorem exists_hardyShortAbsIntegral_le_mul_sqrt :
    ∃ C T0 : ℝ, 0 < C ∧ 1 ≤ T0 ∧
      ∀ T δ t : ℝ, T0 ≤ T → 0 ≤ δ → t ∈ Set.Icc T (2 * T - δ) →
        hardyShortAbsIntegral δ t ≤ C * δ * Real.sqrt T := by
  obtain ⟨C, T0, hC, hT0, hbound⟩ :=
    exists_norm_riemannZeta_critical_line_le_sqrt
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro T δ t hT hδ ht
  have htt : t ≤ t + δ := by linarith
  have habsInt :
      IntervalIntegrable (fun u : ℝ => |hardyZ u|) volume t (t + δ) :=
    hardyZ_continuous.abs.intervalIntegrable _ _
  have hconstInt :
      IntervalIntegrable (fun _u : ℝ => C * Real.sqrt T) volume t (t + δ) :=
    continuous_const.intervalIntegrable _ _
  have hpoint : ∀ u ∈ Set.Icc t (t + δ),
      |hardyZ u| ≤ C * Real.sqrt T := by
    intro u hu
    rw [abs_hardyZ_eq_norm_riemannZeta]
    apply hbound T u hT
    constructor
    · exact ht.1.trans hu.1
    · linarith [hu.2, ht.2]
  dsimp only [hardyShortAbsIntegral]
  calc
    (∫ u in t..t + δ, |hardyZ u|) ≤
        ∫ _u in t..t + δ, C * Real.sqrt T :=
      intervalIntegral.integral_mono_on htt habsInt hconstInt hpoint
    _ = C * δ * Real.sqrt T := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

/-- Averaging the absolute Hardy-Z mass over all sliding intervals of length
`delta` controls `delta` times the mass on the common interior interval. -/
theorem mul_integral_abs_hardyZ_interior_le_integral_hardyShortAbsIntegral
    (T δ : ℝ) (hδ : 0 ≤ δ) (hroom : 2 * δ ≤ T) :
    δ * (∫ u in T + δ..2 * T - δ, |hardyZ u|) ≤
      ∫ t in T..2 * T - δ, hardyShortAbsIntegral δ t := by
  let f : ℝ → ℝ := fun u => |hardyZ u|
  let g : ℝ → ℝ → ℝ := fun t v => f (t + v)
  have hTB : T ≤ 2 * T - δ := by linarith
  have hinter : T + δ ≤ 2 * T - δ := by linarith
  have hfcont : Continuous f := hardyZ_continuous.abs
  have hgcont : Continuous (Function.uncurry g) := by
    exact hfcont.comp (continuous_fst.add continuous_snd)
  have hprodCompact :
      IsCompact (Set.uIcc T (2 * T - δ) ×ˢ Set.uIcc 0 δ) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hgIntCompact : IntegrableOn (Function.uncurry g)
      (Set.uIcc T (2 * T - δ) ×ˢ Set.uIcc 0 δ)
      (volume.prod volume) :=
    hgcont.continuousOn.integrableOn_compact hprodCompact
  have hgInt : Integrable (Function.uncurry g)
      ((volume.restrict (Set.uIoc T (2 * T - δ))).prod
        (volume.restrict (Set.uIoc 0 δ))) := by
    rw [Measure.prod_restrict]
    exact hgIntCompact.mono_set (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (a := T) (b := 2 * T - δ)
    (μ := volume.restrict (Set.uIoc 0 δ)) hgInt
  have hswap' :
      (∫ t in T..2 * T - δ, ∫ v in 0..δ, g t v) =
        ∫ v in 0..δ, ∫ t in T..2 * T - δ, g t v := by
    simpa [intervalIntegral.integral_of_le hδ, Set.uIoc_of_le hδ] using hswap
  have hinner (v : ℝ) (hv : v ∈ Set.Icc 0 δ) :
      (∫ u in T + δ..2 * T - δ, f u) ≤
        ∫ t in T..2 * T - δ, g t v := by
    have hlarge : IntervalIntegrable f volume (T + v) (2 * T - δ + v) :=
      hfcont.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_interval
      (f := f) (μ := volume)
      (c := T + v) (a := T + δ) (b := 2 * T - δ)
      (d := 2 * T - δ + v)
      (by linarith [hv.2]) hinter (by linarith [hv.1])
      (by
        filter_upwards [] with x
        exact abs_nonneg (hardyZ x)) hlarge
    calc
      (∫ u in T + δ..2 * T - δ, f u) ≤
          ∫ u in T + v..2 * T - δ + v, f u := hmono
      _ = ∫ t in T..2 * T - δ, g t v := by
        change (∫ u in T + v..2 * T - δ + v, f u) =
          ∫ t in T..2 * T - δ, f (t + v)
        exact (intervalIntegral.integral_comp_add_right f v).symm
  have hconstInt : IntervalIntegrable
      (fun _v : ℝ => ∫ u in T + δ..2 * T - δ, f u) volume 0 δ :=
    continuous_const.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable
      (fun v : ℝ => ∫ t in T..2 * T - δ, g t v) volume 0 δ := by
    have hcont : Continuous fun v : ℝ => ∫ t in T..2 * T - δ, g t v := by
      have hswapCont : Continuous (Function.uncurry fun v t => g t v) := by
        exact hfcont.comp (continuous_snd.add continuous_fst)
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (a₀ := T)
        (f := fun v t => g t v)
        hswapCont continuous_const
    exact hcont.intervalIntegrable _ _
  have hmonoOuter :
      (∫ _v in 0..δ, ∫ u in T + δ..2 * T - δ, f u) ≤
        ∫ v in 0..δ, ∫ t in T..2 * T - δ, g t v :=
    intervalIntegral.integral_mono_on hδ hconstInt hrightInt hinner
  calc
    δ * (∫ u in T + δ..2 * T - δ, |hardyZ u|) =
        ∫ _v in 0..δ, ∫ u in T + δ..2 * T - δ, f u := by
      simp only [intervalIntegral.integral_const, smul_eq_mul, f]
      ring
    _ ≤ ∫ v in 0..δ, ∫ t in T..2 * T - δ, g t v := hmonoOuter
    _ = ∫ t in T..2 * T - δ, hardyShortAbsIntegral δ t := by
      rw [← hswap']
      apply intervalIntegral.integral_congr
      intro t _ht
      dsimp only [hardyShortAbsIntegral]
      calc
        (∫ v in 0..δ, g t v) = ∫ v in 0..δ, f (v + t) := by
          apply intervalIntegral.integral_congr
          intro v _hv
          simp only [g]
          congr 1
          ring
        _ = ∫ u in 0 + t..δ + t, f u :=
          intervalIntegral.integral_comp_add_right f t
        _ = ∫ u in t..t + δ, |hardyZ u| := by
          simp only [f, zero_add]
          congr 1
          ring

/-- The dyadic `L¹` lower bound survives averaging over every fixed positive
short-interval length. The threshold may depend on the length, while the
linear constant does not. -/
theorem exists_integral_hardyShortAbsIntegral_ge_mul :
    ∃ c : ℝ, 0 < c ∧ ∀ δ : ℝ, 0 < δ → ∃ T0 : ℝ, 1 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        c * δ * T ≤ ∫ t in T..2 * T - δ, hardyShortAbsIntegral δ t := by
  obtain ⟨c0, Tz, hc0, hTz, hzeta⟩ :=
    exists_integral_norm_riemannZeta_critical_line_ge_mul
  obtain ⟨C, Tp, hC, hTp, hshort⟩ :=
    exists_hardyShortAbsIntegral_le_mul_sqrt
  refine ⟨c0 / 2, by positivity, ?_⟩
  intro δ hδpos
  have hδ : 0 ≤ δ := hδpos.le
  let K : ℝ := 4 * C * δ / c0
  let T0 : ℝ := max Tz (max Tp (max (2 * δ) (max 1 (K ^ 2))))
  refine ⟨T0, ?_, ?_⟩
  · exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  intro T hT
  have hTz' : Tz ≤ T := (le_max_left _ _).trans hT
  have hrest : max Tp (max (2 * δ) (max 1 (K ^ 2))) ≤ T :=
    (le_max_right Tz _).trans hT
  have hTp' : Tp ≤ T := (le_max_left _ _).trans hrest
  have hrest2 : max (2 * δ) (max 1 (K ^ 2)) ≤ T :=
    (le_max_right Tp _).trans hrest
  have hroom : 2 * δ ≤ T := (le_max_left _ _).trans hrest2
  have hrest3 : max 1 (K ^ 2) ≤ T := (le_max_right _ _).trans hrest2
  have hT1 : 1 ≤ T := (le_max_left _ _).trans hrest3
  have hKsq : K ^ 2 ≤ T := (le_max_right _ _).trans hrest3
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hKsqrt : K ≤ Real.sqrt T := by
    exact (Real.le_sqrt hKnonneg hTpos.le).2 hKsq
  have hsqrtSq : (Real.sqrt T) ^ 2 = T := Real.sq_sqrt hTpos.le
  have hendpointTotal :
      2 * C * δ * Real.sqrt T ≤ (c0 / 2) * T := by
    have hcMul : 4 * C * δ ≤ c0 * Real.sqrt T := by
      have := mul_le_mul_of_nonneg_left hKsqrt hc0.le
      dsimp only [K] at this
      field_simp [hc0.ne'] at this
      exact this
    have hcMulSqrt := mul_le_mul_of_nonneg_right hcMul (Real.sqrt_nonneg T)
    nlinarith [hcMulSqrt]
  let f : ℝ → ℝ := fun u => |hardyZ u|
  have hfcont : Continuous f := hardyZ_continuous.abs
  have hleftInt : IntervalIntegrable f volume T (T + δ) :=
    hfcont.intervalIntegrable _ _
  have hmiddleInt : IntervalIntegrable f volume (T + δ) (2 * T - δ) :=
    hfcont.intervalIntegrable _ _
  have hrightInt : IntervalIntegrable f volume (2 * T - δ) (2 * T) :=
    hfcont.intervalIntegrable _ _
  have hglobalInt : IntervalIntegrable f volume T (2 * T) :=
    hfcont.intervalIntegrable _ _
  have hglobal : c0 * T ≤ ∫ u in T..2 * T, f u := by
    calc
      c0 * T ≤ ∫ u in T..2 * T,
          ‖riemannZeta ((1 / 2 : ℂ) + I * u)‖ := hzeta T hTz'
      _ = ∫ u in T..2 * T, f u := by
        apply intervalIntegral.integral_congr
        intro u _hu
        change ‖riemannZeta ((1 / 2 : ℂ) + I * u)‖ = |hardyZ u|
        exact (abs_hardyZ_eq_norm_riemannZeta u).symm
  have hleft : (∫ u in T..T + δ, f u) ≤ C * δ * Real.sqrt T := by
    simpa only [hardyShortAbsIntegral, f] using
      hshort T δ T hTp' hδ ⟨le_rfl, by linarith⟩
  have hright : (∫ u in 2 * T - δ..2 * T, f u) ≤
      C * δ * Real.sqrt T := by
    have h := hshort T δ (2 * T - δ) hTp' hδ ⟨by linarith, le_rfl⟩
    dsimp only [hardyShortAbsIntegral, f] at h ⊢
    simpa only [sub_add_cancel] using h
  have hdecomp :
      (∫ u in T..2 * T, f u) =
        (∫ u in T..T + δ, f u) +
        (∫ u in T + δ..2 * T - δ, f u) +
        ∫ u in 2 * T - δ..2 * T, f u := by
    have hfirst := intervalIntegral.integral_add_adjacent_intervals
      hleftInt hmiddleInt
    have hsecond := intervalIntegral.integral_add_adjacent_intervals
      (hleftInt.trans hmiddleInt) hrightInt
    linarith
  have hinterior :
      (c0 / 2) * T ≤ ∫ u in T + δ..2 * T - δ, f u := by
    rw [hdecomp] at hglobal
    linarith
  have havg := mul_integral_abs_hardyZ_interior_le_integral_hardyShortAbsIntegral
    T δ hδ hroom
  have hmul := mul_le_mul_of_nonneg_left hinterior hδ
  dsimp only [f] at hmul
  calc
    (c0 / 2) * δ * T = δ * ((c0 / 2) * T) := by ring
    _ ≤ δ * (∫ u in T + δ..2 * T - δ, |hardyZ u|) := hmul
    _ ≤ ∫ t in T..2 * T - δ, hardyShortAbsIntegral δ t := havg

end HardyTheorem
