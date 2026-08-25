import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set
open scoped Interval

namespace MathlibAux

/-!
# A lower first moment for forward sliding windows

For a nonnegative continuous function, every point `u ∈ [H,T]` is covered by
the full length-`H` family of starts `t ∈ [u-H,u] ⊆ [0,T]`.  The theorem
below records this Tonelli geometry using finite interval integrals.
-/

/-- Averaging the forward length-`H` mass over starts in `[0,T]` captures at
least `H` copies of the mass on the interior interval `[H,T]`. -/
theorem length_mul_integral_interior_le_integral_slidingWindow
    {g : ℝ → ℝ} (hg : Continuous g) (hg_nonneg : ∀ u, 0 ≤ g u)
    {T H : ℝ} (hH : 0 ≤ H) (hHT : H ≤ T) :
    H * (∫ u in H..T, g u) ≤
      ∫ t in 0..T, ∫ u in t..t + H, g u := by
  let q : ℝ → ℝ → ℝ := fun t v => g (t + v)
  have hT : 0 ≤ T := hH.trans hHT
  have hprodCompact : IsCompact (uIcc 0 T ×ˢ uIcc 0 H) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hqcont : Continuous (Function.uncurry q) := by
    exact hg.comp (continuous_fst.add continuous_snd)
  have hqIntCompact : IntegrableOn (Function.uncurry q)
      (uIcc 0 T ×ˢ uIcc 0 H) (volume.prod volume) :=
    hqcont.continuousOn.integrableOn_compact hprodCompact
  have hqInt : Integrable (Function.uncurry q)
      ((volume.restrict (uIoc 0 T)).prod
        (volume.restrict (uIoc 0 H))) := by
    rw [Measure.prod_restrict]
    exact hqIntCompact.mono_set
      (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (a := (0 : ℝ)) (b := T) (μ := volume.restrict (uIoc 0 H)) hqInt
  have hswap' :
      (∫ t in 0..T, ∫ v in 0..H, q t v) =
        ∫ v in 0..H, ∫ t in 0..T, q t v := by
    simpa [intervalIntegral.integral_of_le hH, uIoc_of_le hH] using hswap
  have hinner (v : ℝ) (hv : v ∈ Icc 0 H) :
      (∫ u in H..T, g u) ≤ ∫ t in 0..T, q t v := by
    have hglobalInt : IntervalIntegrable g volume v (T + v) :=
      hg.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_interval
      (f := g) (μ := volume)
      (c := v) (a := H) (b := T) (d := T + v)
      (by linarith [hv.2]) hHT (by linarith [hv.1])
      (Filter.Eventually.of_forall hg_nonneg) hglobalInt
    calc
      (∫ u in H..T, g u) ≤ ∫ u in v..T + v, g u := hmono
      _ = ∫ t in 0..T, q t v := by
        simpa [q] using (intervalIntegral.integral_comp_add_right g v).symm
  have hrightCont : Continuous (fun v : ℝ => ∫ t in 0..T, q t v) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v t => q t v)
      (by
        change Continuous (fun p : ℝ × ℝ => g (p.2 + p.1))
        exact hg.comp (continuous_snd.add continuous_fst)) 0 T
  have hrightInt : IntervalIntegrable
      (fun v : ℝ => ∫ t in 0..T, q t v) volume 0 H :=
    hrightCont.intervalIntegrable _ _
  have hconstInt : IntervalIntegrable
      (fun _v : ℝ => ∫ u in H..T, g u) volume 0 H :=
    continuous_const.intervalIntegrable _ _
  have houter :
      (∫ _v in 0..H, ∫ u in H..T, g u) ≤
        ∫ v in 0..H, ∫ t in 0..T, q t v :=
    intervalIntegral.integral_mono_on hH hconstInt hrightInt hinner
  have hwindow (t : ℝ) :
      (∫ u in t..t + H, g u) = ∫ v in 0..H, q t v := by
    dsimp only [q]
    calc
      (∫ u in t..t + H, g u) = ∫ u in 0 + t..H + t, g u := by ring_nf
      _ = ∫ v in 0..H, g (v + t) :=
        (intervalIntegral.integral_comp_add_right g t).symm
      _ = ∫ v in 0..H, g (t + v) := by
        apply intervalIntegral.integral_congr
        intro v _
        change g (v + t) = g (t + v)
        rw [add_comm]
  calc
    H * (∫ u in H..T, g u) =
        ∫ _v in 0..H, ∫ u in H..T, g u := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring
    _ ≤ ∫ v in 0..H, ∫ t in 0..T, q t v := houter
    _ = ∫ t in 0..T, ∫ v in 0..H, q t v := hswap'.symm
    _ = ∫ t in 0..T, ∫ u in t..t + H, g u := by
      apply intervalIntegral.integral_congr
      intro t _
      exact (hwindow t).symm

end MathlibAux
