import MathlibAux.SlidingIntervalCorrelation
import MathlibAux.SlidingWindowBadSet

open Complex MeasureTheory Set ComplexConjugate

namespace MathlibAux

/-!
# Second moment of a signed sliding-window mass

This file records the structural facts needed to use a signed short integral:
continuity in the starting point, expansion of its second moment as a
translated autocorrelation, and the resulting Chebyshev measure bound.
-/

/-- A signed sliding-window integral of a continuous real function is
continuous in the starting point. -/
theorem continuous_slidingWindowMass_of_continuous
    {F : ℝ → ℝ} (hF : Continuous F) (H : ℝ) :
    Continuous (slidingWindowMass F H) := by
  let G : ℝ → ℝ := fun x => ∫ u in 0..x, F u
  have hG : Continuous G := by
    dsimp only [G]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_x : ℝ) u => F u)
      (hF.comp continuous_snd) continuous_id
  have heq : slidingWindowMass F H = fun t => G (t + H) - G t := by
    funext t
    have h0add : IntervalIntegrable F volume 0 (t + H) :=
      hF.intervalIntegrable _ _
    have h0t : IntervalIntegrable F volume 0 t :=
      hF.intervalIntegrable _ _
    dsimp only [slidingWindowMass, G]
    exact (intervalIntegral.integral_interval_sub_left h0add h0t).symm
  rw [heq]
  exact (hG.comp (continuous_id.add continuous_const)).sub hG

/-- The second moment of a signed sliding-window integral equals the
translated-autocorrelation integral. -/
theorem integral_sq_slidingWindowMass_eq_correlation
    {F : ℝ → ℝ} (hF : Continuous F)
    {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (slidingWindowMass F H t) ^ 2) =
      ∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
        F x * F (x + (w - v)) := by
  have hFc : Continuous (fun t : ℝ => (F t : ℂ)) :=
    Complex.continuous_ofReal.comp hF
  have hk := slidingIntervalCorrelation_kernel hFc hFc hAB hH
  have hI : ∀ t : ℝ,
      (∫ v in 0..H, (F (t + v) : ℂ)) =
        (slidingWindowMass F H t : ℂ) := by
    intro t
    rw [intervalIntegral.integral_ofReal]
    congr 1
    have hcomp :
        (∫ v in 0..H, F (t + v)) = ∫ v in 0..H, F (v + t) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      dsimp only
      rw [add_comm]
    unfold slidingWindowMass
    rw [hcomp, intervalIntegral.integral_comp_add_right, zero_add,
      add_comm H t]
  have hpoint : ∀ t : ℝ,
      conj (∫ v in 0..H, (F (t + v) : ℂ)) *
          (∫ w in 0..H, (F (t + w) : ℂ)) =
        (((slidingWindowMass F H t) ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [hI t]
    simp [pow_two]
  have hmain :
      (∫ t in A..B,
          conj (∫ v in 0..H, (F (t + v) : ℂ)) *
            (∫ w in 0..H, (F (t + w) : ℂ))) =
        ((∫ t in A..B, (slidingWindowMass F H t) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hpoint t
  have htri :
      (∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
          conj (F x : ℂ) * (F (x + (w - v)) : ℂ)) =
        ((∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
          F x * F (x + (w - v)) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro v _hv
    dsimp only
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro w _hw
    dsimp only
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro x _hx
    simp
  exact Complex.ofReal_injective (hmain.symm.trans (hk.trans htri))

/-- Chebyshev's inequality for the absolute value of a signed sliding-window
integral, restricted to a compact interval. -/
theorem volume_abs_slidingWindowMass_ge_inter_Icc_le_secondMoment
    {F : ℝ → ℝ} (hF : Continuous F)
    {A B H eta : ℝ} (hAB : A ≤ B) (heta : 0 < eta) :
    volume.real ({t | eta ≤ |slidingWindowMass F H t|} ∩ Icc A B) ≤
      (∫ t in A..B, (slidingWindowMass F H t) ^ 2) / eta ^ 2 := by
  have hmass_cont : Continuous (slidingWindowMass F H) :=
    continuous_slidingWindowMass_of_continuous hF H
  have hsubset :
      {t | eta ≤ |slidingWindowMass F H t|} ∩ Icc A B ⊆
        {t | eta ^ 2 ≤ (slidingWindowMass F H t) ^ 2} ∩ Icc A B := by
    intro t ht
    constructor
    · change eta ^ 2 ≤ (slidingWindowMass F H t) ^ 2
      rw [← sq_abs (slidingWindowMass F H t)]
      simpa only [pow_two] using mul_self_le_mul_self heta.le ht.1
    · exact ht.2
  have hfint : Integrable
      (fun t : ℝ => (slidingWindowMass F H t) ^ 2)
      (volume.restrict (Icc A B)) :=
    (hmass_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hmarkov :
      eta ^ 2 * volume.real
          ({t | eta ^ 2 ≤ (slidingWindowMass F H t) ^ 2} ∩ Icc A B) ≤
        ∫ t in A..B, (slidingWindowMass F H t) ^ 2 := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (μ := volume.restrict (Icc A B))
      (Filter.Eventually.of_forall fun t => sq_nonneg (slidingWindowMass F H t))
      hfint (eta ^ 2)
    rw [measureReal_restrict_apply' measurableSet_Icc] at h
    calc
      eta ^ 2 * volume.real
          ({t | eta ^ 2 ≤ (slidingWindowMass F H t) ^ 2} ∩ Icc A B)
        ≤ ∫ t, (slidingWindowMass F H t) ^ 2
          ∂volume.restrict (Icc A B) := h
      _ = ∫ t in A..B, (slidingWindowMass F H t) ^ 2 := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hAB]
  have hfinite :
      volume ({t | eta ^ 2 ≤ (slidingWindowMass F H t) ^ 2} ∩ Icc A B) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hmono := measureReal_mono hsubset hfinite
  apply hmono.trans
  rw [le_div_iff₀ (sq_pos_of_pos heta)]
  simpa [mul_comm] using hmarkov

end MathlibAux
