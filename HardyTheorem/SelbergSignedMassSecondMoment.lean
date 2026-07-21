import HardyTheorem.SelbergGoodWindowMeasure
import MathlibAux.SlidingIntervalCorrelation
import MathlibAux.SlidingWindowBadSet

open Complex MeasureTheory Set ComplexConjugate
open scoped BigOperators

namespace HardyTheorem

/-!
# Second moment of the signed short Selberg mass

The sharp Chebyshev route to the excessive-signed-mass bound uses the second
moment of the signed short integral itself, not the crude per-window
Cauchy--Schwarz reduction to a global `L^2` mass.  The sliding correlation
kernel rewrites that second moment as a double integral of the translated
autocorrelation of the mollified Hardy function:

```
∫_t (∫_{u in 0..H} Z(t+u) du)^2 dt
  = ∫_{v in 0..H} ∫_{w in 0..H} ∫_{x} Z(x) * Z(x + (w - v)) dx dw dv .
```

This is the structural hinge of the signed route: the Hardy phase makes the
autocorrelation oscillate on the scale `1 / log T`, so the double integral
carries the `sinc`-type decay in `A` that the budget
`... <= T * eta^2 / 24` ultimately exploits.  No prime-coefficient
obstruction enters, because the bilinear form keeps its signs.
-/

/-- The signed short integral is definitionally a sliding-window mass. -/
theorem selbergSignedShortIntegral_eq_slidingWindowMass (X : ℕ) (H t : ℝ) :
    selbergMoebiusSignedShortIntegral X H t =
      MathlibAux.slidingWindowMass (selbergMoebiusMollifiedHardyZ X) H t :=
  rfl

private theorem continuous_slidingWindowMass_of_continuous'
    {g : ℝ → ℝ} (hg : Continuous g) (H : ℝ) :
    Continuous (MathlibAux.slidingWindowMass g H) := by
  let G : ℝ → ℝ := fun x => ∫ u in 0..x, g u
  have hG : Continuous G := by
    dsimp only [G]
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_x : ℝ) u => g u)
      (hg.comp continuous_snd) continuous_id
  have heq : MathlibAux.slidingWindowMass g H =
      fun t => G (t + H) - G t := by
    funext t
    have h0add : IntervalIntegrable g volume 0 (t + H) :=
      hg.intervalIntegrable _ _
    have h0t : IntervalIntegrable g volume 0 t :=
      hg.intervalIntegrable _ _
    dsimp only [MathlibAux.slidingWindowMass, G]
    exact (intervalIntegral.integral_interval_sub_left h0add h0t).symm
  rw [heq]
  exact (hG.comp (continuous_id.add continuous_const)).sub hG

/-- The signed short integral is continuous in the start parameter. -/
theorem continuous_selbergSignedShortIntegral (X : ℕ) (H : ℝ) :
    Continuous (selbergMoebiusSignedShortIntegral X H) :=
  continuous_slidingWindowMass_of_continuous'
    (continuous_selbergMoebiusMollifiedHardyZ X) H

/-- The second moment of the signed short integral over the start interval
equals the translated-autocorrelation double integral of the mollified Hardy
function. -/
theorem integral_sq_signedShortIntegral_eq_correlation
    (X : ℕ) {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2) =
      ∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
        selbergMoebiusMollifiedHardyZ X x *
          selbergMoebiusMollifiedHardyZ X (x + (w - v)) := by
  have hZc : Continuous (fun t : ℝ => (selbergMoebiusMollifiedHardyZ X t : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_selbergMoebiusMollifiedHardyZ X)
  have hk := MathlibAux.slidingIntervalCorrelation_kernel hZc hZc hAB hH
  have hI : ∀ t : ℝ,
      (∫ v in 0..H, (selbergMoebiusMollifiedHardyZ X (t + v) : ℂ)) =
        (selbergMoebiusSignedShortIntegral X H t : ℂ) := by
    intro t
    rw [intervalIntegral.integral_ofReal]
    congr 1
    have hcomp :
        (∫ v in 0..H, selbergMoebiusMollifiedHardyZ X (t + v)) =
          ∫ v in 0..H, selbergMoebiusMollifiedHardyZ X (v + t) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      dsimp only
      rw [add_comm]
    unfold selbergMoebiusSignedShortIntegral
    rw [hcomp, intervalIntegral.integral_comp_add_right, zero_add,
      add_comm H t]
  have hpoint : ∀ t : ℝ,
      conj (∫ v in 0..H, (selbergMoebiusMollifiedHardyZ X (t + v) : ℂ)) *
          (∫ w in 0..H, (selbergMoebiusMollifiedHardyZ X (t + w) : ℂ)) =
        ((selbergMoebiusSignedShortIntegral X H t ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [hI t]
    simp [pow_two]
  have hmain :
      (∫ t in A..B,
          conj (∫ v in 0..H, (selbergMoebiusMollifiedHardyZ X (t + v) : ℂ)) *
            (∫ w in 0..H, (selbergMoebiusMollifiedHardyZ X (t + w) : ℂ))) =
        ((∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro t _ht
    exact hpoint t
  have htri :
      (∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
          conj (selbergMoebiusMollifiedHardyZ X x : ℂ) *
            (selbergMoebiusMollifiedHardyZ X (x + (w - v)) : ℂ)) =
        ((∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
          selbergMoebiusMollifiedHardyZ X x *
            selbergMoebiusMollifiedHardyZ X (x + (w - v)) : ℝ) : ℂ) := by
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

/-- The excessive-signed starts are controlled by the second moment of the
signed short integral itself: a sharp Chebyshev bound with no per-window
Cauchy--Schwarz loss. -/
theorem volume_selbergExcessiveSignedMassStarts_inter_Icc_le_signedSecondMoment
    (X : ℕ) {A B H eta : ℝ} (hAB : A ≤ B) (heta : 0 < eta) :
    volume.real (selbergExcessiveSignedMassStarts X H eta ∩ Icc A B) ≤
      (∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2) / eta ^ 2 := by
  have hScont : Continuous (fun t : ℝ => selbergMoebiusSignedShortIntegral X H t) :=
    continuous_selbergSignedShortIntegral X H
  have hsubset :
      selbergExcessiveSignedMassStarts X H eta ∩ Icc A B ⊆
        {t | eta ^ 2 ≤ (selbergMoebiusSignedShortIntegral X H t) ^ 2} ∩
          Icc A B := by
    intro t ht
    constructor
    · have hbig : eta ≤ |selbergMoebiusSignedShortIntegral X H t| := ht.1
      change eta ^ 2 ≤ (selbergMoebiusSignedShortIntegral X H t) ^ 2
      rw [← sq_abs (selbergMoebiusSignedShortIntegral X H t)]
      simpa only [pow_two] using mul_self_le_mul_self heta.le hbig
    · exact ht.2
  have hfint : Integrable
      (fun t : ℝ => (selbergMoebiusSignedShortIntegral X H t) ^ 2)
      (volume.restrict (Icc A B)) :=
    (hScont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hmarkov :
      eta ^ 2 * volume.real
          ({t | eta ^ 2 ≤ (selbergMoebiusSignedShortIntegral X H t) ^ 2} ∩
            Icc A B) ≤
        ∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2 := by
    have h := mul_meas_ge_le_integral_of_nonneg
      (μ := volume.restrict (Icc A B))
      (Filter.Eventually.of_forall fun t =>
        sq_nonneg (selbergMoebiusSignedShortIntegral X H t))
      hfint (eta ^ 2)
    rw [measureReal_restrict_apply' measurableSet_Icc] at h
    calc
      eta ^ 2 * volume.real
          ({t | eta ^ 2 ≤ (selbergMoebiusSignedShortIntegral X H t) ^ 2} ∩
            Icc A B)
        ≤ ∫ t, (selbergMoebiusSignedShortIntegral X H t) ^ 2
          ∂volume.restrict (Icc A B) := h
      _ = ∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2 := by
          rw [integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le hAB]
  have hfinite :
      volume ({t | eta ^ 2 ≤ (selbergMoebiusSignedShortIntegral X H t) ^ 2} ∩
          Icc A B) ≠ ⊤ :=
    measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne
  have hmono := measureReal_mono hsubset hfinite
  apply hmono.trans
  rw [le_div_iff₀ (sq_pos_of_pos heta)]
  simpa [mul_comm] using hmarkov

/-- Conditional final step for the excessive-signed endpoint estimate, sharp
form: any upper bound on the translated-autocorrelation double integral of
the mollified Hardy function that meets the budget `T * eta^2 / 24` gives the
`T / 24` measure bound, in the exact shape of the `hexcessive` hypothesis of
`selberg_odd_zero_proportion_target_of_mollified_good_window_bounds`. -/
theorem volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_correlation_le
    (X : ℕ) (A T eta : ℝ) (hA0 : 0 < A) (hT1 : 1 < T)
    (hHT : A / Real.log T ≤ T) (heta : 0 < eta)
    (hcorr :
      (∫ v in 0..A / Real.log T, ∫ w in 0..A / Real.log T,
        ∫ x in T + v..(2 * T - A / Real.log T) + v,
          selbergMoebiusMollifiedHardyZ X x *
            selbergMoebiusMollifiedHardyZ X (x + (w - v))) ≤
        T * eta ^ 2 / 24) :
    volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
      selbergExcessiveSignedMassStarts X (A / Real.log T) eta) ≤ T / 24 := by
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hH : 0 < A / Real.log T := div_pos hA0 hlogT
  have hAB : T ≤ 2 * T - A / Real.log T := by linarith
  have hcheb :=
    volume_selbergExcessiveSignedMassStarts_inter_Icc_le_signedSecondMoment
      X (H := A / Real.log T) hAB heta
  have hcorr_eq := integral_sq_signedShortIntegral_eq_correlation X hAB hH.le
  rw [Set.inter_comm]
  refine le_trans hcheb ?_
  rw [hcorr_eq]
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [div_le_iff₀ heta2]
  calc
    (∫ v in 0..A / Real.log T, ∫ w in 0..A / Real.log T,
      ∫ x in T + v..(2 * T - A / Real.log T) + v,
        selbergMoebiusMollifiedHardyZ X x *
          selbergMoebiusMollifiedHardyZ X (x + (w - v)))
      ≤ T * eta ^ 2 / 24 := hcorr
    _ = T / 24 * eta ^ 2 := by ring

end HardyTheorem
