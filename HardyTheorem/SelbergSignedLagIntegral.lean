import HardyTheorem.SelbergSignedMassSecondMoment
import MathlibAux.SlidingRegionSwap

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Lag form of the signed short-mass second moment

Composing the correlation kernel with the region swap expresses the second
moment of the signed short Selberg mass as a lag integral: for each lag
`τ ∈ (-H, H]`, the start variable runs over the explicit section
`max 0 (-τ) < v ≤ min H (H - τ)` of the diagonal region.  This is the exact
interface at which the Hardy-phase oscillation must supply the `sinc`-type
decay: the section length is the triangle weight `H - |τ|`, and the inner
autocorrelation of the mollified Hardy function oscillates on the scale
`1 / log T`.
-/

/-- The second moment of the signed short integral equals the lag integral of
the translated autocorrelation of the mollified Hardy function. -/
theorem integral_sq_signedShortIntegral_eq_lagIntegral
    (X : ℕ) {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (selbergMoebiusSignedShortIntegral X H t) ^ 2) =
      ∫ τ in (-H)..H, ∫ v in max 0 (-τ)..min H (H - τ),
        ∫ x in A + v..B + v,
          selbergMoebiusMollifiedHardyZ X x *
            selbergMoebiusMollifiedHardyZ X (x + τ) := by
  have hZ := continuous_selbergMoebiusMollifiedHardyZ X
  have hΦrw : ∀ v τ : ℝ,
      (∫ x in A + v..B + v, selbergMoebiusMollifiedHardyZ X x *
          selbergMoebiusMollifiedHardyZ X (x + τ)) =
        ∫ y in A..B, selbergMoebiusMollifiedHardyZ X (y + v) *
          selbergMoebiusMollifiedHardyZ X (y + v + τ) := by
    intro v τ
    exact (intervalIntegral.integral_comp_add_right
      (fun x => selbergMoebiusMollifiedHardyZ X x *
        selbergMoebiusMollifiedHardyZ X (x + τ)) v).symm
  have hΦcont : Continuous (Function.uncurry (fun v τ : ℝ =>
      ∫ x in A + v..B + v, selbergMoebiusMollifiedHardyZ X x *
        selbergMoebiusMollifiedHardyZ X (x + τ))) := by
    have hcont : Continuous (Function.uncurry (fun v τ : ℝ =>
        ∫ y in A..B, selbergMoebiusMollifiedHardyZ X (y + v) *
          selbergMoebiusMollifiedHardyZ X (y + v + τ))) := by
      have hfcont : Continuous
          (Function.uncurry (fun (p : ℝ × ℝ) (y : ℝ) =>
            selbergMoebiusMollifiedHardyZ X (y + p.1) *
              selbergMoebiusMollifiedHardyZ X (y + p.1 + p.2))) :=
        (hZ.comp (continuous_snd.add
          (continuous_fst.comp continuous_fst))).mul
          (hZ.comp ((continuous_snd.add
            (continuous_fst.comp continuous_fst)).add
            (continuous_snd.comp continuous_fst)))
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (μ := volume) hfcont A B
    rw [show (Function.uncurry (fun v τ : ℝ =>
          ∫ x in A + v..B + v, selbergMoebiusMollifiedHardyZ X x *
            selbergMoebiusMollifiedHardyZ X (x + τ))) =
        (Function.uncurry (fun v τ : ℝ =>
          ∫ y in A..B, selbergMoebiusMollifiedHardyZ X (y + v) *
            selbergMoebiusMollifiedHardyZ X (y + v + τ))) from
      funext fun p => hΦrw p.1 p.2]
    exact hcont
  rw [integral_sq_signedShortIntegral_eq_correlation X hAB hH]
  exact MathlibAux.intervalIntegral_pair_sub_eq_lagIntegral hΦcont hH

/-- Conditional final step for the excessive-signed endpoint estimate, lag
form: any upper bound on the lag integral of the translated autocorrelation
of the mollified Hardy function that meets the budget `T * eta^2 / 24` gives
the `T / 24` measure bound, in the exact shape of the `hexcessive` hypothesis
of `selberg_odd_zero_proportion_target_of_mollified_good_window_bounds`. -/
theorem volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_lagIntegral_le
    (X : ℕ) (A T eta : ℝ) (hA0 : 0 < A) (hT1 : 1 < T)
    (hHT : A / Real.log T ≤ T) (heta : 0 < eta)
    (hlag :
      (∫ τ in (-(A / Real.log T))..(A / Real.log T),
        ∫ v in max 0 (-τ)..min (A / Real.log T) ((A / Real.log T) - τ),
          ∫ x in T + v..(2 * T - A / Real.log T) + v,
            selbergMoebiusMollifiedHardyZ X x *
              selbergMoebiusMollifiedHardyZ X (x + τ)) ≤
        T * eta ^ 2 / 24) :
    volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
      selbergExcessiveSignedMassStarts X (A / Real.log T) eta) ≤ T / 24 := by
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hH : 0 < A / Real.log T := div_pos hA0 hlogT
  have hAB : T ≤ 2 * T - A / Real.log T := by linarith
  have hcheb :=
    volume_selbergExcessiveSignedMassStarts_inter_Icc_le_signedSecondMoment
      X (H := A / Real.log T) hAB heta
  have hid := integral_sq_signedShortIntegral_eq_lagIntegral X hAB hH.le
  rw [Set.inter_comm]
  refine le_trans hcheb ?_
  rw [hid]
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [div_le_iff₀ heta2]
  calc
    (∫ τ in (-(A / Real.log T))..(A / Real.log T),
      ∫ v in max 0 (-τ)..min (A / Real.log T) ((A / Real.log T) - τ),
        ∫ x in T + v..(2 * T - A / Real.log T) + v,
          selbergMoebiusMollifiedHardyZ X x *
            selbergMoebiusMollifiedHardyZ X (x + τ))
      ≤ T * eta ^ 2 / 24 := hlag
    _ = T / 24 * eta ^ 2 := by ring

end HardyTheorem
