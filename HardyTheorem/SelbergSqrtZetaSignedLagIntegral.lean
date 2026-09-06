import HardyTheorem.SelbergSqrtZetaGoodWindowMeasure
import MathlibAux.SlidingSignedLagIntegral

open MeasureTheory Set

namespace HardyTheorem

/-!
# Signed lag reduction for the square-root-zeta mollifier

The excessive-signed-mass exceptional set is controlled by the second moment
of the same square-root-zeta mollifier used in the absolute-mass estimate.
The generic sliding-window identities then reduce that second moment to a
triangular lag integral of translated autocorrelations.
-/

/-- The signed square-root-zeta short integral is a sliding-window mass. -/
theorem selbergSqrtZetaSignedShortIntegral_eq_slidingWindowMass
    (X : ℕ) (H t : ℝ) :
    selbergSqrtZetaSignedShortIntegral X H t =
      MathlibAux.slidingWindowMass
        (selbergSqrtZetaMollifiedHardyZ X) H t :=
  rfl

/-- The square-root-zeta signed short integral is continuous in its start. -/
theorem continuous_selbergSqrtZetaSignedShortIntegral
    (X : ℕ) (H : ℝ) :
    Continuous (selbergSqrtZetaSignedShortIntegral X H) := by
  change Continuous
    (fun t : ℝ => selbergSqrtZetaSignedShortIntegral X H t)
  simpa only [selbergSqrtZetaSignedShortIntegral_eq_slidingWindowMass] using
    MathlibAux.continuous_slidingWindowMass_of_continuous
      (continuous_selbergSqrtZetaMollifiedHardyZ X) H

/-- The second moment of the signed square-root-zeta short integral equals
its translated-autocorrelation integral. -/
theorem integral_sq_selbergSqrtZetaSignedShortIntegral_eq_correlation
    (X : ℕ) {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) =
      ∫ v in 0..H, ∫ w in 0..H, ∫ x in A + v..B + v,
        selbergSqrtZetaMollifiedHardyZ X x *
          selbergSqrtZetaMollifiedHardyZ X (x + (w - v)) := by
  simpa only [selbergSqrtZetaSignedShortIntegral_eq_slidingWindowMass] using
    MathlibAux.integral_sq_slidingWindowMass_eq_correlation
      (continuous_selbergSqrtZetaMollifiedHardyZ X) hAB hH

/-- The second moment also has the triangular lag representation. -/
theorem integral_sq_selbergSqrtZetaSignedShortIntegral_eq_lagIntegral
    (X : ℕ) {A B H : ℝ} (hAB : A ≤ B) (hH : 0 ≤ H) :
    (∫ t in A..B, (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) =
      ∫ tau in (-H)..H, ∫ v in max 0 (-tau)..min H (H - tau),
        ∫ x in A + v..B + v,
          selbergSqrtZetaMollifiedHardyZ X x *
            selbergSqrtZetaMollifiedHardyZ X (x + tau) := by
  simpa only [selbergSqrtZetaSignedShortIntegral_eq_slidingWindowMass] using
    MathlibAux.integral_sq_slidingWindowMass_eq_lagIntegral
      (continuous_selbergSqrtZetaMollifiedHardyZ X) hAB hH

/-- Chebyshev bounds the excessive signed starts by the signed second
moment, without the extra per-window Cauchy--Schwarz loss. -/
theorem volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_secondMoment
    (X : ℕ) {A B H eta : ℝ} (hAB : A ≤ B) (heta : 0 < eta) :
    volume.real
        (selbergSqrtZetaExcessiveSignedMassStarts X H eta ∩ Icc A B) ≤
      (∫ t in A..B,
        (selbergSqrtZetaSignedShortIntegral X H t) ^ 2) / eta ^ 2 := by
  simpa only [selbergSqrtZetaExcessiveSignedMassStarts,
    selbergSqrtZetaSignedShortIntegral_eq_slidingWindowMass] using
    MathlibAux.volume_abs_slidingWindowMass_ge_inter_Icc_le_secondMoment
      (continuous_selbergSqrtZetaMollifiedHardyZ X) hAB heta

/-- A lag-autocorrelation budget of `T * eta^2 / 24` gives the exact
`T / 24` excessive-set bound required by the square-root-zeta good-window
assembly theorem. -/
theorem volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_lagIntegral_le
    (X : ℕ) (A T eta : ℝ) (hA0 : 0 < A) (hT1 : 1 < T)
    (hHT : A / Real.log T ≤ T) (heta : 0 < eta)
    (hlag :
      (∫ tau in (-(A / Real.log T))..(A / Real.log T),
        ∫ v in max 0 (-tau)..
            min (A / Real.log T) ((A / Real.log T) - tau),
          ∫ x in T + v..(2 * T - A / Real.log T) + v,
            selbergSqrtZetaMollifiedHardyZ X x *
              selbergSqrtZetaMollifiedHardyZ X (x + tau)) ≤
        T * eta ^ 2 / 24) :
    volume.real
        (Set.Icc T (2 * T - A / Real.log T) ∩
          selbergSqrtZetaExcessiveSignedMassStarts
            X (A / Real.log T) eta) ≤
      T / 24 := by
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hH : 0 < A / Real.log T := div_pos hA0 hlogT
  have hAB : T ≤ 2 * T - A / Real.log T := by linarith
  have hcheb :=
    volume_selbergSqrtZetaExcessiveSignedMassStarts_inter_Icc_le_secondMoment
      X (H := A / Real.log T) hAB heta
  have hid :=
    integral_sq_selbergSqrtZetaSignedShortIntegral_eq_lagIntegral
      X hAB hH.le
  rw [Set.inter_comm]
  refine le_trans hcheb ?_
  rw [hid]
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [div_le_iff₀ heta2]
  calc
    (∫ tau in (-(A / Real.log T))..(A / Real.log T),
      ∫ v in max 0 (-tau)..
          min (A / Real.log T) ((A / Real.log T) - tau),
        ∫ x in T + v..(2 * T - A / Real.log T) + v,
          selbergSqrtZetaMollifiedHardyZ X x *
            selbergSqrtZetaMollifiedHardyZ X (x + tau))
      ≤ T * eta ^ 2 / 24 := hlag
    _ = T / 24 * eta ^ 2 := by ring

end HardyTheorem
