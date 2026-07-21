import HardyTheorem.SelbergSignedBadSet

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Conditional `T / 24` bound for the excessive-signed-mass start set

The unconditional sliding-window Chebyshev estimate
`volume_selbergExcessiveSignedMassStarts_inter_Icc_le` controls the
excessive-signed-mass starts by `H^2 * M / eta^2`, where `M` is any upper
bound on the global second moment of the mollified Hardy function over the
enlarged interval.  This file records the final measure-theoretic step: a
second-moment bound meeting the explicit budget `H^2 * M <= T * eta^2 / 24`
yields the target `T / 24` measure bound, in the exact shape of the
`hexcessive` hypothesis of
`selberg_odd_zero_proportion_target_of_mollified_good_window_bounds`.
-/

/-- Conditional final step for the excessive-signed endpoint estimate: any
upper bound `M` on the global mollified-Hardy second moment over
`T .. 2T - H + H` that meets the budget `H^2 * M <= T * eta^2 / 24` gives the
`T / 24` measure bound for the excessive-signed-mass start set. -/
theorem volume_selbergExcessiveSignedMassStarts_inter_Icc_le_T_div_24_of_secondMoment_le
    (X : ℕ) (A T eta M : ℝ) (hA0 : 0 < A) (hT1 : 1 < T)
    (hHT : A / Real.log T ≤ T) (heta : 0 < eta)
    (hglobal :
      (∫ u in T..(2 * T - A / Real.log T) + A / Real.log T,
        selbergMoebiusMollifiedHardyZ X u ^ 2) ≤ M)
    (hbudget : (A / Real.log T) ^ 2 * M ≤ T * eta ^ 2 / 24) :
    volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
      selbergExcessiveSignedMassStarts X (A / Real.log T) eta) ≤ T / 24 := by
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hH : 0 < A / Real.log T := div_pos hA0 hlogT
  have hAB : T ≤ 2 * T - A / Real.log T := by
    have := hHT
    linarith
  have hmain := volume_selbergExcessiveSignedMassStarts_inter_Icc_le
    (X := X) hAB hH heta hglobal
  rw [Set.inter_comm]
  refine le_trans hmain ?_
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [div_le_iff₀ heta2]
  calc
    (A / Real.log T) ^ 2 * M ≤ T * eta ^ 2 / 24 := hbudget
    _ = T / 24 * eta ^ 2 := by ring

end HardyTheorem
