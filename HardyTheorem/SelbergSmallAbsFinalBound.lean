import HardyTheorem.SelbergSmallAbsGapBound

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

/-!
# Conditional `T / 24` bound for the small-absolute-mass start set

The unconditional Chebyshev reduction
`exists_volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_gapSum` bounds the
small-absolute-mass start set by the explicit ratio

```
selbergShortDirichletGapSum ... / (H - eta - 4 C H X / sqrt T)^2 .
```

This file records the final measure-theoretic step: any explicit gap-sum upper
bound `M` that is at most `T * (H - eta - 4 C H X / sqrt T)^2 / 24` yields the
target `T / 24` measure bound on the interval `Set.Icc T (2 * T - H)`, in the
exact shape of the `hsmall` hypothesis of
`selberg_odd_zero_proportion_target_of_mollified_good_window_bounds`.
-/

/-- Conditional final step for the small-absolute-mass endpoint estimate: with the
gap-bound constants `C, T0`, any explicit upper bound `M` on the short Dirichlet gap
sum that absorbs the Chebyshev denominator with margin `1 / 24` gives the `T / 24`
measure bound for the small-absolute-mass start set. -/
theorem exists_volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_T_div_24_of_gapSum_le :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ (X : ℕ) (A T eta M : ℝ), 2 ≤ X → T0 ≤ T → 0 < A → A ≤ Real.log T →
        0 < A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T →
        selbergShortDirichletGapSum (firstZetaApproximationCutoff T) X T
          (2 * T - A / Real.log T) (A / Real.log T) ≤ M →
        M ≤ T * (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2 / 24 →
        volume.real (Set.Icc T (2 * T - A / Real.log T) ∩
          selbergSmallAbsoluteMassStarts X (A / Real.log T) eta) ≤ T / 24 := by
  obtain ⟨C, T0, hC, hT0, hbound⟩ :=
    exists_volume_selbergSmallAbsoluteMassStarts_inter_Icc_le_gapSum
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X A T eta M hX hT hA0 hALog hthr hgapM hMbound
  have hT1 : (1 : ℝ) ≤ T := le_trans hT0 hT
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlogT_pos : 0 < Real.log T := lt_of_lt_of_le hA0 hALog
  have hH_nn : 0 ≤ A / Real.log T := div_nonneg hA0.le hlogT_nonneg
  have hH_le_one : A / Real.log T ≤ 1 := by
    rw [div_le_iff₀ hlogT_pos, one_mul]
    exact hALog
  have hH_le_T : A / Real.log T ≤ T := le_trans hH_le_one hT1
  have hratio :=
    hbound X hX T (A / Real.log T) eta hT hH_nn hH_le_T hthr
  have hden_pos :
      0 < (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2 :=
    sq_pos_of_pos hthr
  have hstep1 :
      selbergShortDirichletGapSum (firstZetaApproximationCutoff T) X T
          (2 * T - A / Real.log T) (A / Real.log T) /
          (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2
        ≤ M / (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2 := by
    rw [div_le_iff₀ hden_pos, div_mul_cancel₀ _ (ne_of_gt hden_pos)]
    exact hgapM
  have hstep2 :
      M / (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2
        ≤ T / 24 := by
    rw [div_le_iff₀ hden_pos]
    calc M ≤ T * (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2 / 24 :=
          hMbound
      _ = T / 24 * (A / Real.log T - eta - 4 * C * (A / Real.log T) * X / Real.sqrt T) ^ 2 := by
          ring
  rw [Set.inter_comm]
  exact le_trans hratio (le_trans hstep1 hstep2)

end HardyTheorem
