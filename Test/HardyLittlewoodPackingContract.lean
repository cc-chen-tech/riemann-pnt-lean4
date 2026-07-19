import HardyTheorem.HardyLittlewoodPacking

open Complex MeasureTheory Set

open HardyTheorem

#check hardy_littlewood_lower_bound_target_of_good_window_measure

#print axioms hardy_littlewood_lower_bound_target_of_good_window_measure

example (H T0 : ℝ) (good : ℝ → Set ℝ) (hH : 0 < H)
    (hbad : ∀ T ≥ T0,
      volume.real (Set.Icc T (2 * T - H) \ good T) ≤ T / 12)
    (hhit : ∀ T ≥ T0, ∀ t ∈ good T ∩ Set.Icc T (2 * T - 2 * H),
      ∃ u ∈ Set.Ioo t (t + H),
        riemannZeta ((1 / 2 : ℂ) + I * u) = 0) :
    hardy_littlewood_lower_bound_target := by
  exact hardy_littlewood_lower_bound_target_of_good_window_measure
    H T0 good hH hbad hhit
