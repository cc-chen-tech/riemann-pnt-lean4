import HardyTheorem.SelbergPacking

open Complex MeasureTheory Set

namespace HardyTheorem

#check criticalLineOddZeroCount_two_mul_lower_bound_of_good_window_measure
#check selberg_odd_zero_proportion_target_of_log_good_window_measure

example (T H : ℝ) (good : Set ℝ) (hH : 0 < H) (hT8H : 8 * H ≤ T)
    (hbad : volume.real (Set.Icc T (2 * T - H) \ good) ≤ T / 12)
    (hsign : ∀ t ∈ good ∩ Set.Icc T (2 * T - 2 * H),
      ∃ u ∈ Set.Ioo t (t + H), HasLocalSignChangeAt hardyZ u) :
    T / (12 * H) ≤ (criticalLineOddZeroCount (2 * T) : ℝ) := by
  exact criticalLineOddZeroCount_two_mul_lower_bound_of_good_window_measure
    T H good hH hT8H hbad hsign

example (A T0 : ℝ) (good : ℝ → Set ℝ) (hA : 0 < A)
    (hbad : ∀ T ≥ T0,
      volume.real
          (Set.Icc T (2 * T - A / Real.log T) \ good T) ≤ T / 12)
    (hsign : ∀ T ≥ T0, ∀ t ∈
      good T ∩ Set.Icc T (2 * T - 2 * (A / Real.log T)),
      ∃ u ∈ Set.Ioo t (t + A / Real.log T),
        HasLocalSignChangeAt hardyZ u) :
    selberg_odd_zero_proportion_target := by
  exact selberg_odd_zero_proportion_target_of_log_good_window_measure
    A T0 good hA hbad hsign

end HardyTheorem
