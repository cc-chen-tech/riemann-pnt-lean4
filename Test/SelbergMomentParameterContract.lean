import HardyTheorem.SelbergMomentParameter

open Filter

namespace HardyTheorem

example :
    ∀ᶠ T : ℝ in atTop,
      0 < T ∧
      Real.log T / 64 ≤ Real.log (selbergFirstMomentCutoff T : ℝ) ∧
      (selbergFirstMomentCutoff T : ℝ) ≤ T ^ (1 / 32 : ℝ) :=
  eventually_log_div_sixtyFour_le_log_selbergFirstMomentCutoff

example {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℝ in atTop,
      0 < 1 / T ∧
      1 / T ≤ 1 ∧
      1 / T < Real.pi / 2 ∧
      2 ≤ selbergFirstMomentCutoff T ∧
      Real.exp 1 ≤ (selbergFirstMomentCutoff T : ℝ) ∧
      (selbergFirstMomentCutoff T : ℝ) ≤
        (1 / T) ^ (-(1 / 32 : ℝ)) ∧
      2 ≤ Real.log ((selbergFirstMomentCutoff T : ℝ) ^ a) ∧
      2 ≤ Real.log ((1 / T) ^ (-2 : ℝ)) ∧
      Real.log (1 / (1 / T)) /
          Real.log (selbergFirstMomentCutoff T : ℝ) ≤ 64 ∧
      0 < selbergMomentWindow a T ∧
      selbergMomentWindow a T ≤ T / 2 :=
  eventually_selbergMomentParameter_conditions ha

#print axioms eventually_log_div_sixtyFour_le_log_selbergFirstMomentCutoff
#print axioms eventually_selbergMomentParameter_conditions

end HardyTheorem
