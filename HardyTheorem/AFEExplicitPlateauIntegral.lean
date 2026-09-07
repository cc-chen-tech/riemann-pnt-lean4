import HardyTheorem.AFEExplicitPlateauCutoff
import MathlibAux.TwoUnitTransitionIntegral

/-! Weighted L1 bounds for the two fixed-width cutoff transitions. -/

open Set MeasureTheory

namespace HardyTheorem.AFE

theorem intervalIntegral_abs_plateauDeriv_mul_rpow_le
    {C₁ x N p : ℝ} (hx : 1 < x) (hxN : x ≤ N) (hp : 0 ≤ p)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁) :
    (∫ u in (x - 1)..(N + 1), |explicitIntervalPlateauDeriv x N u| * u ^ (-p)) ≤
      4 * C₁ * (x - 1) ^ (-p) := by
  have hcont : Continuous (explicitIntervalPlateauDeriv x N) :=
    continuous_iff_continuousAt.mpr fun u =>
      (explicitIntervalPlateauDeriv_hasDerivAt x N u).continuousAt
  have h := MathlibAux.intervalIntegral_abs_mul_rpow_le_two_unit_transitions
    (f := explicitIntervalPlateauDeriv x N) (C := 2 * C₁)
    hx hxN (by positivity) hp hcont.continuousOn
    (fun u _ => abs_explicitIntervalPlateauDeriv_le hC₁0 hC₁ x N u)
    (fun _ hu => explicitIntervalPlateauDeriv_eq_zero_of_mem_Icc hu)
  calc
    _ ≤ 2 * (2 * C₁) * (x - 1) ^ (-p) := h
    _ = 4 * C₁ * (x - 1) ^ (-p) := by ring

theorem intervalIntegral_abs_plateauSecondDeriv_mul_rpow_le
    {C₁ C₂ x N p : ℝ} (hx : 1 < x) (hxN : x ≤ N) (hp : 0 ≤ p)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    (∫ u in (x - 1)..(N + 1), |explicitIntervalPlateauSecondDeriv x N u| * u ^ (-p)) ≤
      2 * (2 * C₂ + 2 * C₁ ^ 2) * (x - 1) ^ (-p) := by
  exact MathlibAux.intervalIntegral_abs_mul_rpow_le_two_unit_transitions
    hx hxN (by positivity) hp
    (explicitIntervalPlateauSecondDeriv_continuous x N).continuousOn
    (fun u _ => abs_explicitIntervalPlateauSecondDeriv_le hC₁0 hC₂0 hC₁ hC₂ x N u)
    (fun _ hu => explicitIntervalPlateauSecondDeriv_eq_zero_of_mem_Icc hu)

end HardyTheorem.AFE
