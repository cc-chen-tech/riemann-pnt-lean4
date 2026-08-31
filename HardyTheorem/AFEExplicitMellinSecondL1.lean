import HardyTheorem.AFEExplicitMellinAmplitude
import HardyTheorem.AFEExplicitPlateauIntegral

/-! A cutoff-uniform L1 bound for the second Mellin-amplitude derivative. -/

open Set MeasureTheory

namespace HardyTheorem.AFE

/-- Retain the actual cutoff derivatives, rather than replacing them by
constants across the whole interval. -/
theorem norm_explicitMellinSecondDeriv_le_supported
    {sigma x N u : ℝ} (hs : 0 ≤ sigma) (hu : 0 < u) :
    ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖ ≤
      |explicitIntervalPlateauSecondDeriv x N u| * u ^ (-sigma) +
      2 * sigma * (|explicitIntervalPlateauDeriv x N u| * u ^ (-sigma - 1)) +
      sigma * (sigma + 1) * u ^ (-sigma - 2) := by
  have hw0 := explicitIntervalPlateau_nonneg x N u
  have hw1 := explicitIntervalPlateau_le_one x N u
  have hs1 : 0 ≤ sigma + 1 := by linarith
  have habspow (r : ℝ) : |u ^ r| = u ^ r :=
    abs_of_nonneg (Real.rpow_nonneg hu.le r)
  have hp2 : 0 < u ^ (-sigma - 2) := Real.rpow_pos_of_pos hu _
  rw [explicitComplexMellinAmplitudeSecondDeriv, Complex.norm_real,
    Real.norm_eq_abs, explicitMellinAmplitudeSecondDeriv, mellinRpow,
    mellinRpowDeriv, mellinRpowSecondDeriv_eq]
  let a := explicitIntervalPlateauSecondDeriv x N u * u ^ (-sigma)
  let b := 2 * explicitIntervalPlateauDeriv x N u * ((-sigma) * u ^ (-sigma - 1))
  let c := explicitIntervalPlateau x N u *
    ((-sigma) * (-sigma - 1) * u ^ (-sigma - 2))
  change |a + b + c| ≤ _
  calc
    |a + b + c| ≤ |a| + |b| + |c| := by
      linarith [abs_add_le (a + b) c, abs_add_le a b]
    _ = |explicitIntervalPlateauSecondDeriv x N u| * u ^ (-sigma) +
          2 * sigma * (|explicitIntervalPlateauDeriv x N u| * u ^ (-sigma - 1)) +
          explicitIntervalPlateau x N u * (sigma * (sigma + 1) * u ^ (-sigma - 2)) := by
      dsimp only [a, b, c]
      simp only [show -sigma - 1 = -(sigma + 1) by ring, abs_mul, abs_neg,
        abs_of_nonneg hs, abs_of_nonneg hs1, abs_of_nonneg hw0,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        habspow]
      ring
    _ ≤ _ := by
      have hlast := mul_le_mul_of_nonneg_right hw1
        (mul_nonneg (mul_nonneg hs hs1) hp2.le)
      linarith

/-- Uniform in the upper cutoff `N`.  The first two summands use only the
two unit transitions; the pure Mellin second derivative has an integrable
tail because `sigma > 0`. -/
theorem intervalIntegral_norm_explicitMellinSecondDeriv_le
    {C₁ C₂ sigma x N : ℝ} (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    (∫ u in (x - 1)..(N + 1), ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖) ≤
      2 * (2 * C₂ + 2 * C₁ ^ 2) * (x - 1) ^ (-sigma) +
      (8 * sigma * C₁ + sigma) * (x - 1) ^ (-sigma - 1) := by
  have ha : 0 < x - 1 := by linarith
  have hab : x - 1 ≤ N + 1 := by linarith
  have hpos {u : ℝ} (hu : u ∈ Icc (x - 1) (N + 1)) : 0 < u :=
    ha.trans_le hu.1
  have hpow (r : ℝ) : ContinuousOn (fun u : ℝ => u ^ r) (Icc (x - 1) (N + 1)) := by
    intro u hu
    exact (Real.continuousAt_rpow_const u r (Or.inl (hpos hu).ne')).continuousWithinAt
  let G₂ : ℝ → ℝ := fun u => |explicitIntervalPlateauSecondDeriv x N u| * u ^ (-sigma)
  let G₁ : ℝ → ℝ := fun u => |explicitIntervalPlateauDeriv x N u| * u ^ (-sigma - 1)
  let G₀ : ℝ → ℝ := fun u => u ^ (-sigma - 2)
  have hwd : ContinuousOn (explicitIntervalPlateauDeriv x N) (Icc (x - 1) (N + 1)) :=
    fun u _ => (explicitIntervalPlateauDeriv_hasDerivAt x N u).continuousAt.continuousWithinAt
  have hG₂ : IntervalIntegrable G₂ volume (x - 1) (N + 1) :=
    (((explicitIntervalPlateauSecondDeriv_continuous x N).continuousOn.abs).mul
      (hpow (-sigma))).intervalIntegrable_of_Icc hab
  have hG₁ : IntervalIntegrable G₁ volume (x - 1) (N + 1) :=
    (hwd.abs.mul (hpow (-sigma - 1))).intervalIntegrable_of_Icc hab
  have hG₀ : IntervalIntegrable G₀ volume (x - 1) (N + 1) :=
    (hpow (-sigma - 2)).intervalIntegrable_of_Icc hab
  have hA : IntervalIntegrable
      (fun u => ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖)
      volume (x - 1) (N + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    exact (explicitComplexMellinAmplitudeSecondDeriv_continuousAt
      sigma x N (hpos hu).ne').norm.continuousWithinAt
  have hdom :
      (∫ u in (x - 1)..(N + 1), ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖) ≤
        ∫ u in (x - 1)..(N + 1), G₂ u + 2 * sigma * G₁ u + sigma * (sigma + 1) * G₀ u := by
    apply intervalIntegral.integral_mono_on hab hA
      ((hG₂.add (hG₁.const_mul (2 * sigma))).add (hG₀.const_mul (sigma * (sigma + 1))))
    intro u hu
    exact norm_explicitMellinSecondDeriv_le_supported hs.le (hpos hu)
  rw [intervalIntegral.integral_add (hG₂.add (hG₁.const_mul (2 * sigma)))
      (hG₀.const_mul (sigma * (sigma + 1))),
    intervalIntegral.integral_add hG₂ (hG₁.const_mul (2 * sigma)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hdom
  have hb₂ : (∫ u in (x - 1)..(N + 1), G₂ u) ≤
      2 * (2 * C₂ + 2 * C₁ ^ 2) * (x - 1) ^ (-sigma) :=
    intervalIntegral_abs_plateauSecondDeriv_mul_rpow_le hx hxN hs.le hC₁0 hC₂0 hC₁ hC₂
  have hb₁ : (∫ u in (x - 1)..(N + 1), G₁ u) ≤
      4 * C₁ * (x - 1) ^ (-sigma - 1) := by
    have h := intervalIntegral_abs_plateauDeriv_mul_rpow_le
      (p := sigma + 1) hx hxN (by linarith) hC₁0 hC₁
    simpa only [show -(sigma + 1) = -sigma - 1 by ring] using h
  have hb₀ : (∫ u in (x - 1)..(N + 1), G₀ u) ≤
      (x - 1) ^ (-sigma - 1) / (sigma + 1) := by
    have h := MathlibAux.intervalIntegral_rpow_le_left_endpoint
      (r := -sigma - 2) ha hab (by linarith)
    simpa only [show -sigma - 2 + 1 = -sigma - 1 by ring,
      show -(-sigma - 2) - 1 = sigma + 1 by ring] using h
  refine hdom.trans ((add_le_add
    (add_le_add hb₂ (mul_le_mul_of_nonneg_left hb₁ (by positivity)))
    (mul_le_mul_of_nonneg_left hb₀ (by positivity))).trans_eq ?_)
  field_simp [show sigma + 1 ≠ 0 by linarith]
  ring

end HardyTheorem.AFE
