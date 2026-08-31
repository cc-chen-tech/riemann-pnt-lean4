import HardyTheorem.AFEExplicitPoissonSecondIBP
import HardyTheorem.AFEExplicitPoissonGapMajorant
import HardyTheorem.AFEExplicitMellinSecondL1

/-! Cutoff-uniform bounds for nonstationary Fourier--Mellin modes. -/

open Set MeasureTheory

namespace HardyTheorem.AFE

/-- Keep the second amplitude derivative intact; the other terms already
have integrable Mellin decay. -/
theorem norm_explicitPoissonSecondQuotientDerivative_le_supportedGap
    {C₁ sigma x N t g u : ℝ} {k : ℤ}
    (hs : 0 ≤ sigma) (ht : 0 ≤ t) (hu : 0 < u) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hgap : g ≤ |weightedPoissonVelocity t k u|) :
    ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖ ≤
      (1 / g ^ 2) * ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖ +
      (6 * C₁ * t / g ^ 3) * u ^ (-sigma - 2) +
      ((3 * sigma + 2) * t / g ^ 3) * u ^ (-sigma - 3) +
      (3 * t ^ 2 / g ^ 4) * u ^ (-sigma - 4) := by
  have hv0 : weightedPoissonVelocity t k u ≠ 0 :=
    abs_pos.mp (hg.trans_le hgap)
  have hc₁ : |1 / (weightedPoissonVelocity t k u) ^ 2| ≤ 1 / g ^ 2 := by
    simpa only [abs_one] using
      abs_div_pow_le_div_gap_pow 1 (weightedPoissonVelocity t k u) g 2 hg hgap
  have hc₂ : |3 * weightedPoissonVelocityDeriv t u /
      (weightedPoissonVelocity t k u) ^ 3| ≤ 3 * (t / u ^ 2) / g ^ 3 := by
    have h := abs_div_pow_le_div_gap_pow (3 * weightedPoissonVelocityDeriv t u)
      (weightedPoissonVelocity t k u) g 3 hg hgap
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
      abs_weightedPoissonVelocityDeriv ht hu] using h
  have hc₃ : |weightedPoissonVelocitySecondDeriv t u /
      (weightedPoissonVelocity t k u) ^ 3| ≤ (2 * t / u ^ 3) / g ^ 3 := by
    simpa only [abs_weightedPoissonVelocitySecondDeriv ht hu] using
      abs_div_pow_le_div_gap_pow (weightedPoissonVelocitySecondDeriv t u)
        (weightedPoissonVelocity t k u) g 3 hg hgap
  have hc₄ : |3 * (weightedPoissonVelocityDeriv t u) ^ 2 /
      (weightedPoissonVelocity t k u) ^ 4| ≤ 3 * (t / u ^ 2) ^ 2 / g ^ 4 := by
    have h := abs_div_pow_le_div_gap_pow (3 * (weightedPoissonVelocityDeriv t u) ^ 2)
      (weightedPoissonVelocity t k u) g 4 hg hgap
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_pow,
      abs_weightedPoissonVelocityDeriv ht hu] using h
  have hA := norm_explicitComplexMellinAmplitude_le sigma x N hu
  have hA' := norm_explicitComplexMellinAmplitudeDeriv_le hC₁0 hC₁ sigma x N hu
  rw [abs_of_nonneg hs] at hA'
  have hbound : ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖ ≤
      (1 / g ^ 2) * ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖ +
      (3 * (t / u ^ 2) / g ^ 3) *
        (2 * C₁ * u ^ (-sigma) + sigma * u ^ (-sigma - 1)) +
      ((2 * t / u ^ 3) / g ^ 3) * u ^ (-sigma) +
      (3 * (t / u ^ 2) ^ 2 / g ^ 4) * u ^ (-sigma) := by
    refine (norm_explicitPoissonSecondQuotientDerivative_le hv0).trans ?_
    exact add_le_add
      (add_le_add
        (add_le_add (mul_le_mul_of_nonneg_right hc₁ (norm_nonneg _))
          (mul_le_mul hc₂ hA' (norm_nonneg _) (by positivity)))
        (mul_le_mul hc₃ hA (norm_nonneg _) (by positivity)))
      (mul_le_mul hc₄ hA (norm_nonneg _) (by positivity))
  refine hbound.trans_eq ?_
  have hp₁ : u ^ (-sigma - 1) = u ^ (-sigma) / u := by
    simpa using Real.rpow_sub_natCast hu.ne' (-sigma) 1
  have hp₂ : u ^ (-sigma - 2) = u ^ (-sigma) / u ^ 2 := by
    simpa using Real.rpow_sub_natCast hu.ne' (-sigma) 2
  have hp₃ : u ^ (-sigma - 3) = u ^ (-sigma) / u ^ 3 := by
    simpa using Real.rpow_sub_natCast hu.ne' (-sigma) 3
  have hp₄ : u ^ (-sigma - 4) = u ^ (-sigma) / u ^ 4 := by
    simpa using Real.rpow_sub_natCast hu.ne' (-sigma) 4
  rw [hp₁, hp₂, hp₃, hp₄]
  field_simp [hu.ne', hg.ne']
  ring

/-- The nonstationary mode bound is uniform in the upper cutoff. All
integrability and endpoint conditions are derived from the explicit cutoff. -/
theorem norm_explicitPoissonIntegral_le_uniform
    {C₁ C₂ sigma x N t g : ℝ} {k : ℤ}
    (hs : 0 < sigma) (hx : 1 < x) (hxN : x ≤ N) (ht : 0 ≤ t) (hg : 0 < g)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (hgap : ∀ u ∈ Icc (x - 1) (N + 1), g ≤ |weightedPoissonVelocity t k u|) :
    ‖∫ u in (x - 1)..(N + 1), explicitComplexMellinAmplitude sigma x N u *
        Complex.exp (Complex.I * weightedPoissonPhase t k u)‖ ≤
      (1 / g ^ 2) *
        (2 * (2 * C₂ + 2 * C₁ ^ 2) * (x - 1) ^ (-sigma) +
          (8 * sigma * C₁ + sigma) * (x - 1) ^ (-sigma - 1)) +
      (6 * C₁ * t / g ^ 3) * ((x - 1) ^ (-sigma - 1) / (sigma + 1)) +
      ((3 * sigma + 2) * t / g ^ 3) * ((x - 1) ^ (-sigma - 2) / (sigma + 2)) +
      (3 * t ^ 2 / g ^ 4) * ((x - 1) ^ (-sigma - 3) / (sigma + 3)) := by
  have ha : 0 < x - 1 := by linarith
  have hab : x - 1 ≤ N + 1 := by linarith
  have hpos {u : ℝ} (hu : u ∈ Icc (x - 1) (N + 1)) : 0 < u :=
    ha.trans_le hu.1
  have hv {u : ℝ} (hu : u ∈ Icc (x - 1) (N + 1)) :
      weightedPoissonVelocity t k u ≠ 0 :=
    abs_pos.mp (hg.trans_le (hgap u hu))
  have hR : IntervalIntegrable
      (fun u => ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖)
      volume (x - 1) (N + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    exact (explicitPoissonSecondQuotientDerivative_continuousAt
      sigma x N t k (hpos hu).ne' (hv hu)).norm.continuousWithinAt
  have hA : IntervalIntegrable
      (fun u => ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖)
      volume (x - 1) (N + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro u hu
    exact (explicitComplexMellinAmplitudeSecondDeriv_continuousAt
      sigma x N (hpos hu).ne').norm.continuousWithinAt
  have hp (r : ℝ) : IntervalIntegrable (fun u : ℝ => u ^ r)
      volume (x - 1) (N + 1) := MathlibAux.intervalIntegrable_rpow_of_pos ha hab
  have hdom :
      (∫ u in (x - 1)..(N + 1), ‖explicitPoissonSecondQuotientDerivative sigma x N t k u‖) ≤
        ∫ u in (x - 1)..(N + 1),
          (1 / g ^ 2) * ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖ +
          (6 * C₁ * t / g ^ 3) * u ^ (-sigma - 2) +
          ((3 * sigma + 2) * t / g ^ 3) * u ^ (-sigma - 3) +
          (3 * t ^ 2 / g ^ 4) * u ^ (-sigma - 4) := by
    apply intervalIntegral.integral_mono_on hab hR
      ((((hA.const_mul (1 / g ^ 2)).add
        ((hp (-sigma - 2)).const_mul (6 * C₁ * t / g ^ 3))).add
        ((hp (-sigma - 3)).const_mul ((3 * sigma + 2) * t / g ^ 3))).add
        ((hp (-sigma - 4)).const_mul (3 * t ^ 2 / g ^ 4)))
    intro u hu
    exact norm_explicitPoissonSecondQuotientDerivative_le_supportedGap
      hs.le ht (hpos hu) hg hC₁0 hC₁ (hgap u hu)
  rw [intervalIntegral.integral_add
      (((hA.const_mul (1 / g ^ 2)).add
        ((hp (-sigma - 2)).const_mul (6 * C₁ * t / g ^ 3))).add
        ((hp (-sigma - 3)).const_mul ((3 * sigma + 2) * t / g ^ 3)))
      ((hp (-sigma - 4)).const_mul (3 * t ^ 2 / g ^ 4)),
    intervalIntegral.integral_add
      ((hA.const_mul (1 / g ^ 2)).add
        ((hp (-sigma - 2)).const_mul (6 * C₁ * t / g ^ 3)))
      ((hp (-sigma - 3)).const_mul ((3 * sigma + 2) * t / g ^ 3)),
    intervalIntegral.integral_add (hA.const_mul (1 / g ^ 2))
      ((hp (-sigma - 2)).const_mul (6 * C₁ * t / g ^ 3)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hdom
  have hb (j : ℝ) (hj : 1 < j) :
      (∫ u in (x - 1)..(N + 1), u ^ (-sigma - j)) ≤
        (x - 1) ^ (-sigma - (j - 1)) / (sigma + (j - 1)) := by
    have h := MathlibAux.intervalIntegral_rpow_le_left_endpoint
      (r := -sigma - j) ha hab (by linarith)
    simpa only [show -sigma - j + 1 = -sigma - (j - 1) by ring,
      show -(-sigma - j) - 1 = sigma + (j - 1) by ring] using h
  have hb₂ : (∫ u in (x - 1)..(N + 1), u ^ (-sigma - 2)) ≤
      (x - 1) ^ (-sigma - 1) / (sigma + 1) := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using hb 2 (by norm_num)
  have hb₃ : (∫ u in (x - 1)..(N + 1), u ^ (-sigma - 3)) ≤
      (x - 1) ^ (-sigma - 2) / (sigma + 2) := by
    simpa only [show (3 : ℝ) - 1 = 2 by norm_num] using hb 3 (by norm_num)
  have hb₄ : (∫ u in (x - 1)..(N + 1), u ^ (-sigma - 4)) ≤
      (x - 1) ^ (-sigma - 3) / (sigma + 3) := by
    simpa only [show (4 : ℝ) - 1 = 3 by norm_num] using hb 4 (by norm_num)
  refine (norm_explicitPoissonIntegral_le_secondRemainder sigma x N t k hx hxN
    (fun _ hu => hv hu)).trans (hdom.trans ?_)
  exact add_le_add
    (add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_left
          (intervalIntegral_norm_explicitMellinSecondDeriv_le
            hs hx hxN hC₁0 hC₂0 hC₁ hC₂) (by positivity))
        (mul_le_mul_of_nonneg_left hb₂ (by positivity)))
      (mul_le_mul_of_nonneg_left hb₃ (by positivity)))
    (mul_le_mul_of_nonneg_left hb₄ (by positivity))

end HardyTheorem.AFE
