import HardyTheorem.AFEExplicitMellinAmplitude

/-!
# Pointwise bounds for the explicit Mellin amplitude

These bounds retain the two fixed transition-derivative constants and make
all powers of the positive Mellin variable explicit.
-/

noncomputable section

namespace HardyTheorem
namespace AFE

theorem norm_explicitComplexMellinAmplitude_le
    (sigma x N : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖explicitComplexMellinAmplitude sigma x N u‖ ≤ u ^ (-sigma) := by
  have hw0 := explicitIntervalPlateau_nonneg x N u
  have hw1 := explicitIntervalPlateau_le_one x N u
  have hp0 : 0 < u ^ (-sigma) := Real.rpow_pos_of_pos hu _
  rw [explicitComplexMellinAmplitude, Complex.norm_real, Real.norm_eq_abs,
    explicitMellinAmplitude, mellinRpow, abs_mul, abs_of_nonneg hw0,
    abs_of_pos hp0]
  exact mul_le_of_le_one_left hp0.le hw1

theorem norm_explicitComplexMellinAmplitudeDeriv_le
    {C₁ : ℝ} (hC₁0 : 0 ≤ C₁)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (sigma x N : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖explicitComplexMellinAmplitudeDeriv sigma x N u‖ ≤
      2 * C₁ * u ^ (-sigma) + |sigma| * u ^ (-sigma - 1) := by
  have hw0 := explicitIntervalPlateau_nonneg x N u
  have hw1 := explicitIntervalPlateau_le_one x N u
  have hwd := abs_explicitIntervalPlateauDeriv_le hC₁0 hC₁ x N u
  have hp0 : 0 < u ^ (-sigma) := Real.rpow_pos_of_pos hu _
  have hp1 : 0 < u ^ (-sigma - 1) := Real.rpow_pos_of_pos hu _
  rw [explicitComplexMellinAmplitudeDeriv, Complex.norm_real, Real.norm_eq_abs,
    explicitMellinAmplitudeDeriv, mellinRpow, mellinRpowDeriv]
  calc
    |explicitIntervalPlateauDeriv x N u * u ^ (-sigma) +
        explicitIntervalPlateau x N u * ((-sigma) * u ^ (-sigma - 1))|
        ≤ |explicitIntervalPlateauDeriv x N u * u ^ (-sigma)| +
          |explicitIntervalPlateau x N u * ((-sigma) * u ^ (-sigma - 1))| :=
      abs_add_le _ _
    _ = |explicitIntervalPlateauDeriv x N u| * u ^ (-sigma) +
          explicitIntervalPlateau x N u * (|sigma| * u ^ (-sigma - 1)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos hp0, abs_of_nonneg hw0,
        abs_neg, abs_of_pos hp1]
    _ ≤ 2 * C₁ * u ^ (-sigma) +
          1 * (|sigma| * u ^ (-sigma - 1)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hwd hp0.le
      · exact mul_le_mul_of_nonneg_right hw1
          (mul_nonneg (abs_nonneg sigma) hp1.le)
    _ = 2 * C₁ * u ^ (-sigma) + |sigma| * u ^ (-sigma - 1) := by ring

theorem norm_explicitComplexMellinAmplitudeSecondDeriv_le
    {C₁ C₂ : ℝ} (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂)
    (sigma x N : ℝ) {u : ℝ} (hu : 0 < u) :
    ‖explicitComplexMellinAmplitudeSecondDeriv sigma x N u‖ ≤
      (2 * C₂ + 2 * C₁ ^ 2) * u ^ (-sigma) +
      4 * C₁ * |sigma| * u ^ (-sigma - 1) +
      |sigma| * |sigma + 1| * u ^ (-sigma - 2) := by
  have hw0 := explicitIntervalPlateau_nonneg x N u
  have hw1 := explicitIntervalPlateau_le_one x N u
  have hwd := abs_explicitIntervalPlateauDeriv_le hC₁0 hC₁ x N u
  have hwdd := abs_explicitIntervalPlateauSecondDeriv_le
    hC₁0 hC₂0 hC₁ hC₂ x N u
  have hp0 : 0 < u ^ (-sigma) := Real.rpow_pos_of_pos hu _
  have hp1 : 0 < u ^ (-sigma - 1) := Real.rpow_pos_of_pos hu _
  have hp2 : 0 < u ^ (-sigma - 2) := Real.rpow_pos_of_pos hu _
  rw [explicitComplexMellinAmplitudeSecondDeriv, Complex.norm_real,
    Real.norm_eq_abs, explicitMellinAmplitudeSecondDeriv, mellinRpow,
    mellinRpowDeriv, mellinRpowSecondDeriv_eq]
  let a := explicitIntervalPlateauSecondDeriv x N u * u ^ (-sigma)
  let b := 2 * explicitIntervalPlateauDeriv x N u *
    ((-sigma) * u ^ (-sigma - 1))
  let c := explicitIntervalPlateau x N u *
    ((-sigma) * (-sigma - 1) * u ^ (-sigma - 2))
  have habs : |a + b + c| ≤ |a| + |b| + |c| := by
    calc
      |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
      _ ≤ (|a| + |b|) + |c| := by linarith [abs_add_le a b]
      _ = |a| + |b| + |c| := rfl
  change |a + b + c| ≤ _
  calc
    |a + b + c| ≤ |a| + |b| + |c| := habs
    _ = |explicitIntervalPlateauSecondDeriv x N u| * u ^ (-sigma) +
          (2 * |explicitIntervalPlateauDeriv x N u| *
            (|sigma| * u ^ (-sigma - 1))) +
          explicitIntervalPlateau x N u *
            (|sigma| * |sigma + 1| * u ^ (-sigma - 2)) := by
      dsimp only [a, b, c]
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos hp0, abs_of_pos hp1, abs_of_pos hp2,
        abs_of_nonneg hw0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_neg]
      have hs : |-sigma - 1| = |sigma + 1| := by
        rw [show -sigma - 1 = -(sigma + 1) by ring, abs_neg]
      rw [abs_mul, abs_neg, hs]
    _ ≤ (2 * C₂ + 2 * C₁ ^ 2) * u ^ (-sigma) +
          (2 * (2 * C₁) * (|sigma| * u ^ (-sigma - 1))) +
          1 * (|sigma| * |sigma + 1| * u ^ (-sigma - 2)) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right hwdd hp0.le
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hwd (by norm_num : (0 : ℝ) ≤ 2))
            (mul_nonneg (abs_nonneg sigma) hp1.le)
      · exact mul_le_mul_of_nonneg_right hw1
          (mul_nonneg (mul_nonneg (abs_nonneg sigma) (abs_nonneg (sigma + 1)))
            hp2.le)
    _ = (2 * C₂ + 2 * C₁ ^ 2) * u ^ (-sigma) +
          4 * C₁ * |sigma| * u ^ (-sigma - 1) +
          |sigma| * |sigma + 1| * u ^ (-sigma - 2) := by ring

end AFE
end HardyTheorem
