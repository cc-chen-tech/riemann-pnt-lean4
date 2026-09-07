import PrimeNumberTheorem.CarlsonAsymptotic
import PrimeNumberTheorem.CarlsonTwoScaleDetectorGrowth

/-! Uniform squared-logarithmic horizontal bounds for the two-scale
detector.  Only elementary majorant estimates are reused from the old
Carlson module; no zero-density theorem is invoked. -/

open Complex Filter Set

namespace PrimeNumberTheorem.CarlsonZeroDensity

private theorem zeroLogCoefficient_nonneg : 0 ≤ carlsonZeroLogCoefficient := by
  dsimp [carlsonZeroLogCoefficient]
  exact div_nonneg (by norm_num) (Real.log_pos (by norm_num)).le

private theorem horizontalMajorantCoefficient_pos : 0 < carlsonHorizontalMajorantCoefficient := by
  have hk := zeroLogCoefficient_nonneg
  dsimp [carlsonHorizontalMajorantCoefficient, carlsonHorizontalVariationCoefficient]
  positivity

/-- The selected radius contributes only a fixed constant.  The complete
two-scale majorant retains a squared logarithm, with the constants and
all ambient side conditions explicit. -/
theorem twoScale_horizontal_explicitMajorant_le_logSquare
    {C₁ C₂ U S r : ℝ} {Y0 Y1 : ℕ}
    (hC₁ : 1 ≤ C₁) (hC₁U : C₁ ≤ U) (hC₂ : 1 ≤ C₂) (hC₂U : C₂ ≤ U)
    (hY1 : 1 ≤ Y1) (hY1U : (Y1 : ℝ) ≤ U) (hU : 6 ≤ U)
    (hS : 0 ≤ S) (hSU : S + 14 ≤ 4 * U)
    (hr : r ∈ Icc (121 / 32 : ℝ) (122 / 32 : ℝ)) :
    4 * max (regularizedTwoScaleCarlsonFactorLogVariationMajorant C₁ Y0 Y1 S
        (regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 S)) 1 *
        (r + 15 / 4) / (r - 15 / 4) ^ 2 +
      regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 S /
        (1 / (4 * (regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 S + 1))) ≤
      (16 * carlsonHorizontalMajorantCoefficient) * (1 + Real.log U) ^ 2 := by
  let L := 1 + Real.log (4 * (U + 5 / 4) * U)
  let Z := regularizedTwoScaleCarlsonFactorZeroLogMajorant C₂ Y0 Y1 S
  let V := regularizedTwoScaleCarlsonFactorLogVariationMajorant C₁ Y0 Y1 S Z
  have hQ : (1 : ℝ) ≤ 4 * (U + 5 / 4) * U := by nlinarith [sq_nonneg U]
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hQ]
  have hL0 : 0 ≤ L := by linarith
  have hk := zeroLogCoefficient_nonneg
  have hv : 0 ≤ carlsonHorizontalVariationCoefficient := by
    dsimp [carlsonHorizontalVariationCoefficient]
    positivity
  have hzOld := regularizedCarlsonFactorZeroLogMajorant_bounds
    hC₂ hC₂U hY1 hY1U hU hS hSU
  have hZ0 : 0 ≤ Z := hzOld.1
  have hZ : Z ≤ carlsonZeroLogCoefficient * L := hzOld.2
  have hZsq : Z ^ 2 ≤ (carlsonZeroLogCoefficient * L) ^ 2 :=
    (sq_le_sq₀ hZ0 (mul_nonneg hk hL0)).2 hZ
  have hV : V ≤ carlsonHorizontalVariationCoefficient * L ^ 2 :=
    regularizedCarlsonFactorLogVariationMajorant_le_ambientSquare
      hC₁ hC₁U hC₂ hC₂U hY1 hY1U hU hS hSU
  have hmax : max V 1 ≤ (carlsonHorizontalVariationCoefficient + 1) * L ^ 2 := by
    apply max_le
    · nlinarith [sq_nonneg L]
    · nlinarith [sq_nonneg L, mul_nonneg hv (sq_nonneg L)]
  have hZrational : Z / (1 / (4 * (Z + 1))) ≤
      4 * carlsonZeroLogCoefficient * (carlsonZeroLogCoefficient + 1) * L ^ 2 := by
    have heq : Z / (1 / (4 * (Z + 1))) = 4 * Z * (Z + 1) := by field_simp
    rw [heq]
    have hKL : carlsonZeroLogCoefficient * L ≤ carlsonZeroLogCoefficient * L ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg L]) hk
    nlinarith [sq_nonneg carlsonZeroLogCoefficient]
  have hgeom : 4 * max V 1 * (r + 15 / 4) / (r - 15 / 4) ^ 2 ≤
      4 * max V 1 * 7744 := by
    calc
      _ = (4 * max V 1) * ((r + 15 / 4) / (r - 15 / 4) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (regularizedCarlsonFactorGeometry_le hr)
        (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_right _ _)))
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmax (by norm_num : (0 : ℝ) ≤ 4))
    (by norm_num : (0 : ℝ) ≤ 7744)
  have hsquare : 4 * max V 1 * (r + 15 / 4) / (r - 15 / 4) ^ 2 +
      Z / (1 / (4 * (Z + 1))) ≤ carlsonHorizontalMajorantCoefficient * L ^ 2 := by
    dsimp [carlsonHorizontalMajorantCoefficient]
    linarith
  have hU0 : 0 < U := by linarith
  have harg : 4 * (U + 5 / 4) * U ≤ U ^ 4 := by
    have hU2 : 8 ≤ U ^ 2 := by nlinarith [sq_nonneg U]
    have hprod := mul_nonneg (sub_nonneg.mpr hU2) (sq_nonneg U)
    nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < 4 * (U + 5 / 4) * U) harg
  rw [Real.log_pow] at hlog
  have hLupper : L ≤ 4 * (1 + Real.log U) := by dsimp [L]; norm_num at hlog; linarith
  have hLsq : L ^ 2 ≤ 16 * (1 + Real.log U) ^ 2 := by
    have h := pow_le_pow_left₀ hL0 hLupper 2
    nlinarith
  calc
    _ ≤ carlsonHorizontalMajorantCoefficient * L ^ 2 := hsquare
    _ ≤ carlsonHorizontalMajorantCoefficient * (16 * (1 + Real.log U) ^ 2) :=
      mul_le_mul_of_nonneg_left hLsq horizontalMajorantCoefficient_pos.le
    _ = _ := by ring

/-- The fixed constants and ambient threshold precede both integer
cutoffs, the horizontal window, and the left endpoint of the segment. -/
theorem exists_eventually_twoScale_horizontal_logDeriv_le_logSquare :
    ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
      ∀ {Y0 Y1 : ℕ}, 2 ≤ Y0 → Y0 < Y1 → (Y1 : ℝ) ≤ U →
        ∀ {sigma S : ℝ}, 1 / 2 < sigma → 5 ≤ S → S + 14 ≤ 4 * U →
          ∃ t ∈ Icc S (S + 1),
            (∀ x ∈ Icc sigma 4,
              regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + (t : ℂ) * I) ≠ 0) ∧
            ∀ x ∈ Icc sigma 4,
              ‖logDeriv (regularizedTwoScaleCarlsonZeroDetector Y0 Y1) ((x : ℂ) + (t : ℂ) * I)‖ ≤
                K * (1 + Real.log U) ^ 2 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hselect⟩ :=
    exists_regularizedTwoScaleCarlson_horizontal_logDeriv_le_logPolynomial
  refine ⟨16 * carlsonHorizontalMajorantCoefficient,
    mul_pos (by norm_num) horizontalMajorantCoefficient_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (6 : ℝ), eventually_ge_atTop C₁,
    eventually_ge_atTop C₂] with U hU hC₁U hC₂U
  intro Y0 Y1 hY0 hY01 hY1U sigma S hsigma hS hSU
  obtain ⟨r, hr, t, ht, hne, hbound⟩ := hselect hY0 hY01 hsigma hS
  refine ⟨t, ht, hne, ?_⟩
  intro x hx
  exact (hbound x hx).trans (twoScale_horizontal_explicitMajorant_le_logSquare
    hC₁ hC₁U hC₂ hC₂U (by omega) hY1U hU (by linarith) hSU hr)

end PrimeNumberTheorem.CarlsonZeroDensity
