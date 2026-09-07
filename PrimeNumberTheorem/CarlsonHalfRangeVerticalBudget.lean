import PrimeNumberTheorem.CarlsonHalfRangeLeftEdge
import PrimeNumberTheorem.CarlsonTwoScaleRegularizedEdges

/-! The complete regularized vertical boundary budget on an actually
selected left line.  No moment or contour-selection premise remains. -/

open Complex Filter MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

/-- The left line, its positive zero-count weight, both vertical
nonvanishing assertions, and the uniform budget for every inner height
interval are obtained from the proved half-range moments. -/
theorem exists_eventually_halfRange_selectedVerticalBudget :
    ∃ K > (0 : ℝ), ∀ᶠ V : ℝ in atTop,
      let G := regularizedTwoScaleCarlsonZeroDetector (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
      ∃ x ∈ Ioo halfRangeAuxiliaryLeft halfRangeAuxiliaryRight,
        (1 / 20000 : ℝ) ≤ 2 / 3 - x ∧
        (∀ t ∈ Icc (2 * V) (5 * V / 2), G ((x : ℂ) + I * (t : ℂ)) ≠ 0) ∧
        (∀ t : ℝ, G ((4 : ℂ) + I * (t : ℂ)) ≠ 0) ∧
        ∀ u v : ℝ, 2 * V ≤ u → v ≤ 5 * V / 2 → u ≤ v →
          (4 - x) * (∫ t in u..v, (logDeriv G ((4 : ℂ) + I * (t : ℂ))).re) +
            (∫ t in u..v, Real.log ‖G ((x : ℂ) + I * (t : ℂ))‖) -
            (∫ t in u..v, Real.log ‖G ((4 : ℂ) + I * (t : ℂ))‖) ≤
            K * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 := by
  obtain ⟨K, hK, hleft⟩ := exists_eventually_halfRange_selectedLeftEdge_logIntegral_le
  refine ⟨K + 400 + 12 * Real.pi, by positivity, ?_⟩
  filter_upwards [hleft, eventually_halfRange_rightLogIntegral_le,
    eventually_halfRangeCutoff_conditions] with V hleft hright hparams
  obtain ⟨hV, hY0, hY01, _⟩ := hparams
  obtain ⟨x, hx, hweight, hleftNe, hleftLog⟩ := hleft
  have hxHalf : 1 / 2 < x := by
    have h := hx.1
    norm_num [halfRangeAuxiliaryLeft] at h
    linarith
  have hxOne : x < 1 := by
    have h := hx.2
    norm_num [halfRangeAuxiliaryRight] at h
    linarith
  have hx0 : 0 < x := by linarith
  let Y0 := halfRangeCoreCutoff V
  let Y1 := halfRangeOuterCutoff V
  let G := regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  have hregNe {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
      (hne : twoScaleCarlsonZeroDetector Y0 Y1 s ≠ 0) : G s ≠ 0 := by
    dsimp [G]
    rw [regularizedTwoScaleCarlsonZeroDetector_eq_sub_one_sq_mul hs0 hs1]
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hs1)) hne
  have hleftReg : ∀ t ∈ Icc (2 * V) (5 * V / 2), G ((x : ℂ) + I * (t : ℂ)) ≠ 0 := by
    intro t ht
    apply hregNe ?_ ?_ (hleftNe t ht)
    · intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
    · intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      linarith
  have hrightReg : ∀ t : ℝ, G ((4 : ℂ) + I * (t : ℂ)) ≠ 0 := by
    intro t
    apply hregNe ?_ ?_ ?_
    · intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
    · intro heq
      have hre := congrArg Complex.re heq
      norm_num at hre
    · intro hzero
      have hre := eight_ninths_le_re_twoScaleCarlsonZeroDetector hY0 hY01
        (s := (4 : ℂ) + I * (t : ℂ)) (by simp)
      rw [hzero, Complex.zero_re] at hre
      norm_num at hre
  refine ⟨x, hx, hweight, hleftReg, hrightReg, ?_⟩
  intro u v hu hv huv
  have hne : ∀ t ∈ Icc u v, twoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0 :=
    fun t ht => hleftNe t ⟨hu.trans ht.1, ht.2.trans hv⟩
  have hdiff := integral_regularizedTwoScale_verticalLogDifference_le hY0 hY01 hxHalf hxOne huv hne
  have hl := (hleftLog u v hu hv huv).2
  have hr := (hright u v hu hv huv).2
  have harg := (integral_regularizedTwoScale_rightArgument_bound hY0 hY01 u v).2
  have hargUpper : (∫ t in u..v, (logDeriv G ((4 : ℂ) + I * (t : ℂ))).re) ≤ 3 * Real.pi :=
    (le_abs_self _).trans harg
  have hargWeighted : (4 - x) *
      (∫ t in u..v, (logDeriv G ((4 : ℂ) + I * (t : ℂ))).re) ≤ 12 * Real.pi := by
    calc
      _ ≤ (4 - x) * (3 * Real.pi) :=
        mul_le_mul_of_nonneg_left hargUpper (by linarith)
      _ ≤ _ := by nlinarith [Real.pi_pos]
  let W := V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6
  have hW : 1 ≤ W := by
    have hpower : 1 ≤ V ^ halfRangeTargetExponent :=
      Real.one_le_rpow hV.le (by norm_num [halfRangeTargetExponent])
    have hlog : 1 ≤ (1 + Real.log V) ^ 6 := one_le_pow₀ (by linarith [Real.log_nonneg hV.le])
    exact one_le_mul_of_one_le_of_one_le hpower hlog
  have hdecay : V ^ (-7 / 5 : ℝ) ≤ W :=
    (Real.rpow_le_one_of_one_le_of_nonpos hV.le (by norm_num)).trans hW
  have hdiffBound :
      (∫ t in u..v, Real.log ‖G ((x : ℂ) + I * (t : ℂ))‖) -
        (∫ t in u..v, Real.log ‖G ((4 : ℂ) + I * (t : ℂ))‖) ≤ K * W + 400 * W := by
    dsimp [G, Y0, Y1] at hdiff ⊢
    dsimp [W] at hdecay ⊢
    nlinarith
  have hconstant : 12 * Real.pi ≤ 12 * Real.pi * W :=
    le_mul_of_one_le_right (by positivity) hW
  change _ ≤ (K + 400 + 12 * Real.pi) * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6
  rw [mul_assoc]
  change _ ≤ (K + 400 + 12 * Real.pi) * W
  linarith

end PrimeNumberTheorem.CarlsonZeroDensity
