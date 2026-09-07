import HardyTheorem.ConreyV1Approximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Finite-height transfer from the actual V1 product to the explicit V
product. The two error moments remain actual integrals of the same zeta B;
no mollified mean-value theorem is assumed. -/

open Complex Set MeasureTheory

namespace HardyTheorem

private theorem actual_traces_continuous {L sigma U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hs : 0 < sigma) (hU : 3 ≤ U) :
    let z := fun t : ℝ => (sigma : ℂ) + I * t
    ContinuousOn (fun t => conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma P (z t))
      (Icc U T) ∧
    ContinuousOn (fun t => conreyExplicitV L (z t) * conreyMollifier Y sigma P (z t)) (Icc U T) ∧
    ContinuousOn (fun t => riemannZeta (z t) * conreyMollifier Y sigma P (z t)) (Icc U T) := by
  dsimp only
  have hparam : Continuous (fun t : ℝ => (sigma : ℂ) + I * t) := by fun_prop
  have hs1 : ∀ t ∈ Icc U T, (sigma : ℂ) + I * t ≠ 1 := by
    intro t ht he
    have hi := congrArg Complex.im he
    simp at hi
    linarith [ht.1]
  have hb : Continuous (fun t : ℝ => conreyMollifier Y sigma P ((sigma : ℂ) + I * t)) :=
    (analyticOnNhd_conreyMollifier Y sigma P).continuous.comp hparam
  have hz : ContinuousOn (fun t : ℝ => riemannZeta ((sigma : ℂ) + I * t)) (Icc U T) := by
    intro t ht
    exact ((ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one _ (hs1 t ht)).continuousAt.comp
      (f := fun y : ℝ => (sigma : ℂ) + I * y) hparam.continuousAt).continuousWithinAt
  have hd : ContinuousOn (fun t : ℝ => deriv riemannZeta ((sigma : ℂ) + I * t)) (Icc U T) := by
    intro t ht
    exact ((ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one _ (hs1 t ht)).deriv.continuousAt.comp
      (f := fun y : ℝ => (sigma : ℂ) + I * y) hparam.continuousAt).continuousWithinAt
  have hv1 : ContinuousOn
      (fun t : ℝ => conreyDegreeOneV1 (49 / 100) 0 (51 / 50) L ((sigma : ℂ) + I * t)) (Icc U T) := by
    intro t ht
    exact ((analyticAt_conreyDegreeOneV1_of_re_pos_of_ne_one
      (by simpa using hs) (hs1 t ht)).continuousAt.comp
      (f := fun y : ℝ => (sigma : ℂ) + I * y) hparam.continuousAt).continuousWithinAt
  exact ⟨hv1.mul hb.continuousOn,
    (hz.add (continuousOn_const.mul hd)).mul hb.continuousOn, hz.mul hb.continuousOn⟩

private theorem norm_sq_le_young (u v : ℂ) {epsilon : ℝ} (he : 0 < epsilon) :
    ‖u‖ ^ 2 ≤ (1 + epsilon) * ‖v‖ ^ 2 + (1 + 1 / epsilon) * ‖u - v‖ ^ 2 := by
  have htri : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
    have h := norm_add_le v (u - v)
    rw [show v + (u - v) = u by ring] at h
    exact h
  have hsquare := (sq_le_sq₀ (norm_nonneg u) (by positivity)).mpr htri
  have hy : 2 * ‖v‖ * ‖u - v‖ ≤ epsilon * ‖v‖ ^ 2 + ‖u - v‖ ^ 2 / epsilon := by
    apply (mul_le_mul_iff_left₀ he).mp
    field_simp [he.ne']
    nlinarith only [sq_nonneg (epsilon * ‖v‖ - ‖u - v‖)]
  simp only [div_eq_mul_inv] at hy ⊢
  nlinarith only [hsquare, hy]

/-- Actual finite-height V1 mean square bounded by the V moment and two
same-mollifier zeta moments. All integrability is proved; zeros are allowed.
The splitting height may equal either endpoint. -/
theorem conreyMollifiedV1_meanSquare_le_V_and_zeta
    {L sigma a U T epsilon : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hL : 0 < L) (hs : 0 < sigma) (hsHalf : sigma ≤ 1 / 2)
    (ha : a ≤ 1) (hU : 3 ≤ U) (hUZ : U ≤ Real.exp (a * L))
    (hZT : Real.exp (a * L) ≤ T) (hT : T ≤ Real.exp L) (he : 0 < epsilon) :
    let z := fun t : ℝ => (sigma : ℂ) + I * t
    let B := conreyMollifier Y sigma P
    (∫ t in U..T, ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma P (z t)‖ ^ 2) ≤
      (1 + epsilon) * (∫ t in U..T, ‖conreyExplicitV L (z t) * B (z t)‖ ^ 2) +
      (1 + 1 / epsilon) *
        ((conreyV1ComparisonCoefficient L 0) ^ 2 *
          (∫ t in U..Real.exp (a * L), ‖riemannZeta (z t) * B (z t)‖ ^ 2) +
         (conreyV1ComparisonCoefficient L a) ^ 2 *
          (∫ t in Real.exp (a * L)..T, ‖riemannZeta (z t) * B (z t)‖ ^ 2)) := by
  let z := fun t : ℝ => (sigma : ℂ) + I * t
  let B := conreyMollifier Y sigma P
  let F := fun t : ℝ => conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma P (z t)
  let G := fun t : ℝ => conreyExplicitV L (z t) * B (z t)
  let J := fun t : ℝ => riemannZeta (z t) * B (z t)
  let Z := Real.exp (a * L)
  let D0 := conreyV1ComparisonCoefficient L 0
  let Da := conreyV1ComparisonCoefficient L a
  have hUT : U ≤ T := hUZ.trans hZT
  obtain ⟨hF, hG, hJ⟩ := actual_traces_continuous (L := L) (Y := Y) (P := P) hs hU (T := T)
  change ContinuousOn F (Icc U T) at hF
  change ContinuousOn G (Icc U T) at hG
  change ContinuousOn J (Icc U T) at hJ
  have hE : ContinuousOn (fun t => ‖F t - G t‖ ^ 2) (Icc U T) := (hF.sub hG).norm.pow 2
  have hFI : IntervalIntegrable (fun t => ‖F t‖ ^ 2) volume U T :=
    (hF.norm.pow 2).intervalIntegrable_of_Icc hUT
  have hGI : IntervalIntegrable (fun t => ‖G t‖ ^ 2) volume U T :=
    (hG.norm.pow 2).intervalIntegrable_of_Icc hUT
  have hEI : IntervalIntegrable (fun t => ‖F t - G t‖ ^ 2) volume U T :=
    hE.intervalIntegrable_of_Icc hUT
  have hsubLow : Icc U Z ⊆ Icc U T := by intro t ht; exact ⟨ht.1, ht.2.trans hZT⟩
  have hsubHigh : Icc Z T ⊆ Icc U T := by intro t ht; exact ⟨hUZ.trans ht.1, ht.2⟩
  have hEL : IntervalIntegrable (fun t => ‖F t - G t‖ ^ 2) volume U Z :=
    (hE.mono hsubLow).intervalIntegrable_of_Icc hUZ
  have hEH : IntervalIntegrable (fun t => ‖F t - G t‖ ^ 2) volume Z T :=
    (hE.mono hsubHigh).intervalIntegrable_of_Icc hZT
  have hJL : IntervalIntegrable (fun t => ‖J t‖ ^ 2) volume U Z :=
    ((hJ.mono hsubLow).norm.pow 2).intervalIntegrable_of_Icc hUZ
  have hJH : IntervalIntegrable (fun t => ‖J t‖ ^ 2) volume Z T :=
    ((hJ.mono hsubHigh).norm.pow 2).intervalIntegrable_of_Icc hZT
  have hD0 : 0 ≤ D0 := by dsimp [D0, conreyV1ComparisonCoefficient]; positivity
  have hDa : 0 ≤ Da := by
    dsimp [Da, conreyV1ComparisonCoefficient]
    exact mul_nonneg (by norm_num) (add_nonneg
      (div_nonneg (sub_nonneg.mpr ha) (by norm_num)) (by positivity))
  have hlow : (∫ t in U..Z, ‖F t - G t‖ ^ 2) ≤ D0 ^ 2 * ∫ t in U..Z, ‖J t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hUZ hEL (hJL.const_mul _)
    intro t ht
    have ht3 : 3 ≤ t := hU.trans ht.1
    have hp := norm_conreyMollifiedV1_sub_V_le (Y := Y) (P := P) hL hs hsHalf
      (by norm_num : (0 : ℝ) ≤ 1) ht3 (by simpa using (show (1 : ℝ) ≤ t by linarith))
      (ht.2.trans (hZT.trans hT))
    change ‖F t - G t‖ ≤ D0 * ‖J t‖ at hp
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hD0 (norm_nonneg _))).mpr hp
    simpa only [mul_pow] using hsq
  have hhigh : (∫ t in Z..T, ‖F t - G t‖ ^ 2) ≤ Da ^ 2 * ∫ t in Z..T, ‖J t‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hZT hEH (hJH.const_mul _)
    intro t ht
    have hp := norm_conreyMollifiedV1_sub_V_le (Y := Y) (P := P) hL hs hsHalf ha
      (hU.trans (hUZ.trans ht.1)) ht.1 (ht.2.trans hT)
    change ‖F t - G t‖ ≤ Da * ‖J t‖ at hp
    have hsq := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hDa (norm_nonneg _))).mpr hp
    simpa only [mul_pow] using hsq
  have herr : (∫ t in U..T, ‖F t - G t‖ ^ 2) ≤
      D0 ^ 2 * (∫ t in U..Z, ‖J t‖ ^ 2) + Da ^ 2 * (∫ t in Z..T, ‖J t‖ ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hEL hEH]
    exact add_le_add hlow hhigh
  have hYoung := intervalIntegral.integral_mono_on hUT hFI
    ((hGI.const_mul (1 + epsilon)).add (hEI.const_mul (1 + 1 / epsilon)))
    (fun t _ => norm_sq_le_young (F t) (G t) he)
  rw [intervalIntegral.integral_add (hGI.const_mul _) (hEI.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hYoung
  have herror := mul_le_mul_of_nonneg_left herr
    (by positivity : 0 ≤ 1 + 1 / epsilon)
  change (∫ t in U..T, ‖F t‖ ^ 2) ≤
    (1 + epsilon) * (∫ t in U..T, ‖G t‖ ^ 2) + (1 + 1 / epsilon) *
      (D0 ^ 2 * (∫ t in U..Z, ‖J t‖ ^ 2) + Da ^ 2 * (∫ t in Z..T, ‖J t‖ ^ 2))
  linarith only [hYoung, herror]

end HardyTheorem
