import HardyTheorem.AFEExplicitPoissonCutoffLimit
import HardyTheorem.AFEExplicitPoissonHeightScale
import HardyTheorem.AFECriticalUnitPhaseLog

/-! Unconditional logarithmic unit-phase AFE from the proved Poisson/Gamma
transformation.  No analytic target is assumed by these theorems. -/

open Complex

namespace HardyTheorem.AFE

private theorem finiteConstant_nonneg {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    0 ≤ explicitPoissonCriticalFiniteConstant C₁ C₂ := by
  unfold explicitPoissonCriticalFiniteConstant explicitPoissonFarConstant
  positivity

/-- Explicit dependence on the two (already proved to exist) uniform
derivative bounds of the fixed smooth cutoff. -/
theorem exists_zeta_critical_unitPhase_logAfe_of_cutoff_bounds
    {C₁ C₂ t : ℝ} (ht : 72 * Real.pi ≤ t)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
    (hC₁ : ∀ z : ℝ, |deriv Real.smoothTransition z| ≤ C₁)
    (hC₂ : ∀ z : ℝ, |deriv (deriv Real.smoothTransition) z| ≤ C₂) :
    ∃ phase remainder : ℂ, ‖phase‖ = 1 ∧
      riemannZeta ((1 / 2 : ℂ) + I * t) =
        criticalAfeMainSum t + phase * criticalAfeDualSum t + remainder ∧
      ‖remainder‖ ≤ (2 * explicitPoissonCriticalFiniteConstant C₁ C₂ + 1) *
        t ^ (-1 / 4 : ℝ) * (1 + Real.log t) := by
  let s : ℂ := (1 / 2 : ℂ) + I * t
  let K := criticalAfeCutoff t
  let M := Nat.ceil (t / (Real.pi * K))
  let C := explicitPoissonCriticalFiniteConstant C₁ C₂
  let G : ℂ := ∑ m ∈ Finset.Icc 1 K, poissonGammaTerm (1 / 2) t m
  obtain ⟨hK, htL, htU⟩ := natFloor_sqrt_heightCell ht
  have hK' : 6 ≤ K := hK
  obtain ⟨ht1, hscale, hlog, hphaseScale⟩ := sqrt_heightCell_logAfe_scales hK' htL htU.le
  have hC0 : 0 ≤ C := finiteConstant_nonneg hC₁0 hC₂0
  have ht0 : 0 < t := by linarith
  have hLt1 : 1 ≤ 1 + Real.log t := by linarith [Real.log_nonneg ht1]
  have hmain : criticalAfeMainSum t = ∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s) := by
    simpa only [s, K, one_div, ← Complex.cpow_neg] using criticalAfeMainSum_eq_Icc t
  have hdual : criticalAfeDualSum t = ∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (s - 1) := by
    rw [criticalAfeDualSum_eq_Icc]
    apply Finset.sum_congr rfl
    intro n _
    rw [one_div, ← Complex.cpow_neg]
    congr 1
    dsimp only [s]
    ring
  obtain ⟨phase, hphase, hphaseAll⟩ := exists_unitPhase_criticalGammaFrequency_sums t
  have hphaseK : ‖G - phase * criticalAfeDualSum t‖ ≤
      2 * Real.sqrt K * Real.exp (-2 * Real.pi * t) := by
    rw [hdual]
    simpa only [G, poissonGammaTerm_critical_eq] using hphaseAll K
  have hz : ‖riemannZeta s - criticalAfeMainSum t - G‖ ≤
      C * (K : ℝ) ^ (-(1 / 2) : ℝ) * (1 + Real.log M) := by
    rw [hmain]
    exact norm_riemannZeta_sub_primal_sub_dualGamma_le hK' htL htU.le hC₁0 hC₂0 hC₁ hC₂
  have hzScaled : C * (K : ℝ) ^ (-(1 / 2) : ℝ) * (1 + Real.log M) ≤
      C * (2 * t ^ (-1 / 4 : ℝ)) * (1 + Real.log t) := by
    calc
      _ ≤ C * (K : ℝ) ^ (-(1 / 2) : ℝ) * (1 + Real.log t) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hscale hC0) (by linarith)
  have hphaseScaled : ‖G - phase * criticalAfeDualSum t‖ ≤
      t ^ (-1 / 4 : ℝ) * (1 + Real.log t) :=
    (hphaseK.trans hphaseScale).trans
      (le_mul_of_one_le_right (by positivity) hLt1)
  let E := riemannZeta s - criticalAfeMainSum t - phase * criticalAfeDualSum t
  refine ⟨phase, E, hphase, ?_, ?_⟩
  · dsimp only [E, s]
    ring
  · have hid : E = (riemannZeta s - criticalAfeMainSum t - G) +
        (G - phase * criticalAfeDualSum t) := by dsimp only [E]; ring
    rw [hid]
    exact ((norm_add_le _ _).trans (add_le_add (hz.trans hzScaled) hphaseScaled)).trans_eq
      (by dsimp only [C]; ring)

/-- All analytic ingredients are discharged.  The same remainder constant
works for every height above the explicit threshold. -/
theorem exists_zeta_critical_unitPhase_logAfe_fixed_threshold :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℝ, 72 * Real.pi ≤ t →
      ∃ phase remainder : ℂ, ‖phase‖ = 1 ∧
        riemannZeta ((1 / 2 : ℂ) + I * t) =
          criticalAfeMainSum t + phase * criticalAfeDualSum t + remainder ∧
        ‖remainder‖ ≤ R * t ^ (-1 / 4 : ℝ) * (1 + Real.log t) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_uniform_smoothTransition_deriv_bound
  obtain ⟨C₂, hC₂0, hC₂⟩ := exists_uniform_smoothTransition_secondDeriv_bound
  refine ⟨2 * explicitPoissonCriticalFiniteConstant C₁ C₂ + 1, ?_, ?_⟩
  · linarith [finiteConstant_nonneg hC₁0 hC₂0]
  · intro t ht
    exact exists_zeta_critical_unitPhase_logAfe_of_cutoff_bounds ht hC₁0 hC₂0 hC₁ hC₂

/-- The previously conditional target now holds without an AFE premise. -/
theorem zeta_critical_unitPhase_logAfe : zeta_critical_unitPhase_logAfe_target := by
  obtain ⟨R, hR, hAFE⟩ := exists_zeta_critical_unitPhase_logAfe_fixed_threshold
  exact ⟨R, 72 * Real.pi, hR, by linarith [Real.pi_gt_three], hAFE⟩

end HardyTheorem.AFE
