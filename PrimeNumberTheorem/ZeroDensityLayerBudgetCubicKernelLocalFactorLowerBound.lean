import Mathlib.Analysis.Calculus.Deriv.Slope
import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicKernelSecondDifference

open Complex Filter Set Topology

namespace PrimeNumberTheorem

private lemma tendsto_normalized_exp_slope_one :
    Tendsto (fun q : ℂ => (exp q - 1) / q) (𝓝[≠] 0) (𝓝 1) := by
  simpa [div_eq_inv_mul] using (Complex.hasDerivAt_exp 0).tendsto_slope_zero

private lemma tendsto_const_mul_nhdsNE_zero
    {rho : ℂ} (hrho : rho ≠ 0) :
    Tendsto (fun h : ℂ => rho * h) (𝓝[≠] 0) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · simpa using
      ((tendsto_const_nhds.mul tendsto_id).mono_left
        (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left))
  · filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [mem_compl_iff, mem_singleton_iff] at hh ⊢
    exact mul_ne_zero hrho hh

/-- For each fixed nonzero zero frequency, the cubic-kernel de-smoothing
factor tends to one as the logarithmic finite-difference step tends to zero
through nonzero values. -/
theorem tendsto_cubicKernelSecondDifferenceFactor_one
    {rho : ℂ} (hrho : rho ≠ 0) :
    Tendsto (cubicKernelSecondDifferenceFactor rho) (𝓝[≠] 0) (𝓝 1) := by
  have hslope :=
    tendsto_normalized_exp_slope_one.comp (tendsto_const_mul_nhdsNE_zero hrho)
  simpa [cubicKernelSecondDifferenceFactor] using hslope.pow 2

/-- A fixed nonzero zero frequency retains strictly more than half of its
normalized amplitude for all sufficiently small nonzero logarithmic steps. -/
theorem eventually_norm_cubicKernelSecondDifferenceFactor_gt_half
    {rho : ℂ} (hrho : rho ≠ 0) :
    ∀ᶠ h : ℂ in 𝓝[≠] 0,
      (1 / 2 : ℝ) < ‖cubicKernelSecondDifferenceFactor rho h‖ := by
  exact (tendsto_cubicKernelSecondDifferenceFactor_one hrho).norm.eventually
    (Ioi_mem_nhds (by norm_num))

/-- Consequently, the twice de-smoothed cubic zero term retains a strict
`1/2` fraction of the ordinary reciprocal-zero amplitude. -/
theorem eventually_secondLogForwardDifference_exp_div_cube_norm_gt_half
    {rho : ℂ} (u : ℂ) (hrho : rho ≠ 0) :
    ∀ᶠ h : ℂ in 𝓝[≠] 0,
      (1 / 2 : ℝ) * ‖exp (rho * u) / rho‖ <
        ‖secondLogForwardDifference
            (fun v => exp (rho * v) / rho ^ 3) u h / h ^ 2‖ := by
  filter_upwards
      [eventually_norm_cubicKernelSecondDifferenceFactor_gt_half hrho,
        self_mem_nhdsWithin] with h hfactor hh
  have hh0 : h ≠ 0 := by simpa using hh
  rw [secondLogForwardDifference_exp_div_cube_normalized u hrho hh0, norm_mul]
  have hmain : 0 < ‖exp (rho * u) / rho‖ := by
    exact norm_pos_iff.mpr (div_ne_zero (exp_ne_zero _) hrho)
  nlinarith

end PrimeNumberTheorem
