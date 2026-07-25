import PrimeNumberTheorem.VKEdgePiOverTwoAbelPhase
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMean

open Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

private theorem missingOddHarmonicKernel_periodic_for_gaussian
    (k : ℕ) :
    Function.Periodic (missingOddHarmonicKernel k) (2 * Real.pi) := by
  intro theta
  simp only [missingOddHarmonicKernel]
  rw [Real.cos_add_two_pi]
  rw [show
      (((2 * k + 1 : ℕ) : ℝ) * (theta + 2 * Real.pi)) =
        ((2 * k + 1 : ℕ) : ℝ) * theta +
          (2 * k + 1 : ℕ) * (2 * Real.pi) by
      push_cast
      ring]
  rw [Real.cos_add_nat_mul_two_pi]

private theorem abs_sharpenedPsiAbelKernel_periodic
    (rho : ℂ) {gamma : ℝ} (hgamma : 0 < gamma) (k : ℕ) :
    Function.Periodic
      (fun y => |sharpenedPsiAbelKernel rho gamma k y|)
      (2 * Real.pi / gamma) := by
  let f : ℝ → ℝ := fun theta => |missingOddHarmonicKernel k theta|
  have hfperiodic : Function.Periodic f (2 * Real.pi) := by
    simpa only [f, Function.comp_def] using
      (missingOddHarmonicKernel_periodic_for_gaussian k).comp
        (fun x : ℝ => |x|)
  intro y
  dsimp only [sharpenedPsiAbelKernel]
  have htheta :
      zeroResiduePhase rho -
          gamma * (y + 2 * Real.pi / gamma) =
        (zeroResiduePhase rho - gamma * y) - 2 * Real.pi := by
    field_simp [hgamma.ne']
    ring
  rw [htheta]
  exact hfperiodic.sub_eq _

private theorem abs_sharpenedPsiAbelKernel_continuous
    (rho : ℂ) (gamma : ℝ) (k : ℕ) :
    Continuous
      (fun y => |sharpenedPsiAbelKernel rho gamma k y|) := by
  apply Continuous.abs
  unfold sharpenedPsiAbelKernel missingOddHarmonicKernel
  fun_prop

private theorem periodicMean_abs_sharpenedPsiAbelKernel
    (rho : ℂ) {gamma : ℝ} (hgamma : 0 < gamma) (k : ℕ) :
    periodicMean
        (fun y => |sharpenedPsiAbelKernel rho gamma k y|)
        (2 * Real.pi / gamma) =
      sharpenedMissingHarmonicDenominator k := by
  let q : ℝ → ℝ :=
    fun y => |sharpenedPsiAbelKernel rho gamma k y|
  let T : ℝ := 2 * Real.pi / gamma
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hqPeriodic : Function.Periodic q T := by
    simpa only [q, T] using
      abs_sharpenedPsiAbelKernel_periodic rho hgamma k
  have hqContinuous : Continuous q := by
    simpa only [q] using
      abs_sharpenedPsiAbelKernel_continuous rho gamma k
  have hPeriodicLimit :=
    tendsto_realAbelMean_of_continuous_periodic
      hT hqPeriodic hqContinuous
  have hmeanForm :
      (1 / T) * (∫ y in (0 : ℝ)..T, q y) =
        periodicMean q T := by
    unfold periodicMean
    ring
  rw [hmeanForm] at hPeriodicLimit
  have hAbelLimit :
      Tendsto (realAbelMean q) (𝓝[>] 0)
        (𝓝 (sharpenedMissingHarmonicDenominator k)) := by
    simpa only [q] using
      tendsto_abs_sharpenedPsiAbelKernel
        (rho := rho) (gamma := gamma) (k := k) hgamma
  exact tendsto_nhds_unique hPeriodicLimit hAbelLimit

/--
The Gaussian average of the absolute two-frequency certificate converges
uniformly in its center to the exact denominator strictly below `2 / pi`,
with an explicit `O(m^(-1/2))` rate.
-/
theorem exists_uniform_gaussian_abs_sharpenedPsiAbelKernel_bound
    {rho : ℂ} {gamma : ℝ} {k : ℕ} (hgamma : 0 < gamma) :
    ∃ C ≥ 0, ∀ {m : ℝ}, 1 ≤ m → ∀ c : ℝ,
      |(∫ t : ℝ,
          normalizedGaussian m t *
            |sharpenedPsiAbelKernel rho gamma k (c - t)|) -
          sharpenedMissingHarmonicDenominator k| ≤
        C / Real.sqrt m := by
  let q : ℝ → ℝ :=
    fun y => |sharpenedPsiAbelKernel rho gamma k y|
  let T : ℝ := 2 * Real.pi / gamma
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hqPeriodic : Function.Periodic q T := by
    simpa only [q, T] using
      abs_sharpenedPsiAbelKernel_periodic rho hgamma k
  have hqContinuous : Continuous q := by
    simpa only [q] using
      abs_sharpenedPsiAbelKernel_continuous rho gamma k
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_normalizedGaussian_periodicMean_bound
      hT hqPeriodic hqContinuous
  refine ⟨C, hC, ?_⟩
  intro m hm c
  have hmean :=
    periodicMean_abs_sharpenedPsiAbelKernel rho hgamma k
  simpa only [q, T, hmean] using hbound hm c

theorem eventually_uniform_gaussian_abs_sharpenedPsiAbelKernel
    {rho : ℂ} {gamma : ℝ} {k : ℕ}
    (hgamma : 0 < gamma) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ c : ℝ,
      |(∫ t : ℝ,
          normalizedGaussian m t *
            |sharpenedPsiAbelKernel rho gamma k (c - t)|) -
          sharpenedMissingHarmonicDenominator k| < ε := by
  let q : ℝ → ℝ :=
    fun y => |sharpenedPsiAbelKernel rho gamma k y|
  let T : ℝ := 2 * Real.pi / gamma
  have hT : 0 < T := by
    dsimp only [T]
    positivity
  have hqPeriodic : Function.Periodic q T := by
    simpa only [q, T] using
      abs_sharpenedPsiAbelKernel_periodic rho hgamma k
  have hqContinuous : Continuous q := by
    simpa only [q] using
      abs_sharpenedPsiAbelKernel_continuous rho gamma k
  have hlimit :=
    eventually_uniform_normalizedGaussian_periodicMean
      hT hqPeriodic hqContinuous hε
  have hmean :=
    periodicMean_abs_sharpenedPsiAbelKernel rho hgamma k
  simpa only [q, T, hmean] using hlimit

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
