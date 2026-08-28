import HardyTheorem.AFECriticalUnitPhaseLogRemainder
import HardyTheorem.AFECriticalDyadicProductWindow

/-!
# Critical AFE Gaussian window with unit phase and logarithmic remainder

This is the downstream Carlson estimate required from the weaker
Titchmarsh-style AFE.  The existential phase is eliminated pointwise before
integration, so no measurable choice of phase or remainder is needed.
-/

open Complex MeasureTheory Set

namespace HardyTheorem
namespace AFE

private theorem continuous_normSq_criticalAfeProduct_unitPhaseLog
    (X : ℕ) :
    Continuous fun t : ℝ =>
      Complex.normSq
        (riemannZeta ((1 / 2 : ℂ) + I * t) *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) := by
  let line : ℝ → ℂ := fun t => (1 / 2 : ℂ) + I * t
  have hline : Continuous line := by
    dsimp only [line]
    fun_prop
  have hzeta : Continuous fun t : ℝ => riemannZeta (line t) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hline_ne : line t ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num [line] at hre
    exact (differentiableAt_riemannZeta hline_ne).continuousAt.comp
      hline.continuousAt
  have hmoll : Continuous fun t : ℝ =>
      selbergMoebiusMollifier X (line t) := by
    simpa only [line, selbergMoebiusMollifier] using
      continuous_selbergMollifier_criticalLine X
        (fun n => (selbergMoebiusCoeff X n : ℂ))
  exact Complex.continuous_normSq.comp (hzeta.mul hmoll)

/-- The full central Gaussian window estimate under the logarithmic,
unit-phase AFE target.  The target threshold is returned explicitly and the
only remainder cost is `criticalAfeLogRemainderWindowBound`. -/
theorem setIntegral_gaussian_normSq_criticalAfeProduct_le_of_unitPhase_log_target
    (hAFE : zeta_critical_unitPhase_logAfe_target) :
    ∃ R T0 : ℝ, 0 < R ∧ 1 ≤ T0 ∧
      ∀ {K X : ℕ} {L U Delta : ℝ},
        T0 ≤ L → 1 < L → 2 ≤ X →
        Real.sqrt (U / (2 * Real.pi)) < (((2 ^ K : ℕ) : ℝ)) →
        2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta →
        ∀ w : ℝ,
        (∫ t : ℝ in Icc L U,
          Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
            Complex.normSq
              (riemannZeta ((1 / 2 : ℂ) + I * t) *
                selbergMoebiusMollifier X
                  ((1 / 2 : ℂ) + I * t))) ≤
          3 *
            (2 * dyadicCriticalGaussianBound K X Delta +
              Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                criticalAfeLogRemainderWindowBound R L U X) := by
  rcases hAFE with ⟨R, T0, hR, hT0, hAFEpoint⟩
  refine ⟨R, T0, hR, hT0, ?_⟩
  intro K X L U Delta hT0L hL hX hU hDelta w
  let weight : ℝ → ℝ := fun t =>
    Real.exp (-((t - w) ^ 2) / Delta ^ 2)
  let mainEnergy : ℝ → ℝ := fun t =>
    Complex.normSq
      (dyadicClampedCriticalPrefixMollifiedPolynomial K X t)
  let actual : ℝ → ℝ := fun t =>
    Complex.normSq
      (riemannZeta ((1 / 2 : ℂ) + I * t) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))
  let Krem : ℝ := criticalAfeLogRemainderWindowBound R L U X
  have hDeltaPos : 0 < Delta := by
    have hpositive : 0 < ((2 ^ K * X : ℕ) : ℝ) := by positivity
    linarith
  have hweightInt : Integrable weight := by
    simpa only [weight] using integrable_criticalAfeGaussianWeight hDeltaPos w
  have hmainInt : Integrable fun t : ℝ => weight t * mainEnergy t := by
    simpa only [weight, mainEnergy] using
      integrable_gaussian_normSq_dyadicClampedCriticalPrefix hX hDelta w
  have hKrem : 0 ≤ Krem := by
    dsimp only [Krem, criticalAfeLogRemainderWindowBound]
    positivity
  have hsumInt : Integrable fun t : ℝ =>
      2 * (weight t * mainEnergy t) + Krem * weight t :=
    (hmainInt.const_mul 2).add (hweightInt.const_mul Krem)
  have hrightInt : Integrable fun t : ℝ =>
      weight t * (3 * (2 * mainEnergy t + Krem)) := by
    convert hsumInt.const_mul 3 using 1
    funext t
    ring
  have hactualCont : Continuous fun t : ℝ => weight t * actual t := by
    apply Continuous.mul
    · dsimp only [weight]
      fun_prop
    · dsimp only [actual]
      exact continuous_normSq_criticalAfeProduct_unitPhaseLog X
  have hactualInt : IntegrableOn
      (fun t : ℝ => weight t * actual t) (Icc L U) :=
    hactualCont.continuousOn.integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Icc L U) :
      weight t * actual t ≤
        weight t * (3 * (2 * mainEnergy t + Krem)) := by
    have htTarget : T0 ≤ t := hT0L.trans ht.1
    obtain ⟨phase, remainder, hphase, hdecomp, hremPoint⟩ :=
      hAFEpoint t htTarget
    have hcutoff := criticalAfeCutoff_succ_le_pow_of_mem_Icc ht hU
    have hmain := criticalAfeMainSum_mul_mollifier_eq_dyadicClampedPrefix
      (K := K) (X := X) hcutoff
    have hrem :=
      normSq_unitPhaseLogAfeRemainder_product_le_windowBound
        hR hL ht hX hremPoint
    have hbase := normSq_criticalUnitPhaseAfeProduct_le_three_components
      phase remainder hphase X t hdecomp
    rw [hmain] at hbase
    have hcomp : actual t ≤ 3 * (2 * mainEnergy t + Krem) := by
      dsimp only [actual, mainEnergy, Krem]
      exact hbase.trans (by gcongr)
    exact mul_le_mul_of_nonneg_left hcomp (Real.exp_nonneg _)
  have hmono :
      (∫ t : ℝ in Icc L U, weight t * actual t) ≤
        ∫ t : ℝ in Icc L U,
          weight t * (3 * (2 * mainEnergy t + Krem)) := by
    exact setIntegral_mono_on hactualInt hrightInt.integrableOn
      measurableSet_Icc hpoint
  have hrightNonneg :
      0 ≤ᵐ[volume] fun t : ℝ =>
        weight t * (3 * (2 * mainEnergy t + Krem)) :=
    Filter.Eventually.of_forall fun t => by
      exact mul_nonneg (Real.exp_nonneg _)
        (mul_nonneg (by norm_num)
          (add_nonneg
            (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) hKrem))
  have hsetFull :
      (∫ t : ℝ in Icc L U,
          weight t * (3 * (2 * mainEnergy t + Krem))) ≤
        ∫ t : ℝ, weight t * (3 * (2 * mainEnergy t + Krem)) :=
    setIntegral_le_integral hrightInt hrightNonneg
  have hfullSplit :
      (∫ t : ℝ, weight t * (3 * (2 * mainEnergy t + Krem))) =
        3 *
          (2 * (∫ t : ℝ, weight t * mainEnergy t) +
            Krem * (∫ t : ℝ, weight t)) := by
    calc
      _ = ∫ t : ℝ,
          3 * (2 * (weight t * mainEnergy t) + Krem * weight t) := by
        apply integral_congr_ae
        filter_upwards with t
        ring
      _ = 3 * ∫ t : ℝ,
          (2 * (weight t * mainEnergy t) + Krem * weight t) := by
        rw [integral_const_mul]
      _ = 3 *
          ((∫ t : ℝ, 2 * (weight t * mainEnergy t)) +
            ∫ t : ℝ, Krem * weight t) := by
        rw [integral_add (hmainInt.const_mul 2) (hweightInt.const_mul Krem)]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul]
  have hmainBound :
      (∫ t : ℝ, weight t * mainEnergy t) ≤
        dyadicCriticalGaussianBound K X Delta := by
    simpa only [weight, mainEnergy, dyadicCriticalGaussianBound] using
      integral_gaussian_normSq_dyadicClampedCriticalPrefix_le hX hDelta w
  have hweightMass :
      (∫ t : ℝ, weight t) =
        Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
    simpa only [weight] using integral_criticalAfeGaussianWeight hDeltaPos w
  rw [show (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (riemannZeta ((1 / 2 : ℂ) + I * t) *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      fun t : ℝ => weight t * actual t by rfl]
  calc
    (∫ t : ℝ in Icc L U, weight t * actual t) ≤
        ∫ t : ℝ in Icc L U,
          weight t * (3 * (2 * mainEnergy t + Krem)) := hmono
    _ ≤ ∫ t : ℝ, weight t * (3 * (2 * mainEnergy t + Krem)) := hsetFull
    _ = 3 *
          (2 * (∫ t : ℝ, weight t * mainEnergy t) +
            Krem * (∫ t : ℝ, weight t)) := hfullSplit
    _ ≤ 3 *
          (2 * dyadicCriticalGaussianBound K X Delta +
            Krem * (∫ t : ℝ, weight t)) := by
      gcongr
    _ = 3 *
          (2 * dyadicCriticalGaussianBound K X Delta +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              criticalAfeLogRemainderWindowBound R L U X) := by
      rw [hweightMass]
      dsimp only [Krem]
      ring

end AFE
end HardyTheorem
