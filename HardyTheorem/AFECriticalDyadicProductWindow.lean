import HardyTheorem.AFECriticalDyadicCanonicalSelector
import HardyTheorem.AFECriticalGaussianWindow

/-!
# Complete critical AFE window from the dyadic maximal selector

This module combines the proved main and dual dyadic Gaussian bounds with
the canonical AFE remainder.  The square-root AFE remains an explicit
proposition premise; no analytic theorem is introduced here.
-/

open Complex MeasureTheory Set

namespace HardyTheorem
namespace AFE

/-- The common Gaussian bound for one of the two square-root AFE polynomial
terms after multiplication by the concrete Selberg mollifier. -/
noncomputable def dyadicCriticalGaussianBound
    (K X : ℕ) (Delta : ℝ) : ℝ :=
  (K + 1 : ℝ) ^ 2 *
    ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant) *
      (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4))

private theorem continuous_normSq_criticalAfeProduct_dyadic
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

private theorem normSq_criticalAfeCanonicalRemainder_product_le_windowBound
    {R L U t : ℝ} {X : ℕ} (hR : 0 < R) (hL : 1 < L)
    (ht : t ∈ Icc L U) (hX : 2 ≤ X)
    (hcanonical : ∀ u : ℝ, u > 1 →
      ‖criticalAfeCanonicalRemainder u‖ ≤
        R * u ^ (-1 / 4 : ℝ)) :
    Complex.normSq
        (criticalAfeCanonicalRemainder t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      criticalAfeRemainderWindowBound R L X := by
  have hLpos : 0 < L := zero_lt_one.trans hL
  have htpos : 0 < t := hLpos.trans_le ht.1
  have hpow : t ^ (-1 / 4 : ℝ) ≤ L ^ (-1 / 4 : ℝ) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
      hLpos htpos ht.1
  have hremt := hcanonical t (hL.trans_le ht.1)
  have hremL :
      ‖criticalAfeCanonicalRemainder t‖ ≤
        R * L ^ (-1 / 4 : ℝ) :=
    hremt.trans (mul_le_mul_of_nonneg_left hpow hR.le)
  have hRL : 0 ≤ R * L ^ (-1 / 4 : ℝ) := by positivity
  have hprod :
      ‖criticalAfeCanonicalRemainder t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
        (R * L ^ (-1 / 4 : ℝ)) * (2 * Real.sqrt X) := by
    rw [norm_mul]
    exact mul_le_mul hremL
      (norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt hX t)
      (norm_nonneg _) hRL
  have hright :
      0 ≤ R * L ^ (-1 / 4 : ℝ) * (2 * Real.sqrt X) := by
    positivity
  rw [Complex.normSq_eq_norm_sq, criticalAfeRemainderWindowBound]
  exact (sq_le_sq₀ (norm_nonneg _) hright).2 hprod

private theorem criticalAfeDualProduct_withoutPhase_normSq_eq_mainProduct
    (X : ℕ) (t : ℝ) :
    Complex.normSq
        (criticalAfeDualSum t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) =
      Complex.normSq
        (criticalAfeMainSum t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) := by
  rw [Complex.normSq_mul, Complex.normSq_mul,
    criticalAfeDualSum_eq_conj_mainSum, Complex.normSq_conj]

/-- Conditional only on the explicit symmetric square-root AFE target, the
complete mollified zeta product on a height window is bounded by two copies
of the dyadic maximal polynomial moment plus the canonical remainder mass. -/
theorem setIntegral_gaussian_normSq_criticalAfeProduct_le_of_dyadic_target
    (hAFE : zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {K X : ℕ} {L U Delta : ℝ},
      1 < L → 2 ≤ X →
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
              criticalAfeRemainderWindowBound R L X) := by
  obtain ⟨R, hR, hcanonical⟩ :=
    zeta_critical_afe_target_iff_canonical_remainder.mp hAFE
  refine ⟨R, hR, ?_⟩
  intro K X L U Delta hL hX hU hDelta w
  let weight : ℝ → ℝ := fun t =>
    Real.exp (-((t - w) ^ 2) / Delta ^ 2)
  let mainEnergy : ℝ → ℝ := fun t =>
    Complex.normSq
      (dyadicClampedCriticalPrefixMollifiedPolynomial K X t)
  let actual : ℝ → ℝ := fun t =>
    Complex.normSq
      (riemannZeta ((1 / 2 : ℂ) + I * t) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))
  let Krem : ℝ := criticalAfeRemainderWindowBound R L X
  have hDeltaPos : 0 < Delta := by
    have hpositive : 0 < ((2 ^ K * X : ℕ) : ℝ) := by positivity
    linarith
  have hweightInt : Integrable weight := by
    simpa only [weight] using integrable_criticalAfeGaussianWeight hDeltaPos w
  have hmainInt : Integrable fun t : ℝ => weight t * mainEnergy t := by
    simpa only [weight, mainEnergy] using
      integrable_gaussian_normSq_dyadicClampedCriticalPrefix hX hDelta w
  have hKrem : 0 ≤ Krem := by
    dsimp only [Krem, criticalAfeRemainderWindowBound]
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
      exact continuous_normSq_criticalAfeProduct_dyadic X
  have hactualInt : IntegrableOn (fun t : ℝ => weight t * actual t) (Icc L U) :=
    hactualCont.continuousOn.integrableOn_Icc
  have hpoint (t : ℝ) (ht : t ∈ Icc L U) :
      weight t * actual t ≤
        weight t * (3 * (2 * mainEnergy t + Krem)) := by
    have hcutoff := criticalAfeCutoff_succ_le_pow_of_mem_Icc ht hU
    have hmain := criticalAfeMainSum_mul_mollifier_eq_dyadicClampedPrefix
      (K := K) (X := X) hcutoff
    have hdual := criticalAfeDualProduct_withoutPhase_normSq_eq_mainProduct X t
    have hrem :=
      normSq_criticalAfeCanonicalRemainder_product_le_windowBound
        hR hL ht hX hcanonical
    have hbase := normSq_criticalAfeProduct_le_three_components X t
    rw [hmain, hdual, hmain] at hbase
    have hcomp : actual t ≤ 3 * (2 * mainEnergy t + Krem) := by
      dsimp only [actual, mainEnergy, Krem]
      calc
        _ ≤ 3 *
            (Complex.normSq
                (dyadicClampedCriticalPrefixMollifiedPolynomial K X t) +
              Complex.normSq
                (dyadicClampedCriticalPrefixMollifiedPolynomial K X t) +
              Complex.normSq
                (criticalAfeCanonicalRemainder t *
                  selbergMoebiusMollifier X
                    ((1 / 2 : ℂ) + I * t))) := hbase
        _ ≤ 3 *
            (2 * Complex.normSq
                (dyadicClampedCriticalPrefixMollifiedPolynomial K X t) +
              criticalAfeRemainderWindowBound R L X) := by
          gcongr
          linarith
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
              criticalAfeRemainderWindowBound R L X) := by
      rw [hweightMass]
      dsimp only [Krem]
      ring

end AFE
end HardyTheorem
