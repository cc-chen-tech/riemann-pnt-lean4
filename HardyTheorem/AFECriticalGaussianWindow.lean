import HardyTheorem.AFECriticalGaussianFixedEnergy
import HardyTheorem.AFECriticalTargetTwoCutoff

/-!
# Central Gaussian window for the critical-line AFE

Assuming the still-explicit corrected square-root AFE target, the mollified
zeta second moment on a short central height window is bounded by the two
possible fixed-cutoff full-line Gaussian energies and the uniform canonical
AFE remainder.  No moving floor fibre is integrated.
-/

open Complex MeasureTheory Set

namespace HardyTheorem
namespace AFE

/-- The real shifted Gaussian used in the AFE window is integrable. -/
theorem integrable_criticalAfeGaussianWeight
    {Delta : ℝ} (hDelta : 0 < Delta) (w : ℝ) :
    Integrable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) := by
  have hb : 0 < (1 / Delta ^ 2 : ℝ) := by positivity
  have hbase := (integrable_exp_neg_mul_sq hb).comp_sub_right w
  convert hbase using 1
  funext t
  congr 1
  field_simp [hDelta.ne']

/-- Exact total mass of the real shifted Gaussian. -/
theorem integral_criticalAfeGaussianWeight
    {Delta : ℝ} (hDelta : 0 < Delta) (w : ℝ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2)) =
      Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
  let base : ℝ → ℝ := fun u =>
    Real.exp (-(1 / Delta ^ 2) * u ^ 2)
  have hshift : (∫ t : ℝ, base (t - w)) = ∫ t : ℝ, base t :=
    integral_sub_right_eq_self base w
  calc
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2)) =
        ∫ t : ℝ, base (t - w) := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp only [base]
      congr 1
      field_simp [hDelta.ne']
    _ = ∫ t : ℝ, base t := hshift
    _ = Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
      simpa only [base] using integral_gaussian (1 / Delta ^ 2)

private theorem continuous_normSq_criticalAfeProduct (X : ℕ) :
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

/-- Under the corrected square-root AFE target, the central-window mollified
zeta moment is bounded by the two fixed-cutoff full-line polynomial moments
plus the exact full Gaussian mass times the uniform remainder bound. -/
theorem setIntegral_gaussian_normSq_criticalAfeProduct_le_of_target
    (hAFE : zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {L U w Delta : ℝ} {X : ℕ},
      1 < L → L ≤ U →
      Real.sqrt (U / (2 * Real.pi)) <
          Real.sqrt (L / (2 * Real.pi)) + 1 →
      2 ≤ X → 1 ≤ criticalAfeCutoff L →
      2 * ((((criticalAfeCutoff L + 1) * X : ℕ) : ℝ)) ≤ Delta →
      (∫ t : ℝ in Icc L U,
          Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
            Complex.normSq
              (riemannZeta ((1 / 2 : ℂ) + I * t) *
                selbergMoebiusMollifier X
                  ((1 / 2 : ℂ) + I * t))) ≤
        3 *
          (2 *
              (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (2 *
                    (1 + Real.log (criticalAfeCutoff L * X)) ^ 4)) +
            2 *
              (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (2 *
                    (1 + Real.log ((criticalAfeCutoff L + 1) * X)) ^ 4)) +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              criticalAfeRemainderWindowBound R L X) := by
  obtain ⟨R, hR, hpointwise⟩ :=
    normSq_criticalAfeProduct_le_twoCutoffEnergies_of_target hAFE
  refine ⟨R, hR, ?_⟩
  intro L U w Delta X hL hLU hwidth hX hN hlength
  let N := criticalAfeCutoff L
  let weight : ℝ → ℝ := fun t =>
    Real.exp (-((t - w) ^ 2) / Delta ^ 2)
  let actual : ℝ → ℝ := fun t =>
    Complex.normSq
      (riemannZeta ((1 / 2 : ℂ) + I * t) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))
  let E0 : ℝ → ℝ := criticalAfeFixedPolynomialEnergy N X
  let E1 : ℝ → ℝ := criticalAfeFixedPolynomialEnergy (N + 1) X
  let K : ℝ := criticalAfeRemainderWindowBound R L X
  have hDelta : 0 < Delta := by
    have hpositive : 0 < (((N + 1) * X : ℕ) : ℝ) := by
      positivity
    change 2 * ((((N + 1) * X : ℕ) : ℝ)) ≤ Delta at hlength
    linarith
  have hlength0 : 2 * (((N * X : ℕ) : ℝ)) ≤ Delta := by
    have hcast : (((N * X : ℕ) : ℝ)) ≤ (((N + 1) * X : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right X (Nat.le_succ N)
    change 2 * ((((N + 1) * X : ℕ) : ℝ)) ≤ Delta at hlength
    linarith
  have hweightInt : Integrable weight := by
    simpa only [weight] using integrable_criticalAfeGaussianWeight hDelta w
  have hE0Int : Integrable fun t : ℝ => weight t * E0 t := by
    simpa only [weight, E0] using
      integrable_gaussian_mul_criticalAfeFixedPolynomialEnergy
        hDelta w N X
  have hE1Int : Integrable fun t : ℝ => weight t * E1 t := by
    simpa only [weight, E1] using
      integrable_gaussian_mul_criticalAfeFixedPolynomialEnergy
        hDelta w (N + 1) X
  have hKnonneg : 0 ≤ K := by
    dsimp only [K, criticalAfeRemainderWindowBound]
    positivity
  have hKInt : Integrable fun t : ℝ => weight t * K :=
    hweightInt.mul_const K
  have hactualCont : Continuous fun t : ℝ => weight t * actual t := by
    apply Continuous.mul
    · dsimp only [weight]
      fun_prop
    · dsimp only [actual]
      exact continuous_normSq_criticalAfeProduct X
  have hactualSetInt : IntegrableOn (fun t : ℝ => weight t * actual t) (Icc L U) :=
    hactualCont.continuousOn.integrableOn_Icc
  have hrightInt : Integrable fun t : ℝ =>
      weight t * (3 * (E0 t + E1 t + K)) := by
    have hsum : Integrable fun t : ℝ =>
        (weight t * E0 t + weight t * E1 t) + weight t * K :=
      (hE0Int.add hE1Int).add hKInt
    convert hsum.const_mul 3 using 1
    funext t
    ring
  have hmono :
      (∫ t : ℝ in Icc L U, weight t * actual t) ≤
        ∫ t : ℝ in Icc L U,
          weight t * (3 * (E0 t + E1 t + K)) := by
    apply setIntegral_mono_on hactualSetInt hrightInt.integrableOn measurableSet_Icc
    intro t ht
    have hbase := hpointwise hL (show t ∈ Icc L U from ht) hwidth X hX
    dsimp only [actual, E0, E1, K, N]
    exact mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
  have hsplit :
      (∫ t : ℝ in Icc L U,
          weight t * (3 * (E0 t + E1 t + K))) =
        3 *
          ((∫ t : ℝ in Icc L U, weight t * E0 t) +
            (∫ t : ℝ in Icc L U, weight t * E1 t) +
            K * (∫ t : ℝ in Icc L U, weight t)) := by
    calc
      _ = ∫ t : ℝ in Icc L U,
          3 * ((weight t * E0 t + weight t * E1 t) + weight t * K) := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = 3 * (∫ t : ℝ in Icc L U,
          (weight t * E0 t + weight t * E1 t) + weight t * K) := by
            rw [integral_const_mul]
      _ = 3 *
          ((∫ t : ℝ in Icc L U,
              weight t * E0 t + weight t * E1 t) +
            ∫ t : ℝ in Icc L U, weight t * K) := by
        congr 1
        exact integral_add (hE0Int.add hE1Int).integrableOn hKInt.integrableOn
      _ = _ := by
        rw [show (∫ t : ℝ in Icc L U,
              weight t * E0 t + weight t * E1 t) =
            (∫ t : ℝ in Icc L U, weight t * E0 t) +
              ∫ t : ℝ in Icc L U, weight t * E1 t from
          integral_add hE0Int.integrableOn hE1Int.integrableOn,
          integral_mul_const]
        ring
  have hE0set :
      (∫ t : ℝ in Icc L U, weight t * E0 t) ≤
        ∫ t : ℝ, weight t * E0 t := by
    exact setIntegral_le_integral hE0Int
      (Filter.Eventually.of_forall fun t =>
        mul_nonneg (Real.exp_pos _).le
          (criticalAfeFixedPolynomialEnergy_nonneg N X t))
  have hE1set :
      (∫ t : ℝ in Icc L U, weight t * E1 t) ≤
        ∫ t : ℝ, weight t * E1 t := by
    exact setIntegral_le_integral hE1Int
      (Filter.Eventually.of_forall fun t =>
        mul_nonneg (Real.exp_pos _).le
          (criticalAfeFixedPolynomialEnergy_nonneg (N + 1) X t))
  have hweightSet :
      (∫ t : ℝ in Icc L U, weight t) ≤ ∫ t : ℝ, weight t := by
    exact setIntegral_le_integral hweightInt
      (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
  have hE0bound :
      (∫ t : ℝ, weight t * E0 t) ≤
        2 *
          (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant *
              (2 * (1 + Real.log (N * X)) ^ 4)) := by
    simpa only [weight, E0] using
      integral_gaussian_mul_criticalAfeFixedPolynomialEnergy_le
        hN hX hlength0 w
  have hE1bound :
      (∫ t : ℝ, weight t * E1 t) ≤
        2 *
          (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant *
              (2 * (1 + Real.log ((N + 1) * X)) ^ 4)) := by
    simpa only [weight, E1, Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
      integral_gaussian_mul_criticalAfeFixedPolynomialEnergy_le
        (by omega : 1 ≤ N + 1) hX hlength w
  have hweightMass :
      (∫ t : ℝ, weight t) =
        Real.sqrt (Real.pi / (1 / Delta ^ 2)) := by
    simpa only [weight] using integral_criticalAfeGaussianWeight hDelta w
  rw [show (fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (riemannZeta ((1 / 2 : ℂ) + I * t) *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      fun t : ℝ => weight t * actual t by rfl]
  calc
    (∫ t : ℝ in Icc L U, weight t * actual t) ≤
        ∫ t : ℝ in Icc L U,
          weight t * (3 * (E0 t + E1 t + K)) := hmono
    _ = 3 *
          ((∫ t : ℝ in Icc L U, weight t * E0 t) +
            (∫ t : ℝ in Icc L U, weight t * E1 t) +
            K * (∫ t : ℝ in Icc L U, weight t)) := hsplit
    _ ≤ 3 *
          ((∫ t : ℝ, weight t * E0 t) +
            (∫ t : ℝ, weight t * E1 t) +
            K * (∫ t : ℝ, weight t)) := by
      gcongr
    _ ≤ 3 *
          (2 *
              (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (2 * (1 + Real.log (N * X)) ^ 4)) +
            2 *
              (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (2 * (1 + Real.log ((N + 1) * X)) ^ 4)) +
            K * Real.sqrt (Real.pi / (1 / Delta ^ 2))) := by
      rw [hweightMass]
      gcongr
    _ = 3 *
          (2 *
              (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (2 * (1 + Real.log (N * X)) ^ 4)) +
            2 *
              (Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (2 * (1 + Real.log ((N + 1) * X)) ^ 4)) +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) * K) := by ring
    _ = _ := by rfl

end AFE
end HardyTheorem
