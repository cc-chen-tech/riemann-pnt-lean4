import HardyTheorem.AFECriticalPolynomialBridge
import HardyTheorem.AFECriticalDyadicMaximalGaussian
import Mathlib.MeasureTheory.Function.Floor

/-!
# The canonical square-root AFE cutoff as a measurable dyadic selector

The natural cutoff is unbounded on the whole real line.  We therefore clamp
it to the ambient dyadic block before applying the global Gaussian maximal
estimate.  On any window where the natural cutoff is at most the ambient
endpoint, the clamped and genuine prefixes agree exactly.
-/

open Complex MeasureTheory Set

namespace HardyTheorem
namespace AFE

/-- The canonical floor-square-root cutoff is Borel measurable. -/
theorem measurable_criticalAfeCutoff : Measurable criticalAfeCutoff := by
  unfold criticalAfeCutoff
  exact (Real.continuous_sqrt.measurable.comp
    (measurable_id.div_const (2 * Real.pi))).nat_floor

/-- A dyadic endpoint strictly above the square-root coordinate at the right
edge of a window also lies strictly above every natural cutoff
successor in that window. -/
theorem criticalAfeCutoff_succ_le_pow_of_mem_Icc
    {K : ℕ} {L U t : ℝ} (ht : t ∈ Icc L U)
    (hU : Real.sqrt (U / (2 * Real.pi)) < (((2 ^ K : ℕ) : ℝ))) :
    criticalAfeCutoff t + 1 ≤ 2 ^ K := by
  have hc : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hdiv : t / (2 * Real.pi) ≤ U / (2 * Real.pi) :=
    (div_le_div_iff_of_pos_right hc).2 ht.2
  have hsqrt : Real.sqrt (t / (2 * Real.pi)) ≤
      Real.sqrt (U / (2 * Real.pi)) :=
    Real.sqrt_le_sqrt hdiv
  have hy : 0 ≤ Real.sqrt (t / (2 * Real.pi)) := Real.sqrt_nonneg _
  have hfloor : Nat.floor (Real.sqrt (t / (2 * Real.pi))) < 2 ^ K :=
    (Nat.floor_lt hy).2 (hsqrt.trans_lt hU)
  unfold criticalAfeCutoff
  omega

/-- The canonical selector clamped to one ambient dyadic block. -/
noncomputable def dyadicClampedCriticalPrefixMollifiedPolynomial
    (K X : ℕ) (t : ℝ) : ℂ :=
  dyadicMovingPrefixMollifiedPolynomial K
    (min (criticalAfeCutoff t + 1) (2 ^ K)) X t

/-- A measurable finite-piecewise family of fixed dyadic prefixes. -/
theorem measurable_dyadicClampedCriticalPrefixMollifiedPolynomial
    (K X : ℕ) :
    Measurable fun t : ℝ =>
      dyadicClampedCriticalPrefixMollifiedPolynomial K X t := by
  let cutoff : ℝ → ℕ := fun t => min (criticalAfeCutoff t + 1) (2 ^ K)
  have hcutoff : Measurable cutoff :=
    (measurable_criticalAfeCutoff.add measurable_const).min measurable_const
  have hrepr : (fun t : ℝ =>
      dyadicClampedCriticalPrefixMollifiedPolynomial K X t) =
      fun t : ℝ => ∑ m ∈ Finset.range (2 ^ K + 1),
        if cutoff t = m then
          dyadicMovingPrefixMollifiedPolynomial K m X t
        else 0 := by
    funext t
    have hmem : cutoff t ∈ Finset.range (2 ^ K + 1) := by
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (min_le_right _ _)
    rw [Finset.sum_eq_single (cutoff t)]
    · simp only [if_pos]
      rfl
    · intro m hm hne
      simp only [if_neg hne.symm]
    · intro hnot
      exact (hnot hmem).elim
  rw [hrepr]
  exact Finset.measurable_fun_sum (Finset.range (2 ^ K + 1)) fun m hm =>
    Measurable.ite (measurableSet_eq_fun hcutoff measurable_const)
      (continuous_dyadicMovingPrefixMollifiedPolynomial K m X).measurable
      measurable_const

/-- Clamping does not change the prefix below the ambient dyadic endpoint. -/
theorem dyadicClampedCriticalPrefix_eq_of_cutoff_succ_le
    {K X : ℕ} {t : ℝ} (ht : criticalAfeCutoff t + 1 ≤ 2 ^ K) :
    dyadicClampedCriticalPrefixMollifiedPolynomial K X t =
      dyadicMovingPrefixMollifiedPolynomial K (criticalAfeCutoff t + 1) X t := by
  simp [dyadicClampedCriticalPrefixMollifiedPolynomial, min_eq_left ht]

/-- With the necessary successor normalization, the clamped prefix is
exactly the canonical AFE main sum times the concrete mollifier. -/
theorem criticalAfeMainSum_mul_mollifier_eq_dyadicClampedPrefix
    {K X : ℕ} {t : ℝ} (ht : criticalAfeCutoff t + 1 ≤ 2 ^ K) :
    criticalAfeMainSum t *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      dyadicClampedCriticalPrefixMollifiedPolynomial K X t := by
  rw [dyadicClampedCriticalPrefix_eq_of_cutoff_succ_le ht,
    dyadicMovingPrefixMollifiedPolynomial_eq_Ico K
      (criticalAfeCutoff t + 1) X ht t,
    criticalAfeMainSum_eq_Icc]
  congr 2

private theorem conj_inv_nat_cpow_criticalLine_eq_neg
    (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ)
        (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) =
      1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t) := by
  rw [map_div₀, map_one]
  have harg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  have hpow := Complex.cpow_conj
    (n : ℂ) ((1 / 2 : ℂ) + I * t) harg
  have hconj :
      (starRingEnd ℂ) ((1 / 2 : ℂ) + I * t) =
        (1 / 2 : ℂ) - I * t := by
    apply Complex.ext <;> norm_num
  rw [hconj] at hpow
  simpa using congrArg Inv.inv hpow.symm

/-- The dual square-root AFE polynomial is exactly the complex conjugate of
the main polynomial at the same height. -/
theorem criticalAfeDualSum_eq_conj_mainSum (t : ℝ) :
    criticalAfeDualSum t = (starRingEnd ℂ) (criticalAfeMainSum t) := by
  calc
    criticalAfeDualSum t =
        ∑ n ∈ Finset.Icc 1 (criticalAfeCutoff t),
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) - I * t) :=
      criticalAfeDualSum_eq_Icc t
    _ = ∑ n ∈ Finset.Icc 1 (criticalAfeCutoff t),
          (starRingEnd ℂ)
            (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact (conj_inv_nat_cpow_criticalLine_eq_neg n t).symm
    _ = (starRingEnd ℂ)
        (∑ n ∈ Finset.Icc 1 (criticalAfeCutoff t),
          1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) := by
      exact (map_sum (starAddEquiv : ℂ ≃+ ℂ) _ _).symm
    _ = (starRingEnd ℂ) (criticalAfeMainSum t) := by
      rw [criticalAfeMainSum_eq_Icc]

/-- The corrected unit dual phase and complex conjugation preserve exactly
the squared norm of the main AFE term after multiplication by the same
mollifier. -/
theorem criticalAfeDualProduct_normSq_eq_mainProduct
    (X : ℕ) (t : ℝ) :
    Complex.normSq
        (criticalAfeDualPhase t *
          (criticalAfeDualSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
      Complex.normSq
        (criticalAfeMainSum t *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) := by
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_mul,
    criticalAfeDualSum_eq_conj_mainSum, Complex.normSq_conj]
  have hphase : Complex.normSq (criticalAfeDualPhase t) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_criticalAfeDualPhase]
    norm_num
  rw [hphase, one_mul]

private theorem aestronglyMeasurable_gaussian_normSq_dyadicClampedCriticalPrefix
    (K X : ℕ) (Delta w : ℝ) :
    AEStronglyMeasurable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicClampedCriticalPrefixMollifiedPolynomial K X t) := by
  have hweight : Measurable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) := by
    fun_prop
  have henergy : Measurable fun t : ℝ =>
      Complex.normSq
        (dyadicClampedCriticalPrefixMollifiedPolynomial K X t) :=
    Complex.continuous_normSq.measurable.comp
      (measurable_dyadicClampedCriticalPrefixMollifiedPolynomial K X)
  change AEStronglyMeasurable
    ((fun t : ℝ => Real.exp (-((t - w) ^ 2) / Delta ^ 2)) *
      fun t : ℝ => Complex.normSq
        (dyadicClampedCriticalPrefixMollifiedPolynomial K X t))
  exact (hweight.mul henergy).aestronglyMeasurable

/-- The canonical clamped Gaussian prefix energy is globally integrable. -/
theorem integrable_gaussian_normSq_dyadicClampedCriticalPrefix
    {K X : ℕ} (hX : 2 ≤ X) {Delta : ℝ}
    (hDelta : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta) (w : ℝ) :
    Integrable fun t : ℝ =>
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicClampedCriticalPrefixMollifiedPolynomial K X t) := by
  apply integrable_gaussian_normSq_dyadicMovingPrefixMollifiedPolynomial
    hX hDelta w (fun t => min (criticalAfeCutoff t + 1) (2 ^ K))
  · intro t
    exact min_le_right _ _
  · simpa only [dyadicClampedCriticalPrefixMollifiedPolynomial] using
      aestronglyMeasurable_gaussian_normSq_dyadicClampedCriticalPrefix
        K X Delta w

/-- The measurable clamped canonical selector satisfies the global Gaussian
Rademacher--Menshov bound without a separate measurability premise. -/
theorem integral_gaussian_normSq_dyadicClampedCriticalPrefix_le
    {K X : ℕ} (hX : 2 ≤ X) {Delta : ℝ}
    (hDelta : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta) (w : ℝ) :
    (∫ t : ℝ, Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (dyadicClampedCriticalPrefixMollifiedPolynomial K X t)) ≤
      (K + 1 : ℝ) ^ 2 *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
  apply integral_gaussian_normSq_dyadicMovingPrefixMollifiedPolynomial_le
    hX hDelta w (fun t => min (criticalAfeCutoff t + 1) (2 ^ K))
  · intro t
    exact min_le_right _ _
  · simpa only [dyadicClampedCriticalPrefixMollifiedPolynomial] using
      aestronglyMeasurable_gaussian_normSq_dyadicClampedCriticalPrefix
        K X Delta w

/-- On a window lying below the ambient dyadic endpoint, the genuine
canonical AFE main term has no more Gaussian energy than the global clamped
maximal selector. -/
theorem setIntegral_gaussian_normSq_criticalAfeMain_mul_mollifier_le
    {K X : ℕ} (hX : 2 ≤ X) {L U Delta : ℝ}
    (hU : Real.sqrt (U / (2 * Real.pi)) < (((2 ^ K : ℕ) : ℝ)))
    (hDelta : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta) (w : ℝ) :
    (∫ t : ℝ in Icc L U,
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (criticalAfeMainSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) ≤
      (K + 1 : ℝ) ^ 2 *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
  let f : ℝ → ℝ := fun t =>
    Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
      Complex.normSq
        (dyadicClampedCriticalPrefixMollifiedPolynomial K X t)
  have hsetEq :
      (∫ t : ℝ in Icc L U,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (criticalAfeMainSum t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
        ∫ t : ℝ in Icc L U, f t := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only [f]
    rw [criticalAfeMainSum_mul_mollifier_eq_dyadicClampedPrefix
      (criticalAfeCutoff_succ_le_pow_of_mem_Icc ht hU)]
  have hfInt : Integrable f := by
    simpa only [f] using
      integrable_gaussian_normSq_dyadicClampedCriticalPrefix hX hDelta w
  have hfNonneg : 0 ≤ᵐ[volume] f :=
    Filter.Eventually.of_forall fun t =>
      mul_nonneg (Real.exp_nonneg _) (Complex.normSq_nonneg _)
  calc
    (∫ t : ℝ in Icc L U,
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (criticalAfeMainSum t *
            selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t))) =
        ∫ t : ℝ in Icc L U, f t := hsetEq
    _ ≤ ∫ t : ℝ, f t := setIntegral_le_integral hfInt hfNonneg
    _ ≤ (K + 1 : ℝ) ^ 2 *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
      simpa only [f] using
        integral_gaussian_normSq_dyadicClampedCriticalPrefix_le
          hX hDelta w

/-- The complete dual AFE term, including its corrected unit phase, has the
same window Gaussian bound as the main AFE term. -/
theorem setIntegral_gaussian_normSq_criticalAfeDualProduct_le
    {K X : ℕ} (hX : 2 ≤ X) {L U Delta : ℝ}
    (hU : Real.sqrt (U / (2 * Real.pi)) < (((2 ^ K : ℕ) : ℝ)))
    (hDelta : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta) (w : ℝ) :
    (∫ t : ℝ in Icc L U,
      Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
        Complex.normSq
          (criticalAfeDualPhase t *
            (criticalAfeDualSum t *
              selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)))) ≤
      (K + 1 : ℝ) ^ 2 *
        ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
            MathlibAux.gaussianBucketSchurConstant) *
          (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) := by
  have hEq :
      (∫ t : ℝ in Icc L U,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (criticalAfeDualPhase t *
              (criticalAfeDualSum t *
                selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)))) =
        ∫ t : ℝ in Icc L U,
          Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
            Complex.normSq
              (criticalAfeMainSum t *
                selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    dsimp only
    rw [criticalAfeDualProduct_normSq_eq_mainProduct]
  rw [hEq]
  exact setIntegral_gaussian_normSq_criticalAfeMain_mul_mollifier_le
    hX hU hDelta w

end AFE
end HardyTheorem
