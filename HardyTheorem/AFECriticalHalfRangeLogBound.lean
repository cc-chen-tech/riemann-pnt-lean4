import HardyTheorem.AFECriticalHalfRangeRemainder

/-!
# Polylogarithmic normalization of the half-range dyadic AFE bound

This file converts the dyadic depth and polynomial length into the explicit
sixth power of `1 + log U` required by the half-range critical-line estimate.
-/

namespace HardyTheorem
namespace AFE

/-- A dyadic cutoff below `U` has depth at most
`2 * (1 + log U)`. -/
theorem dyadicDepth_succ_le_two_mul_one_add_log
    {K : ℕ} {U : ℝ} (hU : 1 ≤ U)
    (hK : (((2 ^ K : ℕ) : ℝ)) ≤ U) :
    (K + 1 : ℝ) ≤ 2 * (1 + Real.log U) := by
  have hpowPos : 0 < (((2 ^ K : ℕ) : ℝ)) := by positivity
  have hlog := Real.log_le_log hpowPos hK
  have hlogPow :
      Real.log (((2 ^ K : ℕ) : ℝ)) = (K : ℝ) * Real.log 2 := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
  rw [hlogPow] at hlog
  have hlogHalf : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  have hKnonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  nlinarith

/-- If both the dyadic cutoff and the mollifier length lie at their
half-range powers of `U`, the collected polynomial logarithm costs at most
`2 * (1 + log U)`. -/
theorem one_add_log_dyadicProduct_le_two_mul_one_add_log
    {K X : ℕ} {U : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (hK : (((2 ^ K : ℕ) : ℝ)) ≤ U)
    (hXscale : (X : ℝ) ≤ U ^ (9 / 20 : ℝ)) :
    1 + Real.log (((2 ^ K * X : ℕ) : ℝ)) ≤
      2 * (1 + Real.log U) := by
  have hUpos : 0 < U := zero_lt_one.trans_le hU
  have hprodPos : 0 < (((2 ^ K * X : ℕ) : ℝ)) := by positivity
  have hprod : (((2 ^ K * X : ℕ) : ℝ)) ≤
      U * U ^ (9 / 20 : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hK hXscale (Nat.cast_nonneg X) hUpos.le
  have hpower : U * U ^ (9 / 20 : ℝ) = U ^ (29 / 20 : ℝ) := by
    calc
      U * U ^ (9 / 20 : ℝ) = U ^ (1 : ℝ) * U ^ (9 / 20 : ℝ) := by
        rw [Real.rpow_one]
      _ = U ^ ((1 : ℝ) + 9 / 20) := by rw [Real.rpow_add hUpos]
      _ = U ^ (29 / 20 : ℝ) := by norm_num
  rw [hpower] at hprod
  have hlog := Real.log_le_log hprodPos hprod
  rw [Real.log_rpow hUpos] at hlog
  have hlogU : 0 ≤ Real.log U := Real.log_nonneg hU
  nlinarith

/-- The complete dyadic selector factor is bounded by an explicit constant
times the sixth power of the height logarithm. -/
theorem dyadicCriticalGaussianBound_le_halfRange_log
    {K X : ℕ} {U Delta : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X)
    (hK : (((2 ^ K : ℕ) : ℝ)) ≤ U)
    (hXscale : (X : ℝ) ≤ U ^ (9 / 20 : ℝ)) :
    dyadicCriticalGaussianBound K X Delta ≤
      128 * Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant *
          (1 + Real.log U) ^ 6 := by
  have hdepth := dyadicDepth_succ_le_two_mul_one_add_log hU hK
  have hlog := one_add_log_dyadicProduct_le_two_mul_one_add_log
    hU hX hK hXscale
  have hbase : 0 ≤ 1 + Real.log U := by
    linarith [Real.log_nonneg hU]
  have hgauss :
      0 ≤ Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
        MathlibAux.gaussianBucketSchurConstant :=
    mul_nonneg (Real.sqrt_nonneg _)
      MathlibAux.gaussianBucketSchurConstant_pos.le
  have hproductOne : 1 ≤ (2 ^ K * X : ℕ) := by
    exact Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero K (by norm_num))
        (Nat.ne_of_gt (zero_lt_one.trans_le hX)))
  have hlogbase :
      0 ≤ 1 + Real.log (((2 ^ K * X : ℕ) : ℝ)) := by
    have hcastOne : (1 : ℝ) ≤ (((2 ^ K * X : ℕ) : ℝ)) := by
      exact_mod_cast hproductOne
    linarith [Real.log_nonneg hcastOne]
  rw [dyadicCriticalGaussianBound]
  calc
    (K + 1 : ℝ) ^ 2 *
          ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              MathlibAux.gaussianBucketSchurConstant) *
            (2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4)) ≤
        (2 * (1 + Real.log U)) ^ 2 *
          ((Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              MathlibAux.gaussianBucketSchurConstant) *
            (2 * (2 * (1 + Real.log U)) ^ 4)) := by
      gcongr
    _ = 128 * Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
          MathlibAux.gaussianBucketSchurConstant *
            (1 + Real.log U) ^ 6 := by ring

/-- The half-range critical AFE window in final polylogarithmic form.  Apart
from the explicit square-root AFE premise, every contribution is now bounded
by one Gaussian mass times a sixth power of the height logarithm (plus the
fixed AFE remainder constant). -/
theorem setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange_log
    (hAFE : zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {X : ℕ} {L U Delta : ℝ},
      1 < L → L ≤ U → 2 ≤ X →
      (X : ℝ) ≤ L ^ (9 / 20 : ℝ) →
      1 ≤ Real.sqrt (U / (2 * Real.pi)) →
      2 * Real.sqrt (U / (2 * Real.pi)) ≤ U →
      4 * Real.sqrt (U / (2 * Real.pi)) * (X : ℝ) ≤ Delta →
      ∀ w : ℝ,
      (∫ t : ℝ in Set.Icc L U,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
              selbergMoebiusMollifier X
                ((1 / 2 : ℂ) + Complex.I * t))) ≤
        3 * Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log U) ^ 6 + 4 * R ^ 2) := by
  obtain ⟨R, hR, hchoose⟩ :=
    exists_dyadic_setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange
      hAFE
  refine ⟨R, hR, ?_⟩
  intro X L U Delta hL hLU hX hXscale hUsqrt hsqrtU hDelta w
  obtain ⟨K, hKlower, hKtwo, hactual⟩ :=
    hchoose hL hX hXscale hUsqrt hDelta w
  have hKU : (((2 ^ K : ℕ) : ℝ)) ≤ U := hKtwo.trans hsqrtU
  have hXU : (X : ℝ) ≤ U ^ (9 / 20 : ℝ) := by
    exact hXscale.trans
      (Real.rpow_le_rpow (zero_lt_one.trans hL).le hLU (by norm_num))
  have hU : 1 ≤ U := hL.le.trans hLU
  have hXone : 1 ≤ X := by omega
  have hdyadic := dyadicCriticalGaussianBound_le_halfRange_log
    hU hXone hKU hXU (Delta := Delta)
  have hremPower : L ^ (-1 / 20 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hL.le (by norm_num)
  calc
    (∫ t : ℝ in Set.Icc L U,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
              selbergMoebiusMollifier X
                ((1 / 2 : ℂ) + Complex.I * t))) ≤
        3 *
          (2 * dyadicCriticalGaussianBound K X Delta +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              (4 * R ^ 2 * L ^ (-1 / 20 : ℝ))) := hactual
    _ ≤ 3 *
          (2 *
              (128 * Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                MathlibAux.gaussianBucketSchurConstant *
                  (1 + Real.log U) ^ 6) +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              (4 * R ^ 2 * 1)) := by
      gcongr
    _ = 3 * Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
          (256 * MathlibAux.gaussianBucketSchurConstant *
              (1 + Real.log U) ^ 6 + 4 * R ^ 2) := by ring

end AFE
end HardyTheorem
