import HardyTheorem.AFECriticalUnitPhaseLog
import HardyTheorem.AFECriticalHalfRangeRemainder
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Absorbing the logarithmic critical AFE remainder

The weaker critical-line AFE permits a remainder
`R * t^(-1/4) * (1 + log t)`.  After multiplication by a mollifier of
length `X <= L^(9/20)`, its squared contribution is
`O(L^(-1/20) * (1 + log U)^2)` on `[L,U]`.  In the Carlson window
`U = 4L` this tends to zero, so the logarithm costs no power of height.
-/

open Complex Filter

namespace HardyTheorem
namespace AFE

/-- Uniform squared remainder bound for the logarithmic AFE on `[L,U]`. -/
noncomputable def criticalAfeLogRemainderWindowBound
    (R L U : ℝ) (X : ℕ) : ℝ :=
  (R * L ^ (-1 / 4 : ℝ) * (1 + Real.log U) *
    (2 * Real.sqrt X)) ^ 2

/-- Pointwise logarithmic AFE remainders are bounded by the uniform window
quantity. -/
theorem normSq_unitPhaseLogAfeRemainder_product_le_windowBound
    {R L U t : ℝ} {X : ℕ} {remainder : ℂ}
    (hR : 0 < R) (hL : 1 < L) (ht : t ∈ Set.Icc L U) (hX : 2 ≤ X)
    (hrem : ‖remainder‖ ≤
      R * t ^ (-1 / 4 : ℝ) * (1 + Real.log t)) :
    Complex.normSq
        (remainder *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)) ≤
      criticalAfeLogRemainderWindowBound R L U X := by
  have hLpos : 0 < L := zero_lt_one.trans hL
  have htpos : 0 < t := hLpos.trans_le ht.1
  have hUpos : 0 < U := htpos.trans_le ht.2
  have hpow : t ^ (-1 / 4 : ℝ) ≤ L ^ (-1 / 4 : ℝ) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
      hLpos htpos ht.1
  have hlogt : 0 ≤ Real.log t :=
    Real.log_nonneg (hL.le.trans ht.1)
  have hlog : Real.log t ≤ Real.log U :=
    Real.log_le_log htpos ht.2
  have htail :
      t ^ (-1 / 4 : ℝ) * (1 + Real.log t) ≤
        L ^ (-1 / 4 : ℝ) * (1 + Real.log U) := by
    exact mul_le_mul hpow (by linarith) (by linarith)
      (Real.rpow_nonneg hLpos.le _)
  have hremWindow :
      ‖remainder‖ ≤
        R * L ^ (-1 / 4 : ℝ) * (1 + Real.log U) := by
    calc
      ‖remainder‖ ≤ R *
          (t ^ (-1 / 4 : ℝ) * (1 + Real.log t)) := by
        simpa [mul_assoc] using hrem
      _ ≤ R *
          (L ^ (-1 / 4 : ℝ) * (1 + Real.log U)) :=
        mul_le_mul_of_nonneg_left htail hR.le
      _ = R * L ^ (-1 / 4 : ℝ) * (1 + Real.log U) := by ring
  have hrightNonneg :
      0 ≤ R * L ^ (-1 / 4 : ℝ) * (1 + Real.log U) *
        (2 * Real.sqrt X) := by
    have hlogU : 0 ≤ Real.log U := Real.log_nonneg
      (hL.le.trans ht.1 |>.trans ht.2)
    positivity
  have hprod :
      ‖remainder *
          selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
        R * L ^ (-1 / 4 : ℝ) * (1 + Real.log U) *
          (2 * Real.sqrt X) := by
    rw [norm_mul]
    exact mul_le_mul hremWindow
      (norm_selbergMoebiusMollifier_criticalLine_le_two_sqrt hX t)
      (norm_nonneg _)
      (by
        have hlogU : 0 ≤ Real.log U := Real.log_nonneg
          (hL.le.trans ht.1 |>.trans ht.2)
        positivity)
  rw [Complex.normSq_eq_norm_sq, criticalAfeLogRemainderWindowBound]
  exact (sq_le_sq₀ (norm_nonneg _) hrightNonneg).2 hprod

/-- At `X <= L^(9/20)`, the logarithmic remainder retains the strict
`L^(-1/20)` power saving. -/
theorem criticalAfeLogRemainderWindowBound_le_halfRange
    {R L U : ℝ} {X : ℕ} (hL : 1 ≤ L)
    (hX : (X : ℝ) ≤ L ^ (9 / 20 : ℝ)) :
    criticalAfeLogRemainderWindowBound R L U X ≤
      4 * R ^ 2 * L ^ (-1 / 20 : ℝ) *
        (1 + Real.log U) ^ 2 := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hsqrt : (Real.sqrt X) ^ 2 = (X : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg X)
  have hpow : (L ^ (-1 / 4 : ℝ)) ^ 2 = L ^ (-1 / 2 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hLpos]
    congr 1
    norm_num
  rw [criticalAfeLogRemainderWindowBound]
  calc
    (R * L ^ (-1 / 4 : ℝ) * (1 + Real.log U) *
        (2 * Real.sqrt X)) ^ 2 =
        4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * (X : ℝ) *
          (1 + Real.log U) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hpow]
      calc
        R ^ 2 * L ^ (-1 / 2 : ℝ) * (1 + Real.log U) ^ 2 *
            (2 * Real.sqrt X) ^ 2 =
            4 * R ^ 2 * L ^ (-1 / 2 : ℝ) *
              (Real.sqrt X) ^ 2 * (1 + Real.log U) ^ 2 := by ring
        _ = 4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * (X : ℝ) *
              (1 + Real.log U) ^ 2 := by rw [hsqrt]
    _ ≤ 4 * R ^ 2 * L ^ (-1 / 2 : ℝ) *
          L ^ (9 / 20 : ℝ) * (1 + Real.log U) ^ 2 := by
      gcongr
    _ = 4 * R ^ 2 * L ^ (-1 / 20 : ℝ) *
          (1 + Real.log U) ^ 2 := by
      have hcombine : L ^ (-1 / 2 : ℝ) * L ^ (9 / 20 : ℝ) =
          L ^ (-1 / 20 : ℝ) := by
        rw [← Real.rpow_add hLpos]
        norm_num
      calc
        4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * L ^ (9 / 20 : ℝ) *
            (1 + Real.log U) ^ 2 =
            4 * R ^ 2 *
              (L ^ (-1 / 2 : ℝ) * L ^ (9 / 20 : ℝ)) *
                (1 + Real.log U) ^ 2 := by ring
        _ = _ := by rw [hcombine]

private theorem tendsto_rpow_neg_one_twentieth_mul_log_sq :
    Tendsto
      (fun L : ℝ => L ^ (-1 / 20 : ℝ) * Real.log L ^ 2)
      atTop (nhds 0) := by
  have hlogRpow :
      (fun L : ℝ => Real.log L ^ (2 : ℝ))
        =o[atTop] (fun L => L ^ (1 / 40 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num)
  have hlog :
      (fun L : ℝ => Real.log L ^ (2 : ℕ))
        =o[atTop] (fun L => L ^ (1 / 40 : ℝ)) := by
    refine hlogRpow.congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun L =>
      Real.rpow_natCast (Real.log L) 2
  have hraw :
      (fun L : ℝ => Real.log L ^ 2 * L ^ (-1 / 20 : ℝ))
        =o[atTop]
      (fun L => L ^ (1 / 40 : ℝ) * L ^ (-1 / 20 : ℝ)) :=
    hlog.mul_isBigO
      (Asymptotics.isBigO_refl (fun L : ℝ => L ^ (-1 / 20 : ℝ)) atTop)
  have htarget :
      (fun L : ℝ => L ^ (-1 / 20 : ℝ) * Real.log L ^ 2)
        =o[atTop] (fun L => L ^ (-1 / 40 : ℝ)) := by
    refine hraw.congr' ?_ ?_
    · exact Filter.Eventually.of_forall fun L => by ring
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      rw [show (-1 / 40 : ℝ) = 1 / 40 + (-1 / 20) by norm_num,
        Real.rpow_add hL]
  have hdecay :
      Tendsto (fun L : ℝ => L ^ (-(1 / 40 : ℝ))) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 40)
  have hdecay' :
      Tendsto (fun L : ℝ => L ^ (-1 / 40 : ℝ)) atTop (nhds 0) := by
    convert hdecay using 1 <;> norm_num
  exact htarget.tendsto_zero_of_tendsto hdecay'

/-- The logarithmic remainder factor tends to zero in the Carlson window
`[L,4L]`. -/
theorem tendsto_halfRange_logRemainderFactor_atTop_nhds_zero :
    Tendsto
      (fun L : ℝ =>
        L ^ (-1 / 20 : ℝ) * (1 + Real.log (4 * L)) ^ 2)
      atTop (nhds 0) := by
  have hmajor : Tendsto
      (fun L : ℝ => 4 *
        (L ^ (-1 / 20 : ℝ) * Real.log L ^ 2))
      atTop (nhds 0) :=
    by
      simpa using
        tendsto_rpow_neg_one_twentieth_mul_log_sq.const_mul 4
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    positivity
  · filter_upwards
      [eventually_gt_atTop (0 : ℝ),
        Real.tendsto_log_atTop.eventually_ge_atTop (1 + Real.log 4)]
      with L hL hlogL
    have hlogFour : Real.log (4 * L) = Real.log 4 + Real.log L := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hL.ne']
    have hbase : 0 ≤ Real.log L := by
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
    have hlogFourNonneg : 0 ≤ Real.log 4 :=
      Real.log_nonneg (by norm_num)
    have hshift : 1 + Real.log (4 * L) ≤ 2 * Real.log L := by
      rw [hlogFour]
      linarith
    have hsq : (1 + Real.log (4 * L)) ^ 2 ≤
        (2 * Real.log L) ^ 2 := by
      exact pow_le_pow_left₀ (by rw [hlogFour]; nlinarith) hshift 2
    calc
      L ^ (-1 / 20 : ℝ) * (1 + Real.log (4 * L)) ^ 2 ≤
          L ^ (-1 / 20 : ℝ) * (2 * Real.log L) ^ 2 := by
        gcongr
      _ = 4 * (L ^ (-1 / 20 : ℝ) * Real.log L ^ 2) := by ring

/-- Consequently the logarithmic remainder factor is eventually at most
one; downstream estimates can absorb it into an absolute constant. -/
theorem eventually_halfRange_logRemainderFactor_le_one :
    ∀ᶠ L : ℝ in atTop,
      L ^ (-1 / 20 : ℝ) * (1 + Real.log (4 * L)) ^ 2 ≤ 1 := by
  exact
    (tendsto_halfRange_logRemainderFactor_atTop_nhds_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ h => h.le)

end AFE
end HardyTheorem
