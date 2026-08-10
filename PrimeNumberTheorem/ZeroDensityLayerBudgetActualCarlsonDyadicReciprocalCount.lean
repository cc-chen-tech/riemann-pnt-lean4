import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson
import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicReciprocalSummability

/-!
# Actual Carlson dyadic reciprocal count

This module derives a summable reciprocal-height dyadic majorant directly
from the Carlson certificate already available on `main`.  It retains the
full fourth-power logarithmic loss and does not import the historical stacked
dyadic framework.
-/

namespace PrimeNumberTheorem

open Filter

/-- Carlson's classical fixed-strip density exponent. -/
def pntCarlsonClassicalDensityExponent (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

theorem pntCarlsonClassicalDensityExponent_lt_one
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    pntCarlsonClassicalDensityExponent sigma < 1 := by
  have hpos : 0 < 2 * sigma - 1 := by
    linarith
  have hsq : 0 < (2 * sigma - 1) * (2 * sigma - 1) :=
    mul_pos hpos hpos
  unfold pntCarlsonClassicalDensityExponent
  nlinarith

/-- Geometric ratio after combining Carlson density with `1 / |rho|`. -/
noncomputable def pntCarlsonDyadicReciprocalRatio (sigma : ℝ) : ℝ :=
  Real.exp ((pntCarlsonClassicalDensityExponent sigma - 1) * Real.log 2)

theorem pntCarlsonDyadicReciprocalRatio_pos (sigma : ℝ) :
    0 < pntCarlsonDyadicReciprocalRatio sigma := by
  exact Real.exp_pos _

theorem pntCarlsonDyadicReciprocalRatio_lt_one
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    pntCarlsonDyadicReciprocalRatio sigma < 1 := by
  unfold pntCarlsonDyadicReciprocalRatio
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos
    (sub_neg.mpr (pntCarlsonClassicalDensityExponent_lt_one hhalf))
    (Real.log_pos (by norm_num))

/-- Carlson's dyadic reciprocal-height majorant, including `log^4`. -/
noncomputable def pntCarlsonDyadicLogFourthMajorant
    (C sigma : ℝ) (n : ℕ) : ℝ :=
  C * (n : ℝ) ^ 4 * pntCarlsonDyadicReciprocalRatio sigma ^ n

theorem summable_pntCarlsonDyadicLogFourthMajorant
    {C sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    Summable (pntCarlsonDyadicLogFourthMajorant C sigma) := by
  have hratioPos : 0 < pntCarlsonDyadicReciprocalRatio sigma :=
    pntCarlsonDyadicReciprocalRatio_pos sigma
  have hratioNorm : ‖pntCarlsonDyadicReciprocalRatio sigma‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hratioPos]
    exact pntCarlsonDyadicReciprocalRatio_lt_one hhalf
  simpa only [pntCarlsonDyadicLogFourthMajorant, ← mul_assoc] using
    (summable_pow_mul_geometric_of_norm_lt_one
      (R := ℝ) 4 hratioNorm).mul_left C

/-- Reciprocal-height normalization of a dyadic counting sequence. -/
noncomputable def pntDyadicReciprocalWeightedCount
    (count : ℕ → ℝ) (n : ℕ) : ℝ :=
  count n / (2 : ℝ) ^ n

theorem pntDyadicReciprocalWeightedCount_nonneg
    {count : ℕ → ℝ} (hcount : ∀ n, 0 ≤ count n) (n : ℕ) :
    0 ≤ pntDyadicReciprocalWeightedCount count n := by
  exact div_nonneg (hcount n) (by positivity)

theorem summable_pntDyadicReciprocalWeightedCount_of_eventually_le
    {count : ℕ → ℝ} {C sigma : ℝ}
    (hcount : ∀ n, 0 ≤ count n)
    (hbound :
      ∀ᶠ n : ℕ in atTop,
        pntDyadicReciprocalWeightedCount count n ≤
          pntCarlsonDyadicLogFourthMajorant C sigma n)
    (hhalf : 1 / 2 < sigma) :
    Summable (pntDyadicReciprocalWeightedCount count) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hbound
  apply (summable_nat_add_iff N).mp
  exact Summable.of_nonneg_of_le
    (fun n => pntDyadicReciprocalWeightedCount_nonneg hcount (n + N))
    (fun n => hN (n + N) (Nat.le_add_left N n))
    ((summable_nat_add_iff N).mpr
      (summable_pntCarlsonDyadicLogFourthMajorant hhalf))

/-- The actual multiplicity-weighted Carlson count at dyadic height `2^n`. -/
noncomputable def actualCarlsonDyadicCount
    (sigma : ℝ) (n : ℕ) : ℝ :=
  ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ n)

theorem actualCarlsonDyadicCount_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicCount sigma n := by
  exact Nat.cast_nonneg _

theorem dyadic_rpow_div_eq_carlsonDyadicReciprocalRatio
    (q : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ n) ^ q) / (2 : ℝ) ^ n =
      Real.exp ((q - 1) * Real.log 2) ^ n := by
  have hbase : 0 < (2 : ℝ) ^ n := by
    positivity
  calc
    (((2 : ℝ) ^ n) ^ q) / (2 : ℝ) ^ n =
        ((2 : ℝ) ^ n) ^ (q - 1) := by
      rw [Real.rpow_sub hbase, Real.rpow_one]
    _ = ((2 : ℝ) ^ (q - 1)) ^ n := by
      exact (Real.rpow_pow_comm (by norm_num) (q - 1) n).symm
    _ = Real.exp ((q - 1) * Real.log 2) ^ n := by
      rw [Real.rpow_def_of_pos (by norm_num)]
      congr 2
      ring

/-- Compatibility name used by the historical dyadic stack. -/
theorem dyadic_rpow_div_eq_pntDyadicReciprocalDensityRatio
    (q : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ n) ^ q) / (2 : ℝ) ^ n =
      pntDyadicReciprocalDensityRatio q ^ n := by
  simpa only [pntDyadicReciprocalDensityRatio] using
    dyadic_rpow_div_eq_carlsonDyadicReciprocalRatio q n

theorem carlsonDyadicModel_div_eq_logFourthMajorant
    (C sigma : ℝ) (n : ℕ) :
    (C * ‖
        (((2 : ℝ) ^ n) ^
            pntCarlsonClassicalDensityExponent sigma) *
          (Real.log ((2 : ℝ) ^ n)) ^ 4‖) /
        (2 : ℝ) ^ n =
      pntCarlsonDyadicLogFourthMajorant
        (C * (Real.log 2) ^ 4) sigma n := by
  have hpowerNonneg :
      0 ≤ ((2 : ℝ) ^ n) ^ pntCarlsonClassicalDensityExponent sigma :=
    Real.rpow_nonneg (by positivity) _
  have hlogNonneg : 0 ≤ (Real.log ((2 : ℝ) ^ n)) ^ 4 := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hpowerNonneg hlogNonneg), Real.log_pow]
  unfold pntCarlsonDyadicLogFourthMajorant
    pntCarlsonDyadicReciprocalRatio
  rw [← dyadic_rpow_div_eq_carlsonDyadicReciprocalRatio]
  ring

theorem CarlsonEventualMajorant.eventually_actualCarlsonDyadicReciprocalCount_le
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∀ᶠ n : ℕ in atTop,
      pntDyadicReciprocalWeightedCount
          (actualCarlsonDyadicCount sigma) n ≤
        pntCarlsonDyadicLogFourthMajorant
          (certificate.C * (Real.log 2) ^ 4) sigma n := by
  have hdyadic : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hdyadic.eventually certificate.bound] with n hn
  unfold pntDyadicReciprocalWeightedCount actualCarlsonDyadicCount
  calc
    (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ n) : ℝ) /
          (2 : ℝ) ^ n ≤
        (certificate.C *
          ‖((2 : ℝ) ^ n) ^ (4 * sigma * (1 - sigma)) *
            (Real.log ((2 : ℝ) ^ n)) ^ 4‖) /
          (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ = pntCarlsonDyadicLogFourthMajorant
          (certificate.C * (Real.log 2) ^ 4) sigma n := by
      simpa only [pntCarlsonClassicalDensityExponent] using
        carlsonDyadicModel_div_eq_logFourthMajorant
          certificate.C sigma n

theorem CarlsonEventualMajorant.summable_actualCarlsonDyadicReciprocalCount
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (hhalf : 1 / 2 < sigma) :
    Summable
      (pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma)) := by
  exact summable_pntDyadicReciprocalWeightedCount_of_eventually_le
    (actualCarlsonDyadicCount_nonneg sigma)
    certificate.eventually_actualCarlsonDyadicReciprocalCount_le hhalf

theorem exists_summable_actualCarlsonDyadicReciprocalCount
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable
      (pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma)) := by
  let certificate :=
    Classical.choice (exists_carlsonEventualMajorant hhalf hone)
  exact certificate.summable_actualCarlsonDyadicReciprocalCount hhalf

end PrimeNumberTheorem
