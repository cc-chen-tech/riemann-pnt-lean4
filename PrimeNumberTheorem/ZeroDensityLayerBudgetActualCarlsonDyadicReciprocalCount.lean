import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonDyadicEventualSummability

/-!
# Actual Carlson dyadic reciprocal count

This module specializes the abstract dyadic summability interface to the
project's multiplicity-weighted zeta zero count

`zeroDensityCount sigma (2^n)`.

The full Carlson `(log T)^4` loss is retained.  Dividing by the dyadic height
turns the power factor into the strict geometric ratio attached to
`4 * sigma * (1 - sigma) < 1`.
-/

namespace PrimeNumberTheorem

open Filter

/-- The actual multiplicity-weighted Carlson count at dyadic height `2^n`. -/
noncomputable def actualCarlsonDyadicCount
    (sigma : ℝ) (n : ℕ) : ℝ :=
  ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ n)

theorem actualCarlsonDyadicCount_nonneg (sigma : ℝ) (n : ℕ) :
    0 ≤ actualCarlsonDyadicCount sigma n := by
  exact Nat.cast_nonneg _

/-- Exact dyadic power identity behind the reciprocal-height gain. -/
theorem dyadic_rpow_div_eq_pntDyadicReciprocalDensityRatio
    (q : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ n) ^ q) / (2 : ℝ) ^ n =
      pntDyadicReciprocalDensityRatio q ^ n := by
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
    _ = pntDyadicReciprocalDensityRatio q ^ n := by
      rfl

/-- Carlson's polynomial-log model, divided by the dyadic height, is exactly
the summable log-fourth majorant used by the abstract transfer. -/
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
      0 ≤ ((2 : ℝ) ^ n) ^
        pntCarlsonClassicalDensityExponent sigma :=
    Real.rpow_nonneg (by positivity) _
  have hlogNonneg :
      0 ≤ (Real.log ((2 : ℝ) ^ n)) ^ 4 :=
    by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg hpowerNonneg hlogNonneg), Real.log_pow]
  unfold pntCarlsonDyadicLogFourthMajorant
    pntCarlsonDyadicReciprocalRatio
  rw [← dyadic_rpow_div_eq_pntDyadicReciprocalDensityRatio]
  ring

/-- An actual Carlson certificate yields the eventual reciprocal-height
dyadic count bound with its full logarithmic loss. -/
theorem CarlsonEventualMajorant.eventually_actualCarlsonDyadicReciprocalCount_le
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∀ᶠ n : ℕ in atTop,
      pntDyadicReciprocalWeightedCount
          (actualCarlsonDyadicCount sigma) n ≤
        pntCarlsonDyadicLogFourthMajorant
          (certificate.C * (Real.log 2) ^ 4) sigma n := by
  have hdyadic :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  filter_upwards [hdyadic.eventually certificate.bound] with n hn
  unfold pntDyadicReciprocalWeightedCount actualCarlsonDyadicCount
  calc
    (ZeroDensity.zeroDensityCount sigma ((2 : ℝ) ^ n) : ℝ) /
          (2 : ℝ) ^ n ≤
        (certificate.C *
          ‖((2 : ℝ) ^ n) ^
              (4 * sigma * (1 - sigma)) *
            (Real.log ((2 : ℝ) ^ n)) ^ 4‖) /
          (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ =
        pntCarlsonDyadicLogFourthMajorant
          (certificate.C * (Real.log 2) ^ 4) sigma n := by
      simpa only [pntCarlsonClassicalDensityExponent] using
        carlsonDyadicModel_div_eq_logFourthMajorant
          certificate.C sigma n

/-- The actual reciprocal-height Carlson counts at dyadic heights are
summable in every strict strip to the right of the critical line. -/
theorem CarlsonEventualMajorant.summable_actualCarlsonDyadicReciprocalCount
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (hhalf : 1 / 2 < sigma) :
    Summable
      (pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma)) := by
  exact
    summable_pntDyadicReciprocalWeightedCount_of_eventually_le
      (actualCarlsonDyadicCount_nonneg sigma)
      certificate.eventually_actualCarlsonDyadicReciprocalCount_le
      hhalf

/-- Carlson's theorem itself supplies a summability certificate for the
actual dyadic reciprocal count at every fixed `1/2 < sigma < 1`. -/
theorem exists_summable_actualCarlsonDyadicReciprocalCount
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    Summable
      (pntDyadicReciprocalWeightedCount
        (actualCarlsonDyadicCount sigma)) := by
  let certificate :=
    Classical.choice (exists_carlsonEventualMajorant hhalf hone)
  exact certificate.summable_actualCarlsonDyadicReciprocalCount hhalf

end PrimeNumberTheorem
