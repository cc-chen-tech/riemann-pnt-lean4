import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonLogFifthSummability

/-!
# Summability of actual certificate-controlled cubic blocks

This module compresses the raw Carlson certificate block into the canonical
log-fifth geometric majorant and concludes summability after deleting any
finite exceptional zero set.
-/

namespace PrimeNumberTheorem

open Filter

private theorem tendsto_dyadic_succ_atTop :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro m
    refine ⟨m, ?_⟩
    intro n hn
    omega
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp hshift

/-- Once `H` is large enough, the local multiplicity logarithm costs only one
additional power of `log H`. -/
theorem one_add_log_add_six_le_three_mul_log
    {H : ℝ} (hH6 : 6 ≤ H) (hlogOne : 1 ≤ Real.log H) :
    1 + Real.log (H + 6) ≤ 3 * Real.log H := by
  have hHpos : 0 < H := by linarith
  have hlogTwo : Real.log 2 ≤ Real.log H :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogAdd : Real.log (H + 6) ≤ Real.log (2 * H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogMul : Real.log (2 * H) = Real.log 2 + Real.log H := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hHpos.ne']
  rw [hlogMul] at hlogAdd
  linarith

/-- Exact dyadic identity converting the certificate power divided by six
lower-endpoint powers into the cubic geometric ratio. -/
theorem dyadic_succ_rpow_div_sixth_eq_actualCubicCarlsonRatio
    (q : ℝ) (n : ℕ) :
    (((2 : ℝ) ^ (n + 1)) ^ q) / (((2 : ℝ) ^ n) ^ 6) =
      64 * pntDyadicReciprocalDensityRatio (q - 5) ^ (n + 1) := by
  let A : ℝ := (2 : ℝ) ^ n
  let H : ℝ := (2 : ℝ) ^ (n + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hHA : H = 2 * A := by
    dsimp [H, A]
    rw [pow_succ]
    ring
  have hratio :=
    dyadic_rpow_div_eq_pntDyadicReciprocalDensityRatio (q - 5) (n + 1)
  change H ^ q / A ^ 6 = _
  calc
    H ^ q / A ^ 6 = 64 * (H ^ (q - 5) / H) := by
      rw [Real.rpow_sub hH]
      norm_num [Real.rpow_natCast]
      rw [hHA]
      field_simp [hA.ne']
      <;> ring
    _ = 64 * pntDyadicReciprocalDensityRatio (q - 5) ^ (n + 1) := by
      rw [hratio]

/-- On dyadic upper endpoints, the fifth logarithmic power is exactly a degree
five polynomial in the shifted shell index. -/
theorem log_dyadic_succ_pow_five
    (n : ℕ) :
    Real.log ((2 : ℝ) ^ (n + 1)) ^ 5 =
      (Real.log 2) ^ 5 * (((n + 1 : ℕ) : ℝ) ^ 5) := by
  rw [Real.log_pow]
  ring

/-- The raw actual Carlson certificate block is eventually bounded by the
canonical log-fifth majorant with a completely explicit constant. -/
theorem CarlsonEventualMajorant.eventually_actualCubicCertificateBlock_le_logFifth
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B x tau : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x) :
    ∀ᶠ n : ℕ in atTop,
      actualCubicCarlsonCertificateBlockMajorant certificate B x tau n ≤
        actualCubicCarlsonDyadicLogFifthMajorant
          (192 * B * certificate.C * x ^ (2 * tau) * (Real.log 2) ^ 5)
          sigma n := by
  filter_upwards
      [tendsto_dyadic_succ_atTop.eventually
        (eventually_ge_atTop (max 6 (Real.exp 1)))] with n hn
  let A : ℝ := (2 : ℝ) ^ n
  let H : ℝ := (2 : ℝ) ^ (n + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  have hH6 : 6 ≤ H := (le_max_left _ _).trans hn
  have hexp : Real.exp 1 ≤ H := (le_max_right _ _).trans hn
  have hlogOne : 1 ≤ Real.log H :=
    (Real.le_log_iff_exp_le hH).mpr hexp
  have hlocalLog : 1 + Real.log (H + 6) ≤ 3 * Real.log H :=
    one_add_log_add_six_le_three_mul_log hH6 hlogOne
  have hlogNonneg : 0 ≤ Real.log H := zero_le_one.trans hlogOne
  have hxpow : 0 ≤ x ^ (2 * tau) := Real.rpow_nonneg (zero_le_one.trans hx) _
  have hratioNonneg :
      0 ≤ H ^ pntCarlsonClassicalDensityExponent sigma / A ^ 6 :=
    div_nonneg (Real.rpow_nonneg hH.le _) (by positivity)
  let K : ℝ :=
    B * certificate.C * x ^ (2 * tau) * Real.log H ^ 4 *
      (H ^ pntCarlsonClassicalDensityExponent sigma / A ^ 6)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hB certificate.C_nonneg) hxpow)
          (pow_nonneg hlogNonneg 4))
      hratioNonneg
  unfold actualCubicCarlsonCertificateBlockMajorant
    actualCubicCarlsonDyadicLogFifthMajorant
  change
    (x ^ (2 * tau) / A ^ 4) *
        (B * (1 + Real.log (H + 6)) *
          ((certificate.C *
            (H ^ pntCarlsonClassicalDensityExponent sigma * Real.log H ^ 4)) /
            A ^ 2)) ≤ _
  calc
    (x ^ (2 * tau) / A ^ 4) *
        (B * (1 + Real.log (H + 6)) *
          ((certificate.C *
            (H ^ pntCarlsonClassicalDensityExponent sigma * Real.log H ^ 4)) /
            A ^ 2)) = (1 + Real.log (H + 6)) * K := by
      dsimp [K]
      field_simp [hA.ne']
      <;> ring
    _ ≤ (3 * Real.log H) * K :=
      mul_le_mul_of_nonneg_right hlocalLog hK
    _ = 3 * B * certificate.C * x ^ (2 * tau) * Real.log H ^ 5 *
          (H ^ pntCarlsonClassicalDensityExponent sigma / A ^ 6) := by
      dsimp [K]
      ring
    _ = (192 * B * certificate.C * x ^ (2 * tau) * (Real.log 2) ^ 5) *
          (((n + 1 : ℕ) : ℝ) ^ 5) *
          actualCubicCarlsonDyadicRatio sigma ^ (n + 1) := by
      rw [show H ^ pntCarlsonClassicalDensityExponent sigma / A ^ 6 =
          64 * actualCubicCarlsonDyadicRatio sigma ^ (n + 1) by
        simpa [H, A, actualCubicCarlsonDyadicRatio] using
          dyadic_succ_rpow_div_sixth_eq_actualCubicCarlsonRatio
            (pntCarlsonClassicalDensityExponent sigma) n]
      rw [show Real.log H ^ 5 =
          (Real.log 2) ^ 5 * (((n + 1 : ℕ) : ℝ) ^ 5) by
        simpa [H] using log_dyadic_succ_pow_five n]
      ring

/-- After deleting any finite exceptional zero set, the genuine actual cubic
coefficient-square dyadic block sequence is summable. -/
theorem CarlsonEventualMajorant.summable_actualCubicDyadicStripSquareCapacityExcluding
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ) :
    Summable (fun n =>
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S) := by
  rcases actualCubicDyadicStripSquareCapacityExcluding_le_certificateBlock
      certificate (x := x) (tau := tau) hx S with ⟨B, hB, hcapacity⟩
  have hcertificate :=
    certificate.eventually_actualCubicCertificateBlock_le_logFifth
      (tau := tau) hB hx
  have hheight : ∀ᶠ n : ℕ in atTop, 4 ≤ (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).eventually
      (eventually_ge_atTop 4)
  have hbound : ∀ᶠ n : ℕ in atTop,
      actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
        actualCubicCarlsonDyadicLogFifthMajorant
          (192 * B * certificate.C * x ^ (2 * tau) * (Real.log 2) ^ 5)
          sigma n := by
    filter_upwards [hcapacity, hcertificate, hheight] with n hcap hcert hn
    exact (hcap hn).trans hcert
  apply summable_of_eventually_le_actualCubicCarlsonDyadicLogFifthMajorant
  · intro n
    unfold actualCubicDyadicStripSquareCapacityExcluding
    positivity
  · exact hbound

end PrimeNumberTheorem
