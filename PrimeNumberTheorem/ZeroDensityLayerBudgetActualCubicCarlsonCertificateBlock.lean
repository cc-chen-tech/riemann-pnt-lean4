import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail

/-!
# Actual cubic blocks under a Carlson certificate

This module closes the gap between the abstract dyadic count appearing in the
actual cubic square-capacity theorem and a genuine Carlson eventual majorant.
The displayed bound retains both logarithmic losses:

* one logarithm from linear-to-square analytic multiplicity control;
* four logarithms from Carlson's zero-density estimate.

Thus the actual block has an asymptotic log-fifth loss and polynomial dyadic
exponent `q(sigma) - 6`, which is at most `-5`.
-/

namespace PrimeNumberTheorem

open Filter

/-- The raw certificate majorant for one actual cubic dyadic block.  Keeping
the two logarithmic factors separate records their different origins. -/
noncomputable def actualCubicCarlsonCertificateBlockMajorant
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    (B x tau : ℝ) (n : ℕ) : ℝ :=
  (x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4) *
    (B * (1 + Real.log ((2 : ℝ) ^ (n + 1) + 6)) *
      ((certificate.C *
          (((2 : ℝ) ^ (n + 1)) ^
              pntCarlsonClassicalDensityExponent sigma *
            Real.log ((2 : ℝ) ^ (n + 1)) ^ 4)) /
        ((2 : ℝ) ^ n) ^ 2))

/-- A genuine Carlson certificate eventually bounds the actual cubic count
majorant.  This is the direct bridge from the real zeta count to the L2 block. -/
theorem CarlsonEventualMajorant.eventually_actualCubicDyadicCountMajorant_le
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B x tau : ℝ} (hB : 0 ≤ B) (hx : 1 ≤ x) :
    ∀ᶠ n : ℕ in atTop,
      actualCubicDyadicCountMajorant B x sigma tau n ≤
        actualCubicCarlsonCertificateBlockMajorant certificate B x tau n := by
  have hdyadic :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
    have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro m
      refine ⟨m, ?_⟩
      intro n hn
      omega
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp hshift
  filter_upwards [hdyadic.eventually certificate.bound] with n hn
  let T : ℝ := (2 : ℝ) ^ (n + 1)
  have hTpos : 0 < T := by dsimp [T]; positivity
  have hpower : 0 ≤ T ^ pntCarlsonClassicalDensityExponent sigma :=
    Real.rpow_nonneg hTpos.le _
  have hlog4 : 0 ≤ Real.log T ^ 4 := by positivity
  have hcount : actualCarlsonDyadicCount sigma (n + 1) ≤
      certificate.C *
        (T ^ pntCarlsonClassicalDensityExponent sigma * Real.log T ^ 4) := by
    unfold actualCarlsonDyadicCount
    calc
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
          certificate.C *
            ‖T ^ (4 * sigma * (1 - sigma)) * Real.log T ^ 4‖ := by
        simpa [T] using hn
      _ = certificate.C *
          (T ^ pntCarlsonClassicalDensityExponent sigma * Real.log T ^ 4) := by
        rw [Real.norm_eq_abs]
        change certificate.C *
          |T ^ pntCarlsonClassicalDensityExponent sigma * Real.log T ^ 4| = _
        rw [abs_of_nonneg (mul_nonneg hpower hlog4)]
  have houter : 0 ≤ x ^ (2 * tau) / ((2 : ℝ) ^ n) ^ 4 :=
    div_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _) (by positivity)
  have hlogOne :
      0 ≤ 1 + Real.log ((2 : ℝ) ^ (n + 1) + 6) := by
    have hpowPos : 0 < (2 : ℝ) ^ (n + 1) := by positivity
    have : 1 < (2 : ℝ) ^ (n + 1) + 6 := by linarith
    have := Real.log_pos this
    linarith
  unfold actualCubicDyadicCountMajorant
    actualCubicCarlsonCertificateBlockMajorant
  dsimp [T] at hcount
  apply mul_le_mul_of_nonneg_left _ houter
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB hlogOne)
  exact div_le_div_of_nonneg_right hcount (by positivity)

/-- Combining the existing finite-set monotonicity/capacity theorem with a
certificate-controlled block requires no density theorem specialized to the
deleted set. -/
theorem actualCubicDyadicStripSquareCapacityExcluding_le_certificateBlock
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {x tau : ℝ} (hx : 1 ≤ x) (S : Finset ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ n : ℕ in atTop,
        4 ≤ (2 : ℝ) ^ n →
          actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
            actualCubicCarlsonCertificateBlockMajorant
              certificate B x tau n := by
  rcases exists_actualCubicDyadicStripSquareCapacityExcluding_le_count with
    ⟨B, hB, hcapacity⟩
  refine ⟨B, hB, ?_⟩
  filter_upwards [certificate.eventually_actualCubicDyadicCountMajorant_le hB hx]
    with n hcertificate
  intro hn
  exact (hcapacity x sigma tau n hx hn S).trans hcertificate

/-- The polynomial exponent in the certificate block is strictly negative;
indeed the cubic denominator leaves at least five powers of dyadic decay. -/
theorem actualCubicCarlsonCertificatePolynomialExponent_le_neg_five
    (sigma : ℝ) :
    pntCarlsonClassicalDensityExponent sigma - 6 ≤ -5 :=
  pntCarlsonClassicalDensityExponent_sub_six_le_neg_five sigma

end PrimeNumberTheorem
