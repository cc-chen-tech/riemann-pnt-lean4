import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonQuantitativeMovingTail

/-!
# Uniform actual cubic Carlson diagonal tails

The earlier actual cubic certificate bound was eventual after fixing the PNT
scale `x`.  This module exposes the uniformity already present in its proof:
the dyadic threshold is independent of `x`, `tau`, and the finite deleted set
`S`.  Consequently the scale may move diagonally as `x = m` while the dyadic
cut also moves as `floor (log₂ (m^gamma))`.

After normalization by `m^(-2*beta)`, the genuine zeta coefficient-square tail
is bounded by the quantitative `log^5` model tail.  A strictly negative cubic
Carlson exponent therefore gives actual tail decay at the low probing height,
the balanced two-height split, and the outer contour height.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

private theorem tendsto_actualCubicDiagonal_dyadic_succ_atTop :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ (n + 1)) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro m
    refine ⟨m, ?_⟩
    intro n hn
    omega
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).comp hshift

noncomputable def actualCubicCarlsonUniformCoefficient
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) (B : ℝ) : ℝ :=
  192 * B * certificate.C * Real.log 2 ^ 5

theorem CarlsonEventualMajorant.eventually_forall_actualCubicDyadicCountMajorant_le
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ x tau : ℝ, 1 ≤ x →
      actualCubicDyadicCountMajorant B x sigma tau n ≤
        actualCubicCarlsonCertificateBlockMajorant certificate B x tau n := by
  filter_upwards
      [tendsto_actualCubicDiagonal_dyadic_succ_atTop.eventually certificate.bound]
      with n hn
  intro x tau hx
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
  have hlogOne : 0 ≤ 1 + Real.log ((2 : ℝ) ^ (n + 1) + 6) := by
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

theorem CarlsonEventualMajorant.eventually_forall_actualCubicCertificateBlock_le_logFifth
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ᶠ n : ℕ in atTop, ∀ x tau : ℝ, 1 ≤ x →
      actualCubicCarlsonCertificateBlockMajorant certificate B x tau n ≤
        actualCubicCarlsonDyadicLogFifthMajorant
          (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
          sigma n := by
  filter_upwards
      [tendsto_actualCubicDiagonal_dyadic_succ_atTop.eventually
        (eventually_ge_atTop (max 6 (Real.exp 1)))] with n hn
  intro x tau hx
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
    _ ≤ (3 * Real.log H) * K :=
      mul_le_mul_of_nonneg_right hlocalLog hK
    _ = 3 * B * certificate.C * x ^ (2 * tau) * Real.log H ^ 5 *
          (H ^ pntCarlsonClassicalDensityExponent sigma / A ^ 6) := by
      dsimp [K]
      ring
    _ = (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau)) *
          (((n + 1 : ℕ) : ℝ) ^ 5) *
          actualCubicCarlsonDyadicRatio sigma ^ (n + 1) := by
      rw [show H ^ pntCarlsonClassicalDensityExponent sigma / A ^ 6 =
          64 * actualCubicCarlsonDyadicRatio sigma ^ (n + 1) by
        simpa [H, A, actualCubicCarlsonDyadicRatio] using
          dyadic_succ_rpow_div_sixth_eq_actualCubicCarlsonRatio
            (pntCarlsonClassicalDensityExponent sigma) n]
      rw [show Real.log H ^ 5 =
          Real.log 2 ^ 5 * (((n + 1 : ℕ) : ℝ) ^ 5) by
        simpa [H] using log_dyadic_succ_pow_five n]
      unfold actualCubicCarlsonUniformCoefficient
      ring

theorem CarlsonEventualMajorant.exists_eventually_forall_actualCubicCapacity_le_logFifth
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ n : ℕ in atTop, ∀ x tau : ℝ, 1 ≤ x → ∀ S : Finset ℂ,
        actualCubicDyadicStripSquareCapacityExcluding x sigma tau n S ≤
          actualCubicCarlsonDyadicLogFifthMajorant
            (actualCubicCarlsonUniformCoefficient certificate B * x ^ (2 * tau))
            sigma n := by
  rcases exists_actualCubicDyadicStripSquareCapacityExcluding_le_count with
    ⟨B, hB, hcapacity⟩
  have hcount := certificate.eventually_forall_actualCubicDyadicCountMajorant_le hB
  have hcertificate := certificate.eventually_forall_actualCubicCertificateBlock_le_logFifth hB
  have hheight : ∀ᶠ n : ℕ in atTop, 4 ≤ (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)).eventually
      (eventually_ge_atTop 4)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hcount, hcertificate, hheight] with n hcountn hcertn hn
  intro x tau hx S
  exact (hcapacity x sigma tau n hx hn S).trans
    ((hcountn x tau hx).trans (hcertn x tau hx))

noncomputable def actualCubicCarlsonDiagonalTail
    (sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ∑' n : ℕ,
    actualCubicDyadicStripSquareCapacityExcluding
      (m : ℝ) sigma tau
      (n + (actualCubicDyadicPolynomialCut gamma m + 1)) S

noncomputable def actualCubicCarlsonNormalizedDiagonalTail
    (beta sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (-2 * beta) *
    actualCubicCarlsonDiagonalTail sigma tau gamma S m

theorem actualCubicCarlsonDyadicLogFifthTail_mul_coefficient
    (a C sigma : ℝ) (N : ℕ) :
    actualCubicCarlsonDyadicLogFifthTail (a * C) sigma N =
      a * actualCubicCarlsonDyadicLogFifthTail C sigma N := by
  unfold actualCubicCarlsonDyadicLogFifthTail
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold actualCubicCarlsonDyadicLogFifthMajorant
  ring

set_option maxHeartbeats 4000000 in
theorem CarlsonEventualMajorant.exists_eventually_actualCubicCarlsonDiagonalTail_le
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {gamma : ℝ} (hgamma : 0 < gamma) (tau : ℝ) (S : Finset ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ m : ℕ in atTop,
        actualCubicCarlsonDiagonalTail sigma tau gamma S m ≤
          actualCubicCarlsonDyadicLogFifthTail
            (actualCubicCarlsonUniformCoefficient certificate B *
              (m : ℝ) ^ (2 * tau)) sigma
            (actualCubicDyadicPolynomialCut gamma m) := by
  rcases certificate.exists_eventually_forall_actualCubicCapacity_le_logFifth with
    ⟨B, hB, hbound⟩
  rw [eventually_atTop] at hbound
  rcases hbound with ⟨N, hN⟩
  have hcut : ∀ᶠ m : ℕ in atTop,
      N ≤ actualCubicDyadicPolynomialCut gamma m + 1 :=
    (tendsto_actualCubicDyadicPolynomialCut_atTop hgamma).eventually
      (eventually_ge_atTop N) |>.mono (fun m hm => hm.trans (Nat.le_add_right _ _))
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcut] with m hm hmCut
  have hmReal : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  let cut := actualCubicDyadicPolynomialCut gamma m
  let actualTerm : ℕ → ℝ := fun n =>
    actualCubicDyadicStripSquareCapacityExcluding
      (m : ℝ) sigma tau (n + (cut + 1)) S
  let modelTerm : ℕ → ℝ := fun n =>
    actualCubicCarlsonDyadicLogFifthMajorant
      (actualCubicCarlsonUniformCoefficient certificate B *
        (m : ℝ) ^ (2 * tau)) sigma (n + (cut + 1))
  have hactual : Summable actualTerm := by
    exact (summable_nat_add_iff (cut + 1)).2
      (certificate.summable_actualCubicDyadicStripSquareCapacityExcluding
        hmReal S)
  have hmodel : Summable modelTerm := by
    exact (summable_nat_add_iff (cut + 1)).2
      (summable_actualCubicCarlsonDyadicLogFifthMajorant
        (actualCubicCarlsonUniformCoefficient certificate B *
          (m : ℝ) ^ (2 * tau)) sigma)
  have hpointwise : ∀ n : ℕ, actualTerm n ≤ modelTerm n := by
    intro n
    apply hN
    · exact hmCut.trans (Nat.le_add_left _ _)
    · exact hmReal
  have hsum := hactual.tsum_le_tsum hpointwise hmodel
  simpa [actualCubicCarlsonDiagonalTail,
    actualCubicCarlsonDyadicLogFifthTail, actualTerm, modelTerm, cut] using hsum

theorem CarlsonEventualMajorant.eventually_actualCubicCarlsonNormalizedDiagonalTail_le
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta gamma : ℝ} (hgamma : 0 < gamma) (tau : ℝ) (S : Finset ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ᶠ m : ℕ in atTop,
        actualCubicCarlsonNormalizedDiagonalTail beta sigma tau gamma S m ≤
          actualCubicCarlsonNormalizedMovingLogFifthTail
            (actualCubicCarlsonUniformCoefficient certificate B)
            beta tau sigma gamma m := by
  rcases certificate.exists_eventually_actualCubicCarlsonDiagonalTail_le
      hgamma tau S with ⟨B, hB, htail⟩
  refine ⟨B, hB, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), htail] with m hm hmTail
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hnorm : 0 ≤ (m : ℝ) ^ (-2 * beta) :=
    Real.rpow_nonneg hmpos.le _
  unfold actualCubicCarlsonNormalizedDiagonalTail
  calc
    (m : ℝ) ^ (-2 * beta) *
        actualCubicCarlsonDiagonalTail sigma tau gamma S m ≤
      (m : ℝ) ^ (-2 * beta) *
        actualCubicCarlsonDyadicLogFifthTail
          (actualCubicCarlsonUniformCoefficient certificate B *
            (m : ℝ) ^ (2 * tau)) sigma
          (actualCubicDyadicPolynomialCut gamma m) :=
      mul_le_mul_of_nonneg_left hmTail hnorm
    _ = (m : ℝ) ^ (-2 * beta) *
        ((m : ℝ) ^ (2 * tau) *
          actualCubicCarlsonDyadicLogFifthTail
            (actualCubicCarlsonUniformCoefficient certificate B) sigma
            (actualCubicDyadicPolynomialCut gamma m)) := by
      rw [show actualCubicCarlsonUniformCoefficient certificate B *
            (m : ℝ) ^ (2 * tau) =
          (m : ℝ) ^ (2 * tau) *
            actualCubicCarlsonUniformCoefficient certificate B by ring]
      rw [actualCubicCarlsonDyadicLogFifthTail_mul_coefficient]
    _ = ((m : ℝ) ^ (-2 * beta) * (m : ℝ) ^ (2 * tau)) *
          actualCubicCarlsonDyadicLogFifthTail
            (actualCubicCarlsonUniformCoefficient certificate B) sigma
            (actualCubicDyadicPolynomialCut gamma m) := by ring
    _ = actualCubicCarlsonNormalizedMovingLogFifthTail
          (actualCubicCarlsonUniformCoefficient certificate B)
          beta tau sigma gamma m := by
      unfold actualCubicCarlsonNormalizedMovingLogFifthTail
      rw [← Real.rpow_add hmpos]
      congr 1
      ring

theorem actualCubicCarlsonNormalizedDiagonalTail_nonneg
    (beta sigma tau gamma : ℝ) (S : Finset ℂ) (m : ℕ) :
    0 ≤ actualCubicCarlsonNormalizedDiagonalTail beta sigma tau gamma S m := by
  unfold actualCubicCarlsonNormalizedDiagonalTail
    actualCubicCarlsonDiagonalTail
  apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
  apply tsum_nonneg
  intro n
  unfold actualCubicDyadicStripSquareCapacityExcluding
  positivity

theorem CarlsonEventualMajorant.tendsto_actualCubicCarlsonNormalizedDiagonalTail_zero
    {sigma : ℝ} (certificate : CarlsonEventualMajorant sigma)
    {beta tau gamma : ℝ} (hgamma : 0 < gamma)
    (hexponent : cubicCarlsonL2BlockExponent beta sigma tau gamma < 0)
    (S : Finset ℂ) :
    Tendsto
      (actualCubicCarlsonNormalizedDiagonalTail beta sigma tau gamma S)
      atTop (nhds 0) := by
  rcases certificate.eventually_actualCubicCarlsonNormalizedDiagonalTail_le
      hgamma tau S with ⟨B, hB, hbound⟩
  have hcoefficient :
      0 ≤ actualCubicCarlsonUniformCoefficient certificate B := by
    unfold actualCubicCarlsonUniformCoefficient
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) hB)
        certificate.C_nonneg)
      (pow_nonneg (Real.log_nonneg (by norm_num)) 5)
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun m =>
      actualCubicCarlsonNormalizedDiagonalTail_nonneg
        beta sigma tau gamma S m)
    hbound
    (tendsto_actualCubicCarlsonNormalizedMovingLogFifthTail_zero
      hcoefficient hgamma hexponent)

theorem exists_jointTwoHeightParameters_with_actualCubicCarlsonDiagonalTails
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      0 < gammaLow ∧ gammaLow ≤ alpha ∧
      0 < gammaHigh ∧ gammaHigh < alpha ∧ 0 < alpha ∧
      ∀ certificate : CarlsonEventualMajorant sigma, ∀ S : Finset ℂ,
        Tendsto
          (actualCubicCarlsonNormalizedDiagonalTail
            beta sigma tau gammaLow S) atTop (nhds 0) ∧
        Tendsto
          (actualCubicCarlsonNormalizedDiagonalTail
            beta sigma tau gammaHigh S) atTop (nhds 0) ∧
        Tendsto
          (actualCubicCarlsonNormalizedDiagonalTail
            beta sigma tau alpha S) atTop (nhds 0) := by
  obtain ⟨sigma, tau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigma, hsigmaTau, htauBeta, hsigmaOne,
      halphaContour, halpha, halphaOne,
      hgammaLowEq, hgammaLow, hgammaLowAlpha,
      hgammaHighEq, hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowContour, hhighContour, htwoLow, htwoHigh,
      hcubicLow, hcubicHigh, hcubicAlpha⟩ :=
    exists_jointTwoHeightTargetAmplitudeParameters_with_cubicL2
      hbeta hbetaOne
  refine ⟨sigma, tau, alpha, gammaLow, gammaHigh,
    hsigma, hsigmaTau, htauBeta,
    hgammaLow, hgammaLowAlpha, hgammaHigh, hgammaHighAlpha, halpha, ?_⟩
  intro certificate S
  exact ⟨
    certificate.tendsto_actualCubicCarlsonNormalizedDiagonalTail_zero
      hgammaLow hcubicLow S,
    certificate.tendsto_actualCubicCarlsonNormalizedDiagonalTail_zero
      hgammaHigh hcubicHigh S,
    certificate.tendsto_actualCubicCarlsonNormalizedDiagonalTail_zero
      halpha hcubicAlpha S⟩

end PrimeNumberTheorem
