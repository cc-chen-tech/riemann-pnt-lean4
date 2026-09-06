import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonMovingTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicTwoHeightDyadicCuts
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicTwoHeightL2Tail
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonLogAbsorption

/-!
# Quantitative moving cubic Carlson tails

This module upgrades fixed-coefficient summability to a moving dyadic cut.
The shifted fifth-logarithmic geometric tail is bounded without changing the
polynomial exponent.  At `N = floor (log₂ (x^gamma))`, the normalized bound is

`const * x^(2*(tau-beta) + gamma*(q(sigma)-6)) * (log x)^5`.

Thus a strictly negative cubic Carlson block exponent absorbs the exact
`log^5` loss.  Equality is only critical and is deliberately not claimed to
decay.  The final theorem applies the same construction at `gammaLow`,
`gammaHigh`, and the outer height exponent `alpha` supplied by the joint
two-height parameter theorem.
-/

namespace PrimeNumberTheorem

open Filter Topology
open scoped BigOperators

noncomputable def actualCubicCarlsonLogFifthCore (sigma : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℝ) ^ 5 * actualCubicCarlsonDyadicRatio sigma ^ (n + 1)

noncomputable def actualCubicCarlsonLogFifthConstant (sigma : ℝ) : ℝ :=
  ∑' n : ℕ, actualCubicCarlsonLogFifthCore sigma n

noncomputable def actualCubicCarlsonDyadicLogFifthTail
    (C sigma : ℝ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, actualCubicCarlsonDyadicLogFifthMajorant C sigma (n + (N + 1))

theorem summable_actualCubicCarlsonLogFifthCore (sigma : ℝ) :
    Summable (actualCubicCarlsonLogFifthCore sigma) := by
  have hr : ‖actualCubicCarlsonDyadicRatio sigma‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (actualCubicCarlsonDyadicRatio_pos sigma)]
    exact actualCubicCarlsonDyadicRatio_lt_one sigma
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 5 * actualCubicCarlsonDyadicRatio sigma ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hr
  have hshift : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ 5 *
        actualCubicCarlsonDyadicRatio sigma ^ (n + 1))) := by
    simpa only using (summable_nat_add_iff 1).mpr hbase
  have hfun : actualCubicCarlsonLogFifthCore sigma =
      (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 5 *
        actualCubicCarlsonDyadicRatio sigma ^ (n + 1))) := by
    funext n
    simp only [actualCubicCarlsonLogFifthCore, Nat.cast_add, Nat.cast_one]
  rw [hfun]
  exact hshift

theorem actualCubicCarlsonLogFifthConstant_nonneg (sigma : ℝ) :
    0 ≤ actualCubicCarlsonLogFifthConstant sigma := by
  apply tsum_nonneg
  intro n
  unfold actualCubicCarlsonLogFifthCore
  exact mul_nonneg (pow_nonneg (by positivity) 5)
    (pow_nonneg (actualCubicCarlsonDyadicRatio_pos sigma).le (n + 1))

theorem actualCubicCarlsonDyadicLogFifthTail_le
    {C : ℝ} (hC : 0 ≤ C) (sigma : ℝ) (N : ℕ) :
    actualCubicCarlsonDyadicLogFifthTail C sigma N ≤
      (C * (N + 2 : ℝ) ^ 5 * actualCubicCarlsonDyadicRatio sigma ^ (N + 1)) *
        actualCubicCarlsonLogFifthConstant sigma := by
  let r := actualCubicCarlsonDyadicRatio sigma
  have hr0 : 0 ≤ r := (actualCubicCarlsonDyadicRatio_pos sigma).le
  have htail : Summable
      (fun n : ℕ => actualCubicCarlsonDyadicLogFifthMajorant C sigma (n + (N + 1))) :=
    (summable_nat_add_iff (N + 1)).2
      (summable_actualCubicCarlsonDyadicLogFifthMajorant C sigma)
  have hcore := summable_actualCubicCarlsonLogFifthCore sigma
  have hfactor : Summable
      (fun n : ℕ =>
        (C * (N + 2 : ℝ) ^ 5 * r ^ (N + 1)) *
          actualCubicCarlsonLogFifthCore sigma n) :=
    hcore.mul_left _
  have hpointwise : ∀ n : ℕ,
      actualCubicCarlsonDyadicLogFifthMajorant C sigma (n + (N + 1)) ≤
        (C * (N + 2 : ℝ) ^ 5 * r ^ (N + 1)) *
          actualCubicCarlsonLogFifthCore sigma n := by
    intro n
    have hcast : (n + (N + 1) + 1 : ℝ) ≤ (n + 1 : ℝ) * (N + 2 : ℝ) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hpow : r ^ (n + (N + 1) + 1) = r ^ (N + 1) * r ^ (n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    simp only [actualCubicCarlsonDyadicLogFifthMajorant,
      actualCubicCarlsonLogFifthCore, r]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [hpow]
    have hpowIndex : (n + (N + 1) + 1 : ℝ) ^ 5 ≤
        ((n + 1 : ℝ) * (N + 2 : ℝ)) ^ 5 := by
      exact pow_le_pow_left₀ (by positivity) hcast 5
    calc
      C * (n + (N + 1) + 1 : ℝ) ^ 5 * (r ^ (N + 1) * r ^ (n + 1)) ≤
          C * (((n + 1 : ℝ) * (N + 2 : ℝ)) ^ 5) *
            (r ^ (N + 1) * r ^ (n + 1)) := by
              gcongr
      _ = (C * (N + 2 : ℝ) ^ 5 * r ^ (N + 1)) *
          ((n + 1 : ℝ) ^ 5 * r ^ (n + 1)) := by ring
  have hsum := htail.tsum_le_tsum hpointwise hfactor
  simpa [actualCubicCarlsonDyadicLogFifthTail,
    actualCubicCarlsonLogFifthConstant, r, tsum_mul_left] using hsum

theorem actualCubicCarlsonDyadicRatio_pow_cut_succ_le
    (gamma sigma : ℝ)
    {m : ℕ} (hm : 1 ≤ m) :
    actualCubicCarlsonDyadicRatio sigma ^
        (actualCubicDyadicPolynomialCut gamma m + 1) ≤
      (m : ℝ) ^
        (gamma * (carlsonTwoHeightDensityExponent sigma - 6)) := by
  let q := pntCarlsonClassicalDensityExponent sigma
  let L := Real.log (carlsonPolynomialHeight gamma (m : ℝ)) / Real.log 2
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLlt : L < (actualCubicDyadicPolynomialCut gamma m : ℝ) + 1 := by
    simpa [L, actualCubicDyadicPolynomialCut] using (Nat.lt_floor_add_one L)
  have hheightLog :
      Real.log (carlsonPolynomialHeight gamma (m : ℝ)) =
        gamma * Real.log (m : ℝ) := by
    simpa [carlsonPolynomialHeight] using Real.log_rpow hmpos gamma
  have hloglt :
      Real.log (carlsonPolynomialHeight gamma (m : ℝ)) <
        ((actualCubicDyadicPolynomialCut gamma m : ℝ) + 1) * Real.log 2 := by
    exact (div_lt_iff₀ hlogTwo).mp hLlt
  have hqneg : q - 6 < 0 := by
    have hq := pntCarlsonClassicalDensityExponent_le_one sigma
    dsimp [q]
    linarith
  have hscaled :
      (q - 6) * (((actualCubicDyadicPolynomialCut gamma m : ℝ) + 1) * Real.log 2) ≤
        (q - 6) * Real.log (carlsonPolynomialHeight gamma (m : ℝ)) :=
    mul_le_mul_of_nonpos_left hloglt.le hqneg.le
  rw [show actualCubicCarlsonDyadicRatio sigma =
      Real.exp ((q - 6) * Real.log 2) by
        unfold actualCubicCarlsonDyadicRatio
          pntDyadicReciprocalDensityRatio
        congr 1
        dsimp [q]
        ring]
  rw [← Real.exp_nat_mul]
  rw [Real.rpow_def_of_pos hmpos]
  rw [Real.exp_le_exp]
  rw [hheightLog] at hscaled
  simp only [Nat.cast_add, Nat.cast_one]
  unfold carlsonTwoHeightDensityExponent
  dsimp [q, pntCarlsonClassicalDensityExponent] at hscaled
  dsimp [q, pntCarlsonClassicalDensityExponent]
  nlinarith

theorem eventually_actualCubicDyadicPolynomialCut_add_two_le_log
    {gamma : ℝ} (hgamma : 0 < gamma) :
    ∀ᶠ m : ℕ in atTop,
      (actualCubicDyadicPolynomialCut gamma m + 2 : ℝ) ≤
        (gamma / Real.log 2 + 2) * Real.log (m : ℝ) := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (Real.exp 1))] with m hm
  have hmReal : Real.exp 1 ≤ (m : ℝ) := by
    exact (Nat.le_ceil (Real.exp 1)).trans (by exact_mod_cast hm)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos 1).trans_le hmReal
  have hlogOne : 1 ≤ Real.log (m : ℝ) :=
    (Real.le_log_iff_exp_le hmpos).2 (by simpa using hmReal)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hheightLog :
      Real.log (carlsonPolynomialHeight gamma (m : ℝ)) =
        gamma * Real.log (m : ℝ) := by
    simpa [carlsonPolynomialHeight] using Real.log_rpow hmpos gamma
  have hLnonneg :
      0 ≤ Real.log (carlsonPolynomialHeight gamma (m : ℝ)) / Real.log 2 := by
    rw [hheightLog]
    positivity
  have hfloor := Nat.floor_le hLnonneg
  change (actualCubicDyadicPolynomialCut gamma m : ℝ) + 2 ≤ _
  have hcut :
      (actualCubicDyadicPolynomialCut gamma m : ℝ) ≤
        gamma * Real.log (m : ℝ) / Real.log 2 := by
    simpa [actualCubicDyadicPolynomialCut, hheightLog] using hfloor
  calc
    (actualCubicDyadicPolynomialCut gamma m : ℝ) + 2 ≤
        gamma * Real.log (m : ℝ) / Real.log 2 + 2 := by linarith
    _ ≤ (gamma / Real.log 2 + 2) * Real.log (m : ℝ) := by
      have hgammaLog : 0 ≤ gamma / Real.log 2 := by positivity
      rw [show gamma * Real.log (m : ℝ) / Real.log 2 =
        (gamma / Real.log 2) * Real.log (m : ℝ) by ring]
      nlinarith

theorem tendsto_rpow_mul_log_pow_atTop_nhds_zero
    {exponent epsilon : ℝ} (k : ℕ)
    (hepsilon : 0 < epsilon)
    (hmargin : exponent + epsilon < 0) :
    Tendsto
      (fun x : ℝ => x ^ exponent * Real.log x ^ k)
      atTop (nhds 0) := by
  have hlogRpow :
      (fun x : ℝ => Real.log x ^ (k : ℝ))
        =o[atTop] (fun x => x ^ epsilon) :=
    isLittleO_log_rpow_rpow_atTop k hepsilon
  have hlog :
      (fun x : ℝ => Real.log x ^ k)
        =o[atTop] (fun x => x ^ epsilon) := by
    refine hlogRpow.congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall fun x => Real.rpow_natCast (Real.log x) k
  have hraw :
      (fun x : ℝ => Real.log x ^ k * x ^ exponent)
        =o[atTop] (fun x => x ^ epsilon * x ^ exponent) :=
    hlog.mul_isBigO
      (Asymptotics.isBigO_refl (fun x : ℝ => x ^ exponent) atTop)
  have htarget :
      (fun x : ℝ => x ^ exponent * Real.log x ^ k)
        =o[atTop] (fun x => x ^ (exponent + epsilon)) := by
    refine hraw.congr' ?_ ?_
    · exact Filter.Eventually.of_forall fun x => by ring
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.rpow_add hx]
      ring
  exact htarget.tendsto_zero_of_tendsto
    (tendsto_rpow_neg_atTop_nhds_zero hmargin)

noncomputable def actualCubicCarlsonNormalizedMovingLogFifthTail
    (C beta tau sigma gamma : ℝ) (m : ℕ) : ℝ :=
  (m : ℝ) ^ (2 * (tau - beta)) *
    actualCubicCarlsonDyadicLogFifthTail C sigma
      (actualCubicDyadicPolynomialCut gamma m)

noncomputable def actualCubicCarlsonNormalizedMovingLogFifthMajorant
    (C beta tau sigma gamma : ℝ) (m : ℕ) : ℝ :=
  (C * actualCubicCarlsonLogFifthConstant sigma *
      (gamma / Real.log 2 + 2) ^ 5) *
    (m : ℝ) ^ (cubicCarlsonL2BlockExponent beta sigma tau gamma) *
      Real.log (m : ℝ) ^ 5

theorem eventually_actualCubicCarlsonNormalizedMovingLogFifthTail_le_majorant
    {C gamma : ℝ} (hC : 0 ≤ C) (hgamma : 0 < gamma)
    (beta tau sigma : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      actualCubicCarlsonNormalizedMovingLogFifthTail
          C beta tau sigma gamma m ≤
        actualCubicCarlsonNormalizedMovingLogFifthMajorant
          C beta tau sigma gamma m := by
  filter_upwards [eventually_ge_atTop (1 : ℕ),
      eventually_actualCubicDyadicPolynomialCut_add_two_le_log hgamma] with
      m hm hcut
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hmnonneg : 0 ≤ (m : ℝ) := hmpos.le
  have hlognonneg : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hcoeff : 0 ≤ gamma / Real.log 2 + 2 := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have htail := actualCubicCarlsonDyadicLogFifthTail_le hC sigma
    (actualCubicDyadicPolynomialCut gamma m)
  have hratio := actualCubicCarlsonDyadicRatio_pow_cut_succ_le gamma sigma hm
  have hcutPow :
      (actualCubicDyadicPolynomialCut gamma m + 2 : ℝ) ^ 5 ≤
        ((gamma / Real.log 2 + 2) * Real.log (m : ℝ)) ^ 5 :=
    pow_le_pow_left₀ (by positivity) hcut 5
  have hconstantNonneg := actualCubicCarlsonLogFifthConstant_nonneg sigma
  have hratioNonneg :
      0 ≤ actualCubicCarlsonDyadicRatio sigma ^
        (actualCubicDyadicPolynomialCut gamma m + 1) :=
    pow_nonneg (actualCubicCarlsonDyadicRatio_pos sigma).le _
  unfold actualCubicCarlsonNormalizedMovingLogFifthTail
    actualCubicCarlsonNormalizedMovingLogFifthMajorant
  have hxpow : 0 ≤ (m : ℝ) ^ (2 * (tau - beta)) :=
    Real.rpow_nonneg hmnonneg _
  calc
    (m : ℝ) ^ (2 * (tau - beta)) *
        actualCubicCarlsonDyadicLogFifthTail C sigma
          (actualCubicDyadicPolynomialCut gamma m) ≤
      (m : ℝ) ^ (2 * (tau - beta)) *
        ((C * (actualCubicDyadicPolynomialCut gamma m + 2 : ℝ) ^ 5 *
          actualCubicCarlsonDyadicRatio sigma ^
            (actualCubicDyadicPolynomialCut gamma m + 1)) *
          actualCubicCarlsonLogFifthConstant sigma) :=
      mul_le_mul_of_nonneg_left htail hxpow
    _ ≤ (m : ℝ) ^ (2 * (tau - beta)) *
        ((C * (((gamma / Real.log 2 + 2) * Real.log (m : ℝ)) ^ 5) *
          ((m : ℝ) ^
            (gamma * (carlsonTwoHeightDensityExponent sigma - 6)))) *
          actualCubicCarlsonLogFifthConstant sigma) := by
      gcongr
    _ = (C * actualCubicCarlsonLogFifthConstant sigma *
          (gamma / Real.log 2 + 2) ^ 5) *
        ((m : ℝ) ^ (2 * (tau - beta)) *
          (m : ℝ) ^
            (gamma * (carlsonTwoHeightDensityExponent sigma - 6))) *
          Real.log (m : ℝ) ^ 5 := by ring
    _ = (C * actualCubicCarlsonLogFifthConstant sigma *
          (gamma / Real.log 2 + 2) ^ 5) *
        (m : ℝ) ^ cubicCarlsonL2BlockExponent beta sigma tau gamma *
          Real.log (m : ℝ) ^ 5 := by
      rw [← Real.rpow_add hmpos]
      unfold cubicCarlsonL2BlockExponent
      ring

theorem tendsto_actualCubicCarlsonNormalizedMovingLogFifthMajorant_zero
    {C beta tau sigma gamma : ℝ}
    (hexponent : cubicCarlsonL2BlockExponent beta sigma tau gamma < 0) :
    Tendsto
      (actualCubicCarlsonNormalizedMovingLogFifthMajorant
        C beta tau sigma gamma) atTop (nhds 0) := by
  let exponent := cubicCarlsonL2BlockExponent beta sigma tau gamma
  have hepsilon : 0 < -exponent / 2 := by
    dsimp [exponent]
    linarith
  have hmargin : exponent + (-exponent / 2) < 0 := by
    dsimp [exponent]
    linarith
  have hreal := tendsto_rpow_mul_log_pow_atTop_nhds_zero
    (exponent := exponent) (epsilon := -exponent / 2) 5 hepsilon hmargin
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  unfold actualCubicCarlsonNormalizedMovingLogFifthMajorant
  have hmul := hnat.const_mul
    (C * actualCubicCarlsonLogFifthConstant sigma *
      (gamma / Real.log 2 + 2) ^ 5)
  simpa [Function.comp_def, exponent, mul_assoc] using hmul

theorem tendsto_actualCubicCarlsonNormalizedMovingLogFifthTail_zero
    {C beta tau sigma gamma : ℝ}
    (hC : 0 ≤ C) (hgamma : 0 < gamma)
    (hexponent : cubicCarlsonL2BlockExponent beta sigma tau gamma < 0) :
    Tendsto
      (actualCubicCarlsonNormalizedMovingLogFifthTail
        C beta tau sigma gamma) atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_actualCubicCarlsonNormalizedMovingLogFifthMajorant_zero
      (C := C) hexponent)
  · exact Filter.Eventually.of_forall fun m => by
      unfold actualCubicCarlsonNormalizedMovingLogFifthTail
      apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
      unfold actualCubicCarlsonDyadicLogFifthTail
      apply tsum_nonneg
      intro n
      unfold actualCubicCarlsonDyadicLogFifthMajorant
      exact mul_nonneg
        (mul_nonneg hC (pow_nonneg (by positivity) 5))
        (pow_nonneg (actualCubicCarlsonDyadicRatio_pos sigma).le _)
  · exact eventually_actualCubicCarlsonNormalizedMovingLogFifthTail_le_majorant
      hC hgamma beta tau sigma

theorem exists_jointTwoHeightParameters_with_quantitative_cubicCarlsonTails
    {C beta : ℝ} (hC : 0 ≤ C)
    (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha gammaLow gammaHigh : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      0 < gammaLow ∧ gammaLow ≤ alpha ∧
      0 < gammaHigh ∧ gammaHigh < alpha ∧ 0 < alpha ∧
      Tendsto
        (actualCubicCarlsonNormalizedMovingLogFifthTail
          C beta tau sigma gammaLow) atTop (nhds 0) ∧
      Tendsto
        (actualCubicCarlsonNormalizedMovingLogFifthTail
          C beta tau sigma gammaHigh) atTop (nhds 0) ∧
      Tendsto
        (actualCubicCarlsonNormalizedMovingLogFifthTail
          C beta tau sigma alpha) atTop (nhds 0) := by
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
    hgammaLow, hgammaLowAlpha, hgammaHigh, hgammaHighAlpha, halpha,
    ?_, ?_, ?_⟩
  · exact tendsto_actualCubicCarlsonNormalizedMovingLogFifthTail_zero
      hC hgammaLow hcubicLow
  · exact tendsto_actualCubicCarlsonNormalizedMovingLogFifthTail_zero
      hC hgammaHigh hcubicHigh
  · exact tendsto_actualCubicCarlsonNormalizedMovingLogFifthTail_zero
      hC halpha hcubicAlpha

end PrimeNumberTheorem
