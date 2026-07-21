import HardyTheorem.HardyPhaseLinearizedEnergy
import HardyTheorem.HardyPhaseStationaryScale
import MathlibAux.DyadicWeightedSquareHighTail

open scoped BigOperators

open Complex

namespace HardyTheorem

open OscillatoryIntegral

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)]

/-- Above a dyadic cutoff separated by a factor of two from the stationary
scale, every subsequent dyadic block contributes another factor of `log 2`
to the Hardy phase frequency. -/
theorem highDyadicDistance_mul_logTwo_le_abs_deriv_hardyPhase
    {K k n : ℕ} (hKk : K ≤ k) (hn : 0 < n) {t : ℝ} (ht : 0 < t)
    (hscale : 2 * hardyPhaseStationaryScale t ≤ (2 : ℝ) ^ K)
    (hnlower : 2 ^ k ≤ n) :
    (((k - K + 1 : ℕ) : ℝ) * Real.log 2) ≤
      |deriv (hardyPhase n) t| := by
  let j : ℕ := k - K + 1
  have hj : 0 < j := by
    dsimp only [j]
    omega
  have hr : 0 < hardyPhaseStationaryScale t :=
    hardyPhaseStationaryScale_pos ht
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpowPos : 0 < (2 : ℝ) ^ j := by positivity
  have hpowMulScale :
      (2 : ℝ) ^ j * hardyPhaseStationaryScale t ≤ (n : ℝ) := by
    calc
      (2 : ℝ) ^ j * hardyPhaseStationaryScale t =
          (2 : ℝ) ^ (k - K) *
            (2 * hardyPhaseStationaryScale t) := by
        dsimp only [j]
        rw [pow_succ]
        ring
      _ ≤ (2 : ℝ) ^ (k - K) * (2 : ℝ) ^ K :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = (2 : ℝ) ^ k := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ (n : ℝ) := by exact_mod_cast hnlower
  have hratioLower :
      (2 : ℝ) ^ j ≤ (n : ℝ) / hardyPhaseStationaryScale t :=
    (le_div_iff₀ hr).2 hpowMulScale
  have hratioPos : 0 < (n : ℝ) / hardyPhaseStationaryScale t :=
    div_pos hnreal hr
  have hlogLower :
      Real.log ((2 : ℝ) ^ j) ≤
        Real.log ((n : ℝ) / hardyPhaseStationaryScale t) :=
    Real.log_le_log hpowPos hratioLower
  have hlogPow :
      Real.log ((2 : ℝ) ^ j) = (j : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlogPowPos : 0 < Real.log ((2 : ℝ) ^ j) := by
    rw [hlogPow]
    positivity
  have hlogRatioPos :
      0 < Real.log ((n : ℝ) / hardyPhaseStationaryScale t) :=
    hlogPowPos.trans_le hlogLower
  have hlogSwap :
      Real.log (hardyPhaseStationaryScale t / (n : ℝ)) =
        -Real.log ((n : ℝ) / hardyPhaseStationaryScale t) := by
    rw [Real.log_div hr.ne' hnreal.ne', Real.log_div hnreal.ne' hr.ne']
    ring
  rw [abs_deriv_hardyPhase_eq_abs_log_stationaryScale_div
    (Nat.ne_of_gt hn) ht, hlogSwap, abs_neg, abs_of_pos hlogRatioPos,
    ← hlogPow]
  exact hlogLower

/-- If all positive indices lie in a finite dyadic high tail beginning at
`2^K`, while twice the stationary scale is at most `2^K`, their linearized
short-window energy is bounded by an absolute constant. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_far_high_le
    (s : Finset ℕ) (K L : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : 2 * hardyPhaseStationaryScale t ≤ (2 : ℝ) ^ K)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hlower : ∀ n ∈ s, 2 ^ K ≤ n)
    (hupper : ∀ n ∈ s, n < 2 ^ L) :
    (∑ n ∈ s, Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      8 / (Real.log 2) ^ 2 := by
  let envelope : ℕ → ℝ := fun n ↦ hardyPhaseLinearizedEnvelope n delta t
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdecay : ∀ k, K ≤ k → k < L →
      ∀ n ∈ MathlibAux.dyadicBlock s k,
        (envelope n) ^ 2 ≤
          (4 / (Real.log 2) ^ 2) *
            (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹) := by
    intro k hKk hkL n hn
    have hjNat : 0 < k - K + 1 := by omega
    have hj : 0 < ((k - K + 1 : ℕ) : ℝ) := by
      exact_mod_cast hjNat
    have hnmem : n ∈ s := (MathlibAux.mem_dyadicBlock.1 hn).1
    have hnpos : 0 < n := Nat.pos_of_ne_zero (hpos n hnmem)
    have hfreq := highDyadicDistance_mul_logTwo_le_abs_deriv_hardyPhase
      hKk hnpos ht hscale (MathlibAux.mem_dyadicBlock.1 hn).2.1
    have hfreqLower :
        0 < ((k - K + 1 : ℕ) : ℝ) * Real.log 2 :=
      mul_pos hj hlogTwo
    have habs : 0 < |deriv (hardyPhase n) t| :=
      hfreqLower.trans_le hfreq
    have hfreqne : deriv (hardyPhase n) t ≠ 0 := abs_pos.mp habs
    have hquot :
        2 / |deriv (hardyPhase n) t| ≤
          2 / (((k - K + 1 : ℕ) : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_left (by norm_num) hfreqLower hfreq
    have henvelope :
        envelope n ≤ 2 / (((k - K + 1 : ℕ) : ℝ) * Real.log 2) := by
      dsimp only [envelope]
      rw [hardyPhaseLinearizedEnvelope, if_neg hfreqne]
      exact (min_le_right _ _).trans hquot
    have henvelope0 : 0 ≤ envelope n := by
      dsimp only [envelope]
      exact hardyPhaseLinearizedEnvelope_nonneg n hdelta
    calc
      (envelope n) ^ 2 ≤
          (2 / (((k - K + 1 : ℕ) : ℝ) * Real.log 2)) ^ 2 :=
        (sq_le_sq₀ henvelope0 (by positivity)).2 henvelope
      _ = (4 / (Real.log 2) ^ 2) *
          (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹) := by
        field_simp [ne_of_gt hj, ne_of_gt hlogTwo]
        ring
  have hweighted :
      (∑ n ∈ s, ((n : ℝ))⁻¹ * (envelope n) ^ 2) ≤
        8 / (Real.log 2) ^ 2 := by
    have h := MathlibAux.sum_inv_mul_sq_le_of_high_dyadic_decay
      s K L envelope (A := 4 / (Real.log 2) ^ 2)
      (by positivity) hpos hlower hupper hdecay
    calc
      (∑ n ∈ s, ((n : ℝ))⁻¹ * (envelope n) ^ 2) ≤
          2 * (4 / (Real.log 2) ^ 2) := h
      _ = 8 / (Real.log 2) ^ 2 := by ring
  calc
    (∑ n ∈ s, Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
        ∑ n ∈ s, ((n : ℝ))⁻¹ * (envelope n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero (hpos n hn)
      calc
        Complex.normSq (hardyPhaseLinearizedCoeff n delta t) ≤
            ((Real.sqrt n)⁻¹ * hardyPhaseLinearizedEnvelope n delta t) ^ 2 :=
          normSq_hardyPhaseLinearizedCoeff_le_envelope hnpos hdelta
        _ = ((n : ℝ))⁻¹ * (envelope n) ^ 2 := by
          rw [mul_pow, inv_sqrt_sq_nat hnpos]
    _ ≤ 8 / (Real.log 2) ^ 2 := hweighted

end HardyTheorem
