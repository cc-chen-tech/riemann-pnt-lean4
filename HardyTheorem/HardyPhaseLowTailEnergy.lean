import HardyTheorem.HardyPhaseLinearizedEnergy
import HardyTheorem.HardyPhaseStationaryScale
import MathlibAux.DyadicWeightedSquareTail

open scoped BigOperators

open Complex

namespace HardyTheorem

open OscillatoryIntegral

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)]

/-- Below the dyadic cutoff, separation from the stationary scale gives one
factor of `log 2` for every intervening dyadic block. -/
theorem logTwo_mul_dyadicDistance_le_abs_deriv_hardyPhase
    {K k n : ℕ} (hk : k < K) (hn : 0 < n) {t : ℝ} (ht : 0 < t)
    (hscale : (2 : ℝ) ^ (K + 1) ≤ hardyPhaseStationaryScale t)
    (hnupper : n < 2 ^ (k + 1)) :
    ((K - k : ℕ) : ℝ) * Real.log 2 ≤
      |deriv (hardyPhase n) t| := by
  have hdistNat : 0 < K - k := by omega
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnupperReal : (n : ℝ) < (2 : ℝ) ^ (k + 1) := by
    exact_mod_cast hnupper
  have hpowPos : 0 < (2 : ℝ) ^ (K - k) := by positivity
  have hratioLower :
      (2 : ℝ) ^ (K - k) < hardyPhaseStationaryScale t / n := by
    rw [lt_div_iff₀ hnreal]
    calc
      (2 : ℝ) ^ (K - k) * n <
          (2 : ℝ) ^ (K - k) * (2 : ℝ) ^ (k + 1) :=
        mul_lt_mul_of_pos_left hnupperReal hpowPos
      _ = (2 : ℝ) ^ (K + 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ hardyPhaseStationaryScale t := hscale
  have hratioPos : 0 < hardyPhaseStationaryScale t / (n : ℝ) :=
    div_pos (hardyPhaseStationaryScale_pos ht) hnreal
  have hlogLower :
      Real.log ((2 : ℝ) ^ (K - k)) <
        Real.log (hardyPhaseStationaryScale t / n) :=
    Real.strictMonoOn_log hpowPos hratioPos hratioLower
  have hlogPow :
      Real.log ((2 : ℝ) ^ (K - k)) =
        ((K - k : ℕ) : ℝ) * Real.log 2 := by
    rw [Real.log_pow]
  have hlogPowPos : 0 < Real.log ((2 : ℝ) ^ (K - k)) := by
    rw [hlogPow]
    positivity
  have hlogPos : 0 < Real.log (hardyPhaseStationaryScale t / n) :=
    hlogPowPos.trans hlogLower
  rw [abs_deriv_hardyPhase_eq_abs_log_stationaryScale_div
    (Nat.ne_of_gt hn) ht, abs_of_pos hlogPos, ← hlogPow]
  exact hlogLower.le

/-- If all positive indices lie below `2^K` while the stationary scale lies
above `2^(K+1)`, their linearized short-window energy is bounded by an
absolute constant.  The estimate is uniform in every nonnegative window
length `delta`; no `delta ≥ 1` conversion is used. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_far_low_le
    (s : Finset ℕ) (K : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 ≤ delta)
    (hscale : (2 : ℝ) ^ (K + 1) ≤ hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hbound : ∀ n ∈ s, n < 2 ^ K) :
    (∑ n ∈ s, Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      8 / (Real.log 2) ^ 2 := by
  let envelope : ℕ → ℝ := fun n ↦ hardyPhaseLinearizedEnvelope n delta t
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdecay : ∀ k < K, ∀ n ∈ MathlibAux.dyadicBlock s k,
      (envelope n) ^ 2 ≤
        (4 / (Real.log 2) ^ 2) *
          (((((K - k : ℕ) : ℝ) ^ 2))⁻¹) := by
    intro k hk n hn
    have hdistNat : 0 < K - k := by omega
    have hdist : 0 < ((K - k : ℕ) : ℝ) := by
      exact_mod_cast hdistNat
    have hnmem : n ∈ s := (MathlibAux.mem_dyadicBlock.1 hn).1
    have hnpos : 0 < n := Nat.pos_of_ne_zero (hpos n hnmem)
    have hfreq := logTwo_mul_dyadicDistance_le_abs_deriv_hardyPhase
      hk hnpos ht hscale (MathlibAux.mem_dyadicBlock.1 hn).2.2
    have hfreqLower :
        0 < ((K - k : ℕ) : ℝ) * Real.log 2 := mul_pos hdist hlogTwo
    have habs : 0 < |deriv (hardyPhase n) t| := hfreqLower.trans_le hfreq
    have hfreqne : deriv (hardyPhase n) t ≠ 0 := abs_pos.mp habs
    have hquot :
        2 / |deriv (hardyPhase n) t| ≤
          2 / (((K - k : ℕ) : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_left (by norm_num) hfreqLower hfreq
    have henvelope :
        envelope n ≤ 2 / (((K - k : ℕ) : ℝ) * Real.log 2) := by
      dsimp only [envelope]
      rw [hardyPhaseLinearizedEnvelope, if_neg hfreqne]
      exact (min_le_right _ _).trans hquot
    have henvelope0 : 0 ≤ envelope n := by
      dsimp only [envelope]
      exact hardyPhaseLinearizedEnvelope_nonneg n hdelta
    calc
      (envelope n) ^ 2 ≤
          (2 / (((K - k : ℕ) : ℝ) * Real.log 2)) ^ 2 :=
        (sq_le_sq₀ henvelope0 (by positivity)).2 henvelope
      _ = (4 / (Real.log 2) ^ 2) *
          (((((K - k : ℕ) : ℝ) ^ 2))⁻¹) := by
        field_simp [ne_of_gt hdist, ne_of_gt hlogTwo]
        ring
  have hweighted :
      (∑ n ∈ s, ((n : ℝ))⁻¹ * (envelope n) ^ 2) ≤
        8 / (Real.log 2) ^ 2 := by
    have h := MathlibAux.sum_inv_mul_sq_le_of_dyadic_decay
      s K envelope (A := 4 / (Real.log 2) ^ 2)
      (by positivity) hpos hbound hdecay
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
