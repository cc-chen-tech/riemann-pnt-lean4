import HardyTheorem.HardyPhaseHighTailEnergy
import HardyTheorem.HardyPhaseWindowCoeffEnvelope
import MathlibAux.DyadicWeightedSquareHighTail

open scoped BigOperators

open Complex

namespace HardyTheorem

open OscillatoryIntegral

private theorem inv_sqrt_sq_nat {n : ℕ} (hn : 0 < n) :
    ((Real.sqrt n)⁻¹) ^ 2 = ((n : ℝ))⁻¹ := by
  rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le : (0 : ℝ) ≤ n)]

/-- In a finite dyadic high tail, the derivative energy of the moving Hardy
window coefficients has a summable oscillatory envelope. -/
theorem sum_normSq_deriv_hardyPhaseWindowCoeff_far_high_le
    (s : Finset ℕ) (K L : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : 2 * hardyPhaseStationaryScale t ≤ (2 : ℝ) ^ K)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hlower : ∀ n ∈ s, 2 ^ K ≤ n)
    (hupper : ∀ n ∈ s, n < 2 ^ L) :
    (∑ n ∈ s, Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) := by
  let envelope : ℕ → ℝ := fun n ↦
    (1 / (2 * t)) *
      min (delta ^ 2 / 2)
        (delta / |deriv thetaModel t - Real.log n| +
          2 / (deriv thetaModel t - Real.log n) ^ 2)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdelta0 : 0 ≤ delta := by linarith
  have hlogHalf : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hdecay : ∀ k, K ≤ k → k < L →
      ∀ n ∈ MathlibAux.dyadicBlock s k,
        (envelope n) ^ 2 ≤
          (25 * delta ^ 2 / (4 * t ^ 2 * (Real.log 2) ^ 2)) *
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
    have hphase := deriv_hardyPhase_eq_deriv_thetaModel_sub_log hnpos ht
    have htheta : deriv thetaModel t - Real.log n ≠ 0 := by
      rw [← hphase]
      exact hfreqne
    let a : ℝ := ((k - K + 1 : ℕ) : ℝ) * Real.log 2
    let u : ℝ := |deriv (hardyPhase n) t|
    have ha : 0 < a := by
      exact hfreqLower
    have hu : 0 < u := by
      exact habs
    have hhalfA : (1 / 2 : ℝ) < a := by
      have hjone : (1 : ℝ) ≤ ((k - K + 1 : ℕ) : ℝ) := by
        exact_mod_cast hjNat
      dsimp only [a]
      nlinarith
    have hau : a ≤ u := by
      exact hfreq
    have hfirst : delta / u ≤ delta / a :=
      div_le_div_of_nonneg_left hdelta0 ha hau
    have htwo_over_u : 2 / u ≤ 4 := by
      rw [div_le_iff₀ hu]
      nlinarith
    have hsecond : 2 / u ^ 2 ≤ 4 / u := by
      calc
        2 / u ^ 2 = (2 / u) / u := by field_simp [hu.ne']
        _ ≤ 4 / u := div_le_div_of_nonneg_right htwo_over_u (le_of_lt hu)
    have hfour : 4 / u ≤ 4 / a :=
      div_le_div_of_nonneg_left (by norm_num) ha hau
    have hdeltaFour : 4 / a ≤ 4 * delta / a := by
      calc
        4 / a = (4 / a) * 1 := by ring
        _ ≤ (4 / a) * delta :=
          mul_le_mul_of_nonneg_left hdelta (by positivity)
        _ = 4 * delta / a := by ring
    have hmoment : delta / u + 2 / u ^ 2 ≤ 5 * delta / a := by
      calc
        delta / u + 2 / u ^ 2 ≤ delta / a + 4 / u :=
          add_le_add hfirst hsecond
        _ ≤ delta / a + 4 * delta / a :=
          by
            have h := add_le_add_left (hfour.trans hdeltaFour) (delta / a)
            simpa [add_comm] using h
        _ = 5 * delta / a := by ring
    have hmin :
        min (delta ^ 2 / 2)
            (delta / |deriv thetaModel t - Real.log n| +
              2 / (deriv thetaModel t - Real.log n) ^ 2) ≤
          5 * delta / a := by
      rw [← hphase]
      exact (min_le_right _ _).trans (by simpa only [u, sq_abs] using hmoment)
    have henvelope : envelope n ≤ 5 * delta / (2 * t * a) := by
      dsimp only [envelope]
      calc
        (1 / (2 * t)) *
            min (delta ^ 2 / 2)
              (delta / |deriv thetaModel t - Real.log n| +
                2 / (deriv thetaModel t - Real.log n) ^ 2) ≤
            (1 / (2 * t)) * (5 * delta / a) :=
          mul_le_mul_of_nonneg_left hmin (by positivity)
        _ = 5 * delta / (2 * t * a) := by ring
    have henvelope0 : 0 ≤ envelope n := by
      dsimp only [envelope]
      apply mul_nonneg (by positivity)
      exact le_min (by positivity)
        (add_nonneg (div_nonneg hdelta0 (abs_nonneg _))
          (div_nonneg (by norm_num) (sq_nonneg _)))
    calc
      (envelope n) ^ 2 ≤ (5 * delta / (2 * t * a)) ^ 2 :=
        (sq_le_sq₀ henvelope0 (by positivity)).2 henvelope
      _ = (25 * delta ^ 2 / (4 * t ^ 2 * (Real.log 2) ^ 2)) *
          (((((k - K + 1 : ℕ) : ℝ) ^ 2))⁻¹) := by
        dsimp only [a]
        field_simp [ht.ne', ne_of_gt hj, ne_of_gt hlogTwo]
        ring
  have hweighted :
      (∑ n ∈ s, ((n : ℝ))⁻¹ * (envelope n) ^ 2) ≤
        25 * delta ^ 2 / (2 * t ^ 2 * (Real.log 2) ^ 2) := by
    have h := MathlibAux.sum_inv_mul_sq_le_of_high_dyadic_decay
      s K L envelope (A := 25 * delta ^ 2 / (4 * t ^ 2 * (Real.log 2) ^ 2))
      (by positivity) hpos hlower hupper hdecay
    calc
      (∑ n ∈ s, ((n : ℝ))⁻¹ * (envelope n) ^ 2) ≤
          2 * (25 * delta ^ 2 / (4 * t ^ 2 * (Real.log 2) ^ 2)) := h
      _ = 25 * delta ^ 2 / (2 * t ^ 2 * (Real.log 2) ^ 2) := by ring
  calc
    (∑ n ∈ s, Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
        ∑ n ∈ s, ((n : ℝ))⁻¹ * (envelope n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := Nat.pos_of_ne_zero (hpos n hn)
      have hphase := deriv_hardyPhase_eq_deriv_thetaModel_sub_log hnpos ht
      have hfreq : deriv thetaModel t - Real.log n ≠ 0 := by
        rw [← hphase]
        have hblock : n ∈ MathlibAux.dyadicBlock s n.log2 :=
          MathlibAux.mem_dyadicBlock_log2 hn (hpos n hn)
        have hK : K ≤ n.log2 :=
          (Nat.le_log2 (hpos n hn)).2 (hlower n hn)
        have hhigh := highDyadicDistance_mul_logTwo_le_abs_deriv_hardyPhase
          hK hnpos ht hscale (Nat.log2_self_le (hpos n hn))
        exact abs_ne_zero.mp (ne_of_gt
          ((mul_pos (by exact_mod_cast (show 0 < n.log2 - K + 1 by omega)) hlogTwo).trans_le hhigh))
      have hnorm := norm_deriv_hardyPhaseWindowCoeff_le_min
        hnpos hdelta0 ht hfreq
      have henvelope0 : 0 ≤ envelope n := by
        dsimp only [envelope]
        apply mul_nonneg (by positivity)
        exact le_min (by positivity)
          (add_nonneg (div_nonneg hdelta0 (abs_nonneg _))
            (div_nonneg (by norm_num) (sq_nonneg _)))
      rw [Complex.normSq_eq_norm_sq]
      calc
        ‖deriv (hardyPhaseWindowCoeff n delta) t‖ ^ 2 ≤
            ((Real.sqrt n)⁻¹ * envelope n) ^ 2 := by
          apply (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg (by positivity) henvelope0)).2
          simpa only [envelope, mul_assoc] using hnorm
        _ = ((n : ℝ))⁻¹ * (envelope n) ^ 2 := by
          rw [mul_pow, inv_sqrt_sq_nat hnpos]
    _ ≤ 25 * delta ^ 2 / (2 * t ^ 2 * (Real.log 2) ^ 2) := hweighted
    _ ≤ 25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) := by
      have hden : 0 < t ^ 2 * (Real.log 2) ^ 2 :=
        mul_pos (sq_pos_of_pos ht) (sq_pos_of_pos hlogTwo)
      have hquot : 0 ≤ 25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) :=
        div_nonneg (by positivity) hden.le
      calc
        25 * delta ^ 2 / (2 * t ^ 2 * (Real.log 2) ^ 2) =
            (25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2)) / 2 := by
              field_simp [hden.ne']
        _ ≤ 25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) := by
          linarith

end HardyTheorem
