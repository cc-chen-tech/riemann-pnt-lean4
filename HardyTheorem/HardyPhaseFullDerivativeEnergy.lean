import HardyTheorem.HardyPhaseCentralDerivativeEnergy
import HardyTheorem.HardyPhaseDyadicCutoffs
import HardyTheorem.HardyPhaseHighTailDerivativeEnergy
import HardyTheorem.HardyPhaseLowTailDerivativeEnergy

open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

/-- The derivative energy of the complete moving Hardy window splits into
two oscillatory dyadic tails and one central stationary annulus. -/
theorem sum_normSq_deriv_hardyPhaseWindowCoeff_full_le
    (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : 8 ≤ hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      50 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) +
        4 * delta ^ 4 / t ^ 2 := by
  classical
  let r := hardyPhaseStationaryScale t
  let f : ℕ → ℝ := fun n ↦
    Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)
  let low : Finset ℕ := s.filter fun n ↦ (n : ℝ) < r / 8
  let nonlow : Finset ℕ := s.filter fun n ↦ ¬(n : ℝ) < r / 8
  let central : Finset ℕ := nonlow.filter fun n ↦ (n : ℝ) ≤ 8 * r
  let high : Finset ℕ := nonlow.filter fun n ↦ ¬(n : ℝ) ≤ 8 * r
  obtain ⟨Klow, Khigh, L, hlowScale, hlowCutoff, hhighScale,
      _, hhighCutoff, hlastCutoff⟩ :=
    exists_hardyPhaseDyadicCutoffs ht hscale N
  have mem_low {n : ℕ} (hn : n ∈ low) :
      n ∈ s ∧ (n : ℝ) < r / 8 := by
    simpa only [low, Finset.mem_filter] using hn
  have mem_nonlow {n : ℕ} (hn : n ∈ nonlow) :
      n ∈ s ∧ ¬(n : ℝ) < r / 8 := by
    simpa only [nonlow, Finset.mem_filter] using hn
  have mem_central {n : ℕ} (hn : n ∈ central) :
      n ∈ s ∧ ¬(n : ℝ) < r / 8 ∧ (n : ℝ) ≤ 8 * r := by
    have h : (n ∈ s ∧ ¬(n : ℝ) < r / 8) ∧
        (n : ℝ) ≤ 8 * r := by
      simpa only [central, nonlow, Finset.mem_filter] using hn
    exact ⟨h.1.1, h.1.2, h.2⟩
  have mem_high {n : ℕ} (hn : n ∈ high) :
      n ∈ s ∧ ¬(n : ℝ) < r / 8 ∧ ¬(n : ℝ) ≤ 8 * r := by
    have h : (n ∈ s ∧ ¬(n : ℝ) < r / 8) ∧
        ¬(n : ℝ) ≤ 8 * r := by
      simpa only [high, nonlow, Finset.mem_filter] using hn
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hsplitLow :
      (∑ n ∈ low, f n) + (∑ n ∈ nonlow, f n) = ∑ n ∈ s, f n := by
    simpa only [low, nonlow] using
      Finset.sum_filter_add_sum_filter_not s
        (fun n ↦ (n : ℝ) < r / 8) f
  have hsplitCentral :
      (∑ n ∈ central, f n) + (∑ n ∈ high, f n) =
        ∑ n ∈ nonlow, f n := by
    simpa only [central, high] using
      Finset.sum_filter_add_sum_filter_not nonlow
        (fun n ↦ (n : ℝ) ≤ 8 * r) f
  have hlow :
      (∑ n ∈ low, f n) ≤
        25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) := by
    apply sum_normSq_deriv_hardyPhaseWindowCoeff_far_low_le
      low Klow ht hdelta
    · simpa only [r] using hlowScale
    · intro n hn
      exact hpos n (mem_low hn).1
    · intro n hn
      exact hlowCutoff n (by simpa only [r] using (mem_low hn).2)
  have hscaleOne : 1 ≤ r := by
    dsimp only [r]
    linarith
  have hcentral :
      (∑ n ∈ central, f n) ≤ 4 * delta ^ 4 / t ^ 2 := by
    apply sum_normSq_deriv_hardyPhaseWindowCoeff_central_annulus_le
      central ht (by linarith) hscaleOne
    · intro n hn
      exact le_of_not_gt (mem_central hn).2.1
    · intro n hn
      exact (mem_central hn).2.2
  have hhigh :
      (∑ n ∈ high, f n) ≤
        25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) := by
    apply sum_normSq_deriv_hardyPhaseWindowCoeff_far_high_le
      high Khigh L ht hdelta
    · simpa only [r] using hhighScale
    · intro n hn
      exact hpos n (mem_high hn).1
    · intro n hn
      apply hhighCutoff n
      exact lt_of_not_ge (mem_high hn).2.2
    · intro n hn
      exact (hupper n (mem_high hn).1).trans_lt hlastCutoff
  rw [← hsplitLow, ← hsplitCentral]
  dsimp only [f, r] at hlow hcentral hhigh ⊢
  calc
    (∑ n ∈ low,
        Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) +
        ((∑ n ∈ central,
            Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) +
          ∑ n ∈ high,
            Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
        25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) +
          (4 * delta ^ 4 / t ^ 2 +
            25 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2)) :=
      add_le_add hlow (add_le_add hcentral hhigh)
    _ = 50 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) +
        4 * delta ^ 4 / t ^ 2 := by ring

/-- For a window of length at least one, the full moving-coefficient
derivative energy has the scale `delta^4 / t^2` needed by the Hilbert
integration-by-parts estimate. -/
theorem sum_normSq_deriv_hardyPhaseWindowCoeff_full_le_mul
    (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : 8 ≤ hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
      204 * delta ^ 4 / t ^ 2 := by
  have hraw := sum_normSq_deriv_hardyPhaseWindowCoeff_full_le
    s N ht hdelta hscale hpos hupper
  have hlogHalf : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlogPos : 0 < Real.log 2 := by linarith
  have hlogSq : (1 / 4 : ℝ) < (Real.log 2) ^ 2 := by
    nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
  have htSq : 0 < t ^ 2 := sq_pos_of_pos ht
  have hdeltaSq : delta ^ 2 ≤ delta ^ 4 := by
    nlinarith [sq_nonneg delta, sq_nonneg (delta ^ 2 - 1)]
  have htail :
      50 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) ≤
        200 * delta ^ 4 / t ^ 2 := by
    apply (div_le_iff₀ (mul_pos htSq (sq_pos_of_pos hlogPos))).2
    have hcancel :
        200 * delta ^ 4 / t ^ 2 *
            (t ^ 2 * (Real.log 2) ^ 2) =
          200 * delta ^ 4 * (Real.log 2) ^ 2 := by
      field_simp [htSq.ne']
    rw [hcancel]
    calc
      50 * delta ^ 2 ≤ 50 * delta ^ 4 :=
        mul_le_mul_of_nonneg_left hdeltaSq (by norm_num)
      _ = (200 * delta ^ 4) * (1 / 4 : ℝ) := by ring
      _ ≤ (200 * delta ^ 4) * (Real.log 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hlogSq.le (by positivity)
      _ = 200 * delta ^ 4 * (Real.log 2) ^ 2 := by ring
  calc
    (∑ n ∈ s,
      Complex.normSq (deriv (hardyPhaseWindowCoeff n delta) t)) ≤
        50 * delta ^ 2 / (t ^ 2 * (Real.log 2) ^ 2) +
          4 * delta ^ 4 / t ^ 2 := hraw
    _ ≤ 200 * delta ^ 4 / t ^ 2 + 4 * delta ^ 4 / t ^ 2 :=
      by
        simpa [add_comm] using add_le_add_right htail (4 * delta ^ 4 / t ^ 2)
    _ = 204 * delta ^ 4 / t ^ 2 := by ring

end HardyTheorem
