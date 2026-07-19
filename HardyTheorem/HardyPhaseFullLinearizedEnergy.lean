import HardyTheorem.HardyPhaseCentralEnergy
import HardyTheorem.HardyPhaseDyadicCutoffs
import HardyTheorem.HardyPhaseHighTailEnergy
import HardyTheorem.HardyPhaseLowTailEnergy

open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

/-- The complete finite linearized Hardy-phase energy is bounded by the
central stationary contribution and two absolute dyadic tail constants. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_full_le
    (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 8 ≤ hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s,
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      96 * delta +
        16 * delta ^ 2 / hardyPhaseStationaryScale t +
        16 / (Real.log 2) ^ 2 := by
  classical
  let r := hardyPhaseStationaryScale t
  let f : ℕ → ℝ := fun n ↦
    Complex.normSq (hardyPhaseLinearizedCoeff n delta t)
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
      (∑ n ∈ low, f n) ≤ 8 / (Real.log 2) ^ 2 := by
    apply sum_normSq_hardyPhaseLinearizedCoeff_far_low_le
      low Klow ht hdelta.le
    · simpa only [r] using hlowScale
    · intro n hn
      exact hpos n (mem_low hn).1
    · intro n hn
      exact hlowCutoff n (by simpa only [r] using (mem_low hn).2)
  have hscaleOne : 1 ≤ r := by
    dsimp only [r]
    linarith
  have hcentral :
      (∑ n ∈ central, f n) ≤
        96 * delta + 16 * delta ^ 2 / r := by
    apply sum_normSq_hardyPhaseLinearizedCoeff_central_le
      central N ht hdelta hscaleOne
    · intro n hn
      exact hupper n (mem_central hn).1
    · intro n hn
      exact le_of_not_gt (mem_central hn).2.1
    · intro n hn
      exact (mem_central hn).2.2
  have hhigh :
      (∑ n ∈ high, f n) ≤ 8 / (Real.log 2) ^ 2 := by
    apply sum_normSq_hardyPhaseLinearizedCoeff_far_high_le
      high Khigh L ht hdelta.le
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
        Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) +
        ((∑ n ∈ central,
            Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) +
          ∑ n ∈ high,
            Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
        8 / (Real.log 2) ^ 2 +
          ((96 * delta + 16 * delta ^ 2 /
              hardyPhaseStationaryScale t) +
            8 / (Real.log 2) ^ 2) :=
      add_le_add hlow (add_le_add hcentral hhigh)
    _ = 96 * delta +
        16 * delta ^ 2 / hardyPhaseStationaryScale t +
        16 / (Real.log 2) ^ 2 := by ring

/-- If the short-window length is at least one and no larger than the
stationary scale, the complete linearized energy is at most `200 * delta`. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_full_le_mul
    (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 1 ≤ delta)
    (hscale : 8 ≤ hardyPhaseStationaryScale t)
    (hwindow : delta ≤ hardyPhaseStationaryScale t)
    (hpos : ∀ n ∈ s, n ≠ 0)
    (hupper : ∀ n ∈ s, n ≤ N) :
    (∑ n ∈ s,
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      200 * delta := by
  have hdeltaPos : 0 < delta := lt_of_lt_of_le (by norm_num) hdelta
  have hrPos : 0 < hardyPhaseStationaryScale t :=
    hardyPhaseStationaryScale_pos ht
  have hraw := sum_normSq_hardyPhaseLinearizedCoeff_full_le
    s N ht hdeltaPos hscale hpos hupper
  have hquadratic :
      16 * delta ^ 2 / hardyPhaseStationaryScale t ≤ 16 * delta := by
    rw [div_le_iff₀ hrPos]
    nlinarith
  have hlogHalf : (1 / 2 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  have hlogPos : 0 < Real.log 2 := by linarith
  have hlogSq : (1 / 4 : ℝ) < (Real.log 2) ^ 2 := by
    nlinarith [sq_nonneg (Real.log 2 - 1 / 2)]
  have htail : 16 / (Real.log 2) ^ 2 ≤ 64 * delta := by
    have hfixed : 16 / (Real.log 2) ^ 2 ≤ 64 := by
      rw [div_le_iff₀ (sq_pos_of_pos hlogPos)]
      nlinarith
    exact hfixed.trans (by nlinarith)
  linarith

end HardyTheorem
