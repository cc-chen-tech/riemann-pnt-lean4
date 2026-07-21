import HardyTheorem.HardyPhaseCentralLeftEnergy
import HardyTheorem.HardyPhaseCentralRightEnergy
import HardyTheorem.HardyPhaseNearestEnergy

open Complex
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

/-- The central portion of `s` around the stationary scale has `O(delta)`
energy, apart from the explicit `O(delta^2 / r)` contribution of the two
adjacent integer indices. -/
theorem sum_normSq_hardyPhaseLinearizedCoeff_central_le
    (s : Finset ℕ) (N : ℕ) {delta t : ℝ}
    (ht : 0 < t) (hdelta : 0 < delta)
    (hscale : 1 ≤ hardyPhaseStationaryScale t)
    (hupperNat : ∀ n ∈ s, n ≤ N)
    (hlower : ∀ n ∈ s,
      hardyPhaseStationaryScale t / 8 ≤ n)
    (hupper : ∀ n ∈ s,
      (n : ℝ) ≤ 8 * hardyPhaseStationaryScale t) :
    (∑ n ∈ s,
      Complex.normSq (hardyPhaseLinearizedCoeff n delta t)) ≤
      96 * delta +
        16 * delta ^ 2 / hardyPhaseStationaryScale t := by
  classical
  let r := hardyPhaseStationaryScale t
  let m := Nat.floor r
  let f : ℕ → ℝ := fun n =>
    Complex.normSq (hardyPhaseLinearizedCoeff n delta t)
  let left := s.filter fun n => n < m
  let rest := s.filter fun n => ¬n < m
  let near := rest.filter fun n => n ≤ m + 1
  let right := rest.filter fun n => ¬n ≤ m + 1
  have mem_left {n : ℕ} (hn : n ∈ left) : n ∈ s ∧ n < m := by
    simpa only [left, Finset.mem_filter] using hn
  have mem_near {n : ℕ} (hn : n ∈ near) :
      n ∈ s ∧ ¬n < m ∧ n ≤ m + 1 := by
    have h : (n ∈ s ∧ ¬n < m) ∧ n ≤ m + 1 := by
      simpa only [near, rest, Finset.mem_filter] using hn
    exact ⟨h.1.1, h.1.2, h.2⟩
  have mem_right {n : ℕ} (hn : n ∈ right) :
      n ∈ s ∧ ¬n < m ∧ ¬n ≤ m + 1 := by
    have h : (n ∈ s ∧ ¬n < m) ∧ ¬n ≤ m + 1 := by
      simpa only [right, rest, Finset.mem_filter] using hn
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hsplitLeft : (∑ n ∈ left, f n) + (∑ n ∈ rest, f n) =
      ∑ n ∈ s, f n := by
    simpa only [left, rest] using
      Finset.sum_filter_add_sum_filter_not s (fun n => n < m) f
  have hsplitNear : (∑ n ∈ near, f n) + (∑ n ∈ right, f n) =
      ∑ n ∈ rest, f n := by
    simpa only [near, right] using
      Finset.sum_filter_add_sum_filter_not rest (fun n => n ≤ m + 1) f
  have hleft : (∑ n ∈ left, f n) ≤ 48 * delta := by
    apply sum_normSq_hardyPhaseLinearizedCoeff_central_left_le
      left ht hdelta hscale
    · intro n hn
      simpa only [m, r] using (mem_left hn).2
    · intro n hn
      exact hlower n (mem_left hn).1
  have hright : (∑ n ∈ right, f n) ≤ 48 * delta := by
    apply sum_normSq_hardyPhaseLinearizedCoeff_central_right_le
      right N ht hdelta hscale
    · intro n hn
      have h := mem_right hn
      have hn' : m + 1 < n := by omega
      simpa only [m, r] using hn'
    · intro n hn
      exact hupperNat n (mem_right hn).1
    · intro n hn
      exact hupper n (mem_right hn).1
  have hnearSubset : near ⊆ ({m, m + 1} : Finset ℕ) := by
    intro n hn
    have hnNear := (mem_near hn).2.2
    have hnRest := (mem_near hn).2.1
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hnear : (∑ n ∈ near, f n) ≤ 16 * delta ^ 2 / r := by
    calc
      (∑ n ∈ near, f n) ≤ ∑ n ∈ ({m, m + 1} : Finset ℕ), f n :=
        Finset.sum_le_sum_of_subset_of_nonneg hnearSubset (by
          intro n _hn _hnear
          dsimp only [f]
          exact Complex.normSq_nonneg _)
      _ ≤ 16 * delta ^ 2 / r := by
        simpa only [f, m, r] using
          sum_normSq_hardyPhaseLinearizedCoeff_nearest_le
            ht hdelta.le hscale
  rw [← hsplitLeft, ← hsplitNear]
  dsimp only [f]
  linarith

end HardyTheorem
