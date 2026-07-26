import ZeroFreeRegion.VinogradovKorobov.HigherLogDifference
import ZeroFreeRegion.VinogradovKorobov.SignedFirstDerivative

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The real phase left after two A-process differences of a shifted zeta
logarithmic phase. -/
noncomputable def secondDifferenceZetaPhase
    (t h k : ℝ) (m n : ℕ) : ℝ :=
  t * logSecondDifference h k (m + n)

/-- A forward decrement of the twice-differenced zeta phase is exactly `t`
times the third logarithmic difference. -/
lemma secondDifferenceZetaPhase_decrement
    (t h k : ℝ) (m n : ℕ) :
    secondDifferenceZetaPhase t h k m n -
        secondDifferenceZetaPhase t h k m (n + 1) =
      t * logSecondDifferenceDecrement h k (m + n) := by
  unfold secondDifferenceZetaPhase logSecondDifferenceDecrement
  push_cast
  ring_nf

/-- A concrete Kusmin--Landau bound for the phase produced by two A-process
differences of `-t log n`.  The single `hturn` hypothesis says that the full
range of third differences remains in one nonresonant turn. -/
theorem secondDifferenceZetaPhase_kusminLandau
    (t : ℝ) (h k m N : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k (m + N)) :
    ‖∑ n ∈ Finset.range (N + 1),
        phaseTerm (secondDifferenceZetaPhase t h k m) n‖ ≤
      2 * Real.pi /
        (t * logSecondDifferenceDecrement h k (m + N)) := by
  have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmNR : 0 < (m : ℝ) + (N : ℝ) := by positivity
  have hmnR : ∀ n : ℕ, 0 < (m : ℝ) + (n : ℝ) := by
    intro n
    positivity
  let delta : ℝ :=
    t * logSecondDifferenceDecrement h k (m + N)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact mul_pos ht
      (logSecondDifferenceDecrement_pos hmNR hhR hkR)
  apply kusminLandau_negative_antitone_two_pi_div
    (secondDifferenceZetaPhase t h k m) N hdelta
  · intro n hn
    rw [secondDifferenceZetaPhase_decrement]
    dsimp [delta]
    apply mul_le_mul_of_nonneg_left _ ht.le
    apply antitoneOn_logSecondDifferenceDecrement hhR hkR
    · exact hmnR n
    · exact hmNR
    · exact_mod_cast Nat.add_le_add_left hn m
  · intro n hn
    rw [secondDifferenceZetaPhase_decrement]
    calc
      t * logSecondDifferenceDecrement h k (m + n) ≤
          t * logSecondDifferenceDecrement h k m := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        apply antitoneOn_logSecondDifferenceDecrement hhR hkR
        · exact hmR
        · exact hmnR n
        · exact_mod_cast Nat.le_add_right m n
      _ ≤ 2 * Real.pi - delta := by simpa [delta] using hturn
  · intro n hn
    rw [secondDifferenceZetaPhase_decrement,
      secondDifferenceZetaPhase_decrement]
    apply mul_le_mul_of_nonneg_left _ ht.le
    apply antitoneOn_logSecondDifferenceDecrement hhR hkR
    · exact hmnR n
    · exact hmnR (n + 1)
    · exact_mod_cast Nat.add_le_add_left (Nat.le_succ n) m

/-- The same concrete estimate stated directly for the twice-iterated phase
used by the recursive A-process interface. -/
theorem iteratedShiftedZetaPhase_two_kusminLandau
    (t : ℝ) (h k m N : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k (m + N)) :
    ‖∑ n ∈ Finset.range (N + 1),
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
      2 * Real.pi /
        (t * logSecondDifferenceDecrement h k (m + N)) := by
  have hphase :
      iteratedPhaseDifference [h, k] (shiftedZetaPhase t m) =
        secondDifferenceZetaPhase t h k m := by
    funext n
    simpa only [secondDifferenceZetaPhase] using
      iterated_shiftedZetaPhase_two t m n h k
  rw [hphase]
  exact secondDifferenceZetaPhase_kusminLandau
    t h k m N ht hh hk hm hturn

/-- Positive-length form of the twice-differenced logarithmic sum bound.  It
packages the `R - 1 + 1 = R` bookkeeping needed by recursive A-process sums. -/
theorem iteratedShiftedZetaPhase_two_kusminLandau_range
    (t : ℝ) (h k m R : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hR : 1 ≤ R)
    (hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k
            ((m + (R - 1) : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range R,
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
      2 * Real.pi /
        (t * logSecondDifferenceDecrement h k
          ((m + (R - 1) : ℕ) : ℝ)) := by
  have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmLastR : 0 < ((m + (R - 1) : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (by omega)
  have hmnR : ∀ n : ℕ, 0 < (m : ℝ) + (n : ℝ) := by
    intro n
    positivity
  have hrange : R - 1 + 1 = R := by omega
  have hphase :
      iteratedPhaseDifference [h, k] (shiftedZetaPhase t m) =
        secondDifferenceZetaPhase t h k m := by
    funext n
    simpa only [secondDifferenceZetaPhase] using
      iterated_shiftedZetaPhase_two t m n h k
  rw [hphase, ← hrange]
  let delta : ℝ :=
    t * logSecondDifferenceDecrement h k
      ((m + (R - 1) : ℕ) : ℝ)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact mul_pos ht
      (logSecondDifferenceDecrement_pos hmLastR hhR hkR)
  apply kusminLandau_negative_antitone_two_pi_div
    (secondDifferenceZetaPhase t h k m) (R - 1) hdelta
  · intro n hn
    rw [secondDifferenceZetaPhase_decrement]
    dsimp [delta]
    apply mul_le_mul_of_nonneg_left _ ht.le
    apply antitoneOn_logSecondDifferenceDecrement hhR hkR
    · exact hmnR n
    · exact hmLastR
    · exact_mod_cast Nat.add_le_add_left hn m
  · intro n hn
    rw [secondDifferenceZetaPhase_decrement]
    calc
      t * logSecondDifferenceDecrement h k (m + n) ≤
          t * logSecondDifferenceDecrement h k m := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        apply antitoneOn_logSecondDifferenceDecrement hhR hkR
        · exact hmR
        · exact hmnR n
        · exact_mod_cast Nat.le_add_right m n
      _ ≤ 2 * Real.pi - delta := by simpa [delta] using hturn
  · intro n hn
    rw [secondDifferenceZetaPhase_decrement,
      secondDifferenceZetaPhase_decrement]
    apply mul_le_mul_of_nonneg_left _ ht.le
    apply antitoneOn_logSecondDifferenceDecrement hhR hkR
    · exact hmnR n
    · exact hmnR (n + 1)
    · exact_mod_cast Nat.add_le_add_left (Nat.le_succ n) m

end ZeroFreeRegion.VinogradovKorobov
