import ZeroFreeRegion.VinogradovKorobov.SecondDifferenceSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t h k : ℝ) (m n : ℕ) : ℝ :=
  secondDifferenceZetaPhase t h k m n

example (t h k : ℝ) (m n : ℕ) :
    secondDifferenceZetaPhase t h k m n -
        secondDifferenceZetaPhase t h k m (n + 1) =
      t * logSecondDifferenceDecrement h k (m + n) :=
  secondDifferenceZetaPhase_decrement t h k m n

example (t : ℝ) (h k m N : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k (m + N)) :
    ‖∑ n ∈ Finset.range (N + 1),
        phaseTerm (secondDifferenceZetaPhase t h k m) n‖ ≤
      2 * Real.pi /
        (t * logSecondDifferenceDecrement h k (m + N)) :=
  secondDifferenceZetaPhase_kusminLandau
    t h k m N ht hh hk hm hturn

example (t : ℝ) (h k m N : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k (m + N)) :
    ‖∑ n ∈ Finset.range (N + 1),
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
      2 * Real.pi /
        (t * logSecondDifferenceDecrement h k (m + N)) :=
  iteratedShiftedZetaPhase_two_kusminLandau
    t h k m N ht hh hk hm hturn

example (t : ℝ) (h k m R : ℕ)
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
          ((m + (R - 1) : ℕ) : ℝ)) :=
  iteratedShiftedZetaPhase_two_kusminLandau_range
    t h k m R ht hh hk hm hR hturn

end ZeroFreeRegion.VinogradovKorobov
