import ZeroFreeRegion.VinogradovKorobov.HighOrderZetaPhase

namespace ZeroFreeRegion.VinogradovKorobov

example (t : ℝ) (m n : ℕ) (shifts : List ℕ)
    (ht : 0 ≤ t) (hm : 0 < m) :=
  iterated_shiftedZetaPhase_decrement_bounds t m n shifts ht hm

example (t : ℝ) (m n : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m) (hshifts : ∀ h ∈ shifts, 0 < h) :
    0 < iteratedPhaseDifference shifts (shiftedZetaPhase t m) n -
      iteratedPhaseDifference shifts (shiftedZetaPhase t m) (n + 1) :=
  iterated_shiftedZetaPhase_decrement_pos t m n shifts ht hm hshifts

example (t : ℝ) (m R : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m) (hR : 1 ≤ R)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hturn :
      (iteratedPhaseDifference shifts (shiftedZetaPhase t m) 0 -
          iteratedPhaseDifference shifts (shiftedZetaPhase t m) 1) ≤
        2 * Real.pi -
          (iteratedPhaseDifference shifts (shiftedZetaPhase t m) (R - 1) -
            iteratedPhaseDifference shifts (shiftedZetaPhase t m) R)) :
    ‖∑ n ∈ Finset.range R,
        phaseTerm (iteratedPhaseDifference shifts (shiftedZetaPhase t m)) n‖ ≤
      2 * Real.pi /
        (iteratedPhaseDifference shifts (shiftedZetaPhase t m) (R - 1) -
          iteratedPhaseDifference shifts (shiftedZetaPhase t m) R) :=
  iterated_shiftedZetaPhase_kusminLandau_range
    t m R shifts ht hm hR hshifts hturn

end ZeroFreeRegion.VinogradovKorobov
