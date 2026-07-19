import ZeroFreeRegion.VinogradovKorobov.RecursiveZetaBounds

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m N depth : ℕ) : ℝ :=
  zetaAProcessUniformLeafDeltaLower t m N depth

noncomputable example (t : ℝ) (m N depth : ℕ) : ℝ :=
  zetaAProcessUniformLeafSquaredBound t m N depth

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessUniformLeafDeltaLower t m N depth ≤
      zetaAProcessLeafDelta t m N shifts :=
  zetaAProcessUniformLeafDeltaLower_le
    t m N depth shifts ht hm hR hshifts hdepth

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hR : 1 ≤ remainingAProcessLength N shifts)
    (hshifts : ∀ h ∈ shifts, 0 < h)
    (hdepth : shifts.length = depth) :
    zetaAProcessLeafSquaredBound t m N shifts ≤
      zetaAProcessUniformLeafSquaredBound t m N depth :=
  zetaAProcessLeafSquaredBound_le_uniform
    t m N depth shifts ht hm hR hshifts hdepth

end ZeroFreeRegion.VinogradovKorobov
