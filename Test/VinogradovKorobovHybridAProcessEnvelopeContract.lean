import ZeroFreeRegion.VinogradovKorobov.HybridAProcessEnvelope

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (N : ℕ) (C P : ℝ) : ℝ :=
  hybridProductLeafSquaredEnvelope N C P

noncomputable example (H : ℕ → ℕ) (N : ℕ) (C : ℝ)
    (depth level : ℕ) (P : ℝ) : ℝ :=
  hybridProductRecursiveAProcessSquaredBound H N C depth level P

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    zetaAProcessProductLeafSquaredBound t m N depth shifts =
      zetaAProcessUniformLeafSquaredBound t m N depth /
        (shifts.prod : ℝ) ^ 2 :=
  zetaAProcessProductLeafSquaredBound_eq_div_prod_sq
    t m N depth shifts ht hm hshifts

example (t : ℝ) (m N depth : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hshifts : ∀ h ∈ shifts, 0 < h) :
    zetaAProcessHybridProductLeafSquaredBound t m N depth shifts ≤
      hybridProductLeafSquaredEnvelope N
        (zetaAProcessUniformLeafSquaredBound t m N depth)
        (shifts.prod : ℝ) :=
  zetaAProcessHybridProductLeafSquaredBound_le_envelope
    t m N depth shifts ht hm hshifts

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      hybridProductRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 1 :=
  norm_zetaPhase_sum_sq_le_hybridProductEnvelope_of_scale
    t m N depth H ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
