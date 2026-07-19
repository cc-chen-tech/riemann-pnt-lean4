import ZeroFreeRegion.VinogradovKorobov.RecursiveZetaAProcess

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m n : ℕ) (shifts : List ℕ) : ℝ :=
  iteratedZetaPhaseDecrement t m shifts n

noncomputable example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessLeafDelta t m N shifts

noncomputable example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessLeafSquaredBound t m N shifts

example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : Prop :=
  ZetaAProcessLeafValid t m N shifts

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) : Prop :=
  RecursiveZetaAProcessValid t m L N depth shifts

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessValid t m L N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) L
      (zetaAProcessLeafSquaredBound t m N) N depth shifts :=
  recursiveZetaAProcessValid_to_generic
    t m L N depth shifts ht hm hvalid

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessValid t m L N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L
        (zetaAProcessLeafSquaredBound t m N) N depth [] :=
  norm_zetaPhase_sum_sq_le_recursiveAProcess
    t m L N depth ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
