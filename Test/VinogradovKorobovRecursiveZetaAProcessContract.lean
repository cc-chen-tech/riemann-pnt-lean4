import ZeroFreeRegion.VinogradovKorobov.RecursiveZetaAProcess

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m n : ℕ) (shifts : List ℕ) : ℝ :=
  iteratedZetaPhaseDecrement t m shifts n

noncomputable example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessLeafDelta t m N shifts

noncomputable example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessLeafSquaredBound t m N shifts

noncomputable example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessHybridLeafSquaredBound t m N shifts

noncomputable example (t : ℝ) (m : ℕ) (shifts : List ℕ) : ℝ :=
  zetaAProcessLeafInitialMajorant t m shifts

example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : Prop :=
  ZetaAProcessLeafValid t m N shifts

example (t : ℝ) (m N : ℕ) (shifts : List ℕ) : Prop :=
  ZetaAProcessScaleLeafValid t m N shifts

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) : Prop :=
  RecursiveZetaAProcessValid t m L N depth shifts

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) : Prop :=
  RecursiveZetaAProcessScaleValid t m L N depth shifts

example (t : ℝ) (m N : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScaleLeafValid t m N shifts) :
    ZetaAProcessLeafValid t m N shifts :=
  zetaAProcessLeafValid_of_scale t m N shifts ht hm hvalid

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid t m L N depth shifts) :
    RecursiveZetaAProcessValid t m L N depth shifts :=
  recursiveZetaAProcessValid_of_scale
    t m L N depth shifts ht hm hvalid

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessValid t m L N depth shifts) :
    RecursiveAProcessValid (shiftedZetaPhase t m) L
      (zetaAProcessLeafSquaredBound t m N) N depth shifts :=
  recursiveZetaAProcessValid_to_generic
    t m L N depth shifts ht hm hvalid

example (f : ℕ → ℝ) (N : ℕ) (shifts : List ℕ) :
    ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      (remainingAProcessLength N shifts : ℝ) ^ 2 :=
  norm_iteratedPhase_sum_sq_le_trivial f N shifts

example (t : ℝ) (m N : ℕ) (shifts : List ℕ)
    (ht : 0 < t) (hm : 0 < m) :
    ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
        phaseTerm
          (iteratedPhaseDifference shifts (shiftedZetaPhase t m)) n‖ ^ 2 ≤
      zetaAProcessHybridLeafSquaredBound t m N shifts :=
  norm_iteratedZetaPhase_sum_sq_le_hybridLeaf t m N shifts ht hm

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessValid t m L N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L
        (zetaAProcessLeafSquaredBound t m N) N depth [] :=
  norm_zetaPhase_sum_sq_le_recursiveAProcess
    t m L N depth ht hm hvalid

example (t : ℝ) (m : ℕ) (L : List ℕ → ℕ) (N depth : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : RecursiveZetaAProcessScaleValid t m L N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L
        (zetaAProcessLeafSquaredBound t m N) N depth [] :=
  norm_zetaPhase_sum_sq_le_recursiveAProcess_of_scale
    t m L N depth ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
