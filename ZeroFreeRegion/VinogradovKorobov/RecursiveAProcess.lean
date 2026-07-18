import ZeroFreeRegion.VinogradovKorobov.IteratedDifference

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- The block length remaining after applying all shifts in `shifts`. -/
def remainingAProcessLength (N : ℕ) (shifts : List ℕ) : ℕ :=
  N - shifts.sum

/-- Recursive numerical envelope for an arbitrary finite A-process tree.
`L shifts` chooses the next differencing length, while `Q shifts` is the
terminal squared bound at a leaf. -/
noncomputable def recursiveAProcessSquaredBound
    (L : List ℕ → ℕ) (Q : List ℕ → ℝ) (N : ℕ) :
    ℕ → List ℕ → ℝ
  | 0, shifts => Q shifts
  | depth + 1, shifts =>
      aProcessSquaredBound
        (fun ell ↦ Real.sqrt
          (recursiveAProcessSquaredBound L Q N depth (ell :: shifts)))
        (remainingAProcessLength N shifts) (L shifts)

/-- Proof obligations for a recursive A-process tree.  Internal nodes carry
the admissibility of the chosen differencing length; leaves carry the actual
terminal exponential-sum estimate. -/
def RecursiveAProcessValid
    (f : ℕ → ℝ) (L : List ℕ → ℕ) (Q : List ℕ → ℝ) (N : ℕ) :
    ℕ → List ℕ → Prop
  | 0, shifts =>
      ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
          phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤ Q shifts
  | depth + 1, shifts =>
      1 ≤ L shifts ∧
      L shifts ≤ remainingAProcessLength N shifts ∧
      ∀ ell ∈ Finset.Icc 1 (L shifts - 1),
        RecursiveAProcessValid f L Q N depth (ell :: shifts)

@[simp] lemma remainingAProcessLength_cons
    (N ell : ℕ) (shifts : List ℕ) :
    remainingAProcessLength N (ell :: shifts) =
      remainingAProcessLength N shifts - ell := by
  unfold remainingAProcessLength
  simp only [List.sum_cons]
  omega

@[simp] lemma recursiveAProcessSquaredBound_zero
    (L : List ℕ → ℕ) (Q : List ℕ → ℝ) (N : ℕ) (shifts : List ℕ) :
    recursiveAProcessSquaredBound L Q N 0 shifts = Q shifts := rfl

@[simp] lemma recursiveAProcessSquaredBound_succ
    (L : List ℕ → ℕ) (Q : List ℕ → ℝ) (N depth : ℕ)
    (shifts : List ℕ) :
    recursiveAProcessSquaredBound L Q N (depth + 1) shifts =
      aProcessSquaredBound
        (fun ell ↦ Real.sqrt
          (recursiveAProcessSquaredBound L Q N depth (ell :: shifts)))
        (remainingAProcessLength N shifts) (L shifts) := rfl

/-- Soundness of an arbitrary finite recursive A-process tree. -/
theorem norm_iteratedPhase_sum_sq_le_recursiveAProcess
    (f : ℕ → ℝ) (L : List ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ) (shifts : List ℕ)
    (hvalid : RecursiveAProcessValid f L Q N depth shifts) :
    ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L Q N depth shifts := by
  induction depth generalizing shifts with
  | zero =>
      exact hvalid
  | succ depth ih =>
      rcases hvalid with ⟨hL, hLN, hchildren⟩
      apply norm_iteratedPhase_sum_sq_le_aProcess_of_sq_bounds
        f shifts
        (fun ell ↦ recursiveAProcessSquaredBound L Q N depth (ell :: shifts))
        (remainingAProcessLength N shifts) (L shifts) hL hLN
      intro ell hell
      simpa only [remainingAProcessLength_cons] using
        ih (ell :: shifts) (hchildren ell hell)

/-- Root form of recursive A-process soundness. -/
theorem norm_phaseSum_sq_le_recursiveAProcess
    (f : ℕ → ℝ) (L : List ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ)
    (hvalid : RecursiveAProcessValid f L Q N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm f n‖ ^ 2 ≤
      recursiveAProcessSquaredBound L Q N depth [] := by
  simpa only [remainingAProcessLength, List.sum_nil, Nat.sub_zero,
    iteratedPhaseDifference_nil] using
    norm_iteratedPhase_sum_sq_le_recursiveAProcess
      f L Q N depth [] hvalid

end ZeroFreeRegion.VinogradovKorobov
