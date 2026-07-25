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

/-- The trivial squared estimate for an arbitrary iterated phase sum. -/
theorem norm_iteratedPhase_sum_sq_le_trivial
    (f : ℕ → ℝ) (N : ℕ) (shifts : List ℕ) :
    ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
        phaseTerm (iteratedPhaseDifference shifts f) n‖ ^ 2 ≤
      (remainingAProcessLength N shifts : ℝ) ^ 2 := by
  have hnorm :
      ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
          phaseTerm (iteratedPhaseDifference shifts f) n‖ ≤
        (remainingAProcessLength N shifts : ℝ) := by
    calc
      ‖∑ n ∈ Finset.range (remainingAProcessLength N shifts),
          phaseTerm (iteratedPhaseDifference shifts f) n‖ ≤
          ∑ n ∈ Finset.range (remainingAProcessLength N shifts),
            ‖phaseTerm (iteratedPhaseDifference shifts f) n‖ :=
        norm_sum_le _ _
      _ = (remainingAProcessLength N shifts : ℝ) := by
        simp only [norm_phaseTerm, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
  exact (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).2 hnorm

/-- The normalized one-step A-process envelope is nonnegative whenever its
child bounds are nonnegative on the range used by the recurrence. -/
theorem aProcessSquaredBound_nonneg
    (B : ℕ → ℝ) (N L : ℕ) (hL : 1 ≤ L)
    (hB : ∀ ell ∈ Finset.Icc 1 (L - 1), 0 ≤ B ell) :
    0 ≤ aProcessSquaredBound B N L := by
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have hspan : 0 ≤ (N : ℝ) + ((L : ℝ) - 1) := by
    have hLone : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hsum :
      0 ≤ ∑ ell ∈ Finset.Icc 1 (L - 1),
        ((L : ℝ) - (ell : ℝ)) * B ell := by
    apply Finset.sum_nonneg
    intro ell hell
    have hellL : ell ≤ L := by
      have := (Finset.mem_Icc.mp hell).2
      omega
    exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hellL)) (hB ell hell)
  unfold aProcessSquaredBound
  apply add_nonneg
  · exact div_nonneg (mul_nonneg hspan (Nat.cast_nonneg N)) hLpos.le
  · exact div_nonneg
      (mul_nonneg (mul_nonneg (by positivity) hspan) hsum)
      (sq_nonneg (L : ℝ))

/-- Every valid recursive envelope with nonnegative terminal data is itself
nonnegative.  At an internal node this follows directly from the square-root
children used by the A-process recurrence. -/
theorem recursiveAProcessSquaredBound_nonneg
    (f : ℕ → ℝ) (L : List ℕ → ℕ) (Q : List ℕ → ℝ)
    (N depth : ℕ) (shifts : List ℕ)
    (hQ : ∀ s, 0 ≤ Q s)
    (hvalid : RecursiveAProcessValid f L Q N depth shifts) :
    0 ≤ recursiveAProcessSquaredBound L Q N depth shifts := by
  cases depth with
  | zero =>
      exact hQ shifts
  | succ depth =>
      apply aProcessSquaredBound_nonneg
      · exact hvalid.1
      · intro ell hell
        exact Real.sqrt_nonneg _

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
