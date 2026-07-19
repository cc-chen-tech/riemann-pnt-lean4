import ZeroFreeRegion.VinogradovKorobov.RecursiveZetaBounds

namespace ZeroFreeRegion.VinogradovKorobov

/-- Maximum total block length consumed by the first `depth` scheduled
A-process shifts. -/
def aProcessScheduleBudget (H : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | depth + 1 => aProcessScheduleBudget H depth + (H depth - 1)

/-- Product of the first `depth` scheduled differencing lengths. -/
def aProcessScheduleProduct (H : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | depth + 1 => aProcessScheduleProduct H depth * H depth

@[simp] lemma aProcessScheduleBudget_zero (H : ℕ → ℕ) :
    aProcessScheduleBudget H 0 = 0 := rfl

@[simp] lemma aProcessScheduleBudget_succ (H : ℕ → ℕ) (depth : ℕ) :
    aProcessScheduleBudget H (depth + 1) =
      aProcessScheduleBudget H depth + (H depth - 1) := rfl

@[simp] lemma aProcessScheduleProduct_zero (H : ℕ → ℕ) :
    aProcessScheduleProduct H 0 = 1 := rfl

@[simp] lemma aProcessScheduleProduct_succ (H : ℕ → ℕ) (depth : ℕ) :
    aProcessScheduleProduct H (depth + 1) =
      aProcessScheduleProduct H depth * H depth := rfl

lemma monotone_aProcessScheduleBudget (H : ℕ → ℕ) :
    Monotone (aProcessScheduleBudget H) := by
  apply monotone_nat_of_le_succ
  intro depth
  simp only [aProcessScheduleBudget_succ]
  omega

/-- Internal admissibility of a level schedule.  Unlike
`ZetaAProcessScheduleValid`, this only asks that every differencing length is
positive and that every root-to-leaf path fits inside the original block. -/
def AProcessScheduleAdmissible
    (N depth : ℕ) (H : ℕ → ℕ) : Prop :=
  (∀ level < depth, 1 ≤ H level) ∧
    aProcessScheduleBudget H depth < N

/-- Concrete sufficient conditions for a level schedule: all lengths are
positive, the worst path leaves at least one term, and the worst leaf phase
majorant stays below `pi`. -/
noncomputable def ZetaAProcessScheduleValid
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ) : Prop :=
  (∀ level < depth, 1 ≤ H level) ∧
    aProcessScheduleBudget H depth < N ∧
    t * ((depth.factorial : ℝ) *
      (aProcessScheduleProduct H depth : ℝ) *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi

/-- A schedule satisfying only the internal A-process constraints builds a
complete recursive tree with unconditional hybrid terminal bounds. -/
theorem recursiveZetaAProcessHybridValid_of_schedule_aux
    (t : ℝ) (m N totalDepth remainingDepth level : ℕ) (H : ℕ → ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hH : ∀ j < totalDepth, 1 ≤ H j)
    (hbudget : aProcessScheduleBudget H totalDepth < N)
    (hlevel : level + remainingDepth = totalDepth)
    (hlen : shifts.length = level)
    (hsum : shifts.sum ≤ aProcessScheduleBudget H level) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (zetaAProcessHybridLeafSquaredBound t m N) N remainingDepth shifts := by
  induction remainingDepth generalizing level shifts with
  | zero =>
      exact norm_iteratedZetaPhase_sum_sq_le_hybridLeaf
        t m N shifts ht hm
  | succ remainingDepth ih =>
      have hlevelLt : level < totalDepth := by omega
      have hHlevel : 1 ≤ H level := hH level hlevelLt
      have hbudgetNext : aProcessScheduleBudget H (level + 1) < N := by
        exact lt_of_le_of_lt
          (monotone_aProcessScheduleBudget H (by omega)) hbudget
      have hsumH : shifts.sum + H level ≤ N := by
        simp only [aProcessScheduleBudget_succ] at hbudgetNext
        omega
      have hL : 1 ≤ (fun s : List ℕ ↦ H s.length) shifts := by
        simpa only [hlen] using hHlevel
      have hLN : (fun s : List ℕ ↦ H s.length) shifts ≤
          remainingAProcessLength N shifts := by
        unfold remainingAProcessLength
        simpa only [hlen] using (show H level ≤ N - shifts.sum by omega)
      refine ⟨hL, hLN, ?_⟩
      intro ell hell
      have hell' : ell ∈ Finset.Icc 1 (H level - 1) := by
        simpa only [hlen] using hell
      rcases Finset.mem_Icc.mp hell' with ⟨hellPos, hellUpper⟩
      have hchildLevel : level + 1 + remainingDepth = totalDepth := by omega
      have hchildLen : (ell :: shifts).length = level + 1 := by
        simp only [List.length_cons, hlen]
      have hchildSum : (ell :: shifts).sum ≤
          aProcessScheduleBudget H (level + 1) := by
        simp only [List.sum_cons, aProcessScheduleBudget_succ]
        omega
      exact ih (level + 1) (ell :: shifts) hchildLevel hchildLen hchildSum

/-- Root form of the schedule-only hybrid tree construction. -/
theorem recursiveZetaAProcessHybridValid_of_schedule
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hadmissible : AProcessScheduleAdmissible N depth H) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (zetaAProcessHybridLeafSquaredBound t m N) N depth [] := by
  rcases hadmissible with ⟨hH, hbudget⟩
  apply recursiveZetaAProcessHybridValid_of_schedule_aux
    t m N depth depth 0 H [] ht hm hH hbudget
  · omega
  · simp
  · simp

/-- A schedule constrained only by the finite differencing budget yields a
root A-process estimate with hybrid terminal leaves. -/
theorem norm_zetaPhase_sum_sq_le_scheduledHybridRecursiveAProcess
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hadmissible : AProcessScheduleAdmissible N depth H) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound (fun s ↦ H s.length)
        (zetaAProcessHybridLeafSquaredBound t m N) N depth [] := by
  apply norm_phaseSum_sq_le_recursiveAProcess
  exact recursiveZetaAProcessHybridValid_of_schedule
    t m N depth H ht hm hadmissible

/-- Path-invariant form of schedule validity, used to construct the complete
recursive proof tree. -/
theorem recursiveZetaAProcessScaleValid_of_schedule_aux
    (t : ℝ) (m N totalDepth remainingDepth level : ℕ) (H : ℕ → ℕ)
    (shifts : List ℕ) (ht : 0 < t) (hm : 0 < m)
    (hH : ∀ j < totalDepth, 1 ≤ H j)
    (hbudget : aProcessScheduleBudget H totalDepth < N)
    (hmajor : t * ((totalDepth.factorial : ℝ) *
      (aProcessScheduleProduct H totalDepth : ℝ) *
      ((m : ℝ) ^ (totalDepth + 1))⁻¹) ≤ Real.pi)
    (hlevel : level + remainingDepth = totalDepth)
    (hlen : shifts.length = level)
    (hsum : shifts.sum ≤ aProcessScheduleBudget H level)
    (hprod : shifts.prod ≤ aProcessScheduleProduct H level)
    (hpos : ∀ h ∈ shifts, 0 < h) :
    RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N remainingDepth shifts := by
  induction remainingDepth generalizing level shifts with
  | zero =>
      have hlevelEq : level = totalDepth := by omega
      have hsumlt : shifts.sum < N := by
        exact lt_of_le_of_lt (hsum.trans (by
          simpa only [hlevelEq] using
            (le_refl (aProcessScheduleBudget H totalDepth)))) hbudget
      have hR : 1 ≤ remainingAProcessLength N shifts := by
        unfold remainingAProcessLength
        omega
      have hprodR : (shifts.prod : ℝ) ≤
          (aProcessScheduleProduct H totalDepth : ℝ) := by
        exact_mod_cast hprod.trans (by simp [hlevelEq])
      have hleafMajor : zetaAProcessLeafInitialMajorant t m shifts ≤
          t * ((totalDepth.factorial : ℝ) *
            (aProcessScheduleProduct H totalDepth : ℝ) *
            ((m : ℝ) ^ (totalDepth + 1))⁻¹) := by
        unfold zetaAProcessLeafInitialMajorant
        simp only [List.prod_cons, one_mul, prod_natShiftsToReal,
          List.length_cons, length_natShiftsToReal, hlen, hlevelEq]
        gcongr
      exact ⟨hR, hpos, hleafMajor.trans hmajor⟩
  | succ remainingDepth ih =>
      have hlevelLt : level < totalDepth := by omega
      have hHlevel : 1 ≤ H level := hH level hlevelLt
      have hbudgetNext : aProcessScheduleBudget H (level + 1) < N := by
        exact lt_of_le_of_lt
          (monotone_aProcessScheduleBudget H (by omega)) hbudget
      have hsumH : shifts.sum + H level ≤ N := by
        simp only [aProcessScheduleBudget_succ] at hbudgetNext
        omega
      have hL : 1 ≤ (fun s : List ℕ ↦ H s.length) shifts := by
        simpa only [hlen] using hHlevel
      have hLN : (fun s : List ℕ ↦ H s.length) shifts ≤
          remainingAProcessLength N shifts := by
        unfold remainingAProcessLength
        simpa only [hlen] using (show H level ≤ N - shifts.sum by omega)
      refine ⟨hL, hLN, ?_⟩
      intro ell hell
      have hell' : ell ∈ Finset.Icc 1 (H level - 1) := by
        simpa only [hlen] using hell
      rcases Finset.mem_Icc.mp hell' with ⟨hellPos, hellUpper⟩
      have hellH : ell ≤ H level := by omega
      have hchildLevel : level + 1 + remainingDepth = totalDepth := by omega
      have hchildLen : (ell :: shifts).length = level + 1 := by
        simp only [List.length_cons, hlen]
      have hchildSum : (ell :: shifts).sum ≤
          aProcessScheduleBudget H (level + 1) := by
        simp only [List.sum_cons, aProcessScheduleBudget_succ]
        omega
      have hchildProd : (ell :: shifts).prod ≤
          aProcessScheduleProduct H (level + 1) := by
        simp only [List.prod_cons, aProcessScheduleProduct_succ]
        simpa only [Nat.mul_comm] using Nat.mul_le_mul hellH hprod
      have hchildPos : ∀ h ∈ ell :: shifts, 0 < h := by
        intro h hh
        simp only [List.mem_cons] at hh
        rcases hh with rfl | hh
        · exact hellPos
        · exact hpos h hh
      exact ih (level + 1) (ell :: shifts) hchildLevel hchildLen
        hchildSum hchildProd hchildPos

/-- A valid level schedule automatically constructs every internal and leaf
obligation of the recursive zeta A-process. -/
theorem recursiveZetaAProcessScaleValid_of_schedule
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScheduleValid t m N depth H) :
    RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth [] := by
  rcases hvalid with ⟨hH, hbudget, hmajor⟩
  apply recursiveZetaAProcessScaleValid_of_schedule_aux
    t m N depth depth 0 H [] ht hm hH hbudget hmajor
  · omega
  · simp
  · simp
  · simp
  · simp

/-- A valid level schedule directly yields the path-independent recursive
envelope for the original logarithmic exponential sum. -/
theorem norm_zetaPhase_sum_sq_le_scheduledCoarseRecursiveAProcess
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScheduleValid t m N depth H) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 := by
  apply norm_zetaPhase_sum_sq_le_uniformCoarseRecursiveAProcess
    t m N depth H ht hm
  exact recursiveZetaAProcessScaleValid_of_schedule
    t m N depth H ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
