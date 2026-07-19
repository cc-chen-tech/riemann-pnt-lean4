import ZeroFreeRegion.VinogradovKorobov.AProcessSchedule

namespace ZeroFreeRegion.VinogradovKorobov

/-- One-variable numerical envelope for a constant differencing schedule. -/
noncomputable def constantAProcessSquaredEnvelope
    (h N : ℕ) (C : ℝ) : ℕ → ℝ
  | 0 => C
  | depth + 1 =>
      2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * Real.sqrt
          (constantAProcessSquaredEnvelope h N C depth)

@[simp] lemma constantAProcessSquaredEnvelope_zero
    (h N : ℕ) (C : ℝ) :
    constantAProcessSquaredEnvelope h N C 0 = C := rfl

@[simp] lemma constantAProcessSquaredEnvelope_succ
    (h N : ℕ) (C : ℝ) (depth : ℕ) :
    constantAProcessSquaredEnvelope h N C (depth + 1) =
      2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * Real.sqrt
          (constantAProcessSquaredEnvelope h N C depth) := rfl

/-- The generic level-indexed envelope loses its level dependence for a
constant schedule. -/
theorem coarseRecursiveAProcessSquaredBound_const
    (h N : ℕ) (C : ℝ) (depth level : ℕ) :
    coarseRecursiveAProcessSquaredBound (fun _ ↦ h) N C depth level =
      constantAProcessSquaredEnvelope h N C depth := by
  induction depth generalizing level with
  | zero => rfl
  | succ depth ih =>
      simp only [coarseRecursiveAProcessSquaredBound_succ,
        constantAProcessSquaredEnvelope_succ, ih]

/-- Any supersolution of the constant-schedule recurrence bounds every finite
iterate of that recurrence. -/
theorem constantAProcessSquaredEnvelope_le_of_supersolution
    (h N : ℕ) (C K : ℝ) (depth : ℕ)
    (hCK : C ≤ K)
    (hK : 2 * (N : ℝ) ^ 2 / h +
      4 * (N : ℝ) * Real.sqrt K ≤ K) :
    constantAProcessSquaredEnvelope h N C depth ≤ K := by
  induction depth with
  | zero => exact hCK
  | succ depth ih =>
      rw [constantAProcessSquaredEnvelope_succ]
      apply le_trans _ hK
      gcongr

@[simp] theorem aProcessScheduleBudget_const (h depth : ℕ) :
    aProcessScheduleBudget (fun _ ↦ h) depth = depth * (h - 1) := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      simp only [aProcessScheduleBudget_succ, ih]
      rw [Nat.succ_mul]

@[simp] theorem aProcessScheduleProduct_const (h depth : ℕ) :
    aProcessScheduleProduct (fun _ ↦ h) depth = h ^ depth := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      simp only [aProcessScheduleProduct_succ, ih, pow_succ]

/-- The three explicit constant-schedule inequalities imply abstract schedule
validity. -/
theorem zetaAProcessScheduleValid_const
    (t : ℝ) (m N depth h : ℕ)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ZetaAProcessScheduleValid t m N depth (fun _ ↦ h) := by
  refine ⟨?_, ?_, ?_⟩
  · intro level hlevel
    exact hh
  · simpa only [aProcessScheduleBudget_const] using hbudget
  · simpa only [aProcessScheduleProduct_const, Nat.cast_pow,
      Nat.cast_ofNat] using hmajor

/-- Explicit arbitrary-depth logarithmic exponential-sum estimate for a
constant differencing schedule. -/
theorem norm_zetaPhase_sum_sq_le_constantScheduledCoarseRecursiveAProcess
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound (fun _ ↦ h) N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 := by
  apply norm_zetaPhase_sum_sq_le_scheduledCoarseRecursiveAProcess
    t m N depth (fun _ ↦ h) ht hm
  exact zetaAProcessScheduleValid_const
    t m N depth h hh hbudget hmajor

/-- Constant-schedule estimate stated with the one-variable squared
envelope. -/
theorem norm_zetaPhase_sum_sq_le_constantAProcessSquaredEnvelope
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantAProcessSquaredEnvelope h N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth := by
  simpa only [coarseRecursiveAProcessSquaredBound_const] using
    norm_zetaPhase_sum_sq_le_constantScheduledCoarseRecursiveAProcess
      t m N depth h ht hm hh hbudget hmajor

/-- Constant-schedule estimate with the recurrence hidden behind a chosen
supersolution. -/
theorem norm_zetaPhase_sum_sq_le_constantAProcess_supersolution
    (t : ℝ) (m N depth h : ℕ) (K : ℝ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hleaf : zetaAProcessUniformLeafSquaredBound t m N depth ≤ K)
    (hK : 2 * (N : ℝ) ^ 2 / h +
      4 * (N : ℝ) * Real.sqrt K ≤ K) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤ K := by
  exact (norm_zetaPhase_sum_sq_le_constantAProcessSquaredEnvelope
    t m N depth h ht hm hh hbudget hmajor).trans
      (constantAProcessSquaredEnvelope_le_of_supersolution
        h N (zetaAProcessUniformLeafSquaredBound t m N depth)
        K depth hleaf hK)

end ZeroFreeRegion.VinogradovKorobov
