import ZeroFreeRegion.VinogradovKorobov.AProcessSchedule

namespace ZeroFreeRegion.VinogradovKorobov

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

end ZeroFreeRegion.VinogradovKorobov
