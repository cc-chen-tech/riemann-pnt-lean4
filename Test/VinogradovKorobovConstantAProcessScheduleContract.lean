import ZeroFreeRegion.VinogradovKorobov.ConstantAProcessSchedule

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (h N : ℕ) (C : ℝ) (depth : ℕ) : ℝ :=
  constantAProcessSquaredEnvelope h N C depth

example (h N : ℕ) (C : ℝ) (depth level : ℕ) :
    coarseRecursiveAProcessSquaredBound (fun _ ↦ h) N C depth level =
      constantAProcessSquaredEnvelope h N C depth :=
  coarseRecursiveAProcessSquaredBound_const h N C depth level

example (h depth : ℕ) :
    aProcessScheduleBudget (fun _ ↦ h) depth = depth * (h - 1) :=
  aProcessScheduleBudget_const h depth

example (h depth : ℕ) :
    aProcessScheduleProduct (fun _ ↦ h) depth = h ^ depth :=
  aProcessScheduleProduct_const h depth

example (t : ℝ) (m N depth h : ℕ)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ZetaAProcessScheduleValid t m N depth (fun _ ↦ h) :=
  zetaAProcessScheduleValid_const
    t m N depth h hh hbudget hmajor

example (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound (fun _ ↦ h) N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 :=
  norm_zetaPhase_sum_sq_le_constantScheduledCoarseRecursiveAProcess
    t m N depth h ht hm hh hbudget hmajor

example (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantAProcessSquaredEnvelope h N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth :=
  norm_zetaPhase_sum_sq_le_constantAProcessSquaredEnvelope
    t m N depth h ht hm hh hbudget hmajor

end ZeroFreeRegion.VinogradovKorobov
