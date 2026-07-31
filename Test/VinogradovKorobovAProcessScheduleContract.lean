import ZeroFreeRegion.VinogradovKorobov.AProcessSchedule

namespace ZeroFreeRegion.VinogradovKorobov

example (H : ℕ → ℕ) (depth : ℕ) : ℕ :=
  aProcessScheduleBudget H depth

example (H : ℕ → ℕ) (depth : ℕ) : ℕ :=
  aProcessScheduleProduct H depth

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ) : Prop :=
  ZetaAProcessScheduleValid t m N depth H

example (N depth : ℕ) (H : ℕ → ℕ) : Prop :=
  AProcessScheduleAdmissible N depth H

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hadmissible : AProcessScheduleAdmissible N depth H) :
    RecursiveAProcessValid (shiftedZetaPhase t m) (fun s ↦ H s.length)
      (zetaAProcessHybridLeafSquaredBound t m N) N depth [] :=
  recursiveZetaAProcessHybridValid_of_schedule
    t m N depth H ht hm hadmissible

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hadmissible : AProcessScheduleAdmissible N depth H) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      recursiveAProcessSquaredBound (fun s ↦ H s.length)
        (zetaAProcessHybridLeafSquaredBound t m N) N depth [] :=
  norm_zetaPhase_sum_sq_le_scheduledHybridRecursiveAProcess
    t m N depth H ht hm hadmissible

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScheduleValid t m N depth H) :
    RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth [] :=
  recursiveZetaAProcessScaleValid_of_schedule
    t m N depth H ht hm hvalid

example (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hvalid : ZetaAProcessScheduleValid t m N depth H) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      coarseRecursiveAProcessSquaredBound H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 :=
  norm_zetaPhase_sum_sq_le_scheduledCoarseRecursiveAProcess
    t m N depth H ht hm hvalid

end ZeroFreeRegion.VinogradovKorobov
