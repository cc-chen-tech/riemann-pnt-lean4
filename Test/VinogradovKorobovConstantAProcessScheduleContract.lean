import ZeroFreeRegion.VinogradovKorobov.ConstantAProcessSchedule

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (h N : ℕ) (C : ℝ) (depth : ℕ) : ℝ :=
  constantAProcessSquaredEnvelope h N C depth

example (h N : ℕ) (C : ℝ) (depth level : ℕ) :
    coarseRecursiveAProcessSquaredBound (fun _ ↦ h) N C depth level =
      constantAProcessSquaredEnvelope h N C depth :=
  coarseRecursiveAProcessSquaredBound_const h N C depth level

example (h N : ℕ) (C K : ℝ) (depth : ℕ)
    (hCK : C ≤ K)
    (hK : 2 * (N : ℝ) ^ 2 / h + 4 * (N : ℝ) * Real.sqrt K ≤ K) :
    constantAProcessSquaredEnvelope h N C depth ≤ K :=
  constantAProcessSquaredEnvelope_le_of_supersolution
    h N C K depth hCK hK

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

example (t : ℝ) (m N depth h : ℕ) (K : ℝ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hleaf : zetaAProcessUniformLeafSquaredBound t m N depth ≤ K)
    (hK : 2 * (N : ℝ) ^ 2 / h + 4 * (N : ℝ) * Real.sqrt K ≤ K) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤ K :=
  norm_zetaPhase_sum_sq_le_constantAProcess_supersolution
    t m N depth h K ht hm hh hbudget hmajor hleaf hK

noncomputable example (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ) : ℝ :=
  constantRefinedAProcessSquaredEnvelope h N C totalDepth depth

example (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ) (hC : 0 ≤ C) :
    0 ≤ constantRefinedAProcessSquaredEnvelope h N C totalDepth depth :=
  constantRefinedAProcessSquaredEnvelope_nonneg
    h N C totalDepth depth hC

example (h N : ℕ) (C : ℝ) (totalDepth depth level : ℕ)
    (hh : 1 ≤ h) (hC : 0 ≤ C) (hlevel : level + depth = totalDepth) :
    refinedRecursiveAProcessSquaredBound (fun _ ↦ h) N C depth level =
      (h : ℝ) ^ (2 * level) *
        constantRefinedAProcessSquaredEnvelope h N C totalDepth depth :=
  refinedRecursiveAProcessSquaredBound_const
    h N C totalDepth depth level hh hC hlevel

example (h N : ℕ) (C : ℝ) (depth : ℕ)
    (hh : 1 ≤ h) (hC : 0 ≤ C) :
    refinedRecursiveAProcessSquaredBound (fun _ ↦ h) N C depth 0 =
      constantRefinedAProcessSquaredEnvelope h N C depth depth :=
  refinedRecursiveAProcessSquaredBound_const_root h N C depth hh hC

example (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantRefinedAProcessSquaredEnvelope h N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth depth :=
  norm_zetaPhase_sum_sq_le_constantRefinedAProcessSquaredEnvelope
    t m N depth h ht hm hh hbudget hmajor

end ZeroFreeRegion.VinogradovKorobov
