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

example (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ) (K : ℕ → ℝ)
    (hh : 1 ≤ h)
    (hinit : C / (h : ℝ) ^ (2 * totalDepth) ≤ K 0)
    (hstep : ∀ j < depth,
      2 * (N : ℝ) ^ 2 / h +
          4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt (K j) ≤ K (j + 1)) :
    constantRefinedAProcessSquaredEnvelope h N C totalDepth depth ≤ K depth :=
  constantRefinedAProcessSquaredEnvelope_le_of_finite_supersolution
    h N C totalDepth depth K hh hinit hstep

example (t : ℝ) (m N depth h : ℕ) (K : ℕ → ℝ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hinit : zetaAProcessUniformLeafSquaredBound t m N depth /
        (h : ℝ) ^ (2 * depth) ≤ K 0)
    (hstep : ∀ j < depth,
      2 * (N : ℝ) ^ 2 / h +
          4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt (K j) ≤ K (j + 1)) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      K depth :=
  norm_zetaPhase_sum_sq_le_constantRefined_finite_supersolution
    t m N depth h K ht hm hh hbudget hmajor hinit hstep

example (h N j : ℕ) :
    constantAProcessPowerSupersolution h N j =
      constantAProcessCoefficient h j * (N : ℝ) ^ 2 /
        constantAProcessGain h j := rfl

example (h j : ℕ) :
    constantAProcessGain h j =
      (h : ℝ) ^ (2 / (2 : ℝ) ^ j : ℝ) :=
  constantAProcessGain_eq_rpow h j

example (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ)
    (hh : 1 ≤ h)
    (hinit : C / (h : ℝ) ^ (2 * totalDepth) ≤
      (N : ℝ) ^ 2 / (h : ℝ) ^ 2) :
    constantRefinedAProcessSquaredEnvelope h N C totalDepth depth ≤
      constantAProcessPowerSupersolution h N depth :=
  constantRefinedAProcessSquaredEnvelope_le_powerSupersolution
    h N C totalDepth depth hh hinit

example (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hinit : zetaAProcessUniformLeafSquaredBound t m N depth /
        (h : ℝ) ^ (2 * depth) ≤ (N : ℝ) ^ 2 / (h : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantAProcessPowerSupersolution h N depth :=
  norm_zetaPhase_sum_sq_le_constantAProcessPowerSupersolution
    t m N depth h ht hm hh hbudget hmajor hinit

example (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hN : 0 < N)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hinit : zetaAProcessUniformLeafSquaredBound t m N depth /
        (h : ℝ) ^ (2 * depth) ≤ (N : ℝ) ^ 2 / (h : ℝ) ^ 2)
    (hsaving : constantAProcessCoefficient h depth <
      constantAProcessGain h depth) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ < (N : ℝ) :=
  norm_zetaPhase_sum_lt_length_of_constantAProcessPowerSaving
    t m N depth h ht hm hN hh hbudget hmajor hinit hsaving

end ZeroFreeRegion.VinogradovKorobov
