import ZeroFreeRegion.VinogradovKorobov.RecursiveReciprocalEnvelope

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

/-- Normalized product-sensitive recurrence for a constant A-process
schedule.  Its terminal value contains the full `h^(2 * totalDepth)` leaf
gain before the recurrence is propagated back to the root. -/
noncomputable def constantRefinedAProcessSquaredEnvelope
    (h N : ℕ) (C : ℝ) (totalDepth : ℕ) : ℕ → ℝ
  | 0 => C / (h : ℝ) ^ (2 * totalDepth)
  | depth + 1 =>
      2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt
          (constantRefinedAProcessSquaredEnvelope h N C totalDepth depth)

@[simp] lemma constantRefinedAProcessSquaredEnvelope_zero
    (h N : ℕ) (C : ℝ) (totalDepth : ℕ) :
    constantRefinedAProcessSquaredEnvelope h N C totalDepth 0 =
      C / (h : ℝ) ^ (2 * totalDepth) := rfl

@[simp] lemma constantRefinedAProcessSquaredEnvelope_succ
    (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ) :
    constantRefinedAProcessSquaredEnvelope h N C totalDepth (depth + 1) =
      2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt
          (constantRefinedAProcessSquaredEnvelope
            h N C totalDepth depth) := rfl

theorem constantRefinedAProcessSquaredEnvelope_nonneg
    (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ) (hC : 0 ≤ C) :
    0 ≤ constantRefinedAProcessSquaredEnvelope h N C totalDepth depth := by
  induction depth with
  | zero =>
      rw [constantRefinedAProcessSquaredEnvelope_zero]
      exact div_nonneg hC (by positivity)
  | succ depth ih =>
      rw [constantRefinedAProcessSquaredEnvelope_succ]
      have hlog : 0 ≤ Real.log (h : ℝ) := by
        by_cases hzero : h = 0
        · simp [hzero]
        · exact Real.log_nonneg (by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzero))
      have hharm : 0 ≤ 1 + Real.log (h : ℝ) := by linarith
      positivity

/-- At a fixed total depth, the level-indexed refined recurrence factors as
the square of the accumulated constant schedule product times the normalized
one-variable recurrence. -/
theorem refinedRecursiveAProcessSquaredBound_const
    (h N : ℕ) (C : ℝ) (totalDepth depth level : ℕ)
    (hh : 1 ≤ h) (hC : 0 ≤ C) (hlevel : level + depth = totalDepth) :
    refinedRecursiveAProcessSquaredBound (fun _ ↦ h) N C depth level =
      (h : ℝ) ^ (2 * level) *
        constantRefinedAProcessSquaredEnvelope h N C totalDepth depth := by
  induction depth generalizing level with
  | zero =>
      have hcast : (h : ℝ) ≠ 0 := by positivity
      simp only [refinedRecursiveAProcessSquaredBound_zero,
        constantRefinedAProcessSquaredEnvelope_zero]
      subst totalDepth
      simp only [Nat.add_zero]
      field_simp
  | succ depth ih =>
      have hnextLevel : level + 1 + depth = totalDepth := by omega
      have hinner := ih (level + 1) hnextLevel
      have hK : 0 ≤ constantRefinedAProcessSquaredEnvelope
          h N C totalDepth depth :=
        constantRefinedAProcessSquaredEnvelope_nonneg
          h N C totalDepth depth hC
      have hpow : 0 ≤ (h : ℝ) ^ (level + 1) := by positivity
      have hpowSquare :
          (h : ℝ) ^ (2 * (level + 1)) =
            ((h : ℝ) ^ (level + 1)) ^ 2 := by
        rw [show 2 * (level + 1) = (level + 1) * 2 by omega, pow_mul]
      have hsqrt :
          Real.sqrt ((h : ℝ) ^ (2 * (level + 1)) *
            constantRefinedAProcessSquaredEnvelope h N C totalDepth depth) =
            (h : ℝ) ^ (level + 1) * Real.sqrt
              (constantRefinedAProcessSquaredEnvelope
                h N C totalDepth depth) := by
        rw [hpowSquare, Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq_eq_abs, abs_of_nonneg hpow]
      rw [refinedRecursiveAProcessSquaredBound_succ,
        constantRefinedAProcessSquaredEnvelope_succ]
      simp only [aProcessScheduleProduct_const, Nat.cast_pow, hinner, hsqrt]
      have hcast : (h : ℝ) ≠ 0 := by positivity
      simp only [pow_succ]
      field_simp
      ring

/-- Root form of the constant-schedule normalization. -/
theorem refinedRecursiveAProcessSquaredBound_const_root
    (h N : ℕ) (C : ℝ) (depth : ℕ)
    (hh : 1 ≤ h) (hC : 0 ≤ C) :
    refinedRecursiveAProcessSquaredBound (fun _ ↦ h) N C depth 0 =
      constantRefinedAProcessSquaredEnvelope h N C depth depth := by
  simpa using refinedRecursiveAProcessSquaredBound_const
    h N C depth depth 0 hh hC (by simp)

/-- Constant-schedule zeta estimate in the normalized product-sensitive
recurrence, with the full terminal `h^(2 * depth)` gain exposed. -/
theorem norm_zetaPhase_sum_sq_le_constantRefinedAProcessSquaredEnvelope
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantRefinedAProcessSquaredEnvelope h N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth depth := by
  have hrefined :=
    norm_zetaPhase_sum_sq_le_scheduledRefinedRecursiveAProcess
      t m N depth (fun _ ↦ h) ht hm
      (zetaAProcessScheduleValid_const
        t m N depth h hh hbudget hmajor)
  rw [refinedRecursiveAProcessSquaredBound_const_root
    h N (zetaAProcessUniformLeafSquaredBound t m N depth) depth hh
    (sq_nonneg _)] at hrefined
  exact hrefined

end ZeroFreeRegion.VinogradovKorobov
