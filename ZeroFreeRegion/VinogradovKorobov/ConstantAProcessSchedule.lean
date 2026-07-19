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

/-- A finite supersolution sequence controls every finite iterate of the
normalized refined recurrence without replacing it by a depth-independent
fixed point. -/
theorem constantRefinedAProcessSquaredEnvelope_le_of_finite_supersolution
    (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ) (K : ℕ → ℝ)
    (hh : 1 ≤ h)
    (hinit : C / (h : ℝ) ^ (2 * totalDepth) ≤ K 0)
    (hstep : ∀ j < depth,
      2 * (N : ℝ) ^ 2 / h +
          4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt (K j) ≤ K (j + 1)) :
    constantRefinedAProcessSquaredEnvelope h N C totalDepth depth ≤ K depth := by
  have hlog : 0 ≤ Real.log (h : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hh)
  have hharm : 0 ≤ 1 + Real.log (h : ℝ) := by linarith
  induction depth with
  | zero => exact hinit
  | succ depth ih =>
      rw [constantRefinedAProcessSquaredEnvelope_succ]
      have ih' : constantRefinedAProcessSquaredEnvelope
          h N C totalDepth depth ≤ K depth :=
        ih (fun j hj ↦ hstep j (lt_trans hj (Nat.lt_succ_self depth)))
      calc
        2 * (N : ℝ) ^ 2 / h +
            4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt
              (constantRefinedAProcessSquaredEnvelope
                h N C totalDepth depth) ≤
          2 * (N : ℝ) ^ 2 / h +
            4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt (K depth) := by
              gcongr
        _ ≤ K (depth + 1) := hstep depth (Nat.lt_succ_self depth)

/-- Zeta exponential-sum bound obtained by supplying a finite supersolution
sequence for the normalized constant-schedule recurrence. -/
theorem norm_zetaPhase_sum_sq_le_constantRefined_finite_supersolution
    (t : ℝ) (m N depth h : ℕ) (K : ℕ → ℝ)
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
      K depth := by
  exact (norm_zetaPhase_sum_sq_le_constantRefinedAProcessSquaredEnvelope
    t m N depth h ht hm hh hbudget hmajor).trans
      (constantRefinedAProcessSquaredEnvelope_le_of_finite_supersolution
        h N (zetaAProcessUniformLeafSquaredBound t m N depth)
        depth depth K hh hinit hstep)

/-- Denominator gain remaining after repeated square-root propagation. -/
noncomputable def constantAProcessGain (h : ℕ) : ℕ → ℝ
  | 0 => (h : ℝ) ^ 2
  | j + 1 => Real.sqrt (constantAProcessGain h j)

/-- Coefficient growth accompanying the repeated square-root propagation. -/
noncomputable def constantAProcessCoefficient (h : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 =>
      2 + 4 * (1 + Real.log h) * Real.sqrt (constantAProcessCoefficient h j)

/-- Explicit power-saving candidate for every stage of the normalized
constant-schedule recurrence. -/
noncomputable def constantAProcessPowerSupersolution
    (h N j : ℕ) : ℝ :=
  constantAProcessCoefficient h j * (N : ℝ) ^ 2 /
    constantAProcessGain h j

@[simp] lemma constantAProcessGain_zero (h : ℕ) :
    constantAProcessGain h 0 = (h : ℝ) ^ 2 := rfl

@[simp] lemma constantAProcessGain_succ (h j : ℕ) :
    constantAProcessGain h (j + 1) = Real.sqrt (constantAProcessGain h j) := rfl

@[simp] lemma constantAProcessCoefficient_zero (h : ℕ) :
    constantAProcessCoefficient h 0 = 1 := rfl

@[simp] lemma constantAProcessCoefficient_succ (h j : ℕ) :
    constantAProcessCoefficient h (j + 1) =
      2 + 4 * (1 + Real.log h) * Real.sqrt
        (constantAProcessCoefficient h j) := rfl

theorem constantAProcessGain_pos
    (h j : ℕ) (hh : 1 ≤ h) : 0 < constantAProcessGain h j := by
  induction j with
  | zero =>
      rw [constantAProcessGain_zero]
      positivity
  | succ j ih =>
      rw [constantAProcessGain_succ]
      exact Real.sqrt_pos.2 ih

theorem constantAProcessGain_succ_le
    (h j : ℕ) (hh : 1 ≤ h) :
    constantAProcessGain h (j + 1) ≤ (h : ℝ) := by
  induction j with
  | zero =>
      rw [constantAProcessGain_succ, constantAProcessGain_zero,
        Real.sqrt_sq (Nat.cast_nonneg h)]
  | succ j ih =>
      rw [constantAProcessGain_succ]
      apply (Real.sqrt_le_iff).2
      refine ⟨Nat.cast_nonneg h, ?_⟩
      have hhreal : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
      exact ih.trans (by nlinarith)

/-- Closed form of the denominator gain: every A-process level halves the
power of `h` retained in the final estimate. -/
theorem constantAProcessGain_eq_rpow
    (h j : ℕ) :
    constantAProcessGain h j =
      (h : ℝ) ^ (2 / (2 : ℝ) ^ j : ℝ) := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      rw [constantAProcessGain_succ, ih, Real.sqrt_eq_rpow,
        ← Real.rpow_mul (Nat.cast_nonneg h)]
      congr 1
      rw [pow_succ]
      have hpow : (2 : ℝ) ^ j ≠ 0 := by positivity
      field_simp

/-- Square root of the retained gain, in the exponent used by the final
linear exponential-sum bound. -/
theorem sqrt_constantAProcessGain_eq_rpow (h j : ℕ) :
    Real.sqrt (constantAProcessGain h j) =
      (h : ℝ) ^ (1 / (2 : ℝ) ^ j : ℝ) := by
  rw [constantAProcessGain_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg h)]
  congr 1
  have hpow : (2 : ℝ) ^ j ≠ 0 := by positivity
  field_simp

theorem constantAProcessCoefficient_nonneg
    (h j : ℕ) : 0 ≤ constantAProcessCoefficient h j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [constantAProcessCoefficient_succ]
      have hlog : 0 ≤ Real.log (h : ℝ) := by
        by_cases hzero : h = 0
        · simp [hzero]
        · exact Real.log_nonneg (by
            exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzero))
      positivity

/-- Uniform depth-independent bound for the coefficient growth in the
explicit power supersolution. -/
theorem constantAProcessCoefficient_le_log_sq
    (h j : ℕ) (hh : 1 ≤ h) :
    constantAProcessCoefficient h j ≤
      36 * (1 + Real.log h) ^ 2 := by
  let L := 1 + Real.log (h : ℝ)
  have hlog : 0 ≤ Real.log (h : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hh)
  have hL : 1 ≤ L := by dsimp only [L]; linarith
  have hLsq : 1 ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
  induction j with
  | zero =>
      rw [constantAProcessCoefficient_zero]
      change 1 ≤ 36 * L ^ 2
      nlinarith
  | succ j ih =>
      rw [constantAProcessCoefficient_succ]
      change 2 + 4 * L * Real.sqrt (constantAProcessCoefficient h j) ≤
        36 * L ^ 2
      have hsqrt : Real.sqrt (constantAProcessCoefficient h j) ≤ 6 * L := by
        apply (Real.sqrt_le_iff).2
        refine ⟨by linarith, ?_⟩
        calc
          constantAProcessCoefficient h j ≤ 36 * L ^ 2 := ih
          _ = (6 * L) ^ 2 := by ring
      nlinarith

/-- Closed-form sufficient condition for the coefficient to be smaller than
the retained denominator gain. -/
theorem constantAProcessCoefficient_lt_gain_of_log_sq_lt_rpow
    (h depth : ℕ) (hh : 1 ≤ h)
    (hsaving : 36 * (1 + Real.log h) ^ 2 <
      (h : ℝ) ^ (2 / (2 : ℝ) ^ depth : ℝ)) :
    constantAProcessCoefficient h depth < constantAProcessGain h depth := by
  rw [constantAProcessGain_eq_rpow]
  exact (constantAProcessCoefficient_le_log_sq h depth hh).trans_lt hsaving

theorem constantAProcessPowerSupersolution_step
    (h N j : ℕ) (hh : 1 ≤ h) :
    2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt
          (constantAProcessPowerSupersolution h N j) ≤
      constantAProcessPowerSupersolution h N (j + 1) := by
  let D := constantAProcessCoefficient h j
  let G := constantAProcessGain h j
  have hD : 0 ≤ D := constantAProcessCoefficient_nonneg h j
  have hG : 0 < G := constantAProcessGain_pos h j hh
  have hGnext : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  have hroot :
      Real.sqrt (D * (N : ℝ) ^ 2 / G) ≤
        Real.sqrt D * (N : ℝ) / Real.sqrt G := by
    apply (Real.sqrt_le_iff).2
    refine ⟨div_nonneg
      (mul_nonneg (Real.sqrt_nonneg D) (Nat.cast_nonneg N)) hGnext.le, ?_⟩
    rw [div_pow, mul_pow, Real.sq_sqrt hD,
      Real.sq_sqrt hG.le]
  have hfirst :
      2 * (N : ℝ) ^ 2 / h ≤
        2 * (N : ℝ) ^ 2 / Real.sqrt G := by
    apply div_le_div_of_nonneg_left (by positivity) hGnext
    simpa only [G, ← constantAProcessGain_succ] using
      constantAProcessGain_succ_le h j hh
  have hlog : 0 ≤ Real.log (h : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hh)
  have hharm : 0 ≤ 1 + Real.log (h : ℝ) := by linarith
  unfold constantAProcessPowerSupersolution
  change
    2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt
          (D * (N : ℝ) ^ 2 / G) ≤
      (2 + 4 * (1 + Real.log h) * Real.sqrt D) *
        (N : ℝ) ^ 2 / Real.sqrt G
  calc
    2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * (1 + Real.log h) * Real.sqrt
          (D * (N : ℝ) ^ 2 / G) ≤
      2 * (N : ℝ) ^ 2 / h +
        4 * (N : ℝ) * (1 + Real.log h) *
          (Real.sqrt D * (N : ℝ) / Real.sqrt G) := by gcongr
    _ ≤ 2 * (N : ℝ) ^ 2 / Real.sqrt G +
        4 * (N : ℝ) * (1 + Real.log h) *
          (Real.sqrt D * (N : ℝ) / Real.sqrt G) :=
      add_le_add hfirst le_rfl
    _ = (2 + 4 * (1 + Real.log h) * Real.sqrt D) *
        (N : ℝ) ^ 2 / Real.sqrt G := by ring

theorem constantRefinedAProcessSquaredEnvelope_le_powerSupersolution
    (h N : ℕ) (C : ℝ) (totalDepth depth : ℕ)
    (hh : 1 ≤ h)
    (hinit : C / (h : ℝ) ^ (2 * totalDepth) ≤
      (N : ℝ) ^ 2 / (h : ℝ) ^ 2) :
    constantRefinedAProcessSquaredEnvelope h N C totalDepth depth ≤
      constantAProcessPowerSupersolution h N depth := by
  apply constantRefinedAProcessSquaredEnvelope_le_of_finite_supersolution
    h N C totalDepth depth (constantAProcessPowerSupersolution h N) hh
  · simpa [constantAProcessPowerSupersolution] using hinit
  · intro j hj
    exact constantAProcessPowerSupersolution_step h N j hh

theorem norm_zetaPhase_sum_sq_le_constantAProcessPowerSupersolution
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hinit : zetaAProcessUniformLeafSquaredBound t m N depth /
        (h : ℝ) ^ (2 * depth) ≤ (N : ℝ) ^ 2 / (h : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantAProcessPowerSupersolution h N depth := by
  exact (norm_zetaPhase_sum_sq_le_constantRefinedAProcessSquaredEnvelope
    t m N depth h ht hm hh hbudget hmajor).trans
      (constantRefinedAProcessSquaredEnvelope_le_powerSupersolution
        h N (zetaAProcessUniformLeafSquaredBound t m N depth)
        depth depth hh hinit)

/-- A division-free scale condition implies the normalized terminal leaf
bound required by the explicit power supersolution. -/
theorem zetaAProcessUniformLeafSquaredBound_normalized_le_of_scale
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hh : 0 < h)
    (hscale : 2 * Real.pi * (h : ℝ) ≤
      zetaAProcessUniformLeafDeltaLower t m N depth *
        (h : ℝ) ^ depth * (N : ℝ)) :
    zetaAProcessUniformLeafSquaredBound t m N depth /
        (h : ℝ) ^ (2 * depth) ≤ (N : ℝ) ^ 2 / (h : ℝ) ^ 2 := by
  let D := zetaAProcessUniformLeafDeltaLower t m N depth
  have hD : 0 < D := by
    dsimp only [D]
    unfold zetaAProcessUniformLeafDeltaLower
    have hmN : 0 < ((m + N : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    positivity
  have hhreal : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hpow : 0 < (h : ℝ) ^ depth := by positivity
  have hquot :
      2 * Real.pi / (D * (h : ℝ) ^ depth) ≤ (N : ℝ) / h := by
    apply (div_le_div_iff₀ (mul_pos hD hpow) hhreal).2
    simpa only [D, mul_assoc, mul_comm, mul_left_comm] using hscale
  have hquotNonneg : 0 ≤ 2 * Real.pi / (D * (h : ℝ) ^ depth) :=
    div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (mul_pos hD hpow).le
  have hNquotNonneg : 0 ≤ (N : ℝ) / h :=
    div_nonneg (Nat.cast_nonneg N) hhreal.le
  unfold zetaAProcessUniformLeafSquaredBound
  change (2 * Real.pi / D) ^ 2 / (h : ℝ) ^ (2 * depth) ≤
    (N : ℝ) ^ 2 / (h : ℝ) ^ 2
  rw [show 2 * depth = depth * 2 by omega, pow_mul]
  calc
    (2 * Real.pi / D) ^ 2 / ((h : ℝ) ^ depth) ^ 2 =
        (2 * Real.pi / (D * (h : ℝ) ^ depth)) ^ 2 := by
      field_simp
    _ ≤ ((N : ℝ) / h) ^ 2 :=
      (sq_le_sq₀ hquotNonneg hNquotNonneg).2 hquot
    _ = (N : ℝ) ^ 2 / (h : ℝ) ^ 2 := by rw [div_pow]

/-- Explicit criterion under which the arbitrary-depth A-process estimate is
strictly better than the trivial length bound. -/
theorem norm_zetaPhase_sum_lt_length_of_constantAProcessPowerSaving
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hN : 0 < N)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hinit : zetaAProcessUniformLeafSquaredBound t m N depth /
        (h : ℝ) ^ (2 * depth) ≤ (N : ℝ) ^ 2 / (h : ℝ) ^ 2)
    (hsaving : constantAProcessCoefficient h depth <
      constantAProcessGain h depth) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ < (N : ℝ) := by
  have hsq := norm_zetaPhase_sum_sq_le_constantAProcessPowerSupersolution
    t m N depth h ht hm hh hbudget hmajor hinit
  have hgain : 0 < constantAProcessGain h depth :=
    constantAProcessGain_pos h depth hh
  have hNsq : 0 < (N : ℝ) ^ 2 := by positivity
  have hupper : constantAProcessPowerSupersolution h N depth <
      (N : ℝ) ^ 2 := by
    unfold constantAProcessPowerSupersolution
    rw [div_lt_iff₀ hgain]
    nlinarith
  rw [← sq_lt_sq₀ (norm_nonneg _) (Nat.cast_nonneg N)]
  exact hsq.trans_lt hupper

/-- Nontrivial logarithmic exponential-sum estimate stated only with the
division-free terminal scale condition and the explicit coefficient/gain
comparison. -/
theorem norm_zetaPhase_sum_lt_length_of_constantAProcessScaleSaving
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hN : 0 < N)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : 2 * Real.pi * (h : ℝ) ≤
      zetaAProcessUniformLeafDeltaLower t m N depth *
        (h : ℝ) ^ depth * (N : ℝ))
    (hsaving : constantAProcessCoefficient h depth <
      constantAProcessGain h depth) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ < (N : ℝ) := by
  apply norm_zetaPhase_sum_lt_length_of_constantAProcessPowerSaving
    t m N depth h ht hm hN hh hbudget hmajor _ hsaving
  exact zetaAProcessUniformLeafSquaredBound_normalized_le_of_scale
    t m N depth h ht hm (lt_of_lt_of_le Nat.zero_lt_one hh) hscale

/-- Fully explicit arbitrary-depth nontriviality criterion, with no recursive
coefficient or gain terms remaining in the hypotheses. -/
theorem norm_zetaPhase_sum_lt_length_of_constantAProcessExplicitSaving
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m) (hN : 0 < N)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : 2 * Real.pi * (h : ℝ) ≤
      zetaAProcessUniformLeafDeltaLower t m N depth *
        (h : ℝ) ^ depth * (N : ℝ))
    (hsaving : 36 * (1 + Real.log h) ^ 2 <
      (h : ℝ) ^ (2 / (2 : ℝ) ^ depth : ℝ)) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ < (N : ℝ) := by
  apply norm_zetaPhase_sum_lt_length_of_constantAProcessScaleSaving
    t m N depth h ht hm hN hh hbudget hmajor hscale
  exact constantAProcessCoefficient_lt_gain_of_log_sq_lt_rpow
    h depth hh hsaving

/-- Quantitative arbitrary-depth logarithmic exponential-sum estimate.  It
retains the explicit `h^(1 / 2^depth)` denominator needed for subsequent
Dirichlet-block and zeta-strip optimization. -/
theorem norm_zetaPhase_sum_le_constantAProcessExplicitPower
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 1 ≤ h) (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi)
    (hscale : 2 * Real.pi * (h : ℝ) ≤
      zetaAProcessUniformLeafDeltaLower t m N depth *
        (h : ℝ) ^ depth * (N : ℝ)) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ≤
      6 * (1 + Real.log h) * (N : ℝ) /
        (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ) := by
  have hinit :=
    zetaAProcessUniformLeafSquaredBound_normalized_le_of_scale
      t m N depth h ht hm (lt_of_lt_of_le Nat.zero_lt_one hh) hscale
  have hsq := norm_zetaPhase_sum_sq_le_constantAProcessPowerSupersolution
    t m N depth h ht hm hh hbudget hmajor hinit
  let D := constantAProcessCoefficient h depth
  let G := constantAProcessGain h depth
  have hD : 0 ≤ D := constantAProcessCoefficient_nonneg h depth
  have hG : 0 < G := constantAProcessGain_pos h depth hh
  have hGsqrt : 0 < Real.sqrt G := Real.sqrt_pos.2 hG
  have hnorm :
      ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ≤
        Real.sqrt (D * (N : ℝ) ^ 2 / G) := by
    exact Real.le_sqrt_of_sq_le hsq
  have hroot :
      Real.sqrt (D * (N : ℝ) ^ 2 / G) ≤
        Real.sqrt D * (N : ℝ) / Real.sqrt G := by
    apply (Real.sqrt_le_iff).2
    refine ⟨div_nonneg
      (mul_nonneg (Real.sqrt_nonneg D) (Nat.cast_nonneg N)) hGsqrt.le, ?_⟩
    rw [div_pow, mul_pow, Real.sq_sqrt hD, Real.sq_sqrt hG.le]
  have hlog : 0 ≤ Real.log (h : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hh)
  have hL : 0 ≤ 1 + Real.log (h : ℝ) := by linarith
  have hsqrtD : Real.sqrt D ≤ 6 * (1 + Real.log h) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    calc
      D ≤ 36 * (1 + Real.log h) ^ 2 :=
        constantAProcessCoefficient_le_log_sq h depth hh
      _ = (6 * (1 + Real.log h)) ^ 2 := by ring
  calc
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ≤
        Real.sqrt (D * (N : ℝ) ^ 2 / G) := hnorm
    _ ≤ Real.sqrt D * (N : ℝ) / Real.sqrt G := hroot
    _ ≤ 6 * (1 + Real.log h) * (N : ℝ) / Real.sqrt G := by
      apply div_le_div_of_nonneg_right _ hGsqrt.le
      gcongr
    _ = 6 * (1 + Real.log h) * (N : ℝ) /
        (h : ℝ) ^ (1 / (2 : ℝ) ^ depth : ℝ) := by
      dsimp only [G]
      rw [sqrt_constantAProcessGain_eq_rpow]

end ZeroFreeRegion.VinogradovKorobov
