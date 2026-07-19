import ZeroFreeRegion.VinogradovKorobov.PowerDecayAProcess
import ZeroFreeRegion.VinogradovKorobov.ConstantAProcessSchedule

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- Explicit constant-schedule majorant for the path-decaying coefficient.
Unlike the exact finite-sum recurrence, each step displays the retained
negative power of the differencing length. -/
noncomputable def constantPowerDecayCoefficientMajorant
    (h N : ℕ) (C : ℝ) : ℕ → ℝ
  | 0 => (N : ℝ) * Real.sqrt C
  | depth + 1 =>
      8 * (N : ℝ) * Real.sqrt
          (constantPowerDecayCoefficientMajorant h N C depth) /
        (1 - aProcessPowerDecayExponent depth / 2) *
          (h : ℝ) ^ (-(aProcessPowerDecayExponent depth / 2))

@[simp] lemma constantPowerDecayCoefficientMajorant_zero
    (h N : ℕ) (C : ℝ) :
    constantPowerDecayCoefficientMajorant h N C 0 =
      (N : ℝ) * Real.sqrt C := rfl

@[simp] lemma constantPowerDecayCoefficientMajorant_succ
    (h N : ℕ) (C : ℝ) (depth : ℕ) :
    constantPowerDecayCoefficientMajorant h N C (depth + 1) =
      8 * (N : ℝ) * Real.sqrt
          (constantPowerDecayCoefficientMajorant h N C depth) /
        (1 - aProcessPowerDecayExponent depth / 2) *
          (h : ℝ) ^ (-(aProcessPowerDecayExponent depth / 2)) := rfl

theorem constantPowerDecayCoefficientMajorant_nonneg
    (h N : ℕ) (C : ℝ) (depth : ℕ) :
    0 ≤ constantPowerDecayCoefficientMajorant h N C depth := by
  induction depth with
  | zero =>
      rw [constantPowerDecayCoefficientMajorant_zero]
      positivity
  | succ depth ih =>
      rw [constantPowerDecayCoefficientMajorant_succ]
      have hden : 0 < 1 - aProcessPowerDecayExponent depth / 2 := by
        have := aProcessPowerDecayExponent_le_one depth
        linarith
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hden.le)
        (Real.rpow_nonneg (Nat.cast_nonneg h) _)

/-- The path-independent constant recurrence agrees with the existing
constant-schedule A-process recurrence started from zero. -/
theorem aProcessPowerDecayConstant_const
    (h N : ℕ) (C : ℝ) (depth level : ℕ) :
    aProcessPowerDecayConstant (fun _ ↦ h) N C depth level =
      constantAProcessSquaredEnvelope h N 0 depth := by
  induction depth generalizing level with
  | zero => simp
  | succ depth ih =>
      rw [aProcessPowerDecayConstant_succ,
        constantAProcessSquaredEnvelope_succ, ih]

/-- For a constant differencing schedule, the exact path-decay coefficient
is bounded by the recurrence that exposes one real-power saving at every
level. -/
theorem aProcessPowerDecayCoefficient_const_le_majorant
    (h N : ℕ) (C : ℝ) (depth level : ℕ) (hh : 2 ≤ h) :
    aProcessPowerDecayCoefficient (fun _ ↦ h) N C depth level ≤
      constantPowerDecayCoefficientMajorant h N C depth := by
  induction depth generalizing level with
  | zero => simp
  | succ depth ih =>
      have hstep := aProcessPowerDecayCoefficient_succ_le_rpow
        (fun _ ↦ h) N C depth level hh
      calc
        aProcessPowerDecayCoefficient (fun _ ↦ h) N C (depth + 1) level ≤
            8 * (N : ℝ) * Real.sqrt
                (aProcessPowerDecayCoefficient (fun _ ↦ h) N C depth
                  (level + 1)) /
              (1 - aProcessPowerDecayExponent depth / 2) *
                (h : ℝ) ^ (-(aProcessPowerDecayExponent depth / 2)) := hstep
        _ ≤ 8 * (N : ℝ) * Real.sqrt
                (constantPowerDecayCoefficientMajorant h N C depth) /
              (1 - aProcessPowerDecayExponent depth / 2) *
                (h : ℝ) ^ (-(aProcessPowerDecayExponent depth / 2)) := by
          have hden : 0 < 1 - aProcessPowerDecayExponent depth / 2 := by
            have := aProcessPowerDecayExponent_le_one depth
            linarith
          have hpow : 0 ≤
              (h : ℝ) ^ (-(aProcessPowerDecayExponent depth / 2)) :=
            Real.rpow_nonneg (Nat.cast_nonneg h) _
          have hsqrt := Real.sqrt_le_sqrt (ih (level + 1))
          exact mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt (by positivity)) hden.le)
            hpow
        _ = constantPowerDecayCoefficientMajorant h N C (depth + 1) := rfl

/-- Constant-schedule logarithmic exponential-sum estimate with the
small-product/trivial leaves retained.  No lower-scale condition is needed;
only the ordinary finite differencing budget and upper-turn condition remain. -/
theorem norm_zetaPhase_sum_sq_le_constantPowerDecayMajorant
    (t : ℝ) (m N depth h : ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hh : 2 ≤ h) (hhN : h ≤ N)
    (hbudget : depth * (h - 1) < N)
    (hmajor : t * ((depth.factorial : ℝ) * (h : ℝ) ^ depth *
      ((m : ℝ) ^ (depth + 1))⁻¹) ≤ Real.pi) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      constantAProcessSquaredEnvelope h N 0 depth +
        constantPowerDecayCoefficientMajorant h N
          (zetaAProcessUniformLeafSquaredBound t m N depth) depth := by
  have hschedule : ZetaAProcessScheduleValid t m N depth (fun _ ↦ h) :=
    zetaAProcessScheduleValid_const t m N depth h (by omega)
      hbudget hmajor
  have hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ (fun _ ↦ h) s.length) N depth [] :=
    recursiveZetaAProcessScaleValid_of_schedule
      t m N depth (fun _ ↦ h) ht hm hschedule
  have hroot := norm_zetaPhase_sum_sq_le_powerDecayEnvelope_of_scale
    t m N depth (fun _ ↦ h) ht hm (fun _ ↦ hh) (fun _ ↦ hhN) hvalid
  calc
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
        aProcessPowerDecayEnvelope (fun _ ↦ h) N
          (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 1 := hroot
    _ = constantAProcessSquaredEnvelope h N 0 depth +
        aProcessPowerDecayCoefficient (fun _ ↦ h) N
          (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 := by
      unfold aProcessPowerDecayEnvelope
      rw [aProcessPowerDecayConstant_const]
      simp
    _ ≤ constantAProcessSquaredEnvelope h N 0 depth +
        constantPowerDecayCoefficientMajorant h N
          (zetaAProcessUniformLeafSquaredBound t m N depth) depth :=
      add_le_add_right
        (aProcessPowerDecayCoefficient_const_le_majorant h N
          (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 hh) _

end ZeroFreeRegion.VinogradovKorobov
