import ZeroFreeRegion.VinogradovKorobov.HybridAProcessEnvelope

namespace ZeroFreeRegion.VinogradovKorobov

/-- Accumulated-product decay exponent after a fixed number of A-process
steps.  Each step halves the exponent. -/
noncomputable def aProcessPowerDecayExponent : ℕ → ℝ
  | 0 => 1
  | depth + 1 => aProcessPowerDecayExponent depth / 2

/-- Path-independent part of the power-decay A-process supersolution. -/
noncomputable def aProcessPowerDecayConstant
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | depth + 1, level =>
      2 * (N : ℝ) ^ 2 / H level +
        4 * (N : ℝ) * Real.sqrt
          (aProcessPowerDecayConstant H N C depth (level + 1))

/-- Coefficient of the accumulated-product decay in the A-process
supersolution. -/
noncomputable def aProcessPowerDecayCoefficient
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => (N : ℝ) * Real.sqrt C
  | depth + 1, level =>
      4 * (N : ℝ) * Real.sqrt
          (aProcessPowerDecayCoefficient H N C depth (level + 1)) *
        finiteRpowSumEnvelope (H level)
          (aProcessPowerDecayExponent depth / 2) /
        H level

/-- Closed power-form supersolution at accumulated path product `P`. -/
noncomputable def aProcessPowerDecayEnvelope
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ)
    (depth level : ℕ) (P : ℝ) : ℝ :=
  aProcessPowerDecayConstant H N C depth level +
    aProcessPowerDecayCoefficient H N C depth level *
      P ^ (-aProcessPowerDecayExponent depth)

@[simp] lemma aProcessPowerDecayExponent_zero :
    aProcessPowerDecayExponent 0 = 1 := rfl

@[simp] lemma aProcessPowerDecayExponent_succ (depth : ℕ) :
    aProcessPowerDecayExponent (depth + 1) =
      aProcessPowerDecayExponent depth / 2 := rfl

@[simp] lemma aProcessPowerDecayConstant_zero
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (level : ℕ) :
    aProcessPowerDecayConstant H N C 0 level = 0 := rfl

@[simp] lemma aProcessPowerDecayConstant_succ
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) :
    aProcessPowerDecayConstant H N C (depth + 1) level =
      2 * (N : ℝ) ^ 2 / H level +
        4 * (N : ℝ) * Real.sqrt
          (aProcessPowerDecayConstant H N C depth (level + 1)) := rfl

@[simp] lemma aProcessPowerDecayCoefficient_zero
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (level : ℕ) :
    aProcessPowerDecayCoefficient H N C 0 level =
      (N : ℝ) * Real.sqrt C := rfl

@[simp] lemma aProcessPowerDecayCoefficient_succ
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) :
    aProcessPowerDecayCoefficient H N C (depth + 1) level =
      4 * (N : ℝ) * Real.sqrt
          (aProcessPowerDecayCoefficient H N C depth (level + 1)) *
        finiteRpowSumEnvelope (H level)
          (aProcessPowerDecayExponent depth / 2) /
        H level := rfl

theorem aProcessPowerDecayExponent_pos (depth : ℕ) :
    0 < aProcessPowerDecayExponent depth := by
  induction depth with
  | zero => norm_num
  | succ depth ih =>
      rw [aProcessPowerDecayExponent_succ]
      positivity

theorem aProcessPowerDecayExponent_le_one (depth : ℕ) :
    aProcessPowerDecayExponent depth ≤ 1 := by
  induction depth with
  | zero => norm_num
  | succ depth ih =>
      rw [aProcessPowerDecayExponent_succ]
      have hpos := aProcessPowerDecayExponent_pos depth
      linarith

theorem aProcessPowerDecayConstant_nonneg
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) :
    0 ≤ aProcessPowerDecayConstant H N C depth level := by
  induction depth generalizing level with
  | zero => simp
  | succ depth ih =>
      rw [aProcessPowerDecayConstant_succ]
      have hH0 : 0 ≤ (H level : ℝ) := Nat.cast_nonneg _
      exact add_nonneg (div_nonneg (by positivity) hH0)
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _))

theorem aProcessPowerDecayCoefficient_nonneg
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ)
    (hH : ∀ j, 2 ≤ H j) :
    0 ≤ aProcessPowerDecayCoefficient H N C depth level := by
  induction depth generalizing level with
  | zero =>
      simp only [aProcessPowerDecayCoefficient_zero]
      exact mul_nonneg (Nat.cast_nonneg N) (Real.sqrt_nonneg C)
  | succ depth ih =>
      rw [aProcessPowerDecayCoefficient_succ]
      have hExp0 : 0 ≤ aProcessPowerDecayExponent depth / 2 := by
        have := aProcessPowerDecayExponent_pos depth
        linarith
      have hExp1 : aProcessPowerDecayExponent depth / 2 < 1 := by
        have := aProcessPowerDecayExponent_le_one depth
        linarith
      have hEnv := finiteRpowSumEnvelope_nonneg
        (H level) (aProcessPowerDecayExponent depth / 2)
        (hH level) hExp0 hExp1
      exact div_nonneg (mul_nonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) hEnv)
        (Nat.cast_nonneg _)

/-- The product-sensitive recursive envelope is dominated by a closed form
consisting of a path-independent constant and one negative power of the
accumulated product. -/
theorem hybridProductRecursiveAProcessSquaredBound_le_powerDecay
    (H : ℕ → ℕ) (N : ℕ) (C : ℝ) (depth level : ℕ) (P : ℝ)
    (hC : 0 ≤ C) (hP : 0 < P)
    (hHlower : ∀ j, 2 ≤ H j) (hHupper : ∀ j, H j ≤ N) :
    hybridProductRecursiveAProcessSquaredBound H N C depth level P ≤
      aProcessPowerDecayEnvelope H N C depth level P := by
  induction depth generalizing level P with
  | zero =>
      simpa [aProcessPowerDecayEnvelope, Real.rpow_neg_one] using
        hybridProductLeafSquaredEnvelope_le_power N C P hC hP
  | succ depth ih =>
      let A := aProcessPowerDecayConstant H N C depth (level + 1)
      let D := aProcessPowerDecayCoefficient H N C depth (level + 1)
      let α := aProcessPowerDecayExponent depth
      have hA : 0 ≤ A := aProcessPowerDecayConstant_nonneg
        H N C depth (level + 1)
      have hD : 0 ≤ D := aProcessPowerDecayCoefficient_nonneg
        H N C depth (level + 1) hHlower
      have hα0 : 0 ≤ α := (aProcessPowerDecayExponent_pos depth).le
      have hα2 : α < 2 :=
        (aProcessPowerDecayExponent_le_one depth).trans_lt (by norm_num)
      have hPpow : 0 ≤ P ^ (-α) := Real.rpow_nonneg hP.le _
      have hstep := aProcessSquaredBound_le_sqrt_add_rpow
        (fun ell ↦ hybridProductRecursiveAProcessSquaredBound H N C depth
          (level + 1) ((ell : ℝ) * P))
        A (D * P ^ (-α)) α N (H level)
        (hHlower level) (hHupper level) hA (mul_nonneg hD hPpow)
        hα0 hα2 (by
          intro ell hell
          have hellPos : 0 < ell := (Finset.mem_Icc.mp hell).1
          have hellReal : 0 < (ell : ℝ) := Nat.cast_pos.mpr hellPos
          calc
            hybridProductRecursiveAProcessSquaredBound H N C depth
                (level + 1) ((ell : ℝ) * P) ≤
              aProcessPowerDecayEnvelope H N C depth (level + 1)
                ((ell : ℝ) * P) :=
              ih (level + 1) ((ell : ℝ) * P) (mul_pos hellReal hP)
            _ = A + (D * P ^ (-α)) * (ell : ℝ) ^ (-α) := by
              unfold aProcessPowerDecayEnvelope
              dsimp only [A, D, α]
              rw [Real.mul_rpow hellReal.le hP.le]
              ring)
      have hsqrtP : Real.sqrt (P ^ (-α)) = P ^ (-(α / 2)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP.le (-α) (1 / 2 : ℝ)]
        congr 1
        ring
      have hsqrtDP : Real.sqrt (D * P ^ (-α)) =
          Real.sqrt D * P ^ (-(α / 2)) := by
        rw [Real.sqrt_mul hD, hsqrtP]
      rw [hybridProductRecursiveAProcessSquaredBound_succ]
      exact hstep.trans_eq (by
        unfold aProcessPowerDecayEnvelope
        rw [aProcessPowerDecayConstant_succ,
          aProcessPowerDecayCoefficient_succ,
          aProcessPowerDecayExponent_succ, hsqrtDP]
        dsimp only [A, D, α]
        have hHnat : H level ≠ 0 := by
          have := hHlower level
          omega
        have hHne : (H level : ℝ) ≠ 0 := by
          exact_mod_cast hHnat
        field_simp
        ring)

/-- Zeta exponential-sum form of the arbitrary-depth power-decay envelope. -/
theorem norm_zetaPhase_sum_sq_le_powerDecayEnvelope_of_scale
    (t : ℝ) (m N depth : ℕ) (H : ℕ → ℕ)
    (ht : 0 < t) (hm : 0 < m)
    (hHlower : ∀ j, 2 ≤ H j) (hHupper : ∀ j, H j ≤ N)
    (hvalid : RecursiveZetaAProcessScaleValid
      t m (fun s ↦ H s.length) N depth []) :
    ‖∑ n ∈ Finset.range N, phaseTerm (shiftedZetaPhase t m) n‖ ^ 2 ≤
      aProcessPowerDecayEnvelope H N
        (zetaAProcessUniformLeafSquaredBound t m N depth) depth 0 1 := by
  have hC : 0 ≤ zetaAProcessUniformLeafSquaredBound t m N depth :=
    sq_nonneg _
  exact (norm_zetaPhase_sum_sq_le_hybridProductEnvelope_of_scale
    t m N depth H ht hm hvalid).trans
      (hybridProductRecursiveAProcessSquaredBound_le_powerDecay
        H N (zetaAProcessUniformLeafSquaredBound t m N depth)
        depth 0 1 hC (by norm_num) hHlower hHupper)

end ZeroFreeRegion.VinogradovKorobov
