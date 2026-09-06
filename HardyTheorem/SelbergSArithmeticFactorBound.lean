import HardyTheorem.SelbergSArithmeticGrouped

open Complex Nat
open scoped BigOperators

namespace HardyTheorem

/-! # The exact exponent cancellation in the grouped S12 factors -/

theorem selberg_rpow_shift_local_cancel
    {X d : ℝ} (theta : ℝ) (hX : 0 < X) (hd : 0 < d) :
    d ^ (theta - 1) * (X / d) ^ theta = X ^ theta / d := by
  rw [Real.rpow_sub_one hd.ne' theta, Real.div_rpow hX.le hd.le]
  field_simp [Real.rpow_pos_of_pos hd theta]

theorem norm_selbergSmoothOuterFactor
    {X d : ℕ} (theta : ℝ) (hX : 1 < X) (hd : 0 < d) :
    ‖selbergSmoothOuterFactor X theta d‖ =
      |selbergSqrtZetaCoeff d| * (d : ℝ) ^ (theta - 1) /
        Real.log (X : ℝ) := by
  unfold selbergSmoothOuterFactor
  rw [norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hd]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by exact_mod_cast hX))]
  congr 2
  ring

noncomputable def selbergGroupedLocalMajorant
    (E : ℝ) (rho X : ℕ) (theta : ℝ) (d : ℕ) : ℝ :=
  E * |selbergSqrtZetaCoeff d| * ((X : ℝ) ^ theta) / (d : ℝ) *
      Real.sqrt (Real.log (X : ℝ)) *
      Real.sqrt (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹)) /
    Real.log (X : ℝ)

private theorem norm_selbergGroupedLocalFactor_le_of_s12
    {E : ℝ} {rho X d : ℕ} {theta : ℝ}
    (hX : 1 < X) (hd : 0 < d)
    (hS12 :
      ‖selbergS12WeightedCoprimeSumReal rho theta
          ((X : ℝ) / (d : ℝ))‖ ≤
        E * (((X : ℝ) / (d : ℝ)) ^ theta) *
          Real.sqrt (Real.log (X : ℝ)) *
          Real.sqrt (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹))) :
    ‖selbergSmoothOuterFactor X theta d *
        selbergS12WeightedCoprimeSumReal rho theta
          ((X : ℝ) / (d : ℝ))‖ ≤
      selbergGroupedLocalMajorant E rho X theta d := by
  rw [norm_mul]
  calc
    ‖selbergSmoothOuterFactor X theta d‖ *
        ‖selbergS12WeightedCoprimeSumReal rho theta
          ((X : ℝ) / (d : ℝ))‖ ≤
      ‖selbergSmoothOuterFactor X theta d‖ *
        (E * (((X : ℝ) / (d : ℝ)) ^ theta) *
          Real.sqrt (Real.log (X : ℝ)) *
          Real.sqrt (∏ p ∈ rho.primeFactors, (1 + (p : ℝ)⁻¹))) :=
      mul_le_mul_of_nonneg_left hS12 (norm_nonneg _)
    _ = selbergGroupedLocalMajorant E rho X theta d := by
      rw [norm_selbergSmoothOuterFactor theta hX hd]
      unfold selbergGroupedLocalMajorant
      have hcancel := selberg_rpow_shift_local_cancel
        (X := (X : ℝ)) (d := (d : ℝ)) theta
        (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast hd)
      calc
        |selbergSqrtZetaCoeff d| * (d : ℝ) ^ (theta - 1) /
              Real.log (X : ℝ) *
            (E * (((X : ℝ) / (d : ℝ)) ^ theta) *
              Real.sqrt (Real.log (X : ℝ)) *
              Real.sqrt (∏ p ∈ rho.primeFactors,
                (1 + (p : ℝ)⁻¹))) =
          E * |selbergSqrtZetaCoeff d| *
              ((d : ℝ) ^ (theta - 1) *
                (((X : ℝ) / (d : ℝ)) ^ theta)) *
              Real.sqrt (Real.log (X : ℝ)) *
              Real.sqrt (∏ p ∈ rho.primeFactors,
                (1 + (p : ℝ)⁻¹)) /
              Real.log (X : ℝ) := by
            ring
        _ = E * |selbergSqrtZetaCoeff d| * ((X : ℝ) ^ theta) /
              (d : ℝ) * Real.sqrt (Real.log (X : ℝ)) *
              Real.sqrt (∏ p ∈ rho.primeFactors,
                (1 + (p : ℝ)⁻¹)) /
              Real.log (X : ℝ) := by
            rw [hcancel]
            ring

/-- Uniform local factor bound obtained from the real-cutoff S12 estimate. -/
theorem exists_norm_selbergGroupedLocalFactor_le :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (rho : ℕ) [NeZero rho] (theta : ℝ) (X : ℕ)
        (d : selbergSmoothOuterIndex rho X),
        0 ≤ theta → Real.exp 1 ≤ (X : ℝ) →
        ‖selbergSmoothOuterFactor X theta d.1 *
            selbergS12WeightedCoprimeSumReal rho theta
              ((X : ℝ) / (d.1 : ℝ))‖ ≤
          selbergGroupedLocalMajorant E rho X theta d.1 := by
  rcases exists_norm_selbergS12WeightedCoprimeSumReal_context_le with
    ⟨E, hE, hcontext⟩
  refine ⟨E, hE, ?_⟩
  intro rho _ theta X d htheta hXexp
  have hXreal : 0 < (X : ℝ) :=
    (Real.exp_pos 1).trans_le hXexp
  have hXnat : 1 < X := by
    exact_mod_cast ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hXexp)
  have hd : 0 < d.1 :=
    Nat.zero_lt_of_lt (Finset.mem_Icc.mp d.2.1).1
  have hdreal : 0 < (d.1 : ℝ) := by exact_mod_cast hd
  have hY : 0 < (X : ℝ) / (d.1 : ℝ) := div_pos hXreal hdreal
  have hdOne : (1 : ℝ) ≤ d.1 := by
    exact_mod_cast (Finset.mem_Icc.mp d.2.1).1
  have hYX : (X : ℝ) / (d.1 : ℝ) ≤ (X : ℝ) := by
    exact (div_le_iff₀ hdreal).2 (by nlinarith)
  exact norm_selbergGroupedLocalFactor_le_of_s12 hXnat hd
    (hcontext rho theta (X : ℝ) ((X : ℝ) / (d.1 : ℝ))
      htheta hXexp hY hYX)

end HardyTheorem
