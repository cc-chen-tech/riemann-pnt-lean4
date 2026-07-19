import HardyTheorem.HardyPhaseLinearization
import HardyTheorem.FirstZetaApproximation

open Complex MeasureTheory Set
open scoped BigOperators

namespace HardyTheorem

open OscillatoryIntegral

/-- The first Hardy model with each short phase integral replaced by its
tangent-line model at the left endpoint. -/
noncomputable def hardyPhaseLinearizedSum
    (T delta t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
      hardyPhaseLinearizedShortIntegral n delta t

private theorem norm_inv_nat_cpow_half {n : ℕ} (hn : 0 < n) :
    ‖((n : ℂ) ^ (1 / 2 : ℂ))⁻¹‖ = (Real.sqrt n)⁻¹ := by
  rw [norm_inv, Complex.norm_natCast_cpow_of_pos hn]
  norm_num [Real.sqrt_eq_rpow]

/-- Summing the phase-linearization error over the first Hardy model costs
the reciprocal-square-root mass of its finite Dirichlet polynomial. -/
theorem norm_hardyPhaseSum_sub_linearized_le
    {T delta t : ℝ} (hT : 0 < T) (hTt : T ≤ t)
    (hdelta : 0 ≤ delta) :
    ‖(∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            hardyPhaseShortIntegral n delta t) -
        hardyPhaseLinearizedSum T delta t‖ ≤
      (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          (Real.sqrt n)⁻¹) * (delta ^ 3 / (2 * T)) := by
  rw [hardyPhaseLinearizedSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
        (((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            hardyPhaseShortIntegral n delta t -
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            hardyPhaseLinearizedShortIntegral n delta t)‖ ≤
        ∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          ‖((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
              hardyPhaseShortIntegral n delta t -
            ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
              hardyPhaseLinearizedShortIntegral n delta t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
        (Real.sqrt n)⁻¹ * (delta ^ 3 / (2 * T)) := by
      apply Finset.sum_le_sum
      intro n hnmem
      have hn : 0 < n := (Finset.mem_Icc.mp hnmem).1
      rw [← mul_sub, norm_mul, norm_inv_nat_cpow_half hn]
      exact mul_le_mul_of_nonneg_left
        (norm_hardyPhaseShortIntegral_sub_linearized_le
          (Nat.ne_of_gt hn) hT hTt hdelta)
        (by positivity)
    _ = (∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          (Real.sqrt n)⁻¹) * (delta ^ 3 / (2 * T)) := by
      rw [Finset.sum_mul]

/-- The accumulated tangent-line error has the expected square-root cutoff
bound. -/
theorem norm_hardyPhaseSum_sub_linearized_le_sqrtCutoff
    {T delta t : ℝ} (hT : 0 < T) (hTt : T ≤ t)
    (hdelta : 0 ≤ delta) :
    ‖(∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
          ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ *
            hardyPhaseShortIntegral n delta t) -
        hardyPhaseLinearizedSum T delta t‖ ≤
      2 * Real.sqrt (firstZetaApproximationCutoff T) *
        (delta ^ 3 / (2 * T)) := by
  refine (norm_hardyPhaseSum_sub_linearized_le hT hTt hdelta).trans ?_
  exact mul_le_mul_of_nonneg_right
    (sum_inv_sqrt_Icc_one_le_two_sqrt
      (firstZetaApproximationCutoff T)) (by positivity)

end HardyTheorem
