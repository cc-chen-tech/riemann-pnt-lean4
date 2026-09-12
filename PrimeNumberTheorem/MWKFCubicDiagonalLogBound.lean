import MathlibAux.GcdLcmLogBound
import PrimeNumberTheorem.MWKFCubicDiagonalLogKernel

open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Finite bounds for the actual cubic diagonal logarithmic kernel

These theorems specialize the coefficient-uniform reciprocal-LCM bound to the
literal linearly tapered Möbius coefficient at `floor (T^3)`.  They are finite
inequalities only.  No Selberg--Perron asymptotic and no off-diagonal decay is
asserted here.
-/

private theorem abs_cubicMollifierCoefficient_le_one
    (T : ℝ) (hN : 2 ≤ cubicMollifierLength T)
    {n : ℕ} (hn : n ∈ cubicMollifierSupport T) :
    |cubicMollifierCoefficient T n| ≤ 1 := by
  exact HardyTheorem.abs_selbergMoebiusCoeff_le_one hN
    (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2

/-- Exact harmonic-number bound for the actual cubic logarithmic diagonal
kernel. -/
theorem abs_cubicReciprocalLcmLogKernel_le_harmonic
    (T c : ℝ) (hN : 2 ≤ cubicMollifierLength T) :
    |cubicReciprocalLcmLogKernel T c| ≤
      (|c| + 4 * Real.log (cubicMollifierLength T)) *
        ∑ d ∈ cubicMollifierSupport T,
          (d : ℝ)⁻¹ *
            (harmonic (cubicMollifierLength T / d) : ℝ) ^ 2 := by
  unfold cubicReciprocalLcmLogKernel
  exact MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_harmonic
    (cubicMollifierCoefficient T) (cubicMollifierLength T) c hN
      (fun n hn => abs_cubicMollifierCoefficient_le_one T hN hn)

/-- Closed cubic-logarithm bound for the actual cubic logarithmic diagonal
kernel, assuming its exact natural cutoff is at least two. -/
theorem abs_cubicReciprocalLcmLogKernel_le_log_cube
    (T c : ℝ) (hN : 2 ≤ cubicMollifierLength T) :
    |cubicReciprocalLcmLogKernel T c| ≤
      (|c| + 4 * Real.log (cubicMollifierLength T)) *
        (1 + Real.log (cubicMollifierLength T)) ^ 3 := by
  unfold cubicReciprocalLcmLogKernel
  exact MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_log_cube
    (cubicMollifierCoefficient T) (cubicMollifierLength T) c hN
      (fun n hn => abs_cubicMollifierCoefficient_le_one T hN hn)

/-- The exact coefficient `6` version of F6 for the actual cubic mollifier. -/
theorem abs_cubicReciprocalLcmLogKernel_le_log_cube_six
    (T c : ℝ) (hN : 2 ≤ cubicMollifierLength T) :
    |cubicReciprocalLcmLogKernel T c| ≤
      (|c| + 6 * Real.log (cubicMollifierLength T)) *
        (1 + Real.log (cubicMollifierLength T)) ^ 3 := by
  unfold cubicReciprocalLcmLogKernel
  exact MathlibAux.abs_sum_reciprocal_lcm_log_kernel_le_log_cube_six
    (cubicMollifierCoefficient T) (cubicMollifierLength T) c hN
      (fun n hn => abs_cubicMollifierCoefficient_le_one T hN hn)

/-- A real-scale hypothesis `2 ≤ T^3` supplies the exact floor condition
needed by the finite cubic bound. -/
theorem abs_cubicReciprocalLcmLogKernel_le_log_cube_of_two_le_cube
    (T c : ℝ) (hT : (2 : ℝ) ≤ T ^ 3) :
    |cubicReciprocalLcmLogKernel T c| ≤
      (|c| + 4 * Real.log (cubicMollifierLength T)) *
        (1 + Real.log (cubicMollifierLength T)) ^ 3 := by
  apply abs_cubicReciprocalLcmLogKernel_le_log_cube T c
  exact Nat.le_floor hT

end PrimeNumberTheorem.MWKFCubic
