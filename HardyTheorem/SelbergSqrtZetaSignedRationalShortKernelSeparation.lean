import HardyTheorem.SelbergSqrtZetaSignedRationalSeparation
import HardyTheorem.SelbergSqrtZetaSignedRationalShortKernelPhase

/-!
# Arithmetic separation for the signed rational short kernel

The actual rational frequency support is separated by `1 / (N * X^2)`.
Consequently, whenever the short-window drift scale `H / T` is no larger
than this arithmetic spacing, every distinct supported frequency pair is
uniformly nonstationary in the exact Hermitian short kernel.
-/

namespace HardyTheorem

/-- Under the arithmetic scale condition, every distinct supported pair has
frequency gap at least the short-window drift `H / T`. -/
theorem H_div_T_le_abs_frequency_sub_of_mem_ne
    {N X : ℕ} {T H : ℝ} {q r : ℚ}
    (hscale : H / T ≤ 1 / ((N * X ^ 2 : ℕ) : ℝ))
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hne : q ≠ r) :
    H / T ≤
      |selbergSqrtZetaSignedRationalFrequency q -
        selbergSqrtZetaSignedRationalFrequency r| :=
  hscale.trans
    (one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
      hq hr hne)

/-- Below the arithmetic spacing scale, a pair in the stationary gap range
must be diagonal. -/
theorem eq_of_mem_of_abs_frequency_sub_lt_H_div_T
    {N X : ℕ} {T H : ℝ} {q r : ℚ}
    (hscale : H / T ≤ 1 / ((N * X ^ 2 : ℕ) : ℝ))
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hstationary :
      |selbergSqrtZetaSignedRationalFrequency q -
        selbergSqrtZetaSignedRationalFrequency r| < H / T) :
    q = r := by
  by_contra hne
  exact
    (not_lt_of_ge
      (H_div_T_le_abs_frequency_sub_of_mem_ne hscale hq hr hne))
      hstationary

/-- If `H / T` lies below the arithmetic support spacing, the exact short
kernel of every distinct supported pair has reciprocal-gap decay. -/
theorem
    norm_selbergSqrtZetaSignedRationalShortKernel_le_of_mem_ne
    {N X : ℕ} (hN : 0 < N) (hX : 0 < X)
    {T H : ℝ} (hT : 0 < T) (hH : 0 ≤ H) (hroom : H ≤ T)
    (hscale : H / T ≤ 1 / ((N * X ^ 2 : ℕ) : ℝ))
    {q r : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hr : r ∈ selbergSqrtZetaSignedRationalSupport N X)
    (hne : q ≠ r) :
    ‖selbergSqrtZetaSignedRationalShortKernel T H q r‖ ≤
      H ^ 2 *
        (8 /
          |selbergSqrtZetaSignedRationalFrequency q -
            selbergSqrtZetaSignedRationalFrequency r|) := by
  let M : ℝ := ((N * X ^ 2 : ℕ) : ℝ)
  have hM : 0 < M := by
    dsimp only [M]
    exact_mod_cast Nat.mul_pos hN (pow_pos hX 2)
  have hsepArithmetic :
      1 / M ≤
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| := by
    simpa only [M] using
      one_div_nat_mul_sq_le_abs_sub_frequency_of_mem_selbergSqrtZetaSignedRationalSupport
        hq hr hne
  have hgap :
      0 <
        |selbergSqrtZetaSignedRationalFrequency q -
          selbergSqrtZetaSignedRationalFrequency r| :=
    (by positivity : 0 < 1 / M).trans_le hsepArithmetic
  exact
    norm_selbergSqrtZetaSignedRationalShortKernel_le_of_frequencyGap
      q r hT hH hroom hgap
        (H_div_T_le_abs_frequency_sub_of_mem_ne hscale hq hr hne)

end HardyTheorem
