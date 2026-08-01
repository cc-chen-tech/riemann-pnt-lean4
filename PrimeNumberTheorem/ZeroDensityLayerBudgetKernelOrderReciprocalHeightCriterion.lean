import PrimeNumberTheorem.ZeroDensityLayerBudgetHeightNormalizedContourObstruction

/-!
# Kernel-order criterion at the reciprocal-height zero scale

Suppose a smoothed explicit-formula kernel has relative remainder

`C * H(x)^(-k) * (1 + log x)^2`

at polynomial height `H(x) = x^alpha`.  After normalization by the natural
high-zero amplitude `x^(beta-1) / H(x)`, the remaining power is

`x^(1-beta-(k-1)alpha)`.

Consequently an order-`k` kernel is sufficient precisely on the strict power
side `(k-1) alpha > 1-beta`.  In particular, order two is sufficient under
the same contour window `alpha > 1-beta` already used by the selected-height
explicit formula, whereas order one is obstructed by the previous module.
-/

namespace PrimeNumberTheorem

open Filter Topology

noncomputable section

/-- An order-`k` polynomial-height remainder normalized by the
reciprocal-height target zero amplitude. -/
noncomputable def kernelOrderReciprocalHeightRemainderRatio
    (C beta alpha k x : ℝ) : ℝ :=
  (C * x ^ (-(k * alpha)) * (1 + Real.log x) ^ 2) /
    (targetZeroPowerAmplitude beta x / x ^ alpha)

/-- Exact exponent left after reciprocal-height normalization. -/
theorem kernelOrderReciprocalHeightRemainderRatio_eq
    {C beta alpha k x : ℝ} (hx : 0 < x) :
    kernelOrderReciprocalHeightRemainderRatio C beta alpha k x =
      actualPolynomialRemainderTargetMajorant
        C beta ((k - 1) * alpha) x := by
  have hpow :
      x ^ (-(k * alpha)) * x ^ alpha * x ^ (-(beta - 1)) =
        x ^ (1 - beta - (k - 1) * alpha) := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  unfold kernelOrderReciprocalHeightRemainderRatio
    targetZeroPowerAmplitude actualPolynomialRemainderTargetMajorant
  rw [div_eq_mul_inv, inv_div, div_eq_mul_inv,
    ← Real.rpow_neg hx.le]
  calc
    C * x ^ (-(k * alpha)) * (1 + Real.log x) ^ 2 *
          (x ^ alpha * x ^ (-(beta - 1))) =
        C *
          (x ^ (-(k * alpha)) * x ^ alpha * x ^ (-(beta - 1))) *
          (1 + Real.log x) ^ 2 := by ring
    _ = C * x ^ (1 - beta - (k - 1) * alpha) *
          (1 + Real.log x) ^ 2 := by rw [hpow]

/-- A strict kernel-order margin absorbs the logarithmic loss at the natural
reciprocal-height zero scale. -/
theorem tendsto_kernelOrderReciprocalHeightRemainderRatio_zero
    {C beta alpha k : ℝ}
    (hC : 0 ≤ C)
    (hmargin : 1 - beta < (k - 1) * alpha) :
    Tendsto
      (kernelOrderReciprocalHeightRemainderRatio C beta alpha k)
      atTop (nhds 0) := by
  have hbase :=
    tendsto_actualPolynomialRemainderTargetMajorant hC hmargin
  apply hbase.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (kernelOrderReciprocalHeightRemainderRatio_eq hx).symm

/-- For an order-two kernel, the kernel-order margin is exactly the existing
contour-height condition `1-beta < alpha`. -/
theorem tendsto_quadraticKernelReciprocalHeightRemainderRatio_zero
    {C beta alpha : ℝ}
    (hC : 0 ≤ C) (hmargin : 1 - beta < alpha) :
    Tendsto
      (kernelOrderReciprocalHeightRemainderRatio C beta alpha 2)
      atTop (nhds 0) := by
  apply tendsto_kernelOrderReciprocalHeightRemainderRatio_zero hC
  norm_num
  exact hmargin

/-- Pointwise order-two specialization: one power of the polynomial height
survives after paying for the reciprocal zero coefficient. -/
theorem quadraticKernelReciprocalHeightRemainderRatio_eq
    {C beta alpha x : ℝ} (hx : 0 < x) :
    kernelOrderReciprocalHeightRemainderRatio C beta alpha 2 x =
      actualPolynomialRemainderTargetMajorant C beta alpha x := by
  convert
    (kernelOrderReciprocalHeightRemainderRatio_eq
      (C := C) (beta := beta) (alpha := alpha) (k := 2) hx) using 1 <;>
    norm_num

/-- Pointwise order-one specialization: no polynomial-height power survives,
recovering the obstruction exponent `1-beta`. -/
theorem linearKernelReciprocalHeightRemainderRatio_eq
    {C beta alpha x : ℝ} (hx : 0 < x) :
    kernelOrderReciprocalHeightRemainderRatio C beta alpha 1 x =
      actualPolynomialRemainderTargetMajorant C beta 0 x := by
  convert
    (kernelOrderReciprocalHeightRemainderRatio_eq
      (C := C) (beta := beta) (alpha := alpha) (k := 1) hx) using 1 <;>
    norm_num

end
end PrimeNumberTheorem
