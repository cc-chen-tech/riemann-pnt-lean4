import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualLowLayer
import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteAffineLogPowerTransfer

/-!
# Target-amplitude decay of an actual hybrid low layer

This file normalizes the actual global-count low-layer majorant by
`targetZeroPowerAmplitude beta`.  At polynomial height `T = x^alpha`, its
power exponent is exactly

`tau - beta + alpha`.

The logarithm from the global `O(T log T)` count is absorbed by `(log x)^4`
without changing this exponent.  Hence a strict margin

`tau - beta + alpha + epsilon < 0`

forces the genuine multiplicity-weighted outside-cluster layer to be
negligible at the target zero-power scale.
-/

open Filter Topology

namespace PrimeNumberTheorem

open scoped BigOperators

/-- Polynomial-log majorant for the normalized actual hybrid low layer. -/
noncomputable def actualHybridLowNormalizedLogPowerMajorant
    (C kappa beta tau alpha x : ℝ) : ℝ :=
  (C * kappa⁻¹ * (alpha + 2)) *
    x ^ (tau - beta + alpha) * Real.log x ^ 4

theorem actualHybridGlobalLowLayerMajorant_div_target_eq
    {C kappa beta tau alpha x : ℝ}
    (hx : 0 < x) :
    actualHybridGlobalLowLayerMajorant
          C (carlsonPolynomialHeight alpha x) kappa tau x /
        targetZeroPowerAmplitude beta x =
      C * kappa⁻¹ * x ^ (tau - beta + alpha) *
        (1 + Real.log (x ^ alpha + 6)) := by
  have hpow :
      x ^ alpha * x ^ (tau - 1) * (x ^ (beta - 1))⁻¹ =
        x ^ (tau - beta + alpha) := by
    calc
      x ^ alpha * x ^ (tau - 1) * (x ^ (beta - 1))⁻¹ =
          x ^ (alpha + (tau - 1)) / x ^ (beta - 1) := by
        rw [div_eq_mul_inv, Real.rpow_add hx]
      _ = x ^ ((alpha + (tau - 1)) - (beta - 1)) := by
        rw [← Real.rpow_sub hx]
      _ = x ^ (tau - beta + alpha) := by
        congr 1
        ring
  unfold actualHybridGlobalLowLayerMajorant
    carlsonPolynomialHeight stripEndpointRelativeKernelBudget
    targetZeroPowerAmplitude
  rw [div_eq_mul_inv]
  calc
    (C * x ^ alpha * (1 + Real.log (x ^ alpha + 6)) *
          (kappa⁻¹ * x ^ (tau - 1))) *
        (x ^ (beta - 1))⁻¹ =
        C * kappa⁻¹ * (1 + Real.log (x ^ alpha + 6)) *
          (x ^ alpha * x ^ (tau - 1) * (x ^ (beta - 1))⁻¹) := by
      ring
    _ = C * kappa⁻¹ * (1 + Real.log (x ^ alpha + 6)) *
          x ^ (tau - beta + alpha) := by
      rw [hpow]
    _ = C * kappa⁻¹ * x ^ (tau - beta + alpha) *
          (1 + Real.log (x ^ alpha + 6)) := by
      ring

/--
At positive polynomial height exponent, the shifted height logarithm is
eventually absorbed by `(alpha + 2) * (log x)^4`.
-/
theorem
    eventually_one_add_log_polynomialHeight_add_six_le_log_four
    {alpha : ℝ}
    (halpha : 0 < alpha) :
    ∀ᶠ x : ℝ in atTop,
      1 + Real.log (x ^ alpha + 6) ≤
        (alpha + 2) * Real.log x ^ 4 := by
  have hheight :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  filter_upwards
      [eventually_ge_atTop (Real.exp 1),
        hheight.eventually (eventually_ge_atTop (6 : ℝ))] with x hx hheightSix
  have hxpos : 0 < x :=
    (Real.exp_pos 1).trans_le hx
  have hheightPos : 0 < x ^ alpha :=
    Real.rpow_pos_of_pos hxpos alpha
  have hlogOne : 1 ≤ Real.log x := by
    have hlog :=
      Real.log_le_log (Real.exp_pos 1) hx
    simpa using hlog
  have hlogTwo : Real.log 2 ≤ 1 := by
    have :=
      Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢
    exact this
  have hheightAdd :
      x ^ alpha + 6 ≤ 2 * x ^ alpha := by
    linarith
  have hlogHeight :
      Real.log (x ^ alpha + 6) ≤
        1 + alpha * Real.log x := by
    calc
      Real.log (x ^ alpha + 6) ≤
          Real.log (2 * x ^ alpha) :=
        Real.log_le_log (by positivity) hheightAdd
      _ = Real.log 2 + Real.log (x ^ alpha) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hheightPos)]
      _ = Real.log 2 + alpha * Real.log x := by
        rw [Real.log_rpow hxpos]
      _ ≤ 1 + alpha * Real.log x := by
        linarith
  have hlogNonneg : 0 ≤ Real.log x :=
    zero_le_one.trans hlogOne
  have hlogSq :
      Real.log x ≤ Real.log x ^ 2 := by
    nlinarith
      [mul_nonneg hlogNonneg (sub_nonneg.mpr hlogOne)]
  have hlogSqOne : 1 ≤ Real.log x ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - 1)]
  have hlogFourth :
      Real.log x ^ 2 ≤ Real.log x ^ 4 := by
    nlinarith
      [mul_nonneg (sq_nonneg (Real.log x))
        (sub_nonneg.mpr hlogSqOne)]
  have hlogPower :
      Real.log x ≤ Real.log x ^ 4 :=
    hlogSq.trans hlogFourth
  have halphaTwo : 0 ≤ alpha + 2 := by
    linarith
  calc
    1 + Real.log (x ^ alpha + 6) ≤
        2 + alpha * Real.log x := by
      linarith
    _ ≤ (alpha + 2) * Real.log x := by
      nlinarith
        [mul_nonneg halpha.le
          (sub_nonneg.mpr hlogOne)]
    _ ≤ (alpha + 2) * Real.log x ^ 4 :=
      mul_le_mul_of_nonneg_left hlogPower halphaTwo

/-- A strict affine exponent margin makes the normalized log-power majorant
tend to zero. -/
theorem tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
    {C kappa beta tau alpha epsilon : ℝ}
    (hC : 0 ≤ C)
    (hkappa : 0 < kappa)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + alpha + epsilon < 0) :
    Tendsto
      (actualHybridLowNormalizedLogPowerMajorant
        C kappa beta tau alpha)
      atTop (nhds 0) := by
  let K : ℝ := C * kappa⁻¹ * (alpha + 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  let ceiling : Fin 1 → ℝ := fun _ => beta - tau
  let slope : Fin 1 → ℝ := fun _ => 1
  have hcertificate :
      FiniteAffineDensityMarginCertificate
        (alpha - epsilon) ceiling slope alpha epsilon := by
    refine
      { contour := by
          linarith
        strip := ?_ }
    intro i
    dsimp [ceiling, slope]
    linarith
  have hlimit :=
    tendsto_finiteAffineDensityLogPowerMajorant_zero
      (n := 0)
      (contourCoeff := 0)
      (stripCoeff := fun _ : Fin 1 => K)
      (floor := alpha - epsilon)
      (alpha := alpha)
      (delta := epsilon)
      (ceiling := ceiling)
      (slope := slope)
      (by norm_num)
      (fun _ => hK)
      hepsilon
      hcertificate
  have hexponent :
      alpha - (beta - tau) = tau - beta + alpha := by
    ring
  convert hlimit using 1
  funext x
  simp [finiteAffineDensityLogPowerMajorant,
    actualHybridLowNormalizedLogPowerMajorant, K, ceiling, slope,
    hexponent]

/--
The genuine multiplicity-weighted outside-cluster low layer is negligible
relative to the target zero-power amplitude at polynomial height.
-/
theorem
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid
    {n : ℕ} {S : Finset ℂ}
    {beta tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (i : Fin n)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + alpha + epsilon < 0) :
    Tendsto
      (fun x =>
        |dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) S input i x| /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  rcases
      exists_globalCoefficient_dynamicPositiveOutsideClusterPNTLayerNorm_le_actualHybridMajorant
        input i tau kappa hkappa hnorm hre with
    ⟨C, hC, hpointwise⟩
  have hheight :
      Tendsto (fun x : ℝ => x ^ alpha) atTop atTop :=
    tendsto_rpow_atTop halpha
  have hlog :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  have hupper :
      ∀ᶠ x : ℝ in atTop,
        |dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) S input i x| /
            targetZeroPowerAmplitude beta x ≤
          actualHybridLowNormalizedLogPowerMajorant
            C kappa beta tau alpha x := by
    filter_upwards
        [eventually_ge_atTop (1 : ℝ),
          hheight.eventually (eventually_ge_atTop (4 : ℝ)),
          hlog] with x hx hheightFour hlogBound
    have hxpos : 0 < x :=
      zero_lt_one.trans_le hx
    have hamplitude :
        0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos hxpos _
    have hphysical :=
      hpointwise x hx hheightFour
    have hnormalized :
        |dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) S input i x| /
            targetZeroPowerAmplitude beta x ≤
          actualHybridGlobalLowLayerMajorant
                C (carlsonPolynomialHeight alpha x) kappa tau x /
            targetZeroPowerAmplitude beta x :=
      (div_le_div_iff_of_pos_right hamplitude).2 hphysical
    have hcoefficient :
        0 ≤ C * kappa⁻¹ * x ^ (tau - beta + alpha) := by
      positivity
    calc
      |dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) S input i x| /
          targetZeroPowerAmplitude beta x ≤
          actualHybridGlobalLowLayerMajorant
                C (carlsonPolynomialHeight alpha x) kappa tau x /
            targetZeroPowerAmplitude beta x :=
        hnormalized
      _ = C * kappa⁻¹ * x ^ (tau - beta + alpha) *
          (1 + Real.log (x ^ alpha + 6)) :=
        actualHybridGlobalLowLayerMajorant_div_target_eq hxpos
      _ ≤ C * kappa⁻¹ * x ^ (tau - beta + alpha) *
          ((alpha + 2) * Real.log x ^ 4) :=
        mul_le_mul_of_nonneg_left hlogBound hcoefficient
      _ = actualHybridLowNormalizedLogPowerMajorant
          C kappa beta tau alpha x := by
        unfold actualHybridLowNormalizedLogPowerMajorant
        ring
  refine squeeze_zero' ?_ hupper
    (tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
      hC hkappa halpha hepsilon hmargin)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact div_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (zero_le_one.trans hx) _)

end PrimeNumberTheorem
