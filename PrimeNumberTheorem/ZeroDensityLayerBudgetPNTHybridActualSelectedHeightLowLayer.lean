import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridAffineSelectedHeight

/-!
# Actual hybrid low-layer decay at a selected good height

The exact-power low-layer theorem used `T = x^alpha`.  A selected good height
lies below that power scale and tends to infinity.  Since both the global
zero multiplicity and the explicit `T log T` majorant are monotone in the
height on the relevant range, the same normalized decay estimate survives
without changing the exponent or margin.
-/

open Filter Topology

namespace PrimeNumberTheorem

/-- The actual global low-layer majorant is monotone in its height argument
once the lower height is at least four. -/
theorem actualHybridGlobalLowLayerMajorant_mono_height
    {C T U kappa tau x : ℝ}
    (hC : 0 ≤ C)
    (hkappa : 0 < kappa)
    (hx : 0 ≤ x)
    (hT : 4 ≤ T)
    (hTU : T ≤ U) :
    actualHybridGlobalLowLayerMajorant C T kappa tau x ≤
      actualHybridGlobalLowLayerMajorant C U kappa tau x := by
  have hTnonneg : 0 ≤ T := by linarith
  have hUnonneg : 0 ≤ U := hTnonneg.trans hTU
  have hlog :
      Real.log (T + 6) ≤ Real.log (U + 6) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogTnonneg : 0 ≤ Real.log (T + 6) := by
    have :=
      Real.log_le_log (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ T + 6 by linarith)
    simpa using this
  have hlogUnonneg : 0 ≤ Real.log (U + 6) := by
    have :=
      Real.log_le_log (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) ≤ U + 6 by linarith)
    simpa using this
  have hCT :
      C * T ≤ C * U :=
    mul_le_mul_of_nonneg_left hTU hC
  have hcount :
      C * T * (1 + Real.log (T + 6)) ≤
        C * U * (1 + Real.log (U + 6)) := by
    calc
      C * T * (1 + Real.log (T + 6)) ≤
          C * U * (1 + Real.log (T + 6)) :=
        mul_le_mul_of_nonneg_right hCT (by linarith)
      _ ≤ C * U * (1 + Real.log (U + 6)) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg hC hUnonneg)
  unfold actualHybridGlobalLowLayerMajorant
  exact
    mul_le_mul_of_nonneg_right hcount
      (stripEndpointRelativeKernelBudget_nonneg hx hkappa.le)

/--
An actual outside-cluster low layer at any cofinal selected height
eventually bounded by `x^alpha` is negligible at the target amplitude.
-/
theorem
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid_selectedHeight
    {n : ℕ} {S : Finset ℂ}
    {H : ℝ → ℝ}
    {beta tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
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
        |dynamicPositiveOutsideClusterPNTLayerNorm H S input i x| /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  rcases
      exists_globalCoefficient_dynamicPositiveOutsideClusterPNTLayerNorm_le_actualHybridMajorant
        input i tau kappa hkappa hnorm hre with
    ⟨C, hC, hpointwise⟩
  have hlog :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  have hupper :
      ∀ᶠ x : ℝ in atTop,
        |dynamicPositiveOutsideClusterPNTLayerNorm H S input i x| /
            targetZeroPowerAmplitude beta x ≤
          actualHybridLowNormalizedLogPowerMajorant
            C kappa beta tau alpha x := by
    filter_upwards
        [eventually_ge_atTop (1 : ℝ),
          hHtop.eventually (eventually_ge_atTop (4 : ℝ)),
          hHle,
          hlog] with x hx hHfour hHupper hlogBound
    have hxpos : 0 < x :=
      zero_lt_one.trans_le hx
    have hamplitude :
        0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos hxpos _
    have hphysical :=
      hpointwise x hx hHfour
    have hselectedToPower :
        actualHybridGlobalLowLayerMajorant C (H x) kappa tau x ≤
          actualHybridGlobalLowLayerMajorant
            C (carlsonPolynomialHeight alpha x) kappa tau x :=
      actualHybridGlobalLowLayerMajorant_mono_height
        hC hkappa (zero_le_one.trans hx) hHfour hHupper
    have hnormalized :
        |dynamicPositiveOutsideClusterPNTLayerNorm H S input i x| /
            targetZeroPowerAmplitude beta x ≤
          actualHybridGlobalLowLayerMajorant
                C (carlsonPolynomialHeight alpha x) kappa tau x /
            targetZeroPowerAmplitude beta x :=
      (div_le_div_iff_of_pos_right hamplitude).2
        (hphysical.trans hselectedToPower)
    have hcoefficient :
        0 ≤ C * kappa⁻¹ * x ^ (tau - beta + alpha) := by
      positivity
    calc
      |dynamicPositiveOutsideClusterPNTLayerNorm H S input i x| /
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

/-- `TargetAmplitudeNegligible` packaging of the selected-height low-layer
decay theorem. -/
theorem
    actualHybridOutsideClusterLowLayer_selectedHeight_targetAmplitudeNegligible
    {n : ℕ} {S : Finset ℂ}
    {H : ℝ → ℝ}
    {beta tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + alpha + epsilon < 0) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTLayerNorm H S input i) := by
  unfold TargetAmplitudeNegligible
  convert
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid_selectedHeight
      input i hHle hHtop hkappa hnorm hre
      halpha hepsilon hmargin using 1

end PrimeNumberTheorem
