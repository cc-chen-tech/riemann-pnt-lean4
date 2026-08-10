import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryFullTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridCanonicalTwoStripProfile
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonCanonicalTwoStripAutomaticNorm
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualSelectedHeightLowLayer

/-!
# Automatic low layer for a dynamic boundary package

The moving boundary package changes with the natural scale, so the older
selected-height low-layer theorem with a fixed cluster cannot be applied
directly.  The global zero-multiplicity bound is independent of the deleted
cluster, however.  This module applies that bound pointwise to the canonical
two-strip low layer and recovers target-amplitude decay.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Canonical two-strip input after deleting the boundary package visible at
the current natural scale. -/
noncomputable def actualDynamicBoundaryCanonicalTwoStripInput
    (H : ℝ → ℝ) (beta sigma : ℝ) (m : ℕ) :
    PositiveZeroOutsideClusterBucketInput
      (H (m : ℝ))
      (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) 2 :=
  pntHybridCanonicalTwoStripOutsideClusterBucketInput sigma
    (H (m : ℝ))
    (dynamicEqualRealPartZeroPackage H beta (m : ℝ))

theorem actualDynamicBoundaryCanonicalTwoStripInput_low_re_le
    {H : ℝ → ℝ} {beta sigma : ℝ} (m : ℕ)
    {rho : ℂ}
    (hrho :
      rho ∈
        (actualDynamicBoundaryCanonicalTwoStripInput
          H beta sigma m).layer (0 : Fin 2)) :
    rho.re ≤ sigma := by
  exact
    pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho

theorem actualDynamicBoundaryCanonicalTwoStripInput_low_cover
    {H : ℝ → ℝ} {beta sigma : ℝ} (m : ℕ)
    {rho : ℂ}
    (hrho :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset
        (H (m : ℝ))
        (dynamicEqualRealPartZeroPackage H beta (m : ℝ)))
    (hre : rho.re ≤ sigma) :
    (actualDynamicBoundaryCanonicalTwoStripInput
      H beta sigma m).bucket rho = 0 := by
  simp [actualDynamicBoundaryCanonicalTwoStripInput,
    pntHybridCanonicalTwoStripOutsideClusterBucketInput,
    not_lt.mpr hre]

/--
One positive kernel-denominator guard works for every moving-package low
layer.  It is obtained from the stronger empty-cluster guard.
-/
theorem
    exists_actualDynamicBoundaryCanonicalLow_uniform_norm_lower_bound
    (H : ℝ → ℝ) (beta sigma : ℝ) :
    ∃ kappa : ℝ,
      0 < kappa ∧
        ∀ m : ℕ,
          ∀ rho ∈
              (actualDynamicBoundaryCanonicalTwoStripInput
                H beta sigma m).layer (0 : Fin 2),
            kappa ≤ ‖rho‖ := by
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        H sigma ∅ with
    ⟨kappa, hkappa, hnorm⟩
  refine ⟨kappa, hkappa, ?_⟩
  intro m rho hrho
  apply hnorm (m : ℝ) rho
  have hbase :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset
        (H (m : ℝ))
        (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) :=
    (Finset.mem_filter.mp hrho).1
  have hbucket :
      (actualDynamicBoundaryCanonicalTwoStripInput
        H beta sigma m).bucket rho = 0 :=
    (Finset.mem_filter.mp hrho).2
  apply Finset.mem_filter.mpr
  constructor
  · rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hbase with
      ⟨hzero, him, hheight, _⟩
    exact mem_positiveNontrivialZerosOutsideClusterFinset.mpr
      ⟨hzero, him, hheight, by simp⟩
  · simpa [actualDynamicBoundaryCanonicalTwoStripInput,
      pntHybridCanonicalTwoStripOutsideClusterBucketInput] using hbucket

/--
The canonical dynamic low layer is negligible at the target amplitude under
the usual selected-height polynomial ceiling and strict low-layer margin.
-/
theorem
    actualDynamicBoundaryCanonicalLowNormalizedSum_tendsto_zero
    {H : ℝ → ℝ} {beta sigma alpha kappa epsilon : ℝ}
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (hkappa : 0 < kappa)
    (hnorm :
      ∀ m : ℕ,
        ∀ rho ∈
            (actualDynamicBoundaryCanonicalTwoStripInput
              H beta sigma m).layer (0 : Fin 2),
          kappa ≤ ‖rho‖)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0) :
    Tendsto
      (actualDynamicBoundaryLowNormalizedSum H beta
        (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
        (0 : Fin 2))
      atTop (nhds 0) := by
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobal⟩
  have hlogReal :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  have hlog :
      ∀ᶠ m : ℕ in atTop,
        1 + Real.log ((m : ℝ) ^ alpha + 6) ≤
          (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlogReal
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          actualHybridLowNormalizedLogPowerMajorant
            C kappa beta sigma alpha (m : ℝ))
        atTop (nhds 0) :=
    (tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
      hC hkappa halpha hepsilon hmargin).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _)
  · filter_upwards [
      eventually_ge_atTop (1 : ℕ),
      hHtop.eventually (eventually_ge_atTop (4 : ℝ)),
      hHle, hlog] with m hm hHfour hHupper hlogBound
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hAmplitude :
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
      Real.rpow_pos_of_pos hmPos _
    let layer :=
      (actualDynamicBoundaryCanonicalTwoStripInput
        H beta sigma m).layer (0 : Fin 2)
    have hkernel :
        ∀ rho ∈ layer,
          ‖pntRelativeSimpleZeroKernel (m : ℝ) rho‖ ≤
            stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) := by
      intro rho hrho
      exact norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
        (by exact_mod_cast hm) hkappa (hnorm m rho hrho)
        (actualDynamicBoundaryCanonicalTwoStripInput_low_re_le m hrho)
    have hkernelNonneg :
        0 ≤ stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) :=
      stripEndpointRelativeKernelBudget_nonneg
        (by exact_mod_cast (Nat.zero_le m)) hkappa.le
    have hphysical :
        ‖∑ rho ∈ layer,
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          actualHybridGlobalLowLayerMajorant
            C (H (m : ℝ)) kappa sigma (m : ℝ) := by
      calc
        ‖∑ rho ∈ layer,
            pntRelativeZeroContribution (m : ℝ) rho‖
            ≤ ∑ rho ∈ layer,
                ‖pntRelativeZeroContribution (m : ℝ) rho‖ :=
          norm_sum_le _ _
        _ ≤ stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) *
              analyticMultiplicityMass layer :=
          sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
            layer (m : ℝ)
            (stripEndpointRelativeKernelBudget kappa sigma (m : ℝ))
            hkernelNonneg hkernel
        _ ≤ stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) *
              ExplicitFormulaAux.globalZeroMultiplicity (H (m : ℝ)) :=
          mul_le_mul_of_nonneg_left
            ((actualDynamicBoundaryCanonicalTwoStripInput
              H beta sigma m).layer_multiplicityMass_le_globalZeroMultiplicity
                (0 : Fin 2))
            hkernelNonneg
        _ ≤ stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) *
              (C * H (m : ℝ) *
                (1 + Real.log (H (m : ℝ) + 6))) :=
          mul_le_mul_of_nonneg_left
            (hglobal (H (m : ℝ)) hHfour) hkernelNonneg
        _ = actualHybridGlobalLowLayerMajorant
              C (H (m : ℝ)) kappa sigma (m : ℝ) := by
          unfold actualHybridGlobalLowLayerMajorant
          ring
    have hselected :
        actualHybridGlobalLowLayerMajorant
            C (H (m : ℝ)) kappa sigma (m : ℝ) ≤
          actualHybridGlobalLowLayerMajorant
            C (carlsonPolynomialHeight alpha (m : ℝ))
              kappa sigma (m : ℝ) :=
      actualHybridGlobalLowLayerMajorant_mono_height
        hC hkappa hmPos.le hHfour hHupper
    have hnormalized :
        actualDynamicBoundaryLowNormalizedSum H beta
            (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
            (0 : Fin 2) m ≤
          actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight alpha (m : ℝ))
                kappa sigma (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ) := by
      unfold actualDynamicBoundaryLowNormalizedSum
      exact (div_le_div_iff_of_pos_right hAmplitude).2
        (hphysical.trans hselected)
    have hcoefficient :
        0 ≤ C * kappa⁻¹ * (m : ℝ) ^ (sigma - beta + alpha) := by
      positivity
    calc
      actualDynamicBoundaryLowNormalizedSum H beta
          (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
          (0 : Fin 2) m
          ≤
            actualHybridGlobalLowLayerMajorant
                C (carlsonPolynomialHeight alpha (m : ℝ))
                  kappa sigma (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) :=
        hnormalized
      _ =
          C * kappa⁻¹ * (m : ℝ) ^ (sigma - beta + alpha) *
            (1 + Real.log ((m : ℝ) ^ alpha + 6)) :=
        actualHybridGlobalLowLayerMajorant_div_target_eq hmPos
      _ ≤
          C * kappa⁻¹ * (m : ℝ) ^ (sigma - beta + alpha) *
            ((alpha + 2) * Real.log (m : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hlogBound hcoefficient
      _ =
          actualHybridLowNormalizedLogPowerMajorant
            C kappa beta sigma alpha (m : ℝ) := by
        unfold actualHybridLowNormalizedLogPowerMajorant
        ring

/--
Canonical dynamic positive-tail decay with the norm guard constructed
automatically.
-/
theorem
    actualDynamicBoundaryCanonicalPositiveNormalizedSum_tendsto_zero
    {H : ℝ → ℝ} {beta sigma alpha epsilon : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hright :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta) :
    Tendsto
      (actualDynamicBoundaryPositiveNormalizedSum H beta)
      atTop (nhds 0) := by
  rcases
      exists_actualDynamicBoundaryCanonicalLow_uniform_norm_lower_bound
        H beta sigma with
    ⟨kappa, hkappa, hnorm⟩
  apply actualDynamicBoundaryPositiveNormalizedSum_tendsto_zero
    (actualDynamicBoundaryCanonicalTwoStripInput H beta sigma)
    (0 : Fin 2) hhalf hone hHtop
  · exact fun m rho hrho =>
      actualDynamicBoundaryCanonicalTwoStripInput_low_re_le m hrho
  · exact fun m rho hrho hre =>
      actualDynamicBoundaryCanonicalTwoStripInput_low_cover m hrho hre
  · exact hright
  · exact
      actualDynamicBoundaryCanonicalLowNormalizedSum_tendsto_zero
        hHle hHtop hkappa hnorm halpha hepsilon hmargin

end PrimeNumberTheorem
