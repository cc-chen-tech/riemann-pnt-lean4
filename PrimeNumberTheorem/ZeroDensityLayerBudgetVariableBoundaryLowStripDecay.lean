import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryPositiveTailIndexBridge
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticLowLayer

/-!
# Variable-boundary low-strip decay

The low positive strip is controlled uniformly by the global zeta-zero
multiplicity estimate.  A fixed exponent `beta0` below the moving boundary
anchors the final decay rate, while stack103 enlarges the normalization
denominator pointwise.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Canonical two-strip input after deleting the package at the pointwise
moving boundary exponent. -/
noncomputable def variableBoundaryCanonicalTwoStripInput
    (H beta : ℝ → ℝ) (sigma : ℝ) (m : ℕ) :
    PositiveZeroOutsideClusterBucketInput
      (H (m : ℝ)) (variableBoundaryZeroPackage H beta (m : ℝ)) 2 :=
  pntHybridCanonicalTwoStripOutsideClusterBucketInput sigma
    (H (m : ℝ)) (variableBoundaryZeroPackage H beta (m : ℝ))

theorem variableBoundaryCanonicalTwoStripInput_low_re_le
    {H beta : ℝ → ℝ} {sigma : ℝ} (m : ℕ) {rho : ℂ}
    (hrho :
      rho ∈ (variableBoundaryCanonicalTwoStripInput
        H beta sigma m).layer (0 : Fin 2)) :
    rho.re ≤ sigma :=
  pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho

theorem variableBoundaryCanonicalTwoStripInput_low_cover
    {H beta : ℝ → ℝ} {sigma : ℝ} (m : ℕ) {rho : ℂ}
    (_hrho :
      rho ∈ positiveNontrivialZerosOutsideClusterFinset
        (H (m : ℝ)) (variableBoundaryZeroPackage H beta (m : ℝ)))
    (hre : rho.re ≤ sigma) :
    (variableBoundaryCanonicalTwoStripInput H beta sigma m).bucket rho = 0 := by
  simp [variableBoundaryCanonicalTwoStripInput,
    pntHybridCanonicalTwoStripOutsideClusterBucketInput,
    not_lt.mpr hre]

/-- The stronger empty-cluster guard supplies one positive denominator guard
for every pointwise moving low layer. -/
theorem exists_variableBoundaryCanonicalLow_uniform_norm_lower_bound
    (H beta : ℝ → ℝ) (sigma : ℝ) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ m : ℕ,
        ∀ rho ∈ (variableBoundaryCanonicalTwoStripInput
          H beta sigma m).layer (0 : Fin 2),
          kappa ≤ ‖rho‖ := by
  rcases exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
      H sigma ∅ with ⟨kappa, hkappa, hnorm⟩
  refine ⟨kappa, hkappa, ?_⟩
  intro m rho hrho
  apply hnorm (m : ℝ) rho
  have hbase := (Finset.mem_filter.mp hrho).1
  have hbucket := (Finset.mem_filter.mp hrho).2
  apply Finset.mem_filter.mpr
  constructor
  · rcases mem_positiveNontrivialZerosOutsideClusterFinset.mp hbase with
      ⟨hzero, him, hheight, _⟩
    exact mem_positiveNontrivialZerosOutsideClusterFinset.mpr
      ⟨hzero, him, hheight, by simp⟩
  · simpa [variableBoundaryCanonicalTwoStripInput,
      pntHybridCanonicalTwoStripOutsideClusterBucketInput] using hbucket

/-- The actual pointwise moving low strip decays when the moving boundary is
eventually above a fixed exponent satisfying the usual polynomial-height
margin. -/
theorem variableBoundaryLowPositiveNormalizedSum_tendsto_zero
    {H beta : ℝ → ℝ} {beta0 sigma alpha epsilon : ℝ}
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + alpha + epsilon < 0) :
    Tendsto
      (variableBoundaryLowPositiveNormalizedSum sigma H beta)
      atTop (𝓝 0) := by
  rcases exists_variableBoundaryCanonicalLow_uniform_norm_lower_bound
      H beta sigma with ⟨kappa, hkappa, hnorm⟩
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
            C kappa beta0 sigma alpha (m : ℝ))
        atTop (𝓝 0) :=
    (tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
      hC hkappa halpha hepsilon hmargin).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    unfold variableBoundaryLowPositiveNormalizedSum
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _)
  · filter_upwards [eventually_ge_atTop (1 : ℕ), hbetaLower,
      hHtop.eventually (eventually_ge_atTop (4 : ℝ)), hHle, hlog] with
      m hm hbetaM hHfour hHupper hlogBound
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    have hVariableAmplitude :
        0 < variableBoundaryTargetAmplitude beta (m : ℝ) := by
      unfold variableBoundaryTargetAmplitude targetZeroPowerAmplitude
      exact Real.rpow_pos_of_pos hmPos _
    have hFixedAmplitude :
        0 < targetZeroPowerAmplitude beta0 (m : ℝ) :=
      Real.rpow_pos_of_pos hmPos _
    have hAmplitude :=
      targetZeroPowerAmplitude_le_variableBoundaryTargetAmplitude hm hbetaM
    let input := variableBoundaryCanonicalTwoStripInput H beta sigma m
    let layer := input.layer (0 : Fin 2)
    have hlayer :
        layer =
          (positiveNontrivialZerosOutsideClusterFinset
            (H (m : ℝ)) (variableBoundaryZeroPackage H beta (m : ℝ))).filter
              (fun rho => rho.re ≤ sigma) :=
      lowLayer_eq_filter_re_le input (0 : Fin 2)
        (fun rho hrho =>
          variableBoundaryCanonicalTwoStripInput_low_re_le m hrho)
        (fun rho hrho hre =>
          variableBoundaryCanonicalTwoStripInput_low_cover m hrho hre)
    have hkernel :
        ∀ rho ∈ layer,
          ‖pntRelativeSimpleZeroKernel (m : ℝ) rho‖ ≤
            stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) := by
      intro rho hrho
      exact norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
        (by exact_mod_cast hm) hkappa (hnorm m rho hrho)
        (variableBoundaryCanonicalTwoStripInput_low_re_le m hrho)
    have hkernelNonneg :
        0 ≤ stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) :=
      stripEndpointRelativeKernelBudget_nonneg hmPos.le hkappa.le
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
            (input.layer_multiplicityMass_le_globalZeroMultiplicity
              (0 : Fin 2)) hkernelNonneg
        _ ≤ stripEndpointRelativeKernelBudget kappa sigma (m : ℝ) *
              (C * H (m : ℝ) * (1 + Real.log (H (m : ℝ) + 6))) :=
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
    have hlowPhysical :
        ‖∑ rho ∈
            (positiveNontrivialZerosOutsideClusterFinset
              (H (m : ℝ))
                (variableBoundaryZeroPackage H beta (m : ℝ))).filter
                  (fun rho => rho.re ≤ sigma),
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          actualHybridGlobalLowLayerMajorant
            C (carlsonPolynomialHeight alpha (m : ℝ))
              kappa sigma (m : ℝ) := by
      rw [← hlayer]
      exact hphysical.trans hselected
    have hnormalized :
        variableBoundaryLowPositiveNormalizedSum sigma H beta m ≤
          actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight alpha (m : ℝ))
                kappa sigma (m : ℝ) /
            variableBoundaryTargetAmplitude beta (m : ℝ) := by
      unfold variableBoundaryLowPositiveNormalizedSum
      exact (div_le_div_iff_of_pos_right hVariableAmplitude).2 hlowPhysical
    have hglobalNonneg :
        0 ≤ actualHybridGlobalLowLayerMajorant
          C (carlsonPolynomialHeight alpha (m : ℝ))
            kappa sigma (m : ℝ) :=
      (norm_nonneg _).trans hlowPhysical
    have hdenominator :
        actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight alpha (m : ℝ))
                kappa sigma (m : ℝ) /
            variableBoundaryTargetAmplitude beta (m : ℝ) ≤
          actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight alpha (m : ℝ))
                kappa sigma (m : ℝ) /
            targetZeroPowerAmplitude beta0 (m : ℝ) := by
      apply (div_le_div_iff₀ hVariableAmplitude hFixedAmplitude).2
      exact mul_le_mul_of_nonneg_left hAmplitude hglobalNonneg
    have hcoefficient :
        0 ≤ C * kappa⁻¹ * (m : ℝ) ^ (sigma - beta0 + alpha) := by
      positivity
    calc
      variableBoundaryLowPositiveNormalizedSum sigma H beta m
          ≤ actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight alpha (m : ℝ))
                kappa sigma (m : ℝ) /
              variableBoundaryTargetAmplitude beta (m : ℝ) := hnormalized
      _ ≤ actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight alpha (m : ℝ))
                kappa sigma (m : ℝ) /
              targetZeroPowerAmplitude beta0 (m : ℝ) := hdenominator
      _ = C * kappa⁻¹ * (m : ℝ) ^ (sigma - beta0 + alpha) *
            (1 + Real.log ((m : ℝ) ^ alpha + 6)) :=
        actualHybridGlobalLowLayerMajorant_div_target_eq hmPos
      _ ≤ C * kappa⁻¹ * (m : ℝ) ^ (sigma - beta0 + alpha) *
            ((alpha + 2) * Real.log (m : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hlogBound hcoefficient
      _ = actualHybridLowNormalizedLogPowerMajorant
            C kappa beta0 sigma alpha (m : ℝ) := by
        unfold actualHybridLowNormalizedLogPowerMajorant
        ring

/-- Complete actual moving explicit-formula residual with low, high, negative,
and real zero tails all discharged by concrete theorems. -/
theorem
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_automaticZeroTails
    {sigma beta0 alpha epsilon : ℝ} {H beta : ℝ → ℝ}
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + alpha + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta0 H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  apply
    actualVariableBoundaryFullTailExplicitFormulaResidual_targetAmplitudeNegligible_of_realGap
      hbeta0 hbetaLower hHtop hrightReal hhalf hone hright hgap
  · exact variableBoundaryVisiblePositiveTailMajorized_low
      hhalf hone hright
  · exact variableBoundaryLowPositiveNormalizedSum_tendsto_zero
      hbetaLower hHle hHtop halpha hepsilon hmargin
  · exact remainder

end PrimeNumberTheorem
