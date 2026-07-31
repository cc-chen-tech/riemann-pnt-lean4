import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryReciprocalTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryMonotoneUnifiedUpperSignedOmega

/-!
# Reciprocal low-layer transfer for a monotone variable boundary

The moving target amplitude is anchored below by a fixed `beta0`, while the
low zero layer is estimated by the global reciprocal-zero mass.  The resulting
power margin is `sigma - beta0 + epsilon < 0`, with no polynomial-height
exponent loss.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

noncomputable section

/-- The variable-boundary low positive strip decays by reciprocal-zero mass,
under a margin independent of the selected-height exponent. -/
theorem variableBoundaryLowPositiveNormalizedSum_tendsto_zero_reciprocal
    {H beta : ℝ → ℝ} {beta0 sigma alpha epsilon : ℝ}
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + epsilon < 0) :
    Tendsto
      (variableBoundaryLowPositiveNormalizedSum sigma H beta)
      atTop (nhds 0) := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
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
          actualReciprocalLowNormalizedLogPowerMajorant
            C alpha beta0 sigma (m : ℝ))
        atTop (nhds 0) :=
    (tendsto_actualReciprocalLowNormalizedLogPowerMajorant_zero
      hepsilon hmargin).comp
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
    have hmNonneg : 0 ≤ (m : ℝ) := hmPos.le
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
    have hphysical :
        ‖∑ rho ∈ layer, pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          (m : ℝ) ^ (sigma - 1) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity
              (H (m : ℝ)) := by
      exact input.norm_layer_sum_le_rpow_mul_globalReciprocal
        (0 : Fin 2) (by exact_mod_cast hm)
        (fun rho hrho =>
          variableBoundaryCanonicalTwoStripInput_low_re_le m hrho)
    have hlowPhysical :
        ‖∑ rho ∈
            (positiveNontrivialZerosOutsideClusterFinset
              (H (m : ℝ))
                (variableBoundaryZeroPackage H beta (m : ℝ))).filter
                  (fun rho => rho.re ≤ sigma),
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          (m : ℝ) ^ (sigma - 1) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity
              (H (m : ℝ)) := by
      rw [← hlayer]
      exact hphysical
    have hglobalBound :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H (m : ℝ)) ≤
          C * (1 + Real.log (H (m : ℝ) + 6)) ^ 2 :=
      hglobal (H (m : ℝ)) hHfour
    have hlogMono :
        1 + Real.log (H (m : ℝ) + 6) ≤
          1 + Real.log ((m : ℝ) ^ alpha + 6) := by
      have hlogRaw :
          Real.log (H (m : ℝ) + 6) ≤
            Real.log ((m : ℝ) ^ alpha + 6) := by
        apply Real.log_le_log
        · linarith
        · simpa [carlsonPolynomialHeight] using hHupper
      linarith
    have hleftNonneg :
        0 ≤ 1 + Real.log (H (m : ℝ) + 6) := by
      have hlogPos : 0 < Real.log (H (m : ℝ) + 6) :=
        Real.log_pos (by linarith)
      linarith
    have hlogCombined :
        1 + Real.log (H (m : ℝ) + 6) ≤
          (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
      hlogMono.trans hlogBound
    have hrightNonneg :
        0 ≤ (alpha + 2) * Real.log (m : ℝ) ^ 4 :=
      hleftNonneg.trans hlogCombined
    have hfactorNonneg :
        0 ≤
          ((alpha + 2) * Real.log (m : ℝ) ^ 4 -
              (1 + Real.log (H (m : ℝ) + 6))) *
            ((alpha + 2) * Real.log (m : ℝ) ^ 4 +
              (1 + Real.log (H (m : ℝ) + 6))) :=
      mul_nonneg (sub_nonneg.mpr hlogCombined)
        (add_nonneg hrightNonneg hleftNonneg)
    have hlogSquare :
        (1 + Real.log (H (m : ℝ) + 6)) ^ 2 ≤
          ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 := by
      nlinarith
    have hreciprocal :
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity (H (m : ℝ)) ≤
          C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 :=
      hglobalBound.trans (mul_le_mul_of_nonneg_left hlogSquare hC)
    have hphysicalBound :
        ‖∑ rho ∈
            (positiveNontrivialZerosOutsideClusterFinset
              (H (m : ℝ))
                (variableBoundaryZeroPackage H beta (m : ℝ))).filter
                  (fun rho => rho.re ≤ sigma),
            pntRelativeZeroContribution (m : ℝ) rho‖ ≤
          (m : ℝ) ^ (sigma - 1) *
            (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2) :=
      hlowPhysical.trans
        (mul_le_mul_of_nonneg_left hreciprocal
          (Real.rpow_nonneg hmNonneg _))
    have hnormalized :
        variableBoundaryLowPositiveNormalizedSum sigma H beta m ≤
          ((m : ℝ) ^ (sigma - 1) *
              (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
            variableBoundaryTargetAmplitude beta (m : ℝ) := by
      unfold variableBoundaryLowPositiveNormalizedSum
      exact (div_le_div_iff_of_pos_right hVariableAmplitude).2 hphysicalBound
    have hnumeratorNonneg :
        0 ≤ (m : ℝ) ^ (sigma - 1) *
          (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2) := by
      positivity
    have hdenominator :
        ((m : ℝ) ^ (sigma - 1) *
              (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
            variableBoundaryTargetAmplitude beta (m : ℝ) ≤
          ((m : ℝ) ^ (sigma - 1) *
              (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
            targetZeroPowerAmplitude beta0 (m : ℝ) := by
      apply (div_le_div_iff₀ hVariableAmplitude hFixedAmplitude).2
      exact mul_le_mul_of_nonneg_left hAmplitude hnumeratorNonneg
    calc
      variableBoundaryLowPositiveNormalizedSum sigma H beta m
          ≤ ((m : ℝ) ^ (sigma - 1) *
                (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
              variableBoundaryTargetAmplitude beta (m : ℝ) := hnormalized
      _ ≤ ((m : ℝ) ^ (sigma - 1) *
                (C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2)) /
              targetZeroPowerAmplitude beta0 (m : ℝ) := hdenominator
      _ = C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 *
            ((m : ℝ) ^ (sigma - 1) /
              (m : ℝ) ^ (beta0 - 1)) := by
        unfold targetZeroPowerAmplitude
        ring_nf
      _ = C * ((alpha + 2) * Real.log (m : ℝ) ^ 4) ^ 2 *
            (m : ℝ) ^ ((sigma - 1) - (beta0 - 1)) := by
        rw [← Real.rpow_sub hmPos]
      _ = actualReciprocalLowNormalizedLogPowerMajorant
            C alpha beta0 sigma (m : ℝ) := by
        unfold actualReciprocalLowNormalizedLogPowerMajorant
        ring_nf

/-- Complete variable-boundary explicit-formula residual with reciprocal low
tails and the existing automatic high/real tails. -/
theorem
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_reciprocal
    {sigma beta0 alpha epsilon : ℝ} {H beta : ℝ → ℝ}
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright : IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta)
    (remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta0 H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  apply
    actualVariableBoundaryFullTailExplicitFormulaResidual_targetAmplitudeNegligible_of_realGap
      hbeta0 hbetaLower hHtop hrightReal hhalf hone hright hgap
  · exact variableBoundaryVisiblePositiveTailMajorized_low hhalf hone hright
  · exact variableBoundaryLowPositiveNormalizedSum_tendsto_zero_reciprocal
      hbetaLower hHle hHtop halpha hepsilon hmargin
  · exact remainder

/-- Signed moving-package witnesses survive the reciprocal variable-boundary
residual. -/
theorem
    actualMonotoneVariableBoundary_unnormalizedSignedOmega_reciprocal
    {sigma beta0 alpha epsilon c loss : ℝ} {H beta : ℝ → ℝ}
    (hloss : 0 < loss) (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright : IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta0 H)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ => c * variableBoundaryTargetAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ => c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta x) := by
  have hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta :=
    variableBoundaryAbsorptionOrGap_of_monotone hHtop hbetaMono hright
  have hresidual :=
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_reciprocal
      hbeta0 hbetaLower hHle hHtop halpha hepsilon hmargin
      hrightReal hhalf hone hright hgap remainder
  have hamplitude := eventually_variableBoundaryTargetAmplitude_pos beta
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| <
          loss * variableBoundaryTargetAmplitude beta (m : ℝ) :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hresidual hloss
  have hpositiveNatural := hmainPos.transfer_eventually_sub_lt happrox
  have hnegativeNatural := hmainNeg.transfer_eventually_sub_lt happrox
  have hpositiveRelative :
      HasFarPositiveTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * variableBoundaryTargetAmplitude beta x) :=
    hpositiveNatural.toReal
  have hnegativeRelative :
      HasFarNegativeTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * variableBoundaryTargetAmplitude beta x) :=
    hnegativeNatural.toReal
  refine ⟨sub_pos.mpr hlossC, ?_⟩
  exact
    ⟨hpositiveRelative.relativeChebyshevPsi0Error_to_unnormalized_variableExponent,
      hnegativeRelative.relativeChebyshevPsi0Error_to_unnormalized_variableExponent⟩

/-- Unified variable-boundary upper and conditional signed transfer under the
reciprocal low-layer margin. -/
theorem actualMonotoneVariableBoundaryUnifiedUpperSignedOmega_reciprocal
    {sigma beta0 alpha epsilon eta c loss : ℝ} {H beta : ℝ → ℝ}
    (heta : 0 < eta) (hloss : 0 < loss) (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hright : IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta0 H)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ => c * variableBoundaryTargetAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ => c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ)| <
          (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
            variableBoundaryTargetAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta x) := by
  have hsigmaBeta0 : sigma < beta0 := by linarith
  have hgap := variableBoundaryAbsorptionOrGap_of_monotone hHtop hbetaMono hright
  have hresidual :=
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_reciprocal
      hbeta0 hbetaLower hHle hHtop halpha hepsilon hmargin
      hrightReal hhalf hone hright hgap remainder
  have hupper :=
    eventually_abs_relativeChebyshevPsi0Error_lt_variableBoundaryCap_add
      heta
      (actualCarlsonVariableBoundaryCoefficientCap
        hhalf hone hsigmaBeta0 hbetaLower)
      hresidual
  rcases actualMonotoneVariableBoundary_unnormalizedSignedOmega_reciprocal
      hloss hlossC hbeta0 hbetaLower hbetaMono hHle hHtop halpha hepsilon
      hmargin hrightReal hhalf hone hright remainder hmainPos hmainNeg with
    ⟨hcoefficient, hsigned⟩
  exact ⟨hupper, hcoefficient, hsigned⟩

end

end PrimeNumberTheorem
