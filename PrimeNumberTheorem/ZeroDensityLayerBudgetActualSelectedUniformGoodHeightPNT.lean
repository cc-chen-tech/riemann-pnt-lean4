import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightMovingCarlsonPNTTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay

/-!
# PNT transfer at the canonical uniformly good height

This file removes the explicit-formula remainder certificate from the final
selected-height transfer.  The canonical selector already supplies that
certificate at every exponent in `(0, 1]`; only decay of the full finite-zero
tail remains as mathematical input.
-/

namespace PrimeNumberTheorem

open Filter

/-- A canonical height selected from `[x^innerAlpha - 1, x^innerAlpha]`
is eventually below every strictly larger polynomial height. -/
theorem eventually_selectedUniformGoodHeight_le_polynomialHeight
    {innerAlpha outerAlpha : ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ∀ᶠ x : ℝ in atTop,
      selectedUniformGoodHeight innerAlpha selection x ≤
        carlsonPolynomialHeight outerAlpha x := by
  filter_upwards
      [eventually_selectedUniformGoodHeight_mem hinner selection,
        eventually_ge_atTop (1 : ℝ)] with x hx hxOne
  exact hx.2.trans (by
    simpa [carlsonPolynomialHeight] using
      Real.rpow_le_rpow_of_exponent_le hxOne hstrict.le)

/-- The fully automatic exact-height Carlson strip decay survives replacement
of `x^outerAlpha` by the canonical good height selected below
`x^innerAlpha`, provided `innerAlpha < outerAlpha`. -/
theorem tendsto_actualSelectedUniformGoodHeightMovingCarlsonStripMass_zero
    {innerAlpha outerAlpha : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 8 ∧
          128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonStripMass
        (selectedUniformGoodHeight innerAlpha selection) delta)
      atTop (nhds 0) := by
  have hheight :
      ∀ᶠ m : ℕ in atTop,
        selectedUniformGoodHeight innerAlpha selection (m : ℝ) ≤
          carlsonPolynomialHeight outerAlpha (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_selectedUniformGoodHeight_le_polynomialHeight
        hinner hstrict selection)
  have hexact :
      Tendsto
        (actualMovingCarlsonStripMass outerAlpha delta)
        atTop (nhds 0) :=
    tendsto_actualMovingCarlsonStripMass_zero_fullyAutomatic
      houter hdelta hgap
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun m =>
      actualSelectedHeightMovingCarlsonStripMass_nonneg
        (selectedUniformGoodHeight innerAlpha selection) delta m)
    ?_ hexact
  filter_upwards [hheight] with m hm
  exact actualSelectedHeightMovingCarlsonStripMass_le_exact hm

/-- The critical-half layer at the canonical good height tends to zero.
Unlike the earlier unit-window theorem, this uses the selector's actual lower
window and only its polynomial upper bound and divergence to infinity. -/
theorem tendsto_actualSelectedUniformGoodHeightCriticalHalfPNTLayerNorm_zero
    {innerAlpha outerAlpha epsilon : ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun m : ℕ =>
        dynamicPositiveOutsideClusterPNTLayerNorm
          (selectedUniformGoodHeight innerAlpha selection) ∅
          (actualSelectedHeightCriticalHalfCanonicalInput
            (selectedUniformGoodHeight innerAlpha selection))
          0 (m : ℝ))
      atTop (nhds 0) := by
  let H : ℝ → ℝ := selectedUniformGoodHeight innerAlpha selection
  obtain ⟨kappa, hkappa, hnorm⟩ :=
    exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
      H (1 / 2) ∅
  have hre :
      ∀ (x : ℝ),
        ∀ rho ∈ (actualSelectedHeightCriticalHalfCanonicalInput H x).layer 0,
          rho.re ≤ 1 / 2 := by
    intro x rho hrho
    have h :
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) ∅ ∧
          rho.re ≤ 1 / 2 := by
      simpa [actualSelectedHeightCriticalHalfCanonicalInput,
        PositiveZeroOutsideClusterBucketInput.layer,
        pntHybridCanonicalTwoStripOutsideClusterBucketInput] using hrho
    exact h.2
  have hnormalized :=
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid_selectedHeight
      (beta := 1) (tau := 1 / 2) (alpha := outerAlpha)
      (epsilon := epsilon)
      (actualSelectedHeightCriticalHalfCanonicalInput H) 0
      (eventually_selectedUniformGoodHeight_le_polynomialHeight
        hinner hstrict selection)
      (selectedUniformGoodHeight_tendsto_atTop hinner selection)
      hkappa hnorm hre houter hepsilon (by linarith)
  have hreal :
      Tendsto
        (fun x : ℝ =>
          dynamicPositiveOutsideClusterPNTLayerNorm H ∅
            (actualSelectedHeightCriticalHalfCanonicalInput H) 0 x)
        atTop (nhds 0) := by
    simpa [targetZeroPowerAmplitude,
      dynamicPositiveOutsideClusterPNTLayerNorm] using hnormalized
  simpa [H] using hreal.comp tendsto_natCast_atTop_atTop

/-- At canonical good heights, the positive-ordinate finite-zero tail tends to
zero once the genuine middle-strip and right-edge inputs are supplied.
Critical-half decay and the moving Carlson strip are discharged internally. -/
theorem tendsto_dynamicPositivePNTTailNorm_of_selectedUniformGoodHeightMovingCarlson
    {innerAlpha outerAlpha epsilon : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta :
      ∀ᶠ m : ℕ in atTop,
        0 < delta m ∧ delta m ≤ 1 / 8 ∧
          128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap :
      ∀ᶠ m : ℕ in atTop,
        ActualSelectedHeightMovingPositiveRightEdgeCap
          (selectedUniformGoodHeight innerAlpha selection) delta m)
    (hmiddle :
      Tendsto
        (actualSelectedHeightMovingCarlsonMiddleMass
          (selectedUniformGoodHeight innerAlpha selection) delta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ =>
        dynamicPositivePNTTailNorm
          (selectedUniformGoodHeight innerAlpha selection) (m : ℝ))
      atTop (nhds 0) := by
  have hcritical :=
    tendsto_actualSelectedUniformGoodHeightCriticalHalfPNTLayerNorm_zero
      hinner hstrict houter hepsilon hmargin selection
  have hmoving :=
    tendsto_actualSelectedUniformGoodHeightMovingCarlsonStripMass_zero
      hinner hstrict houter selection hdelta hgap
  have hsum :=
    (hcritical.add hmiddle).add hmoving
  have hsum0 :
      Tendsto
        (fun m : ℕ =>
          dynamicPositiveOutsideClusterPNTLayerNorm
                (selectedUniformGoodHeight innerAlpha selection) ∅
                (actualSelectedHeightCriticalHalfCanonicalInput
                  (selectedUniformGoodHeight innerAlpha selection))
                0 (m : ℝ) +
              actualSelectedHeightMovingCarlsonMiddleMass
                (selectedUniformGoodHeight innerAlpha selection) delta m +
            actualSelectedHeightMovingCarlsonStripMass
              (selectedUniformGoodHeight innerAlpha selection) delta m)
        atTop (nhds 0) := by
    simpa using hsum
  refine squeeze_zero'
    (Filter.Eventually.of_forall fun m => by
      unfold dynamicPositivePNTTailNorm
      exact norm_nonneg _)
    ?_ hsum0
  filter_upwards [hcap] with m hm
  exact
    dynamicPositivePNTTailNorm_le_selectedCriticalHalf_add_movingMasses hm

/-- Real-ordinate nontrivial zeros are negligible at the canonical good
height.  This is unconditional: membership in the nontrivial-zero finset
already contains the strict bound `re rho < 1`. -/
theorem tendsto_dynamicRealOrdinatePNTZeroTailNorm_of_selectedUniformGoodHeight
    {alpha : ℝ}
    (halpha : 0 < alpha)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Tendsto
      (fun m : ℕ =>
        dynamicRealOrdinatePNTZeroTailNorm
          (selectedUniformGoodHeight alpha selection) (m : ℝ))
      atTop (nhds 0) := by
  let H : ℝ → ℝ := selectedUniformGoodHeight alpha selection
  have hHtop : Tendsto H atTop atTop :=
    selectedUniformGoodHeight_tendsto_atTop halpha selection
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hHtop.eventually (eventually_ge_atTop (0 : ℝ))
  have hre :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re < 1 := by
    intro rho hrho
    have h :
        (rho ∈ nontrivialZerosFinset 0 ∧ rho.im ≤ 0) ∧
          0 ≤ rho.im := by
      simpa [realOrdinateNontrivialZerosOutsideClusterFinset,
        realOrdinateNontrivialZerosFinset,
        nonPositiveNontrivialZerosFinset] using hrho
    exact (mem_nontrivialZerosFinset.mp h.1.1).1.2.2
  have hnegligible :=
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      H ∅ 1 hHnonneg hre
  have hreal :
      Tendsto
        (dynamicRealOrdinatePNTZeroTailNorm H)
        atTop (nhds 0) := by
    simpa [TargetAmplitudeNegligible, targetZeroPowerAmplitude,
      dynamicRealOrdinateOutsideClusterPNTZeroTailNorm,
      dynamicRealOrdinatePNTZeroTailNorm,
      realOrdinateNontrivialZerosOutsideClusterFinset] using hnegligible
  simpa [H] using hreal.comp tendsto_natCast_atTop_atTop

/-- A fixed global real-part cap strictly left of one eventually implies the
moving selected-height cap whenever the moving gap tends to zero. -/
theorem
    eventually_actualSelectedHeightMovingPositiveRightEdgeCap_of_globalCap
    {H : ℝ → ℝ} {delta : ℕ → ℝ} {beta : ℝ}
    (hbetaOne : beta < 1)
    (hdeltaZero : Tendsto delta atTop (nhds 0))
    (hglobalCap :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.re ≤ beta) :
    ∀ᶠ m : ℕ in atTop,
      ActualSelectedHeightMovingPositiveRightEdgeCap H delta m := by
  have hdeltaUpper :
      ∀ᶠ m : ℕ in atTop, delta m < 1 - beta :=
    (tendsto_order.mp hdeltaZero).2 _ (sub_pos.mpr hbetaOne)
  filter_upwards [hdeltaUpper] with m hm rho hrho
  have hzero :
      RiemannHypothesis.IsNontrivialZero rho :=
    (mem_positiveNontrivialZerosFinset.mp hrho).1
  exact (hglobalCap rho hzero).trans (by linarith)

/-- Under a fixed global real-part cap, the complete moving middle-strip mass
decays whenever the selected-height exponent fits inside the remaining power
gap.  The proof uses the global analytic-multiplicity bound `O(T log T)` on
the actual multiplicity-weighted zeta kernels. -/
theorem
    tendsto_actualSelectedUniformGoodHeightMovingCarlsonMiddleMass_zero_of_globalCap
    {innerAlpha outerAlpha beta : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hpowerGap : beta + outerAlpha < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hglobalCap :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.re ≤ beta) :
    Tendsto
      (actualSelectedHeightMovingCarlsonMiddleMass
        (selectedUniformGoodHeight innerAlpha selection) delta)
      atTop (nhds 0) := by
  let H : ℝ → ℝ := selectedUniformGoodHeight innerAlpha selection
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        H beta ∅ with
    ⟨kappa, hkappa, hnorm⟩
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobalMultiplicity⟩
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight outerAlpha x :=
    eventually_selectedUniformGoodHeight_le_polynomialHeight
      hinner hstrict selection
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using
      selectedUniformGoodHeight_tendsto_atTop hinner selection
  have hlogReal :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four houter
  have hlog :
      ∀ᶠ m : ℕ in atTop,
        1 + Real.log ((m : ℝ) ^ outerAlpha + 6) ≤
          (outerAlpha + 2) * Real.log (m : ℝ) ^ 4 :=
    tendsto_natCast_atTop_atTop.eventually hlogReal
  let gapEpsilon : ℝ := (1 - (beta + outerAlpha)) / 2
  have hgapEpsilon : 0 < gapEpsilon := by
    dsimp [gapEpsilon]
    linarith
  have hdecayMargin :
      beta - 1 + outerAlpha + gapEpsilon < 0 := by
    dsimp [gapEpsilon]
    linarith
  have hmajorReal :
      Tendsto
        (actualHybridLowNormalizedLogPowerMajorant
          C kappa 1 beta outerAlpha)
        atTop (nhds 0) :=
    tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
      hC hkappa houter hgapEpsilon hdecayMargin
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          actualHybridLowNormalizedLogPowerMajorant
            C kappa 1 beta outerAlpha (m : ℝ))
        atTop (nhds 0) :=
    hmajorReal.comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards with m
    exact Finset.sum_nonneg fun rho hrho => norm_nonneg _
  · filter_upwards [
      eventually_ge_atTop (1 : ℕ),
      hHtop.comp tendsto_natCast_atTop_atTop |>.eventually
        (eventually_ge_atTop (4 : ℝ)),
      tendsto_natCast_atTop_atTop.eventually hHle,
      hlog] with m hm hHfour hHupper hlogBound
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast (Nat.zero_lt_of_lt hm)
    let layer :=
      actualPositiveCarlsonStrip
        (1 / 2) (1 - 2 * delta m) (H (m : ℝ))
    have hnormLayer :
        ∀ rho ∈ layer, kappa ≤ ‖rho‖ := by
      intro rho hrho
      rcases mem_actualPositiveCarlsonStrip.mp hrho with
        ⟨hzero, him, himHeight, _, _⟩
      apply hnorm (m : ℝ) rho
      apply Finset.mem_filter.mpr
      constructor
      · exact mem_positiveNontrivialZerosOutsideClusterFinset.mpr
          ⟨hzero, him, himHeight, by simp⟩
      · exact
          pntHybridCanonicalTwoStripOutsideCluster_low_cover
            (mem_positiveNontrivialZerosOutsideClusterFinset.mpr
              ⟨hzero, him, himHeight, by simp⟩)
            (hglobalCap rho hzero)
    have hkernel :
        ∀ rho ∈ layer,
          ‖pntRelativeSimpleZeroKernel (m : ℝ) rho‖ ≤
            stripEndpointRelativeKernelBudget
              kappa beta (m : ℝ) := by
      intro rho hrho
      have hzero :=
        (mem_actualPositiveCarlsonStrip.mp hrho).1
      exact
        norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
          (by exact_mod_cast hm) hkappa (hnormLayer rho hrho)
          (hglobalCap rho hzero)
    have hkernelNonneg :
        0 ≤ stripEndpointRelativeKernelBudget
          kappa beta (m : ℝ) :=
      stripEndpointRelativeKernelBudget_nonneg
        (by exact_mod_cast (Nat.zero_le m)) hkappa.le
    have hmass :
        analyticMultiplicityMass layer ≤
          ExplicitFormulaAux.globalZeroMultiplicity (H (m : ℝ)) := by
      have hsubset :
          layer ⊆ nontrivialZerosFinset (H (m : ℝ)) := by
        intro rho hrho
        rcases mem_actualPositiveCarlsonStrip.mp hrho with
          ⟨hzero, him, himHeight, _, _⟩
        exact mem_nontrivialZerosFinset.mpr
          ⟨hzero, by simpa [abs_of_pos him] using himHeight⟩
      unfold analyticMultiplicityMass
        ExplicitFormulaAux.globalZeroMultiplicity
      exact
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun rho hrho hnot => Nat.cast_nonneg _)
    have hphysical :
        actualSelectedHeightMovingCarlsonMiddleMass H delta m ≤
          actualHybridGlobalLowLayerMajorant
            C (H (m : ℝ)) kappa beta (m : ℝ) := by
      calc
        actualSelectedHeightMovingCarlsonMiddleMass H delta m =
            ∑ rho ∈ layer,
              ‖pntRelativeZeroContribution (m : ℝ) rho‖ := rfl
        _ ≤ stripEndpointRelativeKernelBudget
                kappa beta (m : ℝ) *
              analyticMultiplicityMass layer :=
          sum_norm_pntRelativeZeroContribution_le_kernel_mul_multiplicityMass
            layer (m : ℝ)
            (stripEndpointRelativeKernelBudget
              kappa beta (m : ℝ))
            hkernelNonneg hkernel
        _ ≤ stripEndpointRelativeKernelBudget
                kappa beta (m : ℝ) *
              ExplicitFormulaAux.globalZeroMultiplicity (H (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hmass hkernelNonneg
        _ ≤ stripEndpointRelativeKernelBudget
                kappa beta (m : ℝ) *
              (C * H (m : ℝ) *
                (1 + Real.log (H (m : ℝ) + 6))) :=
          mul_le_mul_of_nonneg_left
            (hglobalMultiplicity (H (m : ℝ)) hHfour) hkernelNonneg
        _ = actualHybridGlobalLowLayerMajorant
              C (H (m : ℝ)) kappa beta (m : ℝ) := by
          unfold actualHybridGlobalLowLayerMajorant
          ring
    have hselected :
        actualHybridGlobalLowLayerMajorant
            C (H (m : ℝ)) kappa beta (m : ℝ) ≤
          actualHybridGlobalLowLayerMajorant
            C (carlsonPolynomialHeight outerAlpha (m : ℝ))
              kappa beta (m : ℝ) :=
      actualHybridGlobalLowLayerMajorant_mono_height
        hC hkappa hmPos.le hHfour hHupper
    have hcoefficient :
        0 ≤ C * kappa⁻¹ *
          (m : ℝ) ^ (beta - 1 + outerAlpha) := by
      positivity
    calc
      actualSelectedHeightMovingCarlsonMiddleMass H delta m ≤
          actualHybridGlobalLowLayerMajorant
            C (carlsonPolynomialHeight outerAlpha (m : ℝ))
              kappa beta (m : ℝ) :=
        hphysical.trans hselected
      _ =
          actualHybridGlobalLowLayerMajorant
              C (carlsonPolynomialHeight outerAlpha (m : ℝ))
                kappa beta (m : ℝ) /
            targetZeroPowerAmplitude 1 (m : ℝ) := by
        rw [show targetZeroPowerAmplitude 1 (m : ℝ) = 1 by
          simp [targetZeroPowerAmplitude], div_one]
      _ =
          C * kappa⁻¹ *
              (m : ℝ) ^ (beta - 1 + outerAlpha) *
            (1 + Real.log ((m : ℝ) ^ outerAlpha + 6)) := by
        exact
          actualHybridGlobalLowLayerMajorant_div_target_eq
            (C := C) (kappa := kappa) (beta := 1)
            (tau := beta) (alpha := outerAlpha) hmPos
      _ ≤
          C * kappa⁻¹ *
              (m : ℝ) ^ (beta - 1 + outerAlpha) *
            ((outerAlpha + 2) * Real.log (m : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hlogBound hcoefficient
      _ =
          actualHybridLowNormalizedLogPowerMajorant
            C kappa 1 beta outerAlpha (m : ℝ) := by
        unfold actualHybridLowNormalizedLogPowerMajorant
        ring

/-- The canonical uniformly good height converts the positive-ordinate moving
Carlson transfer into decay of the full finite-zero tail.  Conjugation accounts
for the second positive-ordinate copy, while the real-ordinate residual is
automatic. -/
theorem tendsto_dynamicFullPNTZeroTailNorm_of_selectedUniformGoodHeightMovingCarlson
    {innerAlpha outerAlpha epsilon : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap : ∀ᶠ m : ℕ in atTop,
      ActualSelectedHeightMovingPositiveRightEdgeCap
        (selectedUniformGoodHeight innerAlpha selection) delta m)
    (hmiddle :
      Tendsto
        (actualSelectedHeightMovingCarlsonMiddleMass
          (selectedUniformGoodHeight innerAlpha selection) delta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ =>
        dynamicFullPNTZeroTailNorm
          (selectedUniformGoodHeight innerAlpha selection) (m : ℝ))
      atTop (nhds 0) := by
  have hpositive :=
    tendsto_dynamicPositivePNTTailNorm_of_selectedUniformGoodHeightMovingCarlson
      hinner hstrict houter hepsilon hmargin selection
      hdelta hgap hcap hmiddle
  have hreal :=
    tendsto_dynamicRealOrdinatePNTZeroTailNorm_of_selectedUniformGoodHeight
      hinner selection
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          dynamicPositivePNTTailNorm
              (selectedUniformGoodHeight innerAlpha selection) (m : ℝ) +
            dynamicPositivePNTTailNorm
              (selectedUniformGoodHeight innerAlpha selection) (m : ℝ) +
            dynamicRealOrdinatePNTZeroTailNorm
              (selectedUniformGoodHeight innerAlpha selection) (m : ℝ))
        atTop (nhds 0) := by
    simpa using (hpositive.add hpositive).add hreal
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards with m
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast hm
    exact dynamicFullPNTZeroTailNorm_le_two_positive_add_real hmPos

/-- At the canonical uniformly good height, decay of the full finite-zero tail
is enough to force decay of the relative `psi₀` error.  The explicit-formula
remainder certificate is generated automatically from the selector. -/
theorem tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeight_fullTail
    {alpha : ℝ}
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hfull :
      Tendsto
        (fun m : ℕ =>
          dynamicFullPNTZeroTailNorm
            (selectedUniformGoodHeight alpha selection) (m : ℝ))
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  apply tendsto_relativeChebyshevPsi0Error_of_dynamicFullPNTZeroTailNorm hfull
  exact
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      (beta := 1) (alpha := alpha)
      (by norm_num) halpha halphaOne (by simpa using halpha) selection

/-- Canonical moving-Carlson PNT transfer.  Once the middle strip and the
moving right-edge cap decay at the uniformly good height, the Carlson layer
budget, conjugation symmetry, real-zero residual, and explicit-formula
remainder assemble into relative `psi₀` decay. -/
theorem tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeightMovingCarlson
    {innerAlpha outerAlpha epsilon : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap : ∀ᶠ m : ℕ in atTop,
      ActualSelectedHeightMovingPositiveRightEdgeCap
        (selectedUniformGoodHeight innerAlpha selection) delta m)
    (hmiddle :
      Tendsto
        (actualSelectedHeightMovingCarlsonMiddleMass
          (selectedUniformGoodHeight innerAlpha selection) delta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hfull :=
    tendsto_dynamicFullPNTZeroTailNorm_of_selectedUniformGoodHeightMovingCarlson
      hinner hstrict houter hepsilon hmargin selection
      hdelta hgap hcap hmiddle
  have hinnerOne : innerAlpha ≤ 1 := by
    linarith
  exact
    tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeight_fullTail
      hinner hinnerOne selection hfull

/-- A fixed global nontrivial-zero real-part cap discharges the moving
right-edge hypothesis in the canonical Carlson-to-PNT transfer.  The middle
strip decay remains the sole zero-tail input. -/
theorem
    tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeightMovingCarlson_globalCap
    {innerAlpha outerAlpha epsilon beta : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (hbetaOne : beta < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hdeltaZero : Tendsto delta atTop (nhds 0))
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hglobalCap :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.re ≤ beta)
    (hmiddle :
      Tendsto
        (actualSelectedHeightMovingCarlsonMiddleMass
          (selectedUniformGoodHeight innerAlpha selection) delta)
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hcap :=
    eventually_actualSelectedHeightMovingPositiveRightEdgeCap_of_globalCap
      (H := selectedUniformGoodHeight innerAlpha selection)
      hbetaOne hdeltaZero hglobalCap
  exact
    tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeightMovingCarlson
      hinner hstrict houter hepsilon hmargin selection
      hdelta hgap hcap hmiddle

/-- Fully assembled canonical Carlson-to-PNT transfer under a fixed global
real-part cap.  The power gap closes the entire middle strip, while
`delta -> 0` closes the moving right edge. -/
theorem
    tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeightMovingCarlson_globalCap_auto
    {innerAlpha outerAlpha epsilon beta : ℝ}
    {delta : ℕ → ℝ}
    (hinner : 0 < innerAlpha)
    (hstrict : innerAlpha < outerAlpha)
    (houter : 0 < outerAlpha)
    (hepsilon : 0 < epsilon)
    (hmargin : outerAlpha + epsilon < 1 / 2)
    (hbetaOne : beta < 1)
    (hpowerGap : beta + outerAlpha < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * outerAlpha * delta m ≤ 1)
    (hdeltaZero : Tendsto delta atTop (nhds 0))
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hglobalCap :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.re ≤ beta) :
    Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      atTop (nhds 0) := by
  have hmiddle :=
    tendsto_actualSelectedUniformGoodHeightMovingCarlsonMiddleMass_zero_of_globalCap
      (delta := delta)
      hinner hstrict houter hpowerGap selection hglobalCap
  exact
    tendsto_relativeChebyshevPsi0Error_of_selectedUniformGoodHeightMovingCarlson_globalCap
      hinner hstrict houter hepsilon hmargin hbetaOne selection
      hdelta hdeltaZero hgap hglobalCap hmiddle

end PrimeNumberTheorem
