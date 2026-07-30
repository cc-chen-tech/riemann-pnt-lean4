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

end PrimeNumberTheorem
