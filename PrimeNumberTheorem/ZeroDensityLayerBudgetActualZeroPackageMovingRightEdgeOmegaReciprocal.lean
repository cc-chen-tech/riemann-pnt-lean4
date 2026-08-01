import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingClusterComplementReciprocal
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualReciprocalBoundaryExtensionAbsoluteMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageMovingRightEdgeOmega

/-!
# Half-threshold moving right-edge Omega by reciprocal mass

Both sides of the moving decomposition now retain the reciprocal zero
coefficient.  The moving-cluster complement is negligible under `tau < beta`,
and the moving extension is controlled in absolute mass under `sigma < beta`.
Consequently the automatic actual-package moving Omega chain needs only
`1/2 < beta < 1`, replacing the former `2/3 < beta < 1` window.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/-- Reciprocal moving-seed lower transfer.  The moving complement needs only
the strict real-part gap `tau < beta`; no two-height Carlson strip parameters
remain in this interface. -/
theorem
    automaticGoodHeight_movingRightEdgeSeedNaturalPointLowerTransfer_reciprocal
    {S₀ : Finset ℂ} {beta tau alpha c loss : ℝ}
    (hbeta : 0 < beta)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (htau : tau < beta)
    (halpha : 0 < alpha)
    (hnet : 0 < c - loss)
    (hS₀ : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hseed :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S₀ (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)))
    (hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection)
            (movingRightEdgeExceptionalCluster
                (selectedUniformGoodHeight alpha selection)
                tau (m : ℝ) \ S₀)
            (m : ℝ)| <
          loss * targetZeroPowerAmplitude beta (m : ℝ)) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => ((c - loss) * targetZeroPowerAmplitude beta x) / 2) := by
  let H := selectedUniformGoodHeight alpha selection
  let epsilon := (beta - tau) / 2
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop, H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using selectedUniformGoodHeight_tendsto_atTop halpha selection
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hmargin : tau - beta + epsilon < 0 := by
    dsimp [epsilon]
    linarith
  have hcomplement :=
    selectedMovingRightEdgeOutsideClusterComplement_targetAmplitudeNegligible_reciprocal
      hHnonneg hHle hHtop halpha hepsilon hmargin
  have hremainder :=
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hcontourMargin selection
  have hsub :
      ∀ᶠ m : ℕ in atTop,
        ∀ rho ∈ S₀,
          rho ∈ movingRightEdgeExceptionalCluster H tau (m : ℝ) := by
    simpa [H] using
      eventually_targetSeed_subset_selectedMovingRightEdgeExceptionalCluster
        halpha selection htau hS₀
  have hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ => movingRightEdgeVisibleClusterPNTMain H tau (m : ℝ))
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [movingRightEdgeVisibleClusterPNTMain, H] using
      hasFarNaturalPointTargetAmplitudeWitness_movingVisibleCluster_of_seed
        H
        (fun m : ℕ => movingRightEdgeExceptionalCluster H tau (m : ℝ))
        hsub (by simpa [H] using hseed) (by simpa [H] using hnew)
  have hamplitude :
      ∀ᶠ m : ℕ in atTop,
        0 < (c - loss) * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards
        [eventually_naturalPoint_pos_of_eventually_pos
          (targetZeroPowerAmplitude_eventually_pos beta)] with m hm
    exact mul_pos hnet hm
  have hclosed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude
      (c - loss)
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
        hbeta).naturalPoint
  have hcontour :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude
      (c - loss) (by simpa [H] using hremainder.negligible)
  have houtside :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ =>
          (c - loss) * targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          movingRightEdgeOutsideClusterPNTComplement H tau (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.const_mul_amplitude
      (c - loss) hcomplement.naturalPoint
  apply HasFarNaturalPointTargetAmplitudeWitness.toReal
  apply
    hasFarNaturalPointTargetAmplitudeWitness_of_three_remainders
      hamplitude hclosed hcontour houtside hmain
  intro m
  exact
    relativeChebyshevPsi0Error_eq_movingRightEdgeCluster_add_actualResiduals
      H tau (m : ℝ)

/-- A nonempty target-line seed with a stable package-local real gap forces an
actual unnormalized moving-right-edge Omega witness for every
`1/2 < beta < 1`.  All geometry and boundary parameters are selected
canonically. -/
theorem
    exists_targetLineSeed_actualZeroPackageMovingRightEdgeUnnormalizedOmega_reciprocal
    {S₀ : Finset ℂ} {beta q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hnonempty : S₀.Nonempty)
    (hbetaHalf : 1 / 2 < beta)
    (hbetaOne : beta < 1)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hrealGap : ∀ {T : ℝ},
      (∀ z ∈ S₀, z ∈ equalRealPartZeroPackage T beta) →
      ∀ z ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
          (equalRealPartZeroPackage T beta), z.re < beta)
    (hq : 0 < q) (hqOne : q < 1) :
    ∃ sigma transferTau alpha T L coefficient : ℝ,
      1 / 2 < sigma ∧
      sigma < transferTau ∧
      transferTau < beta ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      0 ≤ T ∧
      0 < L ∧
      (∀ z ∈ S₀, z ∈ equalRealPartZeroPackage T beta) ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) ∧
      0 < coefficient ∧
      (∃ rate : ℝ,
        0 < rate ∧ rate ≤ 1 ∧
          Tendsto
            (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
            atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x : ℝ => coefficient * x ^ beta) := by
  let sigma := ((1 / 2 : ℝ) + beta) / 2
  let transferTau := (sigma + beta) / 2
  let alpha := 1 - beta / 2
  let epsilonLow := (beta - sigma) / 2
  have hsigmaHalf : 1 / 2 < sigma := by
    dsimp [sigma]
    linarith
  have hsigmaBeta : sigma < beta := by
    dsimp [sigma]
    linarith
  have hsigmaOne : sigma < 1 := hsigmaBeta.trans hbetaOne
  have hsigmaTau : sigma < transferTau := by
    dsimp [transferTau]
    linarith
  have htauBeta : transferTau < beta := by
    dsimp [transferTau]
    linarith
  have hcontour : 1 - beta < alpha := by
    dsimp [alpha]
    linarith
  have halpha : 0 < alpha := by
    dsimp [alpha]
    linarith
  have halphaOne : alpha ≤ 1 := by
    dsimp [alpha]
    linarith
  have hepsilonLow : 0 < epsilonLow := by
    dsimp [epsilonLow]
    linarith
  have hmarginLow : sigma - beta + epsilonLow < 0 := by
    dsimp [epsilonLow]
    linarith
  rcases
      exists_actualZeroPackage_energy_boundaryBudget
        (sigma := sigma) (beta := beta) (q := q)
        hseed hnonempty hsigmaHalf hsigmaOne hcap hq with
    ⟨T, L, hT, hL, hseedPackage, hcapPackage, henergy, houtside⟩
  let P := equalRealPartZeroPackage T beta
  let H := selectedUniformGoodHeight alpha selection
  let c := q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L)
  let boundary := actualCarlsonOutsideClusterBoundaryMass
    (sigma := sigma) beta P
  let delta := (c - 2 * boundary) / 2
  let loss := 2 * boundary + delta
  let coefficient := (c - 2 * boundary) / 4
  have hboundary : 2 * boundary < c := by
    dsimp [boundary, c, P]
    linarith
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hcoefficient : 0 < coefficient := by
    dsimp [coefficient]
    linarith
  have hnet : 0 < c - loss := by
    dsimp [loss, delta]
    linarith
  have hbetaPos : 0 < beta := by linarith
  have hP : ∀ rho : ℂ, rho ∈ P ↔ (starRingEnd ℂ) rho ∈ P := by
    intro rho
    exact (equalRealPartZeroPackage_isConjugationInvariant T beta rho).symm
  have htargetP : IsTargetRealPartNontrivialZeroSeed beta P := by
    intro rho hrho
    have hdata := mem_equalRealPartZeroPackage.mp hrho
    exact ⟨hdata.1, hdata.2.2⟩
  have hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ P →
        actualCarlsonPositiveZeroRealPart index ≤ beta := by
    intro index hout
    exact hcapPackage.actualCarlsonPositiveZeroRealPart_le index hout
  have hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 P,
        rho.re < beta := by
    simpa [P] using hrealGap hseedPackage
  let input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) P 2 :=
    fun x => pntHybridCanonicalTwoStripOutsideClusterBucketInput sigma (H x) P
  have hreLow : ∀ x rho, rho ∈ (input x).layer (0 : Fin 2) →
      rho.re ≤ sigma := by
    intro x rho hrho
    exact pntHybridCanonicalTwoStripOutsideCluster_low_re_le hrho
  have hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) P,
        rho.re ≤ sigma → (input x).bucket rho = (0 : Fin 2) := by
    intro x rho hrho hre
    exact pntHybridCanonicalTwoStripOutsideCluster_low_cover hrho hre
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop, H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using selectedUniformGoodHeight_tendsto_atTop halpha selection
  have hextension :=
    eventually_selectedMovingRightEdgeExtension_div_target_lt_two_mul_boundaryMass_add_reciprocal
      (transferTau := transferTau) input
      (fun rho => (hP rho).symm) hreLow hlowCover
      hHnonneg hHle hHtop hsigmaHalf hsigmaOne halpha
      hepsilonLow hmarginLow hreHigh hreReal hdelta
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hnew :
      ∀ᶠ m : ℕ in atTop,
        |dynamicVisibleClusterPNTMain H
            (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ P)
            (m : ℝ)| <
          loss * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [hextension, hamplitude] with m hm hamp
    have hm' :
        |dynamicVisibleClusterPNTMain H
            (movingRightEdgeExceptionalCluster H transferTau (m : ℝ) \ P)
            (m : ℝ)| /
              targetZeroPowerAmplitude beta (m : ℝ) < loss := by
      simpa [boundary, loss, P] using hm
    exact (div_lt_iff₀ hamp).mp hm'
  have hseedWitness :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ => dynamicVisibleClusterPNTMain H P (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [H, P, c, mul_assoc] using
      hasFarNaturalPointTargetAmplitudeWitness_actualZeroPackage_visibleCluster
        H hHtop T beta L q hL henergy hqOne
  have hrelative :=
    automaticGoodHeight_movingRightEdgeSeedNaturalPointLowerTransfer_reciprocal
      (S₀ := P) (c := c) (loss := loss)
      hbetaPos halphaOne hcontour selection htauBeta halpha hnet htargetP
      (by simpa [H] using hseedWitness)
      (by simpa [H] using hnew)
  have hrelative' :
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ => coefficient * targetZeroPowerAmplitude beta x) := by
    convert hrelative using 1 <;>
      funext x <;> dsimp [coefficient, loss, delta] <;> ring
  have hunnormalized :=
    hrelative'.relativeChebyshevPsi0Error_to_unnormalized
  refine
    ⟨sigma, transferTau, alpha, T, L, coefficient,
      hsigmaHalf, hsigmaTau, htauBeta, hcontour, halpha, halphaOne,
      hT, hL, hseedPackage, henergy, ?_, hcoefficient,
      exists_fixedRate_relativeChebyshevPsi0Error_tendsto,
      hunnormalized⟩
  simpa [boundary, c, P] using hboundary

/-- An attained global right-edge zero above the critical line forces an
actual unnormalized moving-right-edge Omega witness at its exact real-part
scale.  The former `rho.re > 2/3` condition is reduced to `rho.re > 1/2`. -/
theorem
    attainedGlobalRightEdgeRealClosed_actualZeroPackageMovingRightEdgeUnnormalizedOmega_reciprocal
    {rho : ℂ} {q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hattained : IsAttainedGlobalNontrivialZeroRealPart rho)
    (hbetaHalf : 1 / 2 < rho.re)
    (hbetaOne : rho.re < 1)
    (hq : 0 < q) (hqOne : q < 1) :
    ∃ sigma transferTau alpha T L coefficient : ℝ,
      1 / 2 < sigma ∧
      sigma < transferTau ∧
      transferTau < rho.re ∧
      1 - rho.re < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      0 ≤ T ∧
      0 < L ∧
      (∀ z ∈ attainedGlobalRightEdgeRealClosedSeed rho,
        z ∈ equalRealPartZeroPackage T rho.re) ∧
      0 < actualEqualRealPartZeroPackageEnergy T rho.re L ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) rho.re
            (equalRealPartZeroPackage T rho.re) <
        q * Real.sqrt
          (actualEqualRealPartZeroPackageEnergy T rho.re L) ∧
      0 < coefficient ∧
      (∃ rate : ℝ,
        0 < rate ∧ rate ≤ 1 ∧
          Tendsto
            (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
            atTop (nhds 0)) ∧
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x : ℝ => coefficient * x ^ rho.re) := by
  rcases attainedGlobalRightEdgeRealClosedSeed_spec hattained with
    ⟨hseed, hnonempty, hcap, hrealGap⟩
  exact
    exists_targetLineSeed_actualZeroPackageMovingRightEdgeUnnormalizedOmega_reciprocal
      selection hseed hnonempty hbetaHalf hbetaOne
      hcap hrealGap hq hqOne

end
end PrimeNumberTheorem
