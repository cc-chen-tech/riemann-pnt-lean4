import PrimeNumberTheorem.ZeroDensityLayerBudgetAttainedGlobalRightEdgeRealClosedSeed

/-!
# Reciprocal Omega from a real-closed attained right-edge seed

The reciprocal PNT transfer only needs strict real-part control for the
real-ordinate zeros outside the selected equal-real-part package.  Closing an
attained right-edge seed under all real-ordinate zeros on the maximal line
supplies exactly that local condition, without assuming globally that every
real-ordinate nontrivial zero lies strictly to the left.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/-- Package-local real-ordinate strictness is sufficient for the reciprocal
actual-zero-package sign transfer. -/
theorem actualZeroPackage_reciprocalPNTSignAlternative_of_packageRealGap
    {T beta L q sigma heightDelta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hsigmaBeta : sigma < beta) (hbetaOne : beta < 1)
    (hheightDelta : 0 < heightDelta) (hheightDeltaBeta : heightDelta < beta)
    (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hqOne : q < 1)
    (hcap : OutsideClusterRealPartCap
      (equalRealPartZeroPackage T beta) beta)
    (hreReal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
        (equalRealPartZeroPackage T beta), rho.re < beta)
    (houtside :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        (q * Real.sqrt
          (actualEqualRealPartZeroPackageEnergy T beta L)) / 2) :
    let coefficient :=
      (q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta)) / 2
    0 < coefficient ∧
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ => coefficient *
            targetZeroPowerAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ => coefficient *
            targetZeroPowerAmplitude beta (m : ℝ))) := by
  let S := equalRealPartZeroPackage T beta
  let inner := reciprocalContourNearOptimalInnerExponent beta heightDelta
  let outer := reciprocalContourNearOptimalOuterExponent beta heightDelta
  let H := selectedUniformGoodHeight inner selection
  let epsilon := (beta - sigma) / 2
  let c := q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L)
  let boundary := actualCarlsonOutsideClusterBoundaryMass
    (sigma := sigma) beta S
  let coefficient := (c - 2 * boundary) / 2
  have hbeta : 0 < beta := by linarith
  have hcoefficient : 0 < coefficient := by
    dsimp [coefficient, c, boundary, S]
    linarith
  have hwindow := reciprocalContourNearOptimalWindow_spec
    hbetaOne hheightDelta hheightDeltaBeta
  rcases hwindow with ⟨hwindow, _, _⟩
  have houter : 0 < outer := hwindow.1.trans hwindow.2.2.2
  have hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight outer x := by
    simpa [H, inner, outer] using
      eventually_selectedUniformGoodHeight_le_polynomialHeight
        hwindow.1 hwindow.2.2.2 selection
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using selectedUniformGoodHeight_tendsto_atTop hwindow.1 selection
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hmargin : sigma - beta + epsilon < 0 := by
    dsimp [epsilon]
    linarith
  have hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S := by
    intro rho
    exact (equalRealPartZeroPackage_isConjugationInvariant T beta rho).symm
  let input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S 2 :=
    fun x => pntHybridCanonicalTwoStripOutsideClusterBucketInput sigma (H x) S
  have hreLow : ∀ x rho, rho ∈ (input x).layer (0 : Fin 2) →
      rho.re ≤ sigma := by
    intro x rho hrho
    exact pntHybridCanonicalTwoStripOutsideCluster_low_re_le hrho
  have hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = (0 : Fin 2) := by
    intro x rho hrho hre
    exact pntHybridCanonicalTwoStripOutsideCluster_low_cover hrho hre
  have hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta := by
    intro index hout
    exact hcap.actualCarlsonPositiveZeroRealPart_le index hout
  have remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta H := by
    simpa [H, inner] using
      selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hbeta hwindow.1 hwindow.2.1 hwindow.2.2.1 selection
  have hseedSign :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => dynamicVisibleClusterPNTMain H S (m : ℝ))
          (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => dynamicVisibleClusterPNTMain H S (m : ℝ))
          (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [S, c, mul_assoc] using
      actualZeroPackage_visibleCluster_naturalPoint_signAlternative
        H hHtop T beta L q hL henergy hqOne
  have hresidual :=
    eventually_abs_actualCarlsonSelectedHeightPNTClusterResidual_lt_boundaryCoefficient_mul_targetAmplitude_reciprocal
      input (0 : Fin 2) hS hHle hHtop hbeta hhalf hone hreLow hlowCover
      houter hepsilon hmargin hreHigh (by simpa [S] using hreReal)
      remainder hcoefficient
  have hcoefficientIdentity : c - (2 * boundary + coefficient) = coefficient := by
    dsimp [coefficient]
    ring
  refine ⟨hcoefficient, ?_⟩
  rcases hseedSign with hpos | hneg
  · left
    simpa [hcoefficientIdentity] using
      hpos.transfer_eventually_sub_lt
        (f := fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (loss := 2 * boundary + coefficient) hresidual
  · right
    simpa [hcoefficientIdentity] using
      hneg.transfer_eventually_sub_lt
        (f := fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (loss := 2 * boundary + coefficient) hresidual

/-- A target-line seed whose selected packages have a strict real-ordinate
outside gap automatically forces one unnormalized PNT Omega sign. -/
theorem exists_targetLineSeed_actualReciprocalPNTUnnormalizedOmegaAlternative_of_packageRealGap_automatic
    {S₀ : Finset ℂ} {sigma beta q heightDelta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hnonempty : S₀.Nonempty)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hsigmaBeta : sigma < beta) (hbetaOne : beta < 1)
    (hheightDelta : 0 < heightDelta) (hheightDeltaBeta : heightDelta < beta)
    (hcap : OutsideClusterRealPartCap S₀ beta)
    (hrealGap : ∀ {T : ℝ},
      (∀ z ∈ S₀, z ∈ equalRealPartZeroPackage T beta) →
      ∀ z ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
          (equalRealPartZeroPackage T beta), z.re < beta)
    (hq : 0 < q) (hqOne : q < 1) :
    ∃ T L coefficient : ℝ,
      0 ≤ T ∧ 0 < L ∧ 0 < coefficient ∧
      (∀ z ∈ S₀, z ∈ equalRealPartZeroPackage T beta) ∧
      0 < actualEqualRealPartZeroPackageEnergy T beta L ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => coefficient * x ^ beta) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => coefficient * x ^ beta)) := by
  rcases exists_actualZeroPackage_energy_boundaryBudget
      (sigma := sigma) (beta := beta) (q := q)
      hseed hnonempty hhalf hone hcap hq with
    ⟨T, L, hT, hL, hseedPackage, hcapPackage, henergy, houtside⟩
  have hsign := actualZeroPackage_reciprocalPNTSignAlternative_of_packageRealGap
    selection hhalf hone hsigmaBeta hbetaOne hheightDelta hheightDeltaBeta
    hL henergy hqOne hcapPackage (hrealGap hseedPackage) houtside
  let coefficient :=
    (q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) -
      2 * actualCarlsonOutsideClusterBoundaryMass
        (sigma := sigma) beta (equalRealPartZeroPackage T beta)) / 2
  have hcoefficient : 0 < coefficient := by
    simpa [coefficient] using hsign.1
  refine ⟨T, L, coefficient, hT, hL, hcoefficient, hseedPackage, henergy, ?_⟩
  rcases hsign.2 with hpos | hneg
  · left
    exact hpos.toReal.relativeChebyshevPsi0Error_to_unnormalized
  · right
    exact hneg.toReal.relativeChebyshevPsi0Error_to_unnormalized

/-- An attained global right-edge zero forces one unnormalized PNT Omega sign
at the exact `x^(rho.re)` scale, with no global real-ordinate strictness
assumption.  The conclusion remains a one-sign alternative. -/
theorem attainedGlobalRightEdgeRealClosed_actualReciprocalPNTUnnormalizedOmegaAlternative
    {rho : ℂ} {sigma q heightDelta : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hattained : IsAttainedGlobalNontrivialZeroRealPart rho)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hsigmaBeta : sigma < rho.re) (hbetaOne : rho.re < 1)
    (hheightDelta : 0 < heightDelta) (hheightDeltaBeta : heightDelta < rho.re)
    (hq : 0 < q) (hqOne : q < 1) :
    ∃ T L coefficient : ℝ,
      0 ≤ T ∧ 0 < L ∧ 0 < coefficient ∧
      (∀ z ∈ attainedGlobalRightEdgeRealClosedSeed rho,
        z ∈ equalRealPartZeroPackage T rho.re) ∧
      0 < actualEqualRealPartZeroPackageEnergy T rho.re L ∧
      (HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => coefficient * x ^ rho.re) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => coefficient * x ^ rho.re)) := by
  rcases attainedGlobalRightEdgeRealClosedSeed_spec hattained with
    ⟨hseed, hnonempty, hcap, hrealGap⟩
  exact
    exists_targetLineSeed_actualReciprocalPNTUnnormalizedOmegaAlternative_of_packageRealGap_automatic
      selection hseed hnonempty hhalf hone hsigmaBeta hbetaOne
      hheightDelta hheightDeltaBeta hcap hrealGap hq hqOne

end
end PrimeNumberTheorem
