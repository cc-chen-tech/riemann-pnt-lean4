import PrimeNumberTheorem.ZeroDensityLayerBudgetActualReciprocalOutsideClusterFullResidual
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalSignAlternative
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonFiniteSeedGapTransferCluster
import PrimeNumberTheorem.ZeroDensityLayerBudgetReciprocalOptimalContourHeight

/-!
# Actual zero-package reciprocal PNT sign alternative

The actual equal-real-part zeta-zero package supplies an unsigned mean-square
witness and hence one persistent natural-point sign.  The reciprocal fixed-
cluster residual transfers that sign to the true relative PNT error under the
strict threshold `sigma < beta`, replacing the older balanced threshold.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/-- A positive-energy actual equal-real-part package whose outside Carlson
boundary mass is below half its sampled coefficient forces one persistent sign
in the true relative Chebyshev error.  Only `sigma < beta` is required. -/
theorem actualZeroPackage_reciprocalPNTSignAlternative
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
    (hrealStrict : ∀ rho : ℂ,
      RiemannHypothesis.IsNontrivialZero rho →
        rho.im = 0 → rho.re < beta)
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
  have hreReal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta := by
    intro rho hrho
    rcases Finset.mem_sdiff.mp hrho with ⟨hreal, _⟩
    have hdata := mem_realOrdinateNontrivialZerosFinset.mp hreal
    have hzero := (mem_nontrivialZerosFinset.mp hdata.1).1
    exact hrealStrict rho hzero hdata.2
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
      houter hepsilon hmargin hreHigh hreReal remainder hcoefficient
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

end
end PrimeNumberTheorem
