import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryExtensionAbsoluteMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingRightEdgeSeedStabilityTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageAutomaticEnergyBoundaryBudget
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalWitness
import PrimeNumberTheorem.ZeroDensityLayerBudgetAttainedGlobalRightEdgeRealClosedSeed
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTUnnormalizedTargetAmplitudeTransfer

/-!
# Actual zero-package Omega through a moving right-edge decomposition

An actual equal-real-part zero package supplies the fixed finite mean-square
seed.  Carlson boundary capture controls every additional zero entering the
moving right-edge cluster, while the moving two-height transfer controls the
cluster complement and the explicit-formula remainder.  This closes a fully
concrete dynamic-layering route from a zeta-zero package to the unnormalized
Chebyshev error.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/-- A nonempty target-line seed with a stable package-local real gap produces
an actual equal-real-part package whose mean-square witness survives the
moving right-edge extension.  The final coefficient is one quarter of the
seed coefficient left after twice the residual Carlson boundary mass. -/
theorem
    exists_targetLineSeed_actualZeroPackageMovingRightEdgeUnnormalizedOmega
    {S₀ : Finset ℂ} {beta q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S₀)
    (hnonempty : S₀.Nonempty)
    (hbeta : 2 / 3 < beta)
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
      1 / 2 < transferTau ∧
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
  have hanchor :
      (1 / 2 : ℝ) < (3 * beta - 1) / 2 := by
    linarith
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        (theta := (1 / 2 : ℝ)) hbeta hbetaOne hanchor with
    ⟨sigma, transferTau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
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
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hHtop : Tendsto H atTop atTop := by
    simpa [H] using selectedUniformGoodHeight_tendsto_atTop halpha selection
  have hseedWitness :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ => dynamicVisibleClusterPNTMain H P (m : ℝ))
        (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [H, P, c, mul_assoc] using
      hasFarNaturalPointTargetAmplitudeWitness_actualZeroPackage_visibleCluster
        H hHtop T beta L q hL henergy hqOne
  have hfull :=
    eventually_selectedFullOutsideClusterPNTAbsoluteMass_div_target_lt_two_mul_boundaryMass_add
      (fun rho => (hP rho).symm)
      hsigmaHalf hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hHnonneg hHle hreHigh hreReal hdelta
  have hextension :=
    eventually_selectedMovingRightEdgeExtension_div_target_lt_two_mul_boundaryMass_add
      (sigma := sigma) (transferTau := transferTau) (delta := delta) hfull
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
  have hresult :=
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSeedNaturalTargetTransfer
      (S₀ := P) (c := c) (loss := loss)
      hbetaPos halphaOne hcontour selection
      hsigmaHalf hsigmaOne htauBeta halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le
      hepsilonHigh hstripLow hstripHigh
      hnet htargetP
      (by simpa [H] using hseedWitness)
      (by simpa [H] using hnew)
  have hrelative :
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ => coefficient * targetZeroPowerAmplitude beta x) := by
    convert hresult.2 using 1 <;>
      funext x <;> dsimp [coefficient, loss, delta] <;> ring
  have hunnormalized :
      HasFarTargetAmplitudeWitness chebyshevPsi0Error
        (fun x : ℝ => coefficient * x ^ beta) :=
    hrelative.relativeChebyshevPsi0Error_to_unnormalized
  refine
    ⟨sigma, transferTau, alpha, T, L, coefficient,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta,
      hcontour, halpha, halphaOne, hT, hL,
      hseedPackage, henergy, ?_, hcoefficient, hresult.1,
      hunnormalized⟩
  simpa [boundary, c, P] using hboundary

/-- If a global maximal nontrivial-zero real part is attained above `2/3`,
the real-closed attained-edge seed instantiates the complete dynamic-layering
chain and forces an unnormalized PNT Omega witness at the exact maximal
`x^(rho.re)` scale. -/
theorem
    attainedGlobalRightEdgeRealClosed_actualZeroPackageMovingRightEdgeUnnormalizedOmega
    {rho : ℂ} {q : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hattained : IsAttainedGlobalNontrivialZeroRealPart rho)
    (hbeta : 2 / 3 < rho.re)
    (hbetaOne : rho.re < 1)
    (hq : 0 < q) (hqOne : q < 1) :
    ∃ sigma transferTau alpha T L coefficient : ℝ,
      1 / 2 < sigma ∧
      sigma < transferTau ∧
      1 / 2 < transferTau ∧
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
    exists_targetLineSeed_actualZeroPackageMovingRightEdgeUnnormalizedOmega
      selection hseed hnonempty hbeta hbetaOne hcap hrealGap hq hqOne

end
end PrimeNumberTheorem
