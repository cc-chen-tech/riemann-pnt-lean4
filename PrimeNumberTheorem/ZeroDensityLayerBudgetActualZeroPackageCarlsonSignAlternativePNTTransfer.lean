import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSeedWitnessHalfThresholdSignAlternativePNTTransfer

/-!
# Actual zero-package Carlson sign-alternative PNT transfer

This facade instantiates the half-threshold seed transfer with the actual
finite package of zeta zeros on one real-part line.  The package's zeta-zero
and conjugation properties are discharged automatically.  Its natural-point
mean-square witness supplies one persistent sign, which then survives the
Carlson boundary budget in the actual relative PNT error.
-/

namespace PrimeNumberTheorem

open scoped Topology
open Complex Filter ZeroForcedOscillation

noncomputable section

/--
An actual equal-real-part zeta-zero package with positive energy and boundary
mass below half of its sampled coefficient forces one persistent sign in the
actual relative Chebyshev error.

The coefficient is the exact sampled energy coefficient after finite capture
loss.  The conclusion is a disjunction, not simultaneous signed oscillation.
-/
theorem exists_actualZeroPackage_actualCarlsonHalfThresholdPNTSignAlternative
    {T beta L q sigma : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hbalance : (1 + sigma) / 2 < beta)
    (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hq : 0 < q) (hqOne : q < 1)
    (hcap :
      OutsideClusterRealPartCap
        (equalRealPartZeroPackage T beta) beta)
    (hrealStrict :
      ∀ rho : ℂ,
        RiemannHypothesis.IsNontrivialZero rho →
          rho.im = 0 → rho.re < beta)
    (houtside :
      actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta (equalRealPartZeroPackage T beta) <
        (q * Real.sqrt
          (actualEqualRealPartZeroPackageEnergy T beta L)) / 2) :
    ∃ rate loss : ℝ, ∃ S : Finset ℂ,
      0 < rate ∧
      rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0) ∧
      0 < loss ∧
      0 <
        q * Real.sqrt
            (actualEqualRealPartZeroPackageEnergy T beta L) - loss ∧
      (∀ rho ∈ equalRealPartZeroPackage T beta, rho ∈ S) ∧
      IsTargetRealPartNontrivialZeroSeed beta S ∧
      finiteVisibleClusterCoefficientMass
          (S \ equalRealPartZeroPackage T beta) < loss ∧
      2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S <
        (q * Real.sqrt
            (actualEqualRealPartZeroPackageEnergy T beta L) - loss) -
          (q * Real.sqrt
              (actualEqualRealPartZeroPackageEnergy T beta L) - loss) / 2 ∧
      (HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((q * Real.sqrt
                (actualEqualRealPartZeroPackageEnergy T beta L) - loss) / 2) *
              targetZeroPowerAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
          (fun m : ℕ =>
            ((q * Real.sqrt
                (actualEqualRealPartZeroPackageEnergy T beta L) - loss) / 2) *
              targetZeroPowerAmplitude beta (m : ℝ))) := by
  let alpha := actualCarlsonBalancedHeightExponent sigma
  let H := selectedUniformGoodHeight alpha selection
  let c := q * Real.sqrt
    (actualEqualRealPartZeroPackageEnergy T beta L)
  have halpha : 0 < alpha := by
    simpa [alpha] using
      (show 0 < actualCarlsonBalancedHeightExponent sigma by
        unfold actualCarlsonBalancedHeightExponent
        linarith)
  have hH : Tendsto H atTop atTop := by
    simpa [H] using selectedUniformGoodHeight_tendsto_atTop halpha selection
  have hS :
      ∀ rho : ℂ,
        rho ∈ equalRealPartZeroPackage T beta ↔
          (starRingEnd ℂ) rho ∈ equalRealPartZeroPackage T beta := by
    intro rho
    exact
      (equalRealPartZeroPackage_isConjugationInvariant T beta rho).symm
  have hseed :
      IsTargetRealPartNontrivialZeroSeed beta
        (equalRealPartZeroPackage T beta) := by
    intro rho hrho
    have hrhoData := mem_equalRealPartZeroPackage.mp hrho
    exact ⟨hrhoData.1, hrhoData.2.2⟩
  have hseedSign :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
          (fun m : ℕ =>
            dynamicVisibleClusterPNTMain H
              (equalRealPartZeroPackage T beta) (m : ℝ))
          (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) ∨
        HasFarNaturalPointNegativeTargetAmplitudeWitness
          (fun m : ℕ =>
            dynamicVisibleClusterPNTMain H
              (equalRealPartZeroPackage T beta) (m : ℝ))
          (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ)) := by
    simpa [c, mul_assoc] using
      actualZeroPackage_visibleCluster_naturalPoint_signAlternative
        H hH T beta L q hL henergy hqOne
  have htransfer :=
    exists_seedWitness_actualCarlsonHalfThresholdSignAlternativePNTTransfer
      (S₀ := equalRealPartZeroPackage T beta)
      (sigma := sigma) (beta := beta) (c := c)
      selection hS hseed hhalf hone hbalance hcap hrealStrict
      (by simpa [c] using houtside)
      (by simpa [H] using hseedSign)
  simpa [c] using htransfer

end
end PrimeNumberTheorem
