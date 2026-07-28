import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalAutomaticRemainder

/-!
# Natural selected-height PNT lower transfer from a concrete zeta zero

This is the concrete entry point for the natural-sampling route.  A
nontrivial zeta zero supplies a nonempty equal-real-part package and hence a
positive package-energy window.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

theorem actualZeroPackage_selectedUniformGoodHeight_naturalLowerTransfer_of_nontrivialZero
    {rho : ℂ} {T alpha q : ℝ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (hT : |rho.im| ≤ T)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - rho.re < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hqpos : 0 < q) (hq : q < 1)
    {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x)
          (ZeroForcedOscillation.equalRealPartZeroPackage T rho.re) n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        rho.re alpha
          (ZeroForcedOscillation.equalRealPartZeroPackage T rho.re)
          n (selectedUniformGoodHeight alpha selection) input) :
    ∃ L, 0 < L ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x =>
          (q * Real.sqrt
              (actualEqualRealPartZeroPackageEnergy T rho.re L) *
            targetZeroPowerAmplitude rho.re x) / 2) := by
  exact
    actualZeroPackage_selectedUniformGoodHeight_naturalLowerTransfer_of_nonempty
      hzero.2.1 halpha halphaOne hmargin selection
      (equalRealPartZeroPackage_nonempty_of_nontrivialZero hzero hT)
      hqpos hq certificate

end PrimeNumberTheorem
