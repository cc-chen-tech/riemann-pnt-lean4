import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalFromZero
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStripCertificateChoice

/-!
# Threshold-driven natural PNT lower transfer from a zeta zero

This module removes the abstract Carlson finite-strip certificate from the
concrete-zero entry point.  Explicit strip endpoint thresholds select the
common polynomial height exponent and the positive strip slacks.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

noncomputable section

theorem actualZeroPackage_thresholds_naturalLowerTransfer_of_nontrivialZero
    {rho : ℂ} {T q : ℝ}
    (hzero : RiemannHypothesis.IsNontrivialZero rho)
    (hT : |rho.im| ≤ T)
    {n : ℕ} (sigma tau : Fin n → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < rho.re)
    (selection : UniformNaturalPointGoodHeightSelection)
    (hqpos : 0 < q) (hq : q < 1)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripChosenHeight rho.re sigma tau
            hzero.2.1 hzero.2.2 hsigma hsigmaOne hthreshold selection x)
          (ZeroForcedOscillation.equalRealPartZeroPackage T rho.re) n)
    (kappa : Fin n → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ z ∈ (input x).layer i, kappa i ≤ ‖z‖)
    (hre :
      ∀ i x, ∀ z ∈ (input x).layer i, z.re ≤ tau i)
    (hreal :
      ∀ z ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0
          (ZeroForcedOscillation.equalRealPartZeroPackage T rho.re),
        z.re < rho.re) :
    ∃ L, 0 < L ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x =>
          (q * Real.sqrt
              (actualEqualRealPartZeroPackageEnergy T rho.re L) *
            targetZeroPowerAmplitude rho.re x) / 2) := by
  let alpha :=
    actualSelectedHeightFiniteStripChosenExponent rho.re sigma tau
      hzero.2.1 hzero.2.2 hsigma hsigmaOne hthreshold
  have halpha :=
    actualSelectedHeightFiniteStripExponent_spec rho.re sigma tau
      hzero.2.1 hzero.2.2 hsigma hsigmaOne hthreshold
  have halpha' :
      0 < alpha ∧ alpha ≤ 1 ∧ 1 - rho.re < alpha := by
    simpa [alpha, actualSelectedHeightFiniteStripChosenExponent] using
      ⟨halpha.1, halpha.2.1, halpha.2.2.1⟩
  have certificate :=
    actualCarlsonOutsideClusterGoodHeightFiniteStripCertificate_of_thresholds
      sigma tau hzero.2.1 hzero.2.2 hsigma hsigmaOne hthreshold
      selection input kappa
      (equalRealPartZeroPackage_isConjugationInvariant T rho.re)
      hfixedSigma hkappa hnorm hre hreal
  have hheight :
      Tendsto
        (actualSelectedHeightFiniteStripChosenHeight rho.re sigma tau
          hzero.2.1 hzero.2.2 hsigma hsigmaOne hthreshold selection)
        atTop atTop := by
    simpa [actualSelectedHeightFiniteStripChosenHeight, alpha] using
      selectedUniformGoodHeight_tendsto_atTop halpha'.1 selection
  have remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate rho.re
        (actualSelectedHeightFiniteStripChosenHeight rho.re sigma tau
          hzero.2.1 hzero.2.2 hsigma hsigmaOne hthreshold selection) := by
    simpa [actualSelectedHeightFiniteStripChosenHeight, alpha] using
      selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hzero.2.1 halpha'.1 halpha'.2.1 halpha'.2.2 selection
  rcases exists_actualEqualRealPartZeroPackageEnergy_pos_of_nontrivialZero
      hzero hT with ⟨L, hL, henergy⟩
  exact ⟨L, hL,
    actualZeroPackage_naturalPointRemainder_lowerTransfer
      hzero.2.1 hheight hL henergy hqpos hq certificate
      remainderCertificate⟩

end

end PrimeNumberTheorem
