import PrimeNumberTheorem.ZeroDensityLayerBudgetActualZeroPackageNaturalPNTLowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay

/-!
# Automatic natural remainder for the actual zero-package lower transfer

For the uniform natural-point good-height selector, the contour remainder
certificate and height cofinality are automatic.  The Carlson outside-cluster
certificate remains explicit.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

theorem actualZeroPackage_selectedUniformGoodHeight_naturalLowerTransfer
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    {T L q : ℝ} (hL : 0 < L)
    (henergy : 0 < actualEqualRealPartZeroPackageEnergy T beta L)
    (hqpos : 0 < q) (hq : q < 1)
    {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x)
          (ZeroForcedOscillation.equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha (ZeroForcedOscillation.equalRealPartZeroPackage T beta)
          n (selectedUniformGoodHeight alpha selection) input) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x =>
        (q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
          targetZeroPowerAmplitude beta x) / 2) := by
  exact actualZeroPackage_naturalPointRemainder_lowerTransfer
    hbeta
    (selectedUniformGoodHeight_tendsto_atTop halpha selection)
    hL henergy hqpos hq certificate
    (selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hmargin selection)

theorem actualZeroPackage_selectedUniformGoodHeight_naturalLowerTransfer_of_nonempty
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (halpha : 0 < alpha) (halphaOne : alpha ≤ 1)
    (hmargin : 1 - beta < alpha)
    (selection : UniformNaturalPointGoodHeightSelection)
    {T q : ℝ}
    (hnonempty :
      (ZeroForcedOscillation.equalRealPartZeroPackage T beta).Nonempty)
    (hqpos : 0 < q) (hq : q < 1)
    {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x)
          (ZeroForcedOscillation.equalRealPartZeroPackage T beta) n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha (ZeroForcedOscillation.equalRealPartZeroPackage T beta)
          n (selectedUniformGoodHeight alpha selection) input) :
    ∃ L, 0 < L ∧
      HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x =>
          (q * Real.sqrt (actualEqualRealPartZeroPackageEnergy T beta L) *
            targetZeroPowerAmplitude beta x) / 2) := by
  rcases exists_actualEqualRealPartZeroPackageEnergy_pos_of_nonempty hnonempty with
    ⟨L, hL, henergy⟩
  exact ⟨L, hL,
    actualZeroPackage_selectedUniformGoodHeight_naturalLowerTransfer
      hbeta halpha halphaOne hmargin selection hL henergy hqpos hq certificate⟩

end PrimeNumberTheorem
