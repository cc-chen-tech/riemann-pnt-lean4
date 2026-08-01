import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedCarlsonTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightUnifiedTransfer

/-!
# Unified actual transfer at the slope-weighted balanced height

The physical Carlson optimizer selects one polynomial height for both the
actual outside-cluster zeta tail and the explicit-formula remainder.  Its
certified inequality `1 - beta < alpha` automatically supplies the strict
target-amplitude margin for the remainder certificate.

The finite main-cluster witness remains an explicit input.  It is intentionally
owned by the independent sharp-oscillation development.
-/

namespace PrimeNumberTheorem

open Filter

/--
Complete weighted Pintz--Carlson--explicit-formula transfer.

The slope-weighted optimizer automatically discharges both the finite-strip
Carlson exponent margins and the polynomial explicit-formula remainder margin.
The only oscillatory hypothesis left is the far target-amplitude witness for
the actual visible main cluster.
-/
theorem
    unified_parametricPNTUpper_actualWeightedBalancedHeightRemainderCertificate
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta)
    {n : ℕ} {S : Finset ℂ}
    {sigma tau kappa : Fin (n + 1) → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          S (n + 1)}
    (certificate :
      ActualWeightedBalancedHeightOutsideClusterCertificate
        beta S n sigma tau kappa input)
    (remainderCertificate :
      ActualSelectedHeightExplicitFormulaRemainderCertificate
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau)
        (actualSelectedHeightFiniteStripWeightedBalancedHeight
          beta sigma tau))
    (hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau)
          S)
        (targetZeroPowerAmplitude beta)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau certificate.beta_one certificate.sigma_half
      certificate.sigma_one certificate.tau_nonneg
      certificate.endpoint_threshold
  have hmargin :
      1 - beta <
        actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau :=
    hspec.2.2.2.1
  apply
    unified_parametricPNTUpper_clusterExcludedComplementLower
      threshold hhalf hlt
      certificate.actualSignedComplementCertificate
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta)
      (remainderCertificate.targetAmplitudeNegligible hmargin)
      hmain
  intro x
  exact
    relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
      (actualSelectedHeightFiniteStripWeightedBalancedHeight
        beta sigma tau)
      S x

/-- A uniform polynomial-height remainder certificate specializes
definitionally to the slope-weighted balanced height. -/
def
    ActualPolynomialExplicitFormulaRemainderCertificate.weightedBalancedHeightCertificate
    {beta : ℝ} {n : ℕ} {sigma tau : Fin (n + 1) → ℝ}
    (certificate :
      ActualPolynomialExplicitFormulaRemainderCertificate
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau)) :
    ActualSelectedHeightExplicitFormulaRemainderCertificate
      (actualSelectedHeightFiniteStripWeightedBalancedExponent
        beta sigma tau)
      (actualSelectedHeightFiniteStripWeightedBalancedHeight
        beta sigma tau) where
  constant := certificate.constant
  constant_nonneg := certificate.constant_nonneg
  eventually_bound := by
    simpa [actualSelectedHeightFiniteStripWeightedBalancedHeight] using
      certificate.eventually_bound

/--
Weighted unified transfer from the standard uniform polynomial-height
explicit-formula remainder certificate.

The selected-height specialization and the strict target-amplitude exponent
margin are both automatic.  The remaining `hmain` input is exactly the
independent finite-cluster anti-cancellation problem.
-/
theorem
    unified_parametricPNTUpper_actualWeightedBalancedHeightPolynomialRemainderCertificate
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta : ℝ} (hbeta : 0 < beta)
    {n : ℕ} {S : Finset ℂ}
    {sigma tau kappa : Fin (n + 1) → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau x)
          S (n + 1)}
    (certificate :
      ActualWeightedBalancedHeightOutsideClusterCertificate
        beta S n sigma tau kappa input)
    (remainderCertificate :
      ActualPolynomialExplicitFormulaRemainderCertificate
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau))
    (hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain
          (actualSelectedHeightFiniteStripWeightedBalancedHeight
            beta sigma tau)
          S)
        (targetZeroPowerAmplitude beta)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  exact
    unified_parametricPNTUpper_actualWeightedBalancedHeightRemainderCertificate
      threshold hhalf hlt hbeta certificate
      (remainderCertificate.weightedBalancedHeightCertificate
        (beta := beta) (sigma := sigma) (tau := tau))
      hmain

end PrimeNumberTheorem
