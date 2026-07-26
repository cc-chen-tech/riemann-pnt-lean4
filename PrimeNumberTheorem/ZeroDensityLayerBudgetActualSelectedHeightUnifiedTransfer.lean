import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStrips
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualClusterComplementUnifiedTransfer

/-!
# Unified actual explicit-formula transfer at one selected height

The selected good height `H(x)` now enters every height-dependent term:

* the visible finite main cluster;
* the actual signed zeta complement;
* the finite-strip Carlson count;
* the actual explicit-formula remainder.

The analytic construction of a uniform remainder certificate is intentionally
separate.  This module proves the exact exponent arithmetic and assembles the
certificate with the selected-height Carlson complement and the actual
finite-height explicit formula.
-/

namespace PrimeNumberTheorem

open Filter

/-- Uniform polynomial-rate bound for the actual explicit-formula remainder
evaluated at an arbitrary selected height function. -/
structure ActualSelectedHeightExplicitFormulaRemainderCertificate
    (alpha : ℝ) (H : ℝ → ℝ) : Type where
  constant : ℝ
  constant_nonneg : 0 ≤ constant
  eventually_bound :
    ∀ᶠ x : ℝ in atTop,
      |actualPNTExplicitFormulaRelativeRemainder H x| ≤
        constant * x ^ (-alpha) * (1 + Real.log x) ^ 2

/-- A selected-height uniform remainder certificate is target-negligible
under the sharp polynomial exponent condition `1 - beta < alpha`. -/
theorem
    ActualSelectedHeightExplicitFormulaRemainderCertificate.targetAmplitudeNegligible
    {beta alpha : ℝ} {H : ℝ → ℝ}
    (certificate :
      ActualSelectedHeightExplicitFormulaRemainderCertificate alpha H)
    (hmargin : 1 - beta < alpha) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (actualPNTExplicitFormulaRelativeRemainder H) := by
  let bound : ℝ → ℝ := fun x =>
    certificate.constant * x ^ (-alpha) * (1 + Real.log x) ^ 2
  have hboundNegligible :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta) bound := by
    unfold TargetAmplitudeNegligible
    have htarget :=
      tendsto_actualPolynomialRemainderTargetMajorant
        certificate.constant_nonneg hmargin
    apply htarget.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hboundNonneg : 0 ≤ bound x := by
      dsimp [bound]
      exact mul_nonneg
        (mul_nonneg certificate.constant_nonneg
          (Real.rpow_nonneg hx.le (-alpha)))
        (sq_nonneg (1 + Real.log x))
    rw [abs_of_nonneg hboundNonneg]
    dsimp [bound, actualPolynomialRemainderTargetMajorant,
      targetZeroPowerAmplitude]
    rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
    have hpower :
        x ^ (-alpha) * x ^ (-(beta - 1)) =
          x ^ (1 - beta - alpha) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    rw [← hpower]
    ring
  exact
    TargetAmplitudeNegligible.of_eventually_abs_le
      (targetZeroPowerAmplitude_eventually_pos beta)
      hboundNegligible certificate.eventually_bound

/--
Complete selected-height Pintz--Carlson--explicit-formula transfer.

All height-dependent terms use the same selected good height `H`.  The closed
real-axis term is automatic for `beta > 0`; the selected-height remainder
certificate is automatic after the strict exponent margin.  The only
remaining lower-bound input is a far target-amplitude witness for the visible
finite main cluster.
-/
theorem
    unified_parametricPNTUpper_actualSelectedHeightRemainderCertificate
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {beta alpha : ℝ} (hbeta : 0 < beta)
    (hmargin : 1 - beta < alpha)
    {S : Finset ℂ} {n : ℕ} {H : ℝ → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha S n H input)
    (remainderCertificate :
      ActualSelectedHeightExplicitFormulaRemainderCertificate alpha H)
    (hmain :
      HasFarTargetAmplitudeWitness
        (dynamicVisibleClusterPNTMain H S)
        (targetZeroPowerAmplitude beta)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
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
      H S x

end PrimeNumberTheorem
