import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualLowLayerDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterKernelTail

/-!
# Hybrid actual-kernel target-amplitude decay

This file combines two already concrete estimates:

* a dynamic finite low-strip layer of actual zeta kernels;
* the infinite Carlson-summable high-strip kernel tail outside a finite cluster.

The conclusion is a decay theorem for their sum after division by the target
relative amplitude.  This module deliberately calls the sum a majorant: a
separate coverage theorem is still needed before identifying it with every
term in a truncated explicit-formula residual.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

/-- Hybrid normalized majorant consisting of one dynamic low layer and the
complete indexed Carlson high-strip tail. -/
def actualCarlsonHybridNormalizedKernelMajorant
    {n : ℕ} (sigma beta alpha : ℝ) (S : Finset ℂ)
    (input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (carlsonPolynomialHeight alpha x) S n)
    (i : Fin n) (m : ℕ) : ℝ :=
  |dynamicPositiveOutsideClusterPNTLayerNorm
      (carlsonPolynomialHeight alpha) S input i (m : ℝ)| /
      targetZeroPowerAmplitude beta (m : ℝ) +
    actualCarlsonOutsideClusterNormalizedKernelTail
      (sigma := sigma) beta S m

/-- A fixed-gap low strip and a pointwise-gap Carlson high strip jointly give
target-amplitude decay. -/
theorem actualCarlsonHybridNormalizedKernelMajorant_tendsto_zero
    {n : ℕ} {sigma beta alpha kappa epsilon : ℝ}
    (S : Finset ℂ)
    (input : (x : ℝ) →
      PositiveZeroOutsideClusterBucketInput
        (carlsonPolynomialHeight alpha x) S n)
    (i : Fin n)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hreLow : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, rho.re ≤ sigma)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta) :
    Tendsto
      (actualCarlsonHybridNormalizedKernelMajorant
        sigma beta alpha S input i)
      atTop (nhds 0) := by
  have hlowReal :=
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_of_hybrid
      input i hkappa hnorm hreLow halpha hepsilon hmargin
  have hlowNat :
      Tendsto
        (fun m : ℕ =>
          |dynamicPositiveOutsideClusterPNTLayerNorm
              (carlsonPolynomialHeight alpha) S input i (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      hlowReal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hhigh :=
    actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_zero
      S hhalf hone hreHigh
  simpa [actualCarlsonHybridNormalizedKernelMajorant] using hlowNat.add hhigh

end

end PrimeNumberTheorem
