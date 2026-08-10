import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonHybridKernelTail
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonTruncatedSplit

/-!
# Dynamic truncated positive-zero decay

This file combines the static low/high split with the two decay theorems.  It
controls the actual finite positive-zero sum outside a main cluster at the
polynomial truncation height `T(m) = m^alpha`.
-/

namespace PrimeNumberTheorem

open scoped BigOperators Topology
open Filter Complex

noncomputable section

/-- The actual positive-zero finite sum outside `S`, normalized by the target
relative amplitude at a polynomial truncation height. -/
def actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum
    (alpha beta : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset
        (carlsonPolynomialHeight alpha (m : ℝ)) S,
      pntRelativeZeroContribution (m : ℝ) rho‖ /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- Under a fixed-gap low-strip budget and pointwise strict separation in the
Carlson strip, the complete actual positive-zero finite sum outside the main
cluster is negligible at target-amplitude scale. -/
theorem actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum_tendsto_zero
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
    (hlowCover :
      ∀ (x : ℝ),
        ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset
          (carlsonPolynomialHeight alpha x) S,
          rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index < beta) :
    Tendsto
      (actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum
        alpha beta S)
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (actualCarlsonHybridNormalizedKernelMajorant
          sigma beta alpha S input i)
        atTop (nhds 0) :=
    actualCarlsonHybridNormalizedKernelMajorant_tendsto_zero
      S input i hhalf hone hkappa hnorm hreLow
      halpha hepsilon hmargin hreHigh
  refine squeeze_zero'
    (g := actualCarlsonHybridNormalizedKernelMajorant
      sigma beta alpha S input i) ?_ ?_ hmajor
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hm
    unfold actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum
    exact div_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _)
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hm => hm⟩] with m hm
    simpa [actualCarlsonDynamicTruncatedPositiveZeroNormalizedSum,
      actualCarlsonHybridNormalizedKernelMajorant,
      dynamicPositiveOutsideClusterPNTLayerNorm,
      targetZeroPowerAmplitude] using
        truncatedPositiveZeroKernelSum_div_target_le_low_add_CarlsonTail
          (input (m : ℝ)) i (hreLow (m : ℝ))
          (hlowCover (m : ℝ)) hhalf hone hreHigh hm

end

end PrimeNumberTheorem
