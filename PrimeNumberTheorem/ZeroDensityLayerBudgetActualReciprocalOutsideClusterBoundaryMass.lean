import PrimeNumberTheorem.ZeroDensityLayerBudgetActualReciprocalOutsideClusterLowLayer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundarySelectedHeightBound

/-!
# Reciprocal fixed-cluster Carlson boundary mass

The generic reciprocal low layer is combined with the unchanged Carlson high
tail.  The resulting positive-zero sum outside a fixed cluster retains the
exact boundary mass while requiring no polynomial-height term in the decay
margin.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- The selected positive-zero sum outside an arbitrary fixed cluster is
eventually bounded by the Carlson boundary mass plus any positive loss under
the reciprocal margin `sigma - beta + epsilon < 0`. -/
theorem
    eventually_actualCarlsonSelectedHeightPositiveZeroNormalizedSum_lt_boundaryMass_add_reciprocal
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hreLow : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ sigma)
    (hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m <
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hlow :=
    tendsto_dynamicPositiveOutsideClusterPNTLayerNorm_div_targetAmplitude_zero_reciprocal
      input i hHle hHtop halpha hepsilon hmargin hreLow
  have hhigh :=
    actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_boundaryMass
      S hhalf hone hreHigh
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) +
            actualCarlsonOutsideClusterNormalizedKernelTail
              (sigma := sigma) beta S m)
        atTop
        (nhds (actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S)) := by
    simpa using hlow.add hhigh
  have hmajorLt :
      ∀ᶠ m : ℕ in atTop,
        dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) +
            actualCarlsonOutsideClusterNormalizedKernelTail
              (sigma := sigma) beta S m <
          actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S + delta :=
    (tendsto_order.mp hmajor).2 _ (lt_add_of_pos_right _ hdelta)
  filter_upwards [hmajorLt, eventually_ge_atTop (1 : ℕ)] with m hmajorM hm
  have hbound :=
    truncatedPositiveZeroKernelSum_div_target_le_low_add_CarlsonTail_of_le
      (input (m : ℝ)) i (hreLow (m : ℝ)) (hlowCover (m : ℝ))
      hhalf hone hreHigh hm
  have hbound' :
      actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m ≤
        dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) +
            actualCarlsonOutsideClusterNormalizedKernelTail
              (sigma := sigma) beta S m := by
    simpa [actualCarlsonSelectedHeightPositiveZeroNormalizedSum,
      dynamicPositiveOutsideClusterPNTLayerNorm,
      targetZeroPowerAmplitude] using hbound
  exact hbound'.trans_lt hmajorM

end PrimeNumberTheorem
