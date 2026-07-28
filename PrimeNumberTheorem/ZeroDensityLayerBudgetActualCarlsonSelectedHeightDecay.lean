import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonTruncatedSplit
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonOutsideClusterConjugation
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualRealOrdinateExcludingCluster

/-!
# Carlson decay at a selected dynamic height

The exact polynomial height is not needed for the zero sum.  It is enough that
the selected height tends to infinity and is eventually bounded above by the
polynomial Carlson envelope.  This is the interface needed by good-height
versions of the explicit formula.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Positive-ordinate zeta zeros outside `S`, truncated at a selected height
`H`, and normalized by the target zero amplitude. -/
noncomputable def actualCarlsonSelectedHeightPositiveZeroNormalizedSum
    (H : ℝ → ℝ) (beta : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H (m : ℝ)) S,
      pntRelativeZeroContribution (m : ℝ) rho‖ /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- The complete zeta-zero sum outside `S`, truncated at a selected height
`H`, and normalized by the target zero amplitude. -/
noncomputable def actualCarlsonSelectedHeightFullZeroNormalizedSum
    (H : ℝ → ℝ) (beta : ℝ) (S : Finset ℂ) (m : ℕ) : ℝ :=
  ‖∑ rho ∈ nontrivialZerosOutsideClusterFinset (H (m : ℝ)) S,
      pntRelativeZeroContribution (m : ℝ) rho‖ /
    targetZeroPowerAmplitude beta (m : ℝ)

/-- A selected-height positive zero sum is target-negligible when its low strip
has a fixed polynomial margin and its Carlson high strip has only a pointwise
strict real-part gap outside the finite main cluster. -/
theorem actualCarlsonSelectedHeightPositiveZeroNormalizedSum_tendsto_zero
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha kappa epsilon : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hHle :
      ∀ᶠ x : ℝ in atTop, H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hreLow : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ (x : ℝ),
        ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
          rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta) :
    Tendsto
      (actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S)
      atTop (𝓝 0) := by
  have hlowReal :=
    actualHybridOutsideClusterLowLayer_selectedHeight_targetAmplitudeNegligible
      input i hHle hHtop hkappa hnorm hreLow halpha hepsilon hmargin
  have hlow :
      Tendsto
        (fun m : ℕ =>
          dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ))
        atTop (𝓝 0) := by
    have hlowNat := TargetAmplitudeNegligible.naturalPoint hlowReal
    simpa [NaturalPointTargetAmplitudeNegligible,
      dynamicPositiveOutsideClusterPNTLayerNorm, abs_of_nonneg] using hlowNat
  have hhigh :
      Tendsto
        (actualCarlsonOutsideClusterNormalizedKernelTail
          (sigma := sigma) beta S)
        atTop (𝓝 0) :=
    actualCarlsonOutsideClusterNormalizedKernelTail_tendsto_zero
      S hhalf hone hreHigh
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          dynamicPositiveOutsideClusterPNTLayerNorm H S input i (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) +
            actualCarlsonOutsideClusterNormalizedKernelTail
              (sigma := sigma) beta S m)
        atTop (𝓝 0) := by
    simpa using hlow.add hhigh
  apply squeeze_zero'
  · have hamp :=
      eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta)
    filter_upwards [hamp] with m hm
    exact div_nonneg (norm_nonneg _) hm.le
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hbound :=
      truncatedPositiveZeroKernelSum_div_target_le_low_add_CarlsonTail
        (input (m : ℝ)) i (hreLow (m : ℝ)) (hlowCover (m : ℝ))
        hhalf hone hreHigh hm
    simpa [
      actualCarlsonSelectedHeightPositiveZeroNormalizedSum,
      dynamicPositiveOutsideClusterPNTLayerNorm,
      targetZeroPowerAmplitude] using hbound
  · exact hmajor

/-- The complete selected-height zero residual is target-negligible.  Negative
ordinates are transferred by conjugation and real ordinates retain their
separate concrete decay hypothesis. -/
theorem actualCarlsonSelectedHeightFullZeroNormalizedSum_tendsto_zero
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha kappa epsilon : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hHle :
      ∀ᶠ x : ℝ in atTop, H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hreLow : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ (x : ℝ),
        ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
          rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    Tendsto
      (actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S)
      atTop (𝓝 0) := by
  have hpositive :=
    actualCarlsonSelectedHeightPositiveZeroNormalizedSum_tendsto_zero
      input i hHle hHtop hhalf hone hkappa hnorm hreLow hlowCover
      halpha hepsilon hmargin hreHigh
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hHtop.eventually (eventually_ge_atTop (0 : ℝ))
  have hrealReal :=
    dynamicRealOrdinateOutsideClusterPNTZeroTailNorm_targetAmplitudeNegligible
      H S beta hHnonneg hreReal
  have hreal :
      Tendsto
        (fun m : ℕ =>
          dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ))
        atTop (𝓝 0) := by
    have hrealNat := TargetAmplitudeNegligible.naturalPoint hrealReal
    simpa [NaturalPointTargetAmplitudeNegligible,
      dynamicRealOrdinateOutsideClusterPNTZeroTailNorm, abs_of_nonneg] using
      hrealNat
  have hmajor :
      Tendsto
        (fun m : ℕ =>
          2 * actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m +
            dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ))
        atTop (𝓝 0) := by
    convert (hpositive.const_mul 2).add hreal using 1 <;> norm_num
  apply squeeze_zero'
  · have hamp :=
      eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta)
    filter_upwards [hamp] with m hm
    exact div_nonneg (norm_nonneg _) hm.le
  · have hamp :=
      eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta)
    filter_upwards [eventually_gt_atTop (0 : ℕ), hamp] with m hm hAmplitude
    have hmx : 0 < (m : ℝ) := by exact_mod_cast hm
    have hzero :=
      norm_fullOutsideClusterZeroSum_le_two_mul_positive_add_real
        (T := H (m : ℝ)) (x := (m : ℝ)) hmx S hS
    calc
      actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m
          ≤
            (2 *
                  ‖∑ rho ∈
                      positiveNontrivialZerosOutsideClusterFinset
                        (H (m : ℝ)) S,
                      pntRelativeZeroContribution (m : ℝ) rho‖ +
                ‖∑ rho ∈
                    realOrdinateNontrivialZerosOutsideClusterFinset
                      (H (m : ℝ)) S,
                    pntRelativeZeroContribution (m : ℝ) rho‖) /
              targetZeroPowerAmplitude beta (m : ℝ) := by
                exact (div_le_div_iff_of_pos_right hAmplitude).2 hzero
      _ =
          2 * actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m +
            dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) := by
              simp only [
                actualCarlsonSelectedHeightPositiveZeroNormalizedSum,
                dynamicRealOrdinateOutsideClusterPNTZeroTailNorm]
              ring
  · exact hmajor

end PrimeNumberTheorem
