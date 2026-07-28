import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryTruncatedSplit
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightDecay

/-!
# Selected-height Carlson bounds with a boundary mass

When outside-cluster high-strip zeros satisfy `Re rho <= beta`, the selected
positive-zero sum is no longer necessarily target-negligible.  Its normalized
size is eventually bounded by the explicit Carlson boundary mass, up to an
arbitrarily small loss.  Conjugation doubles that boundary coefficient for
the complete nonreal zero sum.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- The selected positive-zero sum is eventually bounded by the Carlson
boundary mass plus any positive loss. -/
theorem eventually_actualCarlsonSelectedHeightPositiveZeroNormalizedSum_lt_boundaryMass_add
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha kappa epsilon delta : ℝ}
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
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m <
        actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
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
        (𝓝 (actualCarlsonOutsideClusterBoundaryMass
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
    simpa [
      actualCarlsonSelectedHeightPositiveZeroNormalizedSum,
      dynamicPositiveOutsideClusterPNTLayerNorm,
      targetZeroPowerAmplitude] using hbound
  exact hbound'.trans_lt hmajorM

/-- The complete selected-height zero sum outside `S` is eventually bounded
by twice the positive-ordinate boundary mass plus any positive loss. -/
theorem eventually_actualCarlsonSelectedHeightFullZeroNormalizedSum_lt_two_mul_boundaryMass_add
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha kappa epsilon delta : ℝ}
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
          actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m <
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hpositive :=
    eventually_actualCarlsonSelectedHeightPositiveZeroNormalizedSum_lt_boundaryMass_add
      input i hHle hHtop hhalf hone hkappa hnorm hreLow hlowCover
      halpha hepsilon hmargin hreHigh (show 0 < delta / 4 by positivity)
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
  have hrealSmall :
      ∀ᶠ m : ℕ in atTop,
        dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ) < delta / 2 :=
    (tendsto_order.mp hreal).2 _ (show 0 < delta / 2 by positivity)
  have hamp :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  filter_upwards
      [hpositive, hrealSmall, eventually_gt_atTop (0 : ℕ), hamp] with
      m hpositiveM hrealM hm hAmplitude
  have hmx : 0 < (m : ℝ) := by exact_mod_cast hm
  have hzero :=
    norm_fullOutsideClusterZeroSum_le_two_mul_positive_add_real
      (T := H (m : ℝ)) (x := (m : ℝ)) hmx S hS
  have hfull :
      actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m ≤
        2 * actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m +
          dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
            targetZeroPowerAmplitude beta (m : ℝ) := by
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
  calc
    actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m
        ≤
          2 * actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m +
            dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) := hfull
    _ <
        2 *
              (actualCarlsonOutsideClusterBoundaryMass
                (sigma := sigma) beta S + delta / 4) +
            delta / 2 := by
          exact add_lt_add
            (mul_lt_mul_of_pos_left hpositiveM (by norm_num))
            hrealM
    _ =
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by ring

end PrimeNumberTheorem
