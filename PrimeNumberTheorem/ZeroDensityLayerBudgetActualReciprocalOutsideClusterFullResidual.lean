import PrimeNumberTheorem.ZeroDensityLayerBudgetActualReciprocalOutsideClusterBoundaryMass
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundaryPNTTransfer

/-!
# Reciprocal fixed-cluster full zero sum and PNT residual

The reciprocal positive-zero boundary bound is doubled by conjugation, the
strictly-left real-ordinate tail is absorbed, and the actual explicit formula
adds the closed-axis and contour terms.  The resulting fixed-cluster residual
retains the exact Carlson boundary coefficient with no polynomial-height term
in the low-layer margin.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- The complete selected-height zero sum outside a conjugation-invariant
fixed cluster is eventually bounded by twice the Carlson boundary mass plus
any positive loss under the reciprocal margin. -/
theorem
    eventually_actualCarlsonSelectedHeightFullZeroNormalizedSum_lt_two_mul_boundaryMass_add_reciprocal
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hreLow : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ sigma)
    (hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m <
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hpositive :=
    eventually_actualCarlsonSelectedHeightPositiveZeroNormalizedSum_lt_boundaryMass_add_reciprocal
      input i hHle hHtop hhalf hone hreLow hlowCover halpha hepsilon
      hmargin hreHigh (show 0 < delta / 4 by positivity)
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
        atTop (nhds 0) := by
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
          ≤ (2 *
                ‖∑ rho ∈ positiveNontrivialZerosOutsideClusterFinset
                    (H (m : ℝ)) S,
                    pntRelativeZeroContribution (m : ℝ) rho‖ +
              ‖∑ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset
                  (H (m : ℝ)) S,
                  pntRelativeZeroContribution (m : ℝ) rho‖) /
                targetZeroPowerAmplitude beta (m : ℝ) := by
            exact (div_le_div_iff_of_pos_right hAmplitude).2 hzero
      _ = 2 * actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m +
            dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) := by
          simp only [actualCarlsonSelectedHeightPositiveZeroNormalizedSum,
            dynamicRealOrdinateOutsideClusterPNTZeroTailNorm]
          ring
  calc
    actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m
        ≤ 2 * actualCarlsonSelectedHeightPositiveZeroNormalizedSum H beta S m +
            dynamicRealOrdinateOutsideClusterPNTZeroTailNorm H S (m : ℝ) /
              targetZeroPowerAmplitude beta (m : ℝ) := hfull
    _ < 2 * (actualCarlsonOutsideClusterBoundaryMass
              (sigma := sigma) beta S + delta / 4) + delta / 2 := by
          exact add_lt_add
            (mul_lt_mul_of_pos_left hpositiveM (by norm_num)) hrealM
    _ = 2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by ring

/-- Generic actual-PNT residual bound for a fixed cluster under the reciprocal
low-layer margin. -/
theorem
    eventually_actualCarlsonSelectedHeightPNTClusterResidual_normalized_lt_boundaryCoefficient_add_reciprocal
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hreLow : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ sigma)
    (hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta)
    (remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) <
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hfull :=
    eventually_actualCarlsonSelectedHeightFullZeroNormalizedSum_lt_two_mul_boundaryMass_add_reciprocal
      input i hS hHle hHtop hhalf hone hreLow hlowCover halpha hepsilon
      hmargin hreHigh hreReal (show 0 < delta / 2 by positivity)
  have hamplitude := eventually_naturalPoint_pos_of_eventually_pos
    (targetZeroPowerAmplitude_eventually_pos beta)
  have hclosed := TargetAmplitudeNegligible.naturalPoint
    (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta)
  have hclosedContour := NaturalPointTargetAmplitudeNegligible.add
    hamplitude hclosed remainder.negligible
  have hsmall := eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
    hamplitude hclosedContour (show 0 < delta / 2 by positivity)
  filter_upwards [hfull, hamplitude, hsmall] with m hfullM hAmp hsmallM
  have hsmallDiv :
      |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) < delta / 2 := by
    apply (div_lt_iff₀ hAmp).2
    simpa [mul_comm] using hsmallM
  have hcomplementDiv :
      |dynamicOutsideClusterPNTComplement H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) ≤
        actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m := by
    exact (div_le_div_iff_of_pos_right hAmp).2
      (abs_dynamicOutsideClusterPNTComplement_le_tailNorm H S (m : ℝ))
  rw [relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
    H S (m : ℝ)]
  simp only [add_sub_cancel_left]
  calc
    |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
        actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
        dynamicOutsideClusterPNTComplement H S (m : ℝ)| /
          targetZeroPowerAmplitude beta (m : ℝ)
      ≤ (|actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| +
            |dynamicOutsideClusterPNTComplement H S (m : ℝ)|) /
          targetZeroPowerAmplitude beta (m : ℝ) := by
        exact (div_le_div_iff_of_pos_right hAmp).2 (abs_add_le _ _)
    _ = |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) +
          |dynamicOutsideClusterPNTComplement H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) := by ring
    _ < delta / 2 +
          (2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S + delta / 2) := by
        exact add_lt_add hsmallDiv (hcomplementDiv.trans_lt hfullM)
    _ = 2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by ring

/-- Unnormalized residual form used by sharp and sign-alternative witness
transfers. -/
theorem
    eventually_abs_actualCarlsonSelectedHeightPNTClusterResidual_lt_boundaryCoefficient_mul_targetAmplitude_reciprocal
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hHle : ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma) (hone : sigma < 1)
    (hreLow : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ sigma)
    (hlowCover : ∀ x,
      ∀ rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S,
        rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + epsilon < 0)
    (hreHigh : ∀ index : ActualCarlsonPositiveZeroIndex sigma,
      actualCarlsonPositiveZero index ∉ S →
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hreReal : ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
      rho.re < beta)
    (remainder : ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H S (m : ℝ)| <
        (2 * actualCarlsonOutsideClusterBoundaryMass
              (sigma := sigma) beta S + delta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  have hnormalized :=
    eventually_actualCarlsonSelectedHeightPNTClusterResidual_normalized_lt_boundaryCoefficient_add_reciprocal
      input i hS hHle hHtop hbeta hhalf hone hreLow hlowCover halpha
      hepsilon hmargin hreHigh hreReal remainder hdelta
  have hamplitude := eventually_naturalPoint_pos_of_eventually_pos
    (targetZeroPowerAmplitude_eventually_pos beta)
  filter_upwards [hnormalized, hamplitude] with m hm hAmp
  exact (div_lt_iff₀ hAmp).1 hm

end PrimeNumberTheorem
