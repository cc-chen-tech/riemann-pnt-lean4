import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonBoundarySelectedHeightBound
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightPNTTransfer

/-!
# Actual PNT transfer with a Carlson boundary mass

The actual explicit formula retains a non-decaying rightmost boundary layer.
If all outside-cluster high-strip zeros satisfy `Re rho <= beta`, then the
genuine PNT residual is eventually bounded, on the target scale, by twice the
positive-ordinate Carlson boundary mass plus an arbitrarily small loss.

This is a quantitative replacement for target-negligibility when zeros on
`Re rho = beta` remain outside the finite visible cluster.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- Generic selected-height actual-PNT residual bound retaining the exact
Carlson boundary coefficient. -/
theorem eventually_actualCarlsonSelectedHeightPNTClusterResidual_normalized_lt_boundaryCoefficient_add
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha kappa epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hHle :
      ∀ᶠ x : ℝ in atTop, H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hbeta : 0 < beta)
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
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) <
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by
  have hfull :=
    eventually_actualCarlsonSelectedHeightFullZeroNormalizedSum_lt_two_mul_boundaryMass_add
      input i hS hHle hHtop hhalf hone hkappa hnorm hreLow hlowCover
      halpha hepsilon hmargin hreHigh hreReal
      (show 0 < delta / 2 by positivity)
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hclosed :=
    TargetAmplitudeNegligible.naturalPoint
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta)
  have hcontour := remainder.negligible
  have hclosedContour :=
    NaturalPointTargetAmplitudeNegligible.add
      hamplitude hclosed hcontour
  have hclosedContourSmall :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hclosedContour (show 0 < delta / 2 by positivity)
  filter_upwards [hfull, hamplitude, hclosedContourSmall] with
      m hfullM hAmplitude hclosedContourM
  have hclosedContourDiv :
      |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) < delta / 2 := by
    apply (div_lt_iff₀ hAmplitude).2
    simpa [mul_comm] using hclosedContourM
  have hcomplementDiv :
      |dynamicOutsideClusterPNTComplement H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) ≤
        actualCarlsonSelectedHeightFullZeroNormalizedSum H beta S m := by
    have hdominated :=
      abs_dynamicOutsideClusterPNTComplement_le_tailNorm H S (m : ℝ)
    have hdivided :=
      (div_le_div_iff_of_pos_right hAmplitude).2 hdominated
    simpa [
      actualCarlsonSelectedHeightFullZeroNormalizedSum,
      dynamicFullOutsideClusterPNTZeroTailNorm] using hdivided
  have hcomplementLt :
      |dynamicOutsideClusterPNTComplement H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) <
        2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S + delta / 2 :=
    hcomplementDiv.trans_lt hfullM
  rw [relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
    H S (m : ℝ)]
  simp only [add_sub_cancel_left]
  calc
    |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
          dynamicOutsideClusterPNTComplement H S (m : ℝ)| /
          targetZeroPowerAmplitude beta (m : ℝ)
        ≤
          (|actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
                actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| +
              |dynamicOutsideClusterPNTComplement H S (m : ℝ)|) /
            targetZeroPowerAmplitude beta (m : ℝ) := by
              exact
                (div_le_div_iff_of_pos_right hAmplitude).2
                  (abs_add_le _ _)
    _ =
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) +
          |dynamicOutsideClusterPNTComplement H S (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) := by ring
    _ <
        delta / 2 +
          (2 * actualCarlsonOutsideClusterBoundaryMass
            (sigma := sigma) beta S + delta / 2) :=
      add_lt_add hclosedContourDiv hcomplementLt
    _ =
        2 * actualCarlsonOutsideClusterBoundaryMass
          (sigma := sigma) beta S + delta := by ring

/-- Equivalent unnormalized bound used directly by sharp witness-transfer
lemmas. -/
theorem eventually_abs_actualCarlsonSelectedHeightPNTClusterResidual_lt_boundaryCoefficient_mul_targetAmplitude
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha kappa epsilon delta : ℝ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hHle :
      ∀ᶠ x : ℝ in atTop, H x ≤ carlsonPolynomialHeight alpha x)
    (hHtop : Tendsto H atTop atTop)
    (hbeta : 0 < beta)
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
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H S (m : ℝ)| <
        (2 * actualCarlsonOutsideClusterBoundaryMass
              (sigma := sigma) beta S + delta) *
          targetZeroPowerAmplitude beta (m : ℝ) := by
  have hnormalized :=
    eventually_actualCarlsonSelectedHeightPNTClusterResidual_normalized_lt_boundaryCoefficient_add
      input i hS hHle hHtop hbeta hhalf hone hkappa hnorm hreLow
      hlowCover halpha hepsilon hmargin hreHigh hreReal remainder hdelta
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  filter_upwards [hnormalized, hamplitude] with m hnormalizedM hAmplitude
  exact (div_lt_iff₀ hAmplitude).1 hnormalizedM

end PrimeNumberTheorem
