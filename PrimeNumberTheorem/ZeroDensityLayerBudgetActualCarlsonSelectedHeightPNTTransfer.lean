import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonSelectedHeightDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalRemainderDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightClusterApproximation

/-!
# Pointwise-gap Carlson transfer to the actual PNT error

This module inserts the selected-height Carlson zero residual into the concrete
explicit formula.  The output concerns the actual relative Chebyshev error,
not an abstract kernel:

`relativeChebyshevPsi0Error - dynamicVisibleClusterPNTMain`.

The closed real-axis term, contour remainder, and full zeta-zero complement are
all kept as separate verified inputs before the final explicit-formula
identity is applied.
-/

open scoped BigOperators Topology

namespace PrimeNumberTheorem

open Complex Filter

/-- A natural-point full zero-tail norm limit gives target-negligibility of
the signed outside-cluster complement appearing in the explicit formula. -/
theorem actualCarlsonSelectedHeightOutsideClusterComplement_targetNegligible
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
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m => dynamicOutsideClusterPNTComplement H S (m : ℝ)) := by
  have hfull :=
    actualCarlsonSelectedHeightFullZeroNormalizedSum_tendsto_zero
      input i hS hHle hHtop hhalf hone hkappa hnorm hreLow hlowCover
      halpha hepsilon hmargin hreHigh hreReal
  change Tendsto
    (fun m : ℕ =>
      ‖∑ rho ∈ nontrivialZerosOutsideClusterFinset (H (m : ℝ)) S,
          pntRelativeZeroContribution (m : ℝ) rho‖ /
        targetZeroPowerAmplitude beta (m : ℝ))
    atTop (nhds 0) at hfull
  have hfullNegligible :
      NaturalPointTargetAmplitudeNegligible
        (fun m => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m =>
          dynamicFullOutsideClusterPNTZeroTailNorm H S (m : ℝ)) := by
    rw [NaturalPointTargetAmplitudeNegligible]
    simpa only [dynamicFullOutsideClusterPNTZeroTailNorm,
      abs_of_nonneg (norm_nonneg _)] using hfull
  exact
    NaturalPointTargetAmplitudeNegligible.of_eventually_abs_le
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hfullNegligible
      (Eventually.of_forall fun m =>
        abs_dynamicOutsideClusterPNTComplement_le_tailNorm H S (m : ℝ))

/-- Generic selected-height pointwise-gap transfer to the actual PNT error.
The contour contribution is supplied by the concrete selected-height
remainder certificate. -/
theorem actualCarlsonSelectedHeightPNTClusterResidual_targetNegligible
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {sigma beta alpha kappa epsilon : ℝ}
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
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta)
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H S (m : ℝ)) := by
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hclosed :=
    TargetAmplitudeNegligible.naturalPoint
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta)
  have hcontour := remainder.negligible
  have hcomplement :=
    actualCarlsonSelectedHeightOutsideClusterComplement_targetNegligible
      input i hS hHle hHtop hhalf hone hkappa hnorm hreLow hlowCover
      halpha hepsilon hmargin hreHigh hreReal
  have hthree :=
    NaturalPointTargetAmplitudeNegligible.add hamplitude
      (NaturalPointTargetAmplitudeNegligible.add
        hamplitude hclosed hcontour)
      hcomplement
  rw [NaturalPointTargetAmplitudeNegligible] at hthree ⊢
  apply hthree.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals]
  congr 2 <;> ring

/-- Concrete good-height version.  The selected height lies below `x^alpha`,
tends to infinity, and carries the verified explicit-formula remainder
certificate. -/
theorem selectedUniformGoodHeightActualCarlsonPNTClusterResidual_targetNegligible
    {n : ℕ} {S : Finset ℂ}
    {sigma beta alpha kappa epsilon : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (selectedUniformGoodHeight alpha selection x) S n)
    (i : Fin n)
    (hS : ∀ rho : ℂ, rho ∈ S ↔ (starRingEnd ℂ) rho ∈ S)
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hkappa : 0 < kappa)
    (hnorm : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hreLow : ∀ (x : ℝ), ∀ rho ∈ (input x).layer i, rho.re ≤ sigma)
    (hlowCover :
      ∀ (x : ℝ),
        ∀ rho ∈
            positiveNontrivialZerosOutsideClusterFinset
              (selectedUniformGoodHeight alpha selection x) S,
          rho.re ≤ sigma → (input x).bucket rho = i)
    (halpha : 0 < alpha)
    (halphaOne : alpha ≤ 1)
    (hcontourMargin : 1 - beta < alpha)
    (hepsilon : 0 < epsilon)
    (hlowMargin : sigma - beta + alpha + epsilon < 0)
    (hreHigh :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZero index ∉ S →
          actualCarlsonPositiveZeroRealPart index < beta)
    (hreReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (selectedUniformGoodHeight alpha selection) S (m : ℝ)) := by
  have hinterval := eventually_selectedUniformGoodHeight_mem halpha selection
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        selectedUniformGoodHeight alpha selection x ≤
          carlsonPolynomialHeight alpha x := by
    filter_upwards [hinterval] with x hx
    exact hx.2
  have hbase :
      Tendsto (fun x : ℝ => x ^ alpha - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ)
        (tendsto_rpow_atTop halpha))
  have hHtop :
      Tendsto (selectedUniformGoodHeight alpha selection) atTop atTop := by
    apply tendsto_atTop_mono' atTop
      (hinterval.mono fun x hx => hx.1) hbase
  exact
    actualCarlsonSelectedHeightPNTClusterResidual_targetNegligible
      input i hS hHle hHtop hbeta hhalf hone hkappa hnorm hreLow
      hlowCover halpha hepsilon hlowMargin hreHigh hreReal
      (selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hbeta halpha halphaOne hcontourMargin selection)

end PrimeNumberTheorem
