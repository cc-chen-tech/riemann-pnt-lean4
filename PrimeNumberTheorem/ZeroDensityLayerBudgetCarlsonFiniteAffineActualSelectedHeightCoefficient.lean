import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineActualCoefficientBridge
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineLogThresholdDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightNaturalTransfer

/-!
# Actual Carlson coefficients at the weighted selected good height

The polynomial-height Carlson `O`-constants also control the shorter
uniformly selected good height.  The reason is purely monotone: eventually
the selected height lies below the polynomial ceiling, so every actual
Carlson layer count at the selected height is bounded by the corresponding
polynomial-height count.

This transfers the actual multiplicity-weighted finite-strip norm sum to the
previously optimized affine logarithmic majorant, with the hidden Carlson
constants exposed as a finite nonnegative coefficient family.
-/

namespace PrimeNumberTheorem

open Filter Set
open scoped Topology

/-- The weighted selected good height inherits a finite family of actual
Carlson count coefficients from the polynomial-height estimate. -/
theorem
    nonempty_actualSelectedHeightWeightedBalancedCountCoefficientCertificate
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection) :
    Nonempty
      (CarlsonFiniteStripCountCoefficientCertificate
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)
        sigma
        (actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau)) := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := hspec.2.1
  have hselected :
      ∀ᶠ x : ℝ in atTop,
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x ∈
          Set.Icc
            (actualCarlsonPolynomialGoodHeightBase alpha x)
            (actualCarlsonPolynomialGoodHeightBase alpha x + 1) := by
    simpa [alpha,
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight,
      actualCarlsonPolynomialGoodHeightBase] using
      eventually_selectedUniformGoodHeight_mem halpha selection
  have hheight :
      ∀ᶠ x : ℝ in atTop,
        actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x ≤
          carlsonPolynomialHeight alpha x :=
    eventually_selectedHeight_le_carlsonPolynomialHeight hselected
  rcases
      nonempty_carlsonPolynomialFiniteStripCountCoefficientCertificate
        sigma hsigma hsigmaOne halpha with
    ⟨polynomialCertificate⟩
  refine ⟨
    { coeff := polynomialCertificate.coeff
      coeff_nonneg := polynomialCertificate.coeff_nonneg
      count_eventually_le := ?_ }⟩
  intro i
  filter_upwards
      [hheight, polynomialCertificate.count_eventually_le i] with
      x hxHeight hxCount
  exact
    (dynamicCarlsonLayerCount_mono_height hxHeight).trans hxCount

/-- A canonical actual Carlson coefficient certificate at the weighted
selected good height. -/
noncomputable def
    actualSelectedHeightWeightedBalancedCountCoefficientCertificate
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection) :
    CarlsonFiniteStripCountCoefficientCertificate
      (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
        beta sigma tau selection)
      sigma
      (actualSelectedHeightFiniteStripWeightedBalancedExponent
        beta sigma tau) :=
  Classical.choice
    (nonempty_actualSelectedHeightWeightedBalancedCountCoefficientCertificate
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection)

/-- At the weighted selected good height, the genuine finite-strip norm sum
is eventually bounded by the optimized Carlson affine log-majorant with its
actual finite coefficient family. -/
theorem
    eventually_actualSelectedHeightWeightedBalancedNormalizedLayerNormSum_le
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    let certificate :=
      actualSelectedHeightWeightedBalancedCountCoefficientCertificate
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
    ∀ᶠ x : ℝ in atTop,
      actualCarlsonFiniteStripNormalizedLayerNormSum
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection)
          input beta x ≤
        carlsonFiniteAffineBalancedLogPowerMajorant
          0
          (actualCarlsonFiniteAffineStripCoeff certificate kappa)
          beta sigma tau x := by
  dsimp only
  have hbound :=
    eventually_actualCarlsonFiniteStripNormalizedLayerNormSum_le_finiteAffine
      (beta := beta)
      (actualSelectedHeightWeightedBalancedCountCoefficientCertificate
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection)
      input tau kappa hfixedSigma hkappa hnorm hre
  simpa only
      [carlsonFiniteAffineBalancedLogPowerMajorant_eq_weighted] using
    hbound

/-- Under the Carlson endpoint thresholds, the genuine finite-strip
multiplicity-weighted norm sum at the weighted selected good height is
`o` of the target zero amplitude. -/
theorem
    tendsto_actualSelectedHeightWeightedBalancedNormalizedLayerNormSum_zero
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    Tendsto
      (actualCarlsonFiniteStripNormalizedLayerNormSum
        (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
          beta sigma tau selection)
        input beta)
      atTop (nhds 0) := by
  let certificate :=
    actualSelectedHeightWeightedBalancedCountCoefficientCertificate
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
  have hmajorant :
      Tendsto
        (carlsonFiniteAffineBalancedLogPowerMajorant
          0
          (actualCarlsonFiniteAffineStripCoeff certificate kappa)
          beta sigma tau)
        atTop (nhds 0) :=
    tendsto_carlsonFiniteAffineBalancedLogPowerMajorant_zero_of_threshold
      (by norm_num)
      (actualCarlsonFiniteAffineStripCoeff_nonneg
        certificate hkappa)
      hsigma hsigmaOne hthreshold
  have hlower :
      ∀ᶠ x : ℝ in atTop,
        0 ≤
          actualCarlsonFiniteStripNormalizedLayerNormSum
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            input beta x := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    unfold actualCarlsonFiniteStripNormalizedLayerNormSum
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hx _)
  have hupper :
      ∀ᶠ x : ℝ in atTop,
        actualCarlsonFiniteStripNormalizedLayerNormSum
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            input beta x ≤
          carlsonFiniteAffineBalancedLogPowerMajorant
            0
            (actualCarlsonFiniteAffineStripCoeff certificate kappa)
            beta sigma tau x := by
    simpa [certificate] using
      eventually_actualSelectedHeightWeightedBalancedNormalizedLayerNormSum_le
        sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
        input kappa hfixedSigma hkappa hnorm hre
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hmajorant hlower hupper

end PrimeNumberTheorem
