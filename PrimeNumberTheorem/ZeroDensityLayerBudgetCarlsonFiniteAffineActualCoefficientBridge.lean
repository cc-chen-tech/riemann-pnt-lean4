import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualStripTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonFiniteAffineLogThresholdDecay

/-!
# Actual Carlson coefficients for the finite affine logarithmic majorant

Carlson's zero-density theorem is an `IsBigO` statement, so its multiplicative
constant is not visible in the exponent optimizer.  This module exposes those
constants as a finite coefficient certificate and carries them through the
actual zeta-kernel estimate.

For each strip, the certificate bounds the actual multiplicity-weighted zero
count by a fixed nonnegative coefficient times the polynomial Carlson count
budget.  The denominator guard contributes `kappa i` inverse, while composing
the fourth logarithmic power with `x ^ alpha` contributes `alpha ^ 4`.

The resulting actual normalized layer-norm sum is eventually bounded by an
endpoint coefficient majorant, and that majorant is proved equal to the
finite affine fourth-logarithmic-power majorant.  This is the coefficient
bridge needed before adjoining the explicit-formula contour term.
-/

noncomputable section

namespace PrimeNumberTheorem

open Filter
open scoped BigOperators

/-- Fixed Carlson `BigO` coefficients for a finite strip family at a dynamic
height, measured against the direct polynomial count budgets. -/
structure CarlsonFiniteStripCountCoefficientCertificate
    {n : ℕ} (T : ℝ → ℝ)
    (sigma : Fin (n + 1) → ℝ)
    (alpha : ℝ) where
  coeff : Fin (n + 1) → ℝ
  coeff_nonneg : ∀ i, 0 ≤ coeff i
  count_eventually_le :
    ∀ i,
      ∀ᶠ x : ℝ in atTop,
        dynamicCarlsonLayerCount (sigma i) T x ≤
          coeff i * carlsonPolynomialCountBudget (sigma i) alpha x

/-- Carlson's proved polynomial-height `BigO` theorem supplies a finite
nonnegative count-coefficient certificate. -/
theorem
    nonempty_carlsonPolynomialFiniteStripCountCoefficientCertificate
    {n : ℕ} {alpha : ℝ}
    (sigma : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (halpha : 0 < alpha) :
    Nonempty
      (CarlsonFiniteStripCountCoefficientCertificate
        (carlsonPolynomialHeight alpha) sigma alpha) := by
  classical
  have hwitness :
      ∀ i,
        ∃ C : ℝ, 0 ≤ C ∧
          Asymptotics.IsBigOWith C atTop
            (fun x =>
              (ZeroDensity.zeroDensityCount
                (sigma i) (carlsonPolynomialHeight alpha x) : ℝ))
            (carlsonPolynomialCountBudget (sigma i) alpha) := by
    intro i
    exact
      (carlson_zeroDensity_polynomialHeight_countBudget_isBigO
        (hsigma i) (hsigmaOne i) halpha).exists_nonneg
  choose C hC hbigO using hwitness
  refine ⟨{
    coeff := C
    coeff_nonneg := hC
    count_eventually_le := ?_
  }⟩
  intro i
  filter_upwards [(hbigO i).bound,
      eventually_ge_atTop (0 : ℝ)] with x hx hx0
  have hbudget :
      0 ≤ carlsonPolynomialCountBudget (sigma i) alpha x := by
    unfold carlsonPolynomialCountBudget
    positivity
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg
      (ZeroDensity.zeroDensityCount
        (sigma i) (carlsonPolynomialHeight alpha x)))] at hx
  rw [Real.norm_of_nonneg hbudget] at hx
  simpa [dynamicCarlsonLayerCount] using hx

/-- Complete coefficient of one actual strip after polynomial-height
composition and the denominator guard. -/
def actualCarlsonFiniteAffineStripCoeff
    {n : ℕ} {T : ℝ → ℝ}
    {sigma : Fin (n + 1) → ℝ} {alpha : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    (kappa : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  certificate.coeff i * alpha ^ (4 : ℕ) * (kappa i)⁻¹

/-- The actual strip coefficients are nonnegative under positive denominator
guards. -/
theorem actualCarlsonFiniteAffineStripCoeff_nonneg
    {n : ℕ} {T : ℝ → ℝ}
    {sigma : Fin (n + 1) → ℝ} {alpha : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    {kappa : Fin (n + 1) → ℝ}
    (hkappa : ∀ i, 0 < kappa i) :
    ∀ i, 0 ≤ actualCarlsonFiniteAffineStripCoeff certificate kappa i := by
  intro i
  unfold actualCarlsonFiniteAffineStripCoeff
  have halpha : 0 ≤ alpha ^ (4 : ℕ) := by positivity
  exact mul_nonneg
    (mul_nonneg (certificate.coeff_nonneg i) halpha)
    (inv_nonneg.mpr (hkappa i).le)

/-- Sum of the actual positive-height layer norms, with each layer normalized
by the target-zero power amplitude. -/
def actualCarlsonFiniteStripNormalizedLayerNormSum
    {n : ℕ} (T : ℝ → ℝ)
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) (n + 1))
    (beta x : ℝ) : ℝ :=
  ∑ i,
    dynamicPositivePNTLayerNorm T input i x /
      targetZeroPowerAmplitude beta x

/-- Endpoint-aware coefficient majorant corresponding to the actual Carlson
count constants and denominator guards. -/
def actualCarlsonFiniteStripEndpointCoefficientLogMajorant
    {n : ℕ} {T : ℝ → ℝ}
    {sigma : Fin (n + 1) → ℝ} {alpha : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    (beta : ℝ)
    (tau kappa : Fin (n + 1) → ℝ)
    (x : ℝ) : ℝ :=
  ∑ i,
    actualCarlsonFiniteAffineStripCoeff certificate kappa i *
      carlsonStripEndpointNormalizedLogMajorant
        beta (sigma i) (tau i) alpha x

/-- The endpoint coefficient majorant is exactly the generic finite affine
fourth-logarithmic-power majorant with zero contour coefficient. -/
theorem
    actualCarlsonFiniteStripEndpointCoefficientLogMajorant_eq_finiteAffine
    {n : ℕ} {T : ℝ → ℝ}
    {sigma : Fin (n + 1) → ℝ} {alpha : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    (beta : ℝ)
    (tau kappa : Fin (n + 1) → ℝ) :
    actualCarlsonFiniteStripEndpointCoefficientLogMajorant
        certificate beta tau kappa =
      finiteAffineDensityLogPowerMajorant
        0
        (actualCarlsonFiniteAffineStripCoeff certificate kappa)
        (carlsonAffineDensityFloor beta)
        alpha
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma) := by
  funext x
  unfold actualCarlsonFiniteStripEndpointCoefficientLogMajorant
    finiteAffineDensityLogPowerMajorant
  simp only [zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro i _hi
  have hexponent :
      targetAmplitudeStripEndpointExponent beta (tau i)
          (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) =
        carlsonAffineDensitySlope sigma i * alpha -
          carlsonAffineDensityCeiling beta tau i := by
    unfold targetAmplitudeStripEndpointExponent
      carlsonClassicalPolynomialDensityExponent
      carlsonPolynomialHeightDensityExponent
      carlsonAffineDensitySlope
      actualSelectedHeightStripCarlsonSlope
      carlsonAffineDensityCeiling
    ring
  unfold carlsonStripEndpointNormalizedLogMajorant
  rw [hexponent]
  ring

/-- A count-coefficient certificate and the actual strip kernel bounds place
the genuine normalized layer-norm sum below the endpoint coefficient
majorant eventually. -/
theorem
    eventually_actualCarlsonFiniteStripNormalizedLayerNormSum_le_majorant
    {n : ℕ} {T : ℝ → ℝ}
    {sigma : Fin (n + 1) → ℝ} {alpha beta : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) (n + 1))
    (tau kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    ∀ᶠ x : ℝ in atTop,
      actualCarlsonFiniteStripNormalizedLayerNormSum
          T input beta x ≤
        actualCarlsonFiniteStripEndpointCoefficientLogMajorant
          certificate beta tau kappa x := by
  have hcounts :
      ∀ᶠ x : ℝ in atTop,
        ∀ i ∈ Finset.univ,
          dynamicCarlsonLayerCount (sigma i) T x ≤
            certificate.coeff i *
              carlsonPolynomialCountBudget (sigma i) alpha x :=
    Finset.univ.eventually_all.mpr fun i _ =>
      certificate.count_eventually_le i
  have hbudgetFormula :
      ∀ᶠ x : ℝ in atTop,
        ∀ i ∈ Finset.univ,
          carlsonPolynomialCountBudget (sigma i) alpha x *
                stripEndpointRelativeKernelBudget (kappa i) (tau i) x /
              targetZeroPowerAmplitude beta x =
            (alpha ^ (4 : ℕ) * (kappa i)⁻¹) *
              carlsonStripEndpointNormalizedLogMajorant
                beta (sigma i) (tau i) alpha x :=
    Finset.univ.eventually_all.mpr fun i _ =>
      eventually_carlsonCountBudget_mul_stripEndpoint_div_targetAmplitude
        beta (sigma i) (tau i) alpha (kappa i)
  filter_upwards [hcounts, hbudgetFormula,
      eventually_ge_atTop (1 : ℝ)] with x hcount hformula hx
  unfold actualCarlsonFiniteStripNormalizedLayerNormSum
    actualCarlsonFiniteStripEndpointCoefficientLogMajorant
  apply Finset.sum_le_sum
  intro i _hi
  have hlayer :=
    dynamicPositivePNTLayerNorm_le_carlson_mul_stripEndpoint
      input i (sigma i) (tau i) (kappa i)
      (hfixedSigma i) (hkappa i) (hnorm i) (hre i) hx
  have hlayerNonneg :
      0 ≤ dynamicPositivePNTLayerNorm T input i x := by
    unfold dynamicPositivePNTLayerNorm
    exact norm_nonneg _
  rw [abs_of_nonneg hlayerNonneg] at hlayer
  have hkernel :
      0 ≤ stripEndpointRelativeKernelBudget (kappa i) (tau i) x :=
    stripEndpointRelativeKernelBudget_nonneg
      (zero_le_one.trans hx) (hkappa i).le
  have hamplitude :
      0 < targetZeroPowerAmplitude beta x := by
    unfold targetZeroPowerAmplitude
    exact Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
  calc
    dynamicPositivePNTLayerNorm T input i x /
          targetZeroPowerAmplitude beta x ≤
        (dynamicCarlsonLayerCount (sigma i) T x *
            stripEndpointRelativeKernelBudget (kappa i) (tau i) x) /
          targetZeroPowerAmplitude beta x :=
      div_le_div_of_nonneg_right hlayer hamplitude.le
    _ ≤
        ((certificate.coeff i *
              carlsonPolynomialCountBudget (sigma i) alpha x) *
            stripEndpointRelativeKernelBudget (kappa i) (tau i) x) /
          targetZeroPowerAmplitude beta x := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (hcount i (Finset.mem_univ i)) hkernel)
        hamplitude.le
    _ =
        certificate.coeff i *
          (carlsonPolynomialCountBudget (sigma i) alpha x *
              stripEndpointRelativeKernelBudget (kappa i) (tau i) x /
            targetZeroPowerAmplitude beta x) := by
      ring
    _ =
        actualCarlsonFiniteAffineStripCoeff certificate kappa i *
          carlsonStripEndpointNormalizedLogMajorant
            beta (sigma i) (tau i) alpha x := by
      rw [hformula i (Finset.mem_univ i)]
      unfold actualCarlsonFiniteAffineStripCoeff
      ring

/-- The genuine normalized layer-norm sum is eventually bounded directly by
the generic finite affine logarithmic majorant. -/
theorem
    eventually_actualCarlsonFiniteStripNormalizedLayerNormSum_le_finiteAffine
    {n : ℕ} {T : ℝ → ℝ}
    {sigma : Fin (n + 1) → ℝ} {alpha beta : ℝ}
    (certificate :
      CarlsonFiniteStripCountCoefficientCertificate T sigma alpha)
    (input : (x : ℝ) → PositiveZeroBucketInput (T x) (n + 1))
    (tau kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x, ∀ rho ∈ (input x).layer i, kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    ∀ᶠ x : ℝ in atTop,
      actualCarlsonFiniteStripNormalizedLayerNormSum
          T input beta x ≤
        finiteAffineDensityLogPowerMajorant
          0
          (actualCarlsonFiniteAffineStripCoeff certificate kappa)
          (carlsonAffineDensityFloor beta)
          alpha
          (carlsonAffineDensityCeiling beta tau)
          (carlsonAffineDensitySlope sigma)
          x := by
  simpa only
    [actualCarlsonFiniteStripEndpointCoefficientLogMajorant_eq_finiteAffine]
    using
      eventually_actualCarlsonFiniteStripNormalizedLayerNormSum_le_majorant
        certificate input tau kappa hfixedSigma hkappa hnorm hre

end PrimeNumberTheorem
