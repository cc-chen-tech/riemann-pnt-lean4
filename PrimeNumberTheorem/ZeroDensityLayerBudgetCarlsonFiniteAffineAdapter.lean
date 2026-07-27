import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteAffineDensityOptimizer

/-!
# Carlson as an instance of the finite affine density optimizer

For a target exponent `beta` and strip data `(sigma i, tau i)`, the Carlson
physical-margin problem has the affine parameters

* contour floor `1 - beta`;
* strip ceiling `beta - tau i`;
* density slope `4 * sigma i * (1 - sigma i)`.

The general affine optimizer therefore recovers exactly, not merely
asymptotically, the existing weighted balanced Carlson exponent and optimal
physical margin.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- Contour floor in the affine presentation of the Carlson optimizer. -/
def carlsonAffineDensityFloor (beta : ℝ) : ℝ :=
  1 - beta

/-- Strip ceilings in the affine presentation of the Carlson optimizer. -/
def carlsonAffineDensityCeiling
    {n : ℕ} (beta : ℝ) (tau : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => beta - tau i

/-- Strip slopes in the affine presentation of the Carlson optimizer. -/
def carlsonAffineDensitySlope
    {n : ℕ} (sigma : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => actualSelectedHeightStripCarlsonSlope (sigma i)

/-- Each Carlson pairwise balanced margin is exactly the corresponding
general affine balanced margin. -/
theorem carlsonAffineStripBalancedMargin_eq
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    finiteAffineStripBalancedMargin
        (carlsonAffineDensityFloor beta)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma) i =
      actualSelectedHeightStripBalancedPhysicalMargin
        beta (sigma i) (tau i) := by
  rfl

/-- The general affine optimum is definitionally the existing finite-strip
Carlson optimal physical margin. -/
theorem carlsonAffineOptimalMargin_eq
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) :
    finiteAffineOptimalMargin
        (carlsonAffineDensityFloor beta)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma) =
      actualSelectedHeightFiniteStripOptimalPhysicalMargin
        beta sigma tau := by
  rfl

/-- The general affine balanced exponent is exactly the existing weighted
balanced Carlson height exponent. -/
theorem carlsonAffineBalancedExponent_eq
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) :
    finiteAffineBalancedExponent
        (carlsonAffineDensityFloor beta)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma) =
      actualSelectedHeightFiniteStripWeightedBalancedExponent
        beta sigma tau := by
  rfl

/-- Carlson physical-margin certificates and general affine certificates are
equivalent under the exact parameter adapter. -/
theorem carlsonPhysicalMarginCertificate_iff_finiteAffine
    {n : ℕ} {beta alpha delta : ℝ}
    (sigma tau : Fin (n + 1) → ℝ) :
    ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha delta ↔
      FiniteAffineDensityMarginCertificate
        (carlsonAffineDensityFloor beta)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma)
        alpha delta := by
  constructor
  · intro certificate
    constructor
    · simpa [carlsonAffineDensityFloor] using certificate.contour
    · intro i
      simpa [carlsonAffineDensityCeiling,
        carlsonAffineDensitySlope,
        actualSelectedHeightStripPhysicalMargin_eq] using
        certificate.strip i
  · intro certificate
    constructor
    · simpa [carlsonAffineDensityFloor] using certificate.contour
    · intro i
      simpa [carlsonAffineDensityCeiling,
        carlsonAffineDensitySlope,
        actualSelectedHeightStripPhysicalMargin_eq] using
        certificate.strip i

/-- The Carlson weighted exponent attains its optimal physical margin as a
direct instance of the general affine optimizer. -/
theorem carlsonWeightedBalancedExponent_marginCertificate_via_finiteAffine
    {n : ℕ} (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    ActualSelectedHeightFiniteStripPhysicalMarginCertificate
      beta sigma tau
      (actualSelectedHeightFiniteStripWeightedBalancedExponent
        beta sigma tau)
      (actualSelectedHeightFiniteStripOptimalPhysicalMargin
        beta sigma tau) := by
  rw [carlsonPhysicalMarginCertificate_iff_finiteAffine]
  rw [← carlsonAffineBalancedExponent_eq,
    ← carlsonAffineOptimalMargin_eq]
  apply finiteAffineBalancedExponent_marginCertificate
  intro i
  exact
    actualSelectedHeightStripSlope_pos
      (hsigma i) (hsigmaOne i)

/-- The Carlson common physical margin is maximal by the general affine
maximin theorem. -/
theorem carlsonWeightedBalancedExponent_maximizes_via_finiteAffine
    {n : ℕ} {beta alpha delta : ℝ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha delta) :
    delta ≤
      actualSelectedHeightFiniteStripOptimalPhysicalMargin
        beta sigma tau := by
  rw [← carlsonAffineOptimalMargin_eq]
  apply finiteAffineBalancedExponent_maximizes_margin
  · intro i
    exact
      actualSelectedHeightStripSlope_pos
        (hsigma i) (hsigmaOne i)
  · exact
      (carlsonPhysicalMarginCertificate_iff_finiteAffine
        sigma tau).mp certificate

/-- Any Carlson exponent attaining the optimal physical margin is uniquely
the weighted balanced exponent, by the general affine uniqueness theorem. -/
theorem carlsonWeightedBalancedExponent_unique_via_finiteAffine
    {n : ℕ} {beta alpha : ℝ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha
        (actualSelectedHeightFiniteStripOptimalPhysicalMargin
          beta sigma tau)) :
    alpha =
      actualSelectedHeightFiniteStripWeightedBalancedExponent
        beta sigma tau := by
  rw [← carlsonAffineBalancedExponent_eq]
  apply finiteAffineBalancedExponent_unique
  · intro i
    exact
      actualSelectedHeightStripSlope_pos
        (hsigma i) (hsigmaOne i)
  · rw [carlsonAffineOptimalMargin_eq]
    exact
      (carlsonPhysicalMarginCertificate_iff_finiteAffine
        sigma tau).mp certificate

/-- The Carlson endpoint criterion supplies the positive-budget hypothesis of
the general affine optimizer. -/
theorem carlsonAffineOptimalMargin_pos
    {n : ℕ} {beta : ℝ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hthreshold :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta) :
    0 <
      finiteAffineOptimalMargin
        (carlsonAffineDensityFloor beta)
        (carlsonAffineDensityCeiling beta tau)
        (carlsonAffineDensitySlope sigma) := by
  apply finiteAffineOptimalMargin_pos
  · intro i
    exact
      actualSelectedHeightStripSlope_pos
        (hsigma i) (hsigmaOne i)
  · intro i
    have hq :
        0 < actualSelectedHeightStripCarlsonSlope (sigma i) :=
      actualSelectedHeightStripSlope_pos
        (hsigma i) (hsigmaOne i)
    have hden :
        0 < 1 + actualSelectedHeightStripCarlsonSlope (sigma i) := by
      linarith
    have hi := hthreshold i
    dsimp [carlsonStripEndpointTargetThreshold] at hi
    dsimp [actualSelectedHeightStripCarlsonSlope] at hden
    rw [div_lt_iff₀ hden] at hi
    dsimp [carlsonAffineDensityFloor,
      carlsonAffineDensityCeiling,
      carlsonAffineDensitySlope]
    dsimp [actualSelectedHeightStripCarlsonSlope] at hi ⊢
    nlinarith

end PrimeNumberTheorem
