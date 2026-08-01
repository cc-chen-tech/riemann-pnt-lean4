import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryMonotoneUnifiedUpperSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightCriticalHalfDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedUniformGoodHeightPNT

/-!
# Canonical polynomial-height window for power-scale transfer

When `beta > (1 + sigma) / 2`, the contour lower exponent `1 - beta`
lies strictly below the density upper exponent `beta - sigma`. We divide this
open interval into three equal parts, reserving separate margins for the
selected-height unit window and logarithmic losses.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Width of the feasible polynomial-height interval. -/
noncomputable def canonicalPolynomialHeightGap (beta sigma : ℝ) : ℝ :=
  2 * beta - 1 - sigma

/-- Inner exponent at the first trisection point. -/
noncomputable def canonicalPolynomialHeightInnerExponent (beta sigma : ℝ) : ℝ :=
  1 - beta + canonicalPolynomialHeightGap beta sigma / 3

/-- Outer exponent at the second trisection point. -/
noncomputable def canonicalPolynomialHeightOuterExponent (beta sigma : ℝ) : ℝ :=
  1 - beta + 2 * canonicalPolynomialHeightGap beta sigma / 3

/-- Half of the final third, reserved to absorb logarithmic losses. -/
noncomputable def canonicalPolynomialHeightEpsilon (beta sigma : ℝ) : ℝ :=
  canonicalPolynomialHeightGap beta sigma / 6

/-- Complete arithmetic specification of the canonical trisection window. -/
theorem canonicalPolynomialHeightWindow_spec
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hbeta : (1 + sigma) / 2 < beta) (hbetaOne : beta < 1) :
    0 < canonicalPolynomialHeightGap beta sigma ∧
    0 < canonicalPolynomialHeightInnerExponent beta sigma ∧
    canonicalPolynomialHeightInnerExponent beta sigma <
      canonicalPolynomialHeightOuterExponent beta sigma ∧
    1 - beta < canonicalPolynomialHeightInnerExponent beta sigma ∧
    canonicalPolynomialHeightOuterExponent beta sigma < beta - sigma ∧
    canonicalPolynomialHeightInnerExponent beta sigma ≤ 1 ∧
    0 < canonicalPolynomialHeightEpsilon beta sigma ∧
    sigma - beta + canonicalPolynomialHeightOuterExponent beta sigma +
        canonicalPolynomialHeightEpsilon beta sigma < 0 := by
  unfold canonicalPolynomialHeightInnerExponent
    canonicalPolynomialHeightOuterExponent
    canonicalPolynomialHeightEpsilon
    canonicalPolynomialHeightGap
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The canonical inner selected height is eventually below the canonical
outer polynomial height, tends to infinity, and carries the actual
power-normalized explicit-formula remainder certificate. -/
theorem canonicalPolynomialSelectedHeight_spec
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hbeta : (1 + sigma) / 2 < beta) (hbetaOne : beta < 1)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (∀ᶠ m : ℕ in atTop,
      selectedUniformGoodHeight
          (canonicalPolynomialHeightInnerExponent beta sigma)
          selection (m : ℝ) ≤
        carlsonPolynomialHeight
          (canonicalPolynomialHeightOuterExponent beta sigma) (m : ℝ)) ∧
    Tendsto
      (fun m : ℕ =>
        selectedUniformGoodHeight
          (canonicalPolynomialHeightInnerExponent beta sigma)
          selection (m : ℝ))
      atTop atTop ∧
    ActualSelectedHeightNaturalPointRemainderCertificate beta
      (selectedUniformGoodHeight
        (canonicalPolynomialHeightInnerExponent beta sigma) selection) := by
  have hspec :=
    canonicalPolynomialHeightWindow_spec hsigma hbeta hbetaOne
  have hheightReal :=
    eventually_selectedUniformGoodHeight_le_polynomialHeight
      hspec.2.1 hspec.2.2.1 selection
  have hheightNatural := tendsto_natCast_atTop_atTop.eventually hheightReal
  have htopReal := selectedUniformGoodHeight_tendsto_atTop hspec.2.1 selection
  have htopNatural := htopReal.comp tendsto_natCast_atTop_atTop
  have hremainder :=
    selectedUniformGoodHeight_actualNaturalRemainderCertificate
      (by linarith : 0 < beta)
      hspec.2.1 hspec.2.2.2.2.2.1 hspec.2.2.2.1 selection
  exact ⟨hheightNatural, htopNatural, hremainder⟩

end PrimeNumberTheorem
