import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualTwoHeightSplit
import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeTwoHeightExponent

/-!
# Actual target-amplitude two-height Carlson strips

This module transfers the target-normalized exponent arithmetic to the
existing multiplicity-weighted actual zeta-zero two-height split.  Division by
`x ^ (beta - 1)` is implemented by shifting the ordinary strip endpoint from
`tau` to `tau - beta + 1`.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- Dividing the strip endpoint power by the target-zero power is exactly an
endpoint shift. -/
theorem rpow_stripEndpoint_div_targetZeroPowerAmplitude
    {x beta tau : ℝ} (hx : 0 < x) :
    x ^ (tau - 1) / targetZeroPowerAmplitude beta x =
      x ^ ((tau - beta + 1) - 1) := by
  rw [targetZeroPowerAmplitude,
    ← Real.rpow_sub hx (tau - 1) (beta - 1)]
  congr 1
  ring

/-- Actual low-height Carlson budget normalized by the target-zero
amplitude. -/
noncomputable def actualCarlsonTargetTwoHeightLowBudget
    (beta sigma tau gamma x : ℝ) : ℝ :=
  actualCarlsonTwoHeightLowBudget sigma tau gamma x /
    targetZeroPowerAmplitude beta x

/-- Actual high-annulus Carlson budget normalized by the target-zero
amplitude. -/
noncomputable def actualCarlsonTargetTwoHeightHighBudget
    (beta sigma tau alpha gamma x : ℝ) : ℝ :=
  actualCarlsonTwoHeightHighBudget sigma tau alpha gamma x /
    targetZeroPowerAmplitude beta x

theorem actualCarlsonTargetTwoHeightLowBudget_eq_shifted
    {x beta sigma tau gamma : ℝ} (hx : 0 < x) :
    actualCarlsonTargetTwoHeightLowBudget
        beta sigma tau gamma x =
      actualCarlsonTwoHeightLowBudget
        sigma (tau - beta + 1) gamma x := by
  unfold actualCarlsonTargetTwoHeightLowBudget
    actualCarlsonTwoHeightLowBudget
  calc
    ((x ^ (tau - 1) / sigma) *
          (ZeroDensity.zeroDensityCount sigma
            (carlsonPolynomialHeight gamma x) : ℝ)) /
        targetZeroPowerAmplitude beta x =
      ((x ^ (tau - 1) /
          targetZeroPowerAmplitude beta x) / sigma) *
        (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight gamma x) : ℝ) := by
            ring
    _ = ((x ^ ((tau - beta + 1) - 1)) / sigma) *
        (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight gamma x) : ℝ) := by
            rw [rpow_stripEndpoint_div_targetZeroPowerAmplitude hx]

theorem actualCarlsonTargetTwoHeightHighBudget_eq_shifted
    {x beta sigma tau alpha gamma : ℝ} (hx : 0 < x) :
    actualCarlsonTargetTwoHeightHighBudget
        beta sigma tau alpha gamma x =
      actualCarlsonTwoHeightHighBudget
        sigma (tau - beta + 1) alpha gamma x := by
  unfold actualCarlsonTargetTwoHeightHighBudget
    actualCarlsonTwoHeightHighBudget
    polynomialOrdinateRectangleKernel
  calc
    (((x ^ (tau - 1) /
          carlsonPolynomialHeight gamma x) *
        (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight alpha x) : ℝ)) /
        targetZeroPowerAmplitude beta x) =
      (((x ^ (tau - 1) /
          targetZeroPowerAmplitude beta x) /
          carlsonPolynomialHeight gamma x) *
        (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight alpha x) : ℝ)) := by
            ring
    _ = ((x ^ ((tau - beta + 1) - 1) /
          carlsonPolynomialHeight gamma x) *
        (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight alpha x) : ℝ)) := by
            rw [rpow_stripEndpoint_div_targetZeroPowerAmplitude hx]

theorem tendsto_actualCarlsonTargetTwoHeightLowBudget
    {beta sigma tau gamma epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hgamma : 0 < gamma) (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gamma + epsilon < 0) :
    Tendsto
      (actualCarlsonTargetTwoHeightLowBudget
        beta sigma tau gamma)
      atTop (nhds 0) := by
  have hshiftMargin :
      carlsonTwoHeightLowExponent
          sigma (tau - beta + 1) gamma + epsilon < 0 := by
    rw [carlsonTwoHeightLowExponent_eq]
    unfold targetAmplitudeCarlsonTwoHeightLowExponent at hmargin
    linarith
  have hshift :=
    tendsto_actualCarlsonTwoHeightLowBudget
      hsigma hsigmaOne hgamma hepsilon hshiftMargin
  apply hshift.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (actualCarlsonTargetTwoHeightLowBudget_eq_shifted hx).symm

theorem tendsto_actualCarlsonTargetTwoHeightHighBudget
    {beta sigma tau alpha gamma epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (actualCarlsonTargetTwoHeightHighBudget
        beta sigma tau alpha gamma)
      atTop (nhds 0) := by
  have hshiftMargin :
      carlsonTwoHeightHighExponent
          sigma (tau - beta + 1) alpha gamma + epsilon < 0 := by
    rw [carlsonTwoHeightHighExponent_eq]
    unfold targetAmplitudeCarlsonTwoHeightHighExponent at hmargin
    linarith
  have hshift :=
    tendsto_actualCarlsonTwoHeightHighBudget
      hsigma hsigmaOne halpha hepsilon hshiftMargin
  apply hshift.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (actualCarlsonTargetTwoHeightHighBudget_eq_shifted hx).symm

/-- Multiplicity-weighted actual strip mass divided by the target-zero
amplitude. -/
noncomputable def actualPositiveCarlsonStripTargetAmplitudeMass
    (beta sigma tau alpha x : ℝ) : ℝ :=
  (∑ rho ∈ actualPositiveCarlsonStrip sigma tau
      (carlsonPolynomialHeight alpha x),
      ‖pntRelativeZeroContribution x rho‖) /
    targetZeroPowerAmplitude beta x

theorem actualPositiveCarlsonStripTargetAmplitudeMass_le_twoHeightBudget
    {x beta sigma tau alpha gamma : ℝ}
    (hx : 1 ≤ x) (hsigma : 0 < sigma)
    (hgammaAlpha : gamma ≤ alpha) :
    actualPositiveCarlsonStripTargetAmplitudeMass
        beta sigma tau alpha x ≤
      actualCarlsonTargetTwoHeightLowBudget
          beta sigma tau gamma x +
        actualCarlsonTargetTwoHeightHighBudget
          beta sigma tau alpha gamma x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hamplitude :
      0 < targetZeroPowerAmplitude beta x :=
    Real.rpow_pos_of_pos hx0 _
  have hraw :=
    sum_norm_actualPositiveCarlsonStrip_le_twoHeightBudget
      (x := x) (sigma := sigma) (tau := tau)
      (alpha := alpha) (gamma := gamma)
      hx hsigma hgammaAlpha
  have hdiv :=
    div_le_div_of_nonneg_right hraw hamplitude.le
  simpa [actualPositiveCarlsonStripTargetAmplitudeMass,
    actualCarlsonTargetTwoHeightLowBudget,
    actualCarlsonTargetTwoHeightHighBudget, add_div] using hdiv

/-- The complete actual multiplicity-weighted strip is negligible on the
target-zero scale under the two target-normalized exponent margins. -/
theorem tendsto_actualPositiveCarlsonStripTargetAmplitudeMass_twoHeight
    {beta sigma tau alpha gamma epsilon : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hgammaAlpha : gamma ≤ alpha)
    (hepsilon : 0 < epsilon)
    (hlow :
      targetAmplitudeCarlsonTwoHeightLowExponent
          beta sigma tau gamma + epsilon < 0)
    (hhigh :
      targetAmplitudeCarlsonTwoHeightHighExponent
          beta sigma tau alpha gamma + epsilon < 0) :
    Tendsto
      (actualPositiveCarlsonStripTargetAmplitudeMass
        beta sigma tau alpha)
      atTop (nhds 0) := by
  have hmajor :
      Tendsto
        (fun x =>
          actualCarlsonTargetTwoHeightLowBudget
              beta sigma tau gamma x +
            actualCarlsonTargetTwoHeightHighBudget
              beta sigma tau alpha gamma x)
        atTop (nhds 0) := by
    simpa using
      (tendsto_actualCarlsonTargetTwoHeightLowBudget
        hsigma hsigmaOne hgamma hepsilon hlow).add
        (tendsto_actualCarlsonTargetTwoHeightHighBudget
          hsigma hsigmaOne halpha hepsilon hhigh)
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (by
        simpa [targetZeroPowerAmplitude] using
          (Real.rpow_nonneg hx.le (beta - 1)))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact
      actualPositiveCarlsonStripTargetAmplitudeMass_le_twoHeightBudget
        hx (lt_trans (by norm_num) hsigma) hgammaAlpha

/-- One feasibility inequality chooses a contour-admissible outer height and
proves actual target-normalized strip decay at the balanced cut. -/
theorem exists_outerHeight_tendsto_actualPositiveCarlsonStripTargetAmplitudeMass
    {beta sigma tau : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hbetaOne : beta < 1)
    (hfeasible :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + tau - beta < 0) :
    ∃ alpha : ℝ,
      1 - beta < alpha ∧
      Tendsto
        (actualPositiveCarlsonStripTargetAmplitudeMass
          beta sigma tau alpha)
        atTop (nhds 0) := by
  rcases
      exists_targetAmplitudeCarlsonTwoHeightStrictMargins
        hsigma hsigmaOne hbetaOne hfeasible with
    ⟨alpha, gamma, epsilon, hcontour, hgamma,
      hgammaAlpha, hepsilon, hlow, hhigh⟩
  refine ⟨alpha, hcontour, ?_⟩
  exact
    tendsto_actualPositiveCarlsonStripTargetAmplitudeMass_twoHeight
      hsigma hsigmaOne (lt_trans (sub_pos.mpr hbetaOne) hcontour)
      hgamma hgammaAlpha.le hepsilon hlow hhigh

/-- For every `2/3 < beta < 1`, there is a genuine positive-width actual
Carlson strip and a contour-admissible outer height whose complete
multiplicity-weighted mass is negligible relative to `x ^ (beta - 1)`. -/
theorem exists_positiveWidth_actualCarlsonStripTargetAmplitudeMass_tendsto_zero
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ sigma tau alpha : ℝ,
      1 / 2 < sigma ∧ sigma < tau ∧ tau < beta ∧
      1 - beta < alpha ∧
      Tendsto
        (actualPositiveCarlsonStripTargetAmplitudeMass
          beta sigma tau alpha)
        atTop (nhds 0) := by
  let sigma :=
    targetAmplitudeCarlsonTwoHeightCanonicalThreshold beta
  let slope :=
    targetAmplitudeCarlsonTwoHeightBalancedSlope sigma
  let upper := beta - slope * (1 - beta)
  have hspec :=
    targetAmplitudeCarlsonTwoHeightCanonicalThreshold_spec
      hbeta hbetaOne
  have hsigmaHalf : 1 / 2 < sigma := by
    simpa [sigma] using hspec.1
  have hsigmaOne : sigma < 1 := by
    simpa [sigma] using hspec.2.2
  have hslopePos : 0 < slope := by
    simpa [slope] using
      targetAmplitudeCarlsonTwoHeightBalancedSlope_pos
        hsigmaHalf hsigmaOne
  have hfloor : 0 < 1 - beta := sub_pos.mpr hbetaOne
  have hsigmaUpper : sigma < upper := by
    have hcanonical :=
      targetAmplitudeCarlsonTwoHeightCanonical_feasible
        hbeta hbetaOne
    dsimp [sigma, slope, upper]
    linarith
  have hupperBeta : upper < beta := by
    dsimp [upper]
    nlinarith
  let tau := (sigma + upper) / 2
  have hsigmaTau : sigma < tau := by
    dsimp [tau]
    linarith
  have htauUpper : tau < upper := by
    dsimp [tau]
    linarith
  have htauBeta : tau < beta := htauUpper.trans hupperBeta
  have hfeasible :
      targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) + tau - beta < 0 := by
    dsimp [upper] at htauUpper
    change tau <
      beta -
        targetAmplitudeCarlsonTwoHeightBalancedSlope sigma *
          (1 - beta) at htauUpper
    linarith
  rcases
      exists_outerHeight_tendsto_actualPositiveCarlsonStripTargetAmplitudeMass
        hsigmaHalf hsigmaOne hbetaOne hfeasible with
    ⟨alpha, hcontour, hlimit⟩
  exact
    ⟨sigma, tau, alpha, hsigmaHalf, hsigmaTau, htauBeta,
      hcontour, hlimit⟩

end PrimeNumberTheorem
