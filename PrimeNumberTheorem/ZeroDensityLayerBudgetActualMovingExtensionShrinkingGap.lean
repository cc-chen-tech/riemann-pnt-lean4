import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass

/-!
# Moving extensions under a shrinking outside-zero gap

The outside cap may approach the target real part.  Its quantitative content is
the decay of the exact normalized two-height Carlson budget.  Every extension
estimate continues to pass through the cancellation-free absolute mass from
`ZeroDensityLayerBudgetActualMovingExtensionAbsoluteMass`.
-/

namespace PrimeNumberTheorem

open Filter Real
open scoped Topology

/-- A coefficient is small enough to absorb a cap approaching `beta` at the
chosen scale. -/
def HasShrinkingGapMassRate
    (beta : ℝ) (scale capTau massCoefficient : ℝ → ℝ) : Prop :=
  Tendsto
    (fun x => massCoefficient x * (scale x) ^ (capTau x - beta))
    atTop (nhds 0)

/-- A diverging exponential margin is a cancellation-free sufficient
condition for a shrinking-gap mass rate. -/
theorem shrinkingGapMassRate_of_exponentialMargin
    {beta : ℝ} {scale capTau massCoefficient margin : ℝ → ℝ}
    (hnonneg :
      ∀ᶠ x in atTop,
        0 ≤ massCoefficient x * (scale x) ^ (capTau x - beta))
    (hle :
      ∀ᶠ x in atTop,
        massCoefficient x * (scale x) ^ (capTau x - beta) ≤
          Real.exp (-margin x))
    (hmargin : Tendsto margin atTop atTop) :
    HasShrinkingGapMassRate beta scale capTau massCoefficient := by
  unfold HasShrinkingGapMassRate
  have hneg : Tendsto (fun x => -margin x) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hmargin
  have hexp : Tendsto (fun x => Real.exp (-margin x)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hneg
  exact squeeze_zero' hnonneg hle hexp

/-- The exact normalized Carlson budget for a cap depending on the evaluation
scale.  The first conjunct records that this really is an outside gap; the
second records the quantitative rate that makes the gap useful. -/
def HasShrinkingGapCarlsonTwoHeightRate
    (beta sigma alpha gamma : ℝ) (capTau : ℝ → ℝ) : Prop :=
  (∀ᶠ x in atTop, capTau x < beta) ∧
    Tendsto
      (fun x =>
        actualCarlsonTargetTwoHeightLowBudget
            beta sigma (capTau x) gamma x +
          actualCarlsonTargetTwoHeightHighBudget
            beta sigma (capTau x) alpha gamma x)
      atTop (nhds 0)

/-- Separate coefficient estimates for the two Carlson height ranges imply
the exact dynamic two-height rate. -/
theorem shrinkingGapCarlsonTwoHeightRate_of_budget_majorants
    {beta sigma alpha gamma : ℝ}
    {capTau lowCoefficient highCoefficient : ℝ → ℝ}
    (hbelow : ∀ᶠ x in atTop, capTau x < beta)
    (hlowRate :
      HasShrinkingGapMassRate beta id capTau lowCoefficient)
    (hhighRate :
      HasShrinkingGapMassRate beta id capTau highCoefficient)
    (hlowNonneg :
      ∀ᶠ x in atTop,
        0 ≤ actualCarlsonTargetTwoHeightLowBudget
          beta sigma (capTau x) gamma x)
    (hhighNonneg :
      ∀ᶠ x in atTop,
        0 ≤ actualCarlsonTargetTwoHeightHighBudget
          beta sigma (capTau x) alpha gamma x)
    (hlow :
      ∀ᶠ x in atTop,
        actualCarlsonTargetTwoHeightLowBudget
            beta sigma (capTau x) gamma x ≤
          lowCoefficient x * x ^ (capTau x - beta))
    (hhigh :
      ∀ᶠ x in atTop,
        actualCarlsonTargetTwoHeightHighBudget
            beta sigma (capTau x) alpha gamma x ≤
          highCoefficient x * x ^ (capTau x - beta)) :
    HasShrinkingGapCarlsonTwoHeightRate
      beta sigma alpha gamma capTau := by
  refine ⟨hbelow, ?_⟩
  unfold HasShrinkingGapMassRate at hlowRate hhighRate
  have hlowRate' :
      Tendsto
        (fun x => lowCoefficient x * x ^ (capTau x - beta))
        atTop (nhds 0) := by
    simpa using hlowRate
  have hhighRate' :
      Tendsto
        (fun x => highCoefficient x * x ^ (capTau x - beta))
        atTop (nhds 0) := by
    simpa using hhighRate
  have hlowTendsto := squeeze_zero' hlowNonneg hlow hlowRate'
  have hhighTendsto := squeeze_zero' hhighNonneg hhigh hhighRate'
  simpa using hlowTendsto.add hhighTendsto

/-- The actual positive Carlson strip with moving right endpoint is negligible
whenever its exact two-height budget has the shrinking-gap rate. -/
theorem
    tendsto_dynamicActualPositiveCarlsonStripTargetAmplitudeMass_of_shrinkingGap
    {beta sigma alpha gamma : ℝ} {capTau : ℝ → ℝ}
    (hsigma : 0 < sigma)
    (hgammaAlpha : gamma ≤ alpha)
    (hrate :
      HasShrinkingGapCarlsonTwoHeightRate
        beta sigma alpha gamma capTau) :
    Tendsto
      (fun x =>
        (∑ rho ∈ actualPositiveCarlsonStrip sigma (capTau x)
              (carlsonPolynomialHeight alpha x),
            ‖pntRelativeZeroContribution x rho‖) /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ hrate.2
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hamp : 0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
    exact div_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) hamp.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    simpa [actualPositiveCarlsonStripTargetAmplitudeMass] using
      (actualPositiveCarlsonStripTargetAmplitudeMass_le_twoHeightBudget
        (x := x) (beta := beta) (sigma := sigma) (tau := capTau x)
        (alpha := alpha) (gamma := gamma) hx hsigma hgammaAlpha)

/-- The selected positive outside-zero absolute mass is negligible under a
moving cap whose exact Carlson budget has the shrinking-gap rate. -/
theorem
    selectedPositiveOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap
    {H : ℝ → ℝ} {S : Finset ℂ} {capTau : ℝ → ℝ}
    {beta sigma alpha gammaLow epsilonLow gammaHigh : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh : alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
          sigma < rho.re → rho.re ≤ capTau x)
    (hstripRate :
      HasShrinkingGapCarlsonTwoHeightRate
        beta sigma alpha gammaHigh capTau) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTAbsoluteMass H S) := by
  let polynomialInput := fun y =>
    pntHybridCanonicalTwoStripOutsideClusterBucketInput
      sigma (carlsonPolynomialHeight alpha y) S
  rcases
      exists_canonicalTwoStripOutsideCluster_uniform_norm_lower_bound
        (carlsonPolynomialHeight alpha) sigma S with
    ⟨kappa, hkappa, hnorm⟩
  have hlow :=
    tendsto_dynamicOutsideClusterTwoHeightMass_div_target
      polynomialInput 0 hkappa hnorm
      (fun _ _ hrho =>
        pntHybridCanonicalTwoStripOutsideCluster_lowLayer_re_le hrho)
      halpha hgammaLow hepsilonLow hlowLow hlowHigh
  have hsigmaPos : 0 < sigma := by linarith
  have hstrip :=
    tendsto_dynamicActualPositiveCarlsonStripTargetAmplitudeMass_of_shrinkingGap
      hsigmaPos hgammaHighAlpha hstripRate
  have hmajor := hlow.add hstrip
  unfold TargetAmplitudeNegligible
  refine squeeze_zero' ?_ ?_ (by simpa using hmajor)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg (abs_nonneg _)
      (Real.rpow_nonneg (zero_le_one.trans hx) _)
  · filter_upwards
      [eventually_ge_atTop (1 : ℝ), hHle] with x hx hHx
    have hamp : 0 < targetZeroPowerAmplitude beta x :=
      Real.rpow_pos_of_pos (zero_lt_one.trans_le hx) _
    have hp :=
      dynamicSelectedPositiveOutsideClusterPNTAbsoluteMass_le
        (gamma := gammaLow) hHx (hcap x)
    have hmassNonneg :
        0 ≤ dynamicPositiveOutsideClusterPNTAbsoluteMass H S x :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    rw [abs_of_nonneg hmassNonneg]
    have hdiv := (div_le_div_iff_of_pos_right hamp).2 hp
    simpa [add_div] using hdiv

/-- Conjugation and the fixed real-ordinate slice upgrade positive moving-cap
decay to the full cancellation-free outside mass. -/
theorem
    selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap
    {H : ℝ → ℝ} {S : Finset ℂ} {capTau : ℝ → ℝ}
    {beta sigma alpha gammaLow epsilonLow gammaHigh : ℝ}
    (hS : IsConjugationInvariantCluster S)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha)
    (hgammaLow : 0 < gammaLow)
    (hepsilonLow : 0 < epsilonLow)
    (hlowLow : gammaLow + sigma - beta + epsilonLow < 0)
    (hlowHigh : alpha + sigma - beta - gammaLow + epsilonLow < 0)
    (hgammaHighAlpha : gammaHigh ≤ alpha)
    (hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x)
    (hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hcap :
      ∀ x rho,
        rho ∈ positiveNontrivialZerosOutsideClusterFinset (H x) S →
          sigma < rho.re → rho.re ≤ capTau x)
    (hstripRate :
      HasShrinkingGapCarlsonTwoHeightRate
        beta sigma alpha gammaHigh capTau)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (dynamicFullOutsideClusterPNTAbsoluteMass H S) := by
  have hpositive :=
    selectedPositiveOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap
      hsigma hsigmaOne halpha hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHighAlpha hHle hcap hstripRate
  have hrealMass :=
    dynamicRealOrdinateOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible
      H S beta hHnonneg hreal
  have hamplitude := targetZeroPowerAmplitude_eventually_pos beta
  have hmajor :=
    (hpositive.add hamplitude hpositive).add hamplitude hrealMass
  apply hmajor.of_eventually_abs_le hamplitude
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [dynamicFullOutsideClusterPNTAbsoluteMass_eq_two_positive_add_real
    hS hx]
  rw [abs_of_nonneg]
  exact add_nonneg
    (add_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Full absolute-mass decay controls the moving extension for any fixed
threshold used by the signed transfer. -/
theorem
    selectedMovingRightEdgeExtension_targetAmplitudeNegligible_of_shrinkingGap
    {H : ℝ → ℝ} {S : Finset ℂ} {beta transferTau : ℝ}
    (hfull :
      TargetAmplitudeNegligible
        (targetZeroPowerAmplitude beta)
        (dynamicFullOutsideClusterPNTAbsoluteMass H S)) :
    TargetAmplitudeNegligible
      (targetZeroPowerAmplitude beta)
      (fun x =>
        dynamicVisibleClusterPNTMain H
          (movingRightEdgeExceptionalCluster H transferTau x \ S) x) :=
  selectedMovingRightEdgeExtension_targetAmplitudeNegligible hfull

/-- A scale-dependent outside cap with a vanishing exact Carlson budget
discharges the moving-extension loss and transfers signed seed witnesses to the
actual PNT error at coefficient `c / 4`. -/
theorem
    exists_shrinkingGap_positiveOutsideClusterMovingSeedSignedNaturalTargetTransfer
    {S : Finset ℂ} {beta c : ℝ}
    (hbeta : 2 / 3 < beta)
    (hbetaOne : beta < 1)
    (hc : 0 < c)
    (hseed : IsTargetRealPartNontrivialZeroSeed beta S)
    (hS : IsConjugationInvariantCluster S)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    ∃ sigma transferTau alpha gammaLow gammaHigh epsilonLow : ℝ,
      1 / 2 < sigma ∧
      sigma < transferTau ∧
      1 / 2 < transferTau ∧
      transferTau < beta ∧
      sigma < 1 ∧
      1 - beta < alpha ∧
      0 < alpha ∧
      alpha ≤ 1 ∧
      0 < gammaLow ∧
      0 < gammaHigh ∧
      gammaHigh ≤ alpha ∧
      0 < epsilonLow ∧
      gammaLow + sigma - beta + epsilonLow < 0 ∧
      alpha + sigma - beta - gammaLow + epsilonLow < 0 ∧
      ∀ (selection : UniformNaturalPointGoodHeightSelection)
          (capTau : ℝ → ℝ),
        (∀ x rho,
          rho ∈ positiveNontrivialZerosOutsideClusterFinset
              (selectedUniformGoodHeight alpha selection x) S →
            sigma < rho.re → rho.re ≤ capTau x) →
        HasShrinkingGapCarlsonTwoHeightRate
            beta sigma alpha gammaHigh capTau →
        HasFarNaturalPointPositiveTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection) S (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        HasFarNaturalPointNegativeTargetAmplitudeWitness
            (fun m : ℕ =>
              dynamicVisibleClusterPNTMain
                (selectedUniformGoodHeight alpha selection) S (m : ℝ))
            (fun m : ℕ =>
              c * targetZeroPowerAmplitude beta (m : ℝ)) →
        (∃ rate : ℝ,
            0 < rate ∧
            rate ≤ 1 ∧
            Tendsto
              (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
              atTop (nhds 0)) ∧
          HasFarSignedTargetAmplitudeWitnesses
            relativeChebyshevPsi0Error
            (fun x => (c / 4) * targetZeroPowerAmplitude beta x) := by
  have hhalf : (1 / 2 : ℝ) < (3 * beta - 1) / 2 := by linarith
  rcases
      exists_jointTwoHeightTargetAmplitudeParameters_above_cap
        (theta := (1 / 2 : ℝ)) hbeta hbetaOne hhalf with
    ⟨sigma, transferTau, alpha, gammaLow, gammaHigh,
      epsilonLow, epsilonHigh,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, _hgammaLowEq,
      hgammaLow, _hgammaLowAlpha, _hgammaHighEq,
      hgammaHigh, hgammaHighAlpha,
      hepsilonLow, hepsilonHigh,
      hlowLow, hlowHigh, hstripLow, hstripHigh⟩
  refine
    ⟨sigma, transferTau, alpha, gammaLow, gammaHigh, epsilonLow,
      hsigmaHalf, hsigmaTau, hhalfTau, htauBeta, hsigmaOne,
      hcontour, halpha, halphaOne, hgammaLow, hgammaHigh,
      hgammaHighAlpha.le, hepsilonLow, hlowLow, hlowHigh, ?_⟩
  intro selection capTau hselectedCap hstripRate hseedPos hseedNeg
  let H := selectedUniformGoodHeight alpha selection
  have hheight :=
    eventually_selectedUniformGoodHeight_nonneg_le_polynomial
      halpha selection
  have hHnonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ H x :=
    hheight.mono fun _ hx => hx.1
  have hHle :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x :=
    hheight.mono fun _ hx => hx.2
  have hfull :=
    selectedFullOutsideClusterPNTAbsoluteMass_targetAmplitudeNegligible_of_shrinkingGap
      hS hsigmaHalf hsigmaOne halpha hgammaLow hepsilonLow
      hlowLow hlowHigh hgammaHighAlpha.le hHnonneg hHle
      (by simpa [H] using hselectedCap) hstripRate hreal
  have hextension :=
    selectedMovingRightEdgeExtension_targetAmplitudeNegligible_of_shrinkingGap
      (transferTau := transferTau) hfull
  have hloss : 0 < c / 2 := by linarith
  have hnew :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hextension.naturalPoint hloss
  have hbetaPos : 0 < beta := by linarith
  have hnet : 0 < c - c / 2 := by linarith
  have hresult :=
    unified_automaticGoodHeight_twoHeight_movingRightEdgeSignedSeedNaturalTargetTransfer
      (S₀ := S) (c := c) (loss := c / 2)
      hbetaPos halphaOne hcontour selection
      hsigmaHalf hsigmaOne htauBeta halpha
      hgammaLow hepsilonLow hlowLow hlowHigh
      hgammaHigh hgammaHighAlpha.le
      hepsilonHigh hstripLow hstripHigh
      hnet hseed
      (by simpa [H] using hseedPos)
      (by simpa [H] using hseedNeg)
      (by simpa [H] using hnew)
  refine ⟨hresult.1, ?_⟩
  convert hresult.2 using 1 <;> funext x <;> ring

end PrimeNumberTheorem
