import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryRealOrdinateDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightNaturalTransfer

/-!
# Explicit-formula transfer for a dynamic boundary package

This module assembles the complete target-normalized remainder around the
moving equal-real-part package.  The low positive strip is controlled by the
global zero-multiplicity estimate, the high positive strip by the summable
Carlson tail, negative ordinates by conjugation, and real ordinates by finite
dominated convergence.  The closed real-axis and contour terms are then added
through the exact explicit formula.

The conclusion is a remainder theorem, not an oscillation theorem.  A
separate anti-cancellation witness for the moving package main term is still
required.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
The complete zero complement outside the dynamic equal-real-part package is
negligible at the target amplitude, with both the low strip and real-ordinate
residual discharged automatically.
-/
theorem
    actualDynamicBoundarySignedComplement_targetAmplitudeNegligible
    {H : ℝ → ℝ} {beta sigma alpha epsilon : ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hrightPositive :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        dynamicOutsideClusterPNTComplement H
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) (m : ℝ)) := by
  have hpositive :=
    actualDynamicBoundaryCanonicalPositiveNormalizedSum_tendsto_zero
      hhalf hone hHle hHtop halpha hepsilon hmargin hrightPositive
  have hreal :=
    actualDynamicBoundaryRealNormalizedSum_tendsto_zero
      hHtop hrightReal
  have hfull :=
    actualDynamicBoundaryFullNormalizedSum_tendsto_zero
      hpositive hreal
  have hcomplement :=
    abs_dynamicOutsideDynamicBoundaryPNTComplement_div_target_tendsto_zero
      hfull
  unfold NaturalPointTargetAmplitudeNegligible
  exact hcomplement

/--
Full target-amplitude remainder theorem for the actual explicit formula
centered on the moving equal-real-part package.
-/
theorem
    actualDynamicBoundaryExplicitFormulaResidual_targetAmplitudeNegligible
    {H : ℝ → ℝ} {beta sigma alpha epsilon : ℝ}
    (hbeta : 0 < beta)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hrightPositive :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
            (m : ℝ)) := by
  have hamplitude :
      ∀ᶠ m : ℕ in atTop,
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hclosed :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ => actualPNTClosedRealAxisRelativeTerm (m : ℝ)) :=
    (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
      hbeta).naturalPoint
  have hcontour :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTExplicitFormulaRelativeRemainder H (m : ℝ)) :=
    remainder.negligible
  have hcomplement :=
    actualDynamicBoundarySignedComplement_targetAmplitudeNegligible
      hhalf hone hHle hHtop halpha hepsilon hmargin
      hrightPositive hrightReal
  have hthree :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
              actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ)) :=
    NaturalPointTargetAmplitudeNegligible.add hamplitude
      (NaturalPointTargetAmplitudeNegligible.add
        hamplitude hclosed hcontour)
      hcomplement
  unfold NaturalPointTargetAmplitudeNegligible at hthree ⊢
  apply hthree.congr'
  filter_upwards with m
  rw [relativeChebyshevPsi0Error_eq_dynamicBoundaryPackage_add_actualResiduals
    H beta (m : ℝ)]
  congr 2 <;> ring

end PrimeNumberTheorem
