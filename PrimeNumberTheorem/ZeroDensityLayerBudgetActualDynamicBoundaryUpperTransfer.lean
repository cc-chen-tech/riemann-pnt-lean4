import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticWitnessTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVisibleClusterCoefficientMass

/-!
# Dynamic-boundary PNT upper transfer

The full explicit-formula residual outside the moving equal-real-part package
is already `o(x^(beta - 1))`.  To obtain a matching upper bound, it remains to
control the coefficient mass of that moving finite package uniformly.

This module isolates that input honestly and proves the resulting upper
transfer.  It does not claim that Carlson density alone supplies the uniform
coefficient cap.
-/

namespace PrimeNumberTheorem

open Filter

/-- Eventual uniform coefficient-mass cap for the moving equal-real-part zero
package. -/
def DynamicBoundaryPackageCoefficientCap
    (beta : ℝ) (H : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    finiteVisibleClusterCoefficientMass
        (dynamicEqualRealPartZeroPackage H beta (m : ℝ)) ≤ C

/--
An `o(x^(beta - 1))` explicit-formula residual and a package coefficient cap
give the sharp eventual upper bound `(C + eta) * x^(beta - 1)` for every
`eta > 0`.
-/
theorem eventually_abs_relativeChebyshevPsi0Error_lt_dynamicBoundaryCap_add
    {beta C eta : ℝ} {H : ℝ → ℝ}
    (heta : 0 < eta)
    (hcap : DynamicBoundaryPackageCoefficientCap beta H C)
    (hresidual :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (C + eta) * targetZeroPowerAmplitude beta (m : ℝ) := by
  have hamplitude :
      ∀ᶠ m : ℕ in atTop,
        0 < targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  have hremainder :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ)| <
          eta * targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hresidual heta
  filter_upwards
      [eventually_ge_atTop (1 : ℕ), hcap, hamplitude, hremainder] with
      m hm hcapM hamplitudeM hremainderM
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hpackageRe :
      ∀ rho ∈ dynamicEqualRealPartZeroPackage H beta (m : ℝ),
        rho.re ≤ beta := by
    intro rho hrho
    exact (mem_dynamicEqualRealPartZeroPackage.mp hrho).2.2.le
  have hmain :=
    abs_dynamicVisibleClusterPNTMain_le_coefficientMass_mul_targetAmplitude
      H (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
      hmReal hpackageRe
  have hmainCap :
      |dynamicVisibleClusterPNTMain H
          (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
          (m : ℝ)| ≤
        C * targetZeroPowerAmplitude beta (m : ℝ) :=
    hmain.trans
      (mul_le_mul_of_nonneg_right hcapM hamplitudeM.le)
  calc
    |relativeChebyshevPsi0Error (m : ℝ)| =
        |dynamicVisibleClusterPNTMain H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ) +
            (relativeChebyshevPsi0Error (m : ℝ) -
              dynamicVisibleClusterPNTMain H
                (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
                (m : ℝ))| := by
          congr 1
          ring
    _ ≤
        |dynamicVisibleClusterPNTMain H
            (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
            (m : ℝ)| +
          |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (dynamicEqualRealPartZeroPackage H beta (m : ℝ))
              (m : ℝ)| :=
      abs_add_le _ _
    _ <
        C * targetZeroPowerAmplitude beta (m : ℝ) +
          eta * targetZeroPowerAmplitude beta (m : ℝ) :=
      add_lt_add_of_le_of_lt hmainCap hremainderM
    _ = (C + eta) * targetZeroPowerAmplitude beta (m : ℝ) := by
      ring

/--
Automatic dynamic-boundary upper transfer.  All explicit-formula complement
terms are discharged; the only additional upper-side input is the package
coefficient cap.
-/
theorem actualDynamicBoundaryAutomaticPNTUpperTransfer
    {H : ℝ → ℝ} {beta sigma alpha epsilon C eta : ℝ}
    (hbeta : 0 < beta)
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hheightUpper :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hheightTendsto :
      Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta + alpha + epsilon < 0)
    (hpositiveRightEdge :
      ∀ index : ActualCarlsonPositiveZeroIndex sigma,
        actualCarlsonPositiveZeroRealPart index ≤ beta)
    (hrealRightEdge :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 ∅,
        rho.re ≤ beta)
    (remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (heta : 0 < eta)
    (hcap : DynamicBoundaryPackageCoefficientCap beta H C) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (C + eta) * targetZeroPowerAmplitude beta (m : ℝ) := by
  apply eventually_abs_relativeChebyshevPsi0Error_lt_dynamicBoundaryCap_add
    heta hcap
  exact
    actualDynamicBoundaryExplicitFormulaResidual_targetAmplitudeNegligible
      hbeta hsigma hsigmaOne hheightUpper hheightTendsto halpha hepsilon
      hmargin hpositiveRightEdge hrealRightEdge remainderCertificate

end PrimeNumberTheorem
