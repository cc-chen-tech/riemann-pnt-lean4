import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryMonotoneEndToEndSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualDynamicBoundaryAutomaticCoefficientCap

/-!
# Monotone moving upper bound and signed Omega unified transfer

The coefficient-mass upper argument is generalized from a fixed boundary
exponent to the pointwise moving exponent.  It shares the complete automatic
explicit-formula residual with the signed lower transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Eventual coefficient-mass cap for the pointwise moving boundary package. -/
def VariableBoundaryPackageCoefficientCap
    (H beta : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    finiteVisibleClusterCoefficientMass
      (variableBoundaryZeroPackage H beta (m : ℝ)) ≤ C

/-- The global Carlson positive weight plus the finite real-ordinate mass caps
every eventually right-shifted moving boundary package. -/
theorem actualCarlsonVariableBoundaryCoefficientCap
    {sigma beta0 : ℝ} {H beta : ℝ → ℝ}
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hsigmaBeta0 : sigma < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ)) :
    VariableBoundaryPackageCoefficientCap H beta
      (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma) := by
  filter_upwards [hbetaLower] with m hbetaM
  have hsigmaBetaM : sigma < beta (m : ℝ) :=
    hsigmaBeta0.trans_le hbetaM
  simpa [variableBoundaryZeroPackage,
    dynamicEqualRealPartZeroPackage] using
    finiteVisibleClusterCoefficientMass_dynamicEqualRealPartZeroPackage_le
      (beta := beta (m : ℝ)) hhalf hone hsigmaBetaM H (m : ℝ)

/-- A variable-target negligible residual and a moving package coefficient cap
give the matching eventual relative PNT upper bound. -/
theorem eventually_abs_relativeChebyshevPsi0Error_lt_variableBoundaryCap_add
    {C eta : ℝ} {H beta : ℝ → ℝ}
    (heta : 0 < eta)
    (hcap : VariableBoundaryPackageCoefficientCap H beta C)
    (hresidual :
      NaturalPointTargetAmplitudeNegligible
        (fun m : ℕ => variableBoundaryTargetAmplitude beta (m : ℝ))
        (fun m : ℕ =>
          relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (C + eta) * variableBoundaryTargetAmplitude beta (m : ℝ) := by
  have hamplitude := eventually_variableBoundaryTargetAmplitude_pos beta
  have hremainder :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hresidual heta
  filter_upwards
      [eventually_ge_atTop (1 : ℕ), hcap, hamplitude, hremainder] with
      m hm hcapM hamplitudeM hremainderM
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpackageRe :
      ∀ rho ∈ variableBoundaryZeroPackage H beta (m : ℝ),
        rho.re ≤ beta (m : ℝ) := by
    intro rho hrho
    exact (mem_variableBoundaryZeroPackage.mp hrho).2.2.le
  have hmain :=
    abs_dynamicVisibleClusterPNTMain_le_coefficientMass_mul_targetAmplitude
      H (variableBoundaryZeroPackage H beta (m : ℝ))
        hmReal hpackageRe
  have hmainCap :
      |dynamicVisibleClusterPNTMain H
          (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| ≤
        C * variableBoundaryTargetAmplitude beta (m : ℝ) := by
    have hmain' :
        |dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| ≤
          finiteVisibleClusterCoefficientMass
              (variableBoundaryZeroPackage H beta (m : ℝ)) *
            variableBoundaryTargetAmplitude beta (m : ℝ) := by
      simpa [variableBoundaryTargetAmplitude] using hmain
    exact hmain'.trans
      (mul_le_mul_of_nonneg_right hcapM hamplitudeM.le)
  calc
    |relativeChebyshevPsi0Error (m : ℝ)| =
        |dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ) +
            (relativeChebyshevPsi0Error (m : ℝ) -
              dynamicVisibleClusterPNTMain H
                (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))| := by
      congr 1
      ring
    _ ≤
        |dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| +
          |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| :=
      abs_add_le _ _
    _ <
        C * variableBoundaryTargetAmplitude beta (m : ℝ) +
          eta * variableBoundaryTargetAmplitude beta (m : ℝ) :=
      add_lt_add_of_le_of_lt hmainCap hremainderM
    _ = (C + eta) *
          variableBoundaryTargetAmplitude beta (m : ℝ) := by ring

/-- One moving explicit-formula setup simultaneously gives an automatic
relative PNT upper bound and, from two signed package witnesses, a conditional
unnormalized `Omega±` conclusion. -/
theorem
    actualMonotoneVariableBoundaryUnifiedUpperSignedOmega
    {sigma beta0 alpha epsilon eta c loss : ℝ} {H beta : ℝ → ℝ}
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hbeta0 : 0 < beta0)
    (hbetaLower : ∀ᶠ m : ℕ in atTop, beta0 ≤ beta (m : ℝ))
    (hbetaMono : Monotone (fun m : ℕ => beta (m : ℝ)))
    (hHle :
      ∀ᶠ m : ℕ in atTop,
        H (m : ℝ) ≤ carlsonPolynomialHeight alpha (m : ℝ))
    (hHtop : Tendsto (fun m : ℕ => H (m : ℝ)) atTop atTop)
    (halpha : 0 < alpha)
    (hepsilon : 0 < epsilon)
    (hmargin : sigma - beta0 + alpha + epsilon < 0)
    (hrightReal :
      ∀ rho ∈ realOrdinateNontrivialZerosFinset 0, rho.re < beta0)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (hright :
      IsIndexedVariableBoundaryVisibleRightEdge (sigma := sigma) H beta)
    (remainder :
      ActualSelectedHeightNaturalPointRemainderCertificate beta0 H)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          variableBoundaryTargetAmplitude beta (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta x) := by
  have hsigmaBeta0 : sigma < beta0 := by linarith
  have hgap :=
    variableBoundaryAbsorptionOrGap_of_monotone hHtop hbetaMono hright
  have hresidual :=
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_automaticZeroTails
      hbeta0 hbetaLower hHle hHtop halpha hepsilon hmargin
        hrightReal hhalf hone hright hgap remainder
  have hupper :=
    eventually_abs_relativeChebyshevPsi0Error_lt_variableBoundaryCap_add
      heta
      (actualCarlsonVariableBoundaryCoefficientCap
        hhalf hone hsigmaBeta0 hbetaLower)
      hresidual
  have hlower :=
    actualMonotoneVariableBoundaryAutomaticZeroTails_unnormalizedSignedOmega
      hloss hlossC hbeta0 hbetaLower hbetaMono hHle hHtop halpha
        hepsilon hmargin hrightReal hhalf hone hright remainder
          hmainPos hmainNeg
  exact ⟨hupper, hlower.1, hlower.2⟩

end PrimeNumberTheorem
