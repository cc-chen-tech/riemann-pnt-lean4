import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryMonotoneEndToEndSignTransfer

/-!
# Monotone variable-boundary end-to-end signed Omega

The complete automatic analytic residual is shared by independent positive
and negative moving-package witnesses.  Both signs therefore survive with one
common coefficient loss and the exact unnormalized variable-exponent scale.
-/

namespace PrimeNumberTheorem

open Filter Topology

theorem
    actualMonotoneVariableBoundaryAutomaticZeroTails_unnormalizedSignedOmega
    {sigma beta0 alpha epsilon c loss : ℝ} {H beta : ℝ → ℝ}
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
    0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ => (c - loss) * x ^ beta x) := by
  have hgap : VariableBoundaryAbsorptionOrGap (sigma := sigma) H beta :=
    variableBoundaryAbsorptionOrGap_of_monotone hHtop hbetaMono hright
  have hresidual :=
    actualVariableBoundaryExplicitFormulaResidual_targetAmplitudeNegligible_automaticZeroTails
      hbeta0 hbetaLower hHle hHtop halpha hepsilon hmargin
        hrightReal hhalf hone hright hgap remainder
  have hamplitude := eventually_variableBoundaryTargetAmplitude_pos beta
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H
              (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ)| <
          loss * variableBoundaryTargetAmplitude beta (m : ℝ) :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hresidual hloss
  have hpositiveNatural :=
    hmainPos.transfer_eventually_sub_lt happrox
  have hnegativeNatural :=
    hmainNeg.transfer_eventually_sub_lt happrox
  have hpositiveRelative :
      HasFarPositiveTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * variableBoundaryTargetAmplitude beta x) :=
    hpositiveNatural.toReal
  have hnegativeRelative :
      HasFarNegativeTargetAmplitudeWitness relativeChebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * variableBoundaryTargetAmplitude beta x) :=
    hnegativeNatural.toReal
  refine ⟨sub_pos.mpr hlossC, ?_⟩
  exact
    ⟨hpositiveRelative.relativeChebyshevPsi0Error_to_unnormalized_variableExponent,
      hnegativeRelative.relativeChebyshevPsi0Error_to_unnormalized_variableExponent⟩

end PrimeNumberTheorem
