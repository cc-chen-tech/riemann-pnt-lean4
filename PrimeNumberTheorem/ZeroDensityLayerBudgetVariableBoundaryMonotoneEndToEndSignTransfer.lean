import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryEndToEndSignTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetVariableBoundaryMonotoneAbsorptionGap

/-!
# Monotone variable-boundary end-to-end PNT sign transfer

Monotonicity of the sampled moving boundary makes the per-zero
absorption-or-gap condition automatic.  The complete analytic transfer can
therefore be stated using only concrete schedule properties.
-/

namespace PrimeNumberTheorem

open Filter Topology

theorem
    actualMonotoneVariableBoundaryAutomaticZeroTails_unnormalizedSignAlternativeTransfer
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
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ =>
          dynamicVisibleClusterPNTMain H
            (variableBoundaryZeroPackage H beta (m : ℝ)) (m : ℝ))
        (fun m : ℕ =>
          c * variableBoundaryTargetAmplitude beta (m : ℝ))) :
    0 < c - loss ∧
      ((HasFarPositiveTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ beta x)) ∨
        HasFarNegativeTargetAmplitudeWitness chebyshevPsi0Error
          (fun x : ℝ => (c - loss) * x ^ beta x)) := by
  apply
    actualVariableBoundaryAutomaticZeroTails_unnormalizedSignAlternativeTransfer
      hloss hlossC hbeta0 hbetaLower hHle hHtop halpha hepsilon
        hmargin hrightReal hhalf hone hright
  · exact variableBoundaryAbsorptionOrGap_of_monotone
      hHtop hbetaMono hright
  · exact remainder
  · exact hmain

end PrimeNumberTheorem
