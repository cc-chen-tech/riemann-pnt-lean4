import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedGoodHeightSameFormulaUpper

/-!
# Target-normalized visible-cluster approximation

At the actual selected weighted balanced good height, the real-axis term, the
contour remainder, and the Carlson-controlled signed zero complement are
jointly smaller than half of the target zero-power amplitude.  Consequently
the genuine relative Chebyshev error differs from the visible finite zero
cluster main term by less than that same half-amplitude.

This is the quantitative bridge needed by any separate finite-cluster
anti-cancellation theorem.  It does not itself prove anti-cancellation.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
At the selected weighted balanced good height, the actual relative PNT error
tracks the visible zero-cluster main term to strictly less than half of the
target amplitude at all sufficiently large natural points.
-/
theorem
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_half_targetAmplitude
    {beta : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthreshold :
      ∀ i, carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta)
    (selection : UniformNaturalPointGoodHeightSelection)
    {S : Finset ℂ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          S
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hS : IsConjugationInvariantCluster S)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈ realOrdinateNontrivialZerosOutsideClusterFinset 0 S,
        rho.re < beta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S
            (m : ℝ)| <
        targetZeroPowerAmplitude beta (m : ℝ) / 2 := by
  let alpha :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  let H :=
    actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
      beta sigma tau selection
  have hspec :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_spec
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold
  have halpha : 0 < alpha := hspec.2.1
  have halphaOne : alpha ≤ 1 := hspec.2.2.1.le
  have hmargin : 1 - beta < alpha := hspec.2.2.2.1
  let carlsonCertificate :=
    actualCarlsonOutsideClusterWeightedBalancedGoodHeightFiniteStripCertificate
      sigma tau hbetaOne hsigma hsigmaOne htau hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  have remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H := by
    simpa [H, alpha,
      actualSelectedHeightFiniteStripWeightedBalancedGoodHeight] using
      selectedUniformGoodHeight_actualNaturalRemainderCertificate
        hbeta halpha halphaOne hmargin selection
  have hresidual :
      ∀ᶠ m : ℕ in atTop,
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
            actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H S (m : ℝ)| <
          targetZeroPowerAmplitude beta (m : ℝ) / 2 :=
    eventually_abs_naturalPoint_three_remainders_lt_half
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible
        hbeta).naturalPoint
      remainderCertificate.negligible
      (carlsonCertificate.actualSignedComplementCertificate
        |>.complement_negligible
        |>.naturalPoint)
  have happrox :
      ∀ᶠ m : ℕ in atTop,
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain H S (m : ℝ)| <
          targetZeroPowerAmplitude beta (m : ℝ) / 2 := by
    filter_upwards [hresidual] with m hsmall
    rw [relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
      H S (m : ℝ)]
    simpa only [add_sub_cancel_left] using hsmall
  simpa [H] using happrox

end PrimeNumberTheorem
