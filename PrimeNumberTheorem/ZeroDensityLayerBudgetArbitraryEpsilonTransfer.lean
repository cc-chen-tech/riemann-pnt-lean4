import PrimeNumberTheorem.ZeroDensityLayerBudgetSharpConstantTransfer

/-!
# Arbitrary-epsilon explicit-formula transfer

The fixed half-amplitude remainder used by the first concrete transfer is only
a convenient specialization.  Since all three actual remainder components
are negligible relative to the target zero-power amplitude, their sum is
eventually smaller than `epsilon` times that amplitude for every positive
`epsilon`.

This yields an arbitrarily small constant loss when a finite zero-cluster
oscillation bound is transferred to the genuine PNT error.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
Three natural-point remainders negligible relative to the same eventually
positive amplitude have sum smaller than `epsilon * amplitude` for every
positive `epsilon`.
-/
theorem eventually_abs_naturalPoint_three_remainders_lt_mul
    {amplitude realAxis contour complement : ℕ → ℝ}
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    (hrealAxis :
      NaturalPointTargetAmplitudeNegligible amplitude realAxis)
    (hcontour :
      NaturalPointTargetAmplitudeNegligible amplitude contour)
    (hcomplement :
      NaturalPointTargetAmplitudeNegligible amplitude complement) :
    ∀ᶠ m : ℕ in atTop,
      |realAxis m + contour m + complement m| <
        epsilon * amplitude m := by
  have hepsilonThird : 0 < epsilon / 3 := div_pos hepsilon (by norm_num)
  have hrealRatio :=
    (Metric.tendsto_nhds.1 hrealAxis)
      (epsilon / 3) hepsilonThird
  have hcontourRatio :=
    (Metric.tendsto_nhds.1 hcontour)
      (epsilon / 3) hepsilonThird
  have hcomplementRatio :=
    (Metric.tendsto_nhds.1 hcomplement)
      (epsilon / 3) hepsilonThird
  filter_upwards
      [hamplitude, hrealRatio, hcontourRatio, hcomplementRatio] with
      m hamp hreal hcontour hcomplement
  have hrealNonneg :
      0 ≤ |realAxis m| / amplitude m :=
    div_nonneg (abs_nonneg _) hamp.le
  have hcontourNonneg :
      0 ≤ |contour m| / amplitude m :=
    div_nonneg (abs_nonneg _) hamp.le
  have hcomplementNonneg :
      0 ≤ |complement m| / amplitude m :=
    div_nonneg (abs_nonneg _) hamp.le
  have hrealRatio' :
      |realAxis m| / amplitude m < epsilon / 3 := by
    simpa [Real.dist_eq, abs_of_nonneg hrealNonneg,
      abs_of_pos hamp] using hreal
  have hcontourRatio' :
      |contour m| / amplitude m < epsilon / 3 := by
    simpa [Real.dist_eq, abs_of_nonneg hcontourNonneg,
      abs_of_pos hamp] using hcontour
  have hcomplementRatio' :
      |complement m| / amplitude m < epsilon / 3 := by
    simpa [Real.dist_eq, abs_of_nonneg hcomplementNonneg,
      abs_of_pos hamp] using hcomplement
  have hrealAbs :
      |realAxis m| < (epsilon / 3) * amplitude m :=
    (div_lt_iff₀ hamp).mp hrealRatio'
  have hcontourAbs :
      |contour m| < (epsilon / 3) * amplitude m :=
    (div_lt_iff₀ hamp).mp hcontourRatio'
  have hcomplementAbs :
      |complement m| < (epsilon / 3) * amplitude m :=
    (div_lt_iff₀ hamp).mp hcomplementRatio'
  calc
    |realAxis m + contour m + complement m| ≤
        |realAxis m| + |contour m| + |complement m| := by
      calc
        |realAxis m + contour m + complement m| ≤
            |realAxis m + contour m| + |complement m| :=
          abs_add_le _ _
        _ ≤ |realAxis m| + |contour m| + |complement m| :=
          by
            simpa [add_comm, add_left_comm, add_assoc] using
              (add_le_add_right
                (abs_add_le (realAxis m) (contour m))
                |complement m|)
    _ < epsilon * amplitude m := by
      nlinarith

/--
For every positive `epsilon`, the genuine relative PNT error differs from the
visible zero-cluster main term by less than `epsilon` times the target
zero-power amplitude at all sufficiently large natural points.
-/
theorem
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
    {beta epsilon : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hepsilon : 0 < epsilon)
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
        epsilon * targetZeroPowerAmplitude beta (m : ℝ) := by
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
    change
      ActualSelectedHeightNaturalPointRemainderCertificate beta
        (selectedUniformGoodHeight alpha selection)
    exact selectedUniformGoodHeight_actualNaturalRemainderCertificate
      hbeta halpha halphaOne hmargin selection
  have hresidual :
      ∀ᶠ m : ℕ in atTop,
        |actualPNTClosedRealAxisRelativeTerm (m : ℝ) +
            actualPNTExplicitFormulaRelativeRemainder H (m : ℝ) +
            dynamicOutsideClusterPNTComplement H S (m : ℝ)| <
          epsilon * targetZeroPowerAmplitude beta (m : ℝ) :=
    eventually_abs_naturalPoint_three_remainders_lt_mul
      hepsilon
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
          epsilon * targetZeroPowerAmplitude beta (m : ℝ) := by
    filter_upwards [hresidual] with m hsmall
    rw [relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
      H S (m : ℝ)]
    simpa only [add_sub_cancel_left] using hsmall
  simpa [H] using happrox

/--
Arbitrarily sharp transfer from a visible zero-cluster lower witness to the
actual relative PNT error.

For any `0 < epsilon < c`, a main-cluster coefficient `c` transfers to the
strictly positive coefficient `c - epsilon`.
-/
theorem
    actualWeightedBalancedGoodHeightPNTArbitraryEpsilonSharpConstantTransfer
    {beta c epsilon : ℝ}
    (hbeta : 0 < beta)
    (hbetaOne : beta < 1)
    (hepsilon : 0 < epsilon)
    (hepsilonC : epsilon < c)
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
        rho.re < beta)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m =>
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S
            (m : ℝ))
        (fun m => c * targetZeroPowerAmplitude beta (m : ℝ))) :
    0 < c - epsilon ∧
      HasFarTargetAmplitudeWitness
        relativeChebyshevPsi0Error
        (fun x => (c - epsilon) * targetZeroPowerAmplitude beta x) := by
  have happrox :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
      hbeta hbetaOne hepsilon sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have hnatural :=
    hmain.transfer_eventually_sub_lt happrox
  exact ⟨sub_pos.mpr hepsilonC, hnatural.toReal⟩

end PrimeNumberTheorem
