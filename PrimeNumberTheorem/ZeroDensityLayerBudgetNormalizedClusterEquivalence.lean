import PrimeNumberTheorem.ZeroDensityLayerBudgetArbitrarilySharpSameFormulaBounds

/-!
# Target-normalized cluster equivalence

The actual relative PNT error and the visible finite zero-cluster main term are
asymptotically equivalent at the target zero-power scale.  This file packages
that statement in the repository's standard
`NaturalPointTargetAmplitudeNegligible` interface and derives convergence of
their normalized absolute magnitudes.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
If `f - g` is negligible relative to an eventually positive amplitude, then
the difference between the normalized absolute magnitudes of `f` and `g`
tends to zero.
-/
theorem
    NaturalPointTargetAmplitudeNegligible.tendsto_normalized_abs_sub
    {amplitude f g : ℕ → ℝ}
    (hnegligible :
      NaturalPointTargetAmplitudeNegligible
        amplitude
        (fun m => f m - g m))
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m) :
    Tendsto
      (fun m => |f m| / amplitude m - |g m| / amplitude m)
      atTop
      (nhds 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have hratio :=
    (Metric.tendsto_nhds.1 hnegligible) epsilon hepsilon
  filter_upwards [hamplitude, hratio] with m hamp hsmall
  have hratioNonneg :
      0 ≤ |f m - g m| / amplitude m :=
    div_nonneg (abs_nonneg _) hamp.le
  have hratio' :
      |f m - g m| / amplitude m < epsilon := by
    simpa [Real.dist_eq, abs_of_nonneg hratioNonneg,
      abs_of_pos hamp] using hsmall
  calc
    dist
        (|f m| / amplitude m - |g m| / amplitude m)
        0 =
        abs (|f m| - |g m|) / amplitude m := by
      rw [Real.dist_eq, sub_zero, ← sub_div, abs_div, abs_of_pos hamp]
    _ ≤ |f m - g m| / amplitude m :=
      div_le_div_of_nonneg_right
        (abs_abs_sub_abs_le_abs_sub (f m) (g m))
        hamp.le
    _ < epsilon := hratio'

/--
At the selected weighted balanced good height, the difference between the
genuine relative PNT error and the visible zero-cluster main term is negligible
relative to the target zero-power amplitude.
-/
theorem
    actualWeightedBalancedGoodHeightPNTClusterDifference_targetAmplitudeNegligible
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
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m =>
        relativeChebyshevPsi0Error (m : ℝ) -
          dynamicVisibleClusterPNTMain
            (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
              beta sigma tau selection)
            S
            (m : ℝ)) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  have happrox :=
    eventually_abs_relativeChebyshevPsi0Error_sub_visibleCluster_lt_epsilon_mul_targetAmplitude
      hbeta hbetaOne hepsilon sigma tau hsigma hsigmaOne htau hthreshold
      selection input kappa hS hfixedSigma hkappa hnorm hre hreal
  have hamplitude :=
    eventually_naturalPoint_pos_of_eventually_pos
      (targetZeroPowerAmplitude_eventually_pos beta)
  filter_upwards [happrox, hamplitude] with m hsmall hamp
  have hratioNonneg :
      0 ≤
        |relativeChebyshevPsi0Error (m : ℝ) -
            dynamicVisibleClusterPNTMain
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S
              (m : ℝ)| /
          targetZeroPowerAmplitude beta (m : ℝ) :=
    div_nonneg (abs_nonneg _) hamp.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hratioNonneg]
  exact (div_lt_iff₀ hamp).2 hsmall

/--
The normalized absolute magnitude of the actual relative PNT error is
asymptotic to that of the visible zero-cluster main term at the same selected
weighted balanced good height.
-/
theorem
    tendsto_actualWeightedBalancedGoodHeightPNT_normalizedAbs_sub_cluster_zero
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
    Tendsto
      (fun m : ℕ =>
        |relativeChebyshevPsi0Error (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ) -
          |dynamicVisibleClusterPNTMain
              (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
                beta sigma tau selection)
              S
              (m : ℝ)| /
            targetZeroPowerAmplitude beta (m : ℝ))
      atTop
      (nhds 0) := by
  have hnegligible :=
    actualWeightedBalancedGoodHeightPNTClusterDifference_targetAmplitudeNegligible
      hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  exact
    hnegligible.tendsto_normalized_abs_sub
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))

end PrimeNumberTheorem
