import PrimeNumberTheorem.ZeroDensityLayerBudgetNormalizedClusterEquivalence

/-!
# Empty-cluster PNT upper transfer

When the visible exceptional zero cluster is empty, the normalized cluster
equivalence becomes a pure PNT upper statement: the genuine relative
Chebyshev error is negligible at the target zero-power scale.

All dynamic Carlson bucketing and real-ordinate zero hypotheses remain
explicit inputs.  This is therefore the machine-verified upper-transfer
endpoint, not an unconditional zero-free theorem.
-/

open scoped Topology

namespace PrimeNumberTheorem

open Filter

/--
A natural-point remainder negligible relative to an eventually positive
amplitude is eventually smaller than `epsilon * amplitude` for every positive
`epsilon`.
-/
theorem
    NaturalPointTargetAmplitudeNegligible.eventually_abs_lt_mul
    {amplitude remainder : ℕ → ℝ}
    (hnegligible :
      NaturalPointTargetAmplitudeNegligible amplitude remainder)
    (hamplitude : ∀ᶠ m : ℕ in atTop, 0 < amplitude m)
    {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∀ᶠ m : ℕ in atTop,
      |remainder m| < epsilon * amplitude m := by
  have hratio :=
    (Metric.tendsto_nhds.1 hnegligible) epsilon hepsilon
  filter_upwards [hamplitude, hratio] with m hamp hsmall
  have hratioNonneg :
      0 ≤ |remainder m| / amplitude m :=
    div_nonneg (abs_nonneg _) hamp.le
  have hratio' :
      |remainder m| / amplitude m < epsilon := by
    simpa [Real.dist_eq, abs_of_nonneg hratioNonneg,
      abs_of_pos hamp] using hsmall
  exact (div_lt_iff₀ hamp).mp hratio'

/--
With no visible exceptional cluster, the actual relative PNT error is
negligible relative to the target zero-power amplitude at the selected
weighted balanced good height.
-/
theorem
    actualWeightedBalancedGoodHeightEmptyClusterPNTError_targetAmplitudeNegligible
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
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (∅ : Finset ℂ)
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈
          realOrdinateNontrivialZerosOutsideClusterFinset
            0
            (∅ : Finset ℂ),
        rho.re < beta) :
    NaturalPointTargetAmplitudeNegligible
      (fun m => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m => relativeChebyshevPsi0Error (m : ℝ)) := by
  have hS :
      IsConjugationInvariantCluster (∅ : Finset ℂ) := by
    simp [IsConjugationInvariantCluster]
  have hnegligible :=
    actualWeightedBalancedGoodHeightPNTClusterDifference_targetAmplitudeNegligible
      hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
      input kappa hS hfixedSigma hkappa hnorm hre hreal
  simpa [dynamicVisibleClusterPNTMain,
    dynamicVisibleClusterPNTZeroSum] using hnegligible

/--
Pure quantitative PNT upper transfer for an empty visible cluster: for every
positive `epsilon`, the actual relative error is eventually at most
`epsilon` times the target zero-power amplitude.
-/
theorem
    eventually_abs_relativeChebyshevPsi0Error_lt_epsilon_mul_targetAmplitude_of_emptyCluster
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
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            beta sigma tau selection x)
          (∅ : Finset ℂ)
          (n + 1))
    (kappa : Fin (n + 1) → ℝ)
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hkappa : ∀ i, 0 < kappa i)
    (hnorm :
      ∀ i x rho, rho ∈ (input x).layer i → kappa i ≤ ‖rho‖)
    (hre :
      ∀ i x rho, rho ∈ (input x).layer i → rho.re ≤ tau i)
    (hreal :
      ∀ rho ∈
          realOrdinateNontrivialZerosOutsideClusterFinset
            0
            (∅ : Finset ℂ),
        rho.re < beta) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        epsilon * targetZeroPowerAmplitude beta (m : ℝ) := by
  have hnegligible :=
    actualWeightedBalancedGoodHeightEmptyClusterPNTError_targetAmplitudeNegligible
      hbeta hbetaOne sigma tau hsigma hsigmaOne htau hthreshold selection
      input kappa hfixedSigma hkappa hnorm hre hreal
  exact
    hnegligible.eventually_abs_lt_mul
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      hepsilon

end PrimeNumberTheorem
