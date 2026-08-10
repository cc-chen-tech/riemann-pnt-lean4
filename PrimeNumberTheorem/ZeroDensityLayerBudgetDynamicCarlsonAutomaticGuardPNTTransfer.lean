import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonAutomaticBetaPNTTransfer

/-!
# Automatic denominator guards for the dynamic Carlson PNT transfer

A positive-zero bucket already places every zero strictly to the right of its
strip threshold.  Since the complex norm dominates the absolute real part,
the strip threshold itself is a valid denominator guard.  This removes the
external `kappa`, positivity, and norm-lower-bound inputs from the automatic
target-exponent PNT transfer.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- A fixed positive-zero strip threshold is automatically a lower bound for
the norm of every zero in that strip. -/
theorem PositiveZeroBucketInput.externalSigma_lt_norm
    {T : ℝ} {n : ℕ} (input : PositiveZeroBucketInput T n)
    (sigma : Fin n → ℝ)
    (hfixedSigma : ∀ i, input.sigma i = sigma i)
    (i : Fin n) {rho : ℂ} (hrho : rho ∈ input.layer i) :
    sigma i < ‖rho‖ := by
  have hlayer := Finset.mem_filter.mp hrho
  have hre : sigma i < rho.re := by
    rw [← hfixedSigma i]
    simpa [hlayer.2] using input.sigma_lt_re rho hlayer.1
  exact
    hre.trans_le
      ((le_abs_self rho.re).trans (Complex.abs_re_le_norm rho))

/-- The automatic target-exponent transfer with the denominator guard chosen
canonically as the strip threshold. -/
theorem relativeChebyshevPsi0Error_natural_dynamicCarlsonAutomaticGuard_negligible
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            (dynamicCarlsonAutomaticTargetBeta sigma tau)
            sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    NaturalPointTargetAmplitudeNegligible
      (fun m =>
        targetZeroPowerAmplitude
          (dynamicCarlsonAutomaticTargetBeta sigma tau) (m : ℝ))
      (fun m => relativeChebyshevPsi0Error (m : ℝ)) := by
  apply
    relativeChebyshevPsi0Error_natural_dynamicCarlsonAutomaticBeta_negligible
      sigma tau sigma hsigma hsigmaOne htau hthresholdOne
      selection input hfixedSigma
  · intro i
    linarith [hsigma i]
  · intro i x rho hrho
    exact
      ((input x).externalSigma_lt_norm sigma
        (fun j => hfixedSigma j x) i hrho).le
  · exact hre

/-- Consequently, the actual natural-point relative Chebyshev error tends to
zero without an externally supplied denominator guard. -/
theorem tendsto_relativeChebyshevPsi0Error_natural_dynamicCarlsonAutomaticGuard
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, 0 ≤ tau i)
    (hthresholdOne :
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < 1)
    (selection : UniformNaturalPointGoodHeightSelection)
    (input :
      (x : ℝ) →
        PositiveZeroBucketInput
          (actualSelectedHeightFiniteStripWeightedBalancedGoodHeight
            (dynamicCarlsonAutomaticTargetBeta sigma tau)
            sigma tau selection x)
          (n + 1))
    (hfixedSigma : ∀ i x, (input x).sigma i = sigma i)
    (hre :
      ∀ i x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau i) :
    Filter.Tendsto
      (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
      Filter.atTop (nhds 0) := by
  apply
    tendsto_relativeChebyshevPsi0Error_natural_dynamicCarlsonAutomaticBeta
      sigma tau sigma hsigma hsigmaOne htau hthresholdOne
      selection input hfixedSigma
  · intro i
    linarith [hsigma i]
  · intro i x rho hrho
    exact
      ((input x).externalSigma_lt_norm sigma
        (fun j => hfixedSigma j x) i hrho).le
  · exact hre

end PrimeNumberTheorem
