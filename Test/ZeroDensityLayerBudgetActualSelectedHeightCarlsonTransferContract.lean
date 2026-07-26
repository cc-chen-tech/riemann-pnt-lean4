import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightCarlsonTransfer

open Filter

namespace PrimeNumberTheorem

example {alpha x T : ℝ}
    (hT :
      T ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
        (actualCarlsonPolynomialGoodHeightBase alpha x + 1)) :
    T ≤ carlsonPolynomialHeight alpha x :=
  goodHeightInterval_le_carlsonPolynomialHeight hT

example {alpha : ℝ} {H : ℝ → ℝ}
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
          (actualCarlsonPolynomialGoodHeightBase alpha x + 1)) :
    ∀ᶠ x : ℝ in atTop,
      H x ≤ carlsonPolynomialHeight alpha x :=
  eventually_selectedHeight_le_carlsonPolynomialHeight hH

example {H : ℝ → ℝ}
    {beta sigma tau alpha kappa epsilon : ℝ}
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ≤ carlsonPolynomialHeight alpha x)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) (hkappa : 0 ≤ kappa)
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    Tendsto
      (fun x =>
        dynamicCarlsonLayerCount sigma H x *
            stripEndpointRelativeKernelBudget kappa tau x /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) :=
  tendsto_selectedDynamicCarlsonCount_mul_stripEndpoint_div_targetAmplitude
    hH hsigma hsigmaOne halpha hkappa hepsilon hmargin

example
    {n : ℕ} {S : Finset ℂ} {H : ℝ → ℝ}
    {beta sigma tau alpha kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n)
    (i : Fin n)
    (hfixedSigma : ∀ x, (input x).sigma i = sigma)
    (hH :
      ∀ᶠ x : ℝ in atTop,
        H x ∈ Set.Icc (actualCarlsonPolynomialGoodHeightBase alpha x)
          (actualCarlsonPolynomialGoodHeightBase alpha x + 1))
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) (hkappa : 0 < kappa)
    (hnorm :
      ∀ x, ∀ rho ∈ (input x).layer i, kappa ≤ ‖rho‖)
    (hre :
      ∀ x, ∀ rho ∈ (input x).layer i, rho.re ≤ tau)
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    PintzCarlsonTargetLayerBudget
      (targetZeroPowerAmplitude beta)
      (dynamicPositiveOutsideClusterPNTLayerNorm H S input i)
      (dynamicCarlsonLayerCount sigma H)
      (stripEndpointRelativeKernelBudget kappa tau) :=
  actualZetaOutsideClusterStrip_goodHeight_carlsonTargetLayerBudget
    input i hfixedSigma hH hsigma hsigmaOne halpha hkappa hnorm hre
      hepsilon hmargin

end PrimeNumberTheorem
