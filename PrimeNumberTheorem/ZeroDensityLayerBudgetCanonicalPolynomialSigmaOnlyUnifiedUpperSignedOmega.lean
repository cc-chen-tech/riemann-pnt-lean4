import PrimeNumberTheorem.ZeroDensityLayerBudgetCanonicalPolynomialRunningBoundaryUnifiedUpperSignedOmega
import PrimeNumberTheorem.ZeroDensityLayerBudgetDynamicCarlsonAutomaticBetaPNTTransfer

/-!
# Optimized sigma-only canonical polynomial transfer

The exact critical-half obstruction `(1 + sigma) / 2` is combined with the
finite real-ordinate zero bottleneck. Their maximum determines an automatic
target anchor, eliminating every non-witness parameter from the canonical
running-boundary transfer.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Joint optimized obstruction from the critical-half window and fixed
real-ordinate zeros. -/
noncomputable def canonicalPolynomialSigmaOnlyBottleneck (sigma : ℝ) : ℝ :=
  max realOrdinatePNTZeroBottleneck ((1 + sigma) / 2)

/-- Automatic target anchor halfway between the optimized obstruction and
one. -/
noncomputable def canonicalPolynomialSigmaOnlyBeta0 (sigma : ℝ) : ℝ :=
  (canonicalPolynomialSigmaOnlyBottleneck sigma + 1) / 2

/-- The optimized sigma-only anchor lies in the exact canonical target region
and strictly to the right of every fixed real-ordinate nontrivial zero. -/
theorem canonicalPolynomialSigmaOnlyBeta0_spec
    {sigma : ℝ} (hone : sigma < 1) :
    (1 + sigma) / 2 < canonicalPolynomialSigmaOnlyBeta0 sigma ∧
    canonicalPolynomialSigmaOnlyBeta0 sigma < 1 ∧
    ∀ rho ∈ realOrdinateNontrivialZerosFinset 0,
      rho.re < canonicalPolynomialSigmaOnlyBeta0 sigma := by
  have hcritical : (1 + sigma) / 2 < 1 := by linarith
  have hbottleneck : canonicalPolynomialSigmaOnlyBottleneck sigma < 1 := by
    exact max_lt realOrdinatePNTZeroBottleneck_lt_one hcritical
  have hbelow :
      canonicalPolynomialSigmaOnlyBottleneck sigma <
        canonicalPolynomialSigmaOnlyBeta0 sigma := by
    unfold canonicalPolynomialSigmaOnlyBeta0
    linarith
  refine ⟨(le_max_right _ _).trans_lt hbelow, ?_, ?_⟩
  · unfold canonicalPolynomialSigmaOnlyBeta0
    linarith
  · intro rho hrho
    exact (realOrdinateNontrivialZero_re_le_bottleneck hrho).trans_lt
      ((le_max_left _ _).trans_lt hbelow)

/-- Visible running-boundary main term for the optimized sigma-only package. -/
noncomputable def canonicalPolynomialSigmaOnlyVisibleMain
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (m : ℕ) : ℝ :=
  dynamicVisibleClusterPNTMain
    (canonicalPolynomialRunningBoundaryHeight
      (canonicalPolynomialSigmaOnlyBeta0 sigma) sigma selection)
    (variableBoundaryZeroPackage
      (canonicalPolynomialRunningBoundaryHeight
        (canonicalPolynomialSigmaOnlyBeta0 sigma) sigma selection)
      (canonicalPolynomialRunningVisibleZeroBoundary
        (canonicalPolynomialSigmaOnlyBeta0 sigma) sigma selection)
      (m : ℝ))
    (m : ℝ)

/-- Running target amplitude for the optimized sigma-only package. -/
noncomputable def canonicalPolynomialSigmaOnlyAmplitude
    (sigma : ℝ) (selection : UniformNaturalPointGoodHeightSelection)
    (x : ℝ) : ℝ :=
  variableBoundaryTargetAmplitude
    (canonicalPolynomialRunningVisibleZeroBoundary
      (canonicalPolynomialSigmaOnlyBeta0 sigma) sigma selection) x

/-- Sigma-only canonical power-scale upper/signed transfer. Every parameter
and geometric certificate except the two signed anti-cancellation witnesses is
constructed automatically. -/
theorem actualCanonicalPolynomialSigmaOnlyUnifiedUpperSignedOmega
    {sigma eta c loss : ℝ}
    (selection : UniformNaturalPointGoodHeightSelection)
    (hhalf : 1 / 2 < sigma)
    (hone : sigma < 1)
    (heta : 0 < eta)
    (hloss : 0 < loss)
    (hlossC : loss < c)
    (hmainPos :
      HasFarNaturalPointPositiveTargetAmplitudeWitness
        (canonicalPolynomialSigmaOnlyVisibleMain sigma selection)
        (fun m : ℕ =>
          c * canonicalPolynomialSigmaOnlyAmplitude sigma selection (m : ℝ)))
    (hmainNeg :
      HasFarNaturalPointNegativeTargetAmplitudeWitness
        (canonicalPolynomialSigmaOnlyVisibleMain sigma selection)
        (fun m : ℕ =>
          c * canonicalPolynomialSigmaOnlyAmplitude sigma selection (m : ℝ))) :
    (∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| <
        (actualCarlsonDynamicBoundaryCoefficientCapConstant sigma + eta) *
          canonicalPolynomialSigmaOnlyAmplitude sigma selection (m : ℝ)) ∧
      0 < c - loss ∧
      HasFarSignedTargetAmplitudeWitnesses chebyshevPsi0Error
        (fun x : ℝ =>
          (c - loss) * x ^
            canonicalPolynomialRunningVisibleZeroBoundary
              (canonicalPolynomialSigmaOnlyBeta0 sigma) sigma selection x) := by
  rcases canonicalPolynomialSigmaOnlyBeta0_spec hone with
    ⟨htarget, hbetaOne, hreal⟩
  exact
    actualCanonicalPolynomialRunningBoundaryUnifiedUpperSignedOmega
      selection heta hloss hlossC hhalf htarget hbetaOne hreal
      (by simpa [canonicalPolynomialSigmaOnlyVisibleMain,
          canonicalPolynomialSigmaOnlyAmplitude] using hmainPos)
      (by simpa [canonicalPolynomialSigmaOnlyVisibleMain,
          canonicalPolynomialSigmaOnlyAmplitude] using hmainNeg)

end PrimeNumberTheorem
