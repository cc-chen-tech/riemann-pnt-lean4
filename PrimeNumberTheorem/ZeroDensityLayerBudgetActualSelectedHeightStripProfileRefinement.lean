import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightStripRefinement

/-!
# Cross-cardinality finite-strip profile refinement

Splitting a coarse strip into several finer strips changes the index type and
may change both lower and upper endpoints.  Pointwise comparison on a fixed
`Fin n` is therefore insufficient.

This module gives a scalar refinement certificate between arbitrary nonempty
finite strip profiles.  Every refined threshold must lie below the coarse
bottleneck, and every refined alpha ceiling must lie above the coarse common
ceiling.  These conditions imply improved feasibility and optimal robustness
without requiring a map between the two index types.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- A finite bottleneck lies below a scalar exactly when every strip threshold
does. -/
theorem actualSelectedHeightFiniteStripBottleneck_le_iff
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) (bound : ℝ) :
    actualSelectedHeightFiniteStripBottleneck sigma tau ≤ bound ↔
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) ≤ bound := by
  let thresholds :=
    Finset.univ.image fun i =>
      carlsonStripEndpointTargetThreshold (sigma i) (tau i)
  change thresholds.max' (Finset.univ_nonempty.image _) ≤ bound ↔ _
  rw [Finset.max'_le_iff]
  constructor
  · intro h i
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro h value hvalue
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
    exact h i

/-- A scalar lies below the common finite alpha ceiling exactly when it lies
below every strip ceiling. -/
theorem le_actualSelectedHeightFiniteStripAlphaCeiling_iff
    {beta : ℝ} {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ) (bound : ℝ) :
    bound ≤ actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau ↔
      ∀ i,
        bound ≤
          actualSelectedHeightStripAlphaCeiling
            beta (sigma i) (tau i) := by
  let ceilings :=
    Finset.univ.image fun i =>
      actualSelectedHeightStripAlphaCeiling beta (sigma i) (tau i)
  change bound ≤ ceilings.min' (Finset.univ_nonempty.image _) ↔ _
  rw [Finset.le_min'_iff]
  constructor
  · intro h i
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro h value hvalue
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
    exact h i

/-- Certificate that an arbitrary nonempty finite strip profile refines
another for both endpoint feasibility and truncation robustness. -/
structure ActualSelectedHeightFiniteStripProfileRefinement
    {nRefined nCoarse : ℕ} (beta : ℝ)
    (sigmaRefined tauRefined : Fin (nRefined + 1) → ℝ)
    (sigmaCoarse tauCoarse : Fin (nCoarse + 1) → ℝ) : Prop where
  threshold_le_coarse_bottleneck :
    ∀ i,
      carlsonStripEndpointTargetThreshold
          (sigmaRefined i) (tauRefined i) ≤
        actualSelectedHeightFiniteStripBottleneck
          sigmaCoarse tauCoarse
  coarse_ceiling_le_refined :
    ∀ i,
      actualSelectedHeightFiniteStripAlphaCeiling
          beta sigmaCoarse tauCoarse ≤
        actualSelectedHeightStripAlphaCeiling
          beta (sigmaRefined i) (tauRefined i)

/-- A cross-cardinality refinement decreases the endpoint bottleneck. -/
theorem ActualSelectedHeightFiniteStripProfileRefinement.bottleneck_mono
    {beta : ℝ} {nRefined nCoarse : ℕ}
    {sigmaRefined tauRefined : Fin (nRefined + 1) → ℝ}
    {sigmaCoarse tauCoarse : Fin (nCoarse + 1) → ℝ}
    (certificate :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigmaRefined tauRefined sigmaCoarse tauCoarse) :
    actualSelectedHeightFiniteStripBottleneck
        sigmaRefined tauRefined ≤
      actualSelectedHeightFiniteStripBottleneck
        sigmaCoarse tauCoarse :=
  (actualSelectedHeightFiniteStripBottleneck_le_iff
    sigmaRefined tauRefined
    (actualSelectedHeightFiniteStripBottleneck
      sigmaCoarse tauCoarse)).2
    certificate.threshold_le_coarse_bottleneck

/-- A cross-cardinality refinement increases the common alpha ceiling. -/
theorem ActualSelectedHeightFiniteStripProfileRefinement.alphaCeiling_mono
    {beta : ℝ} {nRefined nCoarse : ℕ}
    {sigmaRefined tauRefined : Fin (nRefined + 1) → ℝ}
    {sigmaCoarse tauCoarse : Fin (nCoarse + 1) → ℝ}
    (certificate :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigmaRefined tauRefined sigmaCoarse tauCoarse) :
    actualSelectedHeightFiniteStripAlphaCeiling
        beta sigmaCoarse tauCoarse ≤
      actualSelectedHeightFiniteStripAlphaCeiling
        beta sigmaRefined tauRefined :=
  (le_actualSelectedHeightFiniteStripAlphaCeiling_iff
    sigmaRefined tauRefined
    (actualSelectedHeightFiniteStripAlphaCeiling
      beta sigmaCoarse tauCoarse)).2
    certificate.coarse_ceiling_le_refined

/-- A cross-cardinality refinement increases the capped effective alpha
ceiling. -/
theorem
    ActualSelectedHeightFiniteStripProfileRefinement.effectiveAlphaCeiling_mono
    {beta : ℝ} {nRefined nCoarse : ℕ}
    {sigmaRefined tauRefined : Fin (nRefined + 1) → ℝ}
    {sigmaCoarse tauCoarse : Fin (nCoarse + 1) → ℝ}
    (certificate :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigmaRefined tauRefined sigmaCoarse tauCoarse) :
    actualSelectedHeightFiniteStripEffectiveAlphaCeiling
        beta sigmaCoarse tauCoarse ≤
      actualSelectedHeightFiniteStripEffectiveAlphaCeiling
        beta sigmaRefined tauRefined :=
  min_le_min le_rfl certificate.alphaCeiling_mono

/-- Feasibility of the coarse profile transfers to every certified refined
profile. -/
theorem ActualSelectedHeightFiniteStripProfileRefinement.feasible
    {beta : ℝ} {nRefined nCoarse : ℕ}
    {sigmaRefined tauRefined : Fin (nRefined + 1) → ℝ}
    {sigmaCoarse tauCoarse : Fin (nCoarse + 1) → ℝ}
    (certificate :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigmaRefined tauRefined sigmaCoarse tauCoarse)
    (hcoarse :
      actualSelectedHeightFiniteStripBottleneck
        sigmaCoarse tauCoarse < beta) :
    actualSelectedHeightFiniteStripBottleneck
        sigmaRefined tauRefined < beta :=
  certificate.bottleneck_mono.trans_lt hcoarse

/-- A cross-cardinality refinement cannot decrease the optimal balanced
robustness margin. -/
theorem ActualSelectedHeightFiniteStripProfileRefinement.robustMargin_mono
    {beta : ℝ} {nRefined nCoarse : ℕ}
    {sigmaRefined tauRefined : Fin (nRefined + 1) → ℝ}
    {sigmaCoarse tauCoarse : Fin (nCoarse + 1) → ℝ}
    (certificate :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigmaRefined tauRefined sigmaCoarse tauCoarse) :
    actualSelectedHeightFiniteStripRobustMargin beta
        sigmaCoarse tauCoarse
        (actualSelectedHeightFiniteStripBalancedExponent
          beta sigmaCoarse tauCoarse) ≤
      actualSelectedHeightFiniteStripRobustMargin beta
        sigmaRefined tauRefined
        (actualSelectedHeightFiniteStripBalancedExponent
          beta sigmaRefined tauRefined) := by
  rw [actualSelectedHeightFiniteStripBalancedExponent_robustMargin,
    actualSelectedHeightFiniteStripBalancedExponent_robustMargin]
  linarith [certificate.effectiveAlphaCeiling_mono]

end PrimeNumberTheorem
