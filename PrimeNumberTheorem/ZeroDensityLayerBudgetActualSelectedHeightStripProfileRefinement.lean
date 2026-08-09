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

/-- Every nonempty finite strip profile refines itself. -/
theorem ActualSelectedHeightFiniteStripProfileRefinement.refl
    (beta : ℝ) {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ) :
    ActualSelectedHeightFiniteStripProfileRefinement beta
      sigma tau sigma tau where
  threshold_le_coarse_bottleneck :=
    carlsonStripEndpointTargetThreshold_le_bottleneck sigma tau
  coarse_ceiling_le_refined :=
    (le_actualSelectedHeightFiniteStripAlphaCeiling_iff
      sigma tau
      (actualSelectedHeightFiniteStripAlphaCeiling
        beta sigma tau)).1 le_rfl

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

/-- Cross-cardinality finite-strip refinement is transitive. -/
theorem ActualSelectedHeightFiniteStripProfileRefinement.trans
    {beta : ℝ} {nFine nMiddle nCoarse : ℕ}
    {sigmaFine tauFine : Fin (nFine + 1) → ℝ}
    {sigmaMiddle tauMiddle : Fin (nMiddle + 1) → ℝ}
    {sigmaCoarse tauCoarse : Fin (nCoarse + 1) → ℝ}
    (fineMiddle :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigmaFine tauFine sigmaMiddle tauMiddle)
    (middleCoarse :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigmaMiddle tauMiddle sigmaCoarse tauCoarse) :
    ActualSelectedHeightFiniteStripProfileRefinement beta
      sigmaFine tauFine sigmaCoarse tauCoarse where
  threshold_le_coarse_bottleneck := fun i =>
    (fineMiddle.threshold_le_coarse_bottleneck i).trans
      middleCoarse.bottleneck_mono
  coarse_ceiling_le_refined := fun i =>
    middleCoarse.alphaCeiling_mono.trans
      (fineMiddle.coarse_ceiling_le_refined i)

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

/-- Mutual refinement forces equality of endpoint bottlenecks. -/
theorem
    ActualSelectedHeightFiniteStripProfileRefinement.bottleneck_eq_of_mutual
    {beta : ℝ} {n₁ n₂ : ℕ}
    {sigma₁ tau₁ : Fin (n₁ + 1) → ℝ}
    {sigma₂ tau₂ : Fin (n₂ + 1) → ℝ}
    (h₁₂ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₁ tau₁ sigma₂ tau₂)
    (h₂₁ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₂ tau₂ sigma₁ tau₁) :
    actualSelectedHeightFiniteStripBottleneck sigma₁ tau₁ =
      actualSelectedHeightFiniteStripBottleneck sigma₂ tau₂ :=
  le_antisymm h₁₂.bottleneck_mono h₂₁.bottleneck_mono

/-- Mutual refinement forces equality of common alpha ceilings. -/
theorem
    ActualSelectedHeightFiniteStripProfileRefinement.alphaCeiling_eq_of_mutual
    {beta : ℝ} {n₁ n₂ : ℕ}
    {sigma₁ tau₁ : Fin (n₁ + 1) → ℝ}
    {sigma₂ tau₂ : Fin (n₂ + 1) → ℝ}
    (h₁₂ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₁ tau₁ sigma₂ tau₂)
    (h₂₁ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₂ tau₂ sigma₁ tau₁) :
    actualSelectedHeightFiniteStripAlphaCeiling beta sigma₁ tau₁ =
      actualSelectedHeightFiniteStripAlphaCeiling beta sigma₂ tau₂ :=
  le_antisymm h₂₁.alphaCeiling_mono h₁₂.alphaCeiling_mono

/-- Mutual refinement forces equality of capped effective alpha ceilings. -/
theorem
    ActualSelectedHeightFiniteStripProfileRefinement.effectiveAlphaCeiling_eq_of_mutual
    {beta : ℝ} {n₁ n₂ : ℕ}
    {sigma₁ tau₁ : Fin (n₁ + 1) → ℝ}
    {sigma₂ tau₂ : Fin (n₂ + 1) → ℝ}
    (h₁₂ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₁ tau₁ sigma₂ tau₂)
    (h₂₁ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₂ tau₂ sigma₁ tau₁) :
    actualSelectedHeightFiniteStripEffectiveAlphaCeiling beta sigma₁ tau₁ =
      actualSelectedHeightFiniteStripEffectiveAlphaCeiling beta sigma₂ tau₂ :=
  le_antisymm h₂₁.effectiveAlphaCeiling_mono
    h₁₂.effectiveAlphaCeiling_mono

/-- Mutual refinement forces equality of optimal balanced robustness
margins. -/
theorem
    ActualSelectedHeightFiniteStripProfileRefinement.robustMargin_eq_of_mutual
    {beta : ℝ} {n₁ n₂ : ℕ}
    {sigma₁ tau₁ : Fin (n₁ + 1) → ℝ}
    {sigma₂ tau₂ : Fin (n₂ + 1) → ℝ}
    (h₁₂ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₁ tau₁ sigma₂ tau₂)
    (h₂₁ :
      ActualSelectedHeightFiniteStripProfileRefinement beta
        sigma₂ tau₂ sigma₁ tau₁) :
    actualSelectedHeightFiniteStripRobustMargin beta sigma₁ tau₁
        (actualSelectedHeightFiniteStripBalancedExponent beta sigma₁ tau₁) =
      actualSelectedHeightFiniteStripRobustMargin beta sigma₂ tau₂
        (actualSelectedHeightFiniteStripBalancedExponent beta sigma₂ tau₂) :=
  le_antisymm h₂₁.robustMargin_mono h₁₂.robustMargin_mono

end PrimeNumberTheorem
