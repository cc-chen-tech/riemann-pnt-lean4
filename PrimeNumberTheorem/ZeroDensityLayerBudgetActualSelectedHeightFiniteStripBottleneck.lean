import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightFiniteStripExponentFeasibility

/-!
# The bottleneck endpoint threshold of a finite strip family

For a nonempty finite Carlson strip decomposition, shared-height feasibility is
controlled by one scalar: the largest endpoint threshold among the strips.
This module defines that bottleneck, identifies a strip attaining it, and
rewrites the common-exponent criterion as one strict inequality.

The result is useful both constructively and diagnostically.  A successful
bound needs only `bottleneck < beta`; a failure exposes an actual worst strip
rather than an opaque conjunction of exponent inequalities.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- The largest endpoint threshold in a nonempty finite strip family. -/
noncomputable def actualSelectedHeightFiniteStripBottleneck
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  let thresholds :=
    Finset.univ.image fun i =>
      carlsonStripEndpointTargetThreshold (sigma i) (tau i)
  thresholds.max' (Finset.univ_nonempty.image _)

/-- Every strip threshold is bounded by the finite-family bottleneck. -/
theorem carlsonStripEndpointTargetThreshold_le_bottleneck
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    carlsonStripEndpointTargetThreshold (sigma i) (tau i) ≤
      actualSelectedHeightFiniteStripBottleneck sigma tau := by
  let thresholds :=
    Finset.univ.image fun j =>
      carlsonStripEndpointTargetThreshold (sigma j) (tau j)
  apply thresholds.le_max'
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- Some strip attains the finite-family bottleneck. -/
theorem exists_strip_eq_actualSelectedHeightFiniteStripBottleneck
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) :
    ∃ i : Fin (n + 1),
      carlsonStripEndpointTargetThreshold (sigma i) (tau i) =
        actualSelectedHeightFiniteStripBottleneck sigma tau := by
  let thresholds :=
    Finset.univ.image fun i =>
      carlsonStripEndpointTargetThreshold (sigma i) (tau i)
  have hmem :
      thresholds.max' (Finset.univ_nonempty.image _) ∈ thresholds :=
    thresholds.max'_mem _
  obtain ⟨i, _hi, hvalue⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hvalue⟩

/-- The bottleneck lies below a target exactly when every strip threshold
does. -/
theorem actualSelectedHeightFiniteStripBottleneck_lt_iff
    {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) (beta : ℝ) :
    actualSelectedHeightFiniteStripBottleneck sigma tau < beta ↔
      ∀ i,
        carlsonStripEndpointTargetThreshold (sigma i) (tau i) < beta := by
  let thresholds :=
    Finset.univ.image fun i =>
      carlsonStripEndpointTargetThreshold (sigma i) (tau i)
  change thresholds.max' (Finset.univ_nonempty.image _) < beta ↔ _
  rw [Finset.max'_lt_iff]
  constructor
  · intro h i
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  · intro h value hvalue
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
    exact h i

/-- Exact one-scalar criterion for an actual selected-height exponent shared
by a nonempty finite family of endpoint-aware Carlson strips. -/
theorem exists_actualSelectedHeightExponent_finiteStrips_decay_iff_bottleneck
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    (∃ alpha : ℝ,
        0 < alpha ∧ alpha ≤ 1 ∧ 1 - beta < alpha ∧
        ∀ i,
          targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) <
              0) ↔
      actualSelectedHeightFiniteStripBottleneck sigma tau < beta := by
  rw [exists_actualSelectedHeightExponent_finiteStrips_decay_iff
    sigma tau hbeta hbetaOne hsigma hsigmaOne]
  exact
    (actualSelectedHeightFiniteStripBottleneck_lt_iff
      sigma tau beta).symm

/-- If the target does not clear the bottleneck, no common actual
selected-height exponent exists. -/
theorem not_exists_actualSelectedHeightExponent_of_le_bottleneck
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hbetaBottleneck :
      beta ≤ actualSelectedHeightFiniteStripBottleneck sigma tau) :
    ¬ ∃ alpha : ℝ,
        0 < alpha ∧ alpha ≤ 1 ∧ 1 - beta < alpha ∧
        ∀ i,
          targetAmplitudeStripEndpointExponent beta (tau i)
            (carlsonClassicalPolynomialDensityExponent alpha (sigma i)) <
              0 := by
  intro hexists
  have hbottleneck :=
    (exists_actualSelectedHeightExponent_finiteStrips_decay_iff_bottleneck
      sigma tau hbeta hbetaOne hsigma hsigmaOne).1 hexists
  exact (not_lt_of_ge hbetaBottleneck) hbottleneck

end PrimeNumberTheorem
