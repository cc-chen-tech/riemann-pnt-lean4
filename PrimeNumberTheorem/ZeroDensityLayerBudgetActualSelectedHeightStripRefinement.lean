import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightBalancedExponentOptimality

/-!
# Monotonic improvement under finite-strip refinement

Keeping a strip's lower density threshold `sigma` fixed while decreasing its
upper kernel endpoint `tau` is a genuine refinement.  This module proves that
such pointwise refinement:

* decreases every endpoint threshold and the finite bottleneck;
* increases every alpha ceiling and the common finite ceiling;
* increases the optimal balanced two-sided robustness margin.

Thus finer real-part localization cannot worsen the certified truncation
strategy in this model.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- The endpoint threshold is monotone increasing in the strip upper
endpoint. -/
theorem carlsonStripEndpointTargetThreshold_mono_tau
    {sigma tau₁ tau₂ : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (htau : tau₁ ≤ tau₂) :
    carlsonStripEndpointTargetThreshold sigma tau₁ ≤
      carlsonStripEndpointTargetThreshold sigma tau₂ := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using
      carlsonClassicalDensitySlope_pos hsigma hsigmaOne
  have hden : 0 < 1 + q := by linarith
  dsimp [carlsonStripEndpointTargetThreshold]
  apply (div_le_div_iff_of_pos_right hden).2
  linarith

/-- Strictly tightening a strip upper endpoint strictly improves its endpoint
threshold. -/
theorem carlsonStripEndpointTargetThreshold_strictMono_tau
    {sigma tau₁ tau₂ : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (htau : tau₁ < tau₂) :
    carlsonStripEndpointTargetThreshold sigma tau₁ <
      carlsonStripEndpointTargetThreshold sigma tau₂ := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using
      carlsonClassicalDensitySlope_pos hsigma hsigmaOne
  have hden : 0 < 1 + q := by linarith
  dsimp [carlsonStripEndpointTargetThreshold]
  apply (div_lt_div_iff_of_pos_right hden).2
  linarith

/-- The admissible alpha ceiling is antitone in the strip upper endpoint. -/
theorem actualSelectedHeightStripAlphaCeiling_antitone_tau
    {beta sigma tau₁ tau₂ : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (htau : tau₁ ≤ tau₂) :
    actualSelectedHeightStripAlphaCeiling beta sigma tau₂ ≤
      actualSelectedHeightStripAlphaCeiling beta sigma tau₁ := by
  let q : ℝ := 4 * sigma * (1 - sigma)
  have hq : 0 < q := by
    simpa [q, mul_assoc] using
      carlsonClassicalDensitySlope_pos hsigma hsigmaOne
  dsimp [actualSelectedHeightStripAlphaCeiling]
  apply (div_le_div_iff_of_pos_right hq).2
  linarith

/-- Some strip attains the common finite alpha ceiling. -/
theorem exists_strip_eq_actualSelectedHeightFiniteStripAlphaCeiling
    {beta : ℝ} {n : ℕ} (sigma tau : Fin (n + 1) → ℝ) :
    ∃ i : Fin (n + 1),
      actualSelectedHeightStripAlphaCeiling beta (sigma i) (tau i) =
        actualSelectedHeightFiniteStripAlphaCeiling beta sigma tau := by
  let ceilings :=
    Finset.univ.image fun i =>
      actualSelectedHeightStripAlphaCeiling beta (sigma i) (tau i)
  have hmem :
      ceilings.min' (Finset.univ_nonempty.image _) ∈ ceilings :=
    ceilings.min'_mem _
  obtain ⟨i, _hi, hvalue⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hvalue⟩

/-- Pointwise strip refinement decreases the finite endpoint bottleneck. -/
theorem actualSelectedHeightFiniteStripBottleneck_mono_of_tau_le
    {n : ℕ} (sigma tauRefined tauCoarse : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, tauRefined i ≤ tauCoarse i) :
    actualSelectedHeightFiniteStripBottleneck sigma tauRefined ≤
      actualSelectedHeightFiniteStripBottleneck sigma tauCoarse := by
  obtain ⟨i, hi⟩ :=
    exists_strip_eq_actualSelectedHeightFiniteStripBottleneck
      sigma tauRefined
  rw [← hi]
  exact
    (carlsonStripEndpointTargetThreshold_mono_tau
      (hsigma i) (hsigmaOne i) (htau i)).trans
      (carlsonStripEndpointTargetThreshold_le_bottleneck
        sigma tauCoarse i)

/-- Pointwise strip refinement increases the common finite alpha ceiling. -/
theorem actualSelectedHeightFiniteStripAlphaCeiling_mono_of_tau_le
    {beta : ℝ} {n : ℕ}
    (sigma tauRefined tauCoarse : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, tauRefined i ≤ tauCoarse i) :
    actualSelectedHeightFiniteStripAlphaCeiling beta sigma tauCoarse ≤
      actualSelectedHeightFiniteStripAlphaCeiling beta sigma tauRefined := by
  obtain ⟨i, hi⟩ :=
    exists_strip_eq_actualSelectedHeightFiniteStripAlphaCeiling
      sigma tauRefined
  calc
    actualSelectedHeightFiniteStripAlphaCeiling
        beta sigma tauCoarse ≤
        actualSelectedHeightStripAlphaCeiling
          beta (sigma i) (tauCoarse i) := by
      let ceilings :=
        Finset.univ.image fun j =>
          actualSelectedHeightStripAlphaCeiling
            beta (sigma j) (tauCoarse j)
      change ceilings.min' (Finset.univ_nonempty.image _) ≤ _
      apply ceilings.min'_le
      exact Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩
    _ ≤ actualSelectedHeightStripAlphaCeiling
          beta (sigma i) (tauRefined i) :=
      actualSelectedHeightStripAlphaCeiling_antitone_tau
        (hsigma i) (hsigmaOne i) (htau i)
    _ = actualSelectedHeightFiniteStripAlphaCeiling
          beta sigma tauRefined := hi

/-- Pointwise strip refinement increases the effective capped alpha ceiling. -/
theorem actualSelectedHeightFiniteStripEffectiveAlphaCeiling_mono_of_tau_le
    {beta : ℝ} {n : ℕ}
    (sigma tauRefined tauCoarse : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, tauRefined i ≤ tauCoarse i) :
    actualSelectedHeightFiniteStripEffectiveAlphaCeiling
        beta sigma tauCoarse ≤
      actualSelectedHeightFiniteStripEffectiveAlphaCeiling
        beta sigma tauRefined := by
  exact min_le_min le_rfl
    (actualSelectedHeightFiniteStripAlphaCeiling_mono_of_tau_le
      sigma tauRefined tauCoarse hsigma hsigmaOne htau)

/-- Pointwise strip refinement cannot decrease the optimal balanced robustness
margin. -/
theorem actualSelectedHeightFiniteStripBalancedRobustMargin_mono_of_tau_le
    {beta : ℝ} {n : ℕ}
    (sigma tauRefined tauCoarse : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (htau : ∀ i, tauRefined i ≤ tauCoarse i) :
    actualSelectedHeightFiniteStripRobustMargin beta sigma tauCoarse
        (actualSelectedHeightFiniteStripBalancedExponent
          beta sigma tauCoarse) ≤
      actualSelectedHeightFiniteStripRobustMargin beta sigma tauRefined
        (actualSelectedHeightFiniteStripBalancedExponent
          beta sigma tauRefined) := by
  rw [actualSelectedHeightFiniteStripBalancedExponent_robustMargin,
    actualSelectedHeightFiniteStripBalancedExponent_robustMargin]
  have heffective :=
    actualSelectedHeightFiniteStripEffectiveAlphaCeiling_mono_of_tau_le
      (beta := beta) sigma tauRefined tauCoarse hsigma hsigmaOne htau
  linarith

end PrimeNumberTheorem
