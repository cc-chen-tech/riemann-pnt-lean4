import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponent

/-!
# Uniqueness of the weighted-balanced truncation exponent

The weighted-balanced exponent was already shown to attain the largest common
physical margin allowed simultaneously by the contour remainder and every
Carlson strip.  This module proves the converse rigidity statement.

Because the strip family is finite and nonempty, one strip attains the minimum
balanced margin.  At the optimal margin, the contour inequality forces any
admissible exponent to be at least the weighted-balanced exponent, while the
bottleneck strip inequality forces it to be at most that exponent.  Hence the
optimal polynomial truncation exponent is unique.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- A finite strip actually attains the minimum balanced physical margin. -/
theorem
    exists_strip_eq_actualSelectedHeightFiniteStripOptimalPhysicalMargin
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ) :
    ∃ i,
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau =
        actualSelectedHeightStripBalancedPhysicalMargin
          beta (sigma i) (tau i) := by
  classical
  let margins : Finset ℝ :=
    Finset.univ.image fun i =>
      actualSelectedHeightStripBalancedPhysicalMargin
        beta (sigma i) (tau i)
  have hmargins : margins.Nonempty :=
    Finset.univ_nonempty.image _
  have hmem : margins.min' hmargins ∈ margins :=
    Finset.min'_mem margins hmargins
  obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hmem
  refine ⟨i, ?_⟩
  change margins.min' hmargins =
    actualSelectedHeightStripBalancedPhysicalMargin
      beta (sigma i) (tau i)
  exact hi.symm

/-- Any polynomial height exponent attaining the optimal common physical
margin equals the weighted-balanced exponent. -/
theorem actualSelectedHeightFiniteStripWeightedBalancedExponent_unique
    {beta alpha : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha
        (actualSelectedHeightFiniteStripOptimalPhysicalMargin
          beta sigma tau)) :
    alpha =
      actualSelectedHeightFiniteStripWeightedBalancedExponent
        beta sigma tau := by
  let delta :=
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau
  have hlower :
      actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau ≤ alpha := by
    have hcontour := certificate.contour
    unfold actualSelectedHeightFiniteStripWeightedBalancedExponent
    change 1 - beta + delta ≤ alpha
    change delta ≤ alpha - (1 - beta) at hcontour
    linarith
  obtain ⟨i, hi⟩ :=
    exists_strip_eq_actualSelectedHeightFiniteStripOptimalPhysicalMargin
      (beta := beta) sigma tau
  let q := actualSelectedHeightStripCarlsonSlope (sigma i)
  have hq : 0 < q :=
    actualSelectedHeightStripSlope_pos (hsigma i) (hsigmaOne i)
  have hiEq :
      delta =
        ((beta - tau i) - q * (1 - beta)) / (1 + q) := by
    simpa [delta, q, actualSelectedHeightStripBalancedPhysicalMargin] using hi
  have hcross :
      delta * (1 + q) =
        (beta - tau i) - q * (1 - beta) :=
    (eq_div_iff (by linarith : 1 + q ≠ 0)).mp hiEq
  have hstrip := certificate.strip i
  rw [actualSelectedHeightStripPhysicalMargin_eq] at hstrip
  have hupper :
      alpha ≤
        actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau := by
    unfold actualSelectedHeightFiniteStripWeightedBalancedExponent
    change alpha ≤ 1 - beta + delta
    change
      delta ≤
        (beta - tau i) - q * alpha at hstrip
    nlinarith
  exact le_antisymm hupper hlower

/-- Characterization of the unique exponent carrying an optimal-margin
certificate. -/
theorem
    actualSelectedHeightFiniteStrip_optimalMarginCertificate_iff
    {beta alpha : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha
        (actualSelectedHeightFiniteStripOptimalPhysicalMargin
          beta sigma tau) ↔
      alpha =
        actualSelectedHeightFiniteStripWeightedBalancedExponent
          beta sigma tau := by
  constructor
  · exact
      actualSelectedHeightFiniteStripWeightedBalancedExponent_unique
        sigma tau hsigma hsigmaOne
  · intro halpha
    subst alpha
    exact
      actualSelectedHeightFiniteStripWeightedBalancedExponent_marginCertificate
        sigma tau hsigma hsigmaOne

end PrimeNumberTheorem
