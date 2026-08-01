import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponentUniqueness

/-!
# Stability of the weighted-balanced truncation exponent

Exact optimality uniquely determines the weighted-balanced polynomial height
exponent.  The quantitative form is also rigid: if an admissible common
physical margin is within `epsilon` of the optimal margin, then the contour
constraint prevents the exponent from falling more than `epsilon` below the
optimizer, while an actual bottleneck Carlson strip controls its excess above
the optimizer after multiplication by that strip's positive slope.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- Near-optimal common physical margin quantitatively traps the polynomial
height exponent around the unique weighted-balanced optimizer.

The returned index is an actual strip attaining the finite minimum defining
the optimal margin.  Its Carlson slope is strictly positive under the usual
strip hypotheses, so the final inequality is a genuine upper stability bound.
-/
theorem
    exists_bottleneck_nearOptimalExponent_bounds
    {beta alpha delta epsilon : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hnear :
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau -
          epsilon ≤
        delta)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha delta) :
    ∃ i,
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau =
          actualSelectedHeightStripBalancedPhysicalMargin
            beta (sigma i) (tau i) ∧
        actualSelectedHeightFiniteStripWeightedBalancedExponent
              beta sigma tau -
            epsilon ≤
          alpha ∧
        actualSelectedHeightStripCarlsonSlope (sigma i) *
            (alpha -
              actualSelectedHeightFiniteStripWeightedBalancedExponent
                beta sigma tau) ≤
          epsilon := by
  let deltaStar :=
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau
  let alphaStar :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent beta sigma tau
  obtain ⟨i, hi⟩ :=
    exists_strip_eq_actualSelectedHeightFiniteStripOptimalPhysicalMargin
      (beta := beta) sigma tau
  let q := actualSelectedHeightStripCarlsonSlope (sigma i)
  have hq : 0 < q :=
    actualSelectedHeightStripSlope_pos (hsigma i) (hsigmaOne i)
  have hiEq :
      deltaStar =
        ((beta - tau i) - q * (1 - beta)) / (1 + q) := by
    simpa [deltaStar, q,
      actualSelectedHeightStripBalancedPhysicalMargin] using hi
  have hcross :
      deltaStar * (1 + q) =
        (beta - tau i) - q * (1 - beta) :=
    (eq_div_iff (by linarith : 1 + q ≠ 0)).mp hiEq
  have hcontour := certificate.contour
  have hstrip := certificate.strip i
  rw [actualSelectedHeightStripPhysicalMargin_eq] at hstrip
  have halphaStar :
      alphaStar = 1 - beta + deltaStar := by
    rfl
  have hlower : alphaStar - epsilon ≤ alpha := by
    change deltaStar - epsilon ≤ delta at hnear
    change delta ≤ alpha - (1 - beta) at hcontour
    rw [halphaStar]
    dsimp [deltaStar]
    linarith
  have hupperScaled :
      q * (alpha - alphaStar) ≤ epsilon := by
    change
      delta ≤
        (beta - tau i) - q * alpha at hstrip
    rw [halphaStar]
    nlinarith
  refine ⟨i, hi, hlower, ?_⟩
  simpa [q, alphaStar] using hupperScaled

/-- Division by the positive bottleneck slope turns the scaled stability bound
into an explicit interval for the near-optimal exponent. -/
theorem
    exists_bottleneck_nearOptimalExponent_interval
    {beta alpha delta epsilon : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (hnear :
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau -
          epsilon ≤
        delta)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha delta) :
    ∃ i,
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau =
          actualSelectedHeightStripBalancedPhysicalMargin
            beta (sigma i) (tau i) ∧
        actualSelectedHeightFiniteStripWeightedBalancedExponent
              beta sigma tau -
            epsilon ≤
          alpha ∧
        alpha ≤
          actualSelectedHeightFiniteStripWeightedBalancedExponent
              beta sigma tau +
            epsilon /
              actualSelectedHeightStripCarlsonSlope (sigma i) := by
  obtain ⟨i, hi, hlower, hscaled⟩ :=
    exists_bottleneck_nearOptimalExponent_bounds
      sigma tau hsigma hsigmaOne hnear certificate
  have hq :
      0 < actualSelectedHeightStripCarlsonSlope (sigma i) :=
    actualSelectedHeightStripSlope_pos (hsigma i) (hsigmaOne i)
  have hdiv :
      alpha -
          actualSelectedHeightFiniteStripWeightedBalancedExponent
            beta sigma tau ≤
        epsilon /
          actualSelectedHeightStripCarlsonSlope (sigma i) := by
    apply (le_div_iff₀ hq).2
    simpa [mul_comm] using hscaled
  refine ⟨i, hi, hlower, ?_⟩
  linarith

end PrimeNumberTheorem
