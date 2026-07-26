import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightBalancedExponent

/-!
# Carlson-slope weighted balanced heights

The existing balanced exponent maximizes distance in the height-exponent
variable.  Actual Carlson strip decay has strip-dependent slope
`4 * sigma * (1 - sigma)`.  This module optimizes the physical exponent margin
instead.

For contour transition `L = 1 - beta`, strip slope `qᵢ`, and endpoint
intercept `bᵢ = beta - tauᵢ`, the constraints are

`δ ≤ alpha - L` and `δ ≤ bᵢ - qᵢ * alpha`.

Their finite optimum is

`δ* = minᵢ (bᵢ - qᵢ * L) / (1 + qᵢ)`,
`alpha* = L + δ*`.
-/

namespace PrimeNumberTheorem

noncomputable section

/-- The polynomial-height slope in Carlson's classical density exponent. -/
def actualSelectedHeightStripCarlsonSlope (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

/-- The positive physical decay margin is the negative of the actual
target-normalized Carlson strip exponent. -/
def actualSelectedHeightStripPhysicalMargin
    (beta sigma tau alpha : ℝ) : ℝ :=
  -targetAmplitudeStripEndpointExponent beta tau
    (carlsonClassicalPolynomialDensityExponent alpha sigma)

theorem actualSelectedHeightStripPhysicalMargin_eq
    (beta sigma tau alpha : ℝ) :
    actualSelectedHeightStripPhysicalMargin beta sigma tau alpha =
      (beta - tau) -
        actualSelectedHeightStripCarlsonSlope sigma * alpha := by
  simp [actualSelectedHeightStripPhysicalMargin,
    targetAmplitudeStripEndpointExponent,
    carlsonClassicalPolynomialDensityExponent,
    carlsonPolynomialHeightDensityExponent,
    actualSelectedHeightStripCarlsonSlope]
  ring

/-- Best common physical margin obtained by balancing the contour against one
Carlson strip. -/
noncomputable def actualSelectedHeightStripBalancedPhysicalMargin
    (beta sigma tau : ℝ) : ℝ :=
  let q := actualSelectedHeightStripCarlsonSlope sigma
  ((beta - tau) - q * (1 - beta)) / (1 + q)

/-- Minimum of the stripwise balanced physical margins. -/
noncomputable def actualSelectedHeightFiniteStripOptimalPhysicalMargin
    {n : ℕ}
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  let margins :=
    Finset.univ.image fun i =>
      actualSelectedHeightStripBalancedPhysicalMargin beta (sigma i) (tau i)
  margins.min' (Finset.univ_nonempty.image _)

/-- The polynomial truncation exponent selected by the physical Carlson
margin. -/
noncomputable def actualSelectedHeightFiniteStripWeightedBalancedExponent
    {n : ℕ}
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ) : ℝ :=
  1 - beta +
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau

/-- A common physical margin certificate for the contour and every Carlson
strip at one polynomial height exponent. -/
structure ActualSelectedHeightFiniteStripPhysicalMarginCertificate
    {n : ℕ}
    (beta : ℝ)
    (sigma tau : Fin (n + 1) → ℝ)
    (alpha delta : ℝ) : Prop where
  contour : delta ≤ alpha - (1 - beta)
  strip :
    ∀ i,
      delta ≤
        actualSelectedHeightStripPhysicalMargin
          beta (sigma i) (tau i) alpha

theorem actualSelectedHeightStripSlope_pos
    {sigma : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1) :
    0 < actualSelectedHeightStripCarlsonSlope sigma := by
  simpa [actualSelectedHeightStripCarlsonSlope, mul_assoc] using
    carlsonClassicalDensitySlope_pos hsigma hsigmaOne

/-- No contour/strip common margin can exceed their slope-weighted balance. -/
theorem physicalMargin_le_stripBalancedPhysicalMargin
    {beta sigma tau alpha delta : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (hcontour : delta ≤ alpha - (1 - beta))
    (hstrip :
      delta ≤
        actualSelectedHeightStripPhysicalMargin beta sigma tau alpha) :
    delta ≤
      actualSelectedHeightStripBalancedPhysicalMargin beta sigma tau := by
  let q := actualSelectedHeightStripCarlsonSlope sigma
  have hq : 0 < q := actualSelectedHeightStripSlope_pos hsigma hsigmaOne
  have hscaled :
      q * delta ≤ q * (alpha - (1 - beta)) :=
    mul_le_mul_of_nonneg_left hcontour hq.le
  rw [actualSelectedHeightStripPhysicalMargin_eq] at hstrip
  unfold actualSelectedHeightStripBalancedPhysicalMargin
  dsimp only
  apply (le_div_iff₀ (by linarith : 0 < 1 + q)).2
  dsimp [q] at hscaled ⊢
  nlinarith

theorem actualSelectedHeightFiniteStripOptimalPhysicalMargin_le_strip
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau ≤
      actualSelectedHeightStripBalancedPhysicalMargin
        beta (sigma i) (tau i) := by
  classical
  unfold actualSelectedHeightFiniteStripOptimalPhysicalMargin
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem le_actualSelectedHeightFiniteStripOptimalPhysicalMargin
    {beta delta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hdelta :
      ∀ i,
        delta ≤
          actualSelectedHeightStripBalancedPhysicalMargin
            beta (sigma i) (tau i)) :
    delta ≤
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau := by
  classical
  unfold actualSelectedHeightFiniteStripOptimalPhysicalMargin
  rw [Finset.le_min'_iff]
  intro value hvalue
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
  exact hdelta i

/-- The explicit weighted exponent attains the finite optimal physical
margin. -/
theorem
    actualSelectedHeightFiniteStripWeightedBalancedExponent_marginCertificate
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1) :
    ActualSelectedHeightFiniteStripPhysicalMarginCertificate
      beta sigma tau
      (actualSelectedHeightFiniteStripWeightedBalancedExponent
        beta sigma tau)
      (actualSelectedHeightFiniteStripOptimalPhysicalMargin
        beta sigma tau) := by
  let delta :=
    actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau
  constructor
  · unfold actualSelectedHeightFiniteStripWeightedBalancedExponent
    linarith
  · intro i
    let q := actualSelectedHeightStripCarlsonSlope (sigma i)
    have hq : 0 < q :=
      actualSelectedHeightStripSlope_pos (hsigma i) (hsigmaOne i)
    have hdelta :=
      actualSelectedHeightFiniteStripOptimalPhysicalMargin_le_strip
        (beta := beta) sigma tau i
    have hmul :
        delta * (1 + q) ≤
          (beta - tau i) - q * (1 - beta) := by
      apply (le_div_iff₀ (by linarith : 0 < 1 + q)).1
      simpa [delta, actualSelectedHeightStripBalancedPhysicalMargin, q] using
        hdelta
    rw [actualSelectedHeightStripPhysicalMargin_eq]
    unfold actualSelectedHeightFiniteStripWeightedBalancedExponent
    dsimp [delta, q] at hmul ⊢
    nlinarith

/-- The weighted balanced exponent maximizes the common physical margin over
all polynomial height exponents. -/
theorem actualSelectedHeightFiniteStripWeightedBalancedExponent_maximizes
    {beta alpha delta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (certificate :
      ActualSelectedHeightFiniteStripPhysicalMarginCertificate
        beta sigma tau alpha delta) :
    delta ≤
      actualSelectedHeightFiniteStripOptimalPhysicalMargin beta sigma tau := by
  apply le_actualSelectedHeightFiniteStripOptimalPhysicalMargin sigma tau
  intro i
  exact physicalMargin_le_stripBalancedPhysicalMargin
    (hsigma i) (hsigmaOne i) certificate.contour (certificate.strip i)

/-- Every actual Carlson endpoint exponent at the weighted balanced height is
at most the negative optimal physical margin. -/
theorem
    actualSelectedHeightFiniteStripWeightedBalancedExponent_endpointExponent_le
    {beta : ℝ}
    {n : ℕ}
    (sigma tau : Fin (n + 1) → ℝ)
    (hsigma : ∀ i, 1 / 2 < sigma i)
    (hsigmaOne : ∀ i, sigma i < 1)
    (i : Fin (n + 1)) :
    targetAmplitudeStripEndpointExponent beta (tau i)
        (carlsonClassicalPolynomialDensityExponent
          (actualSelectedHeightFiniteStripWeightedBalancedExponent
            beta sigma tau)
          (sigma i)) ≤
      -actualSelectedHeightFiniteStripOptimalPhysicalMargin
        beta sigma tau := by
  have hcertificate :=
    actualSelectedHeightFiniteStripWeightedBalancedExponent_marginCertificate
      (beta := beta) sigma tau hsigma hsigmaOne
  have hi := hcertificate.strip i
  unfold actualSelectedHeightStripPhysicalMargin at hi
  linarith

end

end PrimeNumberTheorem
