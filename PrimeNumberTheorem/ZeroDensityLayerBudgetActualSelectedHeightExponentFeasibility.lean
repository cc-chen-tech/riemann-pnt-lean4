import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonStripEndpointCriterion

/-!
# Actual selected-height exponent feasibility

The endpoint-aware Carlson criterion produces an exponent above the contour
threshold `1 - beta`, but the actual selected-height explicit-formula theorem
also requires `0 < alpha` and `alpha ≤ 1`.

For a zeta-zero real part `0 < beta < 1`, these extra conditions cost nothing:
replace any feasible exponent by `min alpha 1`.  The contour inequality remains
strict, and decreasing the exponent can only improve the classical Carlson
density exponent because its slope is positive on `1/2 < sigma < 1`.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- Exact endpoint criterion with all exponent conditions required by the
actual selected-height natural-point remainder theorem. -/
theorem exists_actualSelectedHeightExponent_stripEndpoint_decay_iff
    {beta sigma tau : ℝ}
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1) :
    (∃ alpha : ℝ,
        0 < alpha ∧ alpha ≤ 1 ∧ 1 - beta < alpha ∧
        targetAmplitudeStripEndpointExponent beta tau
          (carlsonClassicalPolynomialDensityExponent alpha sigma) < 0) ↔
      carlsonStripEndpointTargetThreshold sigma tau < beta := by
  constructor
  · rintro ⟨alpha, _halpha, _halphaOne, hmargin, hdecay⟩
    exact
      (exists_carlsonPolynomialHeight_stripEndpoint_decay_iff
        hsigma hsigmaOne).1
        ⟨alpha, hmargin, hdecay⟩
  · intro hthreshold
    obtain ⟨alpha, hmargin, hdecay⟩ :=
      (exists_carlsonPolynomialHeight_stripEndpoint_decay_iff
        hsigma hsigmaOne).2 hthreshold
    let alpha' : ℝ := min alpha 1
    have hmarginOne : 1 - beta < 1 := by linarith
    have hmargin' : 1 - beta < alpha' := by
      exact lt_min hmargin hmarginOne
    have halpha' : 0 < alpha' := by
      have : 0 < 1 - beta := by linarith
      exact this.trans hmargin'
    have halpha'One : alpha' ≤ 1 := min_le_right _ _
    have halpha'Le : alpha' ≤ alpha := min_le_left _ _
    have hslope :
        0 ≤ 4 * sigma * (1 - sigma) :=
      (carlsonClassicalDensitySlope_pos hsigma hsigmaOne).le
    have hmono :
        alpha' * (4 * sigma * (1 - sigma)) ≤
          alpha * (4 * sigma * (1 - sigma)) :=
      mul_le_mul_of_nonneg_right halpha'Le hslope
    refine ⟨alpha', halpha', halpha'One, hmargin', ?_⟩
    simp only [targetAmplitudeStripEndpointExponent,
      carlsonClassicalPolynomialDensityExponent,
      carlsonPolynomialHeightDensityExponent] at hdecay ⊢
    nlinarith

/-- A canonical exponent satisfying the actual selected-height contour and
endpoint-aware Carlson conditions whenever the exact threshold holds. -/
noncomputable def actualSelectedHeightStripExponent
    (beta sigma tau : ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hthreshold :
      carlsonStripEndpointTargetThreshold sigma tau < beta) : ℝ :=
  Classical.choose
    ((exists_actualSelectedHeightExponent_stripEndpoint_decay_iff
      hbeta hbetaOne hsigma hsigmaOne).2 hthreshold)

/-- Full specification of the canonical actual selected-height exponent. -/
theorem actualSelectedHeightStripExponent_spec
    (beta sigma tau : ℝ)
    (hbeta : 0 < beta) (hbetaOne : beta < 1)
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hthreshold :
      carlsonStripEndpointTargetThreshold sigma tau < beta) :
    0 <
        actualSelectedHeightStripExponent beta sigma tau
          hbeta hbetaOne hsigma hsigmaOne hthreshold ∧
      actualSelectedHeightStripExponent beta sigma tau
          hbeta hbetaOne hsigma hsigmaOne hthreshold ≤ 1 ∧
      1 - beta <
        actualSelectedHeightStripExponent beta sigma tau
          hbeta hbetaOne hsigma hsigmaOne hthreshold ∧
      targetAmplitudeStripEndpointExponent beta tau
        (carlsonClassicalPolynomialDensityExponent
          (actualSelectedHeightStripExponent beta sigma tau
            hbeta hbetaOne hsigma hsigmaOne hthreshold)
          sigma) < 0 :=
  Classical.choose_spec
    ((exists_actualSelectedHeightExponent_stripEndpoint_decay_iff
      hbeta hbetaOne hsigma hsigmaOne).2 hthreshold)

end PrimeNumberTheorem
