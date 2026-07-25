import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonLogAbsorption

/-!
# Carlson density at a polynomial dynamic height

This file pulls Carlson's actual multiplicity-weighted zero-density estimate
back from the height variable `T` to the explicit-formula scale `x` through
the dynamic choice `T(x) = x^alpha`.

The resulting count budget is kept separate from the still-missing analytic
statement that a concrete complementary zero sum is bounded by
`count budget * kernel budget`.
-/

namespace PrimeNumberTheorem

open Filter

/-- Polynomial dynamic height used by the lower-transfer strategy. -/
noncomputable def carlsonPolynomialHeight
    (alpha x : ℝ) : ℝ :=
  x ^ alpha

/-- Carlson's original power-times-logarithm majorant after composing the
height variable with `T(x) = x^alpha`. -/
noncomputable def carlsonPolynomialHeightCountMajorant
    (sigma alpha x : ℝ) : ℝ :=
  carlsonPolynomialHeight alpha x ^ (4 * sigma * (1 - sigma)) *
    (Real.log (carlsonPolynomialHeight alpha x)) ^ (4 : ℕ)

/-- The same composed majorant written directly on the `x` scale. -/
noncomputable def carlsonPolynomialCountBudget
    (sigma alpha x : ℝ) : ℝ :=
  alpha ^ (4 : ℕ) *
    (x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
      (Real.log x) ^ (4 : ℕ))

/-- Carlson's actual zero-density estimate remains a `BigO` estimate after
composition with every positive polynomial height. -/
theorem carlson_zeroDensity_polynomialHeight_isBigO
    {sigma alpha : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) :
    (fun x =>
        (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight alpha x) : ℝ))
      =O[Filter.atTop]
    (carlsonPolynomialHeightCountMajorant sigma alpha) := by
  simpa [carlsonPolynomialHeightCountMajorant,
    carlsonPolynomialHeight] using
    (CarlsonZeroDensity.carlson_zeroDensity_isBigO hsigma hsigmaOne).comp_tendsto
      (tendsto_rpow_atTop halpha)

/-- The composed Carlson majorant and its direct `x`-scale budget agree
eventually. -/
theorem eventually_carlsonPolynomialHeightCountMajorant_eq_countBudget
    (sigma alpha : ℝ) :
    carlsonPolynomialHeightCountMajorant sigma alpha
      =ᶠ[Filter.atTop]
    carlsonPolynomialCountBudget sigma alpha := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold carlsonPolynomialHeightCountMajorant
    carlsonPolynomialHeight carlsonPolynomialCountBudget
  rw [← Real.rpow_mul hx.le]
  rw [Real.log_rpow hx alpha]
  have hexponent :
      alpha * (4 * sigma * (1 - sigma)) =
        carlsonClassicalPolynomialDensityExponent alpha sigma := by
    simp [carlsonClassicalPolynomialDensityExponent,
      carlsonPolynomialHeightDensityExponent]
  rw [hexponent]
  ring

/-- Concrete `x`-scale form of Carlson's multiplicity-weighted density
estimate at polynomial height. -/
theorem carlson_zeroDensity_polynomialHeight_countBudget_isBigO
    {sigma alpha : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (halpha : 0 < alpha) :
    (fun x =>
        (ZeroDensity.zeroDensityCount sigma
          (carlsonPolynomialHeight alpha x) : ℝ))
      =O[Filter.atTop]
    (carlsonPolynomialCountBudget sigma alpha) := by
  exact (carlson_zeroDensity_polynomialHeight_isBigO
    hsigma hsigmaOne halpha).congr'
      Filter.EventuallyEq.rfl
      (eventually_carlsonPolynomialHeightCountMajorant_eq_countBudget
        sigma alpha)

/-- With a strict target-exponent margin, the complete Carlson count budget
times the normalized model kernel `x^(sigma-beta)` tends to zero. -/
theorem tendsto_carlsonPolynomialCountBudget_mul_targetKernelRatio
    {beta sigma alpha epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hmargin :
      targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonClassicalPolynomialDensityExponent alpha sigma) +
        epsilon < 0) :
    Filter.Tendsto
      (fun x =>
        carlsonPolynomialCountBudget sigma alpha x *
          x ^ (sigma - beta))
      Filter.atTop (nhds 0) := by
  have hnormalized :
      Filter.Tendsto
        (fun x =>
          alpha ^ (4 : ℕ) *
            carlsonTargetNormalizedLogMajorant beta sigma alpha x)
        Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_carlsonTargetNormalizedLogMajorant
          hepsilon hmargin))
  refine hnormalized.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hexponent :
      carlsonClassicalPolynomialDensityExponent alpha sigma +
          (sigma - beta) =
        targetAmplitudePintzCarlsonExponent beta sigma
          (carlsonClassicalPolynomialDensityExponent alpha sigma) := by
    simp [targetAmplitudePintzCarlsonExponent]
    ring
  simp only [carlsonPolynomialCountBudget,
    carlsonTargetNormalizedLogMajorant]
  rw [show
    alpha ^ (4 : ℕ) *
          (x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
            (Real.log x) ^ (4 : ℕ)) *
        x ^ (sigma - beta) =
      alpha ^ (4 : ℕ) *
        ((x ^ carlsonClassicalPolynomialDensityExponent alpha sigma *
          x ^ (sigma - beta)) * (Real.log x) ^ (4 : ℕ)) by ring]
  rw [← Real.rpow_add hx, hexponent]

/-- In Carlson's admissible target region, one polynomial height simultaneously
has positive slope, clears the contour threshold, carries the actual density
`BigO` estimate, and has a target-normalized count budget tending to zero. -/
theorem exists_carlsonPolynomialHeight_countBudget_targetNormalized
    {beta sigma : ℝ}
    (hsigma : 1 / 2 < sigma) (hsigmaOne : sigma < 1)
    (hbetaOne : beta < 1)
    (hbeta : carlsonClassicalTargetThreshold sigma < beta) :
    ∃ alpha : ℝ,
      0 < alpha ∧
      1 - beta < alpha ∧
      (fun x =>
          (ZeroDensity.zeroDensityCount sigma
            (carlsonPolynomialHeight alpha x) : ℝ))
        =O[Filter.atTop]
      (carlsonPolynomialCountBudget sigma alpha) ∧
      Filter.Tendsto
        (fun x =>
          carlsonPolynomialCountBudget sigma alpha x *
            x ^ (sigma - beta))
        Filter.atTop (nhds 0) := by
  obtain ⟨alpha, epsilon, hepsilon, hcontour, hmargin⟩ :=
    exists_carlsonPolynomialHeight_targetAmplitude_strictMargin
      hsigma hsigmaOne hbeta
  have halpha : 0 < alpha := by
    linarith
  exact ⟨alpha, halpha, hcontour,
    carlson_zeroDensity_polynomialHeight_countBudget_isBigO
      hsigma hsigmaOne halpha,
    tendsto_carlsonPolynomialCountBudget_mul_targetKernelRatio
      hepsilon hmargin⟩

end PrimeNumberTheorem
