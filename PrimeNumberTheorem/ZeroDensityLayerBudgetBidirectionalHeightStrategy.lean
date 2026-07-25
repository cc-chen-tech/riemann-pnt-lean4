import PrimeNumberTheorem.ZeroDensityLayerBudgetTargetAmplitudeHeightIncompatibility

/-!
# Bidirectional height strategies for PNT transfer

The current Pintz--Carlson upper-bound chain and the target-amplitude lower-bound
chain impose incompatible requirements on a single hard truncation height.
This file records the resulting design constraint as a small reusable interface:

* the upper height is subpolynomial on the logarithmic scale;
* the lower height is admissible after normalization by a fixed target amplitude;
* for `beta < 1`, the two height functions cannot coincide.

The concrete strategy below uses the existing Pintz square-root-logarithmic height
on the upper side and a polynomial height with exponent `2 - beta` on the lower
side.  This is an interface theorem, not an explicit-formula comparison between
the two truncations and not an unconditional oscillation theorem.
-/

namespace PrimeNumberTheorem

/-- A bidirectional PNT transfer strategy keeps separate truncation heights for
the upper-bound and target-amplitude lower-bound arguments. -/
structure BidirectionalPNTHeightStrategy (beta : ℝ) where
  /-- Logarithmic truncation height used by the Pintz--Carlson upper chain. -/
  upperLogHeight : ℕ → ℝ
  /-- Logarithmic truncation height used by the target-amplitude lower chain. -/
  lowerLogHeight : ℕ → ℝ
  /-- The upper height remains subpolynomial in the PNT variable. -/
  upper_subpolynomial : IsPNTSubpolynomialLogHeight upperLogHeight
  /-- The lower height defeats the fixed target-amplitude contour scale. -/
  lower_target_admissible :
    IsTargetAmplitudeAdmissibleHeight beta lowerLogHeight

/-- A simple lower-mode logarithmic height.  Its polynomial exponent is
`2 - beta`, one full power above the target-amplitude transition `1 - beta`. -/
noncomputable def pntPolynomialLowerLogHeight (beta : ℝ) (m : ℕ) : ℝ :=
  (2 - beta) * Real.log m

/-- The polynomial lower-mode height has target-amplitude logarithmic gap
exactly `log m`, hence is admissible for every fixed `beta`. -/
theorem isTargetAmplitudeAdmissibleHeight_pntPolynomialLowerLogHeight
    (beta : ℝ) :
    IsTargetAmplitudeAdmissibleHeight beta
      (pntPolynomialLowerLogHeight beta) := by
  unfold IsTargetAmplitudeAdmissibleHeight
  have hlog :
      Filter.Tendsto (fun m : ℕ => Real.log (m : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  convert hlog using 1
  funext m
  simp only [pntTargetAmplitudeContourLogGap,
    pntPolynomialLowerLogHeight]
  ring

/-- The concrete split-height strategy: Pintz square-root-logarithmic height for
the upper chain and a polynomial target-admissible height for the lower chain. -/
noncomputable def pntSqrtLogPolynomialBidirectionalHeightStrategy
    (beta rate : ℝ) (hrate : 0 ≤ rate) :
    BidirectionalPNTHeightStrategy beta where
  upperLogHeight := pntSqrtLogHeight rate
  lowerLogHeight := pntPolynomialLowerLogHeight beta
  upper_subpolynomial :=
    isPNTSubpolynomialLogHeight_pntSqrtLog hrate
  lower_target_admissible :=
    isTargetAmplitudeAdmissibleHeight_pntPolynomialLowerLogHeight beta

/-- A certified split-height strategy exists for every target real part and
every nonnegative Pintz rate. -/
theorem nonempty_bidirectionalPNTHeightStrategy
    (beta rate : ℝ) (hrate : 0 ≤ rate) :
    Nonempty (BidirectionalPNTHeightStrategy beta) :=
  ⟨pntSqrtLogPolynomialBidirectionalHeightStrategy beta rate hrate⟩

/-- Below the line `beta = 1`, no valid bidirectional strategy can collapse its
upper and lower modes to one logarithmic height function. -/
theorem BidirectionalPNTHeightStrategy.upperLogHeight_ne_lowerLogHeight
    {beta : ℝ} (strategy : BidirectionalPNTHeightStrategy beta)
    (hbeta : beta < 1) :
    strategy.upperLogHeight ≠ strategy.lowerLogHeight := by
  intro hsame
  have hlowerSubpolynomial :
      IsPNTSubpolynomialLogHeight strategy.lowerLogHeight := by
    simpa only [hsame] using strategy.upper_subpolynomial
  exact
    (not_isTargetAmplitudeAdmissibleHeight_of_subpolynomial
      hbeta hlowerSubpolynomial) strategy.lower_target_admissible

/-- In particular, the concrete square-root-logarithmic/polynomial strategy has
genuinely different upper and lower height functions whenever `beta < 1`. -/
theorem pntSqrtLogHeight_ne_pntPolynomialLowerLogHeight
    {beta rate : ℝ} (hbeta : beta < 1) (hrate : 0 ≤ rate) :
    pntSqrtLogHeight rate ≠ pntPolynomialLowerLogHeight beta :=
  BidirectionalPNTHeightStrategy.upperLogHeight_ne_lowerLogHeight
    (pntSqrtLogPolynomialBidirectionalHeightStrategy beta rate hrate) hbeta

end PrimeNumberTheorem
