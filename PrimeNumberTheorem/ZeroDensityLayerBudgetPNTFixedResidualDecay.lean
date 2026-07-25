import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTRealOrdinateDecay

/-!
# Fixed residual decay in the natural-point PNT certificate

This module transfers the real-variable real-ordinate decay theorem to the
natural evaluation points used by the cofinal explicit formula.  It also
combines the fixed logarithmic-derivative term with the depth-zero
trivial-zero contribution.
-/

open Filter
open scoped BigOperators

namespace PrimeNumberTheorem

/-- The real-ordinate residual vanishes along any eventually nonnegative
natural-point height schedule. -/
theorem tendsto_naturalPoint_realOrdinateRelativeZeroResidual_of_eventually_nonneg
    (height : ℕ → ℝ)
    (hheight : ∀ᶠ m in atTop, 0 ≤ height m) :
    Tendsto
      (fun m : ℕ =>
        ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset (height m),
          pntRelativeZeroContribution (m : ℝ) ρ‖)
      atTop (nhds 0) := by
  have hfixed :
      Tendsto
        (fun m : ℕ =>
          ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset 0,
            pntRelativeZeroContribution (m : ℝ) ρ‖)
        atTop (nhds 0) :=
    tendsto_realOrdinateRelativeZeroResidual_zeroHeight.comp
      tendsto_natCast_atTop_atTop
  apply hfixed.congr'
  filter_upwards [hheight] with m hm
  rw [realOrdinateNontrivialZerosFinset_eq_zeroHeight hm]

/-- At depth zero, the fixed logarithmic-derivative and trivial-zero terms
vanish after division by the natural evaluation point. -/
theorem tendsto_naturalPoint_fixedPNTConstants_zeroDepth_relative :
    Tendsto
      (fun m : ℕ =>
        (‖deriv riemannZeta 0 / riemannZeta 0‖ +
          ‖cofinalTrivialZeroContribution m 0‖) / (m : ℝ))
      atTop (nhds 0) := by
  have hconstant :
      Tendsto
        (fun m : ℕ =>
          ‖deriv riemannZeta 0 / riemannZeta 0‖ / (m : ℝ))
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  simpa [cofinalTrivialZeroContribution_zero] using hconstant

/-- The complete fixed residual, excluding the contour remainder, vanishes
along every eventually nonnegative natural-point height schedule. -/
theorem tendsto_naturalPoint_fixedRelativeResidual_zeroDepth
    (height : ℕ → ℝ)
    (hheight : ∀ᶠ m in atTop, 0 ≤ height m) :
    Tendsto
      (fun m : ℕ =>
        ‖∑ ρ ∈ realOrdinateNontrivialZerosFinset (height m),
            pntRelativeZeroContribution (m : ℝ) ρ‖ +
          (‖deriv riemannZeta 0 / riemannZeta 0‖ +
            ‖cofinalTrivialZeroContribution m 0‖) / (m : ℝ))
      atTop (nhds 0) := by
  simpa only [zero_add] using
    (tendsto_naturalPoint_realOrdinateRelativeZeroResidual_of_eventually_nonneg
      height hheight).add
      tendsto_naturalPoint_fixedPNTConstants_zeroDepth_relative

end PrimeNumberTheorem
