import PrimeNumberTheorem.ZeroDensityLayerBudgetActualMovingCarlsonPositiveTailTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetActualFullTailConjugation

/-!
# Full finite zero-tail transfer for the moving Carlson decomposition

Complex conjugation turns the positive-tail decay from the moving Carlson
decomposition into decay of the complete finite zero sum.  The real-ordinate
residual remains explicit because positive-height Carlson counts do not see it.
-/

namespace PrimeNumberTheorem

open Filter
open scoped Topology

/-- The fully automatic moving strip, an explicit middle-strip decay, and an
explicit real-ordinate residual decay force the complete finite zeta-zero tail
to vanish along natural points. -/
theorem tendsto_dynamicFullPNTZeroTailNorm_of_actualMovingCarlson
    {alpha epsilonLow : ℝ} {delta : ℕ → ℝ}
    (halpha : 0 < alpha)
    (hepsilonLow : 0 < epsilonLow)
    (hlowMargin : alpha + epsilonLow < 1 / 2)
    (hdelta : ∀ᶠ m : ℕ in atTop,
      0 < delta m ∧ delta m ≤ 1 / 8 ∧
        128 * alpha * delta m ≤ 1)
    (hgap : IsCarlsonMovingQuadraticLogPowerGap delta)
    (hcap : ∀ᶠ m : ℕ in atTop,
      ActualMovingPositiveRightEdgeCap alpha delta m)
    (hmiddle :
      Tendsto (actualMovingCarlsonMiddleMass alpha delta)
        atTop (nhds 0))
    (hreal :
      Tendsto
        (fun m : ℕ =>
          dynamicRealOrdinatePNTZeroTailNorm
            (carlsonPolynomialHeight alpha) (m : ℝ))
        atTop (nhds 0)) :
    Tendsto
      (fun m : ℕ =>
        dynamicFullPNTZeroTailNorm
          (carlsonPolynomialHeight alpha) (m : ℝ))
      atTop (nhds 0) := by
  have hpositive :=
    tendsto_dynamicPositivePNTTailNorm_of_actualMovingCarlson
      halpha hepsilonLow hlowMargin hdelta hgap hcap hmiddle
  have hmajorant :
      Tendsto
        (fun m : ℕ =>
          dynamicPositivePNTTailNorm
              (carlsonPolynomialHeight alpha) (m : ℝ) +
            dynamicPositivePNTTailNorm
              (carlsonPolynomialHeight alpha) (m : ℝ) +
            dynamicRealOrdinatePNTZeroTailNorm
              (carlsonPolynomialHeight alpha) (m : ℝ))
        atTop (nhds 0) := by
    simpa using (hpositive.add hpositive).add hreal
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards with m
    exact norm_nonneg _
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmPos : 0 < (m : ℝ) := by
      exact_mod_cast hm
    exact dynamicFullPNTZeroTailNorm_le_two_positive_add_real hmPos

end PrimeNumberTheorem
