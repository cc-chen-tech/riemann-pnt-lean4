import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlson
import PrimeNumberTheorem.ZeroDensityLayerBudgetDyadicReciprocalSummability

/-!
# Carlson dyadic reciprocal summability

Carlson's classical fixed-strip density exponent is

`q(sigma) = 4 * sigma * (1 - sigma)`.

For every strict strip `1 / 2 < sigma`, this exponent is strictly below one.
Consequently the reciprocal-height gain in the explicit-formula coefficient
turns the dyadic shell factor into a geometric ratio below one.

The Carlson majorant also contains `(log T)^4`.  On dyadic heights this becomes
a fourth-degree polynomial in the shell index.  The resulting
`n^4 * ratio^n` majorant remains summable.
-/

namespace PrimeNumberTheorem

/-- The polynomial height exponent in Carlson's classical zero-density
majorant at real-part threshold `sigma`. -/
def pntCarlsonClassicalDensityExponent (sigma : ℝ) : ℝ :=
  4 * sigma * (1 - sigma)

/-- Strictly to the right of the critical line, Carlson's classical density
exponent is strictly below one. -/
theorem pntCarlsonClassicalDensityExponent_lt_one
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    pntCarlsonClassicalDensityExponent sigma < 1 := by
  have hpos : 0 < 2 * sigma - 1 := by
    linarith
  have hsq : 0 < (2 * sigma - 1) * (2 * sigma - 1) :=
    mul_pos hpos hpos
  unfold pntCarlsonClassicalDensityExponent
  nlinarith

/-- In a genuine Carlson strip, the classical density exponent lies strictly
between zero and one. -/
theorem pntCarlsonClassicalDensityExponent_mem_Ioo
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) (hone : sigma < 1) :
    pntCarlsonClassicalDensityExponent sigma ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · unfold pntCarlsonClassicalDensityExponent
    have hsigma : 0 < sigma := by
      linarith
    exact mul_pos (mul_pos (by norm_num) hsigma) (sub_pos.mpr hone)
  · exact pntCarlsonClassicalDensityExponent_lt_one hhalf

/-- The reciprocal-height dyadic ratio attached to Carlson's actual classical
density exponent. -/
noncomputable def pntCarlsonDyadicReciprocalRatio (sigma : ℝ) : ℝ :=
  pntDyadicReciprocalDensityRatio
    (pntCarlsonClassicalDensityExponent sigma)

theorem pntCarlsonDyadicReciprocalRatio_pos (sigma : ℝ) :
    0 < pntCarlsonDyadicReciprocalRatio sigma := by
  exact pntDyadicReciprocalDensityRatio_pos _

theorem pntCarlsonDyadicReciprocalRatio_lt_one
    {sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    pntCarlsonDyadicReciprocalRatio sigma < 1 := by
  exact pntDyadicReciprocalDensityRatio_lt_one
    (pntCarlsonClassicalDensityExponent_lt_one hhalf)

/-- Dyadic Carlson majorant after combining the reciprocal-height coefficient
with the fourth-power logarithmic loss. -/
noncomputable def pntCarlsonDyadicLogFourthMajorant
    (C sigma : ℝ) (n : ℕ) : ℝ :=
  C * (n : ℝ) ^ 4 * pntCarlsonDyadicReciprocalRatio sigma ^ n

/-- The dyadic reciprocal Carlson majorant remains summable after retaining
the full fourth-power logarithmic loss. -/
theorem summable_pntCarlsonDyadicLogFourthMajorant
    {C sigma : ℝ} (hhalf : 1 / 2 < sigma) :
    Summable (pntCarlsonDyadicLogFourthMajorant C sigma) := by
  have hratioPos : 0 < pntCarlsonDyadicReciprocalRatio sigma :=
    pntCarlsonDyadicReciprocalRatio_pos sigma
  have hratioNorm :
      ‖pntCarlsonDyadicReciprocalRatio sigma‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hratioPos]
    exact pntCarlsonDyadicReciprocalRatio_lt_one hhalf
  change Summable (fun n : ℕ =>
    C * (n : ℝ) ^ 4 * pntCarlsonDyadicReciprocalRatio sigma ^ n)
  simpa only [mul_assoc] using
    (summable_pow_mul_geometric_of_norm_lt_one
      (R := ℝ) 4 hratioNorm).mul_left C

/-- Any nonnegative shell mass bounded by the full dyadic Carlson reciprocal
majorant is summable. -/
theorem summable_of_le_pntCarlsonDyadicLogFourthMajorant
    {mass : ℕ → ℝ} {C sigma : ℝ}
    (hmassNonneg : ∀ n, 0 ≤ mass n)
    (hmass :
      ∀ n, mass n ≤
        pntCarlsonDyadicLogFourthMajorant C sigma n)
    (hhalf : 1 / 2 < sigma) :
    Summable mass := by
  exact Summable.of_nonneg_of_le
    hmassNonneg hmass
    (summable_pntCarlsonDyadicLogFourthMajorant hhalf)

end PrimeNumberTheorem
