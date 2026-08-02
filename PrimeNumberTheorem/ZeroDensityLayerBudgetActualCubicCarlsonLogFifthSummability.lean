import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicCarlsonCertificateBlock

/-!
# Log-fifth summability for actual cubic Carlson blocks

The actual cubic coefficient-square block has dyadic polynomial exponent
`q(sigma) - 6` and asymptotic logarithmic degree five.  This module isolates
the resulting summability mechanism before inserting the concrete certificate
constant.
-/

namespace PrimeNumberTheorem

open Filter

/-- The dyadic geometric ratio corresponding to exponent `q(sigma) - 6`.
It is written through the existing reciprocal-density ratio with input
`q(sigma) - 5`. -/
noncomputable def actualCubicCarlsonDyadicRatio (sigma : ℝ) : ℝ :=
  pntDyadicReciprocalDensityRatio
    (pntCarlsonClassicalDensityExponent sigma - 5)

theorem actualCubicCarlsonDyadicRatio_pos (sigma : ℝ) :
    0 < actualCubicCarlsonDyadicRatio sigma := by
  exact pntDyadicReciprocalDensityRatio_pos _

/-- Six reciprocal dyadic powers leave a strict geometric ratio.  The proof
uses the unconditional bound `q(sigma) - 6 ≤ -5`. -/
theorem actualCubicCarlsonDyadicRatio_lt_one (sigma : ℝ) :
    actualCubicCarlsonDyadicRatio sigma < 1 := by
  apply pntDyadicReciprocalDensityRatio_lt_one
  have hq := actualCubicCarlsonCertificatePolynomialExponent_le_neg_five sigma
  linarith

/-- Canonical log-fifth geometric majorant for actual cubic blocks.  The shift
by one matches Carlson counting at the upper endpoint of a dyadic shell. -/
noncomputable def actualCubicCarlsonDyadicLogFifthMajorant
    (C sigma : ℝ) (n : ℕ) : ℝ :=
  C * ((n + 1 : ℕ) : ℝ) ^ 5 *
    actualCubicCarlsonDyadicRatio sigma ^ (n + 1)

/-- The actual cubic log-fifth dyadic majorant is summable. -/
theorem summable_actualCubicCarlsonDyadicLogFifthMajorant
    (C sigma : ℝ) :
    Summable (actualCubicCarlsonDyadicLogFifthMajorant C sigma) := by
  have hratioPos : 0 < actualCubicCarlsonDyadicRatio sigma :=
    actualCubicCarlsonDyadicRatio_pos sigma
  have hratioNorm : ‖actualCubicCarlsonDyadicRatio sigma‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hratioPos]
    exact actualCubicCarlsonDyadicRatio_lt_one sigma
  have hbase : Summable (fun n : ℕ =>
      (n : ℝ) ^ 5 * actualCubicCarlsonDyadicRatio sigma ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 5 hratioNorm
  have hshift : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ 5 *
        actualCubicCarlsonDyadicRatio sigma ^ (n + 1))) := by
    simpa only using (summable_nat_add_iff 1).mpr hbase
  simpa only [actualCubicCarlsonDyadicLogFifthMajorant, ← mul_assoc] using
    hshift.mul_left C

/-- An eventual log-fifth bound suffices for summability; finitely many initial
dyadic blocks are retained rather than silently discarded. -/
theorem summable_of_eventually_le_actualCubicCarlsonDyadicLogFifthMajorant
    {mass : ℕ → ℝ} {C sigma : ℝ}
    (hmassNonneg : ∀ n, 0 ≤ mass n)
    (hmass : ∀ᶠ n : ℕ in atTop,
      mass n ≤ actualCubicCarlsonDyadicLogFifthMajorant C sigma n) :
    Summable mass := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hmass
  apply (summable_nat_add_iff N).mp
  exact Summable.of_nonneg_of_le
    (fun n => hmassNonneg (n + N))
    (fun n => hN (n + N) (Nat.le_add_left N n))
    ((summable_nat_add_iff N).mpr
      (summable_actualCubicCarlsonDyadicLogFifthMajorant C sigma))

end PrimeNumberTheorem
