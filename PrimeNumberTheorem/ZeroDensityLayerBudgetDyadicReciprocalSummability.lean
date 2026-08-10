import PrimeNumberTheorem.ZeroDensityLayerBudgetWeightedPowerDominatedConvergence

/-!
# Dyadic reciprocal summability below density exponent one

At ordinate scale `2^n`, a zero-density bound of exponent `q` contributes
approximately `2^(n q)` zeros, while the explicit-formula coefficient
`1 / |rho|` contributes `2^(-n)`. The resulting shell ratio is

`exp ((q - 1) * log 2)`.

It is geometrically summable exactly in the range relevant to strict
Carlson strips, `q < 1`.
-/

namespace PrimeNumberTheorem

/-- Geometric ratio left after combining a dyadic `height^q` density cost
with one reciprocal ordinate factor. -/
noncomputable def pntDyadicReciprocalDensityRatio (q : ℝ) : ℝ :=
  Real.exp ((q - 1) * Real.log 2)

theorem pntDyadicReciprocalDensityRatio_pos (q : ℝ) :
    0 < pntDyadicReciprocalDensityRatio q := by
  exact Real.exp_pos _

theorem pntDyadicReciprocalDensityRatio_lt_one
    {q : ℝ} (hq : q < 1) :
    pntDyadicReciprocalDensityRatio q < 1 := by
  unfold pntDyadicReciprocalDensityRatio
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos
    (sub_neg.mpr hq) (Real.log_pos (by norm_num))

/-- Geometric dyadic majorant for a reciprocal-weighted density shell. -/
noncomputable def pntDyadicReciprocalDensityMajorant
    (C q : ℝ) (n : ℕ) : ℝ :=
  C * pntDyadicReciprocalDensityRatio q ^ n

/-- For every `q < 1`, the reciprocal-weighted dyadic density majorant is
summable. -/
theorem summable_pntDyadicReciprocalDensityMajorant
    {C q : ℝ} (hq : q < 1) :
    Summable (pntDyadicReciprocalDensityMajorant C q) := by
  have hratioPos : 0 < pntDyadicReciprocalDensityRatio q :=
    pntDyadicReciprocalDensityRatio_pos q
  have hratioNorm :
      ‖pntDyadicReciprocalDensityRatio q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hratioPos]
    exact pntDyadicReciprocalDensityRatio_lt_one hq
  exact
    (summable_geometric_of_norm_lt_one hratioNorm).mul_left C

/--
Any nonnegative dyadic shell mass bounded by the reciprocal-density
majorant is summable when `q < 1`.

This is the abstract counting-to-weighted-mass interface. A subsequent zeta
specialization must prove the shell bound from Carlson multiplicity counts
and the pointwise estimate `1 / |rho| <= 2^(-n)`.
-/
theorem summable_of_le_pntDyadicReciprocalDensityMajorant
    {mass : ℕ → ℝ} {C q : ℝ}
    (hmassNonneg : ∀ n, 0 ≤ mass n)
    (hmass :
      ∀ n, mass n ≤
        pntDyadicReciprocalDensityMajorant C q n)
    (hq : q < 1) :
    Summable mass := by
  exact Summable.of_nonneg_of_le
    hmassNonneg hmass
    (summable_pntDyadicReciprocalDensityMajorant hq)

end PrimeNumberTheorem
