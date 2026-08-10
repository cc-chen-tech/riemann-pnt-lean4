import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightWeightedBalancedExponentUniqueness

/-!
# A finite affine density-exponent optimizer

This module isolates the maximin arithmetic shared by dynamic zero-density
arguments.  Let `floor` be the contour transition exponent.  For strip `i`,
let `slope i > 0` be the growth cost of the density estimate and let
`ceiling i` be its available exponent budget.  A truncation exponent `alpha`
with common decay margin `delta` must satisfy

* `delta <= alpha - floor`;
* `delta <= ceiling i - slope i * alpha` for every strip.

The optimal common margin is the minimum of the pairwise balanced margins

`(ceiling i - slope i * floor) / (1 + slope i)`,

and the optimal truncation exponent is `floor + optimalMargin`.

Nothing here is Carlson-specific.  A Carlson, Bellotti-type, or other
zero-density input can use this optimizer after exposing an affine exponent
majorant.
-/

noncomputable section

namespace PrimeNumberTheorem

/-- The common margin obtained by balancing the contour constraint against
one affine density strip. -/
def finiteAffineStripBalancedMargin
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  (ceiling i - slope i * floor) / (1 + slope i)

/-- The largest common margin allowed by every affine density strip. -/
noncomputable def finiteAffineOptimalMargin
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ) : ℝ :=
  (Finset.univ.image
      (finiteAffineStripBalancedMargin floor ceiling slope)).min'
    (by
      exact
        Finset.Nonempty.image
          Finset.univ_nonempty
          (finiteAffineStripBalancedMargin floor ceiling slope))

/-- The explicit truncation exponent corresponding to the optimal common
margin. -/
noncomputable def finiteAffineBalancedExponent
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ) : ℝ :=
  floor + finiteAffineOptimalMargin floor ceiling slope

/-- Feasibility certificate for a truncation exponent and a common decay
margin against a finite family of affine density budgets. -/
structure FiniteAffineDensityMarginCertificate
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (alpha delta : ℝ) : Prop where
  contour : delta ≤ alpha - floor
  strip : ∀ i, delta ≤ ceiling i - slope i * alpha

/-- The finite optimum is bounded above by each pairwise balanced strip
margin. -/
theorem finiteAffineOptimalMargin_le_strip
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    finiteAffineOptimalMargin floor ceiling slope ≤
      finiteAffineStripBalancedMargin floor ceiling slope i := by
  classical
  unfold finiteAffineOptimalMargin
  apply Finset.min'_le
  simp

/-- A number bounded by every pairwise balanced strip margin is bounded by
the finite optimum. -/
theorem le_finiteAffineOptimalMargin
    {n : ℕ} (floor delta : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (hdelta :
      ∀ i,
        delta ≤
          finiteAffineStripBalancedMargin floor ceiling slope i) :
    delta ≤ finiteAffineOptimalMargin floor ceiling slope := by
  classical
  unfold finiteAffineOptimalMargin
  rw [Finset.le_min'_iff]
  intro value hvalue
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
  exact hdelta i

/-- At least one strip attains the finite optimal balanced margin. -/
theorem exists_strip_eq_finiteAffineOptimalMargin
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ) :
    ∃ i,
      finiteAffineOptimalMargin floor ceiling slope =
        finiteAffineStripBalancedMargin floor ceiling slope i := by
  classical
  have hmem :
      finiteAffineOptimalMargin floor ceiling slope ∈
        Finset.univ.image
          (finiteAffineStripBalancedMargin floor ceiling slope) := by
    unfold finiteAffineOptimalMargin
    apply Finset.min'_mem
  obtain ⟨i, _hi, hvalue⟩ := Finset.mem_image.mp hmem
  exact ⟨i, hvalue.symm⟩

/-- The explicit balanced exponent attains the finite optimal common
margin. -/
theorem finiteAffineBalancedExponent_marginCertificate
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (hslope : ∀ i, 0 < slope i) :
    FiniteAffineDensityMarginCertificate
      floor ceiling slope
      (finiteAffineBalancedExponent floor ceiling slope)
      (finiteAffineOptimalMargin floor ceiling slope) := by
  let delta := finiteAffineOptimalMargin floor ceiling slope
  constructor
  · simp [finiteAffineBalancedExponent, delta]
  · intro i
    have hpair :=
      finiteAffineOptimalMargin_le_strip floor ceiling slope i
    have hdenom : 0 < 1 + slope i := by
      linarith [hslope i]
    rw [finiteAffineStripBalancedMargin,
      le_div_iff₀ hdenom] at hpair
    dsimp [finiteAffineBalancedExponent, delta]
    nlinarith

/-- Every feasible common margin is at most the explicit finite optimum. -/
theorem finiteAffineBalancedExponent_maximizes_margin
    {n : ℕ} {floor alpha delta : ℝ}
    (ceiling slope : Fin (n + 1) → ℝ)
    (hslope : ∀ i, 0 < slope i)
    (certificate :
      FiniteAffineDensityMarginCertificate
        floor ceiling slope alpha delta) :
    delta ≤ finiteAffineOptimalMargin floor ceiling slope := by
  apply le_finiteAffineOptimalMargin floor delta ceiling slope
  intro i
  have hdenom : 0 < 1 + slope i := by
    linarith [hslope i]
  rw [finiteAffineStripBalancedMargin,
    le_div_iff₀ hdenom]
  have hcontour := certificate.contour
  have hstrip := certificate.strip i
  have hscaled :
      slope i * delta ≤ slope i * (alpha - floor) :=
    mul_le_mul_of_nonneg_left hcontour (hslope i).le
  nlinarith

/-- A truncation exponent attaining the optimal common margin is uniquely the
explicit balanced exponent. -/
theorem finiteAffineBalancedExponent_unique
    {n : ℕ} {floor alpha : ℝ}
    (ceiling slope : Fin (n + 1) → ℝ)
    (hslope : ∀ i, 0 < slope i)
    (certificate :
      FiniteAffineDensityMarginCertificate
        floor ceiling slope alpha
        (finiteAffineOptimalMargin floor ceiling slope)) :
    alpha = finiteAffineBalancedExponent floor ceiling slope := by
  let delta := finiteAffineOptimalMargin floor ceiling slope
  have hlower := certificate.contour
  obtain ⟨i, hi⟩ :=
    exists_strip_eq_finiteAffineOptimalMargin floor ceiling slope
  have hdenom : 0 < 1 + slope i := by
    linarith [hslope i]
  have hcross :
      delta * (1 + slope i) =
        ceiling i - slope i * floor := by
    apply (eq_div_iff hdenom.ne').mp
    simpa [delta, finiteAffineStripBalancedMargin] using hi
  have hstrip := certificate.strip i
  unfold finiteAffineBalancedExponent
  dsimp [delta] at hlower hcross hstrip ⊢
  nlinarith [hslope i]

/-- If every strip has positive budget at the contour floor, then the optimal
common margin is strictly positive. -/
theorem finiteAffineOptimalMargin_pos
    {n : ℕ} (floor : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (hslope : ∀ i, 0 < slope i)
    (hbudget : ∀ i, slope i * floor < ceiling i) :
    0 < finiteAffineOptimalMargin floor ceiling slope := by
  classical
  unfold finiteAffineOptimalMargin
  rw [Finset.lt_min'_iff]
  intro value hvalue
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hvalue
  exact
    div_pos
      (sub_pos.mpr (hbudget i))
      (by linarith [hslope i])

end PrimeNumberTheorem
