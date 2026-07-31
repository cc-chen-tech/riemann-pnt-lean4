import PrimeNumberTheorem.ZeroDensityLayerBudgetActualPintzCarlsonFullBudgetRateOptimizer
import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalAdmissibleBalancedRate

/-!
# Quantitative finite-grid approximation of the classical balanced rate

The actual full PNT budget is discontinuous in the rate because zero counts and
chosen good heights can jump.  The continuous analytic envelope, however, has
rate `min k (b / k)`.  This module proves an explicit multiplicative grid loss
for that envelope without asserting continuity of the actual budget.
-/

namespace PrimeNumberTheorem

/-- Below the constrained balanced optimizer, the contour rate is the active
branch of the classical dynamic envelope. -/
theorem classicalDynamicBalancedRate_eq_rate_of_le_admissible
    {b k : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hkle : k ≤ classicalAdmissibleBalancedRate b) :
    classicalDynamicBalancedRate b k = k := by
  have hksqrt : k ≤ Real.sqrt b :=
    hkle.trans (classicalAdmissibleBalancedRate_le_sqrt b)
  have hsqrt0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hprod :
      0 ≤ (Real.sqrt b - k) * (Real.sqrt b + k) :=
    mul_nonneg (sub_nonneg.mpr hksqrt) (add_nonneg hsqrt0 hk.le)
  have hsquare : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.le
  have hksquare : k * k ≤ b := by
    nlinarith
  have hquot : k ≤ b / k := by
    apply (le_div_iff₀ hk).2
    nlinarith
  rw [classicalDynamicBalancedRate, min_eq_left hquot]

/-- A rate within a factor `q` below the continuous constrained optimizer
retains at least a `1 / q` fraction of its optimal envelope rate. -/
theorem classicalDynamicBalancedRate_ge_admissible_div
    {b q k : ℝ} (hb : 0 < b) (hk : 0 < k)
    (hlower : classicalAdmissibleBalancedRate b / q ≤ k)
    (hupper : k ≤ classicalAdmissibleBalancedRate b) :
    classicalAdmissibleBalancedRate b / q ≤
      classicalDynamicBalancedRate b k := by
  rw [classicalDynamicBalancedRate_eq_rate_of_le_admissible hb hk hupper]
  exact hlower

/-- The same multiplicative rate guarantee controls the two competing
exponential errors. -/
theorem add_competing_exp_le_admissible_grid_exp
    {b q k u : ℝ} (hb : 0 < b) (hk : 0 < k) (hu : 0 ≤ u)
    (hlower : classicalAdmissibleBalancedRate b / q ≤ k)
    (hupper : k ≤ classicalAdmissibleBalancedRate b) :
    Real.exp (-k * u) + Real.exp (-(b / k) * u) ≤
      2 * Real.exp
        (-(classicalAdmissibleBalancedRate b / q) * u) := by
  have hbalanced := add_competing_exp_le_balanced_exp
    (b := b) (alpha := k) (u := u) hk hu
  have hrate :=
    classicalDynamicBalancedRate_ge_admissible_div
      hb hk hlower hupper
  calc
    Real.exp (-k * u) + Real.exp (-(b / k) * u) ≤
        2 * Real.exp (-(classicalDynamicBalancedRate b k) * u) :=
      hbalanced
    _ ≤ 2 * Real.exp
          (-(classicalAdmissibleBalancedRate b / q) * u) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right hrate hu)

/-- The finite set of positive rate values as a `FiniteHeightGrid`, used only
to reuse exact finite minimization. -/
def actualPintzCarlsonRateValueFiniteGrid
    (grid : ActualPintzCarlsonGoodHeightRateGrid) : FiniteHeightGrid where
  heights := grid.rates
  nonempty := ⟨grid.baseRate, grid.baseRate_mem⟩
  positive := grid.rates_pos

/-- Rate maximizing the continuous classical balanced envelope on the finite
grid, implemented by minimizing its negative. -/
noncomputable def classicalBalancedEnvelopeGridOptimalRate
    (b : ℝ) (grid : ActualPintzCarlsonGoodHeightRateGrid) : ℝ :=
  finiteGridOptimalHeight
    (fun k => -classicalDynamicBalancedRate b k)
    (actualPintzCarlsonRateValueFiniteGrid grid)

theorem classicalBalancedEnvelopeGridOptimalRate_mem
    (b : ℝ) (grid : ActualPintzCarlsonGoodHeightRateGrid) :
    classicalBalancedEnvelopeGridOptimalRate b grid ∈ grid.rates :=
  finiteGridOptimalHeight_mem
    (fun k => -classicalDynamicBalancedRate b k)
    (actualPintzCarlsonRateValueFiniteGrid grid)

/-- Exact maximality of the selected envelope rate on the finite grid. -/
theorem classicalBalancedEnvelopeGridOptimalRate_maximal
    (b : ℝ) (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {k : ℝ} (hk : k ∈ grid.rates) :
    classicalDynamicBalancedRate b k ≤
      classicalDynamicBalancedRate b
        (classicalBalancedEnvelopeGridOptimalRate b grid) := by
  have hmin := finiteGridOptimalHeight_le_of_mem
    (fun rate => -classicalDynamicBalancedRate b rate)
    (actualPintzCarlsonRateValueFiniteGrid grid) hk
  have hmin' :
      -classicalDynamicBalancedRate b
          (classicalBalancedEnvelopeGridOptimalRate b grid) ≤
        -classicalDynamicBalancedRate b k := by
    simpa [classicalBalancedEnvelopeGridOptimalRate] using hmin
  linarith

/-- If the finite grid contains one lower multiplicative approximation to the
continuous optimizer, its envelope-optimal rate retains the same guarantee. -/
theorem classicalBalancedEnvelopeGridOptimalRate_ge_admissible_div
    {b q k : ℝ} (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (hb : 0 < b) (hk : k ∈ grid.rates)
    (hlower : classicalAdmissibleBalancedRate b / q ≤ k)
    (hupper : k ≤ classicalAdmissibleBalancedRate b) :
    classicalAdmissibleBalancedRate b / q ≤
      classicalDynamicBalancedRate b
        (classicalBalancedEnvelopeGridOptimalRate b grid) := by
  exact
    (classicalDynamicBalancedRate_ge_admissible_div
      hb (grid.rates_pos k hk) hlower hupper).trans
        (classicalBalancedEnvelopeGridOptimalRate_maximal b grid hk)

/-- No admissible finite-grid rate can beat the continuous constrained
optimizer. -/
theorem classicalBalancedEnvelopeGridOptimalRate_le_admissible
    {b : ℝ} (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (hb : 0 < b) (hratesOne : ∀ k ∈ grid.rates, k ≤ 1) :
    classicalDynamicBalancedRate b
        (classicalBalancedEnvelopeGridOptimalRate b grid) ≤
      classicalAdmissibleBalancedRate b := by
  have hmem := classicalBalancedEnvelopeGridOptimalRate_mem b grid
  exact classicalDynamicBalancedRate_le_admissible hb
    (grid.rates_pos _ hmem) (hratesOne _ hmem)

/-- Quantitative sandwich for the finite-grid envelope optimum. -/
theorem classicalBalancedEnvelopeGridOptimalRate_approximation
    {b q k : ℝ} (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (hb : 0 < b) (hk : k ∈ grid.rates)
    (hlower : classicalAdmissibleBalancedRate b / q ≤ k)
    (hupper : k ≤ classicalAdmissibleBalancedRate b)
    (hratesOne : ∀ rate ∈ grid.rates, rate ≤ 1) :
    classicalAdmissibleBalancedRate b / q ≤
        classicalDynamicBalancedRate b
          (classicalBalancedEnvelopeGridOptimalRate b grid) ∧
      classicalDynamicBalancedRate b
          (classicalBalancedEnvelopeGridOptimalRate b grid) ≤
        classicalAdmissibleBalancedRate b :=
  ⟨classicalBalancedEnvelopeGridOptimalRate_ge_admissible_div
      grid hb hk hlower hupper,
    classicalBalancedEnvelopeGridOptimalRate_le_admissible
      grid hb hratesOne⟩

end PrimeNumberTheorem
