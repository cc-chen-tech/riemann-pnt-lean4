import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalBalancedRateGridApproximation

/-!
# Strict-margin finite-grid transfer for the full actual PNT budget

The additive constant in `log (T + 6)` prevents an exact pointwise use of the
formal zero-free rate `b / k`.  A fixed strict fraction `theta * b / k`, with
`0 < theta < 1`, has the required margin and changes the balanced parameter
from `b` to `theta * b`.

This module proves the arithmetic `1 / q` envelope loss and transfers any
proved per-rate analytic domination to the pointwise minimum actual PNT budget.
It does not assert that the actual domination interface is automatic.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Strictly interior zero-free exponential rate at height rate `k`. -/
noncomputable def classicalStrictMarginZeroFreeRate
    (theta b k : ℝ) : ℝ :=
  theta * b / k

theorem classicalStrictMarginZeroFreeRate_pos
    {theta b k : ℝ} (htheta : 0 < theta) (hb : 0 < b) (hk : 0 < k) :
    0 < classicalStrictMarginZeroFreeRate theta b k := by
  unfold classicalStrictMarginZeroFreeRate
  positivity

/-- The strict fraction supplies the margin required by the actual
`log (T + 6)` zero-free-width calculation. -/
theorem classicalStrictMarginZeroFreeRate_mul_lt
    {theta b k : ℝ} (hb : 0 < b) (htheta : theta < 1) (hk : 0 < k) :
    classicalStrictMarginZeroFreeRate theta b k * k < b := by
  calc
    classicalStrictMarginZeroFreeRate theta b k * k = theta * b := by
      unfold classicalStrictMarginZeroFreeRate
      field_simp [ne_of_gt hk]
    _ < 1 * b := mul_lt_mul_of_pos_right htheta hb
    _ = b := one_mul b

/-- The strict-margin competing rate is exactly the existing classical
balanced profile with parameter `theta * b`. -/
theorem min_rate_strictMarginZeroFreeRate_eq_dynamicBalancedRate
    (theta b k : ℝ) :
    min k (classicalStrictMarginZeroFreeRate theta b k) =
      classicalDynamicBalancedRate (theta * b) k := by
  rfl

/-- Separate contour and zero-free exponentials with a rate-independent
residual. The coefficients may contain logarithmic powers. -/
noncomputable def classicalStrictMarginRateFullBudgetEnvelope
    (contourCoeff zeroCoeff residual : ℕ → ℝ)
    (theta b k : ℝ) (m : ℕ) : ℝ :=
  contourCoeff m * Real.exp (-k * pntSqrtLog m) +
    zeroCoeff m * Real.exp
      (-(classicalStrictMarginZeroFreeRate theta b k) * pntSqrtLog m) +
    residual m

/-- Closed finite-grid envelope retaining the explicit multiplicative
`1 / q` loss from the continuous constrained optimum. -/
noncomputable def classicalStrictMarginGridFullBudgetEnvelope
    (contourCoeff zeroCoeff residual : ℕ → ℝ)
    (theta b q : ℝ) (m : ℕ) : ℝ :=
  2 * (contourCoeff m + zeroCoeff m) *
      Real.exp
        (-(classicalAdmissibleBalancedRate (theta * b) / q) *
          pntSqrtLog m) +
    residual m

/-- Any lower bound on the balanced rate controls the two competing
exponentials. -/
theorem add_competing_exp_le_of_le_dynamicBalancedRate
    {b k target u : ℝ} (hk : 0 < k) (hu : 0 ≤ u)
    (htarget : target ≤ classicalDynamicBalancedRate b k) :
    Real.exp (-k * u) + Real.exp (-(b / k) * u) ≤
      2 * Real.exp (-target * u) := by
  calc
    Real.exp (-k * u) + Real.exp (-(b / k) * u) ≤
        2 * Real.exp (-(classicalDynamicBalancedRate b k) * u) :=
      add_competing_exp_le_balanced_exp hk hu
    _ ≤ 2 * Real.exp (-target * u) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using
        neg_le_neg (mul_le_mul_of_nonneg_right htarget hu)

/-- The Stack 126 envelope-optimal grid rate converts every nonnegative
arbitrary-rate envelope into the explicit `1 / q` closed envelope. -/
theorem classicalStrictMarginRateFullBudgetEnvelope_le_grid
    {theta b q witness : ℝ}
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (contourCoeff zeroCoeff residual : ℕ → ℝ)
    (m : ℕ)
    (htheta : 0 < theta) (hb : 0 < b)
    (hwitness : witness ∈ grid.rates)
    (hlower : classicalAdmissibleBalancedRate (theta * b) / q ≤ witness)
    (hupper : witness ≤ classicalAdmissibleBalancedRate (theta * b))
    (hcontour : 0 ≤ contourCoeff m) (hzero : 0 ≤ zeroCoeff m) :
    classicalStrictMarginRateFullBudgetEnvelope
        contourCoeff zeroCoeff residual theta b
        (classicalBalancedEnvelopeGridOptimalRate (theta * b) grid) m ≤
      classicalStrictMarginGridFullBudgetEnvelope
        contourCoeff zeroCoeff residual theta b q m := by
  let k := classicalBalancedEnvelopeGridOptimalRate (theta * b) grid
  have hkMem : k ∈ grid.rates :=
    classicalBalancedEnvelopeGridOptimalRate_mem (theta * b) grid
  have hk : 0 < k := grid.rates_pos k hkMem
  have hthetaB : 0 < theta * b := mul_pos htheta hb
  have hrate :
      classicalAdmissibleBalancedRate (theta * b) / q ≤
        classicalDynamicBalancedRate (theta * b) k := by
    simpa [k] using
      classicalBalancedEnvelopeGridOptimalRate_ge_admissible_div
        grid hthetaB hwitness hlower hupper
  have hcompeting :
      Real.exp (-k * pntSqrtLog m) +
          Real.exp (-((theta * b) / k) * pntSqrtLog m) ≤
        2 * Real.exp
          (-(classicalAdmissibleBalancedRate (theta * b) / q) *
            pntSqrtLog m) :=
    add_competing_exp_le_of_le_dynamicBalancedRate hk
      (Real.sqrt_nonneg _) hrate
  have hcontourPad :
      contourCoeff m * Real.exp (-k * pntSqrtLog m) ≤
        (contourCoeff m + zeroCoeff m) *
          Real.exp (-k * pntSqrtLog m) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hzero)
      (Real.exp_nonneg _)
  have hzeroPad :
      zeroCoeff m * Real.exp (-((theta * b) / k) * pntSqrtLog m) ≤
        (contourCoeff m + zeroCoeff m) *
          Real.exp (-((theta * b) / k) * pntSqrtLog m) :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hcontour)
      (Real.exp_nonneg _)
  have hweighted := mul_le_mul_of_nonneg_left hcompeting
    (add_nonneg hcontour hzero)
  unfold classicalStrictMarginRateFullBudgetEnvelope
    classicalStrictMarginGridFullBudgetEnvelope
    classicalStrictMarginZeroFreeRate
  change
    contourCoeff m * Real.exp (-k * pntSqrtLog m) +
          zeroCoeff m * Real.exp (-((theta * b) / k) * pntSqrtLog m) +
        residual m ≤
      2 * (contourCoeff m + zeroCoeff m) *
          Real.exp
            (-(classicalAdmissibleBalancedRate (theta * b) / q) *
              pntSqrtLog m) +
        residual m
  calc
    contourCoeff m * Real.exp (-k * pntSqrtLog m) +
          zeroCoeff m * Real.exp (-((theta * b) / k) * pntSqrtLog m) +
        residual m ≤
      ((contourCoeff m + zeroCoeff m) * Real.exp (-k * pntSqrtLog m) +
          (contourCoeff m + zeroCoeff m) *
            Real.exp (-((theta * b) / k) * pntSqrtLog m)) +
        residual m := add_le_add (add_le_add hcontourPad hzeroPad) le_rfl
    _ = (contourCoeff m + zeroCoeff m) *
          (Real.exp (-k * pntSqrtLog m) +
            Real.exp (-((theta * b) / k) * pntSqrtLog m)) +
        residual m := by ring
    _ ≤ (contourCoeff m + zeroCoeff m) *
          (2 * Real.exp
            (-(classicalAdmissibleBalancedRate (theta * b) / q) *
              pntSqrtLog m)) +
        residual m := add_le_add hweighted le_rfl
    _ = 2 * (contourCoeff m + zeroCoeff m) *
          Real.exp
            (-(classicalAdmissibleBalancedRate (theta * b) / q) *
              pntSqrtLog m) +
        residual m := by ring

/-- Explicit interface required to connect an actual Stack 125 rate budget to
the strict-margin classical analytic envelope. -/
def ActualPintzCarlsonRateFullBudgetEnvelopeDominated
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (contourCoeff zeroCoeff residual : ℕ → ℝ)
    (theta b k : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop,
    actualPintzCarlsonRateFullRelativeBudget grid k m ≤
      classicalStrictMarginRateFullBudgetEnvelope
        contourCoeff zeroCoeff residual theta b k m

/-- Per-rate analytic domination transfers to the pointwise minimum complete
actual budget with the explicit finite-grid `1 / q` loss. -/
theorem eventually_actualPintzCarlsonFullBudgetMinimum_le_strictMarginGridEnvelope
    {theta b q witness : ℝ}
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (contourCoeff zeroCoeff residual : ℕ → ℝ)
    (htheta : 0 < theta) (hb : 0 < b)
    (hwitness : witness ∈ grid.rates)
    (hlower : classicalAdmissibleBalancedRate (theta * b) / q ≤ witness)
    (hupper : witness ≤ classicalAdmissibleBalancedRate (theta * b))
    (hcontour : ∀ m, 0 ≤ contourCoeff m)
    (hzero : ∀ m, 0 ≤ zeroCoeff m)
    (hdominated : ∀ k ∈ grid.rates,
      ActualPintzCarlsonRateFullBudgetEnvelopeDominated
        grid contourCoeff zeroCoeff residual theta b k) :
    ∀ᶠ m : ℕ in atTop,
      actualPintzCarlsonFullBudgetMinimum grid m ≤
        classicalStrictMarginGridFullBudgetEnvelope
          contourCoeff zeroCoeff residual theta b q m := by
  let k := classicalBalancedEnvelopeGridOptimalRate (theta * b) grid
  have hk : k ∈ grid.rates :=
    classicalBalancedEnvelopeGridOptimalRate_mem (theta * b) grid
  have hdom := hdominated k hk
  filter_upwards [hdom] with m hm
  calc
    actualPintzCarlsonFullBudgetMinimum grid m ≤
        actualPintzCarlsonRateFullRelativeBudget grid k m := by
      exact actualPintzCarlsonFullBudgetOptimalRate_le_of_mem grid m hk
    _ ≤ classicalStrictMarginRateFullBudgetEnvelope
          contourCoeff zeroCoeff residual theta b k m := hm
    _ ≤ classicalStrictMarginGridFullBudgetEnvelope
          contourCoeff zeroCoeff residual theta b q m := by
      simpa [k] using
        classicalStrictMarginRateFullBudgetEnvelope_le_grid
          grid contourCoeff zeroCoeff residual m htheta hb hwitness
          hlower hupper (hcontour m) (hzero m)

/-- The same closed envelope controls the real relative PNT error because the
Stack 125 pointwise minimum already bounds that error eventually. -/
theorem eventually_abs_relativeChebyshevPsi0Error_le_strictMarginGridEnvelope
    {theta b q witness : ℝ}
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (contourCoeff zeroCoeff residual : ℕ → ℝ)
    (htheta : 0 < theta) (hb : 0 < b)
    (hwitness : witness ∈ grid.rates)
    (hlower : classicalAdmissibleBalancedRate (theta * b) / q ≤ witness)
    (hupper : witness ≤ classicalAdmissibleBalancedRate (theta * b))
    (hcontour : ∀ m, 0 ≤ contourCoeff m)
    (hzero : ∀ m, 0 ≤ zeroCoeff m)
    (hdominated : ∀ k ∈ grid.rates,
      ActualPintzCarlsonRateFullBudgetEnvelopeDominated
        grid contourCoeff zeroCoeff residual theta b k) :
    ∀ᶠ m : ℕ in atTop,
      |relativeChebyshevPsi0Error (m : ℝ)| ≤
        classicalStrictMarginGridFullBudgetEnvelope
          contourCoeff zeroCoeff residual theta b q m := by
  have hminimum :=
    eventually_actualPintzCarlsonFullBudgetMinimum_le_strictMarginGridEnvelope
      grid contourCoeff zeroCoeff residual htheta hb hwitness hlower hupper
      hcontour hzero hdominated
  filter_upwards
      [eventually_abs_relativeChebyshevPsi0Error_le_actualPintzCarlsonFullBudgetMinimum
        grid, hminimum] with m herror hmin
  exact herror.trans hmin

end PrimeNumberTheorem
