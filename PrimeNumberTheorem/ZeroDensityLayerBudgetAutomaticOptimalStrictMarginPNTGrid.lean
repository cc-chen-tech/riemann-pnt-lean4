import PrimeNumberTheorem.ZeroDensityLayerBudgetActualStrictMarginGridFullPNTEnvelope

/-!
# Automatic constrained-optimal strict-margin PNT grid

The one-point grid at `classicalAdmissibleBalancedRate (theta * b)` realizes
the exact constrained optimizer of the strict-margin analytic envelope. The
proved classical finite-zero constants then supply an actual PNT error bound
with no manual zero-free or grid-witness inputs.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Actual good-height rate grid concentrated at the exact constrained
optimizer of the strict-margin profile. -/
noncomputable def actualStrictMarginOptimalSingletonGrid
    (theta b : ℝ) (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    ActualPintzCarlsonGoodHeightRateGrid where
  rates := {classicalAdmissibleBalancedRate (theta * b)}
  baseRate := classicalAdmissibleBalancedRate (theta * b)
  baseRate_mem := by simp
  rates_pos := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    subst k
    exact classicalAdmissibleBalancedRate_pos (mul_pos htheta hb)
  baseRate_le := by
    intro k hk
    simp only [Finset.mem_singleton] at hk
    subst k
    exact le_rfl
  selection := selection

@[simp] theorem actualStrictMarginOptimalSingletonGrid_rates
    (theta b : ℝ) (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (actualStrictMarginOptimalSingletonGrid theta b htheta hb selection).rates =
      {classicalAdmissibleBalancedRate (theta * b)} := by
  rfl

@[simp] theorem actualStrictMarginOptimalSingletonGrid_baseRate
    (theta b : ℝ) (htheta : 0 < theta) (hb : 0 < b)
    (selection : UniformNaturalPointGoodHeightSelection) :
    (actualStrictMarginOptimalSingletonGrid theta b htheta hb selection).baseRate =
      classicalAdmissibleBalancedRate (theta * b) := by
  rfl

theorem actualStrictMarginOptimalSingletonRate_pos
    {theta b : ℝ} (htheta : 0 < theta) (hb : 0 < b) :
    0 < classicalAdmissibleBalancedRate (theta * b) :=
  classicalAdmissibleBalancedRate_pos (mul_pos htheta hb)

theorem actualStrictMarginOptimalSingletonRate_le_one
    (theta b : ℝ) :
    classicalAdmissibleBalancedRate (theta * b) ≤ 1 :=
  classicalAdmissibleBalancedRate_le_one (theta * b)

/-- The proved zeta zero-free finite-sum constants automatically yield the
actual relative PNT error bound at the exact constrained-optimal strict-margin
rate. -/
theorem exists_constants_automaticOptimalStrictMarginGrid_PNT_upper :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ (theta : ℝ) (selection : UniformNaturalPointGoodHeightSelection),
        0 < theta → theta < 1 →
          ∃ grid : ActualPintzCarlsonGoodHeightRateGrid,
            grid.rates = {classicalAdmissibleBalancedRate (theta * b)} ∧
            grid.baseRate = classicalAdmissibleBalancedRate (theta * b) ∧
            grid.selection = selection ∧
            ∀ᶠ m : ℕ in atTop,
              |relativeChebyshevPsi0Error (m : ℝ)| ≤
                actualStrictMarginGridFullPNTErrorMajorant
                  grid C theta b 1 m := by
  rcases
      ExplicitFormulaAux.exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq
      with ⟨b, C, hb, hC, hzeros⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro theta selection htheta hthetaOne
  let grid :=
    actualStrictMarginOptimalSingletonGrid theta b htheta hb selection
  let rate := classicalAdmissibleBalancedRate (theta * b)
  refine ⟨grid, ?_, ?_, ?_, ?_⟩
  · simp [grid]
  · simp [grid]
  · rfl
  have hrateMem : rate ∈ grid.rates := by
    simp [grid, rate]
  have hratesOne : ∀ k ∈ grid.rates, k ≤ 1 := by
    intro k hk
    have hkEq : k = rate := by
      simpa [grid, rate] using hk
    rw [hkEq]
    exact classicalAdmissibleBalancedRate_le_one (theta * b)
  have hbound :=
    eventually_abs_relativeChebyshevPsi0Error_le_actualStrictMarginGridMajorant
      (q := 1) (witness := rate)
      grid hb hC htheta hthetaOne hratesOne hrateMem
      (by simp [rate]) le_rfl hzeros
  exact hbound

end PrimeNumberTheorem
