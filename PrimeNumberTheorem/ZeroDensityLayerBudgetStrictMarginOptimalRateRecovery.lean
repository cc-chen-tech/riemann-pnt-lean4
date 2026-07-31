import PrimeNumberTheorem.ZeroDensityLayerBudgetAutomaticActualGridDyadicCarlsonFullPNT

/-!
# Quantitative recovery of the non-strict optimal PNT rate

The strict zero-free factor required by the actual selected height retains at
least the same fraction of the formal constrained optimum. This turns every
`q > 1` into an explicit attainable `1 / q` rate guarantee.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- On the unit interval, `theta` is at most its square root. -/
theorem le_sqrt_of_mem_unitInterval
    {theta : ℝ} (htheta : 0 ≤ theta) (hthetaOne : theta ≤ 1) :
    theta ≤ Real.sqrt theta := by
  have hsq : theta ^ 2 ≤ theta := by
    nlinarith [mul_nonneg htheta (sub_nonneg.mpr hthetaOne)]
  calc
    theta = Real.sqrt (theta ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg htheta]
    _ ≤ Real.sqrt theta := Real.sqrt_le_sqrt hsq

/-- Multiplying the formal constrained optimum by `theta` never exceeds the
actual optimum after scaling the zero-free constant by `theta`. -/
theorem theta_mul_classicalAdmissibleBalancedRate_le
    {theta b : ℝ} (htheta : 0 ≤ theta) (hthetaOne : theta ≤ 1) :
    theta * classicalAdmissibleBalancedRate b ≤
      classicalAdmissibleBalancedRate (theta * b) := by
  have hthetaSqrt : theta ≤ Real.sqrt theta :=
    le_sqrt_of_mem_unitInterval htheta hthetaOne
  unfold classicalAdmissibleBalancedRate
  apply le_min
  · calc
      theta * min 1 (Real.sqrt b) ≤ theta * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) htheta
      _ ≤ 1 := by simpa using hthetaOne
  · calc
      theta * min 1 (Real.sqrt b) ≤ theta * Real.sqrt b :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) htheta
      _ ≤ Real.sqrt theta * Real.sqrt b :=
        mul_le_mul_of_nonneg_right hthetaSqrt (Real.sqrt_nonneg _)
      _ = Real.sqrt (theta * b) := by
        simpa using (Real.sqrt_mul htheta b).symm

/-- Every finite multiplicative loss `q > 1` is compatible with the strict
zero-free margin. -/
theorem classicalAdmissibleBalancedRate_div_le_strictMarginRate
    {b q : ℝ} (hq : 1 < q) :
    classicalAdmissibleBalancedRate b / q ≤
      classicalAdmissibleBalancedRate (b / q) := by
  have hqPos : 0 < q := zero_lt_one.trans hq
  have htheta : 0 ≤ (1 : ℝ) / q := (div_pos zero_lt_one hqPos).le
  have hthetaOne : (1 : ℝ) / q ≤ 1 := by
    exact (div_le_iff₀ hqPos).2 (by simpa using hq.le)
  have hmain := theta_mul_classicalAdmissibleBalancedRate_le
    (b := b) htheta hthetaOne
  calc
    classicalAdmissibleBalancedRate b / q =
        ((1 : ℝ) / q) * classicalAdmissibleBalancedRate b := by
      simp [div_eq_mul_inv, mul_comm]
    _ ≤ classicalAdmissibleBalancedRate (((1 : ℝ) / q) * b) := hmain
    _ = classicalAdmissibleBalancedRate (b / q) := by
      simp [div_eq_mul_inv, mul_comm]

/-- The proved classical constants automatically produce, for every `q > 1`,
an actual good-height grid retaining at least `1 / q` of the non-strict
constrained optimum together with the real PNT error bound. -/
theorem exists_constants_automaticStrictMarginRateRecovery_PNT_upper :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ (q : ℝ) (selection : UniformNaturalPointGoodHeightSelection),
        1 < q →
          ∃ grid : ActualPintzCarlsonGoodHeightRateGrid,
            grid.rates = {classicalAdmissibleBalancedRate (b / q)} ∧
            grid.baseRate = classicalAdmissibleBalancedRate (b / q) ∧
            classicalAdmissibleBalancedRate b / q ≤ grid.baseRate ∧
            grid.selection = selection ∧
            ∀ᶠ m : ℕ in atTop,
              |relativeChebyshevPsi0Error (m : ℝ)| ≤
                actualStrictMarginGridFullPNTErrorMajorant
                  grid C ((1 : ℝ) / q) b 1 m := by
  rcases exists_constants_automaticOptimalStrictMarginGrid_PNT_upper with
    ⟨b, C, hb, hC, hautomatic⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro q selection hq
  have hqPos : 0 < q := zero_lt_one.trans hq
  have htheta : 0 < (1 : ℝ) / q := div_pos zero_lt_one hqPos
  have hthetaOne : (1 : ℝ) / q < 1 := by
    exact (div_lt_iff₀ hqPos).2 (by simpa using hq)
  rcases hautomatic ((1 : ℝ) / q) selection htheta hthetaOne with
    ⟨grid, hrates, hbase, hselection, herror⟩
  have hscale : ((1 : ℝ) / q) * b = b / q := by
    simp [div_eq_mul_inv, mul_comm]
  rw [hscale] at hrates hbase
  have hrates' : grid.rates = {classicalAdmissibleBalancedRate (b / q)} :=
    hrates
  have hbase' : grid.baseRate = classicalAdmissibleBalancedRate (b / q) :=
    hbase
  refine ⟨grid, hrates', hbase', ?_, hselection, herror⟩
  rw [hbase']
  exact classicalAdmissibleBalancedRate_div_le_strictMarginRate hq

end PrimeNumberTheorem
