import PrimeNumberTheorem.ZeroDensityLayerBudgetStrictMarginFullRateGapClosure

/-!
# Automatic actual-grid strict-margin full rate gap

The automatic strict-margin grid now carries a complete normalized PNT upper
certificate at every rate strictly below its certified base rate, together
with the corresponding cofinal lower-witness exclusion.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- The proved classical constants automatically supply, for every finite
multiplicative loss, an actual grid with full normalized strict-rate decay and
the matching lower-witness obstruction. -/
theorem exists_constants_automaticStrictMarginFullRateGap_PNT_upper :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ (q : ℝ) (selection : UniformNaturalPointGoodHeightSelection),
        1 < q →
          ∃ grid : ActualPintzCarlsonGoodHeightRateGrid,
            grid.rates = {classicalAdmissibleBalancedRate (b / q)} ∧
            grid.baseRate = classicalAdmissibleBalancedRate (b / q) ∧
            classicalAdmissibleBalancedRate b / q ≤ grid.baseRate ∧
            grid.selection = selection ∧
            (∀ᶠ m : ℕ in atTop,
              |relativeChebyshevPsi0Error (m : ℝ)| ≤
                actualStrictMarginGridFullPNTErrorMajorant
                  grid C ((1 : ℝ) / q) b 1 m) ∧
            ∀ slowerRate : ℝ, slowerRate < grid.baseRate →
              Tendsto
                (fun m : ℕ =>
                  actualStrictMarginGridFullPNTErrorMajorant
                      grid C ((1 : ℝ) / q) b 1 m /
                    pntSqrtLogExponentialAmplitude slowerRate m)
                atTop (nhds 0) ∧
              ¬ ∃ witness : ℕ → ℕ,
                Tendsto witness atTop atTop ∧
                ∀ᶠ j : ℕ in atTop,
                  pntSqrtLogExponentialAmplitude slowerRate (witness j) ≤
                    |relativeChebyshevPsi0Error (witness j : ℝ)| := by
  rcases exists_constants_automaticStrictMarginRateRecovery_PNT_upper with
    ⟨b, C, hb, hC, hautomatic⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro q selection hq
  rcases hautomatic q selection hq with
    ⟨grid, hrates, hbase, hlower, hselection, herror⟩
  refine ⟨grid, hrates, hbase, hlower, hselection, herror, ?_⟩
  intro slowerRate hslower
  have hqPos : 0 < q := zero_lt_one.trans hq
  have htheta : 0 < (1 : ℝ) / q := div_pos zero_lt_one hqPos
  have hscale : ((1 : ℝ) / q) * b = b / q := by
    simp [div_eq_mul_inv, mul_comm]
  have hslower' :
      slowerRate <
        classicalAdmissibleBalancedRate (((1 : ℝ) / q) * b) / 1 := by
    rw [hscale, div_one, ← hbase]
    exact hslower
  have hnormalized :=
    tendsto_actualStrictMarginGridFullPNTErrorMajorant_strictRateGap
      grid C htheta hb (by norm_num : (0 : ℝ) < 1) hslower'
  exact ⟨hnormalized,
    no_cofinalPNTLowerWitness_at_sqrtLogAmplitude herror hnormalized⟩

end PrimeNumberTheorem
