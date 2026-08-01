import PrimeNumberTheorem.ZeroDensityLayerBudgetStrictMarginOptimalRateRecovery

/-!
# Decay of the actual strict-margin full PNT envelope

The concrete actual-grid majorant from the strict-margin transfer tends to
zero at every positive target rate. Combined with automatic rate recovery,
this supplies a single certificate containing both the real PNT error bound
and convergence of its explicit majorant.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- The rate-independent contour tail `sqrt(log m) / m` tends to zero. -/
theorem tendsto_pntSqrtLog_div_natCast_zero :
    Tendsto (fun m : ℕ => pntSqrtLog m / (m : ℝ)) atTop (nhds 0) := by
  have hlogdiv :
      Tendsto (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ))
        atTop (nhds 0) := by
    simpa using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hlogdiv
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards
      [(Real.tendsto_log_atTop.comp
        tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (1 : ℝ))]
      with m hlog
    have hlog' : 1 ≤ Real.log (m : ℝ) := by
      simpa only [Function.comp_apply] using hlog
    have hsqrt : pntSqrtLog m ≤ Real.log (m : ℝ) := by
      have hsquare := Real.sq_sqrt (le_trans zero_le_one hlog')
      have hsqrt0 : 0 ≤ pntSqrtLog m := Real.sqrt_nonneg _
      dsimp [pntSqrtLog] at hsquare ⊢
      nlinarith
    gcongr

/-- Every term in the rate-independent residual of the actual full PNT
envelope tends to zero. -/
theorem tendsto_actualStrictMarginRateIndependentResidual_zero :
    Tendsto actualStrictMarginRateIndependentResidual atTop (nhds 0) := by
  have htail := tendsto_pntSqrtLog_div_natCast_zero.const_mul
    (2 * cofinalPNTZeroDepthTailConstant)
  convert
    (htail.add tendsto_classicalClosedLogRelativeMajorant_zero).add
      tendsto_abs_actualPNTClosedRealAxisRelativeTerm_natural_zero using 1
  · funext m
    unfold actualStrictMarginRateIndependentResidual
    ring
  · simp

/-- At every positive strict-margin target rate, the complete concrete
actual-grid PNT majorant tends to zero. -/
theorem tendsto_actualStrictMarginGridFullPNTErrorMajorant_zero
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    (C : ℝ) {theta b q : ℝ}
    (htheta : 0 < theta) (hb : 0 < b) (hq : 0 < q) :
    Tendsto
      (actualStrictMarginGridFullPNTErrorMajorant grid C theta b q)
      atTop (nhds 0) := by
  have hbalanced : 0 < classicalAdmissibleBalancedRate (theta * b) :=
    classicalAdmissibleBalancedRate_pos (mul_pos htheta hb)
  have hrate : 0 < classicalAdmissibleBalancedRate (theta * b) / q :=
    div_pos hbalanced hq
  have hcontour :=
    (tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      (classicalAdmissibleBalancedRate (theta * b) / q) hrate 4).const_mul
        (52 * grid.selection.constant)
  have hfinite :=
    (tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      (classicalAdmissibleBalancedRate (theta * b) / q) hrate 2).const_mul
        (18 * C)
  convert
    (hcontour.add hfinite).add
      tendsto_actualStrictMarginRateIndependentResidual_zero using 1
  · funext m
    unfold actualStrictMarginGridFullPNTErrorMajorant
      classicalStrictMarginGridFullBudgetEnvelope
      actualStrictMarginContourCoeff actualStrictMarginFiniteZeroCoeff
    ring
  · simp

/-- The proved zero-free constants automatically supply, for every finite
multiplicative loss `q > 1`, an actual grid whose explicit full-PNT majorant
both dominates the real error and tends to zero. -/
theorem exists_constants_automaticStrictMarginRateRecovery_PNT_majorant_decay :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ (q : ℝ) (selection : UniformNaturalPointGoodHeightSelection),
        1 < q →
          ∃ grid : ActualPintzCarlsonGoodHeightRateGrid,
            grid.rates = {classicalAdmissibleBalancedRate (b / q)} ∧
            grid.baseRate = classicalAdmissibleBalancedRate (b / q) ∧
            classicalAdmissibleBalancedRate b / q ≤ grid.baseRate ∧
            grid.selection = selection ∧
            Tendsto
              (actualStrictMarginGridFullPNTErrorMajorant
                grid C ((1 : ℝ) / q) b 1)
              atTop (nhds 0) ∧
            ∀ᶠ m : ℕ in atTop,
              |relativeChebyshevPsi0Error (m : ℝ)| ≤
                actualStrictMarginGridFullPNTErrorMajorant
                  grid C ((1 : ℝ) / q) b 1 m := by
  rcases exists_constants_automaticStrictMarginRateRecovery_PNT_upper with
    ⟨b, C, hb, hC, hautomatic⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro q selection hq
  rcases hautomatic q selection hq with
    ⟨grid, hrates, hbase, hlower, hselection, herror⟩
  have hqPos : 0 < q := zero_lt_one.trans hq
  have htheta : 0 < (1 : ℝ) / q := div_pos zero_lt_one hqPos
  have hdecay :=
    tendsto_actualStrictMarginGridFullPNTErrorMajorant_zero
      grid C htheta hb (by norm_num : (0 : ℝ) < 1)
  exact ⟨grid, hrates, hbase, hlower, hselection, hdecay, herror⟩

end PrimeNumberTheorem
