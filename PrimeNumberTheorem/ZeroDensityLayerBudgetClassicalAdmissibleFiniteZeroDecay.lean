import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalAdmissibleGoodHeight

open Complex Filter Set Topology

namespace PrimeNumberTheorem

/-- General dynamic-height form of the classical zero-free width calculation.
At height at most `exp (alpha * u)`, a target rate `rate / u` is available
precisely once the strict margin `rate * alpha < b` absorbs the additive
constant in `log (T + 6)`. -/
theorem dynamicHeight_classicalZeroFreeWidth_ge
    {b alpha rate u T : ℝ}
    (halpha : 0 < alpha) (hrate : 0 < rate)
    (hmargin : rate * alpha < b)
    (hu : 0 < u)
    (hthreshold :
      rate * Real.log 8 / (b - rate * alpha) ≤ u)
    (hT : 4 ≤ T)
    (hTupper : T ≤ Real.exp (alpha * u)) :
    rate / u ≤ b / Real.log (T + 6) := by
  have hmarginPos : 0 < b - rate * alpha := sub_pos.mpr hmargin
  let A : ℝ := Real.exp (alpha * u)
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact Real.one_le_exp (mul_nonneg halpha.le hu.le)
  have hTplus : T + 6 ≤ 8 * A := by
    dsimp [A] at hTupper ⊢
    nlinarith
  have hlogUpper :
      Real.log (T + 6) ≤ Real.log 8 + alpha * u := by
    have hlog :=
      Real.log_le_log (by linarith : 0 < T + 6) hTplus
    have hlogA : Real.log A = alpha * u := by
      simp [A]
    rw [Real.log_mul (by norm_num) hApos.ne', hlogA] at hlog
    exact hlog
  have hthresholdMul :
      rate * Real.log 8 ≤ (b - rate * alpha) * u := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (div_le_iff₀ hmarginPos).mp hthreshold
  have hmain :
      rate * (Real.log 8 + alpha * u) ≤ b * u := by
    nlinarith
  have hnumerator :
      rate * Real.log (T + 6) ≤ b * u :=
    (mul_le_mul_of_nonneg_left hlogUpper hrate.le).trans hmain
  have hlogT : 0 < Real.log (T + 6) :=
    Real.log_pos (by linarith)
  exact (div_le_div_iff₀ hu hlogT).2 hnumerator

/-- A generic square-root-logarithmic zero-free width gives the matching real
power bound. -/
theorem rpow_dynamicZeroFreeWidth_le_exp_sqrtRate
    {b rate x T : ℝ}
    (hx : 1 < x)
    (hwidth :
      rate / Real.sqrt (Real.log x) ≤
        b / Real.log (T + 6)) :
    x ^ (1 - b / Real.log (T + 6)) ≤
      x * Real.exp (-rate * Real.sqrt (Real.log x)) := by
  simpa using
    rpow_classicalZeroFreeWidth_le_exp_sqrt
      (b := b) (epsilon := Real.sqrt b - rate)
      (x := x) (T := T) hx (by simpa using hwidth)

/-- At the admissibly optimal selected good height, the complete
multiplicity-weighted finite zero sum divided by the sample scale tends to
zero.  The same height is used by the contour certificate. -/
theorem
    exists_selectedClassicalAdmissibleFiniteZeroSum_relative_tendsto :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ selection : UniformNaturalPointGoodHeightSelection,
        Tendsto
          (fun m : ℕ =>
            ‖finiteNontrivialZeroSumWithMultiplicity
                (m : ℝ)
                (selectedClassicalAdmissibleGoodHeight
                  b selection (m : ℝ))‖ / (m : ℝ))
          atTop (nhds 0) := by
  rcases
      ExplicitFormulaAux.exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq
      with ⟨b, C, hb, hC, hzeros⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro selection
  let alpha : ℝ := classicalAdmissibleBalancedRate b
  let rate : ℝ := alpha / 2
  have halpha : 0 < alpha := by
    exact classicalAdmissibleBalancedRate_pos hb
  have halphaOne : alpha ≤ 1 := by
    exact classicalAdmissibleBalancedRate_le_one b
  have hrate : 0 < rate := by
    dsimp [rate]
    linarith
  have halphaSquare : alpha ^ 2 ≤ b := by
    have hzeroFree :=
      classicalAdmissibleBalancedRate_le_zeroFreeRate hb
    have hmul :=
      (le_div_iff₀ halpha).mp hzeroFree
    nlinarith
  have hmargin : rate * alpha < b := by
    dsimp [rate]
    nlinarith [sq_pos_of_pos halpha]
  let majorant : ℕ → ℝ := fun m =>
    9 * C * pntSqrtLog m ^ 2 *
      Real.exp (-rate * pntSqrtLog m)
  have hmajorant :
      Tendsto majorant atTop (nhds 0) := by
    have hdecay :=
      tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
        rate hrate 2
    simpa [majorant, mul_assoc] using hdecay.const_mul (9 * C)
  refine squeeze_zero' (g := majorant) ?_ ?_ hmajorant
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  · have hheightReal :=
      eventually_selectedClassicalAdmissibleGoodHeight_mem hb selection
    have hheightNat :=
      tendsto_natCast_atTop_atTop.eventually hheightReal
    have hHeightLargeReal :
        ∀ᶠ x : ℝ in atTop,
          9 ≤ pintzCarlsonHeight alpha x :=
      (tendsto_atTop.1
        (tendsto_pintzCarlsonHeight_atTop halpha)) 9
    have hHeightLargeNat :=
      tendsto_natCast_atTop_atTop.eventually hHeightLargeReal
    have hscale :
        Tendsto pntSqrtLog atTop atTop :=
      tendsto_pntSqrtLog_atTop
    have hlarge :
        ∀ᶠ m : ℕ in atTop,
          max
              (rate * Real.log 8 / (b - rate * alpha))
              (max (Real.log 8) 1) ≤
            pntSqrtLog m :=
      hscale.eventually
        (eventually_ge_atTop
          (max
            (rate * Real.log 8 / (b - rate * alpha))
            (max (Real.log 8) 1)))
    filter_upwards
        [hheightNat, hHeightLargeNat, hlarge,
          eventually_ge_atTop (3 : ℕ)]
        with m hmHeight hmHeightLarge hmLarge hm
    let x : ℝ := m
    let T : ℝ :=
      selectedClassicalAdmissibleGoodHeight b selection (m : ℝ)
    let u : ℝ := pntSqrtLog m
    have hx : 1 < x := by
      dsimp [x]
      exact_mod_cast (show 1 < m by omega)
    have hxpos : 0 < x := zero_lt_one.trans hx
    have hu : 0 < u := by
      dsimp [u, pntSqrtLog]
      exact Real.sqrt_pos.2 (Real.log_pos hx)
    have huLogEight : Real.log 8 ≤ u :=
      (le_max_left (Real.log 8) 1).trans
        ((le_max_right
          (rate * Real.log 8 / (b - rate * alpha))
          (max (Real.log 8) 1)).trans hmLarge)
    have huOne : 1 ≤ u :=
      (le_max_right (Real.log 8) 1).trans
        ((le_max_right
          (rate * Real.log 8 / (b - rate * alpha))
          (max (Real.log 8) 1)).trans hmLarge)
    have hthreshold :
        rate * Real.log 8 / (b - rate * alpha) ≤ u :=
      (le_max_left
        (rate * Real.log 8 / (b - rate * alpha))
        (max (Real.log 8) 1)).trans hmLarge
    have hTupper :
        T ≤ Real.exp (alpha * u) := by
      have hupper := hmHeight.2
      dsimp [T, alpha, u]
      simpa [pintzCarlsonGoodHeightBase, pintzCarlsonHeight,
        pintzCarlsonSqrtLogScale, pntSqrtLog] using hupper
    have hT : 4 ≤ T := by
      have hbase :
          8 ≤ pintzCarlsonGoodHeightBase alpha x := by
        dsimp [pintzCarlsonGoodHeightBase, x] at hmHeightLarge ⊢
        linarith
      exact le_trans (by norm_num) (hbase.trans hmHeight.1)
    have hwidth :
        rate / Real.sqrt (Real.log x) ≤
          b / Real.log (T + 6) := by
      apply dynamicHeight_classicalZeroFreeWidth_ge
        halpha hrate hmargin hu hthreshold hT
      simpa [u, pntSqrtLog] using hTupper
    have hrpow :
        x ^ (1 - b / Real.log (T + 6)) ≤
          x * Real.exp (-rate * Real.sqrt (Real.log x)) :=
      rpow_dynamicZeroFreeWidth_le_exp_sqrtRate hx hwidth
    have hzero :=
      hzeros x T hx hT
    have hHpos : 0 < Real.exp (alpha * u) :=
      Real.exp_pos _
    have hTplus : T + 6 ≤ 8 * Real.exp (alpha * u) := by
      nlinarith [Real.one_le_exp
        (mul_nonneg halpha.le hu.le)]
    have hlogUpper :
        Real.log (T + 6) ≤ Real.log 8 + alpha * u := by
      have hlog :=
        Real.log_le_log (by linarith : 0 < T + 6) hTplus
      rw [Real.log_mul (by norm_num) hHpos.ne',
        Real.log_exp] at hlog
      exact hlog
    have hlogTwoU : Real.log (T + 6) ≤ 2 * u := by
      nlinarith [mul_le_mul_of_nonneg_right halphaOne hu.le]
    have hlog0 : 0 ≤ 1 + Real.log (T + 6) := by
      have := Real.log_nonneg (by linarith : 1 ≤ T + 6)
      linarith
    have hlogBound :
        (1 + Real.log (T + 6)) ^ 2 ≤ 9 * u ^ 2 := by
      have hlinear : 1 + Real.log (T + 6) ≤ 3 * u := by
        linarith
      nlinarith
    have hzeroExp :
        ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
          C * (x * Real.exp (-rate * Real.sqrt (Real.log x))) *
            (1 + Real.log (T + 6)) ^ 2 := by
      exact hzero.trans (by gcongr)
    calc
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ / x ≤
          (C * (x * Real.exp (-rate * Real.sqrt (Real.log x))) *
            (1 + Real.log (T + 6)) ^ 2) / x :=
        div_le_div_of_nonneg_right hzeroExp hxpos.le
      _ = C * Real.exp (-rate * u) *
          (1 + Real.log (T + 6)) ^ 2 := by
        dsimp [u, pntSqrtLog, x]
        field_simp [hxpos.ne']
      _ ≤ C * Real.exp (-rate * u) * (9 * u ^ 2) := by
        gcongr
      _ = majorant m := by
        dsimp [majorant, u]
        ring

end PrimeNumberTheorem
