import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalStrictMarginGridFullBudgetTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetClassicalAdmissibleFiniteZeroDecay

/-!
# Actual finite-zero majorant at strict-margin grid heights

At the actual selected good height below `exp (k * sqrt (log m))`, the proved
classical zero-free finite-sum estimate has every strict rate
`theta * b / k`, with `0 < theta < 1`.  This module makes the resulting
relative finite-zero bound explicit and uniform over a finite rate grid.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- Closed relative finite-zero majorant at a strict zero-free rate. -/
noncomputable def classicalStrictMarginFiniteZeroRelativeMajorant
    (C theta b k : ℝ) (m : ℕ) : ℝ :=
  9 * C * pntSqrtLog m ^ 2 *
    Real.exp
      (-(classicalStrictMarginZeroFreeRate theta b k) * pntSqrtLog m)

theorem classicalStrictMarginFiniteZeroRelativeMajorant_nonneg
    {C theta b k : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    0 ≤ classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m := by
  unfold classicalStrictMarginFiniteZeroRelativeMajorant
  positivity

/-- The actual finite zero sum at one certified grid rate is eventually
bounded by the strict-margin square-root-logarithmic majorant. -/
theorem eventually_actualPintzCarlsonRate_finiteZeroRelative_le_strictMarginMajorant
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {b C theta k : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C)
    (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hk : k ∈ grid.rates) (hkOne : k ≤ 1)
    (hzeros : ∀ x T : ℝ, 1 < x → 4 ≤ T →
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        C * x ^ (1 - b / Real.log (T + 6)) *
          (1 + Real.log (T + 6)) ^ 2) :
    ∀ᶠ m : ℕ in atTop,
      ‖finiteNontrivialZeroSumWithMultiplicity (m : ℝ)
          (actualPintzCarlsonRateCandidateHeight grid k (m : ℝ))‖ /
          (m : ℝ) ≤
        classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m := by
  let rate : ℝ := classicalStrictMarginZeroFreeRate theta b k
  have hkPos : 0 < k := grid.rates_pos k hk
  have hrate : 0 < rate := by
    exact classicalStrictMarginZeroFreeRate_pos htheta hb hkPos
  have hmargin : rate * k < b := by
    exact classicalStrictMarginZeroFreeRate_mul_lt hb hthetaOne hkPos
  have hheight := eventually_actualPintzCarlsonRateCandidateHeight_mem grid hk
  have hheightLarge :
      ∀ᶠ m : ℕ in atTop, 9 ≤ pintzCarlsonHeight k (m : ℝ) :=
    (tendsto_atTop.1
      ((tendsto_pintzCarlsonHeight_atTop hkPos).comp
        tendsto_natCast_atTop_atTop)) 9
  have hscale :
      ∀ᶠ m : ℕ in atTop,
        max (rate * Real.log 8 / (b - rate * k))
            (max (Real.log 8) 1) ≤ pntSqrtLog m :=
    tendsto_pntSqrtLog_atTop.eventually
      (eventually_ge_atTop
        (max (rate * Real.log 8 / (b - rate * k))
          (max (Real.log 8) 1)))
  filter_upwards [hheight, hheightLarge, hscale,
      eventually_ge_atTop (3 : ℕ)] with m hmHeight hmHeightLarge hmScale hm
  let x : ℝ := m
  let T : ℝ := actualPintzCarlsonRateCandidateHeight grid k (m : ℝ)
  let u : ℝ := pntSqrtLog m
  have hx : 1 < x := by
    dsimp [x]
    exact_mod_cast (show 1 < m by omega)
  have hxPos : 0 < x := zero_lt_one.trans hx
  have hu : 0 < u := by
    dsimp [u, pntSqrtLog]
    exact Real.sqrt_pos.2 (Real.log_pos hx)
  have huLogEight : Real.log 8 ≤ u :=
    (le_max_left (Real.log 8) 1).trans
      ((le_max_right (rate * Real.log 8 / (b - rate * k))
        (max (Real.log 8) 1)).trans hmScale)
  have huOne : 1 ≤ u :=
    (le_max_right (Real.log 8) 1).trans
      ((le_max_right (rate * Real.log 8 / (b - rate * k))
        (max (Real.log 8) 1)).trans hmScale)
  have hthreshold :
      rate * Real.log 8 / (b - rate * k) ≤ u :=
    (le_max_left (rate * Real.log 8 / (b - rate * k))
      (max (Real.log 8) 1)).trans hmScale
  have hTupper : T ≤ Real.exp (k * u) := by
    have hupper := hmHeight.2
    dsimp [T, u]
    simpa [pintzCarlsonGoodHeightBase, pintzCarlsonHeight,
      pintzCarlsonSqrtLogScale, pntSqrtLog] using hupper
  have hT : 4 ≤ T := by
    have hbase : 8 ≤ pintzCarlsonGoodHeightBase k (m : ℝ) := by
      dsimp [pintzCarlsonGoodHeightBase] at hmHeightLarge ⊢
      linarith
    exact le_trans (by norm_num) (hbase.trans hmHeight.1)
  have hwidth :
      rate / Real.sqrt (Real.log x) ≤ b / Real.log (T + 6) := by
    apply dynamicHeight_classicalZeroFreeWidth_ge
      hkPos hrate hmargin hu hthreshold hT
    simpa [u, pntSqrtLog] using hTupper
  have hrpow :
      x ^ (1 - b / Real.log (T + 6)) ≤
        x * Real.exp (-rate * Real.sqrt (Real.log x)) :=
    rpow_dynamicZeroFreeWidth_le_exp_sqrtRate hx hwidth
  have hzero := hzeros x T hx hT
  have hExpPos : 0 < Real.exp (k * u) := Real.exp_pos _
  have hTplus : T + 6 ≤ 8 * Real.exp (k * u) := by
    nlinarith [Real.one_le_exp (mul_nonneg hkPos.le hu.le)]
  have hlogUpper :
      Real.log (T + 6) ≤ Real.log 8 + k * u := by
    have hlog := Real.log_le_log (by linarith : 0 < T + 6) hTplus
    rw [Real.log_mul (by norm_num) hExpPos.ne', Real.log_exp] at hlog
    exact hlog
  have hlogTwoU : Real.log (T + 6) ≤ 2 * u := by
    nlinarith [mul_le_mul_of_nonneg_right hkOne hu.le]
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
          (1 + Real.log (T + 6)) ^ 2 :=
    hzero.trans (by gcongr)
  calc
    ‖finiteNontrivialZeroSumWithMultiplicity x T‖ / x ≤
        (C * (x * Real.exp (-rate * Real.sqrt (Real.log x))) *
          (1 + Real.log (T + 6)) ^ 2) / x :=
      div_le_div_of_nonneg_right hzeroExp hxPos.le
    _ = C * Real.exp (-rate * u) *
        (1 + Real.log (T + 6)) ^ 2 := by
      dsimp [u, pntSqrtLog, x]
      field_simp [hxPos.ne']
    _ ≤ C * Real.exp (-rate * u) * (9 * u ^ 2) := by
      gcongr
    _ = classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m := by
      dsimp [classicalStrictMarginFiniteZeroRelativeMajorant, rate, u]
      ring

/-- The proved zeta zero-free finite-sum theorem supplies one pair of
constants that works for every admissible rate in the finite grid. -/
theorem exists_constants_actualPintzCarlsonGrid_finiteZeroRelative_le_strictMarginMajorant
    (grid : ActualPintzCarlsonGoodHeightRateGrid)
    {theta : ℝ} (htheta : 0 < theta) (hthetaOne : theta < 1)
    (hratesOne : ∀ k ∈ grid.rates, k ≤ 1) :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧
      ∀ k ∈ grid.rates,
        ∀ᶠ m : ℕ in atTop,
          ‖finiteNontrivialZeroSumWithMultiplicity (m : ℝ)
              (actualPintzCarlsonRateCandidateHeight grid k (m : ℝ))‖ /
              (m : ℝ) ≤
            classicalStrictMarginFiniteZeroRelativeMajorant C theta b k m := by
  rcases
      ExplicitFormulaAux.exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq
      with ⟨b, C, hb, hC, hzeros⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro k hk
  exact
    eventually_actualPintzCarlsonRate_finiteZeroRelative_le_strictMarginMajorant
      grid hb hC htheta hthetaOne hk (hratesOne k hk) hzeros

end PrimeNumberTheorem
