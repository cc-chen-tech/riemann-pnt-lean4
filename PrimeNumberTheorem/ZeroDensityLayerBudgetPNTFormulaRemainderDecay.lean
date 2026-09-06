import PrimeNumberTheorem.PNTAsymptotics
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTFixedResidualDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTGoodHeightCarlsonCeiling

/-!
# Decay of the cofinal PNT contour remainder

At depth zero and a good height in the unit interval immediately below

`H_k(m) = exp (k * sqrt (log m))`,

the relative contour remainder is bounded by a sum of

`u^4 exp (-k u)` and `u / m`, where `u = sqrt (log m)`.

This is the missing analytic residual estimate needed after the hybrid density
and real-ordinate zero terms have been shown to vanish.
-/

open Filter
open scoped BigOperators

namespace PrimeNumberTheorem

/-- Fixed coefficient in the depth-zero left-contour remainder. -/
noncomputable def cofinalPNTZeroDepthTailConstant : ℝ :=
  ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
    ‖Complex.log (Real.pi : ℂ)‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
    Real.pi + 4

theorem cofinalPNTZeroDepthTailConstant_nonneg :
    0 ≤ cofinalPNTZeroDepthTailConstant := by
  unfold cofinalPNTZeroDepthTailConstant
  have hseries :
      0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
    tsum_nonneg fun n => norm_nonneg _
  positivity

/-- Explicit two-scale majorant for the relative depth-zero contour
remainder. -/
noncomputable def cofinalPNTZeroDepthRelativeRemainderMajorant
    (C rate : ℝ) (m : ℕ) : ℝ :=
  26 * C * pntSqrtLog m ^ 4 *
      Real.exp (-rate * pntSqrtLog m) +
    2 * cofinalPNTZeroDepthTailConstant * pntSqrtLog m / (m : ℝ)

set_option maxHeartbeats 1200000 in
/-- Pointwise reduction of the exact cofinal remainder to its two asymptotic
scales. -/
theorem cofinalPNTFormulaRemainderBound_zero_relative_le_majorant
    {C rate T : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hrate : 0 < rate) (hrateOne : rate ≤ 1)
    (hm : 3 ≤ m)
    (hscale :
      max 1 (Real.log 6 / rate) ≤ pntSqrtLog m)
    (hT :
      T ∈ Set.Icc
        (pintzCarlsonGoodHeightBase rate (m : ℝ))
        (pintzCarlsonGoodHeightBase rate (m : ℝ) + 1)) :
    cofinalPNTFormulaRemainderBound C
        (pintzCarlsonGoodHeightBase rate (m : ℝ)) T m 0 /
        (m : ℝ) ≤
      cofinalPNTZeroDepthRelativeRemainderMajorant C rate m := by
  let x : ℝ := m
  let u : ℝ := pntSqrtLog m
  let H : ℝ := pintzCarlsonHeight rate x
  let K0 : ℝ :=
    ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
      ‖Complex.log (Real.pi : ℂ)‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) +
      Real.pi
  have hx3 : (3 : ℝ) ≤ x := by
    dsimp [x]
    exact_mod_cast hm
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hu0 : 0 ≤ u := by
    dsimp [u, pntSqrtLog]
    exact Real.sqrt_nonneg _
  have hu1 : 1 ≤ u := by
    exact (le_max_left 1 (Real.log 6 / rate)).trans hscale
  have hu_sq : u ^ 2 = Real.log x := by
    dsimp [u, pntSqrtLog, x]
    exact Real.sq_sqrt hlogx0
  have hlogSix_le : Real.log 6 ≤ rate * u := by
    have hdiv :
        Real.log 6 / rate ≤ u :=
      (le_max_right 1 (Real.log 6 / rate)).trans hscale
    simpa [mul_comm] using (div_le_iff₀ hrate).mp hdiv
  have hHdef : H = Real.exp (rate * u) := by
    rfl
  have hHsix : 6 ≤ H := by
    calc
      (6 : ℝ) = Real.exp (Real.log 6) := by
        rw [Real.exp_log (by norm_num)]
      _ ≤ Real.exp (rate * u) := Real.exp_le_exp.mpr hlogSix_le
      _ = H := hHdef.symm
  have hHpos : 0 < H := by
    dsimp [H]
    exact pintzCarlsonHeight_pos rate x
  have hrate_u_le_usq : rate * u ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrateOne) hu0,
      mul_nonneg (sub_nonneg.mpr hu1) hu0]
  have hH_le_x : H ≤ x := by
    calc
      H = Real.exp (rate * u) := hHdef
      _ ≤ Real.exp (u ^ 2) := Real.exp_le_exp.mpr hrate_u_le_usq
      _ = x := by rw [hu_sq, Real.exp_log hxpos]
  have hTlower : H - 1 ≤ T := by
    simpa only [pintzCarlsonGoodHeightBase] using hT.1
  have hTupper : T ≤ H := by
    simpa only [pintzCarlsonGoodHeightBase, sub_add_cancel] using hT.2
  have hTpos : 0 < T := by linarith
  have hHalfHpos : 0 < H / 2 := by positivity
  have hHalfH_le_T : H / 2 ≤ T := by linarith
  have hAplus :
      pintzCarlsonGoodHeightBase rate x + 6 ≤ 6 * H := by
    dsimp [pintzCarlsonGoodHeightBase]
    linarith
  have hlogAplus :
      Real.log (pintzCarlsonGoodHeightBase rate x + 6) ≤ 2 * u := by
    have hmono :
        Real.log (pintzCarlsonGoodHeightBase rate x + 6) ≤
          Real.log (6 * H) :=
      Real.log_le_log (by
        dsimp [pintzCarlsonGoodHeightBase]
        linarith) hAplus
    have hlogSixH :
        Real.log (6 * H) = Real.log 6 + rate * u := by
      rw [Real.log_mul (by norm_num) hHpos.ne', hHdef, Real.log_exp]
    rw [hlogSixH] at hmono
    nlinarith [mul_le_mul_of_nonneg_right hrateOne hu0]
  have hLm0 : 0 ≤ 1 + Real.log x := by
    have := Real.log_nonneg hxone
    linarith
  have hLA0 :
      0 ≤ 1 +
        Real.log (pintzCarlsonGoodHeightBase rate x + 6) := by
    have harg :
        1 ≤ pintzCarlsonGoodHeightBase rate x + 6 := by
      dsimp [pintzCarlsonGoodHeightBase]
      linarith
    have := Real.log_nonneg harg
    linarith
  have hLm : 1 + Real.log x ≤ 2 * u ^ 2 := by
    rw [← hu_sq]
    nlinarith [sq_nonneg (u - 1)]
  have hLA :
      1 + Real.log (pintzCarlsonGoodHeightBase rate x + 6) ≤
        3 * u := by
    linarith
  have hu2_le_u4 : u ^ 2 ≤ u ^ 4 := by
    nlinarith [sq_nonneg (u ^ 2 - 1)]
  have hlogSquares :
      (1 + Real.log x) ^ 2 +
          (1 + Real.log
            (pintzCarlsonGoodHeightBase rate x + 6)) ^ 2 ≤
        13 * u ^ 4 := by
    have hLmSq : (1 + Real.log x) ^ 2 ≤ 4 * u ^ 4 := by
      nlinarith
    have hLASq :
        (1 + Real.log
          (pintzCarlsonGoodHeightBase rate x + 6)) ^ 2 ≤
          9 * u ^ 2 := by
      nlinarith
    nlinarith
  have hmain :
      (C * x *
          ((1 + Real.log x) ^ 2 +
            (1 + Real.log
              (pintzCarlsonGoodHeightBase rate x + 6)) ^ 2) / T) / x ≤
        26 * C * u ^ 4 * Real.exp (-rate * u) := by
    calc
      (C * x *
          ((1 + Real.log x) ^ 2 +
            (1 + Real.log
              (pintzCarlsonGoodHeightBase rate x + 6)) ^ 2) / T) / x =
          C *
            ((1 + Real.log x) ^ 2 +
              (1 + Real.log
                (pintzCarlsonGoodHeightBase rate x + 6)) ^ 2) / T := by
            field_simp [hxpos.ne']
      _ ≤ C * (13 * u ^ 4) / T := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogSquares hC) hTpos.le
      _ ≤ C * (13 * u ^ 4) / (H / 2) := by
        exact div_le_div_of_nonneg_left (by positivity)
          hHalfHpos hHalfH_le_T
      _ = 26 * C * u ^ 4 * Real.exp (-rate * u) := by
        rw [hHdef]
        have hexp_ne : Real.exp (rate * u) ≠ 0 :=
          ne_of_gt (Real.exp_pos _)
        field_simp [hexp_ne]
        calc
          C * 13 * 2 = 26 * C := by ring
          _ = 26 * C *
              (Real.exp (u * rate) * Real.exp (-(u * rate))) := by
            rw [← Real.exp_add]
            simp
          _ = C * Real.exp (u * rate) * 26 *
              Real.exp (-(u * rate)) := by ring
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    have hseries :
        0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    positivity
  have hlogT :
      Real.log (T + 4) ≤ 2 * u := by
    have hT4 : T + 4 ≤ 6 * H := by
      linarith
    have hmono : Real.log (T + 4) ≤ Real.log (6 * H) :=
      Real.log_le_log (by linarith) hT4
    rw [show Real.log (6 * H) = Real.log 6 + rate * u by
      rw [Real.log_mul (by norm_num) hHpos.ne', hHdef, Real.log_exp]] at hmono
    nlinarith [mul_le_mul_of_nonneg_right hrateOne hu0]
  have hcoeff0 :
      0 ≤ K0 + 2 * Real.log (T + 4) := by
    have hlog0 : 0 ≤ Real.log (T + 4) :=
      Real.log_nonneg (by linarith)
    positivity
  have hcoeff :
      K0 + 2 * Real.log (T + 4) ≤
        cofinalPNTZeroDepthTailConstant * u := by
    have hK :
        cofinalPNTZeroDepthTailConstant = K0 + 4 := by
      rfl
    rw [hK]
    calc
      K0 + 2 * Real.log (T + 4) ≤ K0 + 4 * u := by
        linarith
      _ ≤ K0 * u + 4 * u := by
        gcongr
        exact le_mul_of_one_le_right hK0 hu1
      _ = (K0 + 4) * u := by ring
  have hinvT : x ^ (-1 : ℝ) * T ≤ 1 := by
    rw [Real.rpow_neg_one]
    exact (inv_mul_le_iff₀ hxpos).2 (by
      simpa [mul_comm] using hTupper.trans hH_le_x)
  have hpi : 1 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have htail :
      (((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
          (2 * T) / (2 * Real.pi)) / x ≤
        2 * cofinalPNTZeroDepthTailConstant * u / x := by
    have hnum0 :
        0 ≤ ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
          (2 * T) := by
      positivity
    have hdrop :
        ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
              (2 * T) / (2 * Real.pi) ≤
          ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
              (2 * T) :=
      div_le_self hnum0 hpi
    apply div_le_div_of_nonneg_right
        (hdrop.trans ?_) hxpos.le
    calc
      ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
          (2 * T) =
        2 * (K0 + 2 * Real.log (T + 4)) *
          (x ^ (-1 : ℝ) * T) := by ring
      _ ≤ 2 * (cofinalPNTZeroDepthTailConstant * u) *
          (x ^ (-1 : ℝ) * T) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hcoeff (by norm_num)
        · exact mul_nonneg (Real.rpow_nonneg hxpos.le _)
            hTpos.le
      _ ≤ 2 * (cofinalPNTZeroDepthTailConstant * u) * 1 := by
        apply mul_le_mul_of_nonneg_left hinvT
        exact mul_nonneg (by norm_num)
          (mul_nonneg cofinalPNTZeroDepthTailConstant_nonneg hu0)
      _ = 2 * cofinalPNTZeroDepthTailConstant * u := by ring
  have hremainder :
      cofinalPNTFormulaRemainderBound C
          (pintzCarlsonGoodHeightBase rate (m : ℝ)) T m 0 =
        C * x *
            ((1 + Real.log x) ^ 2 +
              (1 + Real.log
                (pintzCarlsonGoodHeightBase rate x + 6)) ^ 2) / T +
          ((K0 + 2 * Real.log (T + 4)) * x ^ (-1 : ℝ)) *
            (2 * T) / (2 * Real.pi) := by
    simp [cofinalPNTFormulaRemainderBound, x, K0]
    ring
    all_goals simp
  rw [hremainder, add_div]
  simpa [cofinalPNTZeroDepthRelativeRemainderMajorant, x, u] using
    add_le_add hmain htail

/-- The two-scale relative remainder majorant tends to zero. -/
theorem cofinalPNTZeroDepthRelativeRemainderMajorant_tendsto
    {C rate : ℝ} (hrate : 0 < rate) :
    Tendsto
      (cofinalPNTZeroDepthRelativeRemainderMajorant C rate)
      atTop (nhds 0) := by
  have hmain :=
    (tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      rate hrate 4).const_mul (26 * C)
  have hlogdiv :
      Tendsto
        (fun m : ℕ => Real.log (m : ℝ) / (m : ℝ))
        atTop (nhds 0) := by
    simpa [Function.comp_def, id_eq, neg_mul] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
  have hsqrtdiv :
      Tendsto (fun m : ℕ => pntSqrtLog m / (m : ℝ))
        atTop (nhds 0) := by
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
      have hsqrt :
          pntSqrtLog m ≤ Real.log (m : ℝ) := by
        have hsquare :=
          Real.sq_sqrt (le_trans zero_le_one hlog')
        have hsqrt0 : 0 ≤ pntSqrtLog m := by
          exact Real.sqrt_nonneg _
        dsimp [pntSqrtLog] at hsquare ⊢
        nlinarith
      gcongr
  have htail :=
    hsqrtdiv.const_mul
      (2 * cofinalPNTZeroDepthTailConstant)
  convert hmain.add htail using 1
  · funext m
    unfold cofinalPNTZeroDepthRelativeRemainderMajorant
    ring
  · simp

/-- Every good-height selector in the unit interval below the fixed-rate
Pintz--Carlson height has vanishing relative depth-zero contour remainder. -/
theorem cofinalPNTFormulaRemainderBound_zero_relative_tendsto
    {C rate : ℝ} (hC : 0 ≤ C) (hrate : 0 < rate)
    (hrateOne : rate ≤ 1)
    (height : ℕ → ℝ)
    (hheight :
      ∀ᶠ (m : ℕ) in atTop,
        height m ∈ Set.Icc
          (pintzCarlsonGoodHeightBase rate (m : ℝ))
          (pintzCarlsonGoodHeightBase rate (m : ℝ) + 1)) :
    Tendsto
      (fun m : ℕ =>
        cofinalPNTFormulaRemainderBound C
          (pintzCarlsonGoodHeightBase rate (m : ℝ))
          (height m) m 0 / (m : ℝ))
      atTop (nhds 0) := by
  refine squeeze_zero'
    (g := cofinalPNTZeroDepthRelativeRemainderMajorant C rate) ?_ ?_
    (cofinalPNTZeroDepthRelativeRemainderMajorant_tendsto
      (C := C) hrate)
  · filter_upwards
      [hheight, eventually_ge_atTop (3 : ℕ),
        tendsto_pntSqrtLog_atTop.eventually
          (eventually_ge_atTop (max 1 (Real.log 6 / rate)))]
      with m hmT hm hscale
    have hlogSix_le :
        Real.log 6 ≤ rate * pntSqrtLog m := by
      have hdiv :
          Real.log 6 / rate ≤ pntSqrtLog m :=
        (le_max_right 1 (Real.log 6 / rate)).trans hscale
      simpa [mul_comm] using (div_le_iff₀ hrate).mp hdiv
    have hHsix :
        6 ≤ pintzCarlsonHeight rate (m : ℝ) := by
      calc
        (6 : ℝ) = Real.exp (Real.log 6) := by
          rw [Real.exp_log (by norm_num)]
        _ ≤ Real.exp (rate * pntSqrtLog m) :=
          Real.exp_le_exp.mpr hlogSix_le
        _ = pintzCarlsonHeight rate (m : ℝ) := rfl
    unfold cofinalPNTFormulaRemainderBound
    have hTpos : 0 < height m := by
      have hbasepos :
          0 < pintzCarlsonGoodHeightBase rate (m : ℝ) := by
        dsimp [pintzCarlsonGoodHeightBase]
        linarith
      exact hbasepos.trans_le hmT.1
    have hlog0 : 0 ≤ Real.log (height m + 4) :=
      Real.log_nonneg (by linarith)
    have hseries :
        0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) hm)
    have hrpow :
        0 ≤ (m : ℝ) ^ (-(2 * (((0 : ℕ) : ℝ)) + 1)) :=
      Real.rpow_nonneg hmpos.le _
    have hcoeff0 :
        0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
            ‖Complex.log (Real.pi : ℂ)‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (((0 : ℕ) : ℝ)) + height m + 4)) +
          Real.pi := by
      have hlog0' :
          0 ≤ Real.log
            (2 * (((0 : ℕ) : ℝ)) + height m + 4) := by
        simpa using hlog0
      have hinner :
          0 ≤ ‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (2 * (((0 : ℕ) : ℝ)) + height m + 4) :=
        add_nonneg
          (add_nonneg (norm_nonneg _) (by norm_num))
          hlog0'
      exact add_nonneg
        (add_nonneg
          (add_nonneg hseries (norm_nonneg _))
          (mul_nonneg (by norm_num) hinner))
        Real.pi_pos.le
    have hmain0 :
        0 ≤ C * (m : ℝ) *
          ((1 + Real.log (m : ℝ)) ^ 2 +
            (1 + Real.log
              (pintzCarlsonGoodHeightBase rate (m : ℝ) + 6)) ^ 2) /
          height m := by
      apply div_nonneg
      · exact mul_nonneg
          (mul_nonneg hC (Nat.cast_nonneg _))
          (add_nonneg (sq_nonneg _) (sq_nonneg _))
      · exact hTpos.le
    have htail0 :
        0 ≤
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
                ‖Complex.log (Real.pi : ℂ)‖ +
              2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
                Real.log (2 * (((0 : ℕ) : ℝ)) + height m + 4)) +
              Real.pi) *
            (m : ℝ) ^ (-(2 * (((0 : ℕ) : ℝ)) + 1)) *
            (2 * height m) / (2 * Real.pi) := by
      apply div_nonneg
      · exact mul_nonneg
          (mul_nonneg hcoeff0 hrpow)
          (mul_nonneg (by norm_num) hTpos.le)
      · exact mul_nonneg (by norm_num) Real.pi_pos.le
    exact div_nonneg (add_nonneg hmain0 htail0) hmpos.le
  · filter_upwards
      [hheight, eventually_ge_atTop (3 : ℕ),
        tendsto_pntSqrtLog_atTop.eventually
          (eventually_ge_atTop (max 1 (Real.log 6 / rate)))]
      with m hmT hm hscale
    exact cofinalPNTFormulaRemainderBound_zero_relative_le_majorant
      hC hrate hrateOne hm hscale hmT

end PrimeNumberTheorem
