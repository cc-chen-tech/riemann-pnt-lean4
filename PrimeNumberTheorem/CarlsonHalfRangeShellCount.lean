import PrimeNumberTheorem.CarlsonHalfRangeHorizontalEdges
import PrimeNumberTheorem.CarlsonHalfRangeVerticalBudget
import PrimeNumberTheorem.CarlsonTwoScaleLittlewood

/-! Unconditional multiplicity count on a closed height shell, with the
closed real threshold `2/3`.  All four contour edges are supplied by the
proved two-scale Carlson estimates. -/

open Complex Filter MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem.CarlsonZeroDensity

/-- Any finite family of actual zeta zeros in the closed shell satisfies
the power saving.  No moment, boundary, or zero-detector premise remains. -/
theorem exists_eventually_halfRange_shellFamilyCount_le :
    ∃ K > (0 : ℝ), ∀ᶠ U : ℝ in atTop,
      ∀ S : Finset ℂ,
        (∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho ∧
          (2 / 3 : ℝ) ≤ rho.re ∧ U ≤ rho.im ∧ rho.im ≤ 9 * U / 8) →
        (∑ rho ∈ S, (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
          K * U ^ (8 / 9 - 1 / 400 : ℝ) * (1 + Real.log U) ^ 6 := by
  obtain ⟨Kv, hKv, hvertical⟩ := exists_eventually_halfRange_selectedVerticalBudget
  obtain ⟨Kh, hKh, hhorizontal⟩ := exists_eventually_halfRange_horizontalEdges
  have hscale : Tendsto (fun U : ℝ => 10 * U / 21) atTop atTop := by
    have heq : (fun U : ℝ => 10 * U / 21) = (fun U : ℝ => (10 / 21 : ℝ) * U) := by
      funext U
      ring
    rw [heq]
    exact tendsto_id.const_mul_atTop (by norm_num)
  refine ⟨(Kv + Kh) / (2 * Real.pi * (1 / 20000)), by positivity, ?_⟩
  filter_upwards [hscale.eventually hvertical, hhorizontal,
    hscale.eventually eventually_halfRangeCutoff_conditions, eventually_ge_atTop (21 : ℝ)]
    with U hvertical hhorizontal hparams hU
  intro S hS
  let V := 10 * U / 21
  let H := regularizedTwoScaleCarlsonZeroDetector (halfRangeCoreCutoff V) (halfRangeOuterCutoff V)
  obtain ⟨hV, hY0, hY01, _⟩ := hparams
  change 1 < V at hV
  have hVpos : 0 < V := zero_lt_one.trans hV
  obtain ⟨x, hx, hgap, hleft, hright, hvert⟩ := hvertical
  obtain ⟨u, hu, v, hv, huV, hvV, huv, hbottom, htop, hhoriz⟩ := hhorizontal
  have hxClosed : x ∈ Icc halfRangeAuxiliaryLeft halfRangeAuxiliaryRight := ⟨hx.1.le, hx.2.le⟩
  obtain ⟨hxStrip, _, _⟩ := halfRangeAuxiliary_bounds hxClosed
  have hx0 : 0 < x := by linarith only [hxStrip.1]
  have hx4 : x ≤ 4 := by linarith only [hxStrip.2]
  have hSrect : ∀ rho ∈ S, RiemannHypothesis.IsNontrivialZero rho ∧
      (2 / 3 : ℝ) ≤ rho.re ∧ u ≤ rho.im ∧ rho.im ≤ v := by
    intro rho hrho
    obtain ⟨hz, hre, him0, him1⟩ := hS rho hrho
    exact ⟨hz, hre, hu.2.trans him0, him1.trans hv.1⟩
  have hleftRect : ∀ t ∈ Icc u v, H ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t ht
    simpa only [mul_comm I] using hleft t ⟨huV.trans ht.1, ht.2.trans hvV⟩
  have hrightRect : ∀ t ∈ Icc u v, H ((4 : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro t _
    simpa only [mul_comm I] using hright t
  have hsub : Icc x 4 ⊆ Icc halfRangeAuxiliaryLeft 4 :=
    fun _ hw => ⟨hx.1.le.trans hw.1, hw.2⟩
  have hcount := two_pi_mul_twoScaleZetaFamilyCount_le_logNormForm
    hY0 hY01 hx0 hx4 hxStrip.2 (by norm_num : (1 : ℝ) ≤ 4) huv S hSrect
    hleftRect hrightRect (fun w hw => hbottom w (hsub hw)) (fun w hw => htop w (hsub hw))
  have hverticalBound := hvert u v huV hvV huv
  simp only [mul_comm I] at hverticalBound
  have hhorizontalBound := (hhoriz x hxClosed).2.2
  let B0 := ∫ w in x..4, (w - x) * (logDeriv H ((w : ℂ) + (u : ℂ) * I)).im
  let B1 := ∫ w in x..4, (w - x) * (logDeriv H ((w : ℂ) + (v : ℂ) * I)).im
  have hB : B0 - B1 ≤ |B0| + |B1| := (le_abs_self _).trans (abs_sub _ _)
  have hrectangle : rectangleLittlewoodLogNormForm H x 4 u v ≤
      Kv * V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 + Kh * (1 + Real.log U) ^ 2 := by
    dsimp [rectangleLittlewoodLogNormForm]
    dsimp [B0, B1] at hB
    linarith only [hB, hverticalBound, hhorizontalBound]
  let W := U ^ halfRangeTargetExponent * (1 + Real.log U) ^ 6
  have hVU : V ≤ U := by dsimp [V]; linarith only [hU]
  have hU1 : 1 ≤ U := by linarith only [hU]
  have hq : 0 ≤ halfRangeTargetExponent := by norm_num [halfRangeTargetExponent]
  have htransfer : V ^ halfRangeTargetExponent * (1 + Real.log V) ^ 6 ≤ W := by
    have hp := Real.rpow_le_rpow hVpos.le hVU hq
    have hl := Real.log_le_log hVpos hVU
    have hl0 : 0 ≤ 1 + Real.log V := by linarith only [Real.log_nonneg hV.le]
    exact mul_le_mul hp (pow_le_pow_left₀ hl0 (by linarith only [hl]) 6) (by positivity) (by positivity)
  have hsquare : (1 + Real.log U) ^ 2 ≤ W := by
    have hlog1 : 1 ≤ 1 + Real.log U := by linarith only [Real.log_nonneg hU1]
    have hpow1 : 1 ≤ U ^ halfRangeTargetExponent := Real.one_le_rpow hU1 hq
    calc
      _ ≤ (1 + Real.log U) ^ 6 := pow_le_pow_right₀ hlog1 (by norm_num)
      _ ≤ W := le_mul_of_one_le_left (by positivity) hpow1
  have hrectangleW : rectangleLittlewoodLogNormForm H x 4 u v ≤ (Kv + Kh) * W := by
    have hvTransfer := mul_le_mul_of_nonneg_left htransfer hKv.le
    have hhTransfer := mul_le_mul_of_nonneg_left hsquare hKh.le
    nlinarith only [hrectangle, hvTransfer, hhTransfer]
  have hsum0 : 0 ≤ ∑ rho ∈ S, (analyticOrderNatAt riemannZeta rho : ℝ) :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hweight := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgap hsum0)
    (by positivity : 0 ≤ 2 * Real.pi)
  have htotal : (2 * Real.pi) * ((1 / 20000 : ℝ) *
      ∑ rho ∈ S, (analyticOrderNatAt riemannZeta rho : ℝ)) ≤ (Kv + Kh) * W :=
    hweight.trans (hcount.trans hrectangleW)
  have hden : 0 < 2 * Real.pi * (1 / 20000 : ℝ) := by positivity
  calc
    _ ≤ ((Kv + Kh) * W) / (2 * Real.pi * (1 / 20000)) :=
      (le_div_iff₀ hden).mpr (by nlinarith only [htotal])
    _ = _ := by dsimp [W, halfRangeTargetExponent]; ring

end PrimeNumberTheorem.CarlsonZeroDensity
