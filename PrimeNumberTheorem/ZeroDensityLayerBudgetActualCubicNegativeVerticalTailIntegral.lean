import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicPositiveVerticalTailIntegral

namespace PrimeNumberTheorem

open Complex Set MeasureTheory
open scoped Interval
open ExplicitFormulaResidues

/-- The actual negative-height dynamic cubic left tail has the same
height-independent bound as the positive tail.  The proof changes variables
`t = -u` and estimates the actual points `a(H) - iu`. -/
theorem exists_norm_integral_actualCubicNegativeVerticalTail_le :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 4 ≤ T0 ∧
      ∀ x H : ℝ, 0 < x → T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        ‖∫ t : ℝ in (-H)..(-T0),
            thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤
          x ^ a * C * (1 + Real.log (H + 6)) ^ 2 /
            (2 * T0 ^ 2) := by
  rcases exists_dynamicCubicLeftBoundary_high_logDeriv_le_log_sq with
    ⟨b, C, T0, hb, hC, hT0, hpointBase⟩
  refine ⟨b, C, T0, hb, hC, hT0, ?_⟩
  intro x H hx hH
  rcases hpointBase H hH with ⟨ha, _haHalf, hpoint⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  let L : ℝ := 1 + Real.log (H + 6)
  let K : ℝ := x ^ a * C * L ^ 2
  let f : ℝ → ℂ := fun t =>
    thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)
  let q : ℝ → ℂ := fun u => f (-u)
  let g : ℝ → ℝ := fun u => K * u ^ (-3 : ℝ)
  have hTpos : 0 < T0 := (by norm_num : (0 : ℝ) < 4).trans_le hT0
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hqInt : IntervalIntegrable q volume T0 H := by
    apply ContinuousOn.intervalIntegrable
    intro u huI
    rw [uIcc_of_le hH] at huI
    have huPos : 0 < u := hTpos.trans_le huI.1
    rcases hpoint (-u) (by simpa [abs_neg, abs_of_pos huPos] using huI.1)
        (by simpa [abs_neg, abs_of_pos huPos] using huI.2) with
      ⟨hzeta, _hz1, _hlog⟩
    have hsEq : ((a : ℂ) + (-u) * I) = (a : ℂ) + I * (-u) := by ring
    have hzetaS : riemannZeta ((a : ℂ) + (-u) * I) ≠ 0 := by
      rw [hsEq]
      simpa [a] using hzeta
    have hs0 : ((a : ℂ) + (-u) * I) ≠ 0 := by
      intro hs
      have him := congrArg Complex.im hs
      simp at him
      linarith
    have hs1 : ((a : ℂ) + (-u) * I) ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      simp at him
      linarith
    have han := analyticAt_thirdOrderExplicitFormulaIntegrand_of_ne
      hx hs0 hs1 hzetaS
    have hpath : Continuous (fun v : ℝ => (a : ℂ) + (-v) * I) := by fun_prop
    have hcomp : ContinuousAt
        (thirdOrderExplicitFormulaIntegrand x ∘
          fun v : ℝ => (a : ℂ) + (-v) * I) u :=
      han.continuousAt.comp_of_eq hpath.continuousAt rfl
    simpa [q, f, Function.comp_def] using hcomp.continuousWithinAt
  have hzero : (0 : ℝ) ∉ [[T0, H]] := by
    rw [uIcc_of_le hH]
    simp only [mem_Icc, not_and_or]
    left
    linarith
  have hgInt : IntervalIntegrable g volume T0 H := by
    dsimp [g]
    exact (intervalIntegral.intervalIntegrable_rpow (μ := volume)
      (r := (-3 : ℝ)) (Or.inr hzero)).const_mul K
  have hmajor : ∀ᵐ u : ℝ, u ∈ Set.Ioc T0 H → ‖q u‖ ≤ g u := by
    filter_upwards [] with u huI
    have huPos : 0 < u := hTpos.trans_le huI.1.le
    rcases hpoint (-u) (by simpa [abs_neg, abs_of_pos huPos] using huI.1.le)
        (by simpa [abs_neg, abs_of_pos huPos] using huI.2) with
      ⟨_hzeta, _hz1, hlog⟩
    let s : ℂ := (a : ℂ) + (-u) * I
    have hsEq : s = (a : ℂ) + I * (-u) := by dsimp [s]; ring
    have hlogS : ‖logDeriv riemannZeta s‖ ≤ C * L ^ 2 := by
      rw [hsEq]
      simpa [L] using hlog
    have hsNorm : u ≤ ‖s‖ := by
      calc
        u = |s.im| := by simp [s, abs_of_pos huPos]
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hpow : u ^ 3 ≤ ‖s‖ ^ 3 :=
      pow_le_pow_left₀ huPos.le hsNorm 3
    have hnum : ‖logDeriv riemannZeta s‖ * x ^ a ≤ K := by
      dsimp [K, L]
      have hxpow : 0 ≤ x ^ a := Real.rpow_nonneg hx.le _
      nlinarith [hlogS]
    have hrpow : u ^ (-3 : ℝ) = 1 / u ^ 3 := by
      rw [Real.rpow_neg huPos.le]
      norm_num [Real.rpow_natCast]
    dsimp [q, f]
    have htarget : ((a : ℂ) + ((-u : ℝ) : ℂ) * I) = s := by simp [s]
    rw [htarget]
    rw [norm_thirdOrderExplicitFormulaIntegrand_eq hx]
    have hsre : s.re = a := by simp [s]
    rw [hsre]
    calc
      ‖logDeriv riemannZeta s‖ * x ^ a / ‖s‖ ^ 3 ≤ K / ‖s‖ ^ 3 :=
        div_le_div_of_nonneg_right hnum (pow_nonneg (norm_nonneg _) _)
      _ ≤ K / u ^ 3 :=
        div_le_div_of_nonneg_left hK (pow_pos huPos 3) hpow
      _ = g u := by
        dsimp [g]
        rw [hrpow, div_eq_mul_inv, one_div]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hH hmajor hgInt
  have hscalar := (integral_rpow_neg_three_le_half_inv_sq hTpos hH).2
  have hchange := intervalIntegral.integral_comp_neg
    (f := f) (a := T0) (b := H)
  calc
    ‖∫ t : ℝ in (-H)..(-T0), f t‖ = ‖∫ u : ℝ in T0..H, q u‖ := by
      rw [hchange]
    _ ≤ ∫ u : ℝ in T0..H, g u := hnorm
    _ = K * (∫ u : ℝ in T0..H, u ^ (-3 : ℝ)) := by
      simp [g, intervalIntegral.integral_const_mul]
    _ ≤ K * (1 / (2 * T0 ^ 2)) :=
      mul_le_mul_of_nonneg_left hscalar hK
    _ = x ^ a * C * (1 + Real.log (H + 6)) ^ 2 / (2 * T0 ^ 2) := by
      simp [K, L, div_eq_mul_inv]

end PrimeNumberTheorem
