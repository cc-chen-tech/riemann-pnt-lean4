import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicNegativeVerticalTailIntegral

namespace PrimeNumberTheorem

open Complex Set MeasureTheory
open scoped Interval
open ExplicitFormulaResidues

/-- A pathwise comparison theorem for the actual third-order zeta integrand.
It isolates exactly the data needed to turn a pointwise logarithmic-derivative
budget into a height-independent cubic tail integral. -/
theorem norm_integral_actualCubicVerticalTail_le_of_pointwise
    {x a B T H : ℝ} {s : ℝ → ℂ}
    (hx : 0 < x) (hB : 0 ≤ B) (hT : 0 < T) (hTH : T ≤ H)
    (hscont : Continuous s)
    (hs0 : ∀ u ∈ Set.Icc T H, s u ≠ 0)
    (hs1 : ∀ u ∈ Set.Icc T H, s u ≠ 1)
    (hzeta : ∀ u ∈ Set.Icc T H, riemannZeta (s u) ≠ 0)
    (hlog : ∀ u ∈ Set.Icc T H,
      ‖logDeriv riemannZeta (s u)‖ ≤ B)
    (hre : ∀ u ∈ Set.Icc T H, (s u).re = a)
    (hnorm : ∀ u ∈ Set.Icc T H, u ≤ ‖s u‖) :
    ‖∫ u : ℝ in T..H, thirdOrderExplicitFormulaIntegrand x (s u)‖ ≤
      x ^ a * B / (2 * T ^ 2) := by
  let K : ℝ := x ^ a * B
  let f : ℝ → ℂ := fun u => thirdOrderExplicitFormulaIntegrand x (s u)
  let g : ℝ → ℝ := fun u => K * u ^ (-3 : ℝ)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfInt : IntervalIntegrable f volume T H := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [uIcc_of_le hTH] at hu
    have han := analyticAt_thirdOrderExplicitFormulaIntegrand_of_ne
      hx (hs0 u hu) (hs1 u hu) (hzeta u hu)
    have hcomp : ContinuousAt
        (thirdOrderExplicitFormulaIntegrand x ∘ s) u :=
      han.continuousAt.comp_of_eq hscont.continuousAt rfl
    simpa [f, Function.comp_def] using hcomp.continuousWithinAt
  have hzero : (0 : ℝ) ∉ [[T, H]] := by
    rw [uIcc_of_le hTH]
    simp only [mem_Icc, not_and_or]
    left
    linarith
  have hgInt : IntervalIntegrable g volume T H := by
    dsimp [g]
    exact (intervalIntegral.intervalIntegrable_rpow (μ := volume)
      (r := (-3 : ℝ)) (Or.inr hzero)).const_mul K
  have hmajor : ∀ᵐ u : ℝ, u ∈ Set.Ioc T H → ‖f u‖ ≤ g u := by
    filter_upwards [] with u hu
    have huIcc : u ∈ Set.Icc T H := ⟨hu.1.le, hu.2⟩
    have huPos : 0 < u := hT.trans_le hu.1.le
    have hupow : u ^ 3 ≤ ‖s u‖ ^ 3 :=
      pow_le_pow_left₀ huPos.le (hnorm u huIcc) 3
    have hnum : ‖logDeriv riemannZeta (s u)‖ * x ^ a ≤ K := by
      dsimp [K]
      have hxpow : 0 ≤ x ^ a := Real.rpow_nonneg hx.le _
      nlinarith [hlog u huIcc]
    have hrpow : u ^ (-3 : ℝ) = 1 / u ^ 3 := by
      rw [Real.rpow_neg huPos.le]
      norm_num [Real.rpow_natCast]
    dsimp [f]
    rw [norm_thirdOrderExplicitFormulaIntegrand_eq hx, hre u huIcc]
    calc
      ‖logDeriv riemannZeta (s u)‖ * x ^ a / ‖s u‖ ^ 3 ≤
          K / ‖s u‖ ^ 3 :=
        div_le_div_of_nonneg_right hnum (pow_nonneg (norm_nonneg _) _)
      _ ≤ K / u ^ 3 :=
        div_le_div_of_nonneg_left hK (pow_pos huPos 3) hupow
      _ = g u := by
        dsimp [g]
        rw [hrpow, div_eq_mul_inv, one_div]
  have hnormInt := intervalIntegral.norm_integral_le_of_norm_le hTH hmajor hgInt
  have hscalar := (integral_rpow_neg_three_le_half_inv_sq hT hTH).2
  calc
    ‖∫ u : ℝ in T..H, f u‖ ≤ ∫ u : ℝ in T..H, g u := hnormInt
    _ = K * (∫ u : ℝ in T..H, u ^ (-3 : ℝ)) := by
      simp [g, intervalIntegral.integral_const_mul]
    _ ≤ K * (1 / (2 * T ^ 2)) := mul_le_mul_of_nonneg_left hscalar hK
    _ = x ^ a * B / (2 * T ^ 2) := by simp [K, div_eq_mul_inv]

/-- One invocation of the actual high-height theorem supplies a single shared
`b, C, T0` controlling both positive and negative cubic vertical tails. -/
theorem exists_norm_integral_actualCubicTwoSidedVerticalTails_le :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 4 ≤ T0 ∧
      ∀ x H : ℝ, 0 < x → T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        let M := x ^ a * C * (1 + Real.log (H + 6)) ^ 2 /
          (2 * T0 ^ 2)
        ‖∫ t : ℝ in T0..H,
            thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ M ∧
        ‖∫ t : ℝ in (-H)..(-T0),
            thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤ M := by
  rcases exists_dynamicCubicLeftBoundary_high_logDeriv_le_log_sq with
    ⟨b, C, T0, hb, hC, hT0, hbase⟩
  refine ⟨b, C, T0, hb, hC, hT0, ?_⟩
  intro x H hx hH
  rcases hbase H hH with ⟨ha, _haHalf, hpoint⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  let L : ℝ := 1 + Real.log (H + 6)
  let B : ℝ := C * L ^ 2
  let sp : ℝ → ℂ := fun u => (a : ℂ) + u * I
  let sn : ℝ → ℂ := fun u => (a : ℂ) + (-u) * I
  have hTpos : 0 < T0 := (by norm_num : (0 : ℝ) < 4).trans_le hT0
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpathData (ε : ℝ) (hε : |ε| = 1) :
      let path : ℝ → ℂ := fun u => (a : ℂ) + (ε * u) * I
      Continuous path ∧
      (∀ u ∈ Set.Icc T0 H, path u ≠ 0) ∧
      (∀ u ∈ Set.Icc T0 H, path u ≠ 1) ∧
      (∀ u ∈ Set.Icc T0 H, riemannZeta (path u) ≠ 0) ∧
      (∀ u ∈ Set.Icc T0 H, ‖logDeriv riemannZeta (path u)‖ ≤ B) ∧
      (∀ u ∈ Set.Icc T0 H, (path u).re = a) ∧
      (∀ u ∈ Set.Icc T0 H, u ≤ ‖path u‖) := by
    dsimp only
    have hcont : Continuous (fun u : ℝ => (a : ℂ) + (ε * u) * I) := by fun_prop
    refine ⟨hcont, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu hs
      have him := congrArg Complex.im hs
      simp at him
      have huPos : 0 < u := hTpos.trans_le hu.1
      rcases him with hε0 | hu0
      · rw [hε0, abs_zero] at hε
        norm_num at hε
      · linarith
    · intro u hu hs
      have him := congrArg Complex.im hs
      simp at him
      have huPos : 0 < u := hTpos.trans_le hu.1
      rcases him with hε0 | hu0
      · rw [hε0, abs_zero] at hε
        norm_num at hε
      · linarith
    · intro u hu
      have huPos : 0 < u := hTpos.trans_le hu.1
      have habs : |ε * u| = u := by rw [abs_mul, hε, one_mul, abs_of_pos huPos]
      rcases hpoint (ε * u) (by simpa [habs] using hu.1)
          (by simpa [habs] using hu.2) with ⟨hz, _hz1, _hlog⟩
      have heq : ((a : ℂ) + (ε * u) * I) = (a : ℂ) + I * (ε * u) := by ring
      rw [heq]
      simpa [a] using hz
    · intro u hu
      have huPos : 0 < u := hTpos.trans_le hu.1
      have habs : |ε * u| = u := by rw [abs_mul, hε, one_mul, abs_of_pos huPos]
      rcases hpoint (ε * u) (by simpa [habs] using hu.1)
          (by simpa [habs] using hu.2) with ⟨_hz, _hz1, hld⟩
      have heq : ((a : ℂ) + (ε * u) * I) = (a : ℂ) + I * (ε * u) := by ring
      rw [heq]
      simpa [B, L] using hld
    · intro u hu
      simp
    · intro u hu
      have huPos : 0 < u := hTpos.trans_le hu.1
      have himAbs : |((a : ℂ) + (ε * u) * I).im| = u := by
        simp
        rw [hε, one_mul, abs_of_pos huPos]
      calc
        u = |((a : ℂ) + (ε * u) * I).im| := himAbs.symm
        _ ≤ ‖(a : ℂ) + (ε * u) * I‖ := Complex.abs_im_le_norm _
  rcases hpathData 1 (by norm_num) with
    ⟨hspCont, hsp0, hsp1, hspZeta, hspLog, hspRe, hspNorm⟩
  rcases hpathData (-1) (by norm_num) with
    ⟨hsnCont, hsn0, hsn1, hsnZeta, hsnLog, hsnRe, hsnNorm⟩
  have hpos := norm_integral_actualCubicVerticalTail_le_of_pointwise
    hx hB hTpos hH hspCont hsp0 hsp1 hspZeta hspLog hspRe hspNorm
  have hnegParam := norm_integral_actualCubicVerticalTail_le_of_pointwise
    hx hB hTpos hH hsnCont hsn0 hsn1 hsnZeta hsnLog hsnRe hsnNorm
  let f : ℝ → ℂ := fun t =>
    thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)
  have hchange := intervalIntegral.integral_comp_neg
    (f := f) (a := T0) (b := H)
  have hneg : ‖∫ t : ℝ in (-H)..(-T0), f t‖ ≤
      x ^ a * B / (2 * T0 ^ 2) := by
    rw [← hchange]
    simpa [sn, f] using hnegParam
  refine ⟨?_, ?_⟩
  · simpa [sp, B, L, a, mul_assoc] using hpos
  · simpa [f, B, L, a, mul_assoc] using hneg

end PrimeNumberTheorem
