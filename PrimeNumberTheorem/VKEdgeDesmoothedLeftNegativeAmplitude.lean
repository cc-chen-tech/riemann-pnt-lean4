import PrimeNumberTheorem.VKEdgeDesmoothedLeftAmplitude
import Mathlib.Analysis.Calculus.Deriv.Shift

open Complex Metric

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The actual desmoothed zeta integral on the negative high-height part of
the dynamic left edge has the same oscillatory bound as the positive part.
The proof changes variables by `t ↦ -t`; it does not invoke zeta conjugation. -/
theorem norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_neg_le
    {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzeta : ∀ t ∈ Set.Icc (-v) (-u),
      riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ∀ t ∈ Set.Icc (-v) (-u),
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ∀ t ∈ Set.Icc (-v) (-u),
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : ∀ t ∈ Set.Icc (-v) (-u),
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖∫ t in (-v)..(-u),
        desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
      x ^ a *
        ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
          Real.log x) := by
  let A : ℝ → ℂ := desmoothedLeftOscillatoryAmplitude h a
  let B : ℝ → ℂ := fun t => A (-t)
  let V : ℝ := 3 * D + 11 * L
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hnegMem : ∀ t ∈ Set.Icc u v, -t ∈ Set.Icc (-v) (-u) := by
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hBderivBound : ∀ t ∈ Set.Icc u v, ‖deriv B t‖ ≤ V / t := by
    intro t ht
    have htTwo : 2 ≤ t := hu.trans ht.1
    have htPos : 0 < t := lt_of_lt_of_le (by norm_num) htTwo
    have htOne : 1 ≤ t := by linarith
    have htAbsNeg : |-t| = t := by rw [abs_neg, abs_of_pos htPos]
    have htNegMem := hnegMem t ht
    have hraw := norm_deriv_desmoothedLeftOscillatoryAmplitude_le
      hh (by simpa [htAbsNeg] using htTwo) (hzeta (-t) htNegMem)
        (hlog (-t) htNegMem) (hlog' (-t) htNegMem) (hsmall (-t) htNegMem)
    have hq : 11 * L / t ^ 2 ≤ 11 * L / t := by
      have hcoeff : 0 ≤ 11 * L := by positivity
      have htSq : t ≤ t ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left hcoeff htPos htSq
    have hderivEq : deriv B t = -deriv A (-t) := by
      simpa [B] using (deriv_comp_neg (f := A) (x := t))
    rw [hderivEq, norm_neg]
    rw [htAbsNeg] at hraw
    change ‖deriv A (-t)‖ ≤ _ at hraw ⊢
    calc
      ‖deriv A (-t)‖ ≤ 3 * D / t + 11 * L / t ^ 2 := hraw
      _ ≤ 3 * D / t + 11 * L / t := add_le_add (le_refl _) hq
      _ = V / t := by dsimp [V]; ring
  have hB'int : IntervalIntegrable (deriv B) MeasureTheory.volume u v :=
    MathlibAux.intervalIntegrable_deriv_of_norm_le_div huPos huv hBderivBound
  have hvariation : (∫ t in u..v, ‖deriv B t‖) ≤
      V * Real.log (v / u) :=
    MathlibAux.intervalIntegral_norm_le_mul_log_div_of_norm_le_div
      huPos huv hB'int hBderivBound
  have hBderiv : ∀ t ∈ Set.uIcc u v, HasDerivAt B (deriv B t) t := by
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    have htTwo : 2 ≤ t := hu.trans ht.1
    have htPos : 0 < t := lt_of_lt_of_le (by norm_num) htTwo
    have htNegMem := hnegMem t ht
    have hAneg := differentiableAt_desmoothedLeftOscillatoryAmplitude
      hh (by simpa [abs_neg, abs_of_pos htPos] using htTwo) (hzeta (-t) htNegMem)
    have hneg : DifferentiableAt ℝ (fun s : ℝ => -s) t := differentiableAt_id.neg
    have hcomp : DifferentiableAt ℝ (fun s : ℝ => A (-s)) t := by
      simpa [A, Function.comp_def] using hAneg.comp t hneg
    exact (by simpa [B] using hcomp.hasDerivAt)
  have hB0 : ∀ t ∈ Set.uIcc u v, ‖B t‖ ≤ 3 * L / u := by
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    have htTwo : 2 ≤ t := hu.trans ht.1
    have htPos : 0 < t := lt_of_lt_of_le (by norm_num) htTwo
    have htNegMem := hnegMem t ht
    have hraw := norm_desmoothedLeftOscillatoryAmplitude_le
      hh (by simpa [abs_neg, abs_of_pos htPos] using htTwo)
        (hlog (-t) htNegMem) (hsmall (-t) htNegMem)
    change ‖B t‖ ≤ _ at hraw ⊢
    rw [show |-t| = t by rw [abs_neg, abs_of_pos htPos]] at hraw
    exact hraw.trans (div_le_div_of_nonneg_left (by positivity) huPos ht.1)
  have hibp := MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_of_totalVariation
    (A := B) (A' := deriv B) (omega := -Real.log x)
    (M0 := 3 * L / u) (V0 := V * Real.log (v / u))
    huv (neg_ne_zero.mpr hlogx.ne') hBderiv hB'int hB0 hvariation
  have hibp' :
      ‖∫ t in u..v, B t * Complex.exp (I * ((-Real.log x) * t))‖ ≤
        (6 * L / u + V * Real.log (v / u)) / Real.log x := by
    rw [show 6 * L / u = 2 * (3 * L / u) by ring]
    simpa [abs_of_pos hlogx] using hibp
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hfactor :
      (∫ t in (-v)..(-u),
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)) =
        ((x ^ a : ℝ) : ℂ) *
          ∫ t in u..v, B t * Complex.exp (I * ((-Real.log x) * t)) := by
    rw [← intervalIntegral.integral_comp_neg
      (fun t : ℝ => desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t))]
    calc
      (∫ t in u..v,
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a (-t))) =
          ∫ t in u..v, ((x ^ a : ℝ) : ℂ) *
            (B t * Complex.exp (I * ((-Real.log x) * t))) := by
              apply intervalIntegral.integral_congr
              intro t _ht
              change desmoothedCubicContourIntegrand x h
                (cubicLeftContourPoint a (-t)) = _
              rw [desmoothedCubicLeftContourIntegrand_eq_rpow_mul_amplitude_mul_cexp hxPos]
              dsimp [B, A]
              have hphase : (Real.log x : ℂ) * ((-t : ℝ) : ℂ) =
                  (-(Real.log x : ℂ)) * (t : ℂ) := by
                push_cast
                ring
              rw [hphase]
              ring
      _ = ((x ^ a : ℝ) : ℂ) *
          ∫ t in u..v, B t * Complex.exp (I * ((-Real.log x) * t)) :=
        intervalIntegral.integral_const_mul _ _
  rw [hfactor, norm_mul, norm_real]
  have hxpow : 0 ≤ x ^ a := (Real.rpow_pos_of_pos hxPos a).le
  simpa [V, Real.norm_eq_abs, abs_of_nonneg hxpow] using
    mul_le_mul_of_nonneg_left hibp' hxpow

/-- Combining the positive and negative high-height pieces costs only the
triangle-inequality factor two.  All hypotheses concern the actual zeta
logarithmic derivative on the two contour intervals. -/
theorem norm_add_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
    {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzetaPos : ∀ t ∈ Set.Icc u v,
      riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlogPos : ∀ t ∈ Set.Icc u v,
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlogPos' : ∀ t ∈ Set.Icc u v,
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmallPos : ∀ t ∈ Set.Icc u v,
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2)
    (hzetaNeg : ∀ t ∈ Set.Icc (-v) (-u),
      riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlogNeg : ∀ t ∈ Set.Icc (-v) (-u),
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlogNeg' : ∀ t ∈ Set.Icc (-v) (-u),
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmallNeg : ∀ t ∈ Set.Icc (-v) (-u),
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖(∫ t in u..v,
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)) +
        ∫ t in (-v)..(-u),
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
      2 * x ^ a *
        ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
          Real.log x) := by
  have hpos := norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
    (a := a) hx hh hu huv hL hD hzetaPos hlogPos hlogPos' hsmallPos
  have hneg := norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_neg_le
    (a := a) hx hh hu huv hL hD hzetaNeg hlogNeg hlogNeg' hsmallNeg
  calc
    ‖(∫ t in u..v,
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)) +
        ∫ t in (-v)..(-u),
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
        ‖∫ t in u..v,
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ +
        ‖∫ t in (-v)..(-u),
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ :=
      norm_add_le _ _
    _ ≤ x ^ a *
          ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) / Real.log x) +
        x ^ a *
          ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) / Real.log x) :=
      add_le_add hpos hneg
    _ = 2 * x ^ a *
          ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) / Real.log x) := by
      ring

/-- The negative high-height analogue of
`exists_dynamicCubicLeftBoundary_positive_interval_oscillatory_bound`, on the
same actual dynamic zeta boundary and with the same explicit constant. -/
theorem exists_dynamicCubicLeftBoundary_negative_interval_oscillatory_bound :
    ∃ b C D T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H x h u v : ℝ, T0 ≤ H → 1 < x → 0 < h →
        T0 + 1 ≤ u → u ≤ v → v + 1 ≤ H → h * H ≤ 1 / 2 →
          let a := dynamicCubicLeftBoundary b H
          ‖∫ t in (-v)..(-u),
              desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
            x ^ a *
              ((6 * (C * (1 + Real.log (H + 6)) ^ 2) / u +
                (3 * (D * (1 + Real.log (H + 6)) ^ 3) +
                  11 * (C * (1 + Real.log (H + 6)) ^ 2)) *
                    Real.log (v / u)) / Real.log x) := by
  rcases exists_dynamicCubicLeftBoundary_logDeriv_and_deriv_le with
    ⟨b, C, D, T0, hb, hC, hD, hT0, hbase⟩
  refine ⟨b, C, D, T0, hb, hC, hD, hT0, ?_⟩
  intro H x h u v hH hx hh hu huv hvH hhH
  rcases hbase H hH with ⟨ha, haThird, hpoint⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  let LH : ℝ := 1 + Real.log (H + 6)
  have haA : 0 < a := by simpa [a] using ha
  have huTwo : 2 ≤ u := by linarith
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) huTwo
  have hL0 : 0 ≤ C * LH ^ 2 := mul_nonneg hC (sq_nonneg _)
  have hLH : 0 ≤ LH := by
    dsimp [LH]
    have : 0 < Real.log (H + 6) :=
      Real.log_pos (by linarith [hT0.trans hH] : (1 : ℝ) < H + 6)
    linarith
  have hD0 : 0 ≤ D * LH ^ 3 := mul_nonneg hD (pow_nonneg hLH 3)
  have hdata : ∀ t ∈ Set.Icc (-v) (-u),
      riemannZeta ((a : ℂ) + I * t) ≠ 0 ∧
        ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ C * LH ^ 2 ∧
        ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D * LH ^ 3 := by
    intro t ht
    have htNeg : t < 0 := lt_of_le_of_lt ht.2 (neg_lt_zero.mpr huPos)
    have htAbs : |t| = -t := abs_of_neg htNeg
    have htLow : T0 + 1 ≤ |t| := by rw [htAbs]; linarith [ht.2, hu]
    have htHigh : |t| + 1 ≤ H := by rw [htAbs]; linarith [ht.1, hvH]
    simpa [a, LH] using hpoint t htLow htHigh
  have hscale : ∀ t ∈ Set.Icc (-v) (-u),
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2 := by
    intro t ht
    have htNeg : t < 0 := lt_of_le_of_lt ht.2 (neg_lt_zero.mpr huPos)
    have htAbs : |t| = -t := abs_of_neg htNeg
    have hnorm : ‖(a : ℂ) + I * t‖ ≤ a + (-t) := by
      calc
        ‖(a : ℂ) + I * t‖ ≤ ‖(a : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
        _ = a + (-t) := by simp [abs_of_pos haA, htAbs]
    have hatH : a + (-t) ≤ H := by
      have htH : -t + 1 ≤ H := by linarith [ht.1, hvH]
      linarith
    calc
      h * ‖(a : ℂ) + I * t‖ ≤ h * (a + (-t)) :=
        mul_le_mul_of_nonneg_left hnorm hh.le
      _ ≤ h * H := mul_le_mul_of_nonneg_left hatH hh.le
      _ ≤ 1 / 2 := hhH
  change ‖∫ t in (-v)..(-u),
      desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤ _
  simpa [LH] using
    norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_neg_le
      (a := a) hx hh huTwo huv hL0 hD0
        (fun t ht => (hdata t ht).1)
        (fun t ht => (hdata t ht).2.1)
        (fun t ht => (hdata t ht).2.2) hscale

end ExplicitFormulaResidues
end PrimeNumberTheorem
