import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCubicDynamicLowLeft
import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicContourKernelFactorization

/-!
# Actual compact low vertical integral for the cubic kernel

The compact low-height logarithmic-derivative budget includes analyticity, so
it can be transferred to the actual third-order explicit-formula integrand.
The elementary pointwise denominator estimate used here is deliberately coarse:
`‖a + it‖ ≥ a` gives an explicit `a⁻³` loss.  For the dynamic boundary this is
a cubic logarithmic loss.  No sharper `a⁻²` integrated estimate is claimed.
-/

namespace PrimeNumberTheorem

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval
open ExplicitFormulaResidues

/-- Analyticity of the logarithmic derivative and positivity of the Perron
abscissa suffice for analyticity of the actual cubic integrand. -/
theorem analyticAt_thirdOrderExplicitFormulaIntegrand_of_analyticAt_logDeriv
    {x : ℝ} (hx : 0 < x) {s : ℂ} (hs0 : s ≠ 0)
    (hlog : AnalyticAt ℂ (logDeriv riemannZeta) s) :
    AnalyticAt ℂ (thirdOrderExplicitFormulaIntegrand x) s := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpow : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s :=
    ((differentiable_id : Differentiable ℂ (fun z : ℂ => z)).const_cpow
      (Or.inl hx0)).analyticAt s
  have hfirst : AnalyticAt ℂ
      (fun z : ℂ => -logDeriv riemannZeta z * (x : ℂ) ^ z) s := by
    simpa only [Pi.neg_apply, Pi.mul_apply] using hlog.neg.mul hpow
  have hdiv1 : AnalyticAt ℂ
      (fun z : ℂ => (-logDeriv riemannZeta z * (x : ℂ) ^ z) / z) s := by
    simpa only [Pi.div_apply, id_eq] using hfirst.div analyticAt_id hs0
  have hdiv2 : AnalyticAt ℂ
      (fun z : ℂ => ((-logDeriv riemannZeta z * (x : ℂ) ^ z) / z) / z) s := by
    simpa only [Pi.div_apply, id_eq] using hdiv1.div analyticAt_id hs0
  have hdiv3 : AnalyticAt ℂ
      (fun z : ℂ => (((-logDeriv riemannZeta z * (x : ℂ) ^ z) / z) / z) / z) s := by
    simpa only [Pi.div_apply, id_eq] using hdiv2.div analyticAt_id hs0
  change AnalyticAt ℂ
    (fun z : ℂ => (((-logDeriv riemannZeta z * (x : ℂ) ^ z) / z) / z) / z) s
  exact hdiv3

/-- A compact low segment with an analytic logarithmic-derivative budget has
an actual cubic-integrand bound with the explicit coarse `a⁻³` loss. -/
theorem norm_integral_actualCubicLowVertical_le_of_analyticAt
    {x a C T : ℝ} (hx : 0 < x) (ha : 0 < a) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (han : ∀ t : ℝ, |t| ≤ T →
      AnalyticAt ℂ (logDeriv riemannZeta) ((a : ℂ) + I * t))
    (hlog : ∀ t : ℝ, |t| ≤ T →
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ C) :
    ‖∫ t : ℝ in (-T)..T,
        thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤
      2 * T * (x ^ a * C / a ^ 3) := by
  let f : ℝ → ℂ := fun t =>
    thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)
  let K : ℝ := C * x ^ a
  let g : ℝ → ℝ := fun _ => K / a ^ 3
  have horder : -T ≤ T := by linarith
  have hxpow : 0 ≤ x ^ a := Real.rpow_nonneg hx.le _
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfInt : IntervalIntegrable f volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    intro t htI
    rw [uIcc_of_le horder] at htI
    have htAbs : |t| ≤ T := abs_le.mpr htI
    let s : ℂ := (a : ℂ) + t * I
    have hs0 : s ≠ 0 := by
      intro hs
      have hre := congrArg Complex.re hs
      simp [s] at hre
      linarith
    have hsEq : s = (a : ℂ) + I * t := by dsimp [s]; ring
    have hanS : AnalyticAt ℂ (logDeriv riemannZeta) s := by
      rw [hsEq]
      exact han t htAbs
    have hkernel :=
      analyticAt_thirdOrderExplicitFormulaIntegrand_of_analyticAt_logDeriv
        hx hs0 hanS
    have hpath : Continuous (fun u : ℝ => (a : ℂ) + u * I) := by fun_prop
    have hcomp : ContinuousAt
        (thirdOrderExplicitFormulaIntegrand x ∘
          fun u : ℝ => (a : ℂ) + u * I) t :=
      hkernel.continuousAt.comp_of_eq hpath.continuousAt rfl
    simpa [f, Function.comp_def] using hcomp.continuousWithinAt
  have hgInt : IntervalIntegrable g volume (-T) T := intervalIntegrable_const
  have hmajor : ∀ᵐ t : ℝ, t ∈ Set.Ioc (-T) T → ‖f t‖ ≤ g t := by
    filter_upwards [] with t htI
    have htIcc : t ∈ Set.Icc (-T) T := ⟨htI.1.le, htI.2⟩
    have htAbs : |t| ≤ T := abs_le.mpr htIcc
    let s : ℂ := (a : ℂ) + t * I
    have hsEq : s = (a : ℂ) + I * t := by dsimp [s]; ring
    have hlogS : ‖logDeriv riemannZeta s‖ ≤ C := by
      rw [hsEq]
      exact hlog t htAbs
    have hsNorm : a ≤ ‖s‖ := by
      calc
        a = |s.re| := by simp [s, abs_of_pos ha]
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    have hpowDen : a ^ 3 ≤ ‖s‖ ^ 3 :=
      pow_le_pow_left₀ ha.le hsNorm 3
    have hnum : ‖logDeriv riemannZeta s‖ * x ^ a ≤ K := by
      dsimp [K]
      exact mul_le_mul_of_nonneg_right hlogS hxpow
    change ‖thirdOrderExplicitFormulaIntegrand x s‖ ≤ g t
    rw [norm_thirdOrderExplicitFormulaIntegrand_eq hx]
    have hsre : s.re = a := by simp [s]
    rw [hsre]
    calc
      ‖logDeriv riemannZeta s‖ * x ^ a / ‖s‖ ^ 3 ≤ K / ‖s‖ ^ 3 :=
        div_le_div_of_nonneg_right hnum (pow_nonneg (norm_nonneg _) _)
      _ ≤ K / a ^ 3 :=
        div_le_div_of_nonneg_left hK (pow_pos ha 3) hpowDen
      _ = g t := rfl
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le horder hmajor hgInt
  calc
    ‖∫ t : ℝ in (-T)..T, f t‖ ≤ ∫ t : ℝ in (-T)..T, g t := hnorm
    _ = 2 * T * (K / a ^ 3) := by simp [g]; ring
    _ = 2 * T * (x ^ a * C / a ^ 3) := by simp [K, mul_comm]

/-- The actual compact low vertical segment on every positive dynamic cubic
boundary has a uniform constant and the explicit `a(H)⁻³` kernel loss. -/
theorem exists_norm_integral_actualCubicLowVertical_le
    (b T : ℝ) (hb : 0 < b) (hT : 0 ≤ T) :
    ∃ C H0 : ℝ, 0 ≤ C ∧ 4 ≤ H0 ∧
      ∀ (x H : ℝ), 0 < x → H0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        ‖∫ t : ℝ in (-T)..T,
            thirdOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)‖ ≤
          2 * T * (x ^ a * C / a ^ 3) := by
  rcases exists_dynamicCubicLowLeft_analyticAt_logDeriv_budget b T hb with
    ⟨C, H0, hC, hH0, hbudget⟩
  refine ⟨C, H0, hC, hH0, ?_⟩
  intro x H hx hH
  have hH4 : 4 ≤ H := hH0.trans hH
  have ha : 0 < dynamicCubicLeftBoundary b H := by
    dsimp [dynamicCubicLeftBoundary]
    have hlog : 0 < Real.log (H + 6) :=
      Real.log_pos (by linarith : (1 : ℝ) < H + 6)
    positivity
  apply norm_integral_actualCubicLowVertical_le_of_analyticAt hx ha hC hT
  · intro t ht
    exact (hbudget H hH t ht).1
  · intro t ht
    exact (hbudget H hH t ht).2

end PrimeNumberTheorem
