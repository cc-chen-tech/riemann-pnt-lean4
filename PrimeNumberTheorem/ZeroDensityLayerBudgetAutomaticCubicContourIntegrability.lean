import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicContourKernelFactorization

open Complex MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

noncomputable def cubicBottomContourPoint (W sigma : ℝ) : ℂ :=
  (sigma : ℂ) + ((-(2 * Real.pi * W) : ℝ) : ℂ) * I

noncomputable def cubicTopContourPoint (W sigma : ℝ) : ℂ :=
  (sigma : ℂ) + (((2 * Real.pi * W) : ℝ) : ℂ) * I

noncomputable def cubicLeftContourPoint (a t : ℝ) : ℂ :=
  (a : ℂ) + (t : ℂ) * I

/-- The third-order explicit-formula integrand is analytic away from the
Perron origin, the zeta pole, and zeta zeros. -/
theorem analyticAt_thirdOrderExplicitFormulaIntegrand_of_ne
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    AnalyticAt ℂ (thirdOrderExplicitFormulaIntegrand x) s := by
  have hfirst :=
    analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
      hx hs0 hs1 hzeta
  have hsecond := hfirst.div analyticAt_id hs0
  have hthird := hsecond.div analyticAt_id hs0
  simpa [thirdOrderExplicitFormulaIntegrand,
    secondOrderExplicitFormulaIntegrand] using hthird

private lemma horizontalContourPoint_ne_zero
    {sigma y : ℝ} (hsigma : 0 < sigma) :
    ((sigma : ℂ) + (y : ℂ) * I) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp at hre
  linarith

theorem cubicBottomContourPoint_ne_zero
    {a c W sigma : ℝ} (ha : 0 < a) (hac : a < c)
    (hsigma : sigma ∈ [[a, c]]) :
    cubicBottomContourPoint W sigma ≠ 0 := by
  rw [uIcc_of_le hac.le] at hsigma
  exact horizontalContourPoint_ne_zero (lt_of_lt_of_le ha hsigma.1)

theorem cubicTopContourPoint_ne_zero
    {a c W sigma : ℝ} (ha : 0 < a) (hac : a < c)
    (hsigma : sigma ∈ [[a, c]]) :
    cubicTopContourPoint W sigma ≠ 0 := by
  rw [uIcc_of_le hac.le] at hsigma
  exact horizontalContourPoint_ne_zero (lt_of_lt_of_le ha hsigma.1)

theorem cubicLeftContourPoint_ne_zero
    {a t : ℝ} (ha : 0 < a) :
    cubicLeftContourPoint a t ≠ 0 :=
  horizontalContourPoint_ne_zero ha

/-- The rectangle boundary condition automatically makes the cubic integrand
continuous and interval-integrable on the bottom edge. -/
theorem intervalIntegrable_thirdOrderExplicitFormulaIntegrand_bottom
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    IntervalIntegrable
      (fun sigma => thirdOrderExplicitFormulaIntegrand x
        (cubicBottomContourPoint W sigma)) volume a c := by
  apply ContinuousOn.intervalIntegrable
  intro sigma hsigma
  have hvertical : -(2 * Real.pi * W) ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_pos]
  have hpK : cubicBottomContourPoint W sigma ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) := by
    constructor
    · simpa [cubicBottomContourPoint] using hsigma
    · rw [uIcc_of_le hvertical]
      simp [cubicBottomContourPoint, hvertical]
  have hnot : ¬(cubicBottomContourPoint W sigma = 1 ∨
      riemannZeta (cubicBottomContourPoint W sigma) = 0) := by
    intro hpole
    have hinterior := hboundary _ hpK hpole
    have himpossible : -(2 * Real.pi * W) < -(2 * Real.pi * W) := by
      simpa [cubicBottomContourPoint] using hinterior.2.2.1
    exact (lt_irrefl _ himpossible)
  have han := analyticAt_thirdOrderExplicitFormulaIntegrand_of_ne hx
    (cubicBottomContourPoint_ne_zero ha hac hsigma)
    (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))
  have hpath : Continuous (cubicBottomContourPoint W) := by
    unfold cubicBottomContourPoint
    fun_prop
  have hcomp := han.continuousAt.comp hpath.continuousAt
  simpa [Function.comp_def] using hcomp.continuousWithinAt

/-- Automatic interval integrability on the top edge. -/
theorem intervalIntegrable_thirdOrderExplicitFormulaIntegrand_top
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    IntervalIntegrable
      (fun sigma => thirdOrderExplicitFormulaIntegrand x
        (cubicTopContourPoint W sigma)) volume a c := by
  apply ContinuousOn.intervalIntegrable
  intro sigma hsigma
  have hvertical : -(2 * Real.pi * W) ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_pos]
  have hpK : cubicTopContourPoint W sigma ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) := by
    constructor
    · simpa [cubicTopContourPoint] using hsigma
    · rw [uIcc_of_le hvertical]
      simp [cubicTopContourPoint, hvertical]
  have hnot : ¬(cubicTopContourPoint W sigma = 1 ∨
      riemannZeta (cubicTopContourPoint W sigma) = 0) := by
    intro hpole
    have hinterior := hboundary _ hpK hpole
    have himpossible : 2 * Real.pi * W < 2 * Real.pi * W := by
      simpa [cubicTopContourPoint] using hinterior.2.2.2
    exact (lt_irrefl _ himpossible)
  have han := analyticAt_thirdOrderExplicitFormulaIntegrand_of_ne hx
    (cubicTopContourPoint_ne_zero ha hac hsigma)
    (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))
  have hpath : Continuous (cubicTopContourPoint W) := by
    unfold cubicTopContourPoint
    fun_prop
  have hcomp := han.continuousAt.comp hpath.continuousAt
  simpa [Function.comp_def] using hcomp.continuousWithinAt

/-- Automatic interval integrability on the left edge. -/
theorem intervalIntegrable_thirdOrderExplicitFormulaIntegrand_left
    {x a c W : ℝ} (hx : 0 < x) (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    IntervalIntegrable
      (fun t => thirdOrderExplicitFormulaIntegrand x
        (cubicLeftContourPoint a t)) volume
      (-(2 * Real.pi * W)) (2 * Real.pi * W) := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have hvertical : -(2 * Real.pi * W) ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_pos]
  have hpK : cubicLeftContourPoint a t ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) := by
    constructor
    · rw [uIcc_of_le hac.le]
      simp [cubicLeftContourPoint, hac.le]
    · simpa [cubicLeftContourPoint] using ht
  have hnot : ¬(cubicLeftContourPoint a t = 1 ∨
      riemannZeta (cubicLeftContourPoint a t) = 0) := by
    intro hpole
    have hinterior := hboundary _ hpK hpole
    have himpossible : a < a := by
      simpa [cubicLeftContourPoint] using hinterior.1
    exact (lt_irrefl _ himpossible)
  have han := analyticAt_thirdOrderExplicitFormulaIntegrand_of_ne hx
    (cubicLeftContourPoint_ne_zero ha)
    (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))
  have hpath : Continuous (cubicLeftContourPoint a) := by
    unfold cubicLeftContourPoint
    fun_prop
  have hcomp := han.continuousAt.comp hpath.continuousAt
  simpa [Function.comp_def] using hcomp.continuousWithinAt

/-- Stack 194's pathwise transfer is automatic on the actual bottom edge. -/
theorem intervalIntegral_bottom_thirdOrder_secondDifference_div_sq_eq
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ((∫ sigma : ℝ in a..c, thirdOrderExplicitFormulaIntegrand
          (x * Real.exp (2 * h)) (cubicBottomContourPoint W sigma)) -
        2 * (∫ sigma : ℝ in a..c, thirdOrderExplicitFormulaIntegrand
          (x * Real.exp h) (cubicBottomContourPoint W sigma)) +
        (∫ sigma : ℝ in a..c, thirdOrderExplicitFormulaIntegrand
          x (cubicBottomContourPoint W sigma))) / (h : ℂ) ^ 2 =
      ∫ sigma : ℝ in a..c,
        desmoothedCubicContourIntegrand x h
          (cubicBottomContourPoint W sigma) := by
  apply intervalIntegral_thirdOrder_secondDifference_div_sq_eq
    hx hh (cubicBottomContourPoint W)
  · exact fun sigma hsigma => cubicBottomContourPoint_ne_zero ha hac hsigma
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_bottom
      hx ha hac hW hboundary
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_bottom
      (mul_pos hx (Real.exp_pos h)) ha hac hW hboundary
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_bottom
      (mul_pos hx (Real.exp_pos (2 * h))) ha hac hW hboundary

/-- Automatic pathwise transfer on the actual top edge. -/
theorem intervalIntegral_top_thirdOrder_secondDifference_div_sq_eq
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ((∫ sigma : ℝ in a..c, thirdOrderExplicitFormulaIntegrand
          (x * Real.exp (2 * h)) (cubicTopContourPoint W sigma)) -
        2 * (∫ sigma : ℝ in a..c, thirdOrderExplicitFormulaIntegrand
          (x * Real.exp h) (cubicTopContourPoint W sigma)) +
        (∫ sigma : ℝ in a..c, thirdOrderExplicitFormulaIntegrand
          x (cubicTopContourPoint W sigma))) / (h : ℂ) ^ 2 =
      ∫ sigma : ℝ in a..c,
        desmoothedCubicContourIntegrand x h
          (cubicTopContourPoint W sigma) := by
  apply intervalIntegral_thirdOrder_secondDifference_div_sq_eq
    hx hh (cubicTopContourPoint W)
  · exact fun sigma hsigma => cubicTopContourPoint_ne_zero ha hac hsigma
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_top
      hx ha hac hW hboundary
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_top
      (mul_pos hx (Real.exp_pos h)) ha hac hW hboundary
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_top
      (mul_pos hx (Real.exp_pos (2 * h))) ha hac hW hboundary

/-- Automatic pathwise transfer on the actual left edge. -/
theorem intervalIntegral_left_thirdOrder_secondDifference_div_sq_eq
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (ha : 0 < a) (hac : a < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
        ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ((∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
          thirdOrderExplicitFormulaIntegrand
            (x * Real.exp (2 * h)) (cubicLeftContourPoint a t)) -
        2 * (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
          thirdOrderExplicitFormulaIntegrand
            (x * Real.exp h) (cubicLeftContourPoint a t)) +
        (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
          thirdOrderExplicitFormulaIntegrand
            x (cubicLeftContourPoint a t))) / (h : ℂ) ^ 2 =
      ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
        desmoothedCubicContourIntegrand x h
          (cubicLeftContourPoint a t) := by
  apply intervalIntegral_thirdOrder_secondDifference_div_sq_eq
    hx hh (cubicLeftContourPoint a)
  · exact fun _ _ => cubicLeftContourPoint_ne_zero ha
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_left
      hx ha hac hW hboundary
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_left
      (mul_pos hx (Real.exp_pos h)) ha hac hW hboundary
  · exact intervalIntegrable_thirdOrderExplicitFormulaIntegrand_left
      (mul_pos hx (Real.exp_pos (2 * h))) ha hac hW hboundary

end ExplicitFormulaResidues
end PrimeNumberTheorem
