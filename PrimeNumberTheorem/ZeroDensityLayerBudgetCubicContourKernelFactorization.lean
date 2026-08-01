import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicKernelNearOne

open Complex MeasureTheory Set
open scoped Interval

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The first-order explicit-formula integrand with the exact cubic
de-smoothing multiplier. -/
noncomputable def desmoothedCubicContourIntegrand
    (x h : ℝ) (s : ℂ) : ℂ :=
  explicitFormulaIntegrand x s * cubicKernelMultiplier s h

/-- Logarithmic translation of the sample point multiplies the actual
first-order explicit-formula integrand by `exp (h s)`. -/
theorem explicitFormulaIntegrand_mul_exp_shift
    {x h : ℝ} (hx : 0 < x) (s : ℂ) :
    explicitFormulaIntegrand (x * Real.exp h) s =
      explicitFormulaIntegrand x s * Complex.exp ((h : ℂ) * s) := by
  rw [explicitFormulaIntegrand, explicitFormulaIntegrand,
    ofReal_mul_exp_cpow_eq_cpow_mul_exp (h := h) hx s]
  ring

/-- Pointwise, the normalized logarithmic second difference of the cubic
integrand is exactly the classical first-order integrand times the same
multiplier that appears in the zero residues. -/
theorem thirdOrderExplicitFormulaIntegrand_secondDifference_div_sq_eq
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) {s : ℂ} (hs : s ≠ 0) :
    (thirdOrderExplicitFormulaIntegrand (x * Real.exp (2 * h)) s -
        2 * thirdOrderExplicitFormulaIntegrand (x * Real.exp h) s +
        thirdOrderExplicitFormulaIntegrand x s) / (h : ℂ) ^ 2 =
      desmoothedCubicContourIntegrand x h s := by
  rw [thirdOrderExplicitFormulaIntegrand_eq_explicitFormulaIntegrand_div_sq,
    thirdOrderExplicitFormulaIntegrand_eq_explicitFormulaIntegrand_div_sq,
    thirdOrderExplicitFormulaIntegrand_eq_explicitFormulaIntegrand_div_sq,
    explicitFormulaIntegrand_mul_exp_shift (h := h) hx s,
    explicitFormulaIntegrand_mul_exp_shift (h := 2 * h) hx s,
    desmoothedCubicContourIntegrand, cubicKernelMultiplier]
  have hexpTwo :
      Complex.exp (((2 * h : ℝ) : ℂ) * s) =
        Complex.exp ((h : ℂ) * s) * Complex.exp ((h : ℂ) * s) := by
    rw [show (((2 * h : ℝ) : ℂ) * s) =
        (h : ℂ) * s + (h : ℂ) * s by push_cast; ring,
      Complex.exp_add]
  rw [hexpTwo]
  field_simp [Complex.ofReal_ne_zero.mpr hh.ne', hs]
  ring

/-- A pathwise integral version of the pointwise factorization.  The only
analytic input exposed here is interval integrability of the three cubic
integrands; no contour estimate is hidden in the transfer. -/
theorem intervalIntegral_thirdOrder_secondDifference_div_sq_eq
    {x h A B : ℝ} (hx : 0 < x) (hh : 0 < h) (gamma : ℝ → ℂ)
    (hgamma : ∀ t ∈ [[A, B]], gamma t ≠ 0)
    (hint0 : IntervalIntegrable
      (fun t => thirdOrderExplicitFormulaIntegrand x (gamma t)) volume A B)
    (hint1 : IntervalIntegrable
      (fun t => thirdOrderExplicitFormulaIntegrand
        (x * Real.exp h) (gamma t)) volume A B)
    (hint2 : IntervalIntegrable
      (fun t => thirdOrderExplicitFormulaIntegrand
        (x * Real.exp (2 * h)) (gamma t)) volume A B) :
    ((∫ t : ℝ in A..B,
          thirdOrderExplicitFormulaIntegrand
            (x * Real.exp (2 * h)) (gamma t)) -
        2 * (∫ t : ℝ in A..B,
          thirdOrderExplicitFormulaIntegrand
            (x * Real.exp h) (gamma t)) +
        (∫ t : ℝ in A..B,
          thirdOrderExplicitFormulaIntegrand x (gamma t))) / (h : ℂ) ^ 2 =
      ∫ t : ℝ in A..B, desmoothedCubicContourIntegrand x h (gamma t) := by
  let f0 : ℝ → ℂ := fun t =>
    thirdOrderExplicitFormulaIntegrand x (gamma t)
  let f1 : ℝ → ℂ := fun t =>
    thirdOrderExplicitFormulaIntegrand (x * Real.exp h) (gamma t)
  let f2 : ℝ → ℂ := fun t =>
    thirdOrderExplicitFormulaIntegrand (x * Real.exp (2 * h)) (gamma t)
  change IntervalIntegrable f0 volume A B at hint0
  change IntervalIntegrable f1 volume A B at hint1
  change IntervalIntegrable f2 volume A B at hint2
  have hcomb : IntervalIntegrable
      (fun t => f2 t - 2 * f1 t + f0 t) volume A B :=
    (hint2.sub (hint1.const_mul 2)).add hint0
  have hmul :
      (∫ t : ℝ in A..B, (2 : ℂ) * f1 t) =
        2 * (∫ t : ℝ in A..B, f1 t) :=
    intervalIntegral.integral_const_mul (2 : ℂ) f1
  have hlin :
      (∫ t : ℝ in A..B, f2 t - 2 * f1 t + f0 t) =
        (∫ t : ℝ in A..B, f2 t) -
          2 * (∫ t : ℝ in A..B, f1 t) +
          (∫ t : ℝ in A..B, f0 t) := by
    rw [intervalIntegral.integral_add
        (hint2.sub (hint1.const_mul 2)) hint0,
      intervalIntegral.integral_sub hint2 (hint1.const_mul 2),
      hmul]
  change ((∫ t : ℝ in A..B, f2 t) -
      2 * (∫ t : ℝ in A..B, f1 t) +
      (∫ t : ℝ in A..B, f0 t)) / (h : ℂ) ^ 2 = _
  calc
    ((∫ t : ℝ in A..B, f2 t) -
          2 * (∫ t : ℝ in A..B, f1 t) +
          (∫ t : ℝ in A..B, f0 t)) / (h : ℂ) ^ 2 =
        ((h : ℂ) ^ 2)⁻¹ *
          (∫ t : ℝ in A..B, f2 t - 2 * f1 t + f0 t) := by
      rw [hlin]
      ring
    _ = ∫ t : ℝ in A..B,
          ((h : ℂ) ^ 2)⁻¹ * (f2 t - 2 * f1 t + f0 t) := by
      exact (intervalIntegral.integral_const_mul
        (((h : ℂ) ^ 2)⁻¹) (fun t => f2 t - 2 * f1 t + f0 t)).symm
    _ = ∫ t : ℝ in A..B,
          (f2 t - 2 * f1 t + f0 t) / (h : ℂ) ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = ∫ t : ℝ in A..B,
          desmoothedCubicContourIntegrand x h (gamma t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact thirdOrderExplicitFormulaIntegrand_secondDifference_div_sq_eq
        hx hh (hgamma t ht)

end ExplicitFormulaResidues
end PrimeNumberTheorem
