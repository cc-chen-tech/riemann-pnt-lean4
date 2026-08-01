import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicResidueSecondDifferenceKernel

open Complex

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- The normalized exponential second-difference multiplier attached to a
cubic residue kernel. -/
noncomputable def cubicKernelMultiplier (rho : ℂ) (h : ℝ) : ℂ :=
  ((Complex.exp ((h : ℂ) * rho) - 1) / ((h : ℂ) * rho)) ^ 2

/-- The classical unnormalized simple zero kernel. -/
noncomputable def cubicSimpleZeroKernel (rho : ℂ) (x : ℝ) : ℂ :=
  -(analyticOrderNatAt riemannZeta rho : ℂ) * (x : ℂ) ^ rho / rho

/-- Multiplying a positive real base by `exp h` translates its complex power
by the exact factor `exp (h * rho)`. -/
theorem ofReal_mul_exp_cpow_eq_cpow_mul_exp
    {x h : ℝ} (hx : 0 < x) (rho : ℂ) :
    ((x * Real.exp h : ℝ) : ℂ) ^ rho =
      (x : ℂ) ^ rho * Complex.exp ((h : ℂ) * rho) := by
  rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (mul_pos hx (Real.exp_pos h)).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log (mul_pos hx (Real.exp_pos h)).le,
    Real.log_mul hx.ne' (Real.exp_ne_zero h), Real.log_exp,
    ← Complex.ofReal_log hx.le]
  rw [show (((Real.log x + h : ℝ) : ℂ) * rho) =
      (Real.log x : ℂ) * rho + (h : ℂ) * rho by push_cast; ring,
    Complex.exp_add]

/-- Exact factorization of the normalized cubic discrete kernel into the
classical simple zero kernel and its exponential difference multiplier. -/
theorem cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier
    {rho : ℂ} {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (hrho : rho ≠ 0) :
    cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2 =
      cubicSimpleZeroKernel rho x * cubicKernelMultiplier rho h := by
  rw [cubicZeroResidueSecondDifference, cubicSimpleZeroKernel,
    cubicKernelMultiplier,
    ofReal_mul_exp_cpow_eq_cpow_mul_exp (h := h) hx rho,
    ofReal_mul_exp_cpow_eq_cpow_mul_exp (h := 2 * h) hx rho]
  have hexpTwo :
      Complex.exp (((2 * h : ℝ) : ℂ) * rho) =
        Complex.exp ((h : ℂ) * rho) * Complex.exp ((h : ℂ) * rho) := by
    rw [show (((2 * h : ℝ) : ℂ) * rho) =
        (h : ℂ) * rho + (h : ℂ) * rho by push_cast; ring,
      Complex.exp_add]
  rw [hexpTwo]
  field_simp [Complex.ofReal_ne_zero.mpr hh.ne', hrho]
  ring

/-- The classical simple kernel has exactly the desired
`multiplicity * x^(Re rho) / |rho|` norm. -/
theorem norm_cubicSimpleZeroKernel_eq
    {rho : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖cubicSimpleZeroKernel rho x‖ =
      (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ := by
  rw [cubicSimpleZeroKernel, norm_div, norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- Consequently the normalized cubic kernel preserves the correct simple
zero scale, up to the explicit multiplier norm. -/
theorem norm_cubicZeroResidueSecondDifference_div_sq_eq
    {rho : ℂ} {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (hrho : rho ≠ 0) :
    ‖cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2‖ =
      ((analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖) *
        ‖cubicKernelMultiplier rho h‖ := by
  rw [cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier
    hx hh hrho, norm_mul, norm_cubicSimpleZeroKernel_eq hx]

/-- The pole-at-one term admits the analogous exact real multiplier
factorization. -/
theorem cubicPoleOneSecondDifference_div_sq_eq
    {x h : ℝ} (hh : 0 < h) :
    cubicPoleOneSecondDifference x h / (h : ℂ) ^ 2 =
      (x : ℂ) * ((((Real.exp h - 1) / h : ℝ) : ℂ) ^ 2) := by
  rw [cubicPoleOneSecondDifference]
  have hexpTwo : Real.exp (2 * h) = Real.exp h * Real.exp h := by
    rw [show 2 * h = h + h by ring, Real.exp_add]
  rw [hexpTwo]
  push_cast
  field_simp [hh.ne']
  ring

end ExplicitFormulaResidues
end PrimeNumberTheorem
