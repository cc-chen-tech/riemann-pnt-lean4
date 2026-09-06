import PrimeNumberTheorem.WindowedMellinL2
import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicKernelLocal

/-!
# Windowed detector response kernel

Bridges the local cubic zero kernel (`ZeroDensityLayerBudgetCubicKernelLocal`,
the re-derived per-zero kernel layer of the cubic line) to the L2/L3
response framework: the per-zero windowed Mellin response kernel

    zeroResponseKernel ρ x h γ
      = cubicZeroResidueSecondDifference ρ x h / h² · exp(−i γ log x),

its exact norm identity, and the two-sided scale bounds under the
near-one multiplier control.  These are the per-zero statements the L3
windowed-detector assembly sums over the top layer and the
complementary layer.
-/

namespace PrimeNumberTheorem
namespace WindowedMellinL2

open Complex
open scoped BigOperators
open ExplicitFormulaAux

/-- The per-zero response coefficient: the constant part of the cubic
kernel (`-m/rho` times the exponential multiplier). -/
noncomputable def zeroResponseCoeff (rho : ℂ) (h : ℝ) : ℂ :=
  -(analyticOrderNatAt riemannZeta rho : ℂ) / rho *
    ExplicitFormulaResidues.cubicKernelMultiplier rho h

/-- The per-zero windowed Mellin response kernel: the normalized cubic
residue kernel times the frequency phase `exp(-i γ log x)`. -/
noncomputable def zeroResponseKernel (rho : ℂ) (x h γ : ℝ) : ℂ :=
  ExplicitFormulaResidues.cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2 *
    Complex.exp (-(Complex.I * (γ : ℂ) * Real.log x))

/-- Exact norm identity of the response kernel: the frequency phase has
norm one, so the norm is `m · x^(Re rho) / |rho| · |multiplier|`. -/
theorem norm_zeroResponseKernel_eq
    {rho : ℂ} {x h γ : ℝ} (hx : 0 < x) (hh : 0 < h) (hrho : rho ≠ 0) :
    ‖zeroResponseKernel rho x h γ‖ =
      (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ *
        ‖ExplicitFormulaResidues.cubicKernelMultiplier rho h‖ := by
  dsimp [zeroResponseKernel]
  rw [norm_mul]
  rw [ExplicitFormulaResidues.norm_cubicZeroResidueSecondDifference_div_sq_eq
    hx hh hrho]
  have hphase : ‖Complex.exp (-(Complex.I * (γ : ℂ) * Real.log x))‖ = 1 := by
    rw [Complex.norm_exp]
    rw [Complex.neg_re, Complex.mul_re]
    -- Re(−i·γ·log x) = −(0·γ·log x − 1·γ·0·...) = 0
    simp [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, neg_zero, Real.exp_zero]
  rw [hphase, mul_one]

/-- Two-sided scale bounds: on `h |rho| ≤ 1` (and `h ≤ log 2`,
`0 ≤ Re rho ≤ 1`) the response kernel norm lies between
`(1 − ε) m x^(Re rho) / |rho|` and `(1 + ε) m x^(Re rho) / |rho|` for
`ε = 3 h |rho|`. -/
theorem norm_zeroResponseKernel_correctScale_bounds
    {rho : ℂ} {x h γ : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hre : 0 ≤ rho.re) (hre1 : rho.re ≤ 1)
    (hsmall : h * ‖rho‖ ≤ 1) (hrho : rho ≠ 0) :
    let scale :=
      (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖
    (1 - 3 * (h * ‖rho‖)) * scale ≤ ‖zeroResponseKernel rho x h γ‖ ∧
      ‖zeroResponseKernel rho x h γ‖ ≤ (1 + 3 * (h * ‖rho‖)) * scale := by
  dsimp only
  have hnear : ‖ExplicitFormulaResidues.cubicKernelMultiplier rho h - 1‖ ≤
      3 * (h * ‖rho‖) := by
    exact ExplicitFormulaResidues.norm_cubicKernelMultiplier_sub_one_le_three_mul
      hh hrho hsmall
  have hmult := ExplicitFormulaResidues.norm_multiplier_bounds_of_sub_one_le hnear
  have hscale :
      0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ := by
    positivity
  rw [norm_zeroResponseKernel_eq hx hh hrho]
  constructor
  · rw [mul_comm (1 - 3 * (h * ‖rho‖))]
    exact mul_le_mul_of_nonneg_left hmult.1 hscale
  · rw [mul_comm (1 + 3 * (h * ‖rho‖))]
    exact mul_le_mul_of_nonneg_left hmult.2 hscale

/-- Uniform upper bound of the response kernel on the top layer
(`T0/2 ≤ |rho|`, `Re rho ∈ [0, 1]`, `h ≤ log 2`):
`‖kernel‖ ≤ max 4 (36/(h·T0/2)²) · m · x^(Re rho) / |rho|`. -/
theorem norm_zeroResponseKernel_le_uniform
    {rho : ℂ} {x h γ T0 : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hre : 0 ≤ rho.re) (hre1 : rho.re ≤ 1)
    (hT0 : 0 < T0) (hT0half : T0 / 2 ≤ ‖rho‖) (hhsmall : h ≤ Real.log 2)
    (hrho : rho ≠ 0) :
    ‖zeroResponseKernel rho x h γ‖ ≤
      max 4 (36 / (h * (T0 / 2)) ^ 2) *
        ((analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖) := by
  have hmult := ExplicitFormulaResidues.norm_cubicKernelMultiplier_le_uniform
    hh hre hre1 hT0 hT0half hhsmall hrho
  have hscale :
      0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ := by
    positivity
  calc
    ‖zeroResponseKernel rho x h γ‖ =
        (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ *
          ‖ExplicitFormulaResidues.cubicKernelMultiplier rho h‖ := by
      exact norm_zeroResponseKernel_eq hx hh hrho
    _ ≤ (analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖ *
          max 4 (36 / (h * (T0 / 2)) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hmult hscale
    _ = max 4 (36 / (h * (T0 / 2)) ^ 2) *
          ((analyticOrderNatAt riemannZeta rho : ℝ) * x ^ rho.re / ‖rho‖) := by
      ring

end WindowedMellinL2
end PrimeNumberTheorem
