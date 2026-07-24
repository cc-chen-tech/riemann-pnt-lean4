import HardyTheorem.SelbergSqrtZetaLowRangeEnergy
import HardyTheorem.SelbergShortDirichletCollected
import MathlibAux.SlidingExponentialCoefficientBound

open Complex
open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-!
# Sliding energy of the low-range square-root zeta coefficient

The arithmetic coefficient of `ζ(s) M_X(s)^2` on the critical line is the
collected Dirichlet coefficient divided by `sqrt n`.  In the complete cutoff
range the preceding arithmetic calculation identifies that coefficient with
`selbergSqrtZetaLowRangeCoeff X n / sqrt n`.  This file converts the constant
weighted energy bound into the sliding-coefficient estimate used by the
short-window mean-square argument.
-/

/-- The critical-line coefficient attached to the complete arithmetic
coefficient of `ζ(s) M_X(s)^2`. -/
noncomputable def selbergSqrtZetaArithmeticDirichletCoeff
    (X n : ℕ) : ℂ :=
  (((selbergShortTaperedSqrtZeta X *
          selbergShortTaperedSqrtZeta X) *
        (ArithmeticFunction.zeta :
          ArithmeticFunction ℝ)) n : ℂ) *
    (Real.sqrt (n : ℝ) : ℂ)⁻¹

/-- The normalized low-range critical-line coefficient. -/
noncomputable def selbergSqrtZetaLowRangeDirichletCoeff
    (X n : ℕ) : ℂ :=
  (selbergSqrtZetaLowRangeCoeff X n : ℂ) *
    (Real.sqrt (n : ℝ) : ℂ)⁻¹

/-- In the complete cutoff range, the actual arithmetic coefficient of
`ζ(s) M_X(s)^2` is the explicit low-range coefficient. -/
theorem selbergSqrtZetaArithmeticDirichletCoeff_eq_lowRange
    {X n : ℕ} (hX : 1 < X) (hn : 1 < n) (hnX : n ≤ X) :
    selbergSqrtZetaArithmeticDirichletCoeff X n =
      selbergSqrtZetaLowRangeDirichletCoeff X n := by
  unfold selbergSqrtZetaArithmeticDirichletCoeff
  unfold selbergSqrtZetaLowRangeDirichletCoeff
  rw [selbergShortTaperedSqrtZeta_collected_eq_lowRangeCoeff
    hX hn hnX]

/-- The square norm of a low-range critical-line coefficient is exactly the
weighted coefficient square occurring in the arithmetic energy theorem. -/
theorem normSq_selbergSqrtZetaLowRangeDirichletCoeff
    {X n : ℕ} (hn : 1 ≤ n) :
    Complex.normSq (selbergSqrtZetaLowRangeDirichletCoeff X n) =
      selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold selbergSqrtZetaLowRangeDirichletCoeff
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_inv, Complex.normSq_ofReal,
    Real.mul_self_sqrt hn0.le]
  simp only [div_eq_mul_inv]
  ring

/-- The complete low-range critical-line coefficient energy is bounded by
the absolute constant `15/4`. -/
theorem sum_normSq_selbergSqrtZetaLowRangeDirichletCoeff_le_fifteen_fourths
    {X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) :
    (∑ n ∈ Finset.Ioc 1 X,
        Complex.normSq
          (selbergSqrtZetaLowRangeDirichletCoeff X n)) ≤
      (15 : ℝ) / 4 := by
  calc
    (∑ n ∈ Finset.Ioc 1 X,
        Complex.normSq
          (selbergSqrtZetaLowRangeDirichletCoeff X n)) =
        ∑ n ∈ Finset.Ioc 1 X,
          selbergSqrtZetaLowRangeCoeff X n ^ 2 / (n : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact normSq_selbergSqrtZetaLowRangeDirichletCoeff
        (Finset.mem_Ioc.mp hn).1.le
    _ ≤ (15 : ℝ) / 4 :=
      sum_sq_selbergSqrtZetaLowRangeCoeff_div_le_fifteen_fourths
        hX hlarge

/-- Sliding an exponential coefficient over an interval of length `H` costs
at most the factor `H^2` in square energy. -/
theorem normSq_slidingExponentialCoefficient_le_mul_sq
    {ι : Type*} (H : ℝ) (coeff : ι → ℂ) (freq : ι → ℝ) (j : ι) :
    Complex.normSq
        (MathlibAux.slidingExponentialCoefficient H coeff freq j) ≤
      H ^ 2 * Complex.normSq (coeff j) := by
  have hslide :=
    MathlibAux.norm_slidingExponentialCoefficient_le_abs_length
      H coeff freq j
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖MathlibAux.slidingExponentialCoefficient H coeff freq j‖ ^ 2 ≤
        (‖coeff j‖ * |H|) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hslide
    _ = H ^ 2 * Complex.normSq (coeff j) := by
      rw [mul_pow, sq_abs, Complex.normSq_eq_norm_sq]
      ring

/-- The sliding low-range square-root-zeta coefficient energy is
`O(H^2)` with an explicit absolute constant. -/
theorem sum_normSq_sliding_selbergSqrtZetaLowRangeDirichletCoeff_le
    {X : ℕ} (hX : 1 < X)
    (hlarge : Real.log 4 + 5 ≤ Real.log X) (H : ℝ) :
    (∑ n ∈ Finset.Ioc 1 X,
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaLowRangeDirichletCoeff X)
            selbergShortDirichletCollectedFrequency n)) ≤
      (15 : ℝ) / 4 * H ^ 2 := by
  calc
    (∑ n ∈ Finset.Ioc 1 X,
        Complex.normSq
          (MathlibAux.slidingExponentialCoefficient H
            (selbergSqrtZetaLowRangeDirichletCoeff X)
            selbergShortDirichletCollectedFrequency n)) ≤
        ∑ n ∈ Finset.Ioc 1 X,
          H ^ 2 * Complex.normSq
            (selbergSqrtZetaLowRangeDirichletCoeff X n) := by
      apply Finset.sum_le_sum
      intro n _hn
      exact normSq_slidingExponentialCoefficient_le_mul_sq
        H (selbergSqrtZetaLowRangeDirichletCoeff X)
          selbergShortDirichletCollectedFrequency n
    _ = H ^ 2 * ∑ n ∈ Finset.Ioc 1 X,
          Complex.normSq
            (selbergSqrtZetaLowRangeDirichletCoeff X n) := by
      rw [Finset.mul_sum]
    _ ≤ H ^ 2 * ((15 : ℝ) / 4) := by
      exact mul_le_mul_of_nonneg_left
        (sum_normSq_selbergSqrtZetaLowRangeDirichletCoeff_le_fifteen_fourths
          hX hlarge) (sq_nonneg H)
    _ = (15 : ℝ) / 4 * H ^ 2 := by ring

end HardyTheorem
