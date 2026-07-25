import PrimeNumberTheorem.VKEdgePiOverTwoZetaContour
import PrimeNumberTheorem.LeftVerticalEdge

open Complex Polynomial

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Exact modulus of the polynomial-Gaussian contour weight. -/
theorem norm_localizedGaussianWeight
    (A : ℂ[X]) (w z : ℂ) (m : ℝ) :
    ‖localizedGaussianWeight A w m z‖ =
      ‖A.eval (z - w)‖ *
        Real.exp
          (m * (((z - w).re) ^ 2 - ((z - w).im) ^ 2 +
            16 * (z - w).re)) := by
  unfold localizedGaussianWeight
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/--
A fixed polynomial grows at most like its coefficient `L¹` norm times the
maximum of `1` and the evaluation radius, raised to the polynomial degree.
-/
theorem norm_polynomial_eval_le_coeffL1_mul_max_pow
    (A : ℂ[X]) (z : ℂ) :
    ‖A.eval z‖ ≤
      (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 ‖z‖ ^ A.natDegree := by
  rw [A.eval_eq_sum]
  calc
    ‖∑ k ∈ A.support, A.coeff k * z ^ k‖ ≤
        ∑ k ∈ A.support, ‖A.coeff k * z ^ k‖ :=
      norm_sum_le A.support fun k => A.coeff k * z ^ k
    _ = ∑ k ∈ A.support, ‖A.coeff k‖ * ‖z‖ ^ k := by
      simp only [norm_mul, norm_pow]
    _ ≤ ∑ k ∈ A.support,
        ‖A.coeff k‖ * max 1 ‖z‖ ^ A.natDegree := by
      apply Finset.sum_le_sum
      intro k hk
      gcongr
      exact
        (pow_le_pow_left₀ (norm_nonneg z) (le_max_right 1 ‖z‖) k).trans
          (pow_le_pow_right₀ (le_max_left 1 ‖z‖)
            (A.le_natDegree_of_mem_supp k hk))
    _ = (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 ‖z‖ ^ A.natDegree := by
      rw [Finset.sum_mul]

/--
On the fixed left edge `Re(z) = -1`, the Gaussian factor has a uniform
exponential saving.  The constant `15` is valid simultaneously for every
center real part `0 < u < 1`.
-/
theorem norm_localizedGaussianWeight_left_le
    (A : ℂ[X]) {u v t m : ℝ}
    (hu : 0 < u) (hu1 : u < 1) (hm : 0 ≤ m) :
    ‖localizedGaussianWeight A
        ((u : ℂ) + I * v) m
        ((-1 : ℂ) + I * t)‖ ≤
      ‖A.eval (((-1 : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (-15 * m - m * (t - v) ^ 2) := by
  rw [norm_localizedGaussianWeight]
  gcongr
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have huProduct : 0 < u * (1 - u) :=
    mul_pos hu (sub_pos.mpr hu1)
  nlinarith

/-- Uniform finite-height bound for `-ζ'/ζ` on the fixed line `Re(z) = -1`. -/
def leftLogDerivBound (T : ℝ) : ℝ :=
  ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
    ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
      Real.log (T + 4)) + Real.pi

theorem leftLogDerivBound_nonneg {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ leftLogDerivBound T := by
  have hseries :
      0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
    tsum_nonneg fun n => norm_nonneg _
  have hlog : 0 ≤ Real.log (T + 4) :=
    Real.log_nonneg (by linarith)
  unfold leftLogDerivBound
  positivity

/-- The pole-subtraction factor is uniformly bounded on `Re(z) = -1`. -/
theorem norm_div_sub_one_left_vertical_le_one (t : ℝ) :
    ‖(((-1 : ℂ) + I * t) /
      (((-1 : ℂ) + I * t) - 1))‖ ≤ 1 := by
  let z : ℂ := (-1 : ℂ) + I * t
  have hzsub : z - 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [z] at hre
  have hsq : ‖z‖ ^ 2 ≤ ‖z - 1‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
    norm_num [z]
  rw [norm_div, div_le_one (norm_pos_iff.mpr hzsub)]
  exact
    (sq_le_sq₀ (norm_nonneg z) (norm_nonneg (z - 1))).mp hsq

/--
Pointwise left-edge estimate for the actual regularized zeta logarithmic
derivative multiplied by the localized polynomial-Gaussian weight.
-/
theorem norm_regularizedLogDeriv_localizedGaussianWeight_left_le
    (A : ℂ[X]) {u v T t m : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hT : 0 ≤ T) (ht : |t| ≤ T) (hm : 0 ≤ m) :
    ‖localizedGaussianWeight A ((u : ℂ) + I * v) m
          ((-1 : ℂ) + I * t) *
        (-logDeriv riemannZeta ((-1 : ℂ) + I * t) -
          (((-1 : ℂ) + I * t) /
            (((-1 : ℂ) + I * t) - 1)))‖ ≤
      ‖A.eval (((-1 : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (-15 * m - m * (t - v) ^ 2) *
          (leftLogDerivBound T + 1) := by
  let z : ℂ := (-1 : ℂ) + I * t
  let w : ℂ := (u : ℂ) + I * v
  have hweight :
      ‖localizedGaussianWeight A w m z‖ ≤
        ‖A.eval (z - w)‖ *
          Real.exp (-15 * m - m * (t - v) ^ 2) := by
    simpa [z, w] using
      norm_localizedGaussianWeight_left_le A hu hu1 hm
  have hlog :
      ‖-logDeriv riemannZeta z‖ ≤ leftLogDerivBound T := by
    have hbase :=
      ExplicitFormulaResidues.norm_neg_logDeriv_riemannZeta_odd_vertical_le_of_abs_le
        (N := 0) hT ht
    simpa [z, leftLogDerivBound, mul_comm] using hbase
  have hregularized :
      ‖-logDeriv riemannZeta z - z / (z - 1)‖ ≤
        leftLogDerivBound T + 1 := by
    calc
      ‖-logDeriv riemannZeta z - z / (z - 1)‖ ≤
          ‖-logDeriv riemannZeta z‖ + ‖z / (z - 1)‖ :=
        norm_sub_le _ _
      _ ≤ leftLogDerivBound T + 1 := by
        gcongr
        simpa [z] using norm_div_sub_one_left_vertical_le_one t
  rw [norm_mul]
  exact mul_le_mul hweight hregularized
    (norm_nonneg _) (by
      positivity [leftLogDerivBound_nonneg hT])

/--
Uniform version of the true zeta left-edge bound.  All dependence on the
height variable is absorbed into a polynomial factor determined by `A`.
-/
theorem norm_regularizedLogDeriv_localizedGaussianWeight_left_le_uniform
    (A : ℂ[X]) {u v T t m : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hT : 0 ≤ T) (ht : |t| ≤ T) (hm : 0 ≤ m) :
    ‖localizedGaussianWeight A ((u : ℂ) + I * v) m
          ((-1 : ℂ) + I * t) *
        (-logDeriv riemannZeta ((-1 : ℂ) + I * t) -
          (((-1 : ℂ) + I * t) /
            (((-1 : ℂ) + I * t) - 1)))‖ ≤
      (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 (u + T + |v| + 2) ^ A.natDegree *
        Real.exp (-15 * m) * (leftLogDerivBound T + 1) := by
  let d : ℂ :=
    ((-1 : ℂ) + I * t) - ((u : ℂ) + I * v)
  have hd :
      ‖d‖ ≤ u + T + |v| + 2 := by
    calc
      ‖d‖ ≤ |d.re| + |d.im| :=
        Complex.norm_le_abs_re_add_abs_im d
      _ = (1 + u) + |t - v| := by
        norm_num [d, Complex.sub_re, Complex.sub_im,
          abs_of_neg (by linarith : -1 - u < 0)]
        ring
      _ ≤ (1 + u) + (|t| + |v|) := by
        gcongr
        exact abs_sub t v
      _ ≤ u + T + |v| + 2 := by linarith
  have hpoly :
      ‖A.eval d‖ ≤
        (∑ k ∈ A.support, ‖A.coeff k‖) *
          max 1 (u + T + |v| + 2) ^ A.natDegree := by
    calc
      ‖A.eval d‖ ≤
          (∑ k ∈ A.support, ‖A.coeff k‖) *
            max 1 ‖d‖ ^ A.natDegree :=
        norm_polynomial_eval_le_coeffL1_mul_max_pow A d
      _ ≤ (∑ k ∈ A.support, ‖A.coeff k‖) *
            max 1 (u + T + |v| + 2) ^ A.natDegree := by
        gcongr
  have hexp :
      Real.exp (-15 * m - m * (t - v) ^ 2) ≤
        Real.exp (-15 * m) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hm (sq_nonneg (t - v))]
  calc
    _ ≤ ‖A.eval d‖ *
          Real.exp (-15 * m - m * (t - v) ^ 2) *
            (leftLogDerivBound T + 1) := by
      simpa [d] using
        norm_regularizedLogDeriv_localizedGaussianWeight_left_le
          A hu hu1 hT ht hm
    _ ≤ (∑ k ∈ A.support, ‖A.coeff k‖) *
          max 1 (u + T + |v| + 2) ^ A.natDegree *
          Real.exp (-15 * m) * (leftLogDerivBound T + 1) := by
      gcongr
      exact add_nonneg (leftLogDerivBound_nonneg hT) (by norm_num)

/-- Explicit finite-height bound for the complete true-zeta left edge. -/
theorem norm_integral_regularizedLogDeriv_localizedGaussianWeight_left_le
    (A : ℂ[X]) {u v T m : ℝ}
    (hu : 0 < u) (hu1 : u < 1)
    (hT : 0 ≤ T) (hm : 0 ≤ m) :
    ‖∫ t : ℝ in (-T)..T,
        localizedGaussianWeight A ((u : ℂ) + I * v) m
            ((-1 : ℂ) + I * t) *
          (-logDeriv riemannZeta ((-1 : ℂ) + I * t) -
            (((-1 : ℂ) + I * t) /
              (((-1 : ℂ) + I * t) - 1)))‖ ≤
      ((∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 (u + T + |v| + 2) ^ A.natDegree *
        Real.exp (-15 * m) * (leftLogDerivBound T + 1)) *
          (2 * T) := by
  let C : ℝ :=
    (∑ k ∈ A.support, ‖A.coeff k‖) *
      max 1 (u + T + |v| + 2) ^ A.natDegree *
      Real.exp (-15 * m) * (leftLogDerivBound T + 1)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ =>
      localizedGaussianWeight A ((u : ℂ) + I * v) m
          ((-1 : ℂ) + I * t) *
        (-logDeriv riemannZeta ((-1 : ℂ) + I * t) -
          (((-1 : ℂ) + I * t) /
            (((-1 : ℂ) + I * t) - 1))))
    (a := -T) (b := T) (C := C) (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T :=
        abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact
        norm_regularizedLogDeriv_localizedGaussianWeight_left_le_uniform
          A hu hu1 hT habs hm)
  change _ ≤ C * (2 * T)
  convert hbound using 1
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]
  ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
