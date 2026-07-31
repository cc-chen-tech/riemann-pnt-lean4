import PrimeNumberTheorem.VKEdgePiOverTwoCenteredContour
import PrimeNumberTheorem.VKEdgePiOverTwoFarZeroDecay

open Complex Filter MeasureTheory Polynomial Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The fixed vertical radius used to remove all centered near-zero poles. -/
def centeredPoleRadius (q : ℝ) : ℝ :=
  q + 5

/--
The enlarged radius leaves an exponential margin of at least eight for every
real-part displacement in the critical strip.
-/
theorem real_sq_add_q_mul_sub_centeredPoleRadius_sq_le
    {q a : ℝ} (hq : 0 < q) (ha : |a| ≤ 1) :
    a ^ 2 + q * a - centeredPoleRadius q ^ 2 ≤ -8 := by
  have haLower : -1 ≤ a := (abs_le.mp ha).1
  have haUpper : a ≤ 1 := (abs_le.mp ha).2
  have haSq : a ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr haLower)
      (sub_nonneg.mpr haUpper)]
  have hqa : q * a ≤ q := by
    nlinarith
  unfold centeredPoleRadius
  nlinarith [sq_nonneg q]

/-- Exact modulus of the centered polynomial-Gaussian contour weight. -/
theorem norm_localizedGaussianWeightAtCenter
    (q : ℝ) (A : ℂ[X]) (w z : ℂ) (m : ℝ) :
    ‖localizedGaussianWeightAtCenter q A w m z‖ =
      ‖A.eval (z - w)‖ *
        Real.exp
          (m * (((z - w).re) ^ 2 - ((z - w).im) ^ 2 +
            q * (z - w).re)) := by
  unfold localizedGaussianWeightAtCenter
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/--
For `q ≥ 16`, the centered left edge retains the original
`exp (-15*m)` saving.
-/
theorem norm_localizedGaussianWeightAtCenter_left_le
    (q : ℝ) (A : ℂ[X]) {u v t m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1) (hm : 0 ≤ m) :
    ‖localizedGaussianWeightAtCenter q A
        ((u : ℂ) + I * v) m
        ((-1 : ℂ) + I * t)‖ ≤
      ‖A.eval (((-1 : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (-15 * m - m * (t - v) ^ 2) := by
  rw [norm_localizedGaussianWeightAtCenter]
  gcongr
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hqa :
      q * (-1 - u) ≤ 16 * (-1 - u) := by
    exact mul_le_mul_of_nonpos_right hq (by linarith)
  have huProduct : 0 < u * (1 - u) :=
    mul_pos hu (sub_pos.mpr hu1)
  nlinarith

/--
On every horizontal or right edge, the centered real-direction exponent is
bounded by the exact constant `4 + 2*q`.
-/
theorem norm_localizedGaussianWeightAtCenter_horizontal_le
    (q : ℝ) (A : ℂ[X]) {u v σ t m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ u + 2) (hm : 0 ≤ m) :
    ‖localizedGaussianWeightAtCenter q A
        ((u : ℂ) + I * v) m ((σ : ℂ) + I * t)‖ ≤
      ‖A.eval (((σ : ℂ) + I * t) - ((u : ℂ) + I * v))‖ *
        Real.exp (m * ((4 + 2 * q) - (t - v) ^ 2)) := by
  rw [norm_localizedGaussianWeightAtCenter]
  gcongr
  let a : ℝ := σ - u
  have haLower : -2 < a := by
    dsimp [a]
    linarith
  have haUpper : a ≤ 2 := by
    dsimp [a]
    linarith
  have hfactor : 0 ≤ (2 - a) * (q + 2 + a) :=
    mul_nonneg (sub_nonneg.mpr haUpper) (by linarith)
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im] at *
  nlinarith [mul_nonneg hm hfactor]

private theorem
    norm_localizedGaussianWeightAtCenter_horizontal_le_uniform
    (q : ℝ) (A : ℂ[X]) {u v T σ t m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ u + 2)
    (ht : |t| = T) (hm : 0 ≤ m) :
    ‖localizedGaussianWeightAtCenter q A
        ((u : ℂ) + I * v) m ((σ : ℂ) + I * t)‖ ≤
      (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 (T + |v| + 3) ^ A.natDegree *
          Real.exp (m * ((4 + 2 * q) - (t - v) ^ 2)) := by
  let d : ℂ :=
    ((σ : ℂ) + I * t) - ((u : ℂ) + I * v)
  have hre : |σ - u| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  have him : |t - v| ≤ T + |v| := by
    calc
      |t - v| ≤ |t| + |v| := abs_sub t v
      _ = T + |v| := by rw [ht]
  have hd : ‖d‖ ≤ T + |v| + 3 := by
    calc
      ‖d‖ ≤ |d.re| + |d.im| :=
        Complex.norm_le_abs_re_add_abs_im d
      _ = |σ - u| + |t - v| := by
        norm_num [d, Complex.sub_re, Complex.sub_im]
      _ ≤ 2 + (T + |v|) := add_le_add hre him
      _ ≤ T + |v| + 3 := by linarith
  have hpoly :
      ‖A.eval d‖ ≤
        (∑ k ∈ A.support, ‖A.coeff k‖) *
          max 1 (T + |v| + 3) ^ A.natDegree := by
    calc
      ‖A.eval d‖ ≤
          (∑ k ∈ A.support, ‖A.coeff k‖) *
            max 1 ‖d‖ ^ A.natDegree :=
        norm_polynomial_eval_le_coeffL1_mul_max_pow A d
      _ ≤ (∑ k ∈ A.support, ‖A.coeff k‖) *
            max 1 (T + |v| + 3) ^ A.natDegree := by
        gcongr
  calc
    _ ≤ ‖A.eval d‖ *
          Real.exp (m * ((4 + 2 * q) - (t - v) ^ 2)) := by
      simpa [d] using
        norm_localizedGaussianWeightAtCenter_horizontal_le
          q A hq hu hu1 hσlo hσhi hm
    _ ≤ (∑ k ∈ A.support, ‖A.coeff k‖) *
          max 1 (T + |v| + 3) ^ A.natDegree *
            Real.exp (m * ((4 + 2 * q) - (t - v) ^ 2)) := by
      gcongr

private theorem
    norm_localizedGaussianWeightAtCenter_horizontal_le_heightGap
    (q : ℝ) (A : ℂ[X]) {u v T σ t m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hσlo : -1 ≤ σ) (hσhi : σ ≤ u + 2)
    (hgap : 12 * m + |v| ≤ T) (ht : |t| = T)
    (hm : 1 ≤ m) (hqScale : q ≤ 27 * m ^ 2) :
    ‖localizedGaussianWeightAtCenter q A
        ((u : ℂ) + I * v) m ((σ : ℂ) + I * t)‖ ≤
      (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 (T + |v| + 3) ^ A.natDegree *
          Real.exp (-(m * (T - |v|) ^ 2) / 2) := by
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hdNonneg : 0 ≤ T - |v| := by linarith
  have hdAbs : T - |v| ≤ |t - v| := by
    calc
      T - |v| = |t| - |v| := by rw [ht]
      _ ≤ |t - v| := abs_sub_abs_le_abs_sub t v
  have hdSq : (T - |v|) ^ 2 ≤ (t - v) ^ 2 := by
    have h :=
      (sq_le_sq₀ hdNonneg (abs_nonneg (t - v))).2 hdAbs
    simpa [sq_abs] using h
  have hdTwelve : 12 * m ≤ T - |v| := by linarith
  have hdSqLarge : 2 * (4 + 2 * q) ≤ (T - |v|) ^ 2 := by
    have hmFactor : 0 ≤ (m - 1) * (m + 1) :=
      mul_nonneg (sub_nonneg.mpr hm) (by positivity)
    nlinarith [sq_nonneg (T - |v| - 12 * m)]
  have hmulSq :
      m * (T - |v|) ^ 2 ≤ m * (t - v) ^ 2 :=
    mul_le_mul_of_nonneg_left hdSq hm0
  have hexponent :
      m * ((4 + 2 * q) - (t - v) ^ 2) ≤
        -(m * (T - |v|) ^ 2) / 2 := by
    nlinarith [mul_nonneg hm0
      (sub_nonneg.mpr hdSqLarge)]
  calc
    _ ≤ (∑ k ∈ A.support, ‖A.coeff k‖) *
          max 1 (T + |v| + 3) ^ A.natDegree *
            Real.exp (m * ((4 + 2 * q) - (t - v) ^ 2)) :=
      norm_localizedGaussianWeightAtCenter_horizontal_le_uniform
        q A hq hu hu1 hσlo hσhi ht hm0
    _ ≤ (∑ k ∈ A.support, ‖A.coeff k‖) *
          max 1 (T + |v| + 3) ^ A.natDegree *
            Real.exp (-(m * (T - |v|) ^ 2) / 2) := by
      gcongr

private theorem
    norm_regularizedLogDeriv_localizedGaussianWeightAtCenter_left_le_uniform
    (q : ℝ) (A : ℂ[X]) {u v T t m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hT : 0 ≤ T) (ht : |t| ≤ T) (hm : 0 ≤ m) :
    ‖localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m ((-1 : ℂ) + I * t)‖ ≤
      (∑ k ∈ A.support, ‖A.coeff k‖) *
        max 1 (u + T + |v| + 2) ^ A.natDegree *
        Real.exp (-15 * m) * (leftLogDerivBound T + 1) := by
  let z : ℂ := (-1 : ℂ) + I * t
  let w : ℂ := (u : ℂ) + I * v
  let d : ℂ := z - w
  have hd :
      ‖d‖ ≤ u + T + |v| + 2 := by
    calc
      ‖d‖ ≤ |d.re| + |d.im| :=
        Complex.norm_le_abs_re_add_abs_im d
      _ = (1 + u) + |t - v| := by
        norm_num [d, z, w, Complex.sub_re, Complex.sub_im,
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
  have hweight :
      ‖localizedGaussianWeightAtCenter q A w m z‖ ≤
        ‖A.eval d‖ *
          Real.exp (-15 * m - m * (t - v) ^ 2) := by
    simpa [z, w, d] using
      norm_localizedGaussianWeightAtCenter_left_le
        q A hq hu hu1 hm
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
      _ ≤ ‖-logDeriv riemannZeta z‖ + ‖z / (z - 1)‖ :=
        norm_sub_le _ _
      _ ≤ leftLogDerivBound T + 1 := by
        gcongr
        simpa [z] using norm_div_sub_one_left_vertical_le_one t
  have hexp :
      Real.exp (-15 * m - m * (t - v) ^ 2) ≤
        Real.exp (-15 * m) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hm (sq_nonneg (t - v))]
  rw [localizedRegularizedLogDerivIntegrandAtCenter, norm_mul]
  calc
    _ ≤ (‖A.eval d‖ *
          Real.exp (-15 * m - m * (t - v) ^ 2)) *
            (leftLogDerivBound T + 1) := by
      exact mul_le_mul hweight hregularized
        (norm_nonneg _) (by
          positivity [leftLogDerivBound_nonneg hT])
    _ ≤ (∑ k ∈ A.support, ‖A.coeff k‖) *
          max 1 (u + T + |v| + 2) ^ A.natDegree *
          Real.exp (-15 * m) * (leftLogDerivBound T + 1) := by
      gcongr
      exact add_nonneg (leftLogDerivBound_nonneg hT) (by norm_num)

private theorem
    norm_integral_regularizedLogDeriv_localizedGaussianWeightAtCenter_left_le
    (q : ℝ) (A : ℂ[X]) {u v T m : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hT : 0 ≤ T) (hm : 0 ≤ m) :
    ‖∫ t : ℝ in (-T)..T,
        localizedRegularizedLogDerivIntegrandAtCenter q A
          ((u : ℂ) + I * v) m ((-1 : ℂ) + I * t)‖ ≤
      localizedLeftEdgeUpperBound A u v m T := by
  let C : ℝ :=
    (∑ k ∈ A.support, ‖A.coeff k‖) *
      max 1 (u + T + |v| + 2) ^ A.natDegree *
      Real.exp (-15 * m) * (leftLogDerivBound T + 1)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ =>
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m ((-1 : ℂ) + I * t))
    (a := -T) (b := T) (C := C) (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T :=
        abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact
        norm_regularizedLogDeriv_localizedGaussianWeightAtCenter_left_le_uniform
          q A hq hu hu1 hT habs hm)
  unfold localizedLeftEdgeUpperBound
  change _ ≤ C * (2 * T)
  convert hbound using 1
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)]
  ring

private theorem
    norm_integral_regularizedLogDeriv_localizedGaussianWeightAtCenter_horizontal_le
    (q : ℝ) (A : ℂ[X]) {u v m t C H T : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hm : 1 ≤ m) (hqScale : q ≤ 27 * m ^ 2)
    (hTlower : 12 * m + |v| ≤ T) (ht : |t| = T)
    (hregularized :
      ∀ σ : ℝ, -1 ≤ σ → σ ≤ u + 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + I * t) -
            (((σ : ℂ) + I * t) /
              (((σ : ℂ) + I * t) - 1))‖ ≤
          max
            (C * (1 + Real.log (H + 6)) ^ 2)
            (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1) + 2) :
    ‖∫ σ : ℝ in (-1)..(u + 2),
        localizedRegularizedLogDerivIntegrandAtCenter q A
          ((u : ℂ) + I * v) m ((σ : ℂ) + I * t)‖ ≤
      localizedHorizontalEdgeUpperBound A u v m C H T := by
  let W : ℝ :=
    (∑ k ∈ A.support, ‖A.coeff k‖) *
      max 1 (T + |v| + 3) ^ A.natDegree *
        Real.exp (-(m * (T - |v|) ^ 2) / 2)
  let R : ℝ :=
    max
      (C * (1 + Real.log (H + 6)) ^ 2)
      (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1) + 2
  have hW : 0 ≤ W := by
    dsimp [W]
    positivity
  have hpoint : ∀ σ ∈ Set.uIoc (-1 : ℝ) (u + 2),
      ‖localizedRegularizedLogDerivIntegrandAtCenter q A
          ((u : ℂ) + I * v) m ((σ : ℂ) + I * t)‖ ≤ W * R := by
    intro σ hσ
    rw [Set.uIoc_of_le (by linarith)] at hσ
    have hweight :=
      norm_localizedGaussianWeightAtCenter_horizontal_le_heightGap
        q A hq hu hu1 hσ.1.le hσ.2 hTlower ht hm hqScale
    have hlog := hregularized σ hσ.1.le hσ.2
    rw [localizedRegularizedLogDerivIntegrandAtCenter, norm_mul]
    exact mul_le_mul hweight hlog (norm_nonneg _) hW
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ =>
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m ((σ : ℂ) + I * t))
    (a := (-1 : ℝ)) (b := u + 2) (C := W * R) hpoint
  unfold localizedHorizontalEdgeUpperBound
  change _ ≤ (W * R) * (u + 3)
  convert hbound using 1
  rw [abs_of_nonneg (by linarith : 0 ≤ u + 2 - (-1))]
  ring

private theorem
    localizedRegularizedLogDerivIntegrandAtCenter_eq_mul_phase
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ) (z : ℂ) :
    localizedRegularizedLogDerivIntegrandAtCenter q A w m z =
      localizedRegularizedLogDerivIntegrand A w m z *
        Complex.exp ((((q - 16) * m : ℝ) : ℂ) * (z - w)) := by
  unfold localizedRegularizedLogDerivIntegrandAtCenter
    localizedRegularizedLogDerivIntegrand
    localizedGaussianWeightAtCenter localizedGaussianWeight
  have harg :
      (m : ℂ) * (z - w) ^ 2 +
          ((q * m : ℝ) : ℂ) * (z - w) =
        ((m : ℂ) * (z - w) ^ 2 +
            ((16 * m : ℝ) : ℂ) * (z - w)) +
          (((q - 16) * m : ℝ) : ℂ) * (z - w) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  ring

/-- The centered true-zeta integrand is integrable on the complete right edge. -/
theorem
    integrable_localizedRegularizedLogDerivIntegrandAtCenter_verticalLine
    (q : ℝ) (A : ℂ[X]) {u v m : ℝ} (hu : 0 < u) (hm : 0 < m) :
    Integrable
      (fun t : ℝ =>
        localizedRegularizedLogDerivIntegrandAtCenter q A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)) := by
  let w : ℂ := (u : ℂ) + I * v
  let f : ℝ → ℂ := fun t =>
    localizedRegularizedLogDerivIntegrand A w m
      (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let p : ℝ → ℂ := fun t =>
    Complex.exp ((((q - 16) * m : ℝ) : ℂ) *
      ((((u + 2 : ℝ) : ℂ) + (t : ℂ) * I) - w))
  have hf : Integrable f := by
    simpa [f, w] using
      integrable_localizedRegularizedLogDerivIntegrand_verticalLine
        A hu hm
  have hp : AEStronglyMeasurable p := by
    exact (by fun_prop : Measurable p).aestronglyMeasurable
  have hpBound :
      ∀ᵐ t : ℝ,
        ‖p t‖ ≤ Real.exp (2 * ((q - 16) * m)) := by
    filter_upwards with t
    rw [Complex.norm_exp]
    dsimp [p, w]
    norm_num [Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.add_im, Complex.mul_im]
    ring_nf
    exact le_rfl
  have hproduct : Integrable (fun t => f t * p t) :=
    hf.mul_bdd hp hpBound
  apply hproduct.congr
  filter_upwards with t
  simpa [f, p, w] using
    (localizedRegularizedLogDerivIntegrandAtCenter_eq_mul_phase
      q A w m (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)).symm

/--
Past the fixed-`q` scale threshold, the centered right-edge integrand is
dominated by the same concentrated Gaussian used at center coefficient 16.
-/
theorem norm_localizedRegularizedLogDerivIntegrandAtCenter_right_le_gaussian
    (q : ℝ) (A : ℂ[X]) {u v m t : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hm : 1 ≤ m)
    (hdegree : (A.natDegree : ℝ) ≤ m)
    (hqScale : q ≤ 27 * m ^ 2)
    (htail : 12 * m ≤ |t - v|) :
    ‖localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        (((u + 2 : ℝ) : ℂ) + I * t)‖ ≤
      ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2)) *
        Real.exp (-(m / 2) * (t - v) ^ 2) := by
  have hqNonneg : 0 ≤ q := le_trans (by norm_num) hq
  let y : ℝ := t - v
  let d : ℂ :=
    (((u + 2 : ℝ) : ℂ) + I * t) -
      ((u : ℂ) + I * v)
  have hm0 : 0 ≤ m := zero_le_one.trans hm
  have hy : 12 * m ≤ |y| := by
    simpa [y] using htail
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hyTwelve : 12 ≤ |y| := by nlinarith
  have hdNorm : ‖d‖ ≤ |y| + 2 := by
    calc
      ‖d‖ ≤ |d.re| + |d.im| :=
        Complex.norm_le_abs_re_add_abs_im d
      _ = |y| + 2 := by
        simp only [d, y, Complex.sub_re, Complex.sub_im, Complex.add_re,
          Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        norm_num
        ring
  have hbase : max 1 ‖d‖ ≤ |y| + 2 := by
    rw [max_le_iff]
    exact ⟨by linarith, hdNorm⟩
  have hbaseExp : |y| + 2 ≤ Real.exp (|y| + 2) := by
    calc
      |y| + 2 ≤ |y| + 2 + 1 := by linarith
      _ ≤ Real.exp (|y| + 2) := Real.add_one_le_exp _
  have hpow :
      max 1 ‖d‖ ^ A.natDegree ≤
        Real.exp ((A.natDegree : ℝ) * (|y| + 2)) := by
    calc
      max 1 ‖d‖ ^ A.natDegree ≤
          (Real.exp (|y| + 2)) ^ A.natDegree := by
        gcongr
        exact hbase.trans hbaseExp
      _ = Real.exp ((A.natDegree : ℝ) * (|y| + 2)) := by
        rw [← Real.exp_nat_mul]
  have hdegreeMul :
      (A.natDegree : ℝ) * (|y| + 2) ≤
        m * (|y| + 2) :=
    mul_le_mul_of_nonneg_right hdegree (by positivity)
  have hlargeProduct :
      0 ≤ (|y| - 12 * m) * (|y| + 12 * m - 2) := by
    exact mul_nonneg (sub_nonneg.mpr hy) (by nlinarith)
  have hmProduct : 0 ≤ (m - 1) * (3 * m + 1) :=
    mul_nonneg (sub_nonneg.mpr hm) (by positivity)
  have hscalar :
      2 * (6 + 2 * q + |y|) ≤ |y| ^ 2 := by
    nlinarith [hqNonneg]
  have hexponent :
      m * ((4 + 2 * q) - y ^ 2) +
          (A.natDegree : ℝ) * (|y| + 2) ≤
        -(m / 2) * y ^ 2 := by
    have hySq : y ^ 2 = |y| ^ 2 := by rw [sq_abs]
    rw [hySq]
    calc
      m * ((4 + 2 * q) - |y| ^ 2) +
            (A.natDegree : ℝ) * (|y| + 2) ≤
          m * ((4 + 2 * q) - |y| ^ 2) +
            m * (|y| + 2) :=
        add_le_add_right hdegreeMul _
      _ ≤ -(m / 2) * |y| ^ 2 := by
        nlinarith [mul_nonneg hm0
          (sub_nonneg.mpr hscalar)]
  have hweight :
      ‖localizedGaussianWeightAtCenter q A
          ((u : ℂ) + I * v) m
          (((u + 2 : ℝ) : ℂ) + I * t)‖ ≤
        (∑ k ∈ A.support, ‖A.coeff k‖) *
          Real.exp (-(m / 2) * y ^ 2) := by
    rw [norm_localizedGaussianWeightAtCenter]
    have hpoly :=
      norm_polynomial_eval_le_coeffL1_mul_max_pow A d
    have hcoord :
        ((((u + 2 : ℝ) : ℂ) + I * t) -
            ((u : ℂ) + I * v)).re ^ 2 -
          ((((u + 2 : ℝ) : ℂ) + I * t) -
            ((u : ℂ) + I * v)).im ^ 2 +
          q *
            ((((u + 2 : ℝ) : ℂ) + I * t) -
              ((u : ℂ) + I * v)).re =
          (4 + 2 * q) - y ^ 2 := by
      simp only [y, Complex.sub_re, Complex.sub_im, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      norm_num
      ring
    rw [hcoord]
    calc
      ‖A.eval d‖ * Real.exp (m * ((4 + 2 * q) - y ^ 2)) ≤
          ((∑ k ∈ A.support, ‖A.coeff k‖) *
            max 1 ‖d‖ ^ A.natDegree) *
              Real.exp (m * ((4 + 2 * q) - y ^ 2)) := by
        gcongr
      _ ≤
          ((∑ k ∈ A.support, ‖A.coeff k‖) *
            Real.exp ((A.natDegree : ℝ) * (|y| + 2))) *
              Real.exp (m * ((4 + 2 * q) - y ^ 2)) := by
        gcongr
      _ =
          (∑ k ∈ A.support, ‖A.coeff k‖) *
            Real.exp
              (m * ((4 + 2 * q) - y ^ 2) +
                (A.natDegree : ℝ) * (|y| + 2)) := by
        rw [Real.exp_add]
        ring
      _ ≤
          (∑ k ∈ A.support, ‖A.coeff k‖) *
            Real.exp (-(m / 2) * y ^ 2) := by
        gcongr
  rw [localizedRegularizedLogDerivIntegrandAtCenter, norm_mul]
  calc
    _ ≤
        ((∑ k ∈ A.support, ‖A.coeff k‖) *
          Real.exp (-(m / 2) * y ^ 2)) *
        (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 + 2) := by
      gcongr
      simpa using norm_regularizedLogDeriv_right_vertical_le hu t
    _ = _ := by
      dsimp [y]
      ring

/--
The centered right-edge tails satisfy the center-16 Gaussian bound once the
fixed-`q` threshold is reached.
-/
theorem norm_localizedRightEdgeTailAtCenter_le_gaussian_of_linearHeight
    (q : ℝ) (A : ℂ[X]) {u v m T : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hm : 1 ≤ m)
    (hdegree : (A.natDegree : ℝ) ≤ m)
    (hqScale : q ≤ 27 * m ^ 2)
    (hTlower : 12 * m + |v| ≤ T) :
    ‖localizedRightEdgeTailAtCenter q A
        ((u : ℂ) + I * v) m u T‖ ≤
      localizedRightEdgeGaussianUpperBound A m := by
  let f : ℝ → ℂ := fun t =>
    localizedRegularizedLogDerivIntegrandAtCenter q A
      ((u : ℂ) + I * v) m
      (((u + 2 : ℝ) : ℂ) + (t : ℂ) * I)
  let g : ℝ → ℝ := localizedRightEdgeGaussianMajorant A m v
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  have hbaseHeight : 0 ≤ 12 * m + |v| := by positivity
  have hT : 0 ≤ T := hbaseHeight.trans hTlower
  have hf : Integrable f := by
    exact
      integrable_localizedRegularizedLogDerivIntegrandAtCenter_verticalLine
        q A hu hmPos
  have hg : Integrable g := by
    simpa [g] using
      integrable_localizedRightEdgeGaussianMajorant A hmPos v
  have htailDom :
      ∀ t : ℝ, T ≤ |t| → ‖f t‖ ≤ g t := by
    intro t ht
    have hgap : 12 * m ≤ |t - v| := by
      have hreverse : |t| - |v| ≤ |t - v| :=
        abs_sub_abs_le_abs_sub t v
      linarith [hTlower]
    simpa [f, g, localizedRightEdgeGaussianMajorant, mul_comm] using
      norm_localizedRegularizedLogDerivIntegrandAtCenter_right_le_gaussian
        q A hq hu hm hdegree hqScale hgap
  have hleftDom :
      ∀ t ∈ Set.Iic (-T), ‖f t‖ ≤ g t := by
    intro t ht
    change t ≤ -T at ht
    apply htailDom t
    have ht0 : t ≤ 0 := ht.trans (neg_nonpos.mpr hT)
    rw [abs_of_nonpos ht0]
    linarith [ht]
  have hrightDom :
      ∀ t ∈ Set.Ioi T, ‖f t‖ ≤ g t := by
    intro t ht
    apply htailDom t
    rw [abs_of_pos (hT.trans_lt ht)]
    exact ht.le
  have hleft :
      ‖∫ t : ℝ in Set.Iic (-T), f t‖ ≤
        ∫ t : ℝ in Set.Iic (-T), g t :=
    MeasureTheory.norm_integral_le_of_norm_le
      hg.integrableOn
        (ae_restrict_of_forall_mem measurableSet_Iic hleftDom)
  have hright :
      ‖∫ t : ℝ in Set.Ioi T, f t‖ ≤
        ∫ t : ℝ in Set.Ioi T, g t :=
    MeasureTheory.norm_integral_le_of_norm_le
      hg.integrableOn
        (ae_restrict_of_forall_mem measurableSet_Ioi hrightDom)
  have hsplitG :
      (∫ t : ℝ in Set.Iic (-T), g t) +
          ∫ t : ℝ in Set.Ioi T, g t ≤
        ∫ t : ℝ, g t := by
    have hseries :
        0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hnonneg : ∀ t : ℝ, 0 ≤ g t := by
      intro t
      unfold g localizedRightEdgeGaussianMajorant
      exact mul_nonneg
        (mul_nonneg
          (Finset.sum_nonneg fun k _ => norm_nonneg _)
          (by linarith))
        (Real.exp_pos _).le
    have hmiddle :
        0 ≤ ∫ t : ℝ in (-T)..T, g t :=
      intervalIntegral.integral_nonneg
        (by linarith [hT]) (fun t _ => hnonneg t)
    have hleftAll :=
      intervalIntegral.integral_Iic_add_Ioi
        (f := g) (b := -T)
        hg.integrableOn hg.integrableOn
    have hmiddleRight :
        (∫ t : ℝ in (-T)..T, g t) +
            ∫ t : ℝ in Set.Ioi T, g t =
          ∫ t : ℝ in Set.Ioi (-T), g t :=
      intervalIntegral.integral_interval_add_Ioi
        hg.integrableOn hg.integrableOn
    linarith
  rw [localizedRightEdgeTailAtCenter]
  have hsplitF :=
    integral_sub_symmetric_intervalIntegral hf T
  change ‖(∫ t : ℝ, f t) -
      ∫ t : ℝ in (-T)..T, f t‖ ≤ _
  rw [hsplitF]
  calc
    _ ≤ ‖∫ t : ℝ in Set.Iic (-T), f t‖ +
          ‖∫ t : ℝ in Set.Ioi T, f t‖ :=
      norm_add_le _ _
    _ ≤ (∫ t : ℝ in Set.Iic (-T), g t) +
          ∫ t : ℝ in Set.Ioi T, g t := by
      gcongr
    _ ≤ ∫ t : ℝ, g t := hsplitG
    _ = localizedRightEdgeGaussianUpperBound A m := by
      simpa [g, localizedRightEdgeGaussianUpperBound] using
        integral_localizedRightEdgeGaussianMajorant A hmPos v

set_option maxHeartbeats 2000000 in
/--
At one Révész good height in the unchanged linear interval, the centered
three-edge contribution has the same decaying upper envelope.
-/
theorem
    exists_goodHeight_linearScale_norm_localizedOtherEdgeContributionAtCenter_le :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℝ) (A : ℂ[X]) (u v m : ℝ),
        16 ≤ q → 0 < u → u < 1 → 1 ≤ m →
          q ≤ 27 * m ^ 2 →
          ∃ T ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1),
            ExplicitFormulaAux.goodHeight T ∧
              ‖localizedOtherEdgeContributionAtCenter q A
                  ((u : ℂ) + I * v) m u T‖ ≤
                localizedOtherEdgeUpperBound A u v m C
                  (12 * m + |v|) T := by
  rcases exists_goodHeight_Icc_norm_regularizedLogDeriv_horizontal_le with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro q A u v m hq hu hu1 hm hqScale
  let H : ℝ := 12 * m + |v|
  have hH : 4 ≤ H := by
    dsimp [H]
    nlinarith [abs_nonneg v]
  rcases hchoose H hH with
    ⟨T, hT, hgood, hregularized⟩
  refine ⟨T, by simpa [H] using hT, hgood, ?_⟩
  let bottom : ℂ :=
    ∫ σ : ℝ in (-1)..(u + 2),
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        ((σ : ℂ) + ((-T : ℝ) : ℂ) * I)
  let top : ℂ :=
    ∫ σ : ℝ in (-1)..(u + 2),
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        ((σ : ℂ) + (T : ℂ) * I)
  let left : ℂ :=
    ∫ t : ℝ in (-T)..T,
      localizedRegularizedLogDerivIntegrandAtCenter q A
        ((u : ℂ) + I * v) m
        ((-1 : ℂ) + (t : ℂ) * I)
  let horizontalBound : ℝ :=
    localizedHorizontalEdgeUpperBound A u v m C H T
  let leftBound : ℝ :=
    localizedLeftEdgeUpperBound A u v m T
  have hTnonneg : 0 ≤ T := by linarith [hH, hT.1]
  have hTabs : |T| = T := abs_of_nonneg hTnonneg
  have hnegTabs : |-T| = T := by rw [abs_neg, hTabs]
  have hbottom : ‖bottom‖ ≤ horizontalBound := by
    simpa [
      bottom, horizontalBound, mul_comm] using
        norm_integral_regularizedLogDeriv_localizedGaussianWeightAtCenter_horizontal_le
          q A hq hu hu1 hm hqScale hT.1 hnegTabs
          (fun σ hσlo hσhi =>
            hregularized u hu hu1 (-T) hnegTabs σ hσlo hσhi)
  have htop : ‖top‖ ≤ horizontalBound := by
    simpa [
      top, horizontalBound, mul_comm] using
        norm_integral_regularizedLogDeriv_localizedGaussianWeightAtCenter_horizontal_le
          q A hq hu hu1 hm hqScale hT.1 hTabs
          (fun σ hσlo hσhi =>
            hregularized u hu hu1 T hTabs σ hσlo hσhi)
  have hleft : ‖left‖ ≤ leftBound := by
    unfold leftBound
    simpa [left, mul_comm] using
      norm_integral_regularizedLogDeriv_localizedGaussianWeightAtCenter_left_le
        q A hq hu hu1 hTnonneg (zero_le_one.trans hm)
  change ‖I * (bottom - top) + left‖ ≤
    2 * horizontalBound + leftBound
  calc
    _ ≤ ‖I * (bottom - top)‖ + ‖left‖ := norm_add_le _ _
    _ = ‖bottom - top‖ + ‖left‖ := by
      rw [norm_mul, norm_I, one_mul]
    _ ≤ (‖bottom‖ + ‖top‖) + ‖left‖ := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ 2 * horizontalBound + leftBound := by linarith

set_option maxHeartbeats 2000000 in
/--
The selected centered contour identity and quantitative remainder bound can
be installed simultaneously at the same good height.
-/
theorem
    exists_goodHeight_linearScale_localizedPsiGaussianAverageAtCenter_eq_zeroSum :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : ℝ) (A : ℂ[X]) (u v m : ℝ),
        16 ≤ q → 0 < u → u < 1 → 1 ≤ m →
          (A.natDegree : ℝ) ≤ m → q ≤ 27 * m ^ 2 →
          ∃ T ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1),
            ExplicitFormulaAux.goodHeight T ∧
              ∃ zeros : Finset ℂ,
                (∀ rho ∈ zeros,
                  riemannZeta rho = 0 ∧
                    (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
                    -T < rho.im ∧ rho.im < T) ∧
                (∀ rho ∈
                    ([[(-1 : ℝ), u + 2]] ×ℂ [[-T, T]] : Set ℂ),
                  riemannZeta rho = 0 → rho ∈ zeros) ∧
                localizedPsiGaussianAverageAtCenter q A
                    ((u : ℂ) + I * v) m =
                  -(2 * Real.pi : ℂ) *
                      localizedZeroResidueSumAtCenter q A
                        ((u : ℂ) + I * v) m zeros +
                    localizedContourRemainderAtCenter q A
                      ((u : ℂ) + I * v) m u T ∧
                ‖localizedContourRemainderAtCenter q A
                    ((u : ℂ) + I * v) m u T‖ ≤
                  localizedOtherEdgeUpperBound A u v m C
                      (12 * m + |v|) T +
                    localizedRightEdgeGaussianUpperBound A m := by
  rcases
      exists_goodHeight_linearScale_norm_localizedOtherEdgeContributionAtCenter_le
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro q A u v m hq hu hu1 hm hdegree hqScale
  rcases hchoose q A u v m hq hu hu1 hm hqScale with
    ⟨T, hT, hgood, hother⟩
  have hmPos : 0 < m := zero_lt_one.trans_le hm
  have hTPos : 0 < T := by
    have hbase : 0 < 12 * m + |v| := by positivity
    exact hbase.trans_le hT.1
  rcases
      exists_localizedPsiGaussianAverageAtCenter_eq_zeroSum_add_contourRemainder_of_goodHeight
        q A hu hmPos hTPos hgood with
    ⟨zeros, hzeros, hcomplete, heq⟩
  have htail :=
    norm_localizedRightEdgeTailAtCenter_le_gaussian_of_linearHeight
      q A hq hu hm hdegree hqScale hT.1
  refine ⟨T, hT, hgood, zeros, hzeros, hcomplete, heq, ?_⟩
  rw [localizedContourRemainderAtCenter]
  exact (norm_add_le _ _).trans (add_le_add hother htail)

/-- The fixed good-height constant for centered contour selection. -/
def centeredLocalizedContourGoodHeightConstant : ℝ :=
  Classical.choose
    exists_goodHeight_linearScale_localizedPsiGaussianAverageAtCenter_eq_zeroSum

theorem centeredLocalizedContourGoodHeightConstant_nonneg :
    0 ≤ centeredLocalizedContourGoodHeightConstant :=
  (Classical.choose_spec
    exists_goodHeight_linearScale_localizedPsiGaussianAverageAtCenter_eq_zeroSum).1

/-- One exact centered finite-height zeta contour slice. -/
structure CenteredConcreteLocalizedContourSlice
    (q : ℝ) (A : ℂ[X]) (u v m : ℝ) where
  height : ℝ
  height_mem :
    height ∈ Set.Icc (12 * m + |v|) (12 * m + |v| + 1)
  goodHeight : ExplicitFormulaAux.goodHeight height
  zeros : Finset ℂ
  zeros_spec :
    ∀ rho ∈ zeros,
      riemannZeta rho = 0 ∧
        (-1 : ℝ) < rho.re ∧ rho.re < u + 2 ∧
        -height < rho.im ∧ rho.im < height
  zeros_complete :
    ∀ rho ∈
        ([[(-1 : ℝ), u + 2]] ×ℂ [[-height, height]] : Set ℂ),
      riemannZeta rho = 0 → rho ∈ zeros
  contour_eq :
    localizedPsiGaussianAverageAtCenter q A
        ((u : ℂ) + I * v) m =
      -(2 * Real.pi : ℂ) *
          localizedZeroResidueSumAtCenter q A
            ((u : ℂ) + I * v) m zeros +
        localizedContourRemainderAtCenter q A
          ((u : ℂ) + I * v) m u height
  remainder_bound :
    ‖localizedContourRemainderAtCenter q A
        ((u : ℂ) + I * v) m u height‖ ≤
      localizedOtherEdgeUpperBound A u v m
          centeredLocalizedContourGoodHeightConstant
          (12 * m + |v|) height +
        localizedRightEdgeGaussianUpperBound A m

/-- The genuine fixed-`q` scale hypotheses used by centered selection. -/
def centeredLocalizedContourScaleValid
    (q : ℝ) (A : ℂ[X]) (u m : ℝ) : Prop :=
  16 ≤ q ∧ 0 < u ∧ u < 1 ∧ 1 ≤ m ∧
    (A.natDegree : ℝ) ≤ m ∧ q ≤ 27 * m ^ 2

theorem exists_centeredConcreteLocalizedContourSlice
    (q : ℝ) (A : ℂ[X]) {u v m : ℝ}
    (hvalid : centeredLocalizedContourScaleValid q A u m) :
    Nonempty (CenteredConcreteLocalizedContourSlice q A u v m) := by
  have hspec :=
    (Classical.choose_spec
      exists_goodHeight_linearScale_localizedPsiGaussianAverageAtCenter_eq_zeroSum).2
  rcases hspec q A u v m hvalid.1 hvalid.2.1 hvalid.2.2.1
      hvalid.2.2.2.1 hvalid.2.2.2.2.1 hvalid.2.2.2.2.2 with
    ⟨T, hT, hgood, zeros, hzeros, hcomplete, heq, hbound⟩
  exact ⟨{
    height := T
    height_mem := hT
    goodHeight := hgood
    zeros := zeros
    zeros_spec := hzeros
    zeros_complete := hcomplete
    contour_eq := heq
    remainder_bound := hbound
  }⟩

noncomputable def selectedCenteredConcreteLocalizedContourSlice
    (q : ℝ) (A : ℂ[X]) (u v m : ℝ)
    (hvalid : centeredLocalizedContourScaleValid q A u m) :
    CenteredConcreteLocalizedContourSlice q A u v m :=
  Classical.choice
    (exists_centeredConcreteLocalizedContourSlice q A hvalid)

/-- The selected centered remainder, zero before its fixed-`q` regime. -/
noncomputable def selectedLocalizedContourRemainderAtCenter
    (q : ℝ) (A : ℂ[X]) (u v m : ℝ) : ℂ := by
  classical
  exact
    if hvalid : centeredLocalizedContourScaleValid q A u m then
      localizedContourRemainderAtCenter q A
        ((u : ℂ) + I * v) m u
        (selectedCenteredConcreteLocalizedContourSlice
          q A u v m hvalid).height
    else 0

/-- The zero sum selected in the same centered contour slice. -/
noncomputable def selectedLocalizedZeroResidueSumAtCenter
    (q : ℝ) (A : ℂ[X]) (u v m : ℝ) : ℂ := by
  classical
  exact
    if hvalid : centeredLocalizedContourScaleValid q A u m then
      localizedZeroResidueSumAtCenter q A
        ((u : ℂ) + I * v) m
        (selectedCenteredConcreteLocalizedContourSlice
          q A u v m hvalid).zeros
    else 0

theorem selected_localizedPsiGaussianAverageAtCenter_eq
    (q : ℝ) (A : ℂ[X]) {u v m : ℝ}
    (hvalid : centeredLocalizedContourScaleValid q A u m) :
    localizedPsiGaussianAverageAtCenter q A
        ((u : ℂ) + I * v) m =
      -(2 * Real.pi : ℂ) *
          selectedLocalizedZeroResidueSumAtCenter q A u v m +
        selectedLocalizedContourRemainderAtCenter q A u v m := by
  rw [selectedLocalizedZeroResidueSumAtCenter, dif_pos hvalid]
  rw [selectedLocalizedContourRemainderAtCenter, dif_pos hvalid]
  exact
    (selectedCenteredConcreteLocalizedContourSlice
      q A u v m hvalid).contour_eq

/-- The unchanged linear height eventually exceeds every fixed radius. -/
theorem eventually_centeredPoleRadius_le_linearHeight
    (q v : ℝ) :
    ∀ᶠ m : ℝ in atTop,
      centeredPoleRadius q ≤ 12 * m + |v| := by
  filter_upwards [
    eventually_ge_atTop ((centeredPoleRadius q - |v|) / 12)] with m hm
  linarith

/-- The selected centered true-zeta remainder tends to zero for fixed `q`. -/
theorem tendsto_selectedLocalizedContourRemainderAtCenter
    (q : ℝ) (A : ℂ[X]) {u : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1) (v : ℝ) :
    Tendsto
      (selectedLocalizedContourRemainderAtCenter q A u v)
      atTop (𝓝 0) := by
  let otherUpper : ℝ → ℝ := fun m =>
    localizedOtherEdgeDecayConstant A u v
        centeredLocalizedContourGoodHeightConstant *
      m ^ (A.natDegree + 2) * Real.exp (-15 * m)
  let rightUpper : ℝ → ℝ :=
    localizedRightEdgeGaussianUpperBound A
  let upper : ℝ → ℝ := fun m => otherUpper m + rightUpper m
  have hother : Tendsto otherUpper atTop (𝓝 0) := by
    simpa [otherUpper] using
      tendsto_localizedOtherEdgeDecayEnvelope A u v
        centeredLocalizedContourGoodHeightConstant
  have hright : Tendsto rightUpper atTop (𝓝 0) := by
    simpa [rightUpper] using
      tendsto_localizedRightEdgeGaussianUpperBound A
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hother.add hright
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖selectedLocalizedContourRemainderAtCenter q A u v m‖ ≤
          upper m := by
    filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (A.natDegree : ℝ),
      eventually_ge_atTop q] with m hm hdegree hmq
    have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
    have hqScale : q ≤ 27 * m ^ 2 := by
      have hm0 : 0 ≤ m := zero_le_one.trans hm
      nlinarith [mul_nonneg hqPos.le (sub_nonneg.mpr hmq)]
    have hvalid : centeredLocalizedContourScaleValid q A u m :=
      ⟨hq, hu, hu1, hm, hdegree, hqScale⟩
    let slice :=
      selectedCenteredConcreteLocalizedContourSlice q A u v m hvalid
    have hotherBound :=
      localizedOtherEdgeUpperBound_le_decayEnvelope
        A hu hu1 centeredLocalizedContourGoodHeightConstant_nonneg
          hm slice.height_mem
    have hslicebound := slice.remainder_bound
    rw [selectedLocalizedContourRemainderAtCenter, dif_pos hvalid]
    change
      ‖localizedContourRemainderAtCenter q A
          ((u : ℂ) + I * v) m u slice.height‖ ≤ upper m
    calc
      _ ≤ localizedOtherEdgeUpperBound A u v m
              centeredLocalizedContourGoodHeightConstant
              (12 * m + |v|) slice.height +
            localizedRightEdgeGaussianUpperBound A m :=
        hslicebound
      _ ≤ otherUpper m + rightUpper m := by
        gcongr
      _ = upper m := rfl
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    hbound hupper

/-- The centered near-zero filter annihilates every listed nonzero offset. -/
theorem localizedGaussianWeightAtCenter_nearZeroFilter_eq_zero
    (q : ℝ) {w rho : ℂ} {B m : ℝ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hrhoNe : rho ≠ w) (him : |rho.im - w.im| ≤ B) :
    localizedGaussianWeightAtCenter q
        (localizedNearZeroFilter w B) w m rho = 0 := by
  unfold localizedGaussianWeightAtCenter localizedNearZeroFilter
  rw [targetPreservingPoleFilter_eval_eq_zero
    (mem_localizedNearZeroOffsets_of_isNontrivialZero hrho him)
    (sub_ne_zero.mpr hrhoNe)]
  simp

/-- The part of a centered zero sum outside its fixed radius. -/
def localizedFarZeroResidueSumAtCenter
    (q : ℝ) (A : ℂ[X]) (w : ℂ) (m : ℝ)
    (zeros : Finset ℂ) : ℂ :=
  ∑ rho ∈ zeros.filter
      (fun rho => centeredPoleRadius q < |rho.im - w.im|),
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      localizedGaussianWeightAtCenter q A w m rho

theorem CenteredConcreteLocalizedContourSlice.isNontrivialZero_of_mem
    {q : ℝ} {A : ℂ[X]} {u v m : ℝ}
    (slice : CenteredConcreteLocalizedContourSlice q A u v m)
    {rho : ℂ} (hrho : rho ∈ slice.zeros) :
    RiemannHypothesis.IsNontrivialZero rho := by
  rcases slice.zeros_spec rho hrho with
    ⟨hzero, hreLower, _hreUpper, _himLower, _himUpper⟩
  have hrePos : 0 < rho.re := by
    by_contra hnot
    apply PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero
      (le_of_not_gt hnot)
    · intro n hrhoEq
      have hreEq := congrArg Complex.re hrhoEq
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      simp at hreEq
      linarith
    · exact hzero
  have hreLt : rho.re < 1 := by
    by_contra hnot
    exact (riemannZeta_ne_zero_of_one_le_re
      (le_of_not_gt hnot)) hzero
  exact ⟨hzero, hrePos, hreLt⟩

theorem CenteredConcreteLocalizedContourSlice.center_mem
    {q : ℝ} {A : ℂ[X]} {u v m : ℝ}
    (slice : CenteredConcreteLocalizedContourSlice q A u v m)
    (hu : 0 < u) (hm : 0 < m)
    (hzero : riemannZeta ((u : ℂ) + I * v) = 0) :
    ((u : ℂ) + I * v) ∈ slice.zeros := by
  apply slice.zeros_complete ((u : ℂ) + I * v)
  · have hT : |v| < slice.height := by
      have hlower := slice.height_mem.1
      linarith
    have hvLower : -slice.height ≤ v := by
      linarith [neg_abs_le v]
    have hvUpper : v ≤ slice.height :=
      (le_abs_self v).trans hT.le
    rw [Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith [hu] : (-1 : ℝ) ≤ u + 2),
      Set.uIcc_of_le (by linarith [abs_nonneg v] :
        -slice.height ≤ slice.height)]
    simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im,
      I_im, zero_mul, one_mul, add_im, mul_im]
    constructor
    · constructor <;> linarith
    · exact ⟨by simpa using hvLower, by simpa using hvUpper⟩
  · exact hzero

private theorem
    localizedZeroResidueSumAtCenter_nearZeroFilter_eq_target_add_far
    {q : ℝ} {zeros : Finset ℂ} {w : ℂ} {m : ℝ}
    (hq : 0 < q) (hw : w ∈ zeros)
    (hzeros :
      ∀ rho ∈ zeros, RiemannHypothesis.IsNontrivialZero rho) :
    localizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter w (centeredPoleRadius q))
        w m zeros =
      (analyticOrderNatAt riemannZeta w : ℂ) +
        localizedFarZeroResidueSumAtCenter q
          (localizedNearZeroFilter w (centeredPoleRadius q))
          w m zeros := by
  let A : ℂ[X] :=
    localizedNearZeroFilter w (centeredPoleRadius q)
  let f : ℂ → ℂ := fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      localizedGaussianWeightAtCenter q A w m rho
  have htarget :
      f w = (analyticOrderNatAt riemannZeta w : ℂ) := by
    dsimp [f, A]
    unfold localizedGaussianWeightAtCenter
    rw [sub_self, localizedNearZeroFilter_eval_zero]
    norm_num
  have herase :
      (∑ rho ∈ zeros.erase w, f rho) =
        ∑ rho ∈ zeros.filter
          (fun rho =>
            centeredPoleRadius q < |rho.im - w.im|), f rho := by
    calc
      (∑ rho ∈ zeros.erase w, f rho) =
          ∑ rho ∈ zeros.erase w,
            if centeredPoleRadius q < |rho.im - w.im|
              then f rho else 0 := by
        apply Finset.sum_congr rfl
        intro rho hrho
        by_cases hfar :
            centeredPoleRadius q < |rho.im - w.im|
        · simp [hfar]
        · have hrhoZeros : rho ∈ zeros :=
            (Finset.mem_erase.mp hrho).2
          have hrhoNe : rho ≠ w :=
            (Finset.mem_erase.mp hrho).1
          have hnear :
              |rho.im - w.im| ≤ centeredPoleRadius q :=
            le_of_not_gt hfar
          rw [if_neg hfar]
          dsimp [f, A]
          rw [localizedGaussianWeightAtCenter_nearZeroFilter_eq_zero
            q (hzeros rho hrhoZeros) hrhoNe hnear]
          simp
      _ = ∑ rho ∈
          (zeros.erase w).filter
            (fun rho =>
              centeredPoleRadius q < |rho.im - w.im|), f rho := by
        rw [Finset.sum_filter]
      _ = ∑ rho ∈ zeros.filter
          (fun rho =>
            centeredPoleRadius q < |rho.im - w.im|), f rho := by
        congr 1
        ext rho
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨⟨_hrhoNe, hrho⟩, hfar⟩
          exact ⟨hrho, hfar⟩
        · rintro ⟨hrho, hfar⟩
          refine ⟨⟨?_, hrho⟩, hfar⟩
          intro hrhoEq
          subst rho
          simp at hfar
          unfold centeredPoleRadius at hfar
          linarith
  unfold localizedZeroResidueSumAtCenter
    localizedFarZeroResidueSumAtCenter
  change (∑ rho ∈ zeros, f rho) =
    (analyticOrderNatAt riemannZeta w : ℂ) +
      ∑ rho ∈ zeros.filter
        (fun rho =>
          centeredPoleRadius q < |rho.im - w.im|), f rho
  rw [← Finset.sum_erase_add _ _ hw, herase, htarget]
  ring

private theorem
    localizedZeroResidueSumAtCenter_nearZeroFilter_eq_far_of_not_mem
    {q : ℝ} {zeros : Finset ℂ} {w : ℂ} {m : ℝ}
    (hw : w ∉ zeros)
    (hzeros :
      ∀ rho ∈ zeros, RiemannHypothesis.IsNontrivialZero rho) :
    localizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter w (centeredPoleRadius q))
        w m zeros =
      localizedFarZeroResidueSumAtCenter q
        (localizedNearZeroFilter w (centeredPoleRadius q))
        w m zeros := by
  let A : ℂ[X] :=
    localizedNearZeroFilter w (centeredPoleRadius q)
  let f : ℂ → ℂ := fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      localizedGaussianWeightAtCenter q A w m rho
  unfold localizedZeroResidueSumAtCenter
    localizedFarZeroResidueSumAtCenter
  change (∑ rho ∈ zeros, f rho) =
    ∑ rho ∈ zeros.filter
      (fun rho =>
        centeredPoleRadius q < |rho.im - w.im|), f rho
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hfar :
      centeredPoleRadius q < |rho.im - w.im|
  · simp [hfar]
  · rw [if_neg hfar]
    have hrhoNe : rho ≠ w := by
      intro heq
      subst rho
      exact hw hrho
    have hnear :
        |rho.im - w.im| ≤ centeredPoleRadius q :=
      le_of_not_gt hfar
    dsimp [f, A]
    rw [localizedGaussianWeightAtCenter_nearZeroFilter_eq_zero
      q (hzeros rho hrho) hrhoNe hnear]
    simp

/-- The selected far-zero term uses exactly `centeredPoleRadius q`. -/
noncomputable def selectedLocalizedFarZeroResidueSumAtCenter
    (q u v m : ℝ) : ℂ := by
  classical
  let w : ℂ := (u : ℂ) + I * v
  let A : ℂ[X] :=
    localizedNearZeroFilter w (centeredPoleRadius q)
  exact
    if hvalid : centeredLocalizedContourScaleValid q A u m then
      localizedFarZeroResidueSumAtCenter q A w m
        (selectedCenteredConcreteLocalizedContourSlice
          q A u v m hvalid).zeros
    else 0

theorem
    selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_eq_target_add_far
    {q u v m : ℝ}
    (hvalid :
      centeredLocalizedContourScaleValid q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u m)
    (hzero : riemannZeta ((u : ℂ) + I * v) = 0) :
    selectedLocalizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u v m =
      (analyticOrderNatAt riemannZeta
          ((u : ℂ) + I * v) : ℂ) +
        selectedLocalizedFarZeroResidueSumAtCenter q u v m := by
  let w : ℂ := (u : ℂ) + I * v
  let A : ℂ[X] :=
    localizedNearZeroFilter w (centeredPoleRadius q)
  let slice : CenteredConcreteLocalizedContourSlice q A u v m :=
    selectedCenteredConcreteLocalizedContourSlice q A u v m hvalid
  rw [selectedLocalizedZeroResidueSumAtCenter, dif_pos hvalid]
  rw [selectedLocalizedFarZeroResidueSumAtCenter, dif_pos hvalid]
  change localizedZeroResidueSumAtCenter q A w m slice.zeros =
    (analyticOrderNatAt riemannZeta w : ℂ) +
      localizedFarZeroResidueSumAtCenter q A w m slice.zeros
  apply localizedZeroResidueSumAtCenter_nearZeroFilter_eq_target_add_far
    (lt_of_lt_of_le (by norm_num) hvalid.1)
  · exact slice.center_mem hvalid.2.1
      (lt_of_lt_of_le zero_lt_one hvalid.2.2.2.1) hzero
  · intro rho hrho
    exact slice.isNontrivialZero_of_mem hrho

theorem
    selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_eq_far_of_ne_zero
    {q u v m : ℝ}
    (hvalid :
      centeredLocalizedContourScaleValid q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u m)
    (hne : riemannZeta ((u : ℂ) + I * v) ≠ 0) :
    selectedLocalizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u v m =
      selectedLocalizedFarZeroResidueSumAtCenter q u v m := by
  let w : ℂ := (u : ℂ) + I * v
  let A : ℂ[X] :=
    localizedNearZeroFilter w (centeredPoleRadius q)
  let slice : CenteredConcreteLocalizedContourSlice q A u v m :=
    selectedCenteredConcreteLocalizedContourSlice q A u v m hvalid
  rw [selectedLocalizedZeroResidueSumAtCenter, dif_pos hvalid]
  rw [selectedLocalizedFarZeroResidueSumAtCenter, dif_pos hvalid]
  change localizedZeroResidueSumAtCenter q A w m slice.zeros =
    localizedFarZeroResidueSumAtCenter q A w m slice.zeros
  apply localizedZeroResidueSumAtCenter_nearZeroFilter_eq_far_of_not_mem
  · intro hwmem
    exact hne (slice.zeros_spec w hwmem).1
  · intro rho hrho
    exact slice.isNontrivialZero_of_mem hrho

/--
Outside `centeredPoleRadius q`, every centered nontrivial-zero weight gains
the uniform factor `exp (-8*m)`.
-/
theorem norm_localizedGaussianWeightAtCenter_far_le
    (q : ℝ) (A : ℂ[X]) {u v m : ℝ} {rho : ℂ}
    (hq : 0 < q) (hu : 0 < u) (hu1 : u < 1) (hm : 0 ≤ m)
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (hfar : centeredPoleRadius q ≤ |rho.im - v|) :
    ‖localizedGaussianWeightAtCenter q A
        ((u : ℂ) + I * v) m rho‖ ≤
      ‖A.eval (rho - ((u : ℂ) + I * v))‖ *
        Real.exp (-8 * m) := by
  rw [norm_localizedGaussianWeightAtCenter]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Real.exp_le_exp]
  let a : ℝ := rho.re - u
  have ha : |a| ≤ 1 := by
    rw [abs_le]
    constructor <;> dsimp [a] <;> linarith [hrho.2.1, hrho.2.2]
  have hmargin :=
    real_sq_add_q_mul_sub_centeredPoleRadius_sq_le hq ha
  have hBnonneg : 0 ≤ centeredPoleRadius q := by
    unfold centeredPoleRadius
    linarith
  have himSq :
      centeredPoleRadius q ^ 2 ≤ (rho.im - v) ^ 2 := by
    have habsSq :=
      pow_le_pow_left₀ hBnonneg hfar 2
    simpa [sq_abs] using habsSq
  have hcore :
      a ^ 2 - (rho.im - v) ^ 2 + q * a ≤ -8 := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hcore hm
  norm_num [a, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im] at hmul ⊢
  simpa [mul_comm] using hmul

theorem
    CenteredConcreteLocalizedContourSlice.mem_nontrivialZerosFinset_linearHeight
    {q : ℝ} {A : ℂ[X]} {u v m : ℝ}
    (slice : CenteredConcreteLocalizedContourSlice q A u v m)
    {rho : ℂ} (hrho : rho ∈ slice.zeros) :
    rho ∈ nontrivialZerosFinset (12 * m + |v| + 1) := by
  have hzero := slice.isNontrivialZero_of_mem hrho
  have himLower := (slice.zeros_spec rho hrho).2.2.2.1
  have himUpper := (slice.zeros_spec rho hrho).2.2.2.2
  apply mem_nontrivialZerosFinset.mpr
  refine ⟨hzero, ?_⟩
  have hT := slice.height_mem.2
  rw [abs_le]
  constructor <;> linarith

/--
The centered far-zero sum is bounded by the global multiplicity count and
one common polynomial-Gaussian envelope.
-/
theorem
    norm_localizedFarZeroResidueSumAtCenter_le_globalMultiplicity
    (q : ℝ) (A : ℂ[X]) {u v m : ℝ}
    (slice : CenteredConcreteLocalizedContourSlice q A u v m)
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1) (hm : 1 ≤ m) :
    ‖localizedFarZeroResidueSumAtCenter q A
        ((u : ℂ) + I * v) m slice.zeros‖ ≤
      ExplicitFormulaAux.globalZeroMultiplicity
          (12 * m + |v| + 1) *
        ((∑ k ∈ A.support, ‖A.coeff k‖) *
          (localizedFarZeroLinearCoefficient v * m) ^ A.natDegree *
          Real.exp (-8 * m)) := by
  let H : ℝ := 12 * m + |v| + 1
  let K : ℝ := localizedFarZeroLinearCoefficient v
  let S : ℝ := ∑ k ∈ A.support, ‖A.coeff k‖
  let farZeros : Finset ℂ :=
    slice.zeros.filter
      (fun rho =>
        centeredPoleRadius q <
          |rho.im - (((u : ℂ) + I * v).im)|)
  let common : ℝ :=
    S * (K * m) ^ A.natDegree * Real.exp (-8 * m)
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hK : 0 < K := localizedFarZeroLinearCoefficient_pos v
  have hKm : 1 ≤ K * m := by
    dsimp [K, localizedFarZeroLinearCoefficient]
    nlinarith [abs_nonneg v]
  have hcommon : 0 ≤ common := by
    dsimp [common, S]
    positivity
  have hsubset :
      farZeros ⊆ nontrivialZerosFinset H := by
    intro rho hrho
    have hrhoZeros := (Finset.mem_filter.mp hrho).1
    dsimp [H]
    exact slice.mem_nontrivialZerosFinset_linearHeight hrhoZeros
  have hmult :
      (∑ rho ∈ farZeros,
          (analyticOrderNatAt riemannZeta rho : ℝ)) ≤
        ExplicitFormulaAux.globalZeroMultiplicity H := by
    unfold ExplicitFormulaAux.globalZeroMultiplicity
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun rho _hrho _hnot => Nat.cast_nonneg _)
  have hterm (rho : ℂ) (hrho : rho ∈ farZeros) :
      ‖(analyticOrderNatAt riemannZeta rho : ℂ) *
          localizedGaussianWeightAtCenter q A
            ((u : ℂ) + I * v) m rho‖ ≤
        (analyticOrderNatAt riemannZeta rho : ℝ) * common := by
    have hrhoZeros := (Finset.mem_filter.mp hrho).1
    have hfar := (Finset.mem_filter.mp hrho).2
    have hrhoNT := slice.isNontrivialZero_of_mem hrhoZeros
    have hrhoH :=
      mem_nontrivialZerosFinset.mp
        (slice.mem_nontrivialZerosFinset_linearHeight hrhoZeros)
    have hcenter :
        ‖rho - ((u : ℂ) + I * v)‖ ≤ K * m := by
      dsimp [K]
      exact norm_sub_center_le_linearHeight
        hu hu1 hm hrhoNT hrhoH.2
    have hpoly :
        ‖A.eval (rho - ((u : ℂ) + I * v))‖ ≤
          S * (K * m) ^ A.natDegree := by
      calc
        _ ≤ S * max 1 ‖rho - ((u : ℂ) + I * v)‖ ^
              A.natDegree := by
          dsimp [S]
          exact norm_polynomial_eval_le_coeffL1_mul_max_pow A _
        _ ≤ S * (K * m) ^ A.natDegree := by
          gcongr
          rw [max_le_iff]
          exact ⟨hKm, hcenter⟩
    have hweight :
        ‖localizedGaussianWeightAtCenter q A
            ((u : ℂ) + I * v) m rho‖ ≤ common := by
      calc
        _ ≤ ‖A.eval (rho - ((u : ℂ) + I * v))‖ *
              Real.exp (-8 * m) :=
          norm_localizedGaussianWeightAtCenter_far_le
            q A hqPos hu hu1 (zero_le_one.trans hm) hrhoNT
              (by simpa using hfar.le)
        _ ≤ common := by
          dsimp [common]
          gcongr
    rw [norm_mul]
    simpa using
      mul_le_mul_of_nonneg_left hweight
        (show 0 ≤
          (analyticOrderNatAt riemannZeta rho : ℝ) by positivity)
  unfold localizedFarZeroResidueSumAtCenter
  change ‖∑ rho ∈ farZeros,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        localizedGaussianWeightAtCenter q A
          ((u : ℂ) + I * v) m rho‖ ≤ _
  change _ ≤ ExplicitFormulaAux.globalZeroMultiplicity H * common
  calc
    _ ≤ ∑ rho ∈ farZeros,
        ‖(analyticOrderNatAt riemannZeta rho : ℂ) *
          localizedGaussianWeightAtCenter q A
            ((u : ℂ) + I * v) m rho‖ :=
      norm_sum_le _ _
    _ ≤ ∑ rho ∈ farZeros,
        (analyticOrderNatAt riemannZeta rho : ℝ) * common :=
      Finset.sum_le_sum hterm
    _ = (∑ rho ∈ farZeros,
          (analyticOrderNatAt riemannZeta rho : ℝ)) * common := by
      rw [Finset.sum_mul]
    _ ≤ ExplicitFormulaAux.globalZeroMultiplicity H * common :=
      mul_le_mul_of_nonneg_right hmult hcommon

/-- Global-zero-count specialization of the centered far-zero bound. -/
theorem norm_localizedFarZeroResidueSumAtCenter_le_decayEnvelope
    (q : ℝ) (A : ℂ[X]) {u v m C : ℝ}
    (slice : CenteredConcreteLocalizedContourSlice q A u v m)
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hm : 1 ≤ m) (hC : 0 ≤ C)
    (hcount :
      ExplicitFormulaAux.globalZeroMultiplicity
          (12 * m + |v| + 1) ≤
        C * (12 * m + |v| + 1) *
          (1 + Real.log (12 * m + |v| + 1 + 6))) :
    ‖localizedFarZeroResidueSumAtCenter q A
        ((u : ℂ) + I * v) m slice.zeros‖ ≤
      localizedFarZeroDecayConstant A v C *
        m ^ (A.natDegree + 2) * Real.exp (-8 * m) := by
  let H : ℝ := 12 * m + |v| + 1
  let K : ℝ := localizedFarZeroLinearCoefficient v
  let S : ℝ := ∑ k ∈ A.support, ‖A.coeff k‖
  have hK : 0 < K := localizedFarZeroLinearCoefficient_pos v
  have hKm : 1 ≤ K * m := by
    dsimp [K, localizedFarZeroLinearCoefficient]
    nlinarith [abs_nonneg v]
  have hH : H ≤ K * m := by
    dsimp [H, K, localizedFarZeroLinearCoefficient]
    nlinarith [mul_nonneg (abs_nonneg v)
      (zero_le_one.trans hm)]
  have hHsix : H + 6 ≤ K * m := by
    dsimp [H, K, localizedFarZeroLinearCoefficient]
    nlinarith [mul_nonneg (abs_nonneg v)
      (zero_le_one.trans hm)]
  have hlogNonneg : 0 ≤ Real.log (H + 6) := by
    apply Real.log_nonneg
    dsimp [H]
    nlinarith [abs_nonneg v]
  have hlog : Real.log (H + 6) ≤ K * m :=
    (show Real.log (H + 6) ≤ H + 6 by
      exact Real.log_le_sub_one_of_pos
        (by dsimp [H]; nlinarith [abs_nonneg v]) |>.trans
          (by linarith)).trans hHsix
  have hcountEnvelope :
      ExplicitFormulaAux.globalZeroMultiplicity H ≤
        2 * C * (K * m) ^ 2 := by
    calc
      _ ≤ C * H * (1 + Real.log (H + 6)) := by
        simpa [H, add_assoc] using hcount
      _ ≤ C * (K * m) * (2 * (K * m)) := by
        gcongr
        nlinarith
      _ = 2 * C * (K * m) ^ 2 := by ring
  have hbase :=
    norm_localizedFarZeroResidueSumAtCenter_le_globalMultiplicity
      q A slice hq hu hu1 hm
  calc
    _ ≤ ExplicitFormulaAux.globalZeroMultiplicity H *
        (S * (K * m) ^ A.natDegree *
          Real.exp (-8 * m)) := by
      simpa [H, K, S] using hbase
    _ ≤ (2 * C * (K * m) ^ 2) *
        (S * (K * m) ^ A.natDegree *
          Real.exp (-8 * m)) := by
      gcongr
    _ = localizedFarZeroDecayConstant A v C *
          m ^ (A.natDegree + 2) * Real.exp (-8 * m) := by
      unfold localizedFarZeroDecayConstant
      dsimp [K, S]
      rw [mul_pow]
      ring

/-- The selected centered far-zero sum tends to zero for fixed `q ≥ 16`. -/
theorem tendsto_selectedLocalizedFarZeroResidueSumAtCenter
    (q : ℝ) {u v : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1) :
    Tendsto
      (selectedLocalizedFarZeroResidueSumAtCenter q u v)
      atTop (𝓝 0) := by
  let w : ℂ := (u : ℂ) + I * v
  let A : ℂ[X] :=
    localizedNearZeroFilter w (centeredPoleRadius q)
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hcount⟩
  let upper : ℝ → ℝ := fun m =>
    localizedFarZeroDecayConstant A v C *
      m ^ (A.natDegree + 2) * Real.exp (-8 * m)
  have hupper : Tendsto upper atTop (𝓝 0) :=
    tendsto_localizedFarZeroDecayEnvelope A v C
  have hbound :
      ∀ᶠ m : ℝ in atTop,
        ‖selectedLocalizedFarZeroResidueSumAtCenter q u v m‖ ≤
          upper m := by
    filter_upwards [
      eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (A.natDegree : ℝ),
      eventually_ge_atTop q] with m hm hdegree hmq
    have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
    have hqScale : q ≤ 27 * m ^ 2 := by
      have hm0 : 0 ≤ m := zero_le_one.trans hm
      nlinarith [mul_nonneg hqPos.le (sub_nonneg.mpr hmq)]
    have hvalid : centeredLocalizedContourScaleValid q A u m :=
      ⟨hq, hu, hu1, hm, hdegree, hqScale⟩
    let slice : CenteredConcreteLocalizedContourSlice q A u v m :=
      selectedCenteredConcreteLocalizedContourSlice q A u v m hvalid
    rw [selectedLocalizedFarZeroResidueSumAtCenter, dif_pos hvalid]
    change
      ‖localizedFarZeroResidueSumAtCenter q A
          w m slice.zeros‖ ≤ upper m
    apply norm_localizedFarZeroResidueSumAtCenter_le_decayEnvelope
      q A slice hq hu hu1 hm hC
    apply hcount
    nlinarith [abs_nonneg v]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _)
    hbound hupper

/-- The filtered centered zero sum converges to the target multiplicity. -/
theorem
    tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter
    (q : ℝ) {u v : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hzero : riemannZeta ((u : ℂ) + I * v) = 0) :
    Tendsto
      (selectedLocalizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u v)
      atTop
      (𝓝 (analyticOrderNatAt riemannZeta
        ((u : ℂ) + I * v) : ℂ)) := by
  let A : ℂ[X] :=
    localizedNearZeroFilter
      ((u : ℂ) + I * v) (centeredPoleRadius q)
  have hfar :=
    tendsto_selectedLocalizedFarZeroResidueSumAtCenter
      q (v := v) hq hu hu1
  have hsum :
      Tendsto
        (fun m =>
          (analyticOrderNatAt riemannZeta
              ((u : ℂ) + I * v) : ℂ) +
            selectedLocalizedFarZeroResidueSumAtCenter q u v m)
        atTop
        (𝓝 (analyticOrderNatAt riemannZeta
          ((u : ℂ) + I * v) : ℂ)) := by
    simpa using tendsto_const_nhds.add hfar
  apply hsum.congr'
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (A.natDegree : ℝ),
    eventually_ge_atTop q] with m hm hdegree hmq
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqScale : q ≤ 27 * m ^ 2 := by
    have hm0 : 0 ≤ m := zero_le_one.trans hm
    nlinarith [mul_nonneg hqPos.le (sub_nonneg.mpr hmq)]
  have hvalid : centeredLocalizedContourScaleValid q A u m :=
    ⟨hq, hu, hu1, hm, hdegree, hqScale⟩
  symm
  simpa [A] using
    selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_eq_target_add_far
      hvalid hzero

/-- At a nonzero center, the filtered centered zero sum converges to zero. -/
theorem
    tendsto_selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_of_ne_zero
    (q : ℝ) {u v : ℝ}
    (hq : 16 ≤ q) (hu : 0 < u) (hu1 : u < 1)
    (hne : riemannZeta ((u : ℂ) + I * v) ≠ 0) :
    Tendsto
      (selectedLocalizedZeroResidueSumAtCenter q
        (localizedNearZeroFilter
          ((u : ℂ) + I * v) (centeredPoleRadius q)) u v)
      atTop (𝓝 0) := by
  let A : ℂ[X] :=
    localizedNearZeroFilter
      ((u : ℂ) + I * v) (centeredPoleRadius q)
  have hfar :=
    tendsto_selectedLocalizedFarZeroResidueSumAtCenter
      q (v := v) hq hu hu1
  apply hfar.congr'
  filter_upwards [
    eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (A.natDegree : ℝ),
    eventually_ge_atTop q] with m hm hdegree hmq
  have hqPos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hqScale : q ≤ 27 * m ^ 2 := by
    have hm0 : 0 ≤ m := zero_le_one.trans hm
    nlinarith [mul_nonneg hqPos.le (sub_nonneg.mpr hmq)]
  have hvalid : centeredLocalizedContourScaleValid q A u m :=
    ⟨hq, hu, hu1, hm, hdegree, hqScale⟩
  symm
  simpa [A] using
    selectedLocalizedZeroResidueSumAtCenter_nearZeroFilter_eq_far_of_ne_zero
      hvalid hne

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
