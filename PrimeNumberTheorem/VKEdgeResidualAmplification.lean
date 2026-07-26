import MathlibAux.ResidualSecondMoment
import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open Complex Filter MeasureTheory Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The normalized real contribution of a conjugate zero pair. -/
def cosineZeroPair (m gamma phase y : ℝ) : ℝ :=
  -2 * m * Real.cos (gamma * y - phase)

/-- Exact second moment of a conjugate zero pair on an oriented interval. -/
theorem intervalIntegral_cosineZeroPair_sq
    {m gamma phase a b : ℝ} (hgamma : gamma ≠ 0) :
    (∫ y in a..b, cosineZeroPair m gamma phase y ^ 2) =
      2 * m ^ 2 * (b - a) +
        m ^ 2 / gamma *
          (Real.sin (2 * gamma * b - 2 * phase) -
            Real.sin (2 * gamma * a - 2 * phase)) := by
  let primitive : ℝ → ℝ := fun y =>
    2 * m ^ 2 * y +
      m ^ 2 / gamma * Real.sin (2 * gamma * y - 2 * phase)
  have hderiv (y : ℝ) :
      HasDerivAt primitive (cosineZeroPair m gamma phase y ^ 2) y := by
    have hlinear :
        HasDerivAt (fun x : ℝ => 2 * gamma * x - 2 * phase)
          (2 * gamma) y := by
      convert ((hasDerivAt_id y).const_mul (2 * gamma)).sub_const
        (2 * phase) using 1 <;> ring
    have hsin :
        HasDerivAt
          (fun x : ℝ =>
            m ^ 2 / gamma *
              Real.sin (2 * gamma * x - 2 * phase))
          (m ^ 2 / gamma *
            (Real.cos (2 * gamma * y - 2 * phase) *
              (2 * gamma))) y :=
      hlinear.sin.const_mul (m ^ 2 / gamma)
    have hmain :
        HasDerivAt (fun x : ℝ => 2 * m ^ 2 * x)
          (2 * m ^ 2) y := by
      convert (hasDerivAt_id y).const_mul (2 * m ^ 2) using 1 <;> ring
    convert hmain.add hsin using 1
    · rw [show 2 * gamma * y - 2 * phase =
          2 * (gamma * y - phase) by ring,
        Real.cos_two_mul]
      unfold cosineZeroPair
      field_simp [hgamma]
      ring
  have hint :
      IntervalIntegrable
        (fun y => cosineZeroPair m gamma phase y ^ 2)
        volume a b := by
    apply Continuous.intervalIntegrable
    unfold cosineZeroPair
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _hy => hderiv y) hint]
  dsimp [primitive]
  ring

/-- The target pair has mean-square density `2m²`, up to an explicit
endpoint error. -/
theorem integral_Icc_cosineZeroPair_sq_le
    {m gamma phase a b : ℝ}
    (hab : a ≤ b) (hgamma : gamma ≠ 0) :
    (∫ y in Icc a b, cosineZeroPair m gamma phase y ^ 2) ≤
      2 * m ^ 2 * (b - a) + 2 * m ^ 2 / |gamma| := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab,
    intervalIntegral_cosineZeroPair_sq hgamma]
  let delta :=
    Real.sin (2 * gamma * b - 2 * phase) -
      Real.sin (2 * gamma * a - 2 * phase)
  have hdelta : |delta| ≤ 2 := by
    dsimp [delta]
    calc
      |Real.sin (2 * gamma * b - 2 * phase) -
          Real.sin (2 * gamma * a - 2 * phase)| ≤
          |Real.sin (2 * gamma * b - 2 * phase)| +
            |Real.sin (2 * gamma * a - 2 * phase)| :=
        abs_sub _ _
      _ ≤ 1 + 1 :=
        add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
      _ = 2 := by norm_num
  have hgammaAbs : 0 < |gamma| := abs_pos.mpr hgamma
  have habs :
      |m ^ 2 / gamma * delta| =
        m ^ 2 / |gamma| * |delta| := by
    rw [abs_mul, abs_div, abs_pow, sq_abs]
  have hterm :
      m ^ 2 / gamma * delta ≤ 2 * m ^ 2 / |gamma| := by
    calc
      m ^ 2 / gamma * delta ≤ |m ^ 2 / gamma * delta| :=
        le_abs_self _
      _ = m ^ 2 / |gamma| * |delta| := habs
      _ ≤ m ^ 2 / |gamma| * 2 :=
        mul_le_mul_of_nonneg_left hdelta
          (div_nonneg (sq_nonneg m) hgammaAbs.le)
      _ = 2 * m ^ 2 / |gamma| := by ring
  dsimp [delta] at hterm
  linarith

/-- The target zero and its conjugate, in the normalization used for the
local PNT error. -/
def normalizedTargetZeroPair (rho : ℂ) (y : ℝ) : ℝ :=
  cosineZeroPair
    (analyticOrderNatAt riemannZeta rho : ℝ)
    rho.im rho.arg y

/-- The normalized PNT error after removing the target conjugate pair. -/
def normalizedPsiResidual (rho : ℂ) (y : ℝ) : ℝ :=
  normalizedPsiError rho y - normalizedTargetZeroPair rho y

theorem measurable_normalizedTargetZeroPair (rho : ℂ) :
    Measurable (normalizedTargetZeroPair rho) := by
  unfold normalizedTargetZeroPair cosineZeroPair
  fun_prop

private theorem measurable_normalizedPsiError_residual (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

theorem measurable_normalizedPsiResidual (rho : ℂ) :
    Measurable (normalizedPsiResidual rho) := by
  unfold normalizedPsiResidual
  exact (measurable_normalizedPsiError_residual rho).sub
    (measurable_normalizedTargetZeroPair rho)

theorem integrableOn_normalizedTargetZeroPair_sq_Icc
    (rho : ℂ) (a b : ℝ) :
    IntegrableOn (fun y => normalizedTargetZeroPair rho y ^ 2)
      (Icc a b) := by
  apply Continuous.integrableOn_Icc
  unfold normalizedTargetZeroPair cosineZeroPair
  fun_prop

private theorem normalizedPsiError_abs_le_exp_growth_residual
    (rho : ℂ) (y : ℝ) :
    |normalizedPsiError rho y| ≤
      ‖rho‖ * (Real.log 4 + 5) *
        Real.exp ((1 - rho.re) * y) := by
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self (Real.exp_pos y).le
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) := by
    unfold chebyshevPsi
    exact Finset.sum_nonneg fun n _ => by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
  have herror :
      |chebyshevPsi (Real.exp y) - Real.exp y| ≤
        (Real.log 4 + 5) * Real.exp y := by
    rw [abs_sub_le_iff]
    constructor
    · nlinarith [Real.exp_pos y]
    · nlinarith [Real.exp_pos y,
        Real.log_pos (by norm_num : 1 < (4 : ℝ))]
  unfold normalizedPsiError
  rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)]
  calc
    ‖rho‖ * |chebyshevPsi (Real.exp y) - Real.exp y| *
          Real.exp (-rho.re * y) ≤
        ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
          Real.exp (-rho.re * y) := by
      gcongr
    _ = ‖rho‖ * (Real.log 4 + 5) *
          Real.exp ((1 - rho.re) * y) := by
      rw [show
          ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
                Real.exp (-rho.re * y) =
              ‖rho‖ * (Real.log 4 + 5) *
                (Real.exp y * Real.exp (-rho.re * y)) by ring,
        ← Real.exp_add]
      congr 1
      ring

private theorem integrableOn_normalizedPsiError_sq_Icc_residual
    {rho : ℂ} (hrhoRe1 : rho.re < 1) (a b : ℝ) :
    IntegrableOn (fun y => normalizedPsiError rho y ^ 2)
      (Icc a b) := by
  let B : ℝ :=
    (‖rho‖ * (Real.log 4 + 5) *
      Real.exp ((1 - rho.re) * b)) ^ 2
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
  · exact
      ((measurable_normalizedPsiError_residual rho).pow_const 2
        |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hcoef : 0 ≤ 1 - rho.re := by linarith
    have hexp :
        Real.exp ((1 - rho.re) * y) ≤
          Real.exp ((1 - rho.re) * b) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hy.2 hcoef)
    have habs :=
      (normalizedPsiError_abs_le_exp_growth_residual rho y).trans
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (norm_nonneg rho)
            (by positivity : 0 ≤ Real.log 4 + 5)))
    have hsq :
        normalizedPsiError rho y ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [sq_abs (normalizedPsiError rho y),
        abs_nonneg (normalizedPsiError rho y)]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (normalizedPsiError rho y))]
    exact hsq

theorem integrableOn_normalizedPsiResidual_sq_Icc
    {rho : ℂ} (hrhoRe1 : rho.re < 1) (a b : ℝ) :
    IntegrableOn (fun y => normalizedPsiResidual rho y ^ 2)
      (Icc a b) := by
  let μ : Measure ℝ := volume.restrict (Icc a b)
  have hf : MemLp (normalizedPsiError rho) 2 μ := by
    apply
      (memLp_two_iff_integrable_sq
        ((measurable_normalizedPsiError_residual rho).aestronglyMeasurable
          (μ := μ))).2
    simpa [μ] using
      integrableOn_normalizedPsiError_sq_Icc_residual hrhoRe1 a b
  have hp : MemLp (normalizedTargetZeroPair rho) 2 μ := by
    apply
      (memLp_two_iff_integrable_sq
        ((measurable_normalizedTargetZeroPair rho).aestronglyMeasurable
          (μ := μ))).2
    simpa [μ] using
      integrableOn_normalizedTargetZeroPair_sq_Icc rho a b
  simpa only [normalizedPsiResidual, Pi.sub_apply, μ] using
    (hf.sub hp).integrable_sq

theorem integral_Icc_normalizedTargetZeroPair_sq_le
    {rho : ℂ} {a b : ℝ}
    (hab : a ≤ b) (hgamma : rho.im ≠ 0) :
    (∫ y in Icc a b, normalizedTargetZeroPair rho y ^ 2) ≤
      2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 * (b - a) +
        2 * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 / |rho.im| := by
  simpa only [normalizedTargetZeroPair] using
    integral_Icc_cosineZeroPair_sq_le
      (m := (analyticOrderNatAt riemannZeta rho : ℝ))
      (gamma := rho.im) (phase := rho.arg) hab hgamma

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
