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

/-- A uniform lower bound for the sharpened missing-harmonic denominator. -/
theorem one_div_pi_le_sharpenedMissingHarmonicDenominator (k : ℕ) :
    1 / Real.pi ≤ sharpenedMissingHarmonicDenominator k := by
  let n : ℝ := ((2 * k + 1 : ℕ) : ℝ)
  have hn : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
  have hnSq : 1 ≤ n ^ 2 := by nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpiLe : Real.pi ≤ Real.pi * n ^ 2 := by
    nlinarith
  have hinv :
      1 / (Real.pi * n ^ 2) ≤ 1 / Real.pi :=
    one_div_le_one_div_of_le hpi hpiLe
  unfold sharpenedMissingHarmonicDenominator
  dsimp [n] at hinv
  calc
    1 / Real.pi = 2 / Real.pi - 1 / Real.pi := by
      field_simp [Real.pi_ne_zero]
      norm_num
    _ ≤
        2 / Real.pi -
          1 / (Real.pi * (((2 * k + 1 : ℕ) : ℝ) ^ 2)) :=
      sub_le_sub_left hinv _

/-- The named projected-kernel envelope includes an additive `1`. -/
theorem one_le_centeredSharpenedProjectedPsiKernelEnvelopeConstant
    (q : ℝ) (rho : ℂ) (k : ℕ) :
    1 ≤ centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k := by
  unfold centeredSharpenedProjectedPsiKernelEnvelopeConstant
  have hsum :
      0 ≤
        projectedPsiKernelAtCenterEnvelopeConstant
            (centeredSharpenedTargetFilter q rho) rho +
          relativeProjectedPsiKernelAtCenterEnvelopeConstant
            (centeredSharpenedMissingFilter q rho k) rho
            (missingHarmonicContourCenter rho k)
            (missingHarmonicContourCoefficient rho k) :=
    add_nonneg
      (projectedPsiKernelAtCenterEnvelopeConstant_nonneg _ _)
      (relativeProjectedPsiKernelAtCenterEnvelopeConstant_nonneg _ _ _ _)
  nlinarith [Real.exp_pos 1]

/--
The current swept ordinary `L²` coefficient is strictly below one half of
the leading energy coefficient of the target conjugate pair.
-/
theorem centeredSharpenedSweptOrdinaryL2Constant_lt_targetPairHalfEnergy
    {epsilon : ℝ} {rho : ℂ} {k : ℕ}
    (hepsilon : 0 < epsilon)
    (hrho1 : rho ≠ 1)
    (hzero : riemannZeta rho = 0) :
    centeredSharpenedSweptOrdinaryL2Constant epsilon rho k <
      epsilon * (analyticOrderNatAt riemannZeta rho : ℝ) ^ 2 := by
  let q : ℝ := epsilonCenterCoefficient (epsilon / 2)
  let d : ℝ := epsilonRadiusCoefficient (epsilon / 2)
  let R : ℝ := epsilonSweepRatio epsilon
  let multiplicity : ℝ := analyticOrderNatAt riemannZeta rho
  let denominator : ℝ := sharpenedMissingHarmonicDenominator k
  let C2 : ℝ := multiplicity ^ 2 / denominator
  let K : ℝ :=
    centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k
  let mass : ℝ := Real.exp 2 * Real.sqrt (2 * R) / q
  let numerator : ℝ := C2 * (R - 1) / (q - d)
  have hepsilon2 : 0 < epsilon / 2 := by positivity
  have hqPos : 0 < q := by
    dsimp [q]
    exact (epsilonRadiusCoefficient_pos hepsilon2).trans
      (epsilonRadiusCoefficient_lt_center hepsilon2)
  have hdq : d < q := by
    dsimp [d, q]
    exact epsilonRadiusCoefficient_lt_center hepsilon2
  have hgapPos : 0 < q - d := sub_pos.mpr hdq
  have hRone : 1 < R := by
    dsimp [R]
    exact one_lt_epsilonSweepRatio hepsilon
  have hRPos : 0 < R := zero_lt_one.trans hRone
  have hmultiplicityPos : 0 < multiplicity := by
    dsimp [multiplicity]
    exact_mod_cast
      ZeroFreeRegion.analyticOrderNatAt_riemannZeta_pos_of_zero
        hrho1 hzero
  have hdenominatorPos : 0 < denominator := by
    dsimp [denominator]
    exact sharpenedMissingHarmonicDenominator_pos k
  have hdenominatorLower : 1 / Real.pi ≤ denominator := by
    dsimp [denominator]
    exact one_div_pi_le_sharpenedMissingHarmonicDenominator k
  have hpiDenominator : 1 ≤ Real.pi * denominator := by
    have hmul :=
      mul_le_mul_of_nonneg_left hdenominatorLower Real.pi_pos.le
    field_simp [Real.pi_ne_zero] at hmul
    exact hmul
  have hC2Pos : 0 < C2 := by
    dsimp [C2]
    exact div_pos (sq_pos_of_pos hmultiplicityPos) hdenominatorPos
  have hC2Le : C2 ≤ Real.pi * multiplicity ^ 2 := by
    dsimp [C2]
    apply (div_le_iff₀ hdenominatorPos).2
    calc
      multiplicity ^ 2 ≤
          multiplicity ^ 2 * (Real.pi * denominator) :=
        by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hpiDenominator
              (sq_nonneg multiplicity)
      _ = Real.pi * multiplicity ^ 2 * denominator := by ring
  have hKOne : 1 ≤ K := by
    dsimp [K]
    exact
      one_le_centeredSharpenedProjectedPsiKernelEnvelopeConstant q rho k
  have hKPos : 0 < K := zero_lt_one.trans_le hKOne
  have hsqrtOne : 1 ≤ Real.sqrt (2 * R) := by
    rw [Real.one_le_sqrt]
    nlinarith
  have hproductOne :
      1 < Real.exp 2 * Real.sqrt (2 * R) := by
    calc
      1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
      _ ≤ Real.exp 2 * Real.sqrt (2 * R) :=
        le_mul_of_one_le_right (Real.exp_pos 2).le hsqrtOne
  have hmassPos : 0 < mass := by
    dsimp [mass]
    positivity
  have honeDivQPos : 0 < 1 / q := one_div_pos.mpr hqPos
  have hmassLower : 1 / q < mass := by
    dsimp [mass]
    exact (div_lt_div_iff_of_pos_right hqPos).2 hproductOne
  have hKmassLower : 1 / q < K * mass := by
    exact hmassLower.trans_le
      (le_mul_of_one_le_left hmassPos.le hKOne)
  have hKmassPos : 0 < K * mass := mul_pos hKPos hmassPos
  have hnumeratorPos : 0 < numerator := by
    dsimp [numerator]
    exact div_pos (mul_pos hC2Pos (sub_pos.mpr hRone)) hgapPos
  have hnumeratorLe :
      numerator ≤
        (Real.pi * multiplicity ^ 2) * (R - 1) / (q - d) := by
    dsimp [numerator]
    gcongr
    exact sub_nonneg.mpr hRone.le
  have hqFormula :
      q = 64 * (epsilon + 4) ^ 2 / epsilon ^ 2 := by
    dsimp [q, epsilonCenterCoefficient]
    field_simp [hepsilon.ne']
    ring
  have hdFormula :
      d = 64 * (epsilon + 4) / epsilon := by
    dsimp [d, epsilonRadiusCoefficient]
    field_simp [hepsilon.ne']
    ring
  have hgapFormula :
      q - d = 256 * (epsilon + 4) / epsilon ^ 2 := by
    rw [hqFormula, hdFormula]
    field_simp [hepsilon.ne']
    ring
  have hRFormula :
      R - 1 = epsilon / (epsilon + 2) := by
    dsimp [R, epsilonSweepRatio]
    field_simp [show epsilon + 2 ≠ 0 by linarith]
    ring
  have hraw :
      numerator / (K * mass) <
        ((Real.pi * multiplicity ^ 2) * (R - 1) / (q - d)) /
          (1 / q) := by
    calc
      numerator / (K * mass) < numerator / (1 / q) :=
        div_lt_div_of_pos_left hnumeratorPos honeDivQPos hKmassLower
      _ ≤
          ((Real.pi * multiplicity ^ 2) * (R - 1) / (q - d)) /
            (1 / q) :=
        div_le_div_of_nonneg_right hnumeratorLe honeDivQPos.le
  have hshape :
      Real.pi * (epsilon + 4) < 8 * (epsilon + 2) := by
    have hpiMul :
        Real.pi * (epsilon + 4) < 4 * (epsilon + 4) :=
      mul_lt_mul_of_pos_right Real.pi_lt_four (by linarith)
    linarith
  have hfinal :
      Real.pi * multiplicity ^ 2 * epsilon * (epsilon + 4) /
          (8 * (epsilon + 2)) <
        epsilon * multiplicity ^ 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < 8 * (epsilon + 2))).2
    have hscale :
        0 < epsilon * multiplicity ^ 2 :=
      mul_pos hepsilon (sq_pos_of_pos hmultiplicityPos)
    have := mul_lt_mul_of_pos_left hshape hscale
    nlinarith
  unfold centeredSharpenedSweptOrdinaryL2Constant
  dsimp only
  change numerator / (K * mass) / 2 <
    epsilon * multiplicity ^ 2
  calc
    numerator / (K * mass) / 2 <
        (((Real.pi * multiplicity ^ 2) * (R - 1) / (q - d)) /
          (1 / q)) / 2 :=
      div_lt_div_of_pos_right hraw (by norm_num)
    _ =
        Real.pi * multiplicity ^ 2 * epsilon * (epsilon + 4) /
          (8 * (epsilon + 2)) := by
      rw [hgapFormula, hRFormula, hqFormula]
      field_simp [hepsilon.ne', show epsilon + 2 ≠ 0 by linarith,
        show epsilon + 4 ≠ 0 by linarith, Real.pi_ne_zero]
      ring
    _ < epsilon * multiplicity ^ 2 := hfinal

/--
A total local second-moment coefficient strictly above the target-pair
budget forces a positive second moment for the residual error.
-/
theorem integral_Icc_normalizedPsiResidual_sq_lower
    {rho : ℂ} {a b A B : ℝ}
    (hrhoRe1 : rho.re < 1)
    (hab : a ≤ b)
    (_hgamma : rho.im ≠ 0)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hBA : B < A)
    (htotal :
      A * (b - a) ≤
        ∫ y in Icc a b, normalizedPsiError rho y ^ 2)
    (hpair :
      (∫ y in Icc a b, normalizedTargetZeroPair rho y ^ 2) ≤
        B * (b - a)) :
    (Real.sqrt A - Real.sqrt B) ^ 2 * (b - a) ≤
      ∫ y in Icc a b, normalizedPsiResidual rho y ^ 2 := by
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
  have hres :=
    MathlibAux.integral_sq_sub_lower_of_integral_sq_bounds
      hf hp (sub_nonneg.mpr hab) hA hB hBA htotal hpair
  simpa only [μ, normalizedPsiResidual, Pi.sub_apply] using hres

/-- Target-pair energy density on an epsilon logarithmic window, including
the finite-height endpoint correction. -/
def epsilonLogWindowTargetPairCoefficient
    (epsilon : ℝ) (rho : ℂ) (Y : ℝ) : ℝ :=
  let multiplicity : ℝ := analyticOrderNatAt riemannZeta rho
  2 * multiplicity ^ 2 +
    2 * multiplicity ^ 2 /
      (|rho.im| * epsilon * Real.log Y)

theorem integral_Icc_normalizedTargetZeroPair_sq_le_epsilonLogWindow
    {epsilon Y : ℝ} {rho : ℂ}
    (hepsilon : 0 < epsilon)
    (hY : 1 < Y)
    (hgamma : rho.im ≠ 0) :
    (∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
        normalizedTargetZeroPair rho y ^ 2) ≤
      epsilonLogWindowTargetPairCoefficient epsilon rho Y *
        (epsilon * Real.log Y) := by
  let multiplicity : ℝ := analyticOrderNatAt riemannZeta rho
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hab :
      Real.log Y ≤ (1 + epsilon) * Real.log Y := by
    nlinarith
  have hpair :=
    integral_Icc_normalizedTargetZeroPair_sq_le
      (rho := rho) hab hgamma
  have hlength :
      (1 + epsilon) * Real.log Y - Real.log Y =
        epsilon * Real.log Y := by ring
  have hcoefficient :
      epsilonLogWindowTargetPairCoefficient epsilon rho Y *
          (epsilon * Real.log Y) =
        2 * multiplicity ^ 2 * (epsilon * Real.log Y) +
          2 * multiplicity ^ 2 / |rho.im| := by
    unfold epsilonLogWindowTargetPairCoefficient
    dsimp only [multiplicity]
    field_simp [abs_ne_zero.mpr hgamma, hepsilon.ne', hlog.ne']
  rw [hlength] at hpair
  rw [hcoefficient]
  exact hpair

/--
Logarithmic-window residual endpoint with the exact finite-height target-pair
correction exposed in the threshold coefficient.
-/
theorem integral_Icc_normalizedPsiResidual_sq_lower_epsilonLogWindow
    {epsilon Y A : ℝ} {rho : ℂ}
    (hrhoRe1 : rho.re < 1)
    (hepsilon : 0 < epsilon)
    (hY : 1 < Y)
    (hgamma : rho.im ≠ 0)
    (hA : 0 ≤ A)
    (hBA :
      epsilonLogWindowTargetPairCoefficient epsilon rho Y < A)
    (htotal :
      A * (epsilon * Real.log Y) ≤
        ∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
          normalizedPsiError rho y ^ 2) :
    (Real.sqrt A -
        Real.sqrt
          (epsilonLogWindowTargetPairCoefficient epsilon rho Y)) ^ 2 *
          (epsilon * Real.log Y) ≤
      ∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
        normalizedPsiResidual rho y ^ 2 := by
  let B := epsilonLogWindowTargetPairCoefficient epsilon rho Y
  have hlog : 0 < Real.log Y := Real.log_pos hY
  have hab :
      Real.log Y ≤ (1 + epsilon) * Real.log Y := by
    nlinarith
  have hB : 0 ≤ B := by
    dsimp [B, epsilonLogWindowTargetPairCoefficient]
    positivity
  have hpair :
      (∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
          normalizedTargetZeroPair rho y ^ 2) ≤
        B * (((1 + epsilon) * Real.log Y) - Real.log Y) := by
    have h :=
      integral_Icc_normalizedTargetZeroPair_sq_le_epsilonLogWindow
        hepsilon hY hgamma
    simpa only [B, show
        (1 + epsilon) * Real.log Y - Real.log Y =
          epsilon * Real.log Y by ring] using h
  have htotal' :
      A * (((1 + epsilon) * Real.log Y) - Real.log Y) ≤
        ∫ y in Icc (Real.log Y) ((1 + epsilon) * Real.log Y),
          normalizedPsiError rho y ^ 2 := by
    simpa only [show
        (1 + epsilon) * Real.log Y - Real.log Y =
          epsilon * Real.log Y by ring] using htotal
  have hres :=
    integral_Icc_normalizedPsiResidual_sq_lower
      hrhoRe1 hab hgamma hA hB (by simpa only [B] using hBA)
      htotal' hpair
  simpa only [B, show
      (1 + epsilon) * Real.log Y - Real.log Y =
        epsilon * Real.log Y by ring] using hres

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
