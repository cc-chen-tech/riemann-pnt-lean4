import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicKernelNearOne
import PrimeNumberTheorem.ZeroDensityLayerBudgetCubicContourKernelFactorization
import PrimeNumberTheorem.ZeroDensityLayerBudgetAutomaticCubicContourIntegrability
import PrimeNumberTheorem.VKEdgeDesmoothedLeftDerivative
import MathlibAux.IntervalOscillatoryIntegrationByParts

open Complex Metric

namespace PrimeNumberTheorem
namespace ExplicitFormulaResidues

/-- Away from the removable point at zero, the cubic de-smoothing multiplier
has derivative of reciprocal-size order. The half-norm disk keeps the written
difference quotient analytic and the multiplier uniformly bounded. -/
theorem norm_deriv_cubicKernelMultiplier_le_eight_div_norm
    {rho : ℂ} {h : ℝ} (hh : 0 < h) (hrho : rho ≠ 0)
    (hsmall : h * ‖rho‖ ≤ 1 / 2) :
    ‖deriv (fun z : ℂ => cubicKernelMultiplier z h) rho‖ ≤
      8 / ‖rho‖ := by
  let R : ℝ := ‖rho‖ / 2
  have hrhoNorm : 0 < ‖rho‖ := norm_pos_iff.mpr hrho
  have hR : 0 < R := by dsimp [R]; positivity
  have hzNonzero : ∀ z ∈ closedBall rho R, z ≠ 0 := by
    intro z hz hz0
    subst z
    have hdist : ‖rho‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm, norm_neg] using hz
    dsimp [R] at hdist
    linarith
  have hdiffClosed : DifferentiableOn ℂ
      (fun z : ℂ => cubicKernelMultiplier z h) (closedBall rho R) := by
    intro z hz
    have hz0 := hzNonzero z hz
    have hlin : DifferentiableAt ℂ (fun w : ℂ => (h : ℂ) * w) z :=
      differentiableAt_id.const_mul (h : ℂ)
    have hden : (h : ℂ) * z ≠ 0 :=
      mul_ne_zero (ofReal_ne_zero.mpr hh.ne') hz0
    unfold cubicKernelMultiplier
    exact ((hlin.cexp.sub_const 1).div hlin hden).pow 2 |>.differentiableWithinAt
  have hdiff : DiffContOnCl ℂ
      (fun z : ℂ => cubicKernelMultiplier z h) (ball rho R) :=
    hdiffClosed.diffContOnCl_ball subset_rfl
  have hnorm : ∀ z ∈ sphere rho R,
      ‖cubicKernelMultiplier z h‖ ≤ 4 := by
    intro z hz
    have hzClosed : z ∈ closedBall rho R := Metric.sphere_subset_closedBall hz
    have hz0 := hzNonzero z hzClosed
    have hdist : ‖z - rho‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzClosed
    have hzNorm : ‖z‖ ≤ 3 * ‖rho‖ / 2 := by
      calc
        ‖z‖ = ‖(z - rho) + rho‖ := congrArg norm (by ring)
        _ ≤ ‖z - rho‖ + ‖rho‖ := norm_add_le _ _
        _ ≤ R + ‖rho‖ := by gcongr
        _ = 3 * ‖rho‖ / 2 := by dsimp [R]; ring
    have hzSmall : h * ‖z‖ ≤ 1 := by
      have : h * ‖z‖ ≤ h * (3 * ‖rho‖ / 2) :=
        mul_le_mul_of_nonneg_left hzNorm hh.le
      nlinarith
    have hnear := norm_cubicKernelMultiplier_sub_one_le_three_mul
      hh hz0 hzSmall
    have hupper := (norm_multiplier_bounds_of_sub_one_le hnear).2
    calc
      ‖cubicKernelMultiplier z h‖ ≤ 1 + 3 * (h * ‖z‖) := hupper
      _ ≤ 4 := by nlinarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hR hdiff hnorm
  calc
    ‖deriv (fun z : ℂ => cubicKernelMultiplier z h) rho‖ ≤ 4 / R := hcauchy
    _ = 8 / ‖rho‖ := by dsimp [R]; field_simp; ring

/-- The nonoscillatory amplitude remaining on the positive-real-part left
edge after the common factor `x^a exp (i t log x)` is removed. -/
noncomputable def desmoothedLeftOscillatoryAmplitude
    (h a t : ℝ) : ℂ :=
  -logDeriv riemannZeta ((a : ℂ) + I * t) /
      ((a : ℂ) + I * t) *
    cubicKernelMultiplier ((a : ℂ) + I * t) h

/-- Exact phase factorization of the actual desmoothed zeta integrand on the
dynamic left edge. -/
theorem desmoothedCubicLeftContourIntegrand_eq_rpow_mul_amplitude_mul_cexp
    {x h a t : ℝ} (hx : 0 < x) :
    desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t) =
      ((x ^ a : ℝ) : ℂ) * desmoothedLeftOscillatoryAmplitude h a t *
        Complex.exp (I * (Real.log x * t)) := by
  have hpow : (x : ℂ) ^ ((a : ℂ) + I * t) =
      ((x ^ a : ℝ) : ℂ) * Complex.exp (I * (Real.log x * t)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    rw [← Complex.ofReal_log hx.le]
    have hexponent :
        (Real.log x : ℂ) * ((a : ℂ) + I * t) =
          (Real.log x * a : ℝ) + I * (Real.log x * t) := by
      push_cast
      ring
    rw [hexponent, Complex.exp_add, ← Complex.ofReal_exp,
      ← Real.rpow_def_of_pos hx]
  rw [desmoothedCubicContourIntegrand, explicitFormulaIntegrand,
    desmoothedLeftOscillatoryAmplitude, cubicLeftContourPoint,
    show (t : ℂ) * I = I * t by ring, hpow]
  ring

private theorem differentiableAt_cubicKernelMultiplier_of_ne_zero
    {rho : ℂ} {h : ℝ} (hh : 0 < h) (hrho : rho ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => cubicKernelMultiplier z h) rho := by
  have hlin : DifferentiableAt ℂ (fun z : ℂ => (h : ℂ) * z) rho :=
    differentiableAt_id.const_mul (h : ℂ)
  have hden : (h : ℂ) * rho ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hh.ne') hrho
  unfold cubicKernelMultiplier
  exact ((hlin.cexp.sub_const 1).div hlin hden).pow 2

/-- The actual nonoscillatory left-edge amplitude has reciprocal-height size
when the cubic multiplier remains in its near-one range. -/
theorem norm_desmoothedLeftOscillatoryAmplitude_le
    {h a t L : ℝ} (hh : 0 < h) (ht : 2 ≤ |t|)
    (hlog : ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hsmall : h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖desmoothedLeftOscillatoryAmplitude h a t‖ ≤ 3 * L / |t| := by
  let s : ℂ := (a : ℂ) + I * t
  have hsIm : s.im = t := by simp [s]
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have htNorm : |t| ≤ ‖s‖ := by
    rw [← hsIm]
    exact Complex.abs_im_le_norm s
  have hsNorm : 0 < ‖s‖ := htPos.trans_le htNorm
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp hsNorm.ne'
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hlog
  have hKNorm : ‖cubicKernelMultiplier s h‖ ≤ 3 := by
    have hsmallOne : h * ‖s‖ ≤ 1 := by
      simpa [s] using hsmall.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hnear := norm_cubicKernelMultiplier_sub_one_le_three_mul
      hh hs0 hsmallOne
    have hupper := (norm_multiplier_bounds_of_sub_one_le hnear).2
    exact hupper.trans (by nlinarith)
  have hquot : ‖-logDeriv riemannZeta s / s‖ ≤ L / |t| := by
    rw [norm_div, norm_neg]
    exact div_le_div₀ hL0 (by simpa [s] using hlog) htPos htNorm
  rw [desmoothedLeftOscillatoryAmplitude]
  change ‖-logDeriv riemannZeta s / s * cubicKernelMultiplier s h‖ ≤ _
  calc
    ‖-logDeriv riemannZeta s / s * cubicKernelMultiplier s h‖ =
        ‖-logDeriv riemannZeta s / s‖ * ‖cubicKernelMultiplier s h‖ := norm_mul _ _
    _ ≤ (L / |t|) * 3 := mul_le_mul hquot hKNorm (norm_nonneg _) (by positivity)
    _ = 3 * L / |t| := by ring

/-- Zeta nonvanishing on the left edge makes the actual amplitude real-
differentiable in the height variable. -/
theorem differentiableAt_desmoothedLeftOscillatoryAmplitude
    {h a t : ℝ} (hh : 0 < h) (ht : 2 ≤ |t|)
    (hzeta : riemannZeta ((a : ℂ) + I * t) ≠ 0) :
    DifferentiableAt ℝ (desmoothedLeftOscillatoryAmplitude h a) t := by
  let s : ℂ := (a : ℂ) + I * t
  have hsIm : s.im = t := by simp [s]
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have htNorm : |t| ≤ ‖s‖ := by
    rw [← hsIm]
    exact Complex.abs_im_le_norm s
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp (htPos.trans_le htNorm).ne'
  have hs1 : s ≠ 1 := by
    intro hsOne
    have : |t| = 0 := by rw [← hsIm, hsOne]; norm_num
    linarith
  have hparamComplex :
      HasDerivAt (fun z : ℂ => (a : ℂ) + I * z) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (a : ℂ)
  have hparam :
      HasDerivAt (fun u : ℝ => (a : ℂ) + I * (u : ℂ)) I t := by
    simpa using hparamComplex.comp_ofReal
  have hlogAnalytic : AnalyticAt ℂ (logDeriv riemannZeta) s :=
    ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      s hs1 (by simpa [s] using hzeta)
  have hf : DifferentiableAt ℝ
      (fun u : ℝ => -logDeriv riemannZeta ((a : ℂ) + I * u)) t :=
    (hlogAnalytic.differentiableAt.hasDerivAt.comp t hparam).neg.differentiableAt
  have hden : DifferentiableAt ℝ (fun u : ℝ => (a : ℂ) + I * u) t :=
    hparam.differentiableAt
  have hKderiv : HasDerivAt
      (fun u : ℝ => cubicKernelMultiplier ((a : ℂ) + I * u) h)
      (deriv (fun z : ℂ => cubicKernelMultiplier z h) s * I) t := by
    simpa [s] using
      (differentiableAt_cubicKernelMultiplier_of_ne_zero hh hs0).hasDerivAt.comp t hparam
  have hK : DifferentiableAt ℝ
      (fun u : ℝ => cubicKernelMultiplier ((a : ℂ) + I * u) h) t :=
    hKderiv.differentiableAt
  simpa [desmoothedLeftOscillatoryAmplitude] using
    (hf.div hden (by simpa [s] using hs0)).mul hK

/-- The actual left-edge amplitude derivative retains the reciprocal-height
decay of each differentiated factor. -/
theorem norm_deriv_desmoothedLeftOscillatoryAmplitude_le
    {h a t L D : ℝ} (hh : 0 < h)
    (ht : 2 ≤ |t|)
    (hzeta : riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖deriv (desmoothedLeftOscillatoryAmplitude h a) t‖ ≤
      3 * D / |t| + 11 * L / |t| ^ 2 := by
  let s : ℂ := (a : ℂ) + I * t
  let f : ℂ := -logDeriv riemannZeta s
  let fp : ℂ := -(deriv (logDeriv riemannZeta) s * I)
  let K : ℂ := cubicKernelMultiplier s h
  let Kp : ℂ := deriv (fun z : ℂ => cubicKernelMultiplier z h) s * I
  let qd : ℂ := (fp * s - f * I) / s ^ 2
  have hsIm : s.im = t := by simp [s]
  have htPos : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have htNorm : |t| ≤ ‖s‖ := by
    rw [← hsIm]
    exact Complex.abs_im_le_norm s
  have hsNorm : 0 < ‖s‖ := htPos.trans_le htNorm
  have hs0 : s ≠ 0 := norm_ne_zero_iff.mp hsNorm.ne'
  have hs1 : s ≠ 1 := by
    intro hsOne
    have : |t| = 0 := by rw [← hsIm, hsOne]; norm_num
    linarith
  have hL0 : 0 ≤ L := (norm_nonneg _).trans hlog
  have hD0 : 0 ≤ D := (norm_nonneg _).trans hlog'
  have hparamComplex :
      HasDerivAt (fun z : ℂ => (a : ℂ) + I * z) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (a : ℂ)
  have hparam :
      HasDerivAt (fun u : ℝ => (a : ℂ) + I * (u : ℂ)) I t := by
    simpa using hparamComplex.comp_ofReal
  have hlogAnalytic : AnalyticAt ℂ (logDeriv riemannZeta) s :=
    ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      s hs1 hzeta
  have hf : HasDerivAt
      (fun u : ℝ => -logDeriv riemannZeta ((a : ℂ) + I * u)) fp t := by
    dsimp [fp, s]
    simpa using
      (hlogAnalytic.differentiableAt.hasDerivAt.comp t hparam).neg
  have hKdiff : DifferentiableAt ℂ
      (fun z : ℂ => cubicKernelMultiplier z h) s :=
    differentiableAt_cubicKernelMultiplier_of_ne_zero hh hs0
  have hK : HasDerivAt
      (fun u : ℝ => cubicKernelMultiplier ((a : ℂ) + I * u) h) Kp t := by
    dsimp [Kp, s]
    simpa using hKdiff.hasDerivAt.comp t hparam
  have hamp : HasDerivAt (desmoothedLeftOscillatoryAmplitude h a)
      (qd * K + (f / s) * Kp) t := by
    have hdiv := hf.div hparam hs0
    have hmul := hdiv.mul hK
    simpa [desmoothedLeftOscillatoryAmplitude, qd, K, Kp, f, fp, s] using hmul
  have hfp : ‖fp‖ ≤ D := by
    dsimp [fp]
    simpa using hlog'
  have hfNorm : ‖f‖ ≤ L := by
    dsimp [f]
    simpa using hlog
  have hKNorm : ‖K‖ ≤ 3 := by
    have hsmallOne : h * ‖s‖ ≤ 1 := by
      simpa [s] using hsmall.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
    have hnear := norm_cubicKernelMultiplier_sub_one_le_three_mul
      hh hs0 hsmallOne
    have hupper := (norm_multiplier_bounds_of_sub_one_le hnear).2
    dsimp [K]
    exact hupper.trans (by nlinarith)
  have hKpNorm : ‖Kp‖ ≤ 8 / |t| := by
    have hraw := norm_deriv_cubicKernelMultiplier_le_eight_div_norm
      hh hs0 hsmall
    have hheight : 8 / ‖s‖ ≤ 8 / |t| := by
      exact div_le_div_of_nonneg_left (by norm_num) htPos htNorm
    dsimp [Kp]
    calc
      ‖deriv (fun z : ℂ => cubicKernelMultiplier z h) s * I‖ =
          ‖deriv (fun z : ℂ => cubicKernelMultiplier z h) s‖ := by simp
      _ ≤ 8 / ‖s‖ := hraw
      _ ≤ 8 / |t| := hheight
  have hqNorm : ‖f / s‖ ≤ L / |t| := by
    rw [norm_div]
    exact div_le_div₀ hL0 hfNorm htPos htNorm
  have hqdNorm : ‖qd‖ ≤ D / |t| + L / |t| ^ 2 := by
    have hnum : ‖fp * s - f * I‖ ≤ D * ‖s‖ + L := by
      calc
        ‖fp * s - f * I‖ ≤ ‖fp * s‖ + ‖f * I‖ := norm_sub_le _ _
        _ = ‖fp‖ * ‖s‖ + ‖f‖ := by simp
        _ ≤ D * ‖s‖ + L := by gcongr
    have hraw : ‖qd‖ ≤ D / ‖s‖ + L / ‖s‖ ^ 2 := by
      dsimp [qd]
      rw [norm_div, norm_pow]
      calc
        ‖fp * s - f * I‖ / ‖s‖ ^ 2 ≤
            (D * ‖s‖ + L) / ‖s‖ ^ 2 := by gcongr
        _ = D / ‖s‖ + L / ‖s‖ ^ 2 := by
          field_simp [hsNorm.ne']
    have hfirst : D / ‖s‖ ≤ D / |t| :=
      div_le_div_of_nonneg_left hD0 htPos htNorm
    have hsSq : |t| ^ 2 ≤ ‖s‖ ^ 2 := by nlinarith
    have htSqPos : 0 < |t| ^ 2 := sq_pos_of_pos htPos
    have hsecond : L / ‖s‖ ^ 2 ≤ L / |t| ^ 2 :=
      div_le_div_of_nonneg_left hL0 htSqPos hsSq
    exact hraw.trans (add_le_add hfirst hsecond)
  rw [hamp.deriv]
  calc
    ‖qd * K + (f / s) * Kp‖ ≤
        ‖qd‖ * ‖K‖ + ‖f / s‖ * ‖Kp‖ := by
      calc
        _ ≤ ‖qd * K‖ + ‖(f / s) * Kp‖ := norm_add_le _ _
        _ = _ := by rw [norm_mul, norm_mul]
    _ ≤ (D / |t| + L / |t| ^ 2) * 3 +
        (L / |t|) * (8 / |t|) := by gcongr
    _ = 3 * D / |t| + 11 * L / |t| ^ 2 := by
      field_simp [htPos.ne']
      ring

/-- On a positive high-height interval, the actual zeta left-edge amplitude
has logarithmic total variation.  Integration by parts therefore gains one
full reciprocal power of the phase frequency without paying the interval
length. -/
theorem norm_intervalIntegral_desmoothedLeftOscillatoryAmplitude_mul_cexp_le
    {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzeta : ∀ t ∈ Set.Icc u v, riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ∀ t ∈ Set.Icc u v,
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ∀ t ∈ Set.Icc u v,
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : ∀ t ∈ Set.Icc u v,
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖∫ t in u..v, desmoothedLeftOscillatoryAmplitude h a t *
        Complex.exp (I * (Real.log x * t))‖ ≤
      (6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
        Real.log x := by
  let A : ℝ → ℂ := desmoothedLeftOscillatoryAmplitude h a
  let V : ℝ := 3 * D + 11 * L
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) hu
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hderivBound : ∀ t ∈ Set.Icc u v, ‖deriv A t‖ ≤ V / t := by
    intro t ht
    have htTwo : 2 ≤ t := hu.trans ht.1
    have htPos : 0 < t := lt_of_lt_of_le (by norm_num) htTwo
    have htOne : 1 ≤ t := by linarith
    have htAbs : |t| = t := abs_of_pos htPos
    have hraw := norm_deriv_desmoothedLeftOscillatoryAmplitude_le
      hh (by simpa [htAbs] using htTwo) (hzeta t ht) (hlog t ht) (hlog' t ht)
        (hsmall t ht)
    have hq : 11 * L / t ^ 2 ≤ 11 * L / t := by
      have hcoeff : 0 ≤ 11 * L := by positivity
      have htSq : t ≤ t ^ 2 := by nlinarith
      exact div_le_div_of_nonneg_left hcoeff htPos htSq
    change ‖deriv (desmoothedLeftOscillatoryAmplitude h a) t‖ ≤ _ at hraw ⊢
    rw [htAbs] at hraw
    calc
      ‖deriv (desmoothedLeftOscillatoryAmplitude h a) t‖ ≤
          3 * D / t + 11 * L / t ^ 2 := hraw
      _ ≤ 3 * D / t + 11 * L / t := add_le_add (le_refl _) hq
      _ = V / t := by dsimp [V]; ring
  have hA'int : IntervalIntegrable (deriv A) MeasureTheory.volume u v :=
    MathlibAux.intervalIntegrable_deriv_of_norm_le_div huPos huv hderivBound
  have hvariation : (∫ t in u..v, ‖deriv A t‖) ≤
      V * Real.log (v / u) :=
    MathlibAux.intervalIntegral_norm_le_mul_log_div_of_norm_le_div
      huPos huv hA'int hderivBound
  have hAderiv : ∀ t ∈ Set.uIcc u v, HasDerivAt A (deriv A t) t := by
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    have htTwo : 2 ≤ t := hu.trans ht.1
    have htAbs : |t| = t := abs_of_pos (lt_of_lt_of_le (by norm_num) htTwo)
    exact (differentiableAt_desmoothedLeftOscillatoryAmplitude
      hh (by simpa [htAbs] using htTwo) (hzeta t ht)).hasDerivAt
  have hA0 : ∀ t ∈ Set.uIcc u v, ‖A t‖ ≤ 3 * L / u := by
    intro t ht
    rw [Set.uIcc_of_le huv] at ht
    have htTwo : 2 ≤ t := hu.trans ht.1
    have htPos : 0 < t := lt_of_lt_of_le (by norm_num) htTwo
    have htAbs : |t| = t := abs_of_pos htPos
    have hraw := norm_desmoothedLeftOscillatoryAmplitude_le
      hh (by simpa [htAbs] using htTwo) (hlog t ht) (hsmall t ht)
    change ‖A t‖ ≤ _ at hraw ⊢
    rw [htAbs] at hraw
    exact hraw.trans (div_le_div_of_nonneg_left (by positivity) huPos ht.1)
  have hibp := MathlibAux.norm_intervalIntegral_mul_cexp_linear_le_of_totalVariation
    (A := A) (A' := deriv A) (omega := Real.log x)
    (M0 := 3 * L / u) (V0 := V * Real.log (v / u))
    huv hlogx.ne' hAderiv hA'int hA0 hvariation
  rw [show 6 * L / u = 2 * (3 * L / u) by ring]
  simpa [A, V, abs_of_pos hlogx] using hibp

/-- The preceding oscillatory estimate, reassembled as the actual desmoothed
zeta integrand on a positive portion of the dynamic left contour. -/
theorem norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
    {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzeta : ∀ t ∈ Set.Icc u v, riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ∀ t ∈ Set.Icc u v,
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ∀ t ∈ Set.Icc u v,
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : ∀ t ∈ Set.Icc u v,
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖∫ t in u..v,
        desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
      x ^ a *
        ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
          Real.log x) := by
  have hxPos : 0 < x := lt_trans (by norm_num) hx
  have hamp :=
    norm_intervalIntegral_desmoothedLeftOscillatoryAmplitude_mul_cexp_le
      hx hh hu huv hL hD hzeta hlog hlog' hsmall
  have hfactor :
      (∫ t in u..v,
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)) =
        ((x ^ a : ℝ) : ℂ) *
          ∫ t in u..v, desmoothedLeftOscillatoryAmplitude h a t *
            Complex.exp (I * (Real.log x * t)) := by
    calc
      (∫ t in u..v,
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)) =
          ∫ t in u..v, ((x ^ a : ℝ) : ℂ) *
            (desmoothedLeftOscillatoryAmplitude h a t *
              Complex.exp (I * (Real.log x * t))) := by
            apply intervalIntegral.integral_congr
            intro t _ht
            change desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t) = _
            rw [desmoothedCubicLeftContourIntegrand_eq_rpow_mul_amplitude_mul_cexp hxPos]
            ring
      _ = ((x ^ a : ℝ) : ℂ) *
          ∫ t in u..v, desmoothedLeftOscillatoryAmplitude h a t *
            Complex.exp (I * (Real.log x * t)) :=
        intervalIntegral.integral_const_mul _ _
  rw [hfactor, norm_mul, norm_real]
  have hxpow : 0 ≤ x ^ a := (Real.rpow_pos_of_pos hxPos a).le
  simpa [Real.norm_eq_abs, abs_of_nonneg hxpow] using
    mul_le_mul_of_nonneg_left hamp hxpow

/-- One dynamic left boundary supports both the pointwise logarithmic-
derivative estimate and its Cauchy derivative estimate.  Keeping the witnesses
joint is essential when the two estimates are inserted into one oscillatory
amplitude. -/
theorem exists_dynamicCubicLeftBoundary_logDeriv_and_deriv_le :
    ∃ b C D T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 3 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            riemannZeta ((a : ℂ) + I * t) ≠ 0 ∧
              ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤
                C * (1 + Real.log (H + 6)) ^ 2 ∧
              ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤
                D * (1 + Real.log (H + 6)) ^ 3 := by
  rcases PrimeNumberTheorem.exists_dynamicCubicLeftBoundary_closedBall_logDeriv_le_log_sq with
    ⟨b, C, T0, hb, hC, hT0, hbase⟩
  let D : ℝ := 4 * C / b
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨b, C, D, T0, hb, hC, hD, hT0, ?_⟩
  intro H hH
  rcases hbase H hH with ⟨ha, haThird, hpoint⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  refine ⟨ha, haThird, ?_⟩
  intro t ht hHt
  let center : ℂ := (a : ℂ) + I * t
  let R : ℝ := a / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hcenterMem : center ∈ closedBall center R := by
    simp [Metric.mem_closedBall, hR.le]
  rcases hpoint t ht hHt center hcenterMem with
    ⟨hcenterOne, hcenterZeta, hcenterLog⟩
  have han : ∀ z ∈ closedBall center R,
      AnalyticAt ℂ (logDeriv riemannZeta) z := by
    intro z hz
    rcases hpoint t ht hHt z hz with ⟨hzOne, hzeta, _⟩
    exact ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      z hzOne hzeta
  have hdiffClosed : DifferentiableOn ℂ (logDeriv riemannZeta)
      (closedBall center R) := by
    intro z hz
    exact (han z hz).differentiableAt.differentiableWithinAt
  have hdiff : DiffContOnCl ℂ (logDeriv riemannZeta) (ball center R) :=
    hdiffClosed.diffContOnCl_ball subset_rfl
  have hnorm : ∀ z ∈ sphere center R,
      ‖logDeriv riemannZeta z‖ ≤
        C * (1 + Real.log (H + 6)) ^ 2 := by
    intro z hz
    exact (hpoint t ht hHt z (Metric.sphere_subset_closedBall hz)).2.2
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hR hdiff hnorm
  have hlogH : 0 < Real.log (H + 6) :=
    Real.log_pos (by linarith [hT0.trans hH] : (1 : ℝ) < H + 6)
  let LH : ℝ := Real.log (H + 6)
  let L : ℝ := 1 + LH
  have hLH : 0 ≤ LH := by dsimp [LH]; exact hlogH.le
  have hL : LH ≤ L := by dsimp [L]; linarith
  refine ⟨hcenterZeta, hcenterLog, ?_⟩
  calc
    ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ =
        ‖deriv (logDeriv riemannZeta) center‖ := by rfl
    _ ≤ C * L ^ 2 / R := by simpa [L, LH] using hcauchy
    _ = D * LH * L ^ 2 := by
      dsimp [R, a, dynamicCubicLeftBoundary, D, LH]
      field_simp [hb.ne', hlogH.ne']
      ring
    _ ≤ D * L * L ^ 2 := by gcongr
    _ = D * L ^ 3 := by ring
    _ = D * (1 + Real.log (H + 6)) ^ 3 := by rfl

/-- A fully instantiated positive high-height budget for the actual zeta
integrand on one dynamic left boundary.  The remaining hypotheses are only
the interval geometry and the cubic de-smoothing scale `h * H ≤ 1/2`. -/
theorem exists_dynamicCubicLeftBoundary_positive_interval_oscillatory_bound :
    ∃ b C D T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H x h u v : ℝ, T0 ≤ H → 1 < x → 0 < h →
        T0 + 1 ≤ u → u ≤ v → v + 1 ≤ H → h * H ≤ 1 / 2 →
          let a := dynamicCubicLeftBoundary b H
          ‖∫ t in u..v,
              desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
            x ^ a *
              ((6 * (C * (1 + Real.log (H + 6)) ^ 2) / u +
                (3 * (D * (1 + Real.log (H + 6)) ^ 3) +
                  11 * (C * (1 + Real.log (H + 6)) ^ 2)) *
                    Real.log (v / u)) / Real.log x) := by
  rcases exists_dynamicCubicLeftBoundary_logDeriv_and_deriv_le with
    ⟨b, C, D, T0, hb, hC, hD, hT0, hbase⟩
  refine ⟨b, C, D, T0, hb, hC, hD, hT0, ?_⟩
  intro H x h u v hH hx hh hu huv hvH hhH
  rcases hbase H hH with ⟨ha, haThird, hpoint⟩
  let a : ℝ := dynamicCubicLeftBoundary b H
  let LH : ℝ := 1 + Real.log (H + 6)
  have haA : 0 < a := by simpa [a] using ha
  have huTwo : 2 ≤ u := by linarith
  have huPos : 0 < u := lt_of_lt_of_le (by norm_num) huTwo
  have hL0 : 0 ≤ C * LH ^ 2 := mul_nonneg hC (sq_nonneg _)
  have hLH : 0 ≤ LH := by
    dsimp [LH]
    have : 0 < Real.log (H + 6) :=
      Real.log_pos (by linarith [hT0.trans hH] : (1 : ℝ) < H + 6)
    linarith
  have hD0 : 0 ≤ D * LH ^ 3 := mul_nonneg hD (pow_nonneg hLH 3)
  have hdata : ∀ t ∈ Set.Icc u v,
      riemannZeta ((a : ℂ) + I * t) ≠ 0 ∧
        ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ C * LH ^ 2 ∧
        ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D * LH ^ 3 := by
    intro t ht
    have htPos : 0 < t := huPos.trans_le ht.1
    have htAbs : |t| = t := abs_of_pos htPos
    have htLow : T0 + 1 ≤ |t| := by rw [htAbs]; exact hu.trans ht.1
    have htHigh : |t| + 1 ≤ H := by rw [htAbs]; linarith [ht.2, hvH]
    simpa [a, LH] using hpoint t htLow htHigh
  have hscale : ∀ t ∈ Set.Icc u v,
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2 := by
    intro t ht
    have htPos : 0 < t := huPos.trans_le ht.1
    have hnorm : ‖(a : ℂ) + I * t‖ ≤ a + t := by
      calc
        ‖(a : ℂ) + I * t‖ ≤ ‖(a : ℂ)‖ + ‖I * (t : ℂ)‖ := norm_add_le _ _
        _ = a + t := by simp [abs_of_pos haA, abs_of_pos htPos]
    have hatH : a + t ≤ H := by
      have htH : t + 1 ≤ H := by linarith [ht.2, hvH]
      linarith
    calc
      h * ‖(a : ℂ) + I * t‖ ≤ h * (a + t) :=
        mul_le_mul_of_nonneg_left hnorm hh.le
      _ ≤ h * H := mul_le_mul_of_nonneg_left hatH hh.le
      _ ≤ 1 / 2 := hhH
  change ‖∫ t in u..v,
      desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤ _
  simpa [LH] using
    norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
      (a := a) hx hh huTwo huv hL0 hD0
        (fun t ht => (hdata t ht).1)
        (fun t ht => (hdata t ht).2.1)
        (fun t ht => (hdata t ht).2.2) hscale

end ExplicitFormulaResidues
end PrimeNumberTheorem
