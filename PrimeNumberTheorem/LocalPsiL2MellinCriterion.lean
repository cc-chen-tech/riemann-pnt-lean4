import PrimeNumberTheorem.LocalPsiL2ZeroCriterion
import PrimeNumberTheorem.VKEdgePiOverTwoAbelIntegral
import ZeroFreeRegion.MeromorphicAux
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Function.L2Space

open Complex Filter Topology
open Metric Real

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

local instance : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    rw [show (fun p : ℝ × ℂ => p.1 • p.2) =
        fun p : ℝ × ℂ => (p.1 : ℂ) * p.2 by
      funext p
      exact Complex.real_smul]
    fun_prop

/-- The Chebyshev error after the logarithmic change of variables `x = exp y`. -/
def logarithmicPsiError (y : ℝ) : ℝ :=
  chebyshevPsi (Real.exp y) - Real.exp y

/--
Square-integrability of every exponential weighting strictly to the right of
`theta`. This is an analytic upper-bound hypothesis, not an unconditional PNT
estimate.
-/
def WeightedLogPsiL2Above (theta : ℝ) : Prop :=
  ∀ beta : ℝ, theta < beta →
    IntegrableOn
      (fun y : ℝ =>
        (logarithmicPsiError y * Real.exp (-beta * y)) ^ 2)
      (Set.Ioi 0)

private theorem measurable_logarithmicPsiError :
    Measurable logarithmicPsiError := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold logarithmicPsiError
  fun_prop

private theorem integrableOn_exp_neg_mul_sq
    {delta : ℝ} (hdelta : 0 < delta) :
    IntegrableOn
      (fun y : ℝ => (Real.exp (-delta * y)) ^ 2)
      (Set.Ioi 0) := by
  have h :=
    Real.GammaIntegral_convergent
      (show 0 < (1 : ℝ) by norm_num)
  have hscaled :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((1 : ℝ) - 1))
      0 (show 0 < 2 * delta by positivity)).mpr h
  convert hscaled using 1 <;>
    simp only [mul_zero, sub_self, Real.rpow_zero, mul_one]
  funext y
  rw [← Real.exp_add]
  congr 1
  ring

private theorem integrableOn_mul_exp_neg_mul_sq
    {delta : ℝ} (hdelta : 0 < delta) :
    IntegrableOn
      (fun y : ℝ => (y * Real.exp (-delta * y)) ^ 2)
      (Set.Ioi 0) := by
  have h :=
    Real.GammaIntegral_convergent
      (show 0 < (3 : ℝ) by norm_num)
  have hscaled :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1))
      0 (show 0 < 2 * delta by positivity)).mpr h
  have hdiv := hscaled.div_const ((2 * delta) ^ 2)
  convert hdiv using 1
  funext y
  simp only [mul_zero, sub_self, Real.rpow_two]
  rw [div_eq_iff (by positivity : (2 * delta) ^ 2 ≠ 0)]
  rw [← Real.exp_add]
  congr 1
  · ring
  · ring

/--
Weighted logarithmic `L²` control makes the Chebyshev-error Mellin transform
differentiable at every point strictly to the right of the weight exponent.
-/
theorem differentiableAt_mellinPsiError_of_weightedLogPsiL2Above
    {theta : ℝ}
    (hweighted : WeightedLogPsiL2Above theta)
    {s : ℂ}
    (hs : theta < s.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => mellin psiErrorAboveOneComplex (-z))
      s := by
  let beta : ℝ := (theta + s.re) / 2
  let radius : ℝ := (s.re - beta) / 2
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let E : ℝ → ℝ := logarithmicPsiError
  let F : ℂ → ℝ → ℂ := fun z y =>
    (E y : ℂ) * Complex.exp (-z * (y : ℂ))
  let F' : ℂ → ℝ → ℂ := fun z y =>
    (-(y : ℂ)) * F z y
  let bound : ℝ → ℝ := fun y =>
    |E y| * y * Real.exp (-(s.re - radius) * y)
  have hthetaBeta : theta < beta := by
    dsimp [beta]
    linarith
  have hbetaS : beta < s.re := by
    dsimp [beta]
    linarith
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hgap : 0 < s.re - radius - beta := by
    dsimp [radius]
    linarith
  have hweightedInt :=
    hweighted beta hthetaBeta
  have hEmeas : Measurable E := by
    simpa [E] using measurable_logarithmicPsiError
  have hweightedLp :
      MemLp
        (fun y : ℝ => E y * Real.exp (-beta * y))
        2 μ := by
    rw [memLp_two_iff_integrable_sq]
    · simpa [μ, E] using hweightedInt
    · exact
        ((hEmeas.mul (Real.measurable_exp.comp
          (measurable_const.mul measurable_id).neg))
          |>.aestronglyMeasurable).restrict
  have hgapLp :
      MemLp
        (fun y : ℝ =>
          y * Real.exp (-(s.re - radius - beta) * y))
        2 μ := by
    rw [memLp_two_iff_integrable_sq]
    · simpa [μ] using integrableOn_mul_exp_neg_mul_sq hgap
    · fun_prop
  have hboundInt : Integrable bound μ := by
    have hproduct :=
      hweightedLp.abs.integrable_mul hgapLp
    convert hproduct using 1
    funext y
    simp only [bound]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add]
    congr 1
    ring
  have hFmeas :
      ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) μ := by
    filter_upwards [] with z
    exact
      ((hEmeas.complex_ofReal.mul
        (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul measurable_id.complex_ofReal).neg)))
        |>.aestronglyMeasurable).restrict
  have hFint : Integrable (F s) μ := by
    have hgap0 : 0 < s.re - beta := by linarith
    have hgap0Lp :
        MemLp
          (fun y : ℝ => Real.exp (-(s.re - beta) * y))
          2 μ := by
      rw [memLp_two_iff_integrable_sq]
      · simpa [μ] using integrableOn_exp_neg_mul_sq hgap0
      · fun_prop
    have hproduct :=
      hweightedLp.integrable_mul hgap0Lp
    apply hproduct.mono'
    · exact
        ((hEmeas.complex_ofReal.mul
          (Complex.continuous_exp.measurable.comp
            ((measurable_const.mul measurable_id.complex_ofReal).neg)))
          |>.aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      dsimp [F]
      rw [norm_mul, norm_real, Complex.norm_exp, neg_re, mul_re,
        ofReal_re, ofReal_im]
      simp only [mul_zero, sub_zero]
      rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
      ring_nf
      rfl
  have hF'meas : AEStronglyMeasurable (F' s) μ := by
    exact
      ((measurable_id.complex_ofReal.neg.mul
        ((hEmeas.complex_ofReal.mul
          (Complex.continuous_exp.measurable.comp
            ((measurable_const.mul measurable_id.complex_ofReal).neg)))))
        |>.aestronglyMeasurable).restrict
  have hbound :
      ∀ᵐ y ∂μ, ∀ z ∈ Metric.ball s radius,
        ‖F' z y‖ ≤ bound y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    have hrez : s.re - radius < z.re := by
      have hdist : ‖z - s‖ < radius := by
        simpa [dist_eq_norm] using hz
      have hreabs : |z.re - s.re| ≤ ‖z - s‖ := by
        simpa using abs_re_le_norm (z - s)
      linarith
    have hy0 : 0 ≤ y := hy.le
    dsimp [F', F, bound]
    rw [norm_mul, norm_neg, norm_real, norm_mul, norm_real,
      Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im]
    simp only [mul_zero, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg hy0]
    have hexp :
        Real.exp (-z.re * y) ≤
          Real.exp (-(s.re - radius) * y) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_right hrez.le (by linarith))
    gcongr
  have hdiff :
      ∀ᵐ y ∂μ, ∀ z ∈ Metric.ball s radius,
        HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [] with y z hz
    dsimp [F, F']
    convert
      (hasDerivAt_const z (E y : ℂ)).mul
        (((hasDerivAt_id z).neg.mul_const (y : ℂ)).cexp)
      using 1 <;> ring
  have hderiv :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds s hradius)
      hFmeas hFint hF'meas hbound hboundInt hdiff
  have hintegral :
      (fun z : ℂ => ∫ y : ℝ, F z y ∂μ) =
        fun z : ℂ =>
          mellin psiErrorAboveOneComplex (-z) := by
    funext z
    simpa [μ, F, E, logarithmicPsiError] using
      integral_logarithmicPsiError_eq_mellin z
  rw [← hintegral]
  exact hderiv.2.differentiableAt

private theorem logarithmicPsiError_abs_le_exp_growth (y : ℝ) :
    |logarithmicPsiError y| ≤
      (Real.log 4 + 5) * Real.exp y := by
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
  unfold logarithmicPsiError
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [Real.exp_pos y]
  · nlinarith [Real.exp_pos y,
      Real.log_pos (by norm_num : 1 < (4 : ℝ))]

private theorem integrableOn_logarithmicPsiError_sq_Icc
    (a b : ℝ) :
    IntegrableOn
      (fun y : ℝ => logarithmicPsiError y ^ 2)
      (Set.Icc a b) := by
  let B : ℝ :=
    ((Real.log 4 + 5) *
      Real.exp (max a b)) ^ 2
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
  · exact
      (measurable_logarithmicPsiError.pow_const 2
        |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hymax : y ≤ max a b :=
      hy.2.trans (le_max_right a b)
    have hexp :
        Real.exp y ≤ Real.exp (max a b) :=
      Real.exp_le_exp.mpr hymax
    have hcoef : 0 ≤ Real.log 4 + 5 := by positivity
    have habs :=
      (logarithmicPsiError_abs_le_exp_growth y).trans
        (mul_le_mul_of_nonneg_left hexp hcoef)
    have hsq : logarithmicPsiError y ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [sq_abs (logarithmicPsiError y),
        abs_nonneg (logarithmicPsiError y)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq

private theorem integrableOn_weightedLogPsiError_sq_Ioc
    (alpha : ℝ) (n : ℕ) :
    IntegrableOn
      (fun y : ℝ =>
        (logarithmicPsiError y * Real.exp (-alpha * y)) ^ 2)
      (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) := by
  let B : ℝ :=
    ((Real.log 4 + 5) *
      Real.exp ((n : ℝ) + 1) *
      Real.exp (|alpha| * ((n : ℝ) + 1))) ^ 2
  apply IntegrableOn.of_bound
    (measure_Ioc_lt_top.ne) 
  · exact
      ((measurable_logarithmicPsiError.mul
        (Real.measurable_exp.comp
          (measurable_const.mul measurable_id).neg)).pow_const 2
        |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hy0 : 0 ≤ y := by
      exact (Nat.cast_nonneg n).trans hy.1.le
    have hyUpper : y ≤ (n : ℝ) + 1 := hy.2.le
    have hexpY :
        Real.exp y ≤ Real.exp ((n : ℝ) + 1) :=
      Real.exp_le_exp.mpr hyUpper
    have hweightArg :
        -alpha * y ≤ |alpha| * ((n : ℝ) + 1) := by
      calc
        -alpha * y ≤ |alpha| * y := by
          have : -alpha ≤ |alpha| := neg_le_abs alpha
          exact mul_le_mul_of_nonneg_right this hy0
        _ ≤ |alpha| * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hyUpper (abs_nonneg alpha)
    have hweight :
        Real.exp (-alpha * y) ≤
          Real.exp (|alpha| * ((n : ℝ) + 1)) :=
      Real.exp_le_exp.mpr hweightArg
    have hcoef : 0 ≤ Real.log 4 + 5 := by positivity
    have hproduct :
        |logarithmicPsiError y * Real.exp (-alpha * y)| ≤
          (Real.log 4 + 5) * Real.exp ((n : ℝ) + 1) *
            Real.exp (|alpha| * ((n : ℝ) + 1)) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      gcongr
      exact logarithmicPsiError_abs_le_exp_growth y
    have hsq :
        (logarithmicPsiError y * Real.exp (-alpha * y)) ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [
        sq_abs (logarithmicPsiError y * Real.exp (-alpha * y)),
        abs_nonneg (logarithmicPsiError y * Real.exp (-alpha * y))]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq

/--
The local logarithmic second-moment exponent hypothesis implies global
exponentially weighted `L²` integrability on the positive logarithmic axis.
-/
theorem weightedLogPsiL2Above_of_localPsiL2ExponentAtMost
    {ε theta : ℝ}
    (hε : 0 < ε)
    (hthetaNonneg : 0 ≤ theta)
    (hupper : LocalPsiL2ExponentAtMost ε theta) :
    WeightedLogPsiL2Above theta := by
  intro alpha hthetaAlpha
  let beta : ℝ := (theta + alpha) / 2
  let f : ℝ → ℝ := fun y =>
    (logarithmicPsiError y * Real.exp (-alpha * y)) ^ 2
  let block : ℕ → Set ℝ := fun n =>
    Set.Ioc (n : ℝ) ((n : ℝ) + 1)
  have hthetaBeta : theta < beta := by
    dsimp [beta]
    linarith
  have hbetaAlpha : beta < alpha := by
    dsimp [beta]
    linarith
  have halphaPos : 0 < alpha :=
    hthetaNonneg.trans_lt hthetaAlpha
  have hbetaNonneg : 0 ≤ beta :=
    hthetaNonneg.trans hthetaBeta.le
  have hmomentBoundY :=
    (hupper beta hthetaBeta).bound
      (show 0 < (1 : ℝ) by norm_num)
  have hexpNat :
      Tendsto (fun n : ℕ => Real.exp (n : ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hmomentBoundN :=
    hexpNat.eventually hmomentBoundY
  have hlargeN :
      ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ε * n := by
    have htendsto :
        Tendsto (fun n : ℕ => ε * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hε
    exact htendsto.eventually (eventually_ge_atTop 1)
  have hblockInt :
      ∀ n : ℕ, IntegrableOn f (block n) := by
    intro n
    simpa [f, block] using
      integrableOn_weightedLogPsiError_sq_Ioc alpha n
  have hblockBound :
      ∀ᶠ n : ℕ in atTop,
        (∫ y : ℝ in block n, ‖f y‖) ≤
          (n : ℝ) *
            Real.exp (-2 * (alpha - beta) * n) := by
    filter_upwards [hmomentBoundN, hlargeN] with n hnMoment hnLarge
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hnUpper :
        (n : ℝ) + 1 ≤ (1 + ε) * n := by
      nlinarith
    have hsubset :
        block n ⊆
          Set.Icc (n : ℝ) ((1 + ε) * n) := by
      intro y hy
      exact ⟨hy.1.le, hy.2.le.trans hnUpper⟩
    have hrawInt :
        IntegrableOn
          (fun y : ℝ => logarithmicPsiError y ^ 2)
          (Set.Icc (n : ℝ) ((1 + ε) * n)) :=
      integrableOn_logarithmicPsiError_sq_Icc _ _
    have hmajorInt :
        IntegrableOn
          (fun y : ℝ =>
            Real.exp (-2 * alpha * n) *
              logarithmicPsiError y ^ 2)
          (Set.Icc (n : ℝ) ((1 + ε) * n)) :=
      hrawInt.const_mul _
    have hpoint :
        ∀ y ∈ block n,
          ‖f y‖ ≤
            Real.exp (-2 * alpha * n) *
              logarithmicPsiError y ^ 2 := by
      intro y hy
      have hyLower : (n : ℝ) ≤ y := hy.1.le
      have hexp :
          Real.exp (-2 * alpha * y) ≤
            Real.exp (-2 * alpha * n) := by
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hyLower
            (by linarith : -2 * alpha ≤ 0))
      dsimp [f]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        mul_pow, ← Real.exp_two_mul]
      exact mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    have hfirst :
        (∫ y : ℝ in block n, ‖f y‖) ≤
          ∫ y : ℝ in block n,
            Real.exp (-2 * alpha * n) *
              logarithmicPsiError y ^ 2 := by
      exact setIntegral_mono_on
        (hblockInt n).norm
        (hmajorInt.mono_set hsubset)
        measurableSet_Ioc hpoint
    have hsecond :
        (∫ y : ℝ in block n,
            Real.exp (-2 * alpha * n) *
              logarithmicPsiError y ^ 2) ≤
          ∫ y : ℝ in Set.Icc (n : ℝ) ((1 + ε) * n),
            Real.exp (-2 * alpha * n) *
              logarithmicPsiError y ^ 2 := by
      exact setIntegral_mono_set hmajorInt
        (Eventually.of_forall fun y =>
          mul_nonneg (Real.exp_pos _).le (sq_nonneg _))
        hsubset.eventuallyLE
    have hmomentNonneg :
        0 ≤ logarithmicPsiErrorSecondMoment ε (Real.exp n) := by
      unfold logarithmicPsiErrorSecondMoment
      exact integral_nonneg fun y => sq_nonneg _
    have hscaleNonneg :
        0 ≤
          Real.exp
              (2 * beta * Real.log (Real.exp n)) *
            Real.log (Real.exp n) :=
      mul_nonneg (Real.exp_pos _).le
        (by simp)
    have hmoment :
        logarithmicPsiErrorSecondMoment ε (Real.exp n) ≤
          Real.exp (2 * beta * n) * n := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hmomentNonneg,
        abs_of_nonneg hscaleNonneg] using hnMoment
    calc
      (∫ y : ℝ in block n, ‖f y‖) ≤
          ∫ y : ℝ in Set.Icc (n : ℝ) ((1 + ε) * n),
            Real.exp (-2 * alpha * n) *
              logarithmicPsiError y ^ 2 :=
        hfirst.trans hsecond
      _ =
          Real.exp (-2 * alpha * n) *
            logarithmicPsiErrorSecondMoment ε (Real.exp n) := by
        rw [integral_const_mul]
        simp [logarithmicPsiErrorSecondMoment, logarithmicPsiError]
      _ ≤
          Real.exp (-2 * alpha * n) *
            (Real.exp (2 * beta * n) * n) := by
        gcongr
      _ =
          (n : ℝ) *
            Real.exp (-2 * (alpha - beta) * n) := by
        rw [← Real.exp_add]
        ring_nf
  have hblockIntegralSummable :
      Summable fun n : ℕ =>
        ∫ y : ℝ in block n, ‖f y‖ := by
    apply summable_of_isBigO_nat
      (Real.summable_pow_mul_exp_neg_nat_mul 1
        (show 0 < 2 * (alpha - beta) by linarith))
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hblockBound] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg
      (integral_nonneg fun y => norm_nonneg _)]
    simpa using hn
  have hUnion :
      (⋃ n : ℕ, block n) = Set.Ioi (0 : ℝ) := by
    simpa [block] using
      (iUnion_Ioc_map_succ_eq_Ioi
        (f := fun n : ℕ => (n : ℝ))
        (fun n => Nat.cast_nonneg n)
        (by
          rw [bddAbove_def]
          push_neg
          intro a
          obtain ⟨n, hn⟩ := exists_nat_gt a
          exact ⟨(n : ℝ), ⟨n, rfl⟩, hn.le⟩))
  rw [← hUnion]
  exact integrableOn_iUnion_of_summable_integral_norm
    hblockInt hblockIntegralSummable

/--
Differentiability of the cutoff Chebyshev-error Mellin transform on a right
half-plane excludes zeta zeros there.

This is the analytic ODE part of the Landau converse, separated from any
particular sufficient condition for Mellin differentiability. In particular,
the premise is not asserted unconditionally.
-/
theorem riemannZeta_ne_zero_of_mellinPsiError_differentiable
    {theta : ℝ}
    (hthetaNonneg : 0 ≤ theta)
    (hthetaOne : theta < 1)
    (hmellin :
      ∀ s : ℂ,
        theta < s.re →
          DifferentiableAt ℂ
            (fun z : ℂ =>
              mellin psiErrorAboveOneComplex (-z))
            s) :
    ∀ rho : ℂ,
      theta < rho.re →
      rho.re < 1 →
      riemannZeta rho ≠ 0 := by
  let U : Set ℂ := {s : ℂ | theta < s.re}
  let M : ℂ → ℂ := fun s =>
    mellin psiErrorAboveOneComplex (-s)
  let G : ℂ → ℂ := fun s => -(1 + s * M s)
  let Q : ℂ → ℂ := ZeroFreeRegion.riemannZetaPoleUnitAtOne
  have hUOpen : IsOpen U := by
    exact isOpen_lt continuous_const Complex.continuous_re
  have hUPreconnected : IsPreconnected U := by
    simpa [U] using (convex_halfSpace_re_gt theta).isPreconnected
  have hQ : AnalyticOnNhd ℂ Q U := by
    exact
      ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
        hthetaNonneg
  have hMDiff : DifferentiableOn ℂ M U := by
    intro s hs
    exact (hmellin s hs).differentiableWithinAt
  have hM : AnalyticOnNhd ℂ M U :=
    hMDiff.analyticOnNhd hUOpen
  have hG : AnalyticOnNhd ℂ G U := by
    dsimp only [G]
    exact (analyticOnNhd_const.add (analyticOnNhd_id.mul hM)).neg
  have hoverlap :
      ∀ s : ℂ, 1 < s.re → deriv Q s = G s * Q s := by
    intro s hs
    simpa [Q, G, M] using
      ZeroFreeRegion.deriv_riemannZetaPoleUnitAtOne_eq_mellin_coefficient_mul
        hs
  let x : ℂ := (max theta 1 + 1 : ℝ)
  have hxU : x ∈ U := by
    change theta < (max theta 1 + 1 : ℝ)
    linarith [le_max_left theta 1]
  have hxOverlap : 1 < x.re := by
    change 1 < (max theta 1 + 1 : ℝ)
    linarith [le_max_right theta 1]
  have hlocal : deriv Q =ᶠ[𝓝 x] G * Q := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hxOverlap] with s hs
    exact hoverlap s hs
  have hODE : Set.EqOn (deriv Q) (G * Q) U :=
    hQ.deriv.eqOn_of_preconnected_of_eventuallyEq
      (hG.mul hQ) hUPreconnected hxU hlocal
  have hOneU : (1 : ℂ) ∈ U := by
    change theta < (1 : ℂ).re
    simpa using hthetaOne
  have hQOne : Q 1 ≠ 0 := by
    simp [Q, ZeroFreeRegion.riemannZetaPoleUnitAtOne_one]
  have hQNe : ∀ s ∈ U, Q s ≠ 0 :=
    ZeroFreeRegion.analyticOnNhd_ne_zero_of_deriv_eq_mul_self
      hUOpen hUPreconnected hQ hG hOneU hQOne
      (fun s hs => hODE hs)
  intro rho hthetaRho hrhoOne hzero
  have hrhoU : rho ∈ U := hthetaRho
  have hrhoZero : rho ≠ 0 := by
    intro h
    subst rho
    norm_num at hthetaRho
    linarith
  have hrhoNotOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrhoOne
  have hQValue :
      Q rho = (rho - 1) * riemannZeta rho :=
    ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
      hrhoZero hrhoNotOne
  exact hQNe rho hrhoU (by simp [hQValue, hzero])

/--
An RH-strength local logarithmic second-moment upper bound implies the Riemann
hypothesis. Unlike the earlier positive-ordinate oscillation converse, the
Mellin continuation argument also excludes hypothetical real zeros in the
open right half of the critical strip.

This remains a conditional criterion: no unconditional proof of the
`LocalPsiL2ExponentAtMost` premise is supplied.
-/
theorem riemannHypothesis_of_localPsiL2ExponentAtMost
    {ε : ℝ}
    (hε : 0 < ε)
    (hupper : LocalPsiL2ExponentAtMost ε (1 / 2)) :
    RiemannHypothesis.Statement := by
  have hweighted :
      WeightedLogPsiL2Above (1 / 2) :=
    weightedLogPsiL2Above_of_localPsiL2ExponentAtMost
      hε (by norm_num) hupper
  have hmellin :
      ∀ s : ℂ,
        (1 / 2 : ℝ) < s.re →
          DifferentiableAt ℂ
            (fun z : ℂ =>
              mellin psiErrorAboveOneComplex (-z))
            s := by
    intro s hs
    exact
      differentiableAt_mellinPsiError_of_weightedLogPsiL2Above
        hweighted hs
  have hzeroFree :
      ∀ rho : ℂ,
        (1 / 2 : ℝ) < rho.re →
        rho.re < 1 →
        riemannZeta rho ≠ 0 :=
    riemannZeta_ne_zero_of_mellinPsiError_differentiable
      (by norm_num) (by norm_num) hmellin
  intro rho hrho
  apply le_antisymm
  · by_contra hle
    have hhalf : (1 / 2 : ℝ) < rho.re :=
      lt_of_not_ge hle
    exact (hzeroFree rho hhalf hrho.2.2) hrho.1
  · by_contra hle
    have hrhoHalf : rho.re < (1 / 2 : ℝ) :=
      lt_of_not_ge hle
    let reflected : ℂ :=
      RiemannVonMangoldt.criticalLineReflection rho
    have hreflectedZero :
        RiemannHypothesis.IsNontrivialZero reflected :=
      RiemannVonMangoldt.isNontrivialZero_criticalLineReflection hrho
    have hreflectedHalf :
        (1 / 2 : ℝ) < reflected.re := by
      dsimp [reflected]
      simp only [RiemannVonMangoldt.criticalLineReflection_re]
      linarith
    exact
      (hzeroFree reflected hreflectedHalf hreflectedZero.2.2)
        hreflectedZero.1

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
