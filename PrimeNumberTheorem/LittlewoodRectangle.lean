import MathlibAux.BoundaryRectResidue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import ZeroFreeRegion.MeromorphicAux

open Complex Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- The imaginary part of a positively oriented rectangular boundary integral
is the bottom imaginary integral minus the top one, plus the right real
integral minus the left one. -/
theorem im_boundaryRectIntegral_eq_four_edges
    {G : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (hbottom : IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (y0 : ℂ) * I))
      MeasureTheory.volume x0 x1)
    (htop : IntervalIntegrable
      (fun x : ℝ => G ((x : ℂ) + (y1 : ℂ) * I))
      MeasureTheory.volume x0 x1)
    (hright : IntervalIntegrable
      (fun y : ℝ => G ((x1 : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume y0 y1)
    (hleft : IntervalIntegrable
      (fun y : ℝ => G ((x0 : ℂ) + (y : ℂ) * I))
      MeasureTheory.volume y0 y1) :
    (MathlibAux.boundaryRectIntegral G x0 x1 y0 y1).im =
      (∫ x in x0..x1,
          (G ((x : ℂ) + (y0 : ℂ) * I)).im) -
        (∫ x in x0..x1,
          (G ((x : ℂ) + (y1 : ℂ) * I)).im) +
        (∫ y in y0..y1,
          (G ((x1 : ℂ) + (y : ℂ) * I)).re) -
        (∫ y in y0..y1,
          (G ((x0 : ℂ) + (y : ℂ) * I)).re) := by
  have hbottomIm := Complex.imCLM.intervalIntegral_comp_comm hbottom
  have htopIm := Complex.imCLM.intervalIntegral_comp_comm htop
  have hrightRe := Complex.reCLM.intervalIntegral_comp_comm hright
  have hleftRe := Complex.reCLM.intervalIntegral_comp_comm hleft
  simp only [Complex.imCLM_apply] at hbottomIm htopIm
  simp only [Complex.reCLM_apply] at hrightRe hleftRe
  simp only [MathlibAux.boundaryRectIntegral, Complex.sub_im, Complex.add_im,
    smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_add]
  rw [← hbottomIm, ← htopIm, ← hrightRe, ← hleftRe]

/-- Along a vertical line, the derivative of `log ‖f‖` is the negative
imaginary part of the logarithmic derivative of `f`. -/
theorem hasDerivAt_log_norm_vertical
    {f : ℂ → ℂ} {sigma t : ℝ}
    (hf : AnalyticAt ℂ f ((sigma : ℂ) + I * (t : ℂ)))
    (hne : f ((sigma : ℂ) + I * (t : ℂ)) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖)
      (-(logDeriv f ((sigma : ℂ) + I * (t : ℂ))).im) t := by
  let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
  have hparam :
      HasDerivAt (fun z : ℂ => (sigma : ℂ) + I * z) I (t : ℂ) := by
    simpa using
      ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (sigma : ℂ)
  have hcompComplex :
      HasDerivAt (fun z : ℂ => f ((sigma : ℂ) + I * z))
        (deriv f s * I) (t : ℂ) := by
    simpa [s, Function.comp_def] using hf.differentiableAt.hasDerivAt.comp (t : ℂ) hparam
  have hvertical :
      HasDerivAt (fun u : ℝ => f ((sigma : ℂ) + I * (u : ℂ)))
        (deriv f s * I) t := by
    simpa using hcompComplex.comp_ofReal
  have hnormSq := hvertical.norm_sq
  have hnormSqNe : ‖f s‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (by simpa [s] using hne))
  have hlogNormSq := hnormSq.log hnormSqNe
  have hhalf := hlogNormSq.const_mul (2 : ℝ)⁻¹
  convert hhalf using 1 <;> (try rfl)
  · funext u
    rw [Real.log_pow]
    ring
  · rw [logDeriv_apply, hf.differentiableAt.hasDerivAt.deriv]
    simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.div_im,
      Complex.normSq_eq_norm_sq]
    field_simp
    ring

/-- Along a vertical line, the derivative of the principal argument of an
analytic function staying in the slit plane is the real part of its
logarithmic derivative. -/
theorem hasDerivAt_im_log_vertical_of_analyticAt
    {f : ℂ → ℂ} {sigma t : ℝ}
    (hf : AnalyticAt ℂ f ((sigma : ℂ) + I * (t : ℂ)))
    (hslit : f ((sigma : ℂ) + I * (t : ℂ)) ∈ Complex.slitPlane) :
    HasDerivAt
      (fun u : ℝ =>
        (Complex.log (f ((sigma : ℂ) + I * (u : ℂ)))).im)
      (logDeriv f ((sigma : ℂ) + I * (t : ℂ))).re t := by
  let s : ℂ := (sigma : ℂ) + I * (t : ℂ)
  have hparam :
      HasDerivAt (fun z : ℂ => (sigma : ℂ) + I * z) I (t : ℂ) := by
    simpa using
      ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (sigma : ℂ)
  have hcompComplex :
      HasDerivAt (fun z : ℂ => f ((sigma : ℂ) + I * z))
        (deriv f s * I) (t : ℂ) := by
    simpa [s, Function.comp_def] using hf.differentiableAt.hasDerivAt.comp (t : ℂ) hparam
  have hvertical :
      HasDerivAt (fun u : ℝ => f ((sigma : ℂ) + I * (u : ℂ)))
        (deriv f s * I) t := by
    simpa using hcompComplex.comp_ofReal
  have hlog := hvertical.clog_real (by simpa [s] using hslit)
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
  convert him using 1 <;> (try rfl)
  change (deriv f s / f s).re = (deriv f s * I / f s).im
  rw [show deriv f s * I / f s = I * (deriv f s / f s) by ring]
  simp

/-- Integration by parts on a vertical edge.  This converts the imaginary
part of the logarithmic derivative into endpoint and `log ‖f‖` terms. -/
theorem intervalIntegral_mul_neg_im_logDeriv_vertical_eq
    {f : ℂ → ℂ} {sigma a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0)
    (hint : IntervalIntegrable
      (fun u : ℝ => -(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)
      MeasureTheory.volume a b) :
    (∫ u in a..b,
        u * (-(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)) =
      b * Real.log ‖f ((sigma : ℂ) + I * (b : ℂ))‖ -
        a * Real.log ‖f ((sigma : ℂ) + I * (a : ℂ))‖ -
          ∫ u in a..b,
            Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖ := by
  simpa only [one_mul] using
    (intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (u := fun u : ℝ => u)
      (v := fun u : ℝ => Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖)
      (u' := fun _ : ℝ => 1)
      (v' := fun u : ℝ =>
        -(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)
      (fun u _ => hasDerivAt_id u)
      (fun u hu => hasDerivAt_log_norm_vertical (hf u hu) (hne u hu))
      intervalIntegrable_const hint)

/-- The imaginary part of the logarithmic derivative is continuous along a
compact vertical segment on which `f` is analytic and nonvanishing. -/
theorem continuousOn_neg_im_logDeriv_vertical
    {f : ℂ → ℂ} {sigma a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0) :
    ContinuousOn
      (fun u : ℝ => -(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)
      [[a, b]] := by
  intro u hu
  have hmap :
      ContinuousAt (fun v : ℝ => (sigma : ℂ) + I * (v : ℂ)) u := by
    fun_prop
  have hlog : ContinuousAt
      (fun v : ℝ => logDeriv f ((sigma : ℂ) + I * (v : ℂ))) u := by
    simpa [Function.comp_def] using
      ((ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
        (hf u hu) (hne u hu)).continuousAt.comp_of_eq hmap rfl)
  exact (Complex.continuous_im.continuousAt.comp hlog).neg.continuousWithinAt

/-- Vertical-edge integration by parts with integrability discharged by
analyticity and nonvanishing on the whole segment. -/
theorem intervalIntegral_mul_neg_im_logDeriv_vertical_eq_of_analytic
    {f : ℂ → ℂ} {sigma a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0) :
    (∫ u in a..b,
        u * (-(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im)) =
      b * Real.log ‖f ((sigma : ℂ) + I * (b : ℂ))‖ -
        a * Real.log ‖f ((sigma : ℂ) + I * (a : ℂ))‖ -
          ∫ u in a..b,
            Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖ :=
  intervalIntegral_mul_neg_im_logDeriv_vertical_eq hf hne
    (continuousOn_neg_im_logDeriv_vertical hf hne).intervalIntegrable

/-- A real-weighted vertical logarithmic derivative splits into an argument
variation term and the endpoint-minus-integral expression for `log ‖f‖`.
When `sigma = anchor`, the argument variation term vanishes. -/
theorem intervalIntegral_re_weighted_logDeriv_vertical_eq_of_analytic
    {f : ℂ → ℂ} {sigma anchor a b : ℝ}
    (hf : ∀ u ∈ [[a, b]],
      AnalyticAt ℂ f ((sigma : ℂ) + I * (u : ℂ)))
    (hne : ∀ u ∈ [[a, b]],
      f ((sigma : ℂ) + I * (u : ℂ)) ≠ 0) :
    (∫ u in a..b,
        ((((sigma : ℂ) + I * (u : ℂ) - (anchor : ℂ)) *
          logDeriv f ((sigma : ℂ) + I * (u : ℂ))).re)) =
      (sigma - anchor) *
          (∫ u in a..b,
            (logDeriv f ((sigma : ℂ) + I * (u : ℂ))).re) +
        b * Real.log ‖f ((sigma : ℂ) + I * (b : ℂ))‖ -
        a * Real.log ‖f ((sigma : ℂ) + I * (a : ℂ))‖ -
        ∫ u in a..b,
          Real.log ‖f ((sigma : ℂ) + I * (u : ℂ))‖ := by
  have hreCont : ContinuousOn
      (fun u : ℝ =>
        (logDeriv f ((sigma : ℂ) + I * (u : ℂ))).re) [[a, b]] := by
    intro u hu
    have hmap :
        ContinuousAt (fun v : ℝ => (sigma : ℂ) + I * (v : ℂ)) u := by
      fun_prop
    have hlog : ContinuousAt
        (fun v : ℝ => logDeriv f ((sigma : ℂ) + I * (v : ℂ))) u := by
      simpa [Function.comp_def] using
        ((ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
          (hf u hu) (hne u hu)).continuousAt.comp_of_eq hmap rfl)
    exact Complex.continuous_re.continuousAt.comp hlog |>.continuousWithinAt
  have hnegImCont := continuousOn_neg_im_logDeriv_vertical hf hne
  have hreInt : IntervalIntegrable
      (fun u : ℝ =>
        (logDeriv f ((sigma : ℂ) + I * (u : ℂ))).re)
      MeasureTheory.volume a b := hreCont.intervalIntegrable
  have hweightedImInt : IntervalIntegrable
      (fun u : ℝ =>
        u * (-(logDeriv f ((sigma : ℂ) + I * (u : ℂ))).im))
      MeasureTheory.volume a b :=
    (continuousOn_id.mul hnegImCont).intervalIntegrable
  calc
    (∫ u in a..b,
        ((((sigma : ℂ) + I * (u : ℂ) - (anchor : ℂ)) *
          logDeriv f ((sigma : ℂ) + I * (u : ℂ))).re)) =
        ∫ u in a..b,
          (sigma - anchor) *
              (logDeriv f ((sigma : ℂ) + I * (u : ℂ))).re +
            u * (-(logDeriv f
              ((sigma : ℂ) + I * (u : ℂ))).im) := by
      apply intervalIntegral.integral_congr
      intro u hu
      simp only [Complex.mul_re, Complex.sub_re, Complex.add_re,
        Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, zero_add, sub_zero]
      ring
    _ = (sigma - anchor) *
          (∫ u in a..b,
            (logDeriv f ((sigma : ℂ) + I * (u : ℂ))).re) +
        ∫ u in a..b,
          u * (-(logDeriv f
            ((sigma : ℂ) + I * (u : ℂ))).im) := by
      rw [intervalIntegral.integral_add
        (IntervalIntegrable.const_mul hreInt (sigma - anchor)) hweightedImInt]
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      rw [intervalIntegral_mul_neg_im_logDeriv_vertical_eq_of_analytic hf hne]
      ring

/-- Along a horizontal line, the derivative of `log ‖f‖` is the real part
of the logarithmic derivative of `f`. -/
theorem hasDerivAt_log_norm_horizontal
    {f : ℂ → ℂ} {x y : ℝ}
    (hf : AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I))
    (hne : f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    HasDerivAt
      (fun u : ℝ => Real.log ‖f ((u : ℂ) + (y : ℂ) * I)‖)
      (logDeriv f ((x : ℂ) + (y : ℂ) * I)).re x := by
  let s : ℂ := (x : ℂ) + (y : ℂ) * I
  have hparam :
      HasDerivAt (fun z : ℂ => z + (y : ℂ) * I) 1 (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)
  have hcompComplex :
      HasDerivAt (fun z : ℂ => f (z + (y : ℂ) * I))
        (deriv f s) (x : ℂ) := by
    simpa [s, Function.comp_def] using hf.differentiableAt.hasDerivAt.comp (x : ℂ) hparam
  have hhorizontal :
      HasDerivAt (fun u : ℝ => f ((u : ℂ) + (y : ℂ) * I))
        (deriv f s) x := by
    simpa using hcompComplex.comp_ofReal
  have hnormSq := hhorizontal.norm_sq
  have hnormSqNe : ‖f s‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (by simpa [s] using hne))
  have hlogNormSq := hnormSq.log hnormSqNe
  have hhalf := hlogNormSq.const_mul (2 : ℝ)⁻¹
  convert hhalf using 1 <;> (try rfl)
  · funext u
    rw [Real.log_pow]
    ring
  · rw [logDeriv_apply, hf.differentiableAt.hasDerivAt.deriv]
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    rw [Complex.div_re, Complex.normSq_eq_norm_sq]
    field_simp
    ring

/-- The logarithmic derivative is continuous along a compact horizontal
segment on which `f` is analytic and nonvanishing. -/
theorem continuousOn_logDeriv_horizontal
    {f : ℂ → ℂ} {y a b : ℝ}
    (hf : ∀ x ∈ [[a, b]],
      AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I))
    (hne : ∀ x ∈ [[a, b]],
      f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    ContinuousOn
      (fun x : ℝ => logDeriv f ((x : ℂ) + (y : ℂ) * I))
      [[a, b]] := by
  intro x hx
  have hmap : ContinuousAt
      (fun u : ℝ => (u : ℂ) + (y : ℂ) * I) x := by
    fun_prop
  simpa [Function.comp_def] using
    ((ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
      (hf x hx) (hne x hx)).continuousAt.comp_of_eq hmap rfl).continuousWithinAt

/-- The horizontal integral of the real part of `f'/f` is the change in
`log ‖f‖`. -/
theorem intervalIntegral_re_logDeriv_horizontal_eq_logNorm_sub
    {f : ℂ → ℂ} {y a b : ℝ}
    (hf : ∀ x ∈ [[a, b]],
      AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I))
    (hne : ∀ x ∈ [[a, b]],
      f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    (∫ x in a..b,
        (logDeriv f ((x : ℂ) + (y : ℂ) * I)).re) =
      Real.log ‖f ((b : ℂ) + (y : ℂ) * I)‖ -
        Real.log ‖f ((a : ℂ) + (y : ℂ) * I)‖ := by
  have hlogCont := continuousOn_logDeriv_horizontal hf hne
  have hreCont : ContinuousOn
      (fun x : ℝ =>
        (logDeriv f ((x : ℂ) + (y : ℂ) * I)).re) [[a, b]] :=
    Complex.continuous_re.comp_continuousOn hlogCont
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_log_norm_horizontal (hf x hx) (hne x hx))
    hreCont.intervalIntegrable

/-- A horizontal weighted logarithmic derivative splits into its weighted
imaginary part and the endpoint change of `log ‖f‖`. -/
theorem intervalIntegral_im_weighted_logDeriv_horizontal_eq_of_analytic
    {f : ℂ → ℂ} {anchor y a b : ℝ}
    (hf : ∀ x ∈ [[a, b]],
      AnalyticAt ℂ f ((x : ℂ) + (y : ℂ) * I))
    (hne : ∀ x ∈ [[a, b]],
      f ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    (∫ x in a..b,
        ((((x : ℂ) + (y : ℂ) * I - (anchor : ℂ)) *
          logDeriv f ((x : ℂ) + (y : ℂ) * I))).im) =
      (∫ x in a..b,
        (x - anchor) *
          (logDeriv f ((x : ℂ) + (y : ℂ) * I)).im) +
      y * (Real.log ‖f ((b : ℂ) + (y : ℂ) * I)‖ -
        Real.log ‖f ((a : ℂ) + (y : ℂ) * I)‖) := by
  have hlogCont := continuousOn_logDeriv_horizontal hf hne
  have hreCont : ContinuousOn
      (fun x : ℝ =>
        (logDeriv f ((x : ℂ) + (y : ℂ) * I)).re) [[a, b]] :=
    Complex.continuous_re.comp_continuousOn hlogCont
  have himCont : ContinuousOn
      (fun x : ℝ =>
        (logDeriv f ((x : ℂ) + (y : ℂ) * I)).im) [[a, b]] :=
    Complex.continuous_im.comp_continuousOn hlogCont
  have hweightedImInt : IntervalIntegrable
      (fun x : ℝ => (x - anchor) *
        (logDeriv f ((x : ℂ) + (y : ℂ) * I)).im)
      MeasureTheory.volume a b :=
    ((continuousOn_id.sub continuousOn_const).mul himCont).intervalIntegrable
  have hyReInt : IntervalIntegrable
      (fun x : ℝ => y *
        (logDeriv f ((x : ℂ) + (y : ℂ) * I)).re)
      MeasureTheory.volume a b :=
    (continuousOn_const.mul hreCont).intervalIntegrable
  calc
    (∫ x in a..b,
        ((((x : ℂ) + (y : ℂ) * I - (anchor : ℂ)) *
          logDeriv f ((x : ℂ) + (y : ℂ) * I))).im) =
        ∫ x in a..b,
          (x - anchor) *
              (logDeriv f ((x : ℂ) + (y : ℂ) * I)).im +
            y * (logDeriv f ((x : ℂ) + (y : ℂ) * I)).re := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [Complex.mul_im, Complex.sub_re, Complex.add_re,
        Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_re,
        Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, add_zero, zero_add, sub_zero]
      ring
    _ = (∫ x in a..b,
          (x - anchor) *
            (logDeriv f ((x : ℂ) + (y : ℂ) * I)).im) +
        ∫ x in a..b,
          y * (logDeriv f ((x : ℂ) + (y : ℂ) * I)).re := by
      rw [intervalIntegral.integral_add hweightedImInt hyReInt]
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral_re_logDeriv_horizontal_eq_logNorm_sub hf hne]

/-- Weighted argument-principle identity on an axis-parallel rectangle.

The hypotheses identify all zeros in the closed rectangle and supply their
analytic multiplicities.  Strict interior containment excludes boundary
zeros.  Removing the finite logarithmic principal parts gives an analytic
remainder, so the weighted rectangle residue formula applies without any
simple-zero assumption. -/
theorem boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ) (anchor : ℂ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1) :
    MathlibAux.boundaryRectIntegral
        (fun z : ℂ => (z - anchor) * logDeriv f z)
        x0 x1 y0 y1 =
      (2 * Real.pi * I) *
        ∑ rho ∈ poles, (rho - anchor) * (multiplicity rho : ℂ) := by
  classical
  let U : Set ℂ := [[x0, x1]] ×ℂ [[y0, y1]]
  let raw : ℂ → ℂ := fun z =>
    logDeriv f z -
      ∑ rho ∈ poles, (multiplicity rho : ℂ) * (z - rho)⁻¹
  let regular : ℂ → ℂ := toMeromorphicNFOn raw U
  have hfU : AnalyticOnNhd ℂ f U := by
    simpa [U] using hf
  have hzeroU : ∀ z ∈ U, f z = 0 ↔ z ∈ poles := by
    simpa [U] using hzero
  have hrawMeromorphic : MeromorphicOn raw U := by
    simpa [raw] using
      ZeroFreeRegion.meromorphicOn_logDeriv_sub_finset_principalParts
        hfU.meromorphicOn poles multiplicity
  have hregular : AnalyticOnNhd ℂ regular U := by
    dsimp [regular]
    exact
      ZeroFreeRegion.analyticOnNhd_toMeromorphicNFOn_logDeriv_sub_finset_principalParts
        hfU poles multiplicity hzeroU horder
  have hboundaryNonzero : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        f z ≠ 0 := by
    intro z hz hnot hzeroz
    exact hnot (hpoles z ((hzeroU z hz).mp hzeroz))
  have hrawAnalyticBoundary : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        AnalyticAt ℂ raw z := by
    intro z hz hnot
    have hlog : AnalyticAt ℂ (fun w : ℂ => logDeriv f w) z := by
      change AnalyticAt ℂ (deriv f / f) z
      exact (hfU z hz).deriv.div (hfU z hz) (hboundaryNonzero z hz hnot)
    have hsum : AnalyticAt ℂ
        (fun w : ℂ =>
          ∑ rho ∈ poles, (multiplicity rho : ℂ) * (w - rho)⁻¹) z := by
      apply Finset.analyticAt_fun_sum
      intro rho hrho
      have hzr : z ≠ rho := by
        intro heq
        subst z
        exact hnot (hpoles rho hrho)
      exact analyticAt_const.mul
        ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hzr))
    convert hlog.sub hsum using 1 <;> (try rfl)
  have hregularEqBoundary : ∀ z ∈ U,
      ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) →
        regular z = raw z := by
    intro z hz hnot
    dsimp [regular]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hrawMeromorphic hz]
    rw [toMeromorphicNFAt_eq_self.2
      (hrawAnalyticBoundary z hz hnot).meromorphicNFAt]
  have hcontour :
      MathlibAux.boundaryRectIntegral
          (fun z : ℂ => (z - anchor) * logDeriv f z)
          x0 x1 y0 y1 =
        MathlibAux.boundaryRectIntegral
          (fun z : ℂ =>
            (z - anchor) *
              (regular z +
                ∑ rho ∈ poles,
                  (z - rho)⁻¹ * (multiplicity rho : ℂ)))
          x0 x1 y0 y1 := by
    apply MathlibAux.boundaryRectIntegral_congr_of_eqOn_boundary
    intro z hz hnot
    have hzU : z ∈ U := by simpa [U] using hz
    have hnot' :
        ¬(x0 < z.re ∧ z.re < x1 ∧ y0 < z.im ∧ z.im < y1) := by
      intro hinside
      apply hnot
      rw [mem_reProdIm]
      exact ⟨⟨hinside.1, hinside.2.1⟩,
        hinside.2.2.1, hinside.2.2.2⟩
    rw [hregularEqBoundary z hzU hnot']
    dsimp [raw]
    have hsumComm :
        (∑ rho ∈ poles,
            (multiplicity rho : ℂ) * (z - rho)⁻¹) =
          ∑ rho ∈ poles,
            (z - rho)⁻¹ * (multiplicity rho : ℂ) := by
      apply Finset.sum_congr rfl
      intro rho hrho
      ring
    rw [hsumComm]
    ring
  rw [hcontour]
  exact
    MathlibAux.boundaryRectIntegral_eq_finite_simple_pole_weighted_residue_sum_of_differentiableOn
      poles (fun rho => (multiplicity rho : ℂ)) anchor
      hregular.differentiableOn hpoles

/-- Taking imaginary parts in the weighted argument principle expresses the
real weighted zero count as the four oriented edge integrals. -/
theorem two_pi_mul_zeroMultiplicityWeightedRealSum_eq_four_edges
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1)
    (hbottom : IntervalIntegrable
      (fun x : ℝ =>
        (((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x : ℂ) + (y0 : ℂ) * I)))
      MeasureTheory.volume x0 x1)
    (htop : IntervalIntegrable
      (fun x : ℝ =>
        (((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x : ℂ) + (y1 : ℂ) * I)))
      MeasureTheory.volume x0 x1)
    (hright : IntervalIntegrable
      (fun y : ℝ =>
        (((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x1 : ℂ) + (y : ℂ) * I)))
      MeasureTheory.volume y0 y1)
    (hleft : IntervalIntegrable
      (fun y : ℝ =>
        (((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x0 : ℂ) + (y : ℂ) * I)))
      MeasureTheory.volume y0 y1) :
    (2 * Real.pi) *
        ∑ rho ∈ poles,
          (rho.re - x0) * (multiplicity rho : ℝ) =
      (∫ x in x0..x1,
          ((((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x : ℂ) + (y0 : ℂ) * I))).im) -
        (∫ x in x0..x1,
          ((((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x : ℂ) + (y1 : ℂ) * I))).im) +
        (∫ y in y0..y1,
          ((((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x1 : ℂ) + (y : ℂ) * I))).re) -
        (∫ y in y0..y1,
          ((((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
            logDeriv f ((x0 : ℂ) + (y : ℂ) * I))).re) := by
  classical
  have hres :=
    boundaryRectIntegral_weighted_logDeriv_eq_zeroMultiplicitySum
      poles multiplicity (x0 : ℂ) hf hzero horder hpoles
  have hedges := im_boundaryRectIntegral_eq_four_edges
    (G := fun z : ℂ => (z - (x0 : ℂ)) * logDeriv f z)
    hbottom htop hright hleft
  have him := congrArg Complex.im hres
  rw [hedges] at him
  have hsumRe :
      (∑ rho ∈ poles,
          (rho - (x0 : ℂ)) * (multiplicity rho : ℂ)).re =
        ∑ rho ∈ poles,
          (rho.re - x0) * (multiplicity rho : ℝ) := by
    simp [Complex.re_sum, Complex.mul_re]
  rw [Complex.mul_im, hsumRe] at him
  simpa using him.symm

/-- Multiplicity mass of the selected zeros on or to the right of a vertical
line. -/
noncomputable def zeroMultiplicityMassAtOrRight
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ) (critical : ℝ) : ℝ :=
  ∑ rho ∈ poles.filter (fun rho => critical ≤ rho.re),
    (multiplicity rho : ℝ)

/-- Every zero on or to the right of `critical` contributes at least
`critical - x0` to the Littlewood weighted divisor sum. -/
theorem sub_mul_zeroMultiplicityMassAtOrRight_le_weightedRealSum
    {poles : Finset ℂ} {multiplicity : ℂ → ℕ} {x0 critical : ℝ}
    (hleft : ∀ rho ∈ poles, x0 ≤ rho.re) :
    (critical - x0) *
        zeroMultiplicityMassAtOrRight poles multiplicity critical ≤
      ∑ rho ∈ poles, (rho.re - x0) * (multiplicity rho : ℝ) := by
  classical
  unfold zeroMultiplicityMassAtOrRight
  rw [Finset.mul_sum]
  calc
    (∑ rho ∈ poles.filter (fun rho => critical ≤ rho.re),
        (critical - x0) * (multiplicity rho : ℝ)) ≤
        ∑ rho ∈ poles.filter (fun rho => critical ≤ rho.re),
          (rho.re - x0) * (multiplicity rho : ℝ) := by
      apply Finset.sum_le_sum
      intro rho hrho
      have hcritical : critical ≤ rho.re := (Finset.mem_filter.mp hrho).2
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right hcritical x0) (Nat.cast_nonneg _)
    _ ≤ ∑ rho ∈ poles,
        (rho.re - x0) * (multiplicity rho : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset (fun rho : ℂ => critical ≤ rho.re) poles)
      intro rho hrho _
      exact mul_nonneg (sub_nonneg.mpr (hleft rho hrho)) (Nat.cast_nonneg _)

/-- Exact Littlewood rectangle identity with all corner logarithms cancelled.

The three terms after the two vertical `log ‖f‖` integrals are the bottom,
top, and far-right argument remainders.  No asymptotic estimate for those
remainders is built into this theorem. -/
theorem littlewoodRectangle_zeroMultiplicityWeightedRealSum_eq_logNormEdges
    {f : ℂ → ℂ} {x0 x1 y0 y1 : ℝ}
    (_hx : x0 < x1) (_hy : y0 < y1)
    (poles : Finset ℂ) (multiplicity : ℂ → ℕ)
    (hf : AnalyticOnNhd ℂ f ([[x0, x1]] ×ℂ [[y0, y1]]))
    (hzero : ∀ z ∈ ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ),
      f z = 0 ↔ z ∈ poles)
    (horder : ∀ rho ∈ poles,
      analyticOrderAt f rho = multiplicity rho)
    (hpoles : ∀ rho ∈ poles,
      x0 < rho.re ∧ rho.re < x1 ∧ y0 < rho.im ∧ rho.im < y1) :
    (2 * Real.pi) *
        ∑ rho ∈ poles,
          (rho.re - x0) * (multiplicity rho : ℝ) =
      (∫ y in y0..y1,
          Real.log ‖f ((x0 : ℂ) + (y : ℂ) * I)‖) -
      (∫ y in y0..y1,
          Real.log ‖f ((x1 : ℂ) + (y : ℂ) * I)‖) +
      (∫ x in x0..x1,
          (x - x0) *
            (logDeriv f ((x : ℂ) + (y0 : ℂ) * I)).im) -
      (∫ x in x0..x1,
          (x - x0) *
            (logDeriv f ((x : ℂ) + (y1 : ℂ) * I)).im) +
      (x1 - x0) *
        (∫ y in y0..y1,
          (logDeriv f ((x1 : ℂ) + (y : ℂ) * I)).re) := by
  have hbottomA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y0 : ℂ) * I) := by
    intro x hxmem
    apply hf
    simpa [mem_reProdIm] using
      And.intro hxmem (left_mem_uIcc : y0 ∈ [[y0, y1]])
  have htopA : ∀ x ∈ [[x0, x1]],
      AnalyticAt ℂ f ((x : ℂ) + (y1 : ℂ) * I) := by
    intro x hxmem
    apply hf
    simpa [mem_reProdIm] using
      And.intro hxmem (right_mem_uIcc : y1 ∈ [[y0, y1]])
  have hrightA : ∀ y ∈ [[y0, y1]],
      AnalyticAt ℂ f ((x1 : ℂ) + I * (y : ℂ)) := by
    intro y hymem
    apply hf
    simpa [mem_reProdIm, mul_comm] using
      And.intro (right_mem_uIcc : x1 ∈ [[x0, x1]]) hymem
  have hleftA : ∀ y ∈ [[y0, y1]],
      AnalyticAt ℂ f ((x0 : ℂ) + I * (y : ℂ)) := by
    intro y hymem
    apply hf
    simpa [mem_reProdIm, mul_comm] using
      And.intro (left_mem_uIcc : x0 ∈ [[x0, x1]]) hymem
  have hbottomNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y0 : ℂ) * I) ≠ 0 := by
    intro x hxmem hfzero
    have hzmem : (x : ℂ) + (y0 : ℂ) * I ∈
        ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      simpa [mem_reProdIm] using
        And.intro hxmem (left_mem_uIcc : y0 ∈ [[y0, y1]])
    have hp := (hzero _ hzmem).mp hfzero
    have hlt : y0 < y0 := by simpa using (hpoles _ hp).2.2.1
    exact (lt_irrefl y0) hlt
  have htopNe : ∀ x ∈ [[x0, x1]],
      f ((x : ℂ) + (y1 : ℂ) * I) ≠ 0 := by
    intro x hxmem hfzero
    have hzmem : (x : ℂ) + (y1 : ℂ) * I ∈
        ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      simpa [mem_reProdIm] using
        And.intro hxmem (right_mem_uIcc : y1 ∈ [[y0, y1]])
    have hp := (hzero _ hzmem).mp hfzero
    have hlt : y1 < y1 := by simpa using (hpoles _ hp).2.2.2
    exact (lt_irrefl y1) hlt
  have hrightNe : ∀ y ∈ [[y0, y1]],
      f ((x1 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro y hymem hfzero
    have hzmem : (x1 : ℂ) + I * (y : ℂ) ∈
        ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      simpa [mem_reProdIm, mul_comm] using
        And.intro (right_mem_uIcc : x1 ∈ [[x0, x1]]) hymem
    have hp := (hzero _ hzmem).mp hfzero
    have hlt : x1 < x1 := by simpa using (hpoles _ hp).2.1
    exact (lt_irrefl x1) hlt
  have hleftNe : ∀ y ∈ [[y0, y1]],
      f ((x0 : ℂ) + I * (y : ℂ)) ≠ 0 := by
    intro y hymem hfzero
    have hzmem : (x0 : ℂ) + I * (y : ℂ) ∈
        ([[x0, x1]] ×ℂ [[y0, y1]] : Set ℂ) := by
      simpa [mem_reProdIm, mul_comm] using
        And.intro (left_mem_uIcc : x0 ∈ [[x0, x1]]) hymem
    have hp := (hzero _ hzmem).mp hfzero
    have hlt : x0 < x0 := by simpa using (hpoles _ hp).1
    exact (lt_irrefl x0) hlt
  have hbottomInt : IntervalIntegrable
      (fun x : ℝ =>
        (((x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x : ℂ) + (y0 : ℂ) * I)))
      MeasureTheory.volume x0 x1 := by
    have hlog := continuousOn_logDeriv_horizontal hbottomA hbottomNe
    exact ((by fun_prop : Continuous
      (fun x : ℝ => (x : ℂ) + (y0 : ℂ) * I - (x0 : ℂ))).continuousOn.mul hlog).intervalIntegrable
  have htopInt : IntervalIntegrable
      (fun x : ℝ =>
        (((x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x : ℂ) + (y1 : ℂ) * I)))
      MeasureTheory.volume x0 x1 := by
    have hlog := continuousOn_logDeriv_horizontal htopA htopNe
    exact ((by fun_prop : Continuous
      (fun x : ℝ => (x : ℂ) + (y1 : ℂ) * I - (x0 : ℂ))).continuousOn.mul hlog).intervalIntegrable
  have hrightLog : ContinuousOn
      (fun y : ℝ => logDeriv f ((x1 : ℂ) + I * (y : ℂ))) [[y0, y1]] := by
    intro y hymem
    have hmap : ContinuousAt (fun u : ℝ => (x1 : ℂ) + I * (u : ℂ)) y := by
      fun_prop
    simpa [Function.comp_def] using
      ((ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
        (hrightA y hymem) (hrightNe y hymem)).continuousAt.comp_of_eq hmap rfl).continuousWithinAt
  have hleftLog : ContinuousOn
      (fun y : ℝ => logDeriv f ((x0 : ℂ) + I * (y : ℂ))) [[y0, y1]] := by
    intro y hymem
    have hmap : ContinuousAt (fun u : ℝ => (x0 : ℂ) + I * (u : ℂ)) y := by
      fun_prop
    simpa [Function.comp_def] using
      ((ZeroFreeRegion.analyticAt_logDeriv_of_analyticAt_ne_zero
        (hleftA y hymem) (hleftNe y hymem)).continuousAt.comp_of_eq hmap rfl).continuousWithinAt
  have hrightInt : IntervalIntegrable
      (fun y : ℝ =>
        (((x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x1 : ℂ) + (y : ℂ) * I)))
      MeasureTheory.volume y0 y1 := by
    have hweight : Continuous
        (fun y : ℝ => (x1 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) := by fun_prop
    have hrightLog' : ContinuousOn
        (fun y : ℝ => logDeriv f ((x1 : ℂ) + (y : ℂ) * I)) [[y0, y1]] := by
      simpa only [mul_comm I] using hrightLog
    exact (hweight.continuousOn.mul hrightLog').intervalIntegrable
  have hleftInt : IntervalIntegrable
      (fun y : ℝ =>
        (((x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) *
          logDeriv f ((x0 : ℂ) + (y : ℂ) * I)))
      MeasureTheory.volume y0 y1 := by
    have hweight : Continuous
        (fun y : ℝ => (x0 : ℂ) + (y : ℂ) * I - (x0 : ℂ)) := by fun_prop
    have hleftLog' : ContinuousOn
        (fun y : ℝ => logDeriv f ((x0 : ℂ) + (y : ℂ) * I)) [[y0, y1]] := by
      simpa only [mul_comm I] using hleftLog
    exact (hweight.continuousOn.mul hleftLog').intervalIntegrable
  have hedges := two_pi_mul_zeroMultiplicityWeightedRealSum_eq_four_edges
    poles multiplicity hf hzero horder hpoles
    hbottomInt htopInt hrightInt hleftInt
  have hbottomEq :=
    intervalIntegral_im_weighted_logDeriv_horizontal_eq_of_analytic
      (f := f) (anchor := x0) hbottomA hbottomNe
  have htopEq :=
    intervalIntegral_im_weighted_logDeriv_horizontal_eq_of_analytic
      (f := f) (anchor := x0) htopA htopNe
  have hrightEq :=
    intervalIntegral_re_weighted_logDeriv_vertical_eq_of_analytic
      (f := f) (anchor := x0) hrightA hrightNe
  have hleftEq :=
    intervalIntegral_re_weighted_logDeriv_vertical_eq_of_analytic
      (f := f) (anchor := x0) hleftA hleftNe
  have hrightEq' := hrightEq
  have hleftEq' := hleftEq
  simp only [mul_comm I] at hrightEq' hleftEq'
  rw [hbottomEq, htopEq, hrightEq', hleftEq'] at hedges
  calc
    _ = _ := hedges
    _ = _ := by ring

end CarlsonZeroDensity
end PrimeNumberTheorem
