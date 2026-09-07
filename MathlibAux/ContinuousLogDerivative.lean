import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives and finite endpoint increments of continuous logarithms

Continuity and an exponential identity determine the derivative of a chosen
logarithm, without requiring its values to lie in the principal strip. For
vertical analytic curves, a continuous extension of the real logarithmic
derivative then identifies the finite one-sided phase increment with an integral.
The complex logarithm itself need not converge at zero endpoints.
-/

open Complex Filter Set Topology MeasureTheory
open scoped Interval

namespace MathlibAux

/-- A continuous logarithm of a differentiable nonzero curve is differentiable.
Nonvanishing follows from the exponential identity. No principal-branch
assumption and no prior differentiability of `ell` is required. -/
theorem hasDerivAt_continuousLog_of_exp_eq
    {ell gamma : ℝ → ℂ} {gamma' : ℂ} {t : ℝ}
    (hell : ContinuousAt ell t) (hgamma : HasDerivAt gamma gamma' t)
    (hexp : ∀ᶠ y in nhds t, Complex.exp (ell y) = gamma y) :
    HasDerivAt ell (gamma' / gamma t) t := by
  have he0 : Complex.exp (ell t) = gamma t := hexp.self_of_nhds
  have hne : gamma t ≠ 0 := he0 ▸ Complex.exp_ne_zero (ell t)
  have hshift : ContinuousAt (fun y => (ell y - ell t).im) t :=
    Complex.continuous_im.continuousAt.comp (hell.sub continuousAt_const)
  have hlim : Tendsto (fun y => (ell y - ell t).im) (nhds t) (nhds 0) := by
    simpa only [ContinuousAt, sub_self, Complex.zero_im] using hshift
  have hsmall : ∀ᶠ y in nhds t,
      -Real.pi < (ell y - ell t).im ∧ (ell y - ell t).im < Real.pi :=
    hlim (Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos)
  have hmodel : (fun y => Complex.log (gamma y / gamma t) + ell t) =ᶠ[nhds t] ell := by
    filter_upwards [hexp, hsmall] with y hy hys
    rw [← hy, ← he0, ← Complex.exp_sub, Complex.log_exp hys.1 hys.2.le]
    abel
  have hslit : gamma t / gamma t ∈ Complex.slitPlane := by simp [hne]
  have hderiv := ((hgamma.div_const (gamma t)).clog_real hslit).add_const (ell t)
  have hmodelDeriv : HasDerivAt
      (fun y => Complex.log (gamma y / gamma t) + ell t) (gamma' / gamma t) t := by
    simpa only [div_self hne, div_one] using hderiv
  exact hmodelDeriv.congr_of_eventuallyEq hmodel.symm

/-- On an upward vertical line, any continuous logarithm has phase derivative
`Re(f'/f)`, even when its branch crosses the principal logarithm's cut. -/
theorem hasDerivAt_im_continuousLog_vertical
    {f : ℂ → ℂ} {ell : ℝ → ℂ} {sigma t : ℝ}
    (hf : DifferentiableAt ℂ f ((sigma : ℂ) + I * t))
    (hell : ContinuousAt ell t)
    (hexp : ∀ᶠ y in nhds t, Complex.exp (ell y) = f ((sigma : ℂ) + I * y)) :
    HasDerivAt (fun y => (ell y).im)
      (logDeriv f ((sigma : ℂ) + I * t)).re t := by
  let s : ℂ := (sigma : ℂ) + I * t
  have hparam : HasDerivAt (fun z : ℂ => (sigma : ℂ) + I * z) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul I).const_add (sigma : ℂ)
  have hcomplex : HasDerivAt (fun z : ℂ => f ((sigma : ℂ) + I * z))
      (deriv f s * I) (t : ℂ) := by
    simpa [s, Function.comp_def] using hf.hasDerivAt.comp (t : ℂ) hparam
  have hvertical : HasDerivAt (fun y : ℝ => f ((sigma : ℂ) + I * y))
      (deriv f s * I) t := by simpa using hcomplex.comp_ofReal
  have hlog := hasDerivAt_continuousLog_of_exp_eq hell hvertical hexp
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hlog
  convert him using 1 <;> (try rfl)
  change (deriv f s / f s).re = (deriv f s * I / f s).im
  rw [show deriv f s * I / f s = I * (deriv f s / f s) by ring]
  simp

/-- Finite one-sided phase limits identify the balanced increment with the
integral of a continuous regularized real trace. No value or full complex limit
of the logarithm is assumed at either endpoint. -/
theorem continuousLog_phase_increment_eq_integral
    {f : ℂ → ℂ} {ell : ℝ → ℂ} {q : ℝ → ℝ} {sigma a b A B : ℝ}
    (hab : a < b) (hell : ContinuousOn ell (Ioo a b))
    (hf : ∀ t ∈ Ioo a b, DifferentiableAt ℂ f ((sigma : ℂ) + I * t))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = f ((sigma : ℂ) + I * t))
    (hq : ContinuousOn q (Icc a b))
    (hlink : ∀ t ∈ Ioo a b, q t = (logDeriv f ((sigma : ℂ) + I * t)).re)
    (hA : Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds A))
    (hB : Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds B)) :
    B - A = ∫ t in a..b, q t := by
  have hderiv : ∀ t ∈ Ioo a b, HasDerivAt (fun y => (ell y).im) (q t) t := by
    intro t ht
    rw [hlink t ht]
    apply hasDerivAt_im_continuousLog_vertical (hf t ht)
      ((hell t ht).continuousAt (isOpen_Ioo.mem_nhds ht))
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy
    exact hexp y hy
  have hint : IntervalIntegrable q volume a b :=
    (by simpa only [uIcc_of_le hab.le] using hq : ContinuousOn q (uIcc a b)).intervalIntegrable
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    hab hderiv hint hA hB).symm

end MathlibAux
