import MathlibAux.ContinuousLogDerivative

open Complex Filter Set Topology MeasureTheory
open scoped Interval

-- A logarithm is only assumed continuous, not differentiable or principal.
-- Adding a derivative or slit-plane hypothesis would break this contract.
example {ell gamma : ℝ → ℂ} {gamma' : ℂ} {t : ℝ}
    (hell : ContinuousAt ell t) (hgamma : HasDerivAt gamma gamma' t)
    (hexp : ∀ᶠ y in nhds t, Complex.exp (ell y) = gamma y) :
    HasDerivAt ell (gamma' / gamma t) t := by
  exact MathlibAux.hasDerivAt_continuousLog_of_exp_eq hell hgamma hexp

-- The upward vertical parameter gives Re(f'/f), with no branch-cut condition.
example {f : ℂ → ℂ} {ell : ℝ → ℂ} {sigma t : ℝ}
    (hf : DifferentiableAt ℂ f ((sigma : ℂ) + I * t))
    (hell : ContinuousAt ell t)
    (hexp : ∀ᶠ y in nhds t, Complex.exp (ell y) = f ((sigma : ℂ) + I * y)) :
    HasDerivAt (fun y => (ell y).im)
      (logDeriv f ((sigma : ℂ) + I * t)).re t := by
  exact MathlibAux.hasDerivAt_im_continuousLog_vertical hf hell hexp

-- q extends through boundary zeros, while ell need not extend at either
-- endpoint. A missing exp linkage or extra endpoint-value assumption is a bug.
example {f : ℂ → ℂ} {ell : ℝ → ℂ} {q : ℝ → ℝ} {sigma a b A B : ℝ}
    (hab : a < b) (hell : ContinuousOn ell (Ioo a b))
    (hf : ∀ t ∈ Ioo a b, DifferentiableAt ℂ f ((sigma : ℂ) + I * t))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = f ((sigma : ℂ) + I * t))
    (hq : ContinuousOn q (Icc a b))
    (hlink : ∀ t ∈ Ioo a b, q t = (logDeriv f ((sigma : ℂ) + I * t)).re)
    (hA : Tendsto (fun t => (ell t).im) (nhdsWithin a (Ioi a)) (nhds A))
    (hB : Tendsto (fun t => (ell t).im) (nhdsWithin b (Iio b)) (nhds B)) :
    B - A = ∫ t in a..b, q t := by
  exact MathlibAux.continuousLog_phase_increment_eq_integral hab hell hf hexp hq hlink hA hB

#print axioms MathlibAux.hasDerivAt_continuousLog_of_exp_eq
#print axioms MathlibAux.hasDerivAt_im_continuousLog_vertical
#print axioms MathlibAux.continuousLog_phase_increment_eq_integral
