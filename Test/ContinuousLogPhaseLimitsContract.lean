import MathlibAux.ContinuousLogPhaseLimits
import MathlibAux.ArgumentCrossingOpen

open Complex Set Filter Topology
open MathlibAux

-- A fixed deck shift transfers the limit of the same logarithm's phase;
-- independent pointwise integer choices would not imply this conclusion.
example {ell model : ℝ → ℂ} {a b alpha : ℝ} {F : Filter ℝ}
    (hab : a < b) (hell : ContinuousOn ell (Ioo a b))
    (hmodel : ContinuousOn model (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell t) = Complex.exp (model t))
    (hmem : Ioo a b ∈ F)
    (hlim : Tendsto (fun t => (model t).im) F (nhds alpha)) :
    ∃ k : ℤ, Tendsto (fun t => (ell t).im) F
      (nhds (alpha + ((k : ℂ) * (2 * Real.pi * I)).im)) := by
  exact exists_int_tendsto_im_continuousLog hab hell hmodel hexp hmem hlim

#print axioms exists_int_tendsto_im_continuousLog

-- Both endpoint shifts must use the same deck integer. Choosing independent
-- shifts would not preserve the balanced component argument increment.
example {ell₁ ell₂ : ℝ → ℂ} {a b A₁ B₁ A₂ B₂ : ℝ}
    (hab : a < b) (h₁ : ContinuousOn ell₁ (Ioo a b))
    (h₂ : ContinuousOn ell₂ (Ioo a b))
    (hexp : ∀ t ∈ Ioo a b, Complex.exp (ell₁ t) = Complex.exp (ell₂ t))
    (hA₁ : Tendsto (fun t => (ell₁ t).im) (nhdsWithin a (Ioi a)) (nhds A₁))
    (hB₁ : Tendsto (fun t => (ell₁ t).im) (nhdsWithin b (Iio b)) (nhds B₁))
    (hA₂ : Tendsto (fun t => (ell₂ t).im) (nhdsWithin a (Ioi a)) (nhds A₂))
    (hB₂ : Tendsto (fun t => (ell₂ t).im) (nhdsWithin b (Iio b)) (nhds B₂)) :
    B₁ - A₁ = B₂ - A₂ := by
  exact continuousLog_phase_increment_eq hab h₁ h₂ hexp hA₁ hB₁ hA₂ hB₂

#print axioms continuousLog_phase_increment_eq
