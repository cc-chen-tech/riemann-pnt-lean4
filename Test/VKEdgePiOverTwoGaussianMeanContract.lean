import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMean

open Filter MeasureTheory

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

#check normalizedGaussian
#check normalizedGaussianDeriv
#check periodicMean

#check normalizedGaussian_pos
#check integral_normalizedGaussian
#check hasDerivAt_normalizedGaussian
#check integrable_normalizedGaussianDeriv
#check integral_abs_normalizedGaussianDeriv_le_inv_sqrt
#check exists_uniform_normalizedGaussian_periodicMean_bound
#check eventually_uniform_normalizedGaussian_periodicMean

example {m t : ℝ} (hm : 0 < m) :
    0 < normalizedGaussian m t :=
  normalizedGaussian_pos hm t

example {m : ℝ} (hm : 0 < m) :
    ∫ t : ℝ, normalizedGaussian m t = 1 :=
  integral_normalizedGaussian hm

example {m t : ℝ} (hm : 0 < m) :
    HasDerivAt (normalizedGaussian m)
      (normalizedGaussianDeriv m t) t :=
  hasDerivAt_normalizedGaussian hm t

example {m : ℝ} (hm : 0 < m) :
    Integrable (normalizedGaussianDeriv m) :=
  integrable_normalizedGaussianDeriv hm

example {m : ℝ} (hm : 0 < m) :
    (∫ t : ℝ, |normalizedGaussianDeriv m t|) ≤
      1 / Real.sqrt m :=
  integral_abs_normalizedGaussianDeriv_le_inv_sqrt hm

example {f : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hperiodic : Function.Periodic f P)
    (hcontinuous : Continuous f) :
    ∃ C ≥ 0, ∀ {m : ℝ}, 1 ≤ m → ∀ c : ℝ,
      |(∫ t : ℝ, normalizedGaussian m t * f (c - t)) -
          periodicMean f P| ≤ C / Real.sqrt m :=
  exists_uniform_normalizedGaussian_periodicMean_bound
    hP hperiodic hcontinuous

example {f : ℝ → ℝ} {P : ℝ}
    (hP : 0 < P) (hperiodic : Function.Periodic f P)
    (hcontinuous : Continuous f) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ c : ℝ,
      |(∫ t : ℝ, normalizedGaussian m t * f (c - t)) -
          periodicMean f P| < ε :=
  eventually_uniform_normalizedGaussian_periodicMean
    hP hperiodic hcontinuous hε

end VKEdgePiOverTwo
end PrimeNumberTheorem
