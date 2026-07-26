import PrimeNumberTheorem.VKEdgePiOverTwoGaussianDual

open Filter MeasureTheory

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

example {rho : ℂ} {gamma : ℝ} {k : ℕ} (hgamma : 0 < gamma) :
    ∃ C ≥ 0, ∀ {m : ℝ}, 1 ≤ m → ∀ c : ℝ,
      |(∫ t : ℝ,
          normalizedGaussian m t *
            |sharpenedPsiAbelKernel rho gamma k (c - t)|) -
          sharpenedMissingHarmonicDenominator k| ≤
        C / Real.sqrt m :=
  exists_uniform_gaussian_abs_sharpenedPsiAbelKernel_bound hgamma

example {rho : ℂ} {gamma : ℝ} {k : ℕ}
    (hgamma : 0 < gamma) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ c : ℝ,
      |(∫ t : ℝ,
          normalizedGaussian m t *
            |sharpenedPsiAbelKernel rho gamma k (c - t)|) -
          sharpenedMissingHarmonicDenominator k| < ε :=
  eventually_uniform_gaussian_abs_sharpenedPsiAbelKernel
    hgamma hε

end VKEdgePiOverTwo
end PrimeNumberTheorem
