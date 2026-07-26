import ZeroFreeRegion.VinogradovKorobov.VinogradovWeightedMoment
import ZeroFreeRegion.VinogradovKorobov.VinogradovMainEstimate

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- Any verified Vinogradov mean-value estimate transfers to the normalized
weighted Weyl moment under the degree-by-degree no-wrap condition. -/
theorem norm_normalizedVinogradovWeightedMomentMod_le_of_meanValueEstimate
    (p a k s X : ℕ) [Fact p.Prime] {ε C : ℝ}
    (hest : VinogradovMeanValueEstimate k s ε C)
    (hX : 1 ≤ X)
    (hscale : ∀ j : Fin k,
      s * X ^ (j.val + 1) < vinogradovWeightedModulus p a j) :
    ‖normalizedVinogradovWeightedMomentMod p a k s X‖ ≤
      C * Real.rpow (X : ℝ) ε *
        ((X : ℝ) ^ s +
          (X : ℝ) ^ (2 * s - vinogradovCriticalWeight k)) := by
  rw [normalizedVinogradovWeightedMomentMod_eq_natCount_of_scale
    p a k s X hscale]
  simpa only [Complex.norm_natCast] using hest.2.2 X hX

end

end ZeroFreeRegion.VinogradovKorobov
