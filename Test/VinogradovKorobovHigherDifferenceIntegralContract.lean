import ZeroFreeRegion.VinogradovKorobov.HigherDifferenceIntegral

namespace ZeroFreeRegion.VinogradovKorobov

example (F : ℕ → ℝ → ℝ)
    (hF : ∀ j y, 0 < y → HasDerivAt (F j) (F (j + 1) y) y)
    (shifts : List ℝ) (hshifts : ∀ h ∈ shifts, 0 ≤ h)
    (j : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedShiftIntegral shifts (F (shifts.length + j)) x =
      (-1 : ℝ) ^ shifts.length *
        realIteratedPhaseDifference shifts (F j) x :=
  iteratedShiftIntegral_tower_eq_signedDifference
    F hF shifts hshifts j hx

end ZeroFreeRegion.VinogradovKorobov
