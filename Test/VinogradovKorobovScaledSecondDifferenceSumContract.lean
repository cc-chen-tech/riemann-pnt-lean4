import ZeroFreeRegion.VinogradovKorobov.ScaledSecondDifferenceSum

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (t : ℝ) (h k m R : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hR : 1 ≤ R) (hhm : h ≤ m) (hkm : k ≤ m)
    (hturn :
      t * logSecondDifferenceDecrement h k m ≤
        2 * Real.pi -
          t * logSecondDifferenceDecrement h k
            ((m + (R - 1) : ℕ) : ℝ)) :
    ‖∑ n ∈ Finset.range R,
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
      162 * Real.pi * ((m + (R - 1) : ℕ) : ℝ) ^ 3 /
        (t * h * k) :=
  iteratedShiftedZetaPhase_two_kusminLandau_scaled_range
    t h k m R ht hh hk hm hR hhm hkm hturn

example (t : ℝ) (h k m R : ℕ)
    (ht : 0 < t) (hh : 0 < h) (hk : 0 < k) (hm : 0 < m)
    (hR : 1 ≤ R) (hhm : h ≤ m) (hkm : k ≤ m)
    (hscale :
      5 * t * (h : ℝ) * (k : ℝ) ≤ Real.pi * (m : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range R,
        phaseTerm
          (iteratedPhaseDifference [h, k] (shiftedZetaPhase t m)) n‖ ≤
      162 * Real.pi * ((m + (R - 1) : ℕ) : ℝ) ^ 3 /
        (t * h * k) :=
  iteratedShiftedZetaPhase_two_kusminLandau_scaled_range_of_start_scale
    t h k m R ht hh hk hm hR hhm hkm hscale

end ZeroFreeRegion.VinogradovKorobov
