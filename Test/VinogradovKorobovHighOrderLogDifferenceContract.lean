import ZeroFreeRegion.VinogradovKorobov.HighOrderLogDifference

namespace ZeroFreeRegion.VinogradovKorobov

example (h : ℝ) (shifts : List ℝ)
    (hh : 0 ≤ h) (hshifts : ∀ k ∈ shifts, 0 ≤ k)
    {x : ℝ} (hx : 0 < x) :
    (shifts.length.factorial : ℝ) * (h :: shifts).prod *
        ((x + (h :: shifts).sum) ^ (h :: shifts).length)⁻¹ ≤
      -realIteratedPhaseDifference (h :: shifts) Real.log x ∧
    -realIteratedPhaseDifference (h :: shifts) Real.log x ≤
      (shifts.length.factorial : ℝ) * (h :: shifts).prod *
        (x ^ (h :: shifts).length)⁻¹ :=
  neg_realIteratedLogDifference_bounds h shifts hh hshifts hx

end ZeroFreeRegion.VinogradovKorobov
