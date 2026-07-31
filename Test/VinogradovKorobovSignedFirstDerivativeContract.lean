import ZeroFreeRegion.VinogradovKorobov.SignedFirstDerivative

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (f : ℕ → ℝ) (n : ℕ) :
    phaseTerm (fun k ↦ -f k) n = star (phaseTerm f n) :=
  phaseTerm_neg f n

example (f : ℕ → ℝ) (N : ℕ) :
    ‖∑ k ∈ Finset.range N, phaseTerm (fun n ↦ -f n) k‖ =
      ‖∑ k ∈ Finset.range N, phaseTerm f k‖ :=
  norm_phaseSum_neg_eq f N

example (f : ℕ → ℝ) (N : ℕ)
    {delta : ℝ} (hdelta : 0 < delta)
    (hlower : ∀ k ≤ N, delta ≤ f k - f (k + 1))
    (hupper : ∀ k ≤ N, f k - f (k + 1) ≤ 2 * Real.pi - delta)
    (hanti : ∀ k < N,
      f (k + 1) - f (k + 2) ≤ f k - f (k + 1)) :
    ‖∑ k ∈ Finset.range (N + 1), phaseTerm f k‖ ≤
      2 * Real.pi / delta :=
  kusminLandau_negative_antitone_two_pi_div
    f N hdelta hlower hupper hanti

end ZeroFreeRegion.VinogradovKorobov
