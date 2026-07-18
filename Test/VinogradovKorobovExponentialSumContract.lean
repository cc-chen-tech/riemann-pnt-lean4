import ZeroFreeRegion.VinogradovKorobov.ExponentialSum

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

example (f : ℕ → ℝ) (n : ℕ) : ‖phaseTerm f n‖ = 1 :=
  norm_phaseTerm f n

example (f : ℕ → ℝ) (n h : ℕ) :
    phaseTerm f n * (starRingEnd ℂ) (phaseTerm f (n + h)) =
      Complex.exp (I * ((f n - f (n + h) : ℝ) : ℂ)) :=
  phaseTerm_mul_conj_shift f n h

example (theta : ℝ) (N : ℕ) :
    ‖linearPhaseSum theta N‖ ≤ N :=
  norm_linearPhaseSum_le_length theta N

example (theta : ℝ) (N : ℕ)
    (htheta : Complex.exp (I * (theta : ℂ)) ≠ 1) :
    ‖linearPhaseSum theta N‖ ≤
      2 / ‖Complex.exp (I * (theta : ℂ)) - 1‖ :=
  norm_linearPhaseSum_le_two_div theta N htheta

example (theta : ℝ) (N : ℕ)
    (htheta : Complex.exp (I * (theta : ℂ)) ≠ 1) :
    ‖linearPhaseSum theta N‖ ≤
      min (N : ℝ) (2 / ‖Complex.exp (I * (theta : ℂ)) - 1‖) :=
  norm_linearPhaseSum_le_min theta N htheta

end ZeroFreeRegion.VinogradovKorobov
