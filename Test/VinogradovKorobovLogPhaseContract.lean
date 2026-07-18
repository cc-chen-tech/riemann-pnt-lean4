import ZeroFreeRegion.VinogradovKorobov.LogPhase

namespace ZeroFreeRegion.VinogradovKorobov

example (h x : ℝ) (hx : 0 < x) (hh : 0 < h) :
    logIncrementDifference h x =
      Real.log (1 + h / (x * (x + h + 1))) :=
  logIncrementDifference_eq hx hh

example (h : ℝ) (hh : 0 < h) :
    AntitoneOn (logIncrementDifference h) (Set.Ioi 0) :=
  antitoneOn_logIncrementDifference hh

example (t : ℝ) (h n : ℕ) :
    logarithmicCorrelationPhase t h (n + 1) -
        logarithmicCorrelationPhase t h n =
      t * logIncrementDifference h n :=
  logarithmicCorrelationPhase_forwardDifference t h n

example (t : ℝ) (h n : ℕ) (ht : 0 < t) (hh : 0 < h) (hn : 0 < n) :
    0 < logarithmicCorrelationPhase t h (n + 1) -
      logarithmicCorrelationPhase t h n :=
  logarithmicCorrelationPhase_forwardDifference_pos ht hh hn

example (t : ℝ) (h n : ℕ) (ht : 0 ≤ t) (hh : 0 < h) (hn : 0 < n) :
    logarithmicCorrelationPhase t h (n + 2) -
        logarithmicCorrelationPhase t h (n + 1) ≤
      logarithmicCorrelationPhase t h (n + 1) -
        logarithmicCorrelationPhase t h n :=
  logarithmicCorrelationPhase_forwardDifference_antitone ht hh hn

example (t : ℝ) (h m N : ℕ) (ht : 0 < t) (hh : 0 < h) (hm : 0 < m)
    (hlt : ∀ k ≤ N,
      logarithmicCorrelationPhase t h (m + (k + 1)) -
        logarithmicCorrelationPhase t h (m + k) < 2 * Real.pi) :
    ‖∑ k ∈ Finset.range (N + 1),
        phaseTerm (fun j ↦ logarithmicCorrelationPhase t h (m + j)) k‖ ≤
      ‖(Complex.exp (Complex.I *
        ((logarithmicCorrelationPhase t h (m + 1) -
          logarithmicCorrelationPhase t h m : ℝ) : ℂ)) - 1)⁻¹‖ +
      ‖(Complex.exp (Complex.I *
        ((logarithmicCorrelationPhase t h (m + (N + 1)) -
          logarithmicCorrelationPhase t h (m + N) : ℝ) : ℂ)) - 1)⁻¹‖ +
      (Real.cot ((logarithmicCorrelationPhase t h (m + (N + 1)) -
          logarithmicCorrelationPhase t h (m + N)) / 2) -
        Real.cot ((logarithmicCorrelationPhase t h (m + 1) -
          logarithmicCorrelationPhase t h m) / 2)) / 2 :=
  logarithmicCorrelation_kusminLandau_endpoint_bound t h m N ht hh hm hlt

end ZeroFreeRegion.VinogradovKorobov
