import ZeroFreeRegion.VinogradovKorobov.HigherLogDifference

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (t : ℝ) (m n : ℕ) : ℝ :=
  shiftedZetaPhase t m n

noncomputable example (h k : ℝ) (x : ℝ) : ℝ :=
  logSecondDifference h k x

noncomputable example (h k : ℝ) (x : ℝ) : ℝ :=
  logSecondDifferenceDecrement h k x

noncomputable example (h k : ℝ) (x : ℝ) : ℝ :=
  logSecondDifferenceDecrementFraction h k x

example {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifference h k x =
      Real.log (1 + h * k / (x * (x + h + k))) :=
  logSecondDifference_eq hx hh hk

example {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    0 < logSecondDifference h k x :=
  logSecondDifference_pos hx hh hk

example {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifference h k x ≤ h * k / (x * (x + h + k)) :=
  logSecondDifference_le_fraction hx hh hk

example {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    AntitoneOn (logSecondDifference h k) (Set.Ioi 0) :=
  antitoneOn_logSecondDifference hh hk

example {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifferenceDecrement h k x =
      Real.log (1 + logSecondDifferenceDecrementFraction h k x) :=
  logSecondDifferenceDecrement_eq hx hh hk

example {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    0 < logSecondDifferenceDecrement h k x :=
  logSecondDifferenceDecrement_pos hx hh hk

example {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifferenceDecrement h k x ≤
      logSecondDifferenceDecrementFraction h k x :=
  logSecondDifferenceDecrement_le_fraction hx hh hk

example {h k x : ℝ} (hx : 0 < x) (hh : 0 < h) (hk : 0 < k) :
    logSecondDifferenceDecrementFraction h k x /
        (1 + logSecondDifferenceDecrementFraction h k x) ≤
      logSecondDifferenceDecrement h k x :=
  fraction_div_one_add_le_logSecondDifferenceDecrement hx hh hk

example {h k : ℝ} (hh : 0 < h) (hk : 0 < k) :
    AntitoneOn (logSecondDifferenceDecrement h k) (Set.Ioi 0) :=
  antitoneOn_logSecondDifferenceDecrement hh hk

example (t : ℝ) (m n h k : ℕ) :
    iteratedPhaseDifference [h, k] (shiftedZetaPhase t m) n =
      t * logSecondDifference h k (m + n) :=
  iterated_shiftedZetaPhase_two t m n h k

example (t : ℝ) (m n : ℕ) :
    phaseTerm (shiftedZetaPhase t m) n = zetaOscillation t (m + n) :=
  phaseTerm_shiftedZetaPhase t m n

end ZeroFreeRegion.VinogradovKorobov
