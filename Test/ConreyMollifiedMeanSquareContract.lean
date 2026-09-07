import HardyTheorem.ConreyMollifiedMeanSquare

open Complex MeasureTheory Set
open scoped Interval
open HardyTheorem

/-! The actual product supplies its own finite zero set, AE nonvanishing,
log integrability and positive second moment, with left zeros allowed. -/

example {g g0 g1 L sigma0 A U T : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hg : g ≠ 0) (hY : 2 ≤ Y) (hP1 : P 1 = 1)
    (hsigma : 0 < sigma0) (hsigmaHalf : sigma0 ≤ 1 / 2)
    (hA : 1 / 2 < A) (hU : 0 < U) (hUT : U < T)
    (hbottom : ∀ z ∈ (Icc sigma0 A ×ℂ Icc U T), z.im = U →
      conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P z ≠ 0) :
    0 < (∫ t in U..T,
      ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖ ^ 2) ∧
      2 * (∫ t in U..T, Real.log
        ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖) ≤
        (T - U) * Real.log ((∫ t in U..T,
          ‖conreyMollifiedDegreeOneV1 g g0 g1 L Y sigma0 P ((sigma0 : ℂ) + I * t)‖ ^ 2) /
          (T - U)) := by
  exact conreyMollified_logNorm_meanSquare_bounds
    hg hY hP1 hsigma hsigmaHalf hA hU hUT hbottom

#print axioms conreyMollified_logNorm_meanSquare_bounds
