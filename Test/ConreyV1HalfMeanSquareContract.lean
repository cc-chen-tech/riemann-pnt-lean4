import HardyTheorem.ConreyV1HalfMeanSquare

/-!
同参数半段转移的完整字面契约；不添加实际均方渐近假设。
The literal contract must retain the original T, log T, sigma, Y and P,
with no low-height moment and no extra analytic hypothesis.
-/

open Complex
open scoped Interval

namespace HardyTheorem

example {T sigma : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hT : 6 ≤ T) (hs : 0 < sigma) (hsHalf : sigma ≤ 1 / 2) :
    let L := Real.log T
    let z := fun t : ℝ => (sigma : ℂ) + I * t
    let B := conreyMollifier Y sigma P
    (∫ t in T / 2..T,
      ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma P (z t)‖ ^ 2) ≤
      (1 + 1 / L) * (∫ t in T / 2..T, ‖conreyExplicitV L (z t) * B (z t)‖ ^ 2) +
      (1 + L) *
        (((51 / 50 : ℝ) * (10 + (Real.log 2 + |Real.log (2 * Real.pi)|) / 2)) / L) ^ 2 *
        (∫ t in T / 2..T, ‖riemannZeta (z t) * B (z t)‖ ^ 2) := by
  exact conreyMollifiedV1_half_meanSquare_le_V_and_zeta hT hs hsHalf

#print axioms conreyMollifiedV1_half_meanSquare_le_V_and_zeta

end HardyTheorem
