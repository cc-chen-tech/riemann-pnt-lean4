import HardyTheorem.ConreyV1MeanSquareTransfer

/-!
# Same-parameter half-interval V1 transfer

局部有限均方转移；不包含实际长均方渐近式或最终零点比例。
This finite transfer does not supply a long-moment asymptotic.

The mathematics is the specialization in #552, Section 2. The split point
is the lower endpoint T/2, so the low integral is exactly zero. No bound
for the long mollifier at low heights and no moment asymptotic is assumed.
-/

open Complex
open scoped Interval

namespace HardyTheorem

/-- The fixed numerator of the comparison coefficient on [T/2,T]. -/
noncomputable def conreyV1HalfIntervalComparisonNumerator : ℝ :=
  (51 / 50 : ℝ) * (10 + (Real.log 2 + |Real.log (2 * Real.pi)|) / 2)

private theorem comparisonCoefficient_half {L : ℝ} (hL : 0 < L) :
    conreyV1ComparisonCoefficient L (1 - Real.log 2 / L) =
      conreyV1HalfIntervalComparisonNumerator / L := by
  unfold conreyV1ComparisonCoefficient conreyV1HalfIntervalComparisonNumerator
  field_simp [hL.ne']
  ring

/-- Finite transfer for the actual original mollifier, on its upper
half-interval. The right side contains only the two actual half moments. -/
theorem conreyMollifiedV1_half_meanSquare_le_V_and_zeta
    {T sigma : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hT : 6 ≤ T) (hs : 0 < sigma) (hsHalf : sigma ≤ 1 / 2) :
    let L := Real.log T
    let z := fun t : ℝ => (sigma : ℂ) + I * t
    let B := conreyMollifier Y sigma P
    (∫ t in T / 2..T,
      ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma P (z t)‖ ^ 2) ≤
      (1 + 1 / L) * (∫ t in T / 2..T, ‖conreyExplicitV L (z t) * B (z t)‖ ^ 2) +
      (1 + L) * (conreyV1HalfIntervalComparisonNumerator / L) ^ 2 *
        (∫ t in T / 2..T, ‖riemannZeta (z t) * B (z t)‖ ^ 2) := by
  let L := Real.log T
  have hTpos : 0 < T := by linarith
  have hL : 0 < L := Real.log_pos (by linarith : (1 : ℝ) < T)
  have hlogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have ha : 1 - Real.log 2 / L ≤ 1 :=
    sub_le_self _ (div_nonneg hlogTwo hL.le)
  have hsplit : Real.exp ((1 - Real.log 2 / L) * L) = T / 2 := by
    calc
      Real.exp ((1 - Real.log 2 / L) * L) = Real.exp (L - Real.log 2) := by
        congr 1
        field_simp [hL.ne']
      _ = T / 2 := by
        rw [Real.exp_sub]
        dsimp only [L]
        rw [Real.exp_log hTpos, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hraw := conreyMollifiedV1_meanSquare_le_V_and_zeta
    (L := L) (sigma := sigma) (a := 1 - Real.log 2 / L)
    (U := T / 2) (T := T) (epsilon := 1 / L) (Y := Y) (P := P)
    hL hs hsHalf ha (by linarith)
    (by rw [hsplit]) (by rw [hsplit]; linarith)
    (by change T ≤ Real.exp (Real.log T); rw [Real.exp_log hTpos])
    (one_div_pos.mpr hL)
  simpa only [hsplit, intervalIntegral.integral_same, mul_zero, zero_add,
    one_div_one_div, comparisonCoefficient_half hL, mul_assoc] using hraw

end HardyTheorem
