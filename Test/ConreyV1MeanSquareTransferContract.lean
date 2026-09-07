import HardyTheorem.ConreyV1MeanSquareTransfer

open Complex Set HardyTheorem

/-! All quantities are the actual same-parameter products. In particular,
there is no moment or error-estimate hypothesis hiding the analytic work. -/
example {L sigma a U T epsilon : ℝ} {Y : ℕ} {P : ℝ → ℝ}
    (hL : 0 < L) (hs : 0 < sigma) (hsHalf : sigma ≤ 1 / 2)
    (ha : a ≤ 1) (hU : 3 ≤ U) (hUZ : U ≤ Real.exp (a * L))
    (hZT : Real.exp (a * L) ≤ T) (hT : T ≤ Real.exp L) (he : 0 < epsilon) :
    let z := fun t : ℝ => (sigma : ℂ) + I * t
    let B := conreyMollifier Y sigma P
    let V := fun s : ℂ => riemannZeta s + ((51 / (50 * L) : ℝ) : ℂ) * deriv riemannZeta s
    let C := 10 + |Real.log (2 * Real.pi)| / 2
    let D := fun b : ℝ => (51 / 50 : ℝ) * ((1 - b) / 2 + C / L)
    (∫ t in U..T, ‖conreyMollifiedDegreeOneV1 (49 / 100) 0 (51 / 50) L Y sigma P (z t)‖ ^ 2) ≤
      (1 + epsilon) * (∫ t in U..T, ‖V (z t) * B (z t)‖ ^ 2) +
      (1 + 1 / epsilon) *
        ((D 0) ^ 2 * (∫ t in U..Real.exp (a * L), ‖riemannZeta (z t) * B (z t)‖ ^ 2) +
         (D a) ^ 2 * (∫ t in Real.exp (a * L)..T, ‖riemannZeta (z t) * B (z t)‖ ^ 2)) :=
  conreyMollifiedV1_meanSquare_le_V_and_zeta hL hs hsHalf ha hU hUZ hZT hT he

#print axioms conreyMollifiedV1_meanSquare_le_V_and_zeta
#print axioms norm_conreyMollifiedV1_sub_V_le
