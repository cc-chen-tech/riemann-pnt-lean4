import HardyTheorem.ConreyShiftedH

open Complex HardyTheorem

/-! The actual shifted H formula, not a supplied asymptotic hypothesis. -/
example {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    deriv conreyH s / conreyH s =
      deriv conreyH (s + 2) / conreyH (s + 2) -
        1 / (s + 2) - 1 / (s + 1) + 1 / (s - 1) :=
  logDeriv_conreyH_shift_two hs hs1

example {sigma t : ℝ} (hs : 0 < sigma) (hsHalf : sigma ≤ 1 / 2) (ht : 3 ≤ t) :
    ‖deriv conreyH ((sigma : ℂ) + I * t) / conreyH ((sigma : ℂ) + I * t) -
      ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ ≤ 10 :=
  norm_logDeriv_conreyH_shifted_sub_half_log_le hs hsHalf ht

#print axioms logDeriv_conreyH_shift_two
#print axioms norm_logDeriv_conreyH_shifted_sub_half_log_le
