import HardyTheorem.ConreyDigammaHeight

/-! The same-height archimedean estimate on the shifted critical strip.
The exact digamma recurrence transfers the existing right-half-plane bound. -/

open Complex

namespace HardyTheorem

/-- Two-step shift of the actual logarithmic derivative, from the already
proved H formula and the differentiated Gamma recurrence. -/
theorem logDeriv_conreyH_shift_two {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    deriv conreyH s / conreyH s =
      deriv conreyH (s + 2) / conreyH (s + 2) -
        1 / (s + 2) - 1 / (s + 1) + 1 / (s - 1) := by
  have hshift : 1 < (s + 2).re := by simp only [add_re]; norm_num; linarith
  have hpoles : ∀ n : ℕ, s / 2 ≠ -(n : ℂ) := by
    intro n he
    have hr := congrArg Complex.re he
    norm_num at hr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [logDeriv_conreyH_eq_of_re_pos_of_ne_one hs hs1, logDeriv_conreyH_eq hshift,
    show (s + 2) / 2 = s / 2 + 1 by ring,
    digamma_apply_add_one (s / 2) hpoles,
    show s + 2 - 1 = s + 1 by ring]
  simp only [inv_div]
  ring

/-- Uniform complex H error on the actual shifted strip. No V1 or
mollifier nonvanishing hypothesis is needed. -/
theorem norm_logDeriv_conreyH_shifted_sub_half_log_le
    {sigma t : ℝ} (hs : 0 < sigma) (hsHalf : sigma ≤ 1 / 2) (ht : 3 ≤ t) :
    ‖deriv conreyH ((sigma : ℂ) + I * t) / conreyH ((sigma : ℂ) + I * t) -
      ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)‖ ≤ 10 := by
  let s : ℂ := (sigma : ℂ) + I * t
  let m : ℂ := ((Real.log (t / (2 * Real.pi)) / 2 : ℝ) : ℂ)
  have hsre : 0 < s.re := by simpa [s] using hs
  have hsim : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro he
    have hi := congrArg Complex.im he
    rw [hsim] at hi
    norm_num at hi
    linarith
  have hright : ‖deriv conreyH (s + 2) / conreyH (s + 2) - m‖ ≤ 8 := by
    have hraw := norm_logDeriv_conreyH_sub_half_log_t_div_two_pi_le
      (sigma := sigma + 2) (by linarith : 2 ≤ t) (by linarith) (by linarith)
    have he : s + 2 = (((sigma + 2 : ℝ) : ℂ) + I * t) := by
      dsimp [s]
      push_cast
      ring
    rw [he]
    exact hraw
  have hinv (c : ℝ) : ‖1 / (s + (c : ℂ))‖ ≤ (1 / 3 : ℝ) := by
    have hnorm : 3 ≤ ‖s + (c : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (s + (c : ℂ))
      simp only [add_im, ofReal_im, add_zero, hsim,
        abs_of_nonneg (by linarith : 0 ≤ t)] at h
      exact ht.trans h
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le (by norm_num) hnorm
  have hi2 : ‖1 / (s + 2)‖ ≤ (1 / 3 : ℝ) := by simpa using hinv 2
  have hi1 : ‖1 / (s + 1)‖ ≤ (1 / 3 : ℝ) := by simpa using hinv 1
  have him : ‖1 / (s - 1)‖ ≤ (1 / 3 : ℝ) := by simpa [sub_eq_add_neg] using hinv (-1)
  change ‖deriv conreyH s / conreyH s - m‖ ≤ 10
  rw [logDeriv_conreyH_shift_two hsre hs1]
  rw [show deriv conreyH (s + 2) / conreyH (s + 2) - 1 / (s + 2) -
      1 / (s + 1) + 1 / (s - 1) - m =
      (deriv conreyH (s + 2) / conreyH (s + 2) - m) - 1 / (s + 2) -
        1 / (s + 1) + 1 / (s - 1) by ring]
  calc
    _ ≤ ‖deriv conreyH (s + 2) / conreyH (s + 2) - m - 1 / (s + 2) - 1 / (s + 1)‖ +
        ‖1 / (s - 1)‖ := norm_add_le _ _
    _ ≤ (‖deriv conreyH (s + 2) / conreyH (s + 2) - m - 1 / (s + 2)‖ +
        ‖1 / (s + 1)‖) + ‖1 / (s - 1)‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (‖deriv conreyH (s + 2) / conreyH (s + 2) - m‖ + ‖1 / (s + 2)‖) +
        ‖1 / (s + 1)‖ + ‖1 / (s - 1)‖ :=
      add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
    _ ≤ 10 := by linarith

end HardyTheorem
