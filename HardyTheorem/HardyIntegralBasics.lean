import HardyTheorem

open Complex Filter Set Topology
open scoped Interval

namespace HardyTheorem

/-- On the critical line, Hardy's real function is the real completed zeta
value divided by the strictly positive archimedean factor. -/
theorem hardyZ_eq_completedRiemannZeta_re_div_norm (t : ℝ) :
    hardyZ t =
      (completedRiemannZeta ((1 / 2 : ℂ) + I * t)).re /
        ‖Gammaℝ ((1 / 2 : ℂ) + I * t)‖ := by
  let s := (0.5 : ℂ) + I * t
  have hs_eq : s = (1 / 2 : ℂ) + I * t := by
    simp [s]
    norm_num
  have hs0 : s ≠ 0 := by
    intro h0
    simp [s, Complex.ext_iff] at h0
    norm_num at h0
  have h_internal :
      hardyZ t = (completedRiemannZeta s).re / ‖Gammaℝ s‖ := by
    have h_def :
        hardyZ t = (riemannZeta s).re * Real.cos (thetaPhase t) -
          (riemannZeta s).im * Real.sin (thetaPhase t) := by
      simp [hardyZ, s]
    rw [h_def]
    have h_zeta : riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
      rw [riemannZeta_def_of_ne_zero hs0]
    rw [h_zeta]
    have h_gamma_ne : Gammaℝ s ≠ 0 := by
      apply Gammaℝ_ne_zero_of_re_pos
      simp [s]
      norm_num
    have h_normSq : Complex.normSq (Gammaℝ s) = ‖Gammaℝ s‖ ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
    have h_gamma :
        (Gammaℝ s).re = ‖Gammaℝ s‖ * Real.cos (thetaPhase t) ∧
          (Gammaℝ s).im = ‖Gammaℝ s‖ * Real.sin (thetaPhase t) := by
      rw [hs_eq]
      exact Gammaℝ_re_im_arg t
    simp [Complex.div_re, Complex.div_im, h_gamma.1, h_gamma.2, h_normSq]
    field_simp [h_gamma_ne]
    ring_nf
    have h_trig :
        (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 +
            (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2 =
          (completedRiemannZeta s).re := by
      calc
        (completedRiemannZeta s).re * Real.cos (thetaPhase t) ^ 2 +
            (completedRiemannZeta s).re * Real.sin (thetaPhase t) ^ 2 =
            (completedRiemannZeta s).re *
              (Real.cos (thetaPhase t) ^ 2 + Real.sin (thetaPhase t) ^ 2) := by
                ring
        _ = (completedRiemannZeta s).re := by rw [Real.cos_sq_add_sin_sq]; ring
    ring_nf at h_trig ⊢
    exact h_trig
  rw [hs_eq] at h_internal
  exact h_internal

theorem abs_hardyZ_eq_norm_riemannZeta (t : ℝ) :
    |hardyZ t| = ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
  let s := (1 / 2 : ℂ) + I * t
  obtain ⟨r, hr⟩ := completedRiemannZeta_critical_line_real t
  have hs0 : s ≠ 0 := by
    intro h
    simp [s, Complex.ext_iff] at h
  have h_gamma_ne : Gammaℝ s ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp [s]
  have h_zeta : riemannZeta s = completedRiemannZeta s / Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero hs0]
  have h_hardyZ : hardyZ t = (completedRiemannZeta s).re / ‖Gammaℝ s‖ := by
    simpa [s] using hardyZ_eq_completedRiemannZeta_re_div_norm t
  rw [h_hardyZ, h_zeta, show completedRiemannZeta s = (r : ℂ) by simpa [s] using hr]
  simp [abs_div]

theorem abs_integral_hardyZ_eq_integral_abs_of_const_sign
    {T : ℝ} (hT : 0 ≤ T)
    (h_sign :
      (∀ t ∈ Set.Icc T (2 * T), 0 ≤ hardyZ t) ∨
        (∀ t ∈ Set.Icc T (2 * T), hardyZ t ≤ 0)) :
    |∫ t in T..(2 * T), hardyZ t| =
      ∫ t in T..(2 * T), |hardyZ t| := by
  have hT2 : T ≤ 2 * T := by linarith
  rcases h_sign with h_pos | h_neg
  · have h_integral_nonneg : 0 ≤ ∫ t in T..(2 * T), hardyZ t :=
      intervalIntegral.integral_nonneg hT2 h_pos
    rw [abs_of_nonneg h_integral_nonneg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT2] at ht
    exact (abs_of_nonneg (h_pos t ht)).symm
  · have h_integral_neg_nonneg : 0 ≤ ∫ t in T..(2 * T), -hardyZ t := by
      refine intervalIntegral.integral_nonneg hT2 ?_
      intro t ht
      exact neg_nonneg.mpr (h_neg t ht)
    rw [intervalIntegral.integral_neg] at h_integral_neg_nonneg
    rw [abs_of_nonpos (by linarith)]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hT2] at ht
    exact (abs_of_nonpos (h_neg t ht)).symm

theorem eventually_abs_integral_hardyZ_eq_integral_norm_zeta_of_bounded_zeros
    (h_bdd : Bornology.IsBounded {t : ℝ | hardyZ t = 0}) :
    ∀ᶠ T : ℝ in atTop,
      |∫ t in T..(2 * T), hardyZ t| =
        ∫ t in T..(2 * T),
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
  rcases hardyZ_eventually_const_sign_of_bounded_zeros h_bdd with h_pos | h_neg
  · rcases eventually_atTop.1 h_pos with ⟨A, hA⟩
    filter_upwards [eventually_ge_atTop (max A 0)] with T hT
    have hT0 : 0 ≤ T := le_trans (le_max_right A 0) hT
    have h_sign : ∀ t ∈ Set.Icc T (2 * T), 0 ≤ hardyZ t := by
      intro t ht
      exact le_of_lt (hA t (le_trans (le_trans (le_max_left A 0) hT) ht.1))
    calc
      |∫ t in T..(2 * T), hardyZ t| =
          ∫ t in T..(2 * T), |hardyZ t| :=
            abs_integral_hardyZ_eq_integral_abs_of_const_sign hT0 (Or.inl h_sign)
      _ = ∫ t in T..(2 * T),
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
            apply intervalIntegral.integral_congr
            intro t _
            exact abs_hardyZ_eq_norm_riemannZeta t
  · rcases eventually_atTop.1 h_neg with ⟨A, hA⟩
    filter_upwards [eventually_ge_atTop (max A 0)] with T hT
    have hT0 : 0 ≤ T := le_trans (le_max_right A 0) hT
    have h_sign : ∀ t ∈ Set.Icc T (2 * T), hardyZ t ≤ 0 := by
      intro t ht
      exact le_of_lt (hA t (le_trans (le_trans (le_max_left A 0) hT) ht.1))
    calc
      |∫ t in T..(2 * T), hardyZ t| =
          ∫ t in T..(2 * T), |hardyZ t| :=
            abs_integral_hardyZ_eq_integral_abs_of_const_sign hT0 (Or.inr h_sign)
      _ = ∫ t in T..(2 * T),
          ‖riemannZeta ((1 / 2 : ℂ) + I * t)‖ := by
            apply intervalIntegral.integral_congr
            intro t _
            exact abs_hardyZ_eq_norm_riemannZeta t

end HardyTheorem
