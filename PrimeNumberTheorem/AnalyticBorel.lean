import ZeroFreeRegion.PhragmenLindelofZeta

open Complex Filter Set Topology

namespace ZeroFreeRegion

/-- Borel--Caratheodory and Cauchy on an arbitrary strictly smaller disk.
The explicit square loss in `R - d` is what permits the retained disk to lie
close to the zero-avoiding boundary circle. -/
theorem norm_logDeriv_le_four_mul_max_sub_mul_add_div_sq_of_sphere_log_norm_le_of_center_lower
    {g : ℂ → ℂ} {c z : ℂ} {R d B C0 : ℝ}
    (hR : 0 < R) (hd : 0 ≤ d) (hdR : d < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hgne : ∀ w ∈ Metric.closedBall c R, g w ≠ 0)
    (hcenter : C0 ≤ Real.log ‖g c‖)
    (hsphere : ∀ w ∈ Metric.sphere c R, Real.log ‖g w‖ ≤ B)
    (hz : z ∈ Metric.closedBall c d) :
    ‖logDeriv g z‖ ≤
      4 * max (B - C0) 1 * (R + d) / (R - d) ^ 2 := by
  let M : ℝ := max (B - C0) 1
  let rho : ℝ := (R - d) / 2
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hrho : 0 < rho := by
    dsimp [rho]
    linarith
  have hdiff : DiffContOnCl ℂ g (Metric.ball c R) :=
    hg.differentiableOn.diffContOnCl_ball subset_rfl
  have hsphere_norm : ∀ w ∈ Metric.sphere c R, ‖g w‖ ≤ Real.exp B := by
    intro w hw
    have hexp := Real.exp_le_exp.mpr (hsphere w hw)
    rw [Real.exp_log (norm_pos_iff.mpr
      (hgne w (Metric.sphere_subset_closedBall hw)))] at hexp
    exact hexp
  have hclosed_norm : ∀ w ∈ Metric.closedBall c R, ‖g w‖ ≤ Real.exp B := by
    intro w hw
    apply Complex.norm_le_of_forall_mem_frontier_norm_le
      Metric.isBounded_ball hdiff
    · intro u hu
      exact hsphere_norm u (Metric.frontier_ball_subset_sphere hu)
    · rw [closure_ball c hR.ne']
      exact hw
  have hre : ∀ w ∈ Metric.ball c R,
      Real.log ‖g w‖ - Real.log ‖g c‖ ≤ M := by
    intro w hw
    have hw_closed : w ∈ Metric.closedBall c R :=
      Metric.ball_subset_closedBall hw
    have hlog_w : Real.log ‖g w‖ ≤ B := by
      have hlog := Real.log_le_log
        (norm_pos_iff.mpr (hgne w hw_closed)) (hclosed_norm w hw_closed)
      simpa using hlog
    have hsub : Real.log ‖g w‖ - Real.log ‖g c‖ ≤ B - C0 := by
      linarith
    exact hsub.trans (le_max_left _ _)
  obtain ⟨h, hh, hhc, hhderiv, _hhexp, hhre⟩ :=
    exists_normalized_analytic_log_primitive_on_ball hR hg hgne
  have hmaps : MapsTo h (Metric.ball c R) {w : ℂ | w.re ≤ M} := by
    intro w hw
    change (h w).re ≤ M
    rw [hhre w hw]
    exact hre w hw
  have hzdist : dist z c ≤ d := Metric.mem_closedBall.mp hz
  have hclosed_subset : Metric.closedBall z rho ⊆ Metric.ball c R := by
    intro w hw
    have hwz : dist w z ≤ rho := Metric.mem_closedBall.mp hw
    have hwc : dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
    apply Metric.mem_ball.mpr
    dsimp [rho] at hwz
    linarith
  have hdiff_closed : DifferentiableOn ℂ h (Metric.closedBall z rho) :=
    hh.differentiableOn.mono hclosed_subset
  have hdiff_h : DiffContOnCl ℂ h (Metric.ball z rho) :=
    hdiff_closed.diffContOnCl_ball subset_rfl
  have hnorm : ∀ w ∈ Metric.sphere z rho,
      ‖h w‖ ≤ 2 * M * ((R + d) / (R - d)) := by
    intro w hw
    have hwz : dist w z = rho := Metric.mem_sphere.mp hw
    have hwc : dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
    have hwc_bound : ‖w - c‖ ≤ (R + d) / 2 := by
      rw [← dist_eq_norm]
      rw [hwz] at hwc
      dsimp [rho] at hwc
      linarith
    have hwc_lt : ‖w - c‖ < R := by
      linarith
    have hw_ball : w ∈ Metric.ball c R := by
      simpa [Metric.mem_ball, dist_eq_norm] using hwc_lt
    have hbc := borelCaratheodory_zero_centered
      hM hh.differentiableOn hmaps hR hw_ball hhc
    have hden_left : 0 < R - ‖w - c‖ := by linarith
    have hden_right : 0 < R - d := sub_pos.mpr hdR
    have hratio : ‖w - c‖ / (R - ‖w - c‖) ≤
        (R + d) / (R - d) := by
      rw [div_le_div_iff₀ hden_left hden_right]
      nlinarith [norm_nonneg (w - c)]
    calc
      ‖h w‖ ≤ 2 * M * ‖w - c‖ / (R - ‖w - c‖) := hbc
      _ = (2 * M) * (‖w - c‖ / (R - ‖w - c‖)) := by ring
      _ ≤ (2 * M) * ((R + d) / (R - d)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = 2 * M * ((R + d) / (R - d)) := by ring
  have hz_ball : z ∈ Metric.ball c R := Metric.mem_ball.mpr (hzdist.trans_lt hdR)
  have hcauchy : ‖deriv h z‖ ≤
      (2 * M * ((R + d) / (R - d))) / rho :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      hrho hdiff_h hnorm
  have hformula :
      (2 * M * ((R + d) / (R - d))) / rho =
        4 * M * (R + d) / (R - d) ^ 2 := by
    dsimp [rho]
    field_simp [sub_ne_zero.mpr hdR.ne]
    ring
  rw [hformula] at hcauchy
  simpa [M, hhderiv z hz_ball] using hcauchy

end ZeroFreeRegion
