import PrimeNumberTheorem.AnalyticBorel

open Complex

namespace ZeroFreeRegion

example {g : ℂ → ℂ} {c z : ℂ} {R d B C0 : ℝ}
    (hR : 0 < R) (hd : 0 ≤ d) (hdR : d < R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hgne : ∀ w ∈ Metric.closedBall c R, g w ≠ 0)
    (hcenter : C0 ≤ Real.log ‖g c‖)
    (hsphere : ∀ w ∈ Metric.sphere c R, Real.log ‖g w‖ ≤ B)
    (hz : z ∈ Metric.closedBall c d) :
    ‖logDeriv g z‖ ≤
      4 * max (B - C0) 1 * (R + d) / (R - d) ^ 2 :=
  norm_logDeriv_le_four_mul_max_sub_mul_add_div_sq_of_sphere_log_norm_le_of_center_lower
    hR hd hdR hg hgne hcenter hsphere hz

#print axioms
  norm_logDeriv_le_four_mul_max_sub_mul_add_div_sq_of_sphere_log_norm_le_of_center_lower

end ZeroFreeRegion
