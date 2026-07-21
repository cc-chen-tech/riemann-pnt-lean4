import PrimeNumberTheorem.AnalyticJensen

open Complex MeasureTheory MeromorphicOn Real

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

example {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (hR : 0 < R)
    (hmeromorphic : MeromorphicOn f (Metric.closedBall c R))
    (hM : 1 ≤ M)
    (hsphere : ∀ z ∈ Metric.sphere c R, ‖f z‖ ≤ M) :
    circleAverage (Real.log ‖f ·‖) c R ≤ Real.log M :=
  circleAverage_log_norm_le_log_of_norm_le
    hR hmeromorphic hM hsphere

example {f : ℂ → ℂ} {c : ℂ} {R K m : ℝ}
    (hR : 0 < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hm : 0 < m) (hcenter : m ≤ ‖f c‖)
    (hcircle : circleAverage (Real.log ‖f ·‖) c R ≤ K) :
    (∑ᶠ u, (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)) ≤
      K - Real.log m :=
  jensen_weighted_zero_mass_le_of_circleAverage_le
    hR hanalytic hm hcenter hcircle

example {f : ℂ → ℂ} {c : ℂ} {r R K m : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hm : 0 < m) (hcenter : m ≤ ‖f c‖)
    (hcircle : circleAverage (Real.log ‖f ·‖) c R ≤ K) :
    Real.log (R / r) *
        (∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
          (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ)) ≤
      K - Real.log m :=
  jensen_inner_zero_multiplicity_le_of_circleAverage_le
    hr hrR hanalytic hm hcenter hcircle

example {f : ℂ → ℂ} {c : ℂ} {r R K m : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hm : 0 < m) (hcenter : m ≤ ‖f c‖)
    (hcircle : circleAverage (Real.log ‖f ·‖) c R ≤ K) :
    (∑ᶠ u ∈ (Metric.closedBall c r : Set ℂ),
        (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ)) ≤
      (K - Real.log m) / Real.log (R / r) :=
  jensen_inner_zero_multiplicity_le_log_div
    hr hrR hanalytic hm hcenter hcircle

example {f : ℂ → ℂ} {c : ℂ} {b : ℝ} (hb : 1 ≤ b)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c b))
    (hc : f c ≠ 0) :
    (∑ᶠ u,
        (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ) *
          Real.log ‖c - u‖) ≤
      Real.log b *
        (∑ᶠ u,
          (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ)) :=
  finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
    hb hanalytic hc

example {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hnotop : ∀ u : (Metric.closedBall c R : Set ℂ),
      meromorphicOrderAt f u ≠ ⊤)
    (hc : f c ≠ 0) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ u : (Metric.closedBall c R : Set ℂ), g u ≠ 0) ∧
      Real.log ‖f c‖ =
        (∑ᶠ u,
          (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) *
            Real.log ‖c - u‖) + Real.log ‖g c‖ :=
  exists_analytic_nonzero_factor_log_norm_at_center
    hR hanalytic hnotop hc

example {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hrR : r < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hnotop : ∀ u : (Metric.closedBall c R : Set ℂ),
      meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ u : (Metric.closedBall c R : Set ℂ), g u ≠ 0) ∧
      ∀ z ∈ Metric.closedBall c r, f z ≠ 0 →
        Real.log ‖f z‖ =
          (∑ᶠ u,
            (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) *
              Real.log ‖z - u‖) + Real.log ‖g z‖ :=
  exists_analytic_nonzero_factor_log_norm_pointwise_of_ne_zero
    hrR hanalytic hnotop

example {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hrR : r < R)
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hnotop : ∀ u : (Metric.closedBall c R : Set ℂ),
      meromorphicOrderAt f u ≠ ⊤) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ u : (Metric.closedBall c R : Set ℂ), g u ≠ 0) ∧
      (∀ z ∈ Metric.closedBall c r, f z ≠ 0 →
        Real.log ‖f z‖ =
          (∑ᶠ u,
            (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) *
              Real.log ‖z - u‖) + Real.log ‖g z‖) ∧
      ∀ z ∈ Metric.ball c R, f z ≠ 0 →
        logDeriv f z =
          (∑ᶠ u,
            (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℂ) *
              (z - u)⁻¹) + logDeriv g z :=
  exists_analytic_nonzero_factor_log_norm_logDeriv_pointwise_of_ne_zero
    hrR hanalytic hnotop

example {f : ℂ → ℂ} {c : ℂ} {b R : ℝ} (hbR : b ≤ R)
    (hmeromorphic : MeromorphicOn f (Metric.closedBall c R)) :
    (∑ᶠ u,
        (MeromorphicOn.divisor f (Metric.closedBall c b) u : ℝ)) =
      ∑ᶠ u ∈ (Metric.closedBall c b : Set ℂ),
        (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) :=
  finsum_divisor_closedBall_eq_finsum_mem_of_le hbR hmeromorphic

example {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hanalytic : AnalyticOnNhd ℂ f (Metric.closedBall c R)) :
    (((MeromorphicOn.divisor f (Metric.closedBall c R)).finiteSupport
        (isCompact_closedBall c R)).toFinset.card : ℝ) ≤
      ∑ᶠ u,
        (MeromorphicOn.divisor f (Metric.closedBall c R) u : ℝ) :=
  card_divisor_support_le_finsum_mass hanalytic

#print axioms jensen_weighted_zero_mass_le_of_circleAverage_le
#print axioms circleAverage_log_norm_le_log_of_norm_le
#print axioms jensen_inner_zero_multiplicity_le_of_circleAverage_le
#print axioms jensen_inner_zero_multiplicity_le_log_div
#print axioms finsum_divisor_mul_log_norm_center_sub_le_log_mul_mass
#print axioms exists_analytic_nonzero_factor_log_norm_at_center
#print axioms exists_analytic_nonzero_factor_log_norm_pointwise_of_ne_zero
#print axioms
  exists_analytic_nonzero_factor_log_norm_logDeriv_pointwise_of_ne_zero
#print axioms finsum_divisor_closedBall_eq_finsum_mem_of_le
#print axioms card_divisor_support_le_finsum_mass

end CarlsonZeroDensity
end PrimeNumberTheorem
