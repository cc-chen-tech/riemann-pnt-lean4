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

#print axioms jensen_weighted_zero_mass_le_of_circleAverage_le
#print axioms circleAverage_log_norm_le_log_of_norm_le
#print axioms jensen_inner_zero_multiplicity_le_of_circleAverage_le
#print axioms jensen_inner_zero_multiplicity_le_log_div

end CarlsonZeroDensity
end PrimeNumberTheorem
