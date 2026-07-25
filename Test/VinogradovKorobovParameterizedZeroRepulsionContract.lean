import ZeroFreeRegion.VinogradovKorobov.ParameterizedZeroRepulsion

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (d a b R M K rho : ℝ) : ℝ :=
  parameterizedJensenEnvelope d a b R M K rho

example {b d E σ t : ℝ}
    (hσ1 : 1 ≤ σ) (hbheight : b < |t|)
    (hs : ((σ : ℂ) + I * t) ∈
      Metric.closedBall ((2 : ℂ) + I * t) d)
    (hregular : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) d,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) b) u : ℂ) *
              (z - u)⁻¹‖ ≤ E) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤ E :=
  re_neg_deriv_div_riemannZeta_le_of_regularized_bound
    hσ1 hbheight hs hregular

end ZeroFreeRegion.VinogradovKorobov
