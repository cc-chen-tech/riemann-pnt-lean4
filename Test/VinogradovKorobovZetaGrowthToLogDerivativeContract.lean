import ZeroFreeRegion.VinogradovKorobov.ZetaGrowthToLogDerivative

open Complex

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable example (M K : ℝ) : ℝ :=
  fixedJensenRegularizedEnvelope M K

noncomputable example (K : ℝ) : ℝ := fixedJensenLogEnvelope K

example : 0 < fixedJensenLogEnvelopeConstant :=
  fixedJensenLogEnvelopeConstant_pos

example {K : ℝ} (hK : 0 ≤ K) :
    fixedJensenLogEnvelope K ≤
      fixedJensenLogEnvelopeConstant * (1 + K) :=
  fixedJensenLogEnvelope_le_constant_mul_one_add hK

example {E σ t : ℝ}
    (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (ht : 4 ≤ |t|)
    (hregular : ∀ z ∈ Metric.closedBall ((2 : ℂ) + I * t) 1,
      riemannZeta z ≠ 0 →
      ‖logDeriv riemannZeta z -
          ∑ᶠ u, (MeromorphicOn.divisor riemannZeta
            (Metric.closedBall ((2 : ℂ) + I * t) (17 / 10 : ℝ)) u : ℂ) *
              (z - u)⁻¹‖ ≤ E) :
    (-deriv riemannZeta ((σ : ℂ) + I * t) /
        riemannZeta ((σ : ℂ) + I * t)).re ≤ E :=
  re_neg_deriv_div_riemannZeta_le_of_fixed_regularized_bound
    hσ1 hσ2 ht hregular

end ZeroFreeRegion.VinogradovKorobov
