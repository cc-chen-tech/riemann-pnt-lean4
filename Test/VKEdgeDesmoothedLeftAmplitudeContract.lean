import PrimeNumberTheorem.VKEdgeDesmoothedLeftAmplitude

open Complex

open PrimeNumberTheorem
open PrimeNumberTheorem.ExplicitFormulaResidues

#check desmoothedLeftOscillatoryAmplitude
#check desmoothedCubicLeftContourIntegrand_eq_rpow_mul_amplitude_mul_cexp
#check norm_desmoothedLeftOscillatoryAmplitude_le
#check differentiableAt_desmoothedLeftOscillatoryAmplitude
#check norm_deriv_desmoothedLeftOscillatoryAmplitude_le
#check norm_intervalIntegral_desmoothedLeftOscillatoryAmplitude_mul_cexp_le
#check norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
#check exists_dynamicCubicLeftBoundary_logDeriv_and_deriv_le
#check exists_dynamicCubicLeftBoundary_positive_interval_oscillatory_bound

example :
    ∃ b C D T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H : ℝ, T0 ≤ H →
        let a := dynamicCubicLeftBoundary b H
        0 < a ∧ a ≤ 1 / 3 ∧
          ∀ t : ℝ, T0 + 1 ≤ |t| → |t| + 1 ≤ H →
            riemannZeta ((a : ℂ) + I * t) ≠ 0 ∧
              ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤
                C * (1 + Real.log (H + 6)) ^ 2 ∧
              ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤
                D * (1 + Real.log (H + 6)) ^ 3 :=
  exists_dynamicCubicLeftBoundary_logDeriv_and_deriv_le

example :
    ∃ b C D T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H x h u v : ℝ, T0 ≤ H → 1 < x → 0 < h →
        T0 + 1 ≤ u → u ≤ v → v + 1 ≤ H → h * H ≤ 1 / 2 →
          let a := dynamicCubicLeftBoundary b H
          ‖∫ t in u..v,
              desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
            x ^ a *
              ((6 * (C * (1 + Real.log (H + 6)) ^ 2) / u +
                (3 * (D * (1 + Real.log (H + 6)) ^ 3) +
                  11 * (C * (1 + Real.log (H + 6)) ^ 2)) *
                    Real.log (v / u)) / Real.log x) :=
  exists_dynamicCubicLeftBoundary_positive_interval_oscillatory_bound

example {h a t L : ℝ} (hh : 0 < h) (ht : 2 ≤ |t|)
    (hlog : ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hsmall : h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖desmoothedLeftOscillatoryAmplitude h a t‖ ≤ 3 * L / |t| :=
  norm_desmoothedLeftOscillatoryAmplitude_le hh ht hlog hsmall

example {h a t : ℝ} (hh : 0 < h) (ht : 2 ≤ |t|)
    (hzeta : riemannZeta ((a : ℂ) + I * t) ≠ 0) :
    DifferentiableAt ℝ (desmoothedLeftOscillatoryAmplitude h a) t :=
  differentiableAt_desmoothedLeftOscillatoryAmplitude hh ht hzeta

example {x h a t : ℝ} (hx : 0 < x) :
    desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t) =
      ((x ^ a : ℝ) : ℂ) * desmoothedLeftOscillatoryAmplitude h a t *
        Complex.exp (I * (Real.log x * t)) :=
  desmoothedCubicLeftContourIntegrand_eq_rpow_mul_amplitude_mul_cexp hx

example {h a t L D : ℝ} (hh : 0 < h)
    (ht : 2 ≤ |t|)
    (hzeta : riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖deriv (desmoothedLeftOscillatoryAmplitude h a) t‖ ≤
      3 * D / |t| + 11 * L / |t| ^ 2 :=
  norm_deriv_desmoothedLeftOscillatoryAmplitude_le
    hh ht hzeta hlog hlog' hsmall

example {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzeta : ∀ t ∈ Set.Icc u v, riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ∀ t ∈ Set.Icc u v,
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ∀ t ∈ Set.Icc u v,
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : ∀ t ∈ Set.Icc u v,
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖∫ t in u..v, desmoothedLeftOscillatoryAmplitude h a t *
        Complex.exp (I * (Real.log x * t))‖ ≤
      (6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
        Real.log x :=
  norm_intervalIntegral_desmoothedLeftOscillatoryAmplitude_mul_cexp_le
    hx hh hu huv hL hD hzeta hlog hlog' hsmall

example {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzeta : ∀ t ∈ Set.Icc u v, riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ∀ t ∈ Set.Icc u v,
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ∀ t ∈ Set.Icc u v,
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : ∀ t ∈ Set.Icc u v,
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖∫ t in u..v,
        desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
      x ^ a *
        ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
          Real.log x) :=
  norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
    hx hh hu huv hL hD hzeta hlog hlog' hsmall
