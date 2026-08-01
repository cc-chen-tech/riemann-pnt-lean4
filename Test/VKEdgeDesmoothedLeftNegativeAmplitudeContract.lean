import PrimeNumberTheorem.VKEdgeDesmoothedLeftNegativeAmplitude

open Complex
open PrimeNumberTheorem
open PrimeNumberTheorem.ExplicitFormulaResidues

#check norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_neg_le
#check norm_add_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
#check exists_dynamicCubicLeftBoundary_negative_interval_oscillatory_bound

example {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzeta : ∀ t ∈ Set.Icc (-v) (-u),
      riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlog : ∀ t ∈ Set.Icc (-v) (-u),
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlog' : ∀ t ∈ Set.Icc (-v) (-u),
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmall : ∀ t ∈ Set.Icc (-v) (-u),
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖∫ t in (-v)..(-u),
        desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
      x ^ a *
        ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
          Real.log x) :=
  norm_intervalIntegral_desmoothedCubicLeftContourIntegrand_neg_le
    hx hh hu huv hL hD hzeta hlog hlog' hsmall

example {x h a u v L D : ℝ}
    (hx : 1 < x) (hh : 0 < h) (hu : 2 ≤ u) (huv : u ≤ v)
    (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hzetaPos : ∀ t ∈ Set.Icc u v,
      riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlogPos : ∀ t ∈ Set.Icc u v,
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlogPos' : ∀ t ∈ Set.Icc u v,
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmallPos : ∀ t ∈ Set.Icc u v,
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2)
    (hzetaNeg : ∀ t ∈ Set.Icc (-v) (-u),
      riemannZeta ((a : ℂ) + I * t) ≠ 0)
    (hlogNeg : ∀ t ∈ Set.Icc (-v) (-u),
      ‖logDeriv riemannZeta ((a : ℂ) + I * t)‖ ≤ L)
    (hlogNeg' : ∀ t ∈ Set.Icc (-v) (-u),
      ‖deriv (logDeriv riemannZeta) ((a : ℂ) + I * t)‖ ≤ D)
    (hsmallNeg : ∀ t ∈ Set.Icc (-v) (-u),
      h * ‖(a : ℂ) + I * t‖ ≤ 1 / 2) :
    ‖(∫ t in u..v,
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)) +
        ∫ t in (-v)..(-u),
          desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
      2 * x ^ a *
        ((6 * L / u + (3 * D + 11 * L) * Real.log (v / u)) /
          Real.log x) :=
  norm_add_intervalIntegral_desmoothedCubicLeftContourIntegrand_le
    hx hh hu huv hL hD hzetaPos hlogPos hlogPos' hsmallPos
      hzetaNeg hlogNeg hlogNeg' hsmallNeg

example :
    ∃ b C D T0 : ℝ, 0 < b ∧ 0 ≤ C ∧ 0 ≤ D ∧ 4 ≤ T0 ∧
      ∀ H x h u v : ℝ, T0 ≤ H → 1 < x → 0 < h →
        T0 + 1 ≤ u → u ≤ v → v + 1 ≤ H → h * H ≤ 1 / 2 →
          let a := dynamicCubicLeftBoundary b H
          ‖∫ t in (-v)..(-u),
              desmoothedCubicContourIntegrand x h (cubicLeftContourPoint a t)‖ ≤
            x ^ a *
              ((6 * (C * (1 + Real.log (H + 6)) ^ 2) / u +
                (3 * (D * (1 + Real.log (H + 6)) ^ 3) +
                  11 * (C * (1 + Real.log (H + 6)) ^ 2)) *
                    Real.log (v / u)) / Real.log x) :=
  exists_dynamicCubicLeftBoundary_negative_interval_oscillatory_bound
