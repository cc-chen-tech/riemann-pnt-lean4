import HardyTheorem.ConreyCoprimeMobiusPerron

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

-- Arbitrary complex shift and positive REAL cutoff, including integer endpoints.
-- No summability, integrability, Euler-product identity, or Perron identity is assumed.
example {d : ℕ} [NeZero d] (α : ℂ) {X u : ℝ}
    (hX : 0 < X) (hu : 0 < u) (hα : 0 < α.re + u) :
    Integrable (fun t : ℝ =>
      (X : ℂ) ^ selbergPerronLine u t *
        (riemannZeta (1 + α + selbergPerronLine u t) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
        (1 / selbergPerronLine u t ^ 2)) ∧
    (1 / (2 * Real.pi) : ℂ) *
      (∫ t : ℝ, (X : ℂ) ^ selbergPerronLine u t *
        (riemannZeta (1 + α + selbergPerronLine u t) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + selbergPerronLine u t))))⁻¹ *
        (1 / selbergPerronLine u t ^ 2)) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (if n.Coprime d then (ArithmeticFunction.moebius n : ℂ) else 0) *
          (n : ℂ) ^ (-(1 + α)) * (Real.log (X / (n : ℝ)) : ℂ) :=
  conrey_coprime_mobius_log_perron α hX hu hα

example (coeff : ℕ → ℂ) {X u : ℝ} (hX : 0 < X) (hu : 0 < u)
    (hsum : LSeriesSummable coeff (u : ℂ)) :
    Integrable (selbergPerronLSeriesIntegrand coeff X u) :=
  integrable_selbergPerronLSeriesIntegrand coeff hX hu hsum

#print axioms conrey_coprime_mobius_log_perron
#print axioms integrable_selbergPerronLSeriesIntegrand

end HardyTheorem
